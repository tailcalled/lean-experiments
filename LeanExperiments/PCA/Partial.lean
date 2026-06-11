/-!
# A computable partiality monad

`Part` (and anything built on `Classical.choice`) forces models to be
`noncomputable`.  Since our intended models are honestly computable, we replace
`Part` with a *gas*-threaded partiality monad.

A computation takes a gas budget and either runs out (`none`) or finishes,
returning the leftover gas together with the value:

```
Nat → Option (Nat × α)
```

We then carve out the **valid** computations (`PComp`) — those that are
*monotone in the threading sense*

```
run n = some (r, a)  →  run (n + k) = some (r + k, a)
```

This single law gives determinacy (at most one result) and stability, and is
preserved by `pure`/`bind`.  Finally we **quotient** by having the same
denotation to obtain `Partial α`, on which propositional equality *is* Kleene
equality.  Everything here is `choice`-free and computes.
-/

namespace LeanExperiments

universe u v w

/-- A *valid* gas-threaded computation: given a gas budget it either runs out
(`none`) or returns leftover gas and a value, and extra gas is threaded straight
through (`valid`). -/
structure PComp (α : Type u) where
  /-- Run with a gas budget, getting back leftover gas and a value (or `none`). -/
  run : Nat → Option (Nat × α)
  /-- Extra gas passes through as extra leftover, with the same value. -/
  valid : ∀ {n r a}, run n = some (r, a) → ∀ k, run (n + k) = some (r + k, a)
  /-- Gas is consumed, never created: leftover never exceeds the budget. -/
  le : ∀ {n r a}, run n = some (r, a) → r ≤ n

namespace PComp

variable {α : Type u} {β : Type v} {γ : Type w}

/-- `a` is *the* result of `x`: some budget produces it. -/
protected def Mem (x : PComp α) (a : α) : Prop := ∃ n r, x.run n = some (r, a)

instance : Membership α (PComp α) := ⟨PComp.Mem⟩

theorem mem_def {x : PComp α} {a : α} : a ∈ x ↔ ∃ n r, x.run n = some (r, a) := Iff.rfl

/-- Validity makes results unique. -/
theorem det {x : PComp α} {a b : α} (ha : a ∈ x) (hb : b ∈ x) : a = b := by
  obtain ⟨n, r, hn⟩ := ha
  obtain ⟨m, s, hm⟩ := hb
  have h1 := x.valid hn m
  have h2 := x.valid hm n
  rw [Nat.add_comm m n] at h2
  rw [h1] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact h2.2

/-- The computation that is defined. -/
def Dom (x : PComp α) : Prop := ∃ a, a ∈ x

/-! ### `pure` and `bind` -/

/-- Return a value without spending gas (leftover = budget). -/
def pure (a : α) : PComp α where
  run n := some (n, a)
  valid := by
    intro n r b h k
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  le := by
    intro n r b h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Nat.le_refl _

/-- Sequence two computations, threading the leftover gas. -/
def bind (x : PComp α) (f : α → PComp β) : PComp β where
  run n := (x.run n).bind fun p => (f p.2).run p.1
  valid := by
    intro n s b hb k
    rw [Option.bind_eq_some_iff] at hb
    obtain ⟨⟨r, a⟩, hx, hf⟩ := hb
    have hx' := x.valid hx k
    have hf' := (f a).valid hf k
    show (x.run (n + k)).bind _ = some (s + k, b)
    rw [hx']
    exact hf'
  le := by
    intro n s b hb
    rw [Option.bind_eq_some_iff] at hb
    obtain ⟨⟨r, a⟩, hx, hf⟩ := hb
    have h1 := x.le hx
    have h2 := (f a).le hf
    omega

@[simp] theorem pure_run (a : α) (n : Nat) : (pure a).run n = some (n, a) := rfl

@[simp] theorem bind_run (x : PComp α) (f : α → PComp β) (n : Nat) :
    (bind x f).run n = (x.run n).bind fun p => (f p.2).run p.1 := rfl

@[simp] theorem mem_pure {a b : α} : a ∈ pure b ↔ a = b := by
  constructor
  · rintro ⟨n, r, h⟩
    simp only [pure_run, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  · rintro rfl
    exact ⟨0, 0, rfl⟩

theorem mem_bind {x : PComp α} {f : α → PComp β} {c : β} :
    c ∈ bind x f ↔ ∃ a, a ∈ x ∧ c ∈ f a := by
  constructor
  · rintro ⟨n, s, hn⟩
    rw [bind_run, Option.bind_eq_some_iff] at hn
    obtain ⟨⟨r, a⟩, hx, hf⟩ := hn
    exact ⟨a, ⟨n, r, hx⟩, ⟨r, s, hf⟩⟩
  · rintro ⟨a, ⟨n, r, hx⟩, ⟨m, s, hf⟩⟩
    have hx' := x.valid hx m
    have hf' := (f a).valid hf r
    refine ⟨n + m, s + r, ?_⟩
    rw [bind_run, hx']
    show (f a).run (r + m) = some (s + r, c)
    rw [Nat.add_comm r m]
    exact hf'

/-! ### Kleene equality and the quotient -/

/-- Kleene equality: two computations with the same denotation. -/
def Equiv (x y : PComp α) : Prop := ∀ a, a ∈ x ↔ a ∈ y

@[refl] theorem Equiv.refl (x : PComp α) : Equiv x x := fun _ => Iff.rfl
theorem Equiv.symm {x y : PComp α} (h : Equiv x y) : Equiv y x := fun a => (h a).symm
theorem Equiv.trans {x y z : PComp α} (h₁ : Equiv x y) (h₂ : Equiv y z) : Equiv x z :=
  fun a => (h₁ a).trans (h₂ a)

instance setoid (α : Type u) : Setoid (PComp α) where
  r := Equiv
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

/-- `bind` is a congruence for Kleene equality. -/
theorem bind_congr {x x' : PComp α} {f f' : α → PComp β}
    (hx : Equiv x x') (hf : ∀ a, Equiv (f a) (f' a)) : Equiv (bind x f) (bind x' f') := by
  intro c
  rw [mem_bind, mem_bind]
  constructor
  · rintro ⟨a, hax, hcf⟩; exact ⟨a, (hx a).mp hax, (hf a c).mp hcf⟩
  · rintro ⟨a, hax, hcf⟩; exact ⟨a, (hx a).mpr hax, (hf a c).mpr hcf⟩

end PComp

/-- Partial values: valid gas-threaded computations up to Kleene equality.
Propositional equality on `Partial α` *is* Kleene equality. -/
def Partial (α : Type u) : Type u := Quotient (PComp.setoid α)

namespace Partial

variable {α : Type u} {β : Type v}

/-- The partial value denoted by a computation. -/
def mk (x : PComp α) : Partial α := Quotient.mk _ x

@[inherit_doc] scoped notation "⟦" x "⟧ₚ" => Partial.mk x

/-- Membership in a partial value (independent of the representative). -/
protected def Mem (p : Partial α) (a : α) : Prop :=
  Quotient.liftOn p (fun x => a ∈ x) fun _ _ h => propext (h a)

instance : Membership α (Partial α) := ⟨Partial.Mem⟩

@[simp] theorem mem_mk {x : PComp α} {a : α} : a ∈ (⟦x⟧ₚ : Partial α) ↔ a ∈ x := Iff.rfl

theorem mk_eq_mk {x y : PComp α} : (⟦x⟧ₚ : Partial α) = ⟦y⟧ₚ ↔ x.Equiv y := by
  constructor
  · intro h; exact Quotient.exact h
  · intro h; exact Quotient.sound h

@[ext] theorem ext {p q : Partial α} (h : ∀ a, a ∈ p ↔ a ∈ q) : p = q := by
  induction p using Quotient.inductionOn with | _ x =>
  induction q using Quotient.inductionOn with | _ y =>
  exact mk_eq_mk.mpr fun a => h a

/-- Results of a partial value are unique. -/
theorem det {p : Partial α} {a b : α} (ha : a ∈ p) (hb : b ∈ p) : a = b := by
  induction p using Quotient.inductionOn with | _ x => exact PComp.det ha hb

/-- A partial value is *defined* if it has a result. -/
def Dom (p : Partial α) : Prop := ∃ a, a ∈ p

/-- The total partial value with the given result. -/
def pure (a : α) : Partial α := ⟦PComp.pure a⟧ₚ

@[simp] theorem mem_pure {a b : α} : a ∈ (pure b : Partial α) ↔ a = b := PComp.mem_pure

/-- A partial value with a known result is exactly `pure` of it. -/
theorem eq_pure_of_mem {p : Partial α} {a : α} (h : a ∈ p) : p = pure a := by
  apply ext
  intro w
  rw [mem_pure]
  exact ⟨fun hw => det hw h, fun hw => hw ▸ h⟩

end Partial

end LeanExperiments
