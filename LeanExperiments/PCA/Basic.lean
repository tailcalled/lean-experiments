import LeanExperiments.PCA.Partial

/-!
# Partial combinatory algebras

A *partial combinatory algebra* (PCA) is the algebraic structure underlying
Kleene realizability: a carrier `A` with a *partial* application and two
distinguished elements `k`, `s` from which every "computable" function on `A`
can be built.

Partiality is modeled with the computable gas monad of
`LeanExperiments.PCA.Partial`:

* the *primitive* application `app : A → A → PComp A` returns a raw (computable)
  gas computation;
* the *lifted* application `⬝ : Partial A → Partial A → Partial A` works on
  partial values (computations up to Kleene equality), so the combinator laws
  are ordinary equations `=` in `Partial A`.

Everything is `choice`-free; concrete instances compute.
-/

namespace LeanExperiments

open scoped LeanExperiments.Partial

universe u

/-- A *partial applicative structure*: a carrier with a partial binary
application, presented as a computable gas computation. -/
class PartialApp (A : Type u) where
  /-- Apply one element to another, as a gas computation. -/
  app : A → A → PComp A

namespace PartialApp

variable {A : Type u}

/-- Coerce an element to the always-defined partial value with that result.
Lets us write mixed expressions like `k ⬝ a ⬝ b`. -/
scoped instance : CoeTail A (Partial A) := ⟨Partial.pure⟩

@[simp] theorem coe_def (a : A) : (↑a : Partial A) = Partial.pure a := rfl

/-- Membership of a coerced element. -/
@[simp] theorem mem_coe {a w : A} : w ∈ (↑a : Partial A) ↔ w = a := Partial.mem_pure

variable [PartialApp A]

/-- Application lifted to partial values: run `p`, then `q`, then apply the
results (threading gas throughout). -/
def applyP (p q : Partial A) : Partial A :=
  Quotient.lift₂
    (fun x y => ⟦PComp.bind x fun f => PComp.bind y fun a => app f a⟧ₚ)
    (fun _ _ _ _ hx hy =>
      Partial.mk_eq_mk.mpr
        (PComp.bind_congr hx fun f => PComp.bind_congr hy fun a => PComp.Equiv.refl (app f a)))
    p q

@[inherit_doc] scoped infixl:70 " ⬝ " => applyP

@[simp] theorem applyP_mk {x y : PComp A} :
    (⟦x⟧ₚ ⬝ ⟦y⟧ₚ : Partial A) = ⟦PComp.bind x fun f => PComp.bind y fun a => app f a⟧ₚ :=
  rfl

/-- Membership through lifted application: `w` is a result of `p ⬝ q` iff `p`
has a result `f`, `q` has a result `a`, and `w` is a result of `app f a`. -/
theorem mem_applyP {p q : Partial A} {w : A} :
    w ∈ (p ⬝ q) ↔ ∃ f a, f ∈ p ∧ a ∈ q ∧ w ∈ app f a := by
  induction p using Quotient.inductionOn with | _ x =>
  induction q using Quotient.inductionOn with | _ y =>
  show (w ∈ PComp.bind x fun f => PComp.bind y fun a => app f a) ↔
      ∃ f a, f ∈ x ∧ a ∈ y ∧ w ∈ app f a
  rw [PComp.mem_bind]
  constructor
  · rintro ⟨f, hf, hw⟩
    rw [PComp.mem_bind] at hw
    obtain ⟨a, ha, hw⟩ := hw
    exact ⟨f, a, hf, ha, hw⟩
  · rintro ⟨f, a, hf, ha, hw⟩
    exact ⟨f, hf, PComp.mem_bind.mpr ⟨a, ha, hw⟩⟩

end PartialApp

open scoped PartialApp

/-- A *partial combinatory algebra*: a partial applicative structure with
combinators `k` and `s`.  `k` projects to its first argument; `s` distributes.
`s ⬝ a ⬝ b` must always be defined (it is `c ↦ (a ⬝ c) ⬝ (b ⬝ c)` waiting for
its argument), even though the right-hand side of `s_eq` may diverge. -/
class PCA (A : Type u) extends PartialApp A where
  /-- The projection combinator. -/
  k : A
  /-- The substitution combinator. -/
  s : A
  /-- `k ⬝ a ⬝ b = a`. -/
  k_eq : ∀ a b : A, (k : Partial A) ⬝ a ⬝ b = ↑a
  /-- `s ⬝ a ⬝ b` is always defined. -/
  s_dom : ∀ a b : A, ((s : Partial A) ⬝ a ⬝ b).Dom
  /-- `s ⬝ a ⬝ b ⬝ c = (a ⬝ c) ⬝ (b ⬝ c)`. -/
  s_eq : ∀ a b c : A,
    (s : Partial A) ⬝ a ⬝ b ⬝ c = ((a : Partial A) ⬝ c) ⬝ ((b : Partial A) ⬝ c)

namespace Combinator

open scoped PartialApp
open PartialApp (mem_applyP coe_def)
open PCA (k s k_eq s_eq)

variable {A : Type u} [PCA A]

/-- The identity combinator `i = s k k`, as a partial value.  This is the first
example of *combinatory completeness*: a term built from `s` and `k` that
realizes a specific function (here, the identity). -/
def i : Partial A := ((s : A) ⬝ (k : A) ⬝ (k : A) : Partial A)

/-- `i` is indeed the identity: `i ⬝ a = a` for every `a`. -/
theorem i_app (a : A) : (i : Partial A) ⬝ a = Partial.pure a := by
  show ((s : A) ⬝ (k : A) ⬝ (k : A)) ⬝ a = Partial.pure a
  rw [s_eq k k a]
  have hmem : a ∈ ((k : A) : Partial A) ⬝ ↑a ⬝ ↑a := by
    rw [k_eq a a]; exact Partial.mem_pure.mpr rfl
  rw [mem_applyP] at hmem
  obtain ⟨f, _, hf, _, _⟩ := hmem
  rw [Partial.eq_pure_of_mem hf]
  have h2 := k_eq a f
  rw [Partial.eq_pure_of_mem hf] at h2
  simpa only [coe_def] using h2

end Combinator

end LeanExperiments
