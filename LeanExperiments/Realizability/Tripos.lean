import LeanExperiments.Realizability
import LeanExperiments.PCA.Pairing
import LeanExperiments.PCA.Tagging

/-!
# The realizability tripos (concrete)

The predicate fibers of the realizability tripos over a PCA `A`.  A predicate
over `I` is an `I`-indexed family of *sets of realizers*

```
Pred A I := I → A → Prop      -- `φ i a` means "`a` realizes `φ` at `i`"
```

and entailment `φ ⊢ ψ` is a **uniform** realizer: a single `e : A` with
`e ⬝ a` realizing `ψ` at `i` whenever `a` realizes `φ` at `i`, for *all* `i`.
Per the extraction discussion, `⊢` is a *truncated type* `Squash {e // …}` —
subsingleton, but carrying the (un-erased) realizer.

This file sets up the fibres, the entailment preorder (reusing `idElem`/
`compElem`), reindexing, and the pairing-free Heyting connectives `⊤`, `⊥`, `→`.
Conjunction/disjunction (needing pairing/tagging combinators), the quantifiers,
and the generic predicate come next; the abstract `Tripos` interface and
tripos→topos are factored out afterwards.
-/

namespace LeanExperiments.Realizability

open LeanExperiments
open scoped LeanExperiments.Partial LeanExperiments.PartialApp

universe u w v

variable {A : Type u} [PCA A] [Abstraction A]

/-- A predicate over `I`, valued in sets of realizers. -/
def Pred (A : Type u) (I : Type w) : Type (max u w) := I → A → Prop

/-- The tripos's object of truth values: sets of realizers (`𝒫 A`).  Note
`Pred A I = I → 𝒫 A`, so a predicate over `I` *is* a map `I → 𝒫 A`. -/
def Prop' (A : Type u) : Type u := A → Prop

namespace Pred

variable {I J : Type w}

/-- `e` *uniformly tracks* `φ ⊢ ψ`: it sends realizers of `φ` to realizers of
`ψ`, uniformly in the index. -/
def UniTracks (e : A) (φ ψ : Pred A I) : Prop :=
  ∀ (i : I) (a : A), φ i a → ∃ b, b ∈ (Partial.pure e ⬝ Partial.pure a : Partial A) ∧ ψ i b

/-- Entailment of predicates: a truncated (un-erased) uniform realizer. -/
abbrev Entails (φ ψ : Pred A I) : Type u := Squash { e : A // UniTracks e φ ψ }

@[inherit_doc] scoped infix:50 " ⊢ " => Entails

/-- Entailment is reflexive (tracked by the identity). -/
def Entails.refl (φ : Pred A I) : φ ⊢ φ :=
  Squash.mk ⟨Hom.idElem, fun _ a ha =>
    ⟨a, by rw [Hom.idElem_spec a]; exact Partial.mem_pure.mpr rfl, ha⟩⟩

/-- Entailment is transitive (tracked by composition). -/
def Entails.trans {φ ψ χ : Pred A I} (h₁ : φ ⊢ ψ) (h₂ : ψ ⊢ χ) : φ ⊢ χ :=
  Squash.lift h₁ fun e₁ => Squash.lift h₂ fun e₂ =>
    Squash.mk ⟨Hom.compElem e₂.1 e₁.1, fun i a ha => by
      obtain ⟨b, hb, hb'⟩ := e₁.2 i a ha
      obtain ⟨c, hc, hc'⟩ := e₂.2 i b hb'
      refine ⟨c, ?_, hc'⟩
      rw [Hom.compElem_spec e₂.1 e₁.1 a, PartialApp.mem_applyP]
      exact ⟨e₂.1, b, Partial.mem_pure.mpr rfl, hb, PartialApp.mem_pure_app.mp hc⟩⟩

/-! ### Reindexing -/

/-- Reindexing a predicate along a function. -/
def subst {J : Type v} (f : I → J) (ψ : Pred A J) : Pred A I := fun i => ψ (f i)

/-- Reindexing is monotone (the same realizer works). -/
def subst_mono (f : I → J) {φ ψ : Pred A J} (h : φ ⊢ ψ) : subst f φ ⊢ subst f ψ :=
  Squash.lift h fun e => Squash.mk ⟨e.1, fun i a ha => e.2 (f i) a ha⟩

/-! ### Pairing-free Heyting connectives -/

/-- Truth: realized by everything. -/
def top : Pred A I := fun _ _ => True

/-- Falsity: realized by nothing. -/
def bot : Pred A I := fun _ _ => False

/-- Heyting implication: `e` realizes `φ → ψ` at `i` iff it sends every realizer
of `φ` to a realizer of `ψ`. -/
def impl (φ ψ : Pred A I) : Pred A I :=
  fun i e => ∀ a, φ i a → ∃ b, b ∈ (Partial.pure e ⬝ Partial.pure a : Partial A) ∧ ψ i b

/-- `⊤` is the greatest predicate. -/
def le_top (φ : Pred A I) : φ ⊢ top :=
  Squash.mk ⟨Hom.idElem, fun _ a ha =>
    ⟨a, by rw [Hom.idElem_spec a]; exact Partial.mem_pure.mpr rfl, trivial⟩⟩

/-- `⊥` is the least predicate. -/
def bot_le (φ : Pred A I) : bot ⊢ φ :=
  Squash.mk ⟨Hom.idElem, fun _ _ h => absurd h (by simp [bot])⟩

/-! ### Existential quantifier (along reindexing) -/

/-- `∃_f φ` at `j`: realized by anything realizing `φ` at some `i` over `j`. -/
def ex (f : I → J) (φ : Pred A I) : Pred A J := fun j a => ∃ i, f i = j ∧ φ i a

/-- `∃_f ⊣ subst f`, one direction (tracked by the same realizer). -/
def ex_adj_mp {f : I → J} {φ : Pred A I} {ψ : Pred A J} (h : ex f φ ⊢ ψ) :
    φ ⊢ subst f ψ :=
  Squash.lift h fun e => Squash.mk ⟨e.1, fun i a ha => e.2 (f i) a ⟨i, rfl, ha⟩⟩

/-- `∃_f ⊣ subst f`, the other direction (same realizer). -/
def ex_adj_mpr {f : I → J} {φ : Pred A I} {ψ : Pred A J} (h : φ ⊢ subst f ψ) :
    ex f φ ⊢ ψ :=
  Squash.lift h fun e => Squash.mk ⟨e.1, fun _ a hja => by
    obtain ⟨i, hfi, ha⟩ := hja
    obtain ⟨b, hb, hb'⟩ := e.2 i a ha
    exact ⟨b, hb, hfi ▸ hb'⟩⟩

/-! ### Universal quantifier (along reindexing)

The realizer of `∀_f φ` at `j` is a *function*: `e ⬝ b` realizes `φ i` for every
`i` over `j` and every `b`.  This is what makes the right adjoint work over empty
fibres — the tracker `λa b. e₀ ⬝ a` returns a *closure* (defined even when
`e₀ ⬝ a` diverges), so an empty fibre is realized vacuously by a defined element. -/

/-- `∀_f φ` at `j`: realized by `e` such that `e ⬝ b` realizes `φ i` for every
`i` over `j` and every `b`. -/
def all (f : I → J) (φ : Pred A I) : Pred A J :=
  fun j e => ∀ i, f i = j → ∀ b, ∃ c, c ∈ (Partial.pure e ⬝ Partial.pure b : Partial A) ∧ φ i c

/-- The tracker `λa. e ⬝ a ⬝ k` for `subst f ⊣ ∀_f`, mpr direction. -/
def allMprElem (e : A) : A :=
  Abstraction.abs "a" (Expr.app (Expr.app (Expr.const e) (Expr.var "a")) (Expr.const PCA.k))

theorem allMprElem_spec (e a : A) :
    (Partial.pure (allMprElem e) ⬝ Partial.pure a : Partial A) =
      Partial.pure e ⬝ Partial.pure a ⬝ Partial.pure PCA.k := by
  have h := Abstraction.abs_spec (A := A) "a"
    (Expr.app (Expr.app (Expr.const e) (Expr.var "a")) (Expr.const PCA.k))
    (by simp [Expr.closed1, Expr.fvE]) a (fun _ => PCA.k)
  simpa [Expr.denote_app, Expr.denote_const, Expr.denote_var, Expr.update_same] using h

/-- The tracker `λa b. e ⬝ a` for `subst f ⊣ ∀_f`, mp direction. -/
def allMpElem (e : A) : A := abs2 "a" "b" (Expr.app (Expr.const e) (Expr.var "a"))

theorem allMpElem_spec (e a b : A) :
    (Partial.pure (allMpElem e) ⬝ Partial.pure a ⬝ Partial.pure b : Partial A) =
      Partial.pure e ⬝ Partial.pure a := by
  rw [allMpElem, abs2_spec "a" "b" _ (by simp [Expr.fvE]) a b (fun _ => PCA.k)]
  simp [Expr.denote_app, Expr.denote_const, Expr.denote_var, Expr.update]

theorem allMpElem_app1 (e a : A) :
    ∃ f, (Partial.pure (allMpElem e) ⬝ Partial.pure a : Partial A) = Partial.pure f :=
  abs2_app1 "a" "b" _ (by simp [Expr.fvE]) a (fun _ => PCA.k)

/-- `subst f ⊣ ∀_f`, one direction. -/
def all_adj_mp {f : I → J} {φ : Pred A I} {ψ : Pred A J} (h : subst f ψ ⊢ φ) :
    ψ ⊢ all f φ :=
  Squash.lift h fun e₀ =>
    Squash.mk ⟨allMpElem e₀.1, fun j a hja => by
      obtain ⟨E, hE⟩ := allMpElem_app1 e₀.1 a
      refine ⟨E, by rw [hE]; exact Partial.mem_pure.mpr rfl, fun i hfi b => ?_⟩
      have hEb : (Partial.pure E ⬝ Partial.pure b : Partial A) = Partial.pure e₀.1 ⬝ Partial.pure a := by
        rw [← hE, allMpElem_spec]
      obtain ⟨c, hc, hc'⟩ := e₀.2 i a (show ψ (f i) a from hfi ▸ hja)
      exact ⟨c, by rw [hEb]; exact hc, hc'⟩⟩

/-- `subst f ⊣ ∀_f`, the other direction. -/
def all_adj_mpr {f : I → J} {φ : Pred A I} {ψ : Pred A J} (h : ψ ⊢ all f φ) :
    subst f ψ ⊢ φ :=
  Squash.lift h fun e' =>
    Squash.mk ⟨allMprElem e'.1, fun i a ha => by
      obtain ⟨E, hE, hE'⟩ := e'.2 (f i) a ha
      obtain ⟨c, hc, hc'⟩ := hE' i rfl PCA.k
      refine ⟨c, ?_, hc'⟩
      rw [allMprElem_spec, Partial.eq_pure_of_mem hE]
      exact hc⟩

/-! ### Conjunction (needs pairing) -/

section
variable [Pairing A]

/-- Conjunction: realized by the pair of a realizer of `φ` and one of `ψ`. -/
def conj (φ ψ : Pred A I) : Pred A I :=
  fun i c => ∃ a b, φ i a ∧ ψ i b ∧
    c ∈ (Partial.pure Pairing.pair ⬝ Partial.pure a ⬝ Partial.pure b : Partial A)

/-- The realizer for `d ↦ ⟨p ⬝ d, q ⬝ d⟩`. -/
def pairOf (p q : A) : A :=
  Abstraction.abs "d"
    (Expr.app (Expr.app (Expr.const Pairing.pair) (Expr.app (Expr.const p) (Expr.var "d")))
      (Expr.app (Expr.const q) (Expr.var "d")))

theorem pairOf_spec (p q d : A) :
    (Partial.pure (pairOf p q) ⬝ Partial.pure d : Partial A) =
      Partial.pure Pairing.pair ⬝ (Partial.pure p ⬝ Partial.pure d) ⬝
        (Partial.pure q ⬝ Partial.pure d) := by
  have h := Abstraction.abs_spec (A := A) "d"
    (Expr.app (Expr.app (Expr.const Pairing.pair) (Expr.app (Expr.const p) (Expr.var "d")))
      (Expr.app (Expr.const q) (Expr.var "d")))
    (by simp [Expr.closed1, Expr.fvE]) d (fun _ => PCA.k)
  simpa [Expr.denote_app, Expr.denote_const, Expr.denote_var, Expr.update_same] using h

/-- `φ ∧ ψ ⊢ φ`, tracked by `fst`. -/
def conj_le_left (φ ψ : Pred A I) : conj φ ψ ⊢ φ :=
  Squash.mk ⟨Pairing.fst, fun _ c hc => by
    obtain ⟨a, b, ha, _, hcab⟩ := hc
    have h := Pairing.fst_pair a b
    rw [Partial.eq_pure_of_mem hcab] at h
    exact ⟨a, by rw [h]; exact Partial.mem_pure.mpr rfl, ha⟩⟩

/-- `φ ∧ ψ ⊢ ψ`, tracked by `snd`. -/
def conj_le_right (φ ψ : Pred A I) : conj φ ψ ⊢ ψ :=
  Squash.mk ⟨Pairing.snd, fun _ c hc => by
    obtain ⟨a, b, _, hb, hcab⟩ := hc
    have h := Pairing.snd_pair a b
    rw [Partial.eq_pure_of_mem hcab] at h
    exact ⟨b, by rw [h]; exact Partial.mem_pure.mpr rfl, hb⟩⟩

/-- The universal property of `∧`: `χ ⊢ φ` and `χ ⊢ ψ` give `χ ⊢ φ ∧ ψ`. -/
def le_conj {χ φ ψ : Pred A I} (h₁ : χ ⊢ φ) (h₂ : χ ⊢ ψ) : χ ⊢ conj φ ψ :=
  Squash.lift h₁ fun p => Squash.lift h₂ fun q =>
    Squash.mk ⟨pairOf p.1 q.1, fun i d hd => by
      obtain ⟨a, ha, ha'⟩ := p.2 i d hd
      obtain ⟨b, hb, hb'⟩ := q.2 i d hd
      obtain ⟨c, hc⟩ := Pairing.pair_total a b
      refine ⟨c, ?_, a, b, ha', hb', hc⟩
      rw [pairOf_spec, Partial.eq_pure_of_mem ha, Partial.eq_pure_of_mem hb]
      exact hc⟩

/-! ### Heyting implication adjunction -/

/-- The realizer for `c ↦ e ⬝ (fst c) ⬝ (snd c)` (uncurrying). -/
def uncurryElem (e : A) : A :=
  Abstraction.abs "c"
    (Expr.app (Expr.app (Expr.const e) (Expr.app (Expr.const Pairing.fst) (Expr.var "c")))
      (Expr.app (Expr.const Pairing.snd) (Expr.var "c")))

theorem uncurryElem_spec (e c : A) :
    (Partial.pure (uncurryElem e) ⬝ Partial.pure c : Partial A) =
      Partial.pure e ⬝ (Partial.pure Pairing.fst ⬝ Partial.pure c) ⬝
        (Partial.pure Pairing.snd ⬝ Partial.pure c) := by
  have h := Abstraction.abs_spec (A := A) "c"
    (Expr.app (Expr.app (Expr.const e) (Expr.app (Expr.const Pairing.fst) (Expr.var "c")))
      (Expr.app (Expr.const Pairing.snd) (Expr.var "c")))
    (by simp [Expr.closed1, Expr.fvE]) c (fun _ => PCA.k)
  simpa [Expr.denote_app, Expr.denote_const, Expr.denote_var, Expr.update_same] using h

/-- The realizer for `d ↦ λa. e ⬝ (pair d a)` (currying). -/
def curryElem (e : A) : A :=
  abs2 "d" "a"
    (Expr.app (Expr.const e)
      (Expr.app (Expr.app (Expr.const Pairing.pair) (Expr.var "d")) (Expr.var "a")))

theorem curryElem_app1 (e d : A) :
    ∃ f, (Partial.pure (curryElem e) ⬝ Partial.pure d : Partial A) = Partial.pure f :=
  abs2_app1 "d" "a" _ (by simp [Expr.fvE]) d (fun _ => PCA.k)

theorem curryElem_spec (e d a : A) :
    (Partial.pure (curryElem e) ⬝ Partial.pure d ⬝ Partial.pure a : Partial A) =
      Partial.pure e ⬝ (Partial.pure Pairing.pair ⬝ Partial.pure d ⬝ Partial.pure a) := by
  rw [curryElem, abs2_spec "d" "a" _ (by simp [Expr.fvE]) d a (fun _ => PCA.k)]
  simp [Expr.denote_app, Expr.denote_const, Expr.denote_var, Expr.update]

/-- `χ ∧ φ ⊢ ψ → χ ⊢ (φ → ψ)`. -/
def curry {χ φ ψ : Pred A I} (h : conj χ φ ⊢ ψ) : χ ⊢ impl φ ψ :=
  Squash.lift h fun e =>
    Squash.mk ⟨curryElem e.1, fun i d hd => by
      obtain ⟨f, hf⟩ := curryElem_app1 e.1 d
      refine ⟨f, by rw [hf]; exact Partial.mem_pure.mpr rfl, fun a ha => ?_⟩
      obtain ⟨c, hc⟩ := Pairing.pair_total d a
      obtain ⟨b, hb, hb'⟩ := e.2 i c ⟨d, a, hd, ha, hc⟩
      refine ⟨b, ?_, hb'⟩
      rw [← hf, curryElem_spec, Partial.eq_pure_of_mem hc]
      exact hb⟩

/-- `χ ⊢ (φ → ψ) → χ ∧ φ ⊢ ψ`. -/
def uncurry {χ φ ψ : Pred A I} (h : χ ⊢ impl φ ψ) : conj χ φ ⊢ ψ :=
  Squash.lift h fun e =>
    Squash.mk ⟨uncurryElem e.1, fun i c hc => by
      obtain ⟨d, a, hd, ha, hcda⟩ := hc
      obtain ⟨g, hg, hg'⟩ := e.2 i d hd
      obtain ⟨b, hb, hb'⟩ := hg' a ha
      refine ⟨b, ?_, hb'⟩
      have hfst : (Partial.pure Pairing.fst ⬝ Partial.pure c : Partial A) = Partial.pure d := by
        have := Pairing.fst_pair d a; rwa [Partial.eq_pure_of_mem hcda] at this
      have hsnd : (Partial.pure Pairing.snd ⬝ Partial.pure c : Partial A) = Partial.pure a := by
        have := Pairing.snd_pair d a; rwa [Partial.eq_pure_of_mem hcda] at this
      rw [uncurryElem_spec, hfst, hsnd, Partial.eq_pure_of_mem hg]
      exact hb⟩

end

/-! ### Disjunction (needs tagging) -/

section
variable [Tagging A]

/-- Disjunction: realized by a left-tag of a `φ`-realizer or a right-tag of a
`ψ`-realizer. -/
def disj (φ ψ : Pred A I) : Pred A I :=
  fun i c => (∃ a, φ i a ∧ c ∈ (Partial.pure Tagging.inl ⬝ Partial.pure a : Partial A)) ∨
             (∃ b, ψ i b ∧ c ∈ (Partial.pure Tagging.inr ⬝ Partial.pure b : Partial A))

/-- The case-analysis realizer `λc. c ⬝ p ⬝ q`. -/
def caseOf (p q : A) : A :=
  Abstraction.abs "c" (Expr.app (Expr.app (Expr.var "c") (Expr.const p)) (Expr.const q))

omit [Tagging A] in
theorem caseOf_spec (p q c : A) :
    (Partial.pure (caseOf p q) ⬝ Partial.pure c : Partial A) =
      Partial.pure c ⬝ Partial.pure p ⬝ Partial.pure q := by
  have h := Abstraction.abs_spec (A := A) "c"
    (Expr.app (Expr.app (Expr.var "c") (Expr.const p)) (Expr.const q))
    (by simp [Expr.closed1, Expr.fvE]) c (fun _ => PCA.k)
  simpa [Expr.denote_app, Expr.denote_const, Expr.denote_var, Expr.update_same] using h

/-- `φ ⊢ φ ∨ ψ`, tracked by `inl`. -/
def inl_le (φ ψ : Pred A I) : φ ⊢ disj φ ψ :=
  Squash.mk ⟨Tagging.inl, fun _ a ha => by
    obtain ⟨c, hc⟩ := Tagging.inl_total a
    exact ⟨c, hc, Or.inl ⟨a, ha, hc⟩⟩⟩

/-- `ψ ⊢ φ ∨ ψ`, tracked by `inr`. -/
def inr_le (φ ψ : Pred A I) : ψ ⊢ disj φ ψ :=
  Squash.mk ⟨Tagging.inr, fun _ b hb => by
    obtain ⟨c, hc⟩ := Tagging.inr_total b
    exact ⟨c, hc, Or.inr ⟨b, hb, hc⟩⟩⟩

/-- The universal property of `∨`: `φ ⊢ χ` and `ψ ⊢ χ` give `φ ∨ ψ ⊢ χ`. -/
def disj_le {φ ψ χ : Pred A I} (h₁ : φ ⊢ χ) (h₂ : ψ ⊢ χ) : disj φ ψ ⊢ χ :=
  Squash.lift h₁ fun p => Squash.lift h₂ fun q =>
    Squash.mk ⟨caseOf p.1 q.1, fun i c hc => by
      rcases hc with ⟨a, ha, hca⟩ | ⟨b, hb, hcb⟩
      · obtain ⟨d, hd, hd'⟩ := p.2 i a ha
        refine ⟨d, ?_, hd'⟩
        rw [caseOf_spec, ← Partial.eq_pure_of_mem hca, Tagging.inl_apply a p.1 q.1]
        exact hd
      · obtain ⟨d, hd, hd'⟩ := q.2 i b hb
        refine ⟨d, ?_, hd'⟩
        rw [caseOf_spec, ← Partial.eq_pure_of_mem hcb, Tagging.inr_apply b p.1 q.1]
        exact hd⟩

end

/-! ### The generic predicate (weak subobject classifier)

The realizability tripos is *generic*: there is a distinguished object of truth
values `Prop' A = 𝒫 A` carrying a predicate `generic`, through which every
predicate factors.  Because `Pred A I = I → 𝒫 A` definitionally, a predicate
`φ : Pred A I` *is* its own characteristic map `I → Prop' A`, and reindexing
`generic` along it recovers `φ` *on the nose* — comprehension holds as an
equality, not merely up to entailment. -/

/-- The generic predicate over `𝒫 A`: a realizer `a` realizes the "proposition"
`S : 𝒫 A` exactly when `a ∈ S`.  (As a function it is `id : 𝒫 A → 𝒫 A`.) -/
def generic : Pred A (Prop' A) := fun S a => S a

omit [PCA A] [Abstraction A] in
/-- **Comprehension.**  Every predicate `φ : Pred A I` is the reindexing of the
generic predicate along its characteristic map — and that map is `φ` itself,
since `Pred A I = I → Prop' A`.  The factorization is a definitional equality. -/
theorem subst_generic {I : Type w} (φ : Pred A I) :
    subst (J := Prop' A) φ generic = φ := rfl

end Pred

end LeanExperiments.Realizability
