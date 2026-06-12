import LeanExperiments.Realizability
import LeanExperiments.PCA.Pairing

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

universe u w

variable {A : Type u} [PCA A] [Abstraction A]

/-- A predicate over `I`, valued in sets of realizers. -/
def Pred (A : Type u) (I : Type w) : Type (max u w) := I → A → Prop

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
def subst (f : I → J) (ψ : Pred A J) : Pred A I := fun i => ψ (f i)

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

end

end Pred

end LeanExperiments.Realizability
