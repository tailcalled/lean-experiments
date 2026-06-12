import LeanExperiments.PCA.Basic

/-!
# Tagging combinators

A `Tagging` structure on a PCA: left/right injection combinators `inl`, `inr`
whose tagged values dispatch to the appropriate handler —

```
inl ⬝ a ⬝ f ⬝ g = f ⬝ a      inr ⬝ b ⬝ f ⬝ g = g ⬝ b
```

(`inl a = λf g. f a`, `inr b = λf g. g b`; case analysis is just applying the
tagged value to the two handlers — no separate `case` combinator needed.)

Like `Pairing`, this is a class (analogous to `Abstraction`) so a PCA with native
tagging can supply it; the closure model does so in `LambdaTagging`.
-/

namespace LeanExperiments

open scoped LeanExperiments.Partial LeanExperiments.PartialApp

universe u

/-- Tagging combinators: left/right injections that dispatch to handlers. -/
class Tagging (A : Type u) [PCA A] where
  /-- Left injection: `inl ⬝ a` is the left-tagged value. -/
  inl : A
  /-- Right injection: `inr ⬝ b` is the right-tagged value. -/
  inr : A
  /-- `inl ⬝ a ⬝ f ⬝ g = f ⬝ a`. -/
  inl_apply : ∀ a f g : A,
    (Partial.pure inl ⬝ Partial.pure a ⬝ Partial.pure f ⬝ Partial.pure g : Partial A) =
      Partial.pure f ⬝ Partial.pure a
  /-- `inr ⬝ b ⬝ f ⬝ g = g ⬝ b`. -/
  inr_apply : ∀ b f g : A,
    (Partial.pure inr ⬝ Partial.pure b ⬝ Partial.pure f ⬝ Partial.pure g : Partial A) =
      Partial.pure g ⬝ Partial.pure b

namespace Tagging

variable {A : Type u} [PCA A] [Tagging A]

omit [Tagging A] in
private theorem k_app_total (a : A) : (Partial.pure PCA.k ⬝ Partial.pure a : Partial A).Dom := by
  refine PartialApp.dom_of_applyP (p := Partial.pure PCA.k ⬝ Partial.pure a)
    (q := Partial.pure a) ?_
  rw [show (Partial.pure PCA.k ⬝ Partial.pure a ⬝ Partial.pure a : Partial A) = Partial.pure a by
    simpa using PCA.k_eq a a]
  exact ⟨a, Partial.mem_pure.mpr rfl⟩

/-- `inl ⬝ a` is always defined (a tagged value exists). -/
theorem inl_total (a : A) : ∃ c, c ∈ (Partial.pure inl ⬝ Partial.pure a : Partial A) := by
  have h1 : (Partial.pure inl ⬝ Partial.pure a ⬝ Partial.pure PCA.k ⬝ Partial.pure PCA.k
      : Partial A).Dom := by rw [inl_apply a PCA.k PCA.k]; exact k_app_total a
  exact PartialApp.dom_of_applyP (PartialApp.dom_of_applyP h1)

/-- `inr ⬝ b` is always defined. -/
theorem inr_total (b : A) : ∃ c, c ∈ (Partial.pure inr ⬝ Partial.pure b : Partial A) := by
  have h1 : (Partial.pure inr ⬝ Partial.pure b ⬝ Partial.pure PCA.k ⬝ Partial.pure PCA.k
      : Partial A).Dom := by rw [inr_apply b PCA.k PCA.k]; exact k_app_total b
  exact PartialApp.dom_of_applyP (PartialApp.dom_of_applyP h1)

end Tagging

end LeanExperiments
