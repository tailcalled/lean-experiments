import LeanExperiments.PCA.LambdaPairing
import LeanExperiments.PCA.Tagging

/-!
# Native tagging for the closure model

`inl = λa f g. f a`, `inr = λb f g. g b`, as actual λ-terms; the dispatch laws
are proved by computing with the gas interpreter (`simp` over the `evalP`
reduction lemmas), just like pairing.
-/

namespace LeanExperiments.Lambda

open LeanExperiments
open scoped LeanExperiments.Partial LeanExperiments.PartialApp

/-- `inl = λa f g. f a`. -/
def inlV : Value :=
  .closure "a" (.lam "f" (.lam "g" (.app (.var "f") (.var "a")))) []

/-- `inr = λb f g. g b`. -/
def inrV : Value :=
  .closure "b" (.lam "f" (.lam "g" (.app (.var "g") (.var "b")))) []

theorem inl_applyV (a f g : Value) :
    (Partial.pure inlV ⬝ Partial.pure a ⬝ Partial.pure f ⬝ Partial.pure g : Partial Value) =
      Partial.pure f ⬝ Partial.pure a := by
  simp [inlV, pure_closure_app, evalC_app_eq]

theorem inr_applyV (b f g : Value) :
    (Partial.pure inrV ⬝ Partial.pure b ⬝ Partial.pure f ⬝ Partial.pure g : Partial Value) =
      Partial.pure g ⬝ Partial.pure b := by
  simp [inrV, pure_closure_app, evalC_app_eq]

/-- The closure model has native tagging. -/
instance : Tagging Value where
  inl := inlV
  inr := inrV
  inl_apply := inl_applyV
  inr_apply := inr_applyV

end LeanExperiments.Lambda
