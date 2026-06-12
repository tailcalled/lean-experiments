import LeanExperiments.PCA.LambdaAbs
import LeanExperiments.PCA.Pairing

/-!
# Native pairing for the closure model

The closure λ-model has pairing combinators built in (they are just λ-terms), so
we supply a `Pairing Value` instance directly:

* `pair = λx y f. f x y`,
* `fst  = λc. c (λu v. u)`,
* `snd  = λc. c (λu v. v)`.

The β-laws are proved by computing with the gas interpreter, reduced to a `simp`
over the `evalP` reduction lemmas.
-/

namespace LeanExperiments.Lambda

open LeanExperiments
open scoped LeanExperiments.Partial LeanExperiments.PartialApp

/-- Evaluating a `lam` yields its closure. -/
@[simp] theorem evalP_lam (env : Env) (x : Var) (b : Term) :
    evalP env (.lam x b) = Partial.pure (.closure x b env) := by
  apply Partial.ext; intro w
  simp only [evalP, Partial.mem_mk, mem_evalC_lam, Partial.mem_pure]

/-- Evaluating a variable walks the environment. -/
@[simp] theorem evalP_var_cons (y : Var) (v : Value) (rest : Env) (x : Var) :
    evalP ((y, v) :: rest) (.var x) =
      if x = y then Partial.pure v else evalP rest (.var x) := by
  by_cases h : x = y
  · subst h; rw [if_pos rfl, evalP_var_of_lookup (by rw [lookup_cons, if_pos rfl])]
  · rw [if_neg h]
    apply Partial.ext; intro w
    simp [evalP, Partial.mem_mk, mem_evalC_var, lookup_cons, h]

/-- `pair = λx y f. f x y`. -/
def pairV : Value :=
  .closure "x" (.lam "y" (.lam "f" (.app (.app (.var "f") (.var "x")) (.var "y")))) []

/-- `fst = λc. c (λu v. u)`. -/
def fstV : Value := .closure "c" (.app (.var "c") (.lam "u" (.lam "v" (.var "u")))) []

/-- `snd = λc. c (λu v. v)`. -/
def sndV : Value := .closure "c" (.app (.var "c") (.lam "u" (.lam "v" (.var "v")))) []

theorem fst_pairV (a b : Value) :
    (Partial.pure fstV ⬝ (Partial.pure pairV ⬝ Partial.pure a ⬝ Partial.pure b) : Partial Value) =
      Partial.pure a := by
  simp [pairV, fstV, pure_closure_app, evalC_app_eq]

theorem snd_pairV (a b : Value) :
    (Partial.pure sndV ⬝ (Partial.pure pairV ⬝ Partial.pure a ⬝ Partial.pure b) : Partial Value) =
      Partial.pure b := by
  simp [pairV, sndV, pure_closure_app, evalC_app_eq]

/-- The closure model has native pairing. -/
instance : Pairing Value where
  pair := pairV
  fst := fstV
  snd := sndV
  fst_pair := fst_pairV
  snd_pair := snd_pairV

end LeanExperiments.Lambda
