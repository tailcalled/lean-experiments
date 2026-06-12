import LeanExperiments.PCA.Partial
import LeanExperiments.PCA.Basic
import LeanExperiments.PCA.Abstraction
import LeanExperiments.PCA.Lambda
import LeanExperiments.PCA.LambdaAbs
import LeanExperiments.PCA.Pairing
import LeanExperiments.PCA.LambdaPairing

/-!
# Partial combinatory algebras (computable)

This module collects the PCA development.  Partiality is modeled with a
*computable* gas monad rather than `Classical`-flavored `Part`, so concrete
models genuinely run (`#eval`-able); nothing is `noncomputable`.

* `LeanExperiments.PCA.Partial` — the partiality monad: raw gas computations
  `Nat → Option (Nat × α)`, the *valid* subset `PComp` (monotone gas-threading,
  with leftover ≤ budget), and the quotient `Partial` by Kleene equality.
* `LeanExperiments.PCA.Basic`   — the `PartialApp` and `PCA` classes, the lifted
  application `⬝`, and the derived identity combinator `i = s k k`.
* `LeanExperiments.PCA.Abstraction` — applicative expressions `Expr A` with named
  variables, and generic `s`/`k` bracket abstraction with combinatory
  completeness (`bracket_correct`).
* `LeanExperiments.PCA.Lambda`  — the first concrete PCA: the closure model of
  the untyped λ-calculus (named variables, environment semantics), with
  application realized by a gas interpreter `eval`.
* `LeanExperiments.PCA.LambdaAbs` — the closure model's *name-preserving*
  `Abstraction` instance: `abs "x" e` builds a real `closure "x" …`, capturing
  embedded constants under freshly generated env names.
* `LeanExperiments.PCA.Pairing` — the `Pairing` class (pairing combinator +
  projections), with the closure model's native instance in `LambdaPairing`.
-/
