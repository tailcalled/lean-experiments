import LeanExperiments.PCA.Partial
import LeanExperiments.PCA.Basic
import LeanExperiments.PCA.Lambda

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
* `LeanExperiments.PCA.Lambda`  — the first concrete PCA: the closure model of
  the untyped λ-calculus (named variables, environment semantics), with
  application realized by a gas interpreter `eval`.
-/
