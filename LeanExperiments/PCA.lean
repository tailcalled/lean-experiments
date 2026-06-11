import LeanExperiments.PCA.Basic
import LeanExperiments.PCA.Lambda

/-!
# Partial combinatory algebras

This module collects the PCA development:

* `LeanExperiments.PCA.Basic`  — the `PartialApp` and `PCA` classes, the
  lifted application `⬝`, and the derived identity combinator `i = s k k`.
* `LeanExperiments.PCA.Lambda` — the first concrete PCA: the closure model of
  the untyped λ-calculus (named variables, environment semantics).
-/
