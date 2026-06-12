import LeanExperiments.PCA.Basic

/-!
# Pairing combinators

A `Pairing` structure on a PCA: a pairing element `pair` with projections
`fst`, `snd` satisfying the β-laws `fst ⬝ (pair ⬝ a ⬝ b) = a` and
`snd ⬝ (pair ⬝ a ⬝ b) = b`.

This is a class (analogous to `Abstraction`) so that a PCA with *native* pairing
combinators can supply them directly.  It is **not** derived generically: the
pairing combinator is a three-variable term, beyond single-variable `abs`, so
over an abstract PCA it only exists as a `Prop`-level `∃` — not the data an
extraction-friendly model needs.
-/

namespace LeanExperiments

open scoped LeanExperiments.Partial LeanExperiments.PartialApp

universe u

/-- Pairing combinators on a PCA: a pairing element and its two projections,
satisfying the projection laws. -/
class Pairing (A : Type u) [PCA A] where
  /-- The pairing combinator: `pair ⬝ a ⬝ b` is the pair `⟨a, b⟩`. -/
  pair : A
  /-- First projection. -/
  fst : A
  /-- Second projection. -/
  snd : A
  /-- `fst ⬝ (pair ⬝ a ⬝ b) = a`. -/
  fst_pair : ∀ a b : A,
    (Partial.pure fst ⬝ (Partial.pure pair ⬝ Partial.pure a ⬝ Partial.pure b) : Partial A) =
      Partial.pure a
  /-- `snd ⬝ (pair ⬝ a ⬝ b) = b`. -/
  snd_pair : ∀ a b : A,
    (Partial.pure snd ⬝ (Partial.pure pair ⬝ Partial.pure a ⬝ Partial.pure b) : Partial A) =
      Partial.pure b

namespace Pairing

variable {A : Type u} [PCA A] [Pairing A]

/-- `pair ⬝ a ⬝ b` is always defined. -/
theorem pair_total (a b : A) :
    ∃ c, c ∈ (Partial.pure pair ⬝ Partial.pure a ⬝ Partial.pure b : Partial A) := by
  have h : a ∈ (Partial.pure fst ⬝
      (Partial.pure pair ⬝ Partial.pure a ⬝ Partial.pure b) : Partial A) := by
    rw [fst_pair a b]; exact Partial.mem_pure.mpr rfl
  rw [PartialApp.mem_applyP] at h
  obtain ⟨_, c, _, hc, _⟩ := h
  exact ⟨c, hc⟩

end Pairing

end LeanExperiments
