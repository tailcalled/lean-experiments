import Mathlib.Data.Part

/-!
# Partial combinatory algebras

A *partial combinatory algebra* (PCA) is the algebraic structure underlying
Kleene realizability: a carrier `A` equipped with a *partial* binary
application together with two distinguished elements `k` and `s` from which
every (partial) "computable" function on `A` can be built (combinatory
completeness).

We model partiality with Mathlib's `Part`, so application has type
`A → A → Part A`.  Two partial values are Kleene-equal exactly when they are
equal as `Part`s, so we can phrase the combinator laws with ordinary `=`.

This file sets up:

* `PartialApp`  — a carrier with partial application `· ⬝ ·`;
* `applyP`      — application lifted to partial values, with notation `⬝`;
* `PCA`         — the combinator axioms for `k` and `s`.

Concrete instances (starting with the term model of the untyped λ-calculus)
live in the sibling files.
-/

namespace LeanExperiments

universe u

/-- A *partial applicative structure*: a carrier with a partial binary
application operation.  This is the data underlying a PCA, before imposing
any axioms. -/
class PartialApp (A : Type u) where
  /-- Partial application of one element to another. -/
  app : A → A → Part A

namespace PartialApp

variable {A : Type u} [PartialApp A]

/-- Application lifted to partial values, in the Kleene sense: `p ⬝ q` is
defined only when both `p` and `q` are, and then applies the value of `p` to
the value of `q`. -/
def applyP (p q : Part A) : Part A :=
  p.bind fun f => q.bind fun a => app f a

@[inherit_doc] scoped infixl:70 " ⬝ " => applyP

/-- Coerce an element to the partial value that is always defined with that
value.  Lets us write mixed expressions like `k ⬝ a ⬝ b`. -/
scoped instance : CoeTail A (Part A) := ⟨Part.some⟩

omit [PartialApp A] in
/-- The coercion `↑a` of an element is the always-defined partial value `some a`. -/
@[simp] theorem coe_def (a : A) : (↑a : Part A) = Part.some a := rfl

@[simp] theorem applyP_some_some (f a : A) :
    (Part.some f) ⬝ (Part.some a) = app f a := by
  simp [applyP]

theorem applyP_dom {p q : Part A} (h : (p ⬝ q).Dom) : p.Dom ∧ q.Dom := by
  rcases h with ⟨hp, hq, -⟩
  exact ⟨hp, hq⟩

end PartialApp

open scoped PartialApp

/-- A *partial combinatory algebra*: a partial applicative structure with
combinators `k` and `s` satisfying the usual laws.  `k` projects to its first
argument, and `s` is the "substitution"/distribution combinator.  Note that
`s ⬝ a ⬝ b` must always be defined (it represents the partial function
`c ↦ (a ⬝ c) ⬝ (b ⬝ c)` waiting for its argument), whereas the right-hand side
of `s_eq` may diverge. -/
class PCA (A : Type u) extends PartialApp A where
  /-- The projection combinator. -/
  k : A
  /-- The substitution combinator. -/
  s : A
  /-- `k ⬝ a ⬝ b = a` (which forces `k ⬝ a` to be defined). -/
  k_eq : ∀ a b : A, (k : Part A) ⬝ a ⬝ b = Part.some a
  /-- `s ⬝ a ⬝ b` is always defined. -/
  s_dom : ∀ a b : A, ((s : Part A) ⬝ a ⬝ b).Dom
  /-- `s ⬝ a ⬝ b ⬝ c = (a ⬝ c) ⬝ (b ⬝ c)` (Kleene equality). -/
  s_eq : ∀ a b c : A,
    (s : Part A) ⬝ a ⬝ b ⬝ c = ((a : Part A) ⬝ c) ⬝ ((b : Part A) ⬝ c)

namespace Combinator

open scoped PartialApp
open PartialApp (applyP_dom applyP_some_some)
open PCA (k s k_eq s_eq)

variable {A : Type u} [PCA A]

/-- The identity combinator `i = s k k`, as a partial value.  This is the first
example of *combinatory completeness*: a term built from `s` and `k` that
realizes a specific function (here, the identity). -/
def i : Part A := ((s : A) ⬝ (k : A) ⬝ (k : A) : Part A)

/-- `i` is indeed the identity: `i ⬝ a = a` for every `a`. -/
theorem i_app (a : A) : (i : Part A) ⬝ a = Part.some a := by
  show ((s : A) ⬝ (k : A) ⬝ (k : A)) ⬝ a = Part.some a
  rw [s_eq k k a]
  have hdom : (((k : A) : Part A) ⬝ (a : A)).Dom := by
    have h : ((((k : A) : Part A) ⬝ a) ⬝ a).Dom := by rw [k_eq a a]; trivial
    exact (applyP_dom h).1
  obtain ⟨ka, hka⟩ := Part.dom_iff_mem.mp hdom
  have hsome : (((k : A) : Part A) ⬝ a) = Part.some ka := Part.eq_some_iff.mpr hka
  have h2 := k_eq a ka
  rw [hsome] at h2 ⊢
  simpa using h2

end Combinator

end LeanExperiments
