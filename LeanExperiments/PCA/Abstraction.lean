import LeanExperiments.PCA.Basic

/-!
# Expressions and bracket abstraction

To express *combinatory completeness* — every function defined by an applicative
expression is realized by an element — we need a syntax of expressions over a
PCA:

* `Expr A` — applicative expressions with **named variables**, constants from
  `A`, and application.
* `Expr.denote ρ e` — the partial value an expression denotes in an environment.
* `Expr.bracket x e` — the generic `s`/`k` *bracket abstraction* removing `x`.

The headline result is `bracket_correct`:
`denote ρ (bracket x e) ⬝ a = denote (ρ[x ↦ a]) e`.

This bracket compiles to `s`/`k`; a PCA may override it with a name-preserving
abstraction (the `abs` field of `PCA`).
-/

namespace LeanExperiments

open scoped LeanExperiments.Partial LeanExperiments.PartialApp

universe u

/-- Applicative expressions over a carrier `A`: named variables, constants, and
application. -/
inductive Expr (A : Type u) where
  | var : String → Expr A
  | const : A → Expr A
  | app : Expr A → Expr A → Expr A
  deriving Inhabited

namespace Expr

variable {A : Type u}

/-- The partial value denoted by an expression under an environment. -/
def denote [PartialApp A] (ρ : String → A) : Expr A → Partial A
  | .var x => Partial.pure (ρ x)
  | .const c => Partial.pure c
  | .app e₁ e₂ => denote ρ e₁ ⬝ denote ρ e₂

@[simp] theorem denote_var [PartialApp A] (ρ : String → A) (x : String) :
    denote ρ (.var x) = Partial.pure (ρ x) := rfl

@[simp] theorem denote_const [PartialApp A] (ρ : String → A) (c : A) :
    denote ρ (.const c) = Partial.pure c := rfl

@[simp] theorem denote_app [PartialApp A] (ρ : String → A) (e₁ e₂ : Expr A) :
    denote ρ (.app e₁ e₂) = denote ρ e₁ ⬝ denote ρ e₂ := rfl

/-- The free variables of an expression. -/
def fvE : Expr A → List String
  | .var x => [x]
  | .const _ => []
  | .app e₁ e₂ => fvE e₁ ++ fvE e₂

/-- An expression has at most the single free variable `x`. -/
def closed1 (x : String) (e : Expr A) : Prop := ∀ y ∈ fvE e, y = x

theorem closed1_app {x : String} {e₁ e₂ : Expr A} (h : closed1 x (.app e₁ e₂)) :
    closed1 x e₁ ∧ closed1 x e₂ :=
  ⟨fun y hy => h y (List.mem_append.mpr (Or.inl hy)),
   fun y hy => h y (List.mem_append.mpr (Or.inr hy))⟩

/-- Update an environment at a single variable. -/
def update (ρ : String → A) (x : String) (a : A) : String → A :=
  fun y => if y = x then a else ρ y

@[simp] theorem update_same (ρ : String → A) (x : String) (a : A) : update ρ x a x = a := by
  simp [update]

theorem update_noteq {x y : String} (ρ : String → A) (a : A) (h : y ≠ x) :
    update ρ x a y = ρ y := by simp only [update, if_neg h]

section
variable [PCA A]
open PCA (k s k_eq s_dom s_eq)

/-! ### The combinator laws in `pure` form -/

theorem k_eq_pure (a b : A) :
    (Partial.pure (k : A) ⬝ Partial.pure a ⬝ Partial.pure b : Partial A) = Partial.pure a := by
  simpa using k_eq a b

theorem s_dom_pure (a b : A) :
    (Partial.pure (s : A) ⬝ Partial.pure a ⬝ Partial.pure b : Partial A).Dom := by
  simpa using s_dom a b

theorem s_eq_pure (a b c : A) :
    (Partial.pure (s : A) ⬝ Partial.pure a ⬝ Partial.pure b ⬝ Partial.pure c : Partial A) =
      (Partial.pure a ⬝ Partial.pure c) ⬝ (Partial.pure b ⬝ Partial.pure c) := by
  simpa using s_eq a b c

theorem i_app_pure (a : A) :
    ((Partial.pure (s : A) ⬝ Partial.pure k) ⬝ Partial.pure k) ⬝ Partial.pure a =
      Partial.pure a := by
  simpa [Combinator.i] using Combinator.i_app a

/-! ### Bracket abstraction -/

/-- Generic bracket abstraction `⟨x⟩e`, compiling to `s`/`k`. -/
def bracket (x : String) : Expr A → Expr A
  | .var y => if y = x then .app (.app (.const s) (.const k)) (.const k)
              else .app (.const k) (.var y)
  | .const c => .app (.const k) (.const c)
  | .app e₁ e₂ => .app (.app (.const s) (bracket x e₁)) (bracket x e₂)

/-- If a composite application is defined, its operator is defined. -/
theorem exists_mem_left {p q : Partial A} (h : (p ⬝ q).Dom) : ∃ f, f ∈ p := by
  obtain ⟨w, hw⟩ := h
  rw [PartialApp.mem_applyP] at hw
  obtain ⟨f, _, hf, _, _⟩ := hw
  exact ⟨f, hf⟩

/-- The denotation of a bracket abstraction is always total: `pure` of the
realizer element. -/
theorem bracket_total (x : String) (e : Expr A) (ρ : String → A) :
    ∃ b, denote ρ (bracket x e) = Partial.pure b := by
  induction e with
  | var y =>
    by_cases h : y = x
    · subst h
      have hd : ((Partial.pure (s : A) ⬝ Partial.pure k) ⬝ Partial.pure k ⬝ Partial.pure k
          : Partial A).Dom := by rw [i_app_pure k]; exact ⟨k, Partial.mem_pure.mpr rfl⟩
      obtain ⟨f, hf⟩ := exists_mem_left hd
      refine ⟨f, ?_⟩
      simp only [bracket]
      exact Partial.eq_pure_of_mem hf
    · have hd : ((Partial.pure (k : A) ⬝ Partial.pure (ρ y)) ⬝ Partial.pure (ρ y)
          : Partial A).Dom := by rw [k_eq_pure (ρ y) (ρ y)]; exact ⟨ρ y, Partial.mem_pure.mpr rfl⟩
      obtain ⟨f, hf⟩ := exists_mem_left hd
      refine ⟨f, ?_⟩
      simp only [bracket, if_neg h, denote_app, denote_const, denote_var]
      exact Partial.eq_pure_of_mem hf
  | const c =>
    have hd : ((Partial.pure (k : A) ⬝ Partial.pure c) ⬝ Partial.pure c : Partial A).Dom := by
      rw [k_eq_pure c c]; exact ⟨c, Partial.mem_pure.mpr rfl⟩
    obtain ⟨f, hf⟩ := exists_mem_left hd
    refine ⟨f, ?_⟩
    simp only [bracket, denote_app, denote_const]
    exact Partial.eq_pure_of_mem hf
  | app e₁ e₂ ih₁ ih₂ =>
    obtain ⟨b₁, hb₁⟩ := ih₁
    obtain ⟨b₂, hb₂⟩ := ih₂
    obtain ⟨w, hw⟩ := s_dom_pure b₁ b₂
    refine ⟨w, ?_⟩
    simp only [bracket, denote_app, denote_const, hb₁, hb₂]
    exact Partial.eq_pure_of_mem hw

/-- **Combinatory completeness.** `bracket x e` realizes the function `a ↦ e` of
`x`: applying it to `a` denotes `e` with `x` bound to `a`. -/
theorem bracket_correct (x : String) (e : Expr A) (a : A) (ρ : String → A) :
    (denote ρ (bracket x e)) ⬝ Partial.pure a = denote (update ρ x a) e := by
  induction e with
  | var y =>
    by_cases h : y = x
    · subst h
      simp only [bracket, denote_var, update_same]
      exact i_app_pure a
    · simp only [bracket, if_neg h, denote_app, denote_const, denote_var,
        update_noteq ρ a h]
      exact k_eq_pure (ρ y) a
  | const c =>
    simp only [bracket, denote_app, denote_const]
    exact k_eq_pure c a
  | app e₁ e₂ ih₁ ih₂ =>
    obtain ⟨b₁, hb₁⟩ := bracket_total x e₁ ρ
    obtain ⟨b₂, hb₂⟩ := bracket_total x e₂ ρ
    show (denote ρ (.app (.app (.const s) (bracket x e₁)) (bracket x e₂))) ⬝ Partial.pure a = _
    simp only [denote_app, denote_const, hb₁, hb₂]
    rw [s_eq_pure b₁ b₂ a, ← hb₁, ← hb₂, ih₁, ih₂]

/-- `bracket y` removes exactly `y` from the free variables. -/
theorem fvE_bracket (y : String) (e : Expr A) {z : String} (hz : z ∈ fvE (bracket y e)) :
    z ∈ fvE e ∧ z ≠ y := by
  induction e with
  | var w =>
    by_cases h : w = y
    · subst h; simp [bracket, fvE] at hz
    · simp only [bracket, if_neg h, fvE, List.mem_append, List.not_mem_nil,
        List.mem_singleton, false_or] at hz
      subst hz; exact ⟨by simp [fvE], h⟩
  | const c => simp [bracket, fvE] at hz
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [bracket, fvE, List.mem_append, List.not_mem_nil, false_or] at hz
    rcases hz with hz | hz
    · obtain ⟨h₁, h₂⟩ := ih₁ hz; exact ⟨by simp [fvE, h₁], h₂⟩
    · obtain ⟨h₁, h₂⟩ := ih₂ hz; exact ⟨by simp [fvE, h₁], h₂⟩

/-- If `e`'s free variables are among `{x, y}`, then `bracket y e` has at most
`x` free. -/
theorem closed1_bracket {x y : String} {e : Expr A}
    (hc : ∀ z ∈ fvE e, z = x ∨ z = y) : closed1 x (bracket y e) := by
  intro z hz
  obtain ⟨h₁, h₂⟩ := fvE_bracket y e hz
  rcases hc z h₁ with h | h
  · exact h
  · exact absurd h h₂

end

end Expr

open scoped LeanExperiments.PartialApp

/-- An *abstraction operator* on a PCA: a name-aware way to turn an expression
into a realizer of the corresponding function.  The generic `s`/`k` bracket is
one implementation (see `Expr.bracket`); a model may override it — e.g. the
closure model builds a real named `lam`, so the parameter name survives.  -/
class Abstraction (A : Type u) [PCA A] where
  /-- Abstract the variable `x` out of `e`, producing a realizer element. -/
  abs : String → Expr A → A
  /-- `abs x e` realizes `a ↦ e` of `x` (for `e` with at most `x` free). -/
  abs_spec : ∀ (x : String) (e : Expr A), Expr.closed1 x e → ∀ (a : A) (ρ : String → A),
    (Partial.pure (abs x e) ⬝ Partial.pure a : Partial A) = e.denote (Expr.update ρ x a)

/-! ### Multi-variable abstraction

Derived from single-variable `abs` by bracket-abstracting the *inner* variables
first (so only the outer one is left free), then `abs`-ing the outer one.  The
spec composes `abs_spec` with `bracket_correct`. -/

section
variable {A : Type u} [PCA A] [Abstraction A]
open scoped LeanExperiments.PartialApp

/-- Two-variable abstraction `λx y. e`. -/
def abs2 (x y : String) (e : Expr A) : A := Abstraction.abs x (Expr.bracket y e)

theorem abs2_spec (x y : String) (e : Expr A) (hc : ∀ z ∈ Expr.fvE e, z = x ∨ z = y)
    (a b : A) (ρ : String → A) :
    (Partial.pure (abs2 x y e) ⬝ Partial.pure a ⬝ Partial.pure b : Partial A) =
      e.denote (Expr.update (Expr.update ρ x a) y b) := by
  rw [abs2, Abstraction.abs_spec x (Expr.bracket y e) (Expr.closed1_bracket hc) a ρ]
  exact Expr.bracket_correct y e b (Expr.update ρ x a)

/-- The first application of a two-variable abstraction is already total. -/
theorem abs2_app1 (x y : String) (e : Expr A) (hc : ∀ z ∈ Expr.fvE e, z = x ∨ z = y)
    (a : A) (ρ : String → A) :
    ∃ f, (Partial.pure (abs2 x y e) ⬝ Partial.pure a : Partial A) = Partial.pure f := by
  rw [abs2, Abstraction.abs_spec x (Expr.bracket y e) (Expr.closed1_bracket hc) a ρ]
  exact Expr.bracket_total y e (Expr.update ρ x a)

/-- Three-variable abstraction `λx y z. e`. -/
def abs3 (x y z : String) (e : Expr A) : A :=
  Abstraction.abs x (Expr.bracket y (Expr.bracket z e))

theorem abs3_spec (x y z : String) (e : Expr A)
    (hc : ∀ w ∈ Expr.fvE e, w = x ∨ w = y ∨ w = z) (a b c : A) (ρ : String → A) :
    (Partial.pure (abs3 x y z e) ⬝ Partial.pure a ⬝ Partial.pure b ⬝ Partial.pure c : Partial A) =
      e.denote (Expr.update (Expr.update (Expr.update ρ x a) y b) z c) := by
  have hc' : ∀ w ∈ Expr.fvE (Expr.bracket z e), w = x ∨ w = y := by
    intro w hw
    obtain ⟨h₁, h₂⟩ := Expr.fvE_bracket z e hw
    rcases hc w h₁ with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h h₂
  rw [abs3,
    Abstraction.abs_spec x (Expr.bracket y (Expr.bracket z e)) (Expr.closed1_bracket hc') a ρ,
    Expr.bracket_correct y (Expr.bracket z e) b (Expr.update ρ x a)]
  exact Expr.bracket_correct z e c (Expr.update (Expr.update ρ x a) y b)

end

end LeanExperiments
