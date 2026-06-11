import LeanExperiments.PCA.Basic

/-!
# The closure model of the untyped λ-calculus as a PCA

This is the first concrete partial combinatory algebra: the term model of the
untyped λ-calculus, presented with **named variables** and a **closure /
environment** operational semantics.  Crucially we never substitute under a
`lam`; instead a `lam` evaluates to a *closure* that captures its defining
environment, and application extends that environment.

* `Term`   — λ-terms with named variables (`Var := String`).
* `Value`  — the values: closures `⟨x, body, env⟩`.
* `Eval`   — big-step evaluation `env ⊢ t ⇓ v`, a deterministic relation.
* `appV`   — application of values; *partial*, since evaluation may diverge.

The carrier of the PCA is `Value`, with `k` and `s` the closures of the usual
λ-terms `λx y. x` and `λx y z. x z (y z)`.  Because application is genuinely
partial here, this is a PCA in the full sense (not merely a total combinatory
algebra).
-/

namespace LeanExperiments.Lambda

open LeanExperiments
open scoped LeanExperiments.PartialApp

/-- Variables are just names. -/
abbrev Var := String

/-- λ-terms with named variables. -/
inductive Term where
  | var : Var → Term
  | lam : Var → Term → Term
  | app : Term → Term → Term
deriving Repr, DecidableEq

/-- Values are closures: a bound variable, a body, and a captured environment.
Environments are association lists from variables to values. -/
inductive Value where
  | closure : Var → Term → List (Var × Value) → Value
deriving Repr

/-- Environments map variables to values. -/
abbrev Env := List (Var × Value)

/-- Look a variable up in an environment (most recent binding wins). -/
def lookup : Env → Var → Option Value
  | [], _ => none
  | (y, v) :: rest, x => if x = y then some v else lookup rest x

/-- Big-step evaluation `env ⊢ t ⇓ v` in the closure semantics. -/
inductive Eval : Env → Term → Value → Prop where
  | var {env x v} : lookup env x = some v → Eval env (.var x) v
  | lam {env x b} : Eval env (.lam x b) (.closure x b env)
  | app {env f a x b cenv av rv} :
      Eval env f (.closure x b cenv) →
      Eval env a av →
      Eval ((x, av) :: cenv) b rv →
      Eval env (.app f a) rv

@[simp] theorem eval_var_iff {env x v} :
    Eval env (.var x) v ↔ lookup env x = some v := by
  constructor
  · intro h; cases h with | var h => exact h
  · intro h; exact .var h

@[simp] theorem eval_lam_iff {env x b v} :
    Eval env (.lam x b) v ↔ v = .closure x b env := by
  constructor
  · intro h; cases h with | lam => rfl
  · rintro rfl; exact .lam

theorem eval_app_iff {env f a rv} :
    Eval env (.app f a) rv ↔
      ∃ x b cenv av, Eval env f (.closure x b cenv) ∧ Eval env a av ∧
        Eval ((x, av) :: cenv) b rv := by
  constructor
  · intro h
    cases h with
    | app hf ha hb => exact ⟨_, _, _, _, hf, ha, hb⟩
  · rintro ⟨x, b, cenv, av, hf, ha, hb⟩
    exact .app hf ha hb

/-- Application of values: apply the closure `vf` to the argument `va` by
evaluating the body in the extended environment.  Defined exactly when that
evaluation converges. -/
def Apply : Value → Value → Value → Prop
  | .closure x b cenv, va, v => Eval ((x, va) :: cenv) b v

/-- Evaluating the application of two variables is exactly applying their
looked-up values. -/
theorem eval_app_var {env : Env} {p q : Var} {vp vq val : Value}
    (hp : lookup env p = some vp) (hq : lookup env q = some vq) :
    Eval env (.app (.var p) (.var q)) val ↔ Apply vp vq val := by
  rw [eval_app_iff]
  constructor
  · rintro ⟨x, b, c, av, hf, ha, hb⟩
    rw [eval_var_iff, hp] at hf
    rw [eval_var_iff, hq] at ha
    obtain rfl := Option.some.inj hf
    obtain rfl := Option.some.inj ha
    exact hb
  · intro h
    cases vp with
    | closure x b c =>
      exact ⟨x, b, c, vq, by rw [eval_var_iff]; exact hp,
        by rw [eval_var_iff]; exact hq, h⟩

/-- Evaluation is deterministic. -/
theorem Eval.det {env : Env} {t : Term} {v₁ v₂ : Value}
    (h₁ : Eval env t v₁) (h₂ : Eval env t v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | var hl =>
      cases h₂ with
      | var hl2 => rw [hl] at hl2; exact Option.some.inj hl2
  | lam =>
      cases h₂ with
      | lam => rfl
  | app _ _ _ ihf iha ihb =>
      cases h₂ with
      | app hf2 ha2 hb2 =>
          have e1 := ihf hf2
          have e2 := iha ha2
          injection e1 with ex eb ec
          subst ex; subst eb; subst ec; subst e2
          exact ihb hb2

theorem Apply.det {vf va v₁ v₂ : Value}
    (h₁ : Apply vf va v₁) (h₂ : Apply vf va v₂) : v₁ = v₂ := by
  cases vf with
  | closure x b cenv => exact Eval.det h₁ h₂

/-- The partial application underlying the PCA.  `appV vf va` is the (unique, by
determinism) result of applying `vf` to `va`, and is undefined when no such
result exists. -/
noncomputable def appV (vf va : Value) : Part Value :=
  haveI : Decidable (∃ v, Apply vf va v) := Classical.dec _
  if h : ∃ v, Apply vf va v then Part.some h.choose else Part.none

theorem mem_appV {vf va v : Value} : v ∈ appV vf va ↔ Apply vf va v := by
  unfold appV
  split
  · next h =>
      rw [Part.mem_some_iff]
      constructor
      · rintro rfl; exact h.choose_spec
      · intro hv; exact Apply.det hv h.choose_spec
  · next h =>
      simp only [Part.notMem_none, false_iff]
      intro hv; exact h ⟨v, hv⟩

noncomputable instance : PartialApp Value := ⟨appV⟩

@[simp] theorem app_def (a b : Value) : PartialApp.app a b = appV a b := rfl

/-! ### Membership through lifted application -/

theorem mem_applyP {p q : Part Value} {w : Value} :
    w ∈ (p ⬝ q) ↔ ∃ f a, f ∈ p ∧ a ∈ q ∧ Apply f a w := by
  unfold PartialApp.applyP
  simp only [Part.mem_bind_iff, app_def, mem_appV]
  constructor
  · rintro ⟨f, hf, a, ha, h⟩; exact ⟨f, a, hf, ha, h⟩
  · rintro ⟨f, a, hf, ha, h⟩; exact ⟨f, hf, a, ha, h⟩

theorem mem_coe_coe {x z w : Value} :
    w ∈ ((↑x : Part Value) ⬝ ↑z) ↔ Apply x z w := by
  rw [mem_applyP]; simp [Part.mem_some_iff]

theorem mem_coe_app {p : Part Value} {z w : Value} :
    w ∈ (p ⬝ (↑z : Part Value)) ↔ ∃ u, u ∈ p ∧ Apply u z w := by
  rw [mem_applyP]; simp [Part.mem_some_iff]

/-! ### The combinators -/

/-- `k = λx y. x`. -/
def K : Value := .closure "x" (.lam "y" (.var "x")) []

/-- The body of `s`, i.e. `x z (y z)`. -/
def Sbody : Term :=
  .app (.app (.var "x") (.var "z")) (.app (.var "y") (.var "z"))

/-- `s = λx y z. x z (y z)`. -/
def S : Value := .closure "x" (.lam "y" (.lam "z" Sbody)) []

theorem Apply_K (a u : Value) :
    Apply K a u ↔ u = .closure "y" (.var "x") [("x", a)] := by
  simp [Apply, K]

theorem Apply_Kcl (a b w : Value) :
    Apply (.closure "y" (.var "x") [("x", a)]) b w ↔ w = a := by
  simp [Apply, lookup, eq_comm]

theorem Apply_S (a u : Value) :
    Apply S a u ↔ u = .closure "y" (.lam "z" Sbody) [("x", a)] := by
  simp [Apply, S]

theorem Apply_Sacl (a b u : Value) :
    Apply (.closure "y" (.lam "z" Sbody) [("x", a)]) b u ↔
      u = .closure "z" Sbody [("y", b), ("x", a)] := by
  simp [Apply]

/-- The defining computation of `s`: applying the fully-saturated closure
`s ⬝ a ⬝ b` to `c` distributes as `(a ⬝ c) ⬝ (b ⬝ c)`. -/
theorem Apply_Sabcl (a b c w : Value) :
    Apply (.closure "z" Sbody [("y", b), ("x", a)]) c w ↔
      ∃ l r, Apply a c l ∧ Apply b c r ∧ Apply l r w := by
  show Eval [("z", c), ("y", b), ("x", a)] Sbody w ↔ _
  have hx : lookup [("z", c), ("y", b), ("x", a)] "x" = some a := by simp [lookup]
  have hy : lookup [("z", c), ("y", b), ("x", a)] "y" = some b := by simp [lookup]
  have hz : lookup [("z", c), ("y", b), ("x", a)] "z" = some c := by simp [lookup]
  rw [Sbody, eval_app_iff]
  constructor
  · rintro ⟨x, b', cenv, av, hf, ha, hb⟩
    have hf' := (eval_app_var hx hz).mp hf
    have ha' := (eval_app_var hy hz).mp ha
    exact ⟨.closure x b' cenv, av, hf', ha', hb⟩
  · rintro ⟨l, r, hl, hr, hlr⟩
    cases l with
    | closure xl bl cl =>
      exact ⟨xl, bl, cl, r, (eval_app_var hx hz).mpr hl,
        (eval_app_var hy hz).mpr hr, hlr⟩

/-! ### The PCA instance -/

noncomputable instance : PCA Value where
  k := K
  s := S
  k_eq := by
    intro a b
    apply Part.ext
    intro w
    rw [Part.mem_some_iff, mem_coe_app]
    constructor
    · rintro ⟨u, hu, hub⟩
      rw [mem_coe_coe, Apply_K] at hu
      subst hu
      rw [Apply_Kcl] at hub
      exact hub
    · intro hwa
      subst w
      exact ⟨_, mem_coe_coe.mpr ((Apply_K a _).mpr rfl), (Apply_Kcl a b a).mpr rfl⟩
  s_dom := by
    intro a b
    rw [Part.dom_iff_mem]
    exact ⟨_, mem_coe_app.mpr
      ⟨_, mem_coe_coe.mpr ((Apply_S a _).mpr rfl), (Apply_Sacl a b _).mpr rfl⟩⟩
  s_eq := by
    intro a b c
    apply Part.ext
    intro w
    rw [mem_coe_app]
    -- left side: ∃ u, u ∈ (↑s ⬝ ↑a ⬝ ↑b) ∧ Apply u c w
    have hleft : (∃ u, u ∈ ((↑S : Part Value) ⬝ ↑a ⬝ ↑b) ∧ Apply u c w) ↔
        Apply (.closure "z" Sbody [("y", b), ("x", a)]) c w := by
      constructor
      · rintro ⟨u, hu, huc⟩
        rw [mem_coe_app] at hu
        obtain ⟨u2, hu2, hu2b⟩ := hu
        rw [mem_coe_coe, Apply_S] at hu2
        subst hu2
        rw [Apply_Sacl] at hu2b
        subst hu2b
        exact huc
      · intro h
        exact ⟨_, by
          rw [mem_coe_app]
          exact ⟨_, mem_coe_coe.mpr ((Apply_S a _).mpr rfl), (Apply_Sacl a b _).mpr rfl⟩, h⟩
    rw [hleft, Apply_Sabcl]
    -- right side
    rw [mem_applyP]
    constructor
    · rintro ⟨l, r, hl, hr, hlr⟩
      exact ⟨l, r, mem_coe_coe.mpr hl, mem_coe_coe.mpr hr, hlr⟩
    · rintro ⟨l, r, hl, hr, hlr⟩
      rw [mem_coe_coe] at hl hr
      exact ⟨l, r, hl, hr, hlr⟩

end LeanExperiments.Lambda
