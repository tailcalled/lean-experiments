import LeanExperiments.PCA.Basic

/-!
# The closure model of the untyped λ-calculus as a (computable) PCA

The first concrete PCA: the term model of the untyped λ-calculus, with **named
variables** and a **closure / environment** semantics (no substitution under
binders).  Application is realized by a **gas interpreter** `eval`, so the whole
model is computable — no `Classical.choice`, nothing `noncomputable`.

`eval` threads the gas budget through an application `f a`: evaluating `f` leaves
some gas, which is fed into `a`, whose leftover is fed into the body.
-/

namespace LeanExperiments.Lambda

open LeanExperiments
open scoped LeanExperiments.Partial

/-- Variables are names. -/
abbrev Var := String

/-- λ-terms with named variables. -/
inductive Term where
  | var : Var → Term
  | lam : Var → Term → Term
  | app : Term → Term → Term
deriving Repr, DecidableEq

/-- Values are closures: a bound variable, a body, and a captured environment. -/
inductive Value where
  | closure : Var → Term → List (Var × Value) → Value
deriving Repr

/-- Environments map variables to values. -/
abbrev Env := List (Var × Value)

/-- Look a variable up in an environment (most recent binding wins). -/
def lookup : Env → Var → Option Value
  | [], _ => none
  | (y, v) :: rest, x => if x = y then some v else lookup rest x

/-- The gas interpreter.  Given a gas budget it either runs out (`none`) or
returns leftover gas and a value.  Gas is threaded through applications; the
`min … n` clamps make termination obvious and are shown to be no-ops by
`eval_le`. -/
def eval : Nat → Env → Term → Option (Nat × Value)
  | 0, _, _ => none
  | n + 1, env, .var x => (lookup env x).map fun v => (n, v)
  | n + 1, env, .lam x b => some (n, .closure x b env)
  | n + 1, env, .app f a =>
      match eval n env f with
      | some (r1, .closure x b cenv) =>
          match eval (min r1 n) env a with
          | some (r2, av) => eval (min r2 n) ((x, av) :: cenv) b
          | none => none
      | none => none
  termination_by n => n
  decreasing_by
    · omega
    · omega
    · omega

@[simp] theorem eval_zero (env : Env) (t : Term) : eval 0 env t = none := by simp [eval]

theorem eval_var (n : Nat) (env : Env) (x : Var) :
    eval (n + 1) env (.var x) = (lookup env x).map fun v => (n, v) := by rw [eval]

theorem eval_lam (n : Nat) (env : Env) (x : Var) (b : Term) :
    eval (n + 1) env (.lam x b) = some (n, .closure x b env) := by rw [eval]

theorem eval_app (n : Nat) (env : Env) (f a : Term) :
    eval (n + 1) env (.app f a) =
      (match eval n env f with
       | some (r1, .closure x b cenv) =>
           (match eval (min r1 n) env a with
            | some (r2, av) => eval (min r2 n) ((x, av) :: cenv) b
            | none => none)
       | none => none) := by rw [eval]

/-- Leftover gas never exceeds the budget. -/
theorem eval_le : ∀ {g : Nat} {env : Env} {t : Term} {r : Nat} {v : Value},
    eval g env t = some (r, v) → r ≤ g
  | 0, _, _, _, _, h => by simp at h
  | n + 1, env, .var x, r, v, h => by
      rw [eval_var, Option.map_eq_some_iff] at h
      obtain ⟨v0, _, h2⟩ := h
      rw [Prod.mk.injEq] at h2; omega
  | n + 1, env, .lam x b, r, v, h => by
      rw [eval_lam, Option.some.injEq, Prod.mk.injEq] at h; omega
  | n + 1, env, .app f a, r, v, h => by
      rw [eval_app] at h
      split at h
      next r1 x b cenv he1 =>
        split at h
        next r2 av he2 =>
          have h1 := eval_le h
          have h2 := Nat.min_le_right r2 n
          omega
        next => simp at h
      next => simp at h
  termination_by g => g
  decreasing_by exact Nat.lt_succ_of_le (Nat.min_le_right _ _)

/-- Extra gas threads straight through to extra leftover (the `valid` law). -/
theorem eval_mono : ∀ {g : Nat} {env : Env} {t : Term} {r : Nat} {v : Value},
    eval g env t = some (r, v) → ∀ k, eval (g + k) env t = some (r + k, v)
  | 0, _, _, _, _, h, _ => by simp at h
  | n + 1, env, .var x, r, v, h, k => by
      rw [eval_var, Option.map_eq_some_iff] at h
      obtain ⟨v0, hl, h2⟩ := h
      simp only [Prod.mk.injEq] at h2
      rw [show n + 1 + k = (n + k) + 1 from by omega, eval_var, hl]
      show some (n + k, v0) = some (r + k, v)
      rw [h2.1, h2.2]
  | n + 1, env, .lam x b, r, v, h, k => by
      rw [eval_lam, Option.some.injEq, Prod.mk.injEq] at h
      rw [show n + 1 + k = (n + k) + 1 from by omega, eval_lam, h.1, h.2]
  | n + 1, env, .app f a, r, v, h, k => by
      rw [eval_app] at h
      split at h
      next r1 x b cenv he1 =>
        rw [Nat.min_eq_left (eval_le he1)] at h
        split at h
        next r2 av he2 =>
          have hr1 : r1 ≤ n := eval_le he1
          have hr2 : r2 ≤ n := Nat.le_trans (eval_le he2) hr1
          rw [Nat.min_eq_left hr2] at h
          have e1 := eval_mono he1 k
          have e2 := eval_mono he2 k
          have e3 := eval_mono h k
          simp only [show n + 1 + k = (n + k) + 1 from by omega, eval_app, e1, e2, e3,
            Nat.min_eq_left (show r1 + k ≤ n + k from by omega),
            Nat.min_eq_left (show r2 + k ≤ n + k from by omega)]
        next => simp at h
      next => simp at h
  termination_by g => g
  decreasing_by all_goals omega

/-! ### Wrapping the interpreter as a partial value -/

/-- The computation evaluating `t` in `env`, as a valid gas computation. -/
def evalC (env : Env) (t : Term) : PComp Value where
  run g := eval g env t
  valid h k := eval_mono h k
  le h := eval_le h

@[simp] theorem evalC_run (env : Env) (t : Term) (g : Nat) :
    (evalC env t).run g = eval g env t := rfl

theorem mem_evalC {env : Env} {t : Term} {w : Value} :
    w ∈ evalC env t ↔ ∃ g r, eval g env t = some (r, w) := Iff.rfl

/-- Application of values: apply a closure to an argument by evaluating the body
in the extended environment. -/
def appV : Value → Value → PComp Value
  | .closure x b cenv, va => evalC ((x, va) :: cenv) b

instance : PartialApp Value := ⟨appV⟩

@[simp] theorem app_def (a b : Value) : PartialApp.app a b = appV a b := rfl

/-! ### Membership lemmas for the interpreter -/

@[simp] theorem mem_evalC_lam {env : Env} {x : Var} {b : Term} {w : Value} :
    w ∈ evalC env (.lam x b) ↔ w = .closure x b env := by
  rw [mem_evalC]
  constructor
  · rintro ⟨g, r, h⟩
    cases g with
    | zero => simp at h
    | succ n => rw [eval_lam, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  · rintro rfl; exact ⟨1, 0, by simp [eval]⟩

@[simp] theorem mem_evalC_var {env : Env} {x : Var} {w : Value} :
    w ∈ evalC env (.var x) ↔ lookup env x = some w := by
  rw [mem_evalC]
  constructor
  · rintro ⟨g, r, h⟩
    cases g with
    | zero => simp at h
    | succ n =>
      rw [eval_var, Option.map_eq_some_iff] at h
      obtain ⟨v0, hl, h2⟩ := h
      rw [Prod.mk.injEq] at h2
      rw [hl, h2.2]
  · intro h; exact ⟨1, 0, by simp [eval, h]⟩

/-- The run of an application is, after one gas step, exactly the `bind` that
runs `f`, then `a`, then applies. -/
theorem evalC_app_run (env : Env) (f a : Term) (n : Nat) :
    (evalC env (.app f a)).run (n + 1) =
      (PComp.bind (evalC env f) fun cl => PComp.bind (evalC env a) fun av => appV cl av).run n := by
  show eval (n + 1) env (.app f a) =
    (eval n env f).bind fun p => (eval p.1 env a).bind fun q => (appV p.2 q.2).run q.1
  rw [eval_app]
  cases he1 : eval n env f with
  | none => rfl
  | some p1 =>
    obtain ⟨r1, cl⟩ := p1
    cases cl with
    | closure x b cenv =>
      simp only [Nat.min_eq_left (eval_le he1)]
      cases he2 : eval r1 env a with
      | none => simp [he2]
      | some p2 =>
        obtain ⟨r2, av⟩ := p2
        simp [he2, Nat.min_eq_left (Nat.le_trans (eval_le he2) (eval_le he1)), appV]

theorem mem_evalC_app {env : Env} {f a : Term} {w : Value} :
    w ∈ evalC env (.app f a) ↔
      ∃ cl av, cl ∈ evalC env f ∧ av ∈ evalC env a ∧ w ∈ appV cl av := by
  have hbind : w ∈ evalC env (.app f a) ↔
      w ∈ PComp.bind (evalC env f) fun cl => PComp.bind (evalC env a) fun av => appV cl av := by
    constructor
    · rintro ⟨g, r, h⟩
      cases g with
      | zero => simp at h
      | succ n => exact ⟨n, r, by rw [← evalC_app_run]; exact h⟩
    · rintro ⟨n, r, h⟩
      exact ⟨n + 1, r, by rw [evalC_app_run]; exact h⟩
  rw [hbind, PComp.mem_bind]
  constructor
  · rintro ⟨cl, hcl, hw⟩
    rw [PComp.mem_bind] at hw
    obtain ⟨av, hav, hw⟩ := hw
    exact ⟨cl, av, hcl, hav, hw⟩
  · rintro ⟨cl, av, hcl, hav, hw⟩
    exact ⟨cl, hcl, PComp.mem_bind.mpr ⟨av, hav, hw⟩⟩

/-- Specialisation to an application of two variables. -/
theorem mem_evalC_app_var {env : Env} {p q : Var} {vp vq w : Value}
    (hp : lookup env p = some vp) (hq : lookup env q = some vq) :
    w ∈ evalC env (.app (.var p) (.var q)) ↔ w ∈ appV vp vq := by
  rw [mem_evalC_app]
  constructor
  · rintro ⟨cl, av, hcl, hav, hw⟩
    rw [mem_evalC_var, hp, Option.some.injEq] at hcl
    rw [mem_evalC_var, hq, Option.some.injEq] at hav
    subst hcl; subst hav; exact hw
  · intro hw
    exact ⟨vp, vq, mem_evalC_var.mpr hp, mem_evalC_var.mpr hq, hw⟩

/-! ### The combinators -/

/-- `k = λx y. x`. -/
def K : Value := .closure "x" (.lam "y" (.var "x")) []

/-- The body of `s`, i.e. `x z (y z)`. -/
def Sbody : Term :=
  .app (.app (.var "x") (.var "z")) (.app (.var "y") (.var "z"))

/-- `s = λx y z. x z (y z)`. -/
def S : Value := .closure "x" (.lam "y" (.lam "z" Sbody)) []

/-- Applying one value to another (membership form). -/
def Apply (vf va w : Value) : Prop := w ∈ appV vf va

theorem Apply_K (a w : Value) :
    Apply K a w ↔ w = .closure "y" (.var "x") [("x", a)] := by
  show w ∈ evalC [("x", a)] (.lam "y" (.var "x")) ↔ _
  simp

theorem Apply_Kcl (a b w : Value) :
    Apply (.closure "y" (.var "x") [("x", a)]) b w ↔ w = a := by
  show w ∈ evalC [("y", b), ("x", a)] (.var "x") ↔ _
  rw [mem_evalC_var]
  simp [lookup, eq_comm]

theorem Apply_S (a w : Value) :
    Apply S a w ↔ w = .closure "y" (.lam "z" Sbody) [("x", a)] := by
  show w ∈ evalC [("x", a)] (.lam "y" (.lam "z" Sbody)) ↔ _
  simp

theorem Apply_Sacl (a b w : Value) :
    Apply (.closure "y" (.lam "z" Sbody) [("x", a)]) b w ↔
      w = .closure "z" Sbody [("y", b), ("x", a)] := by
  show w ∈ evalC [("y", b), ("x", a)] (.lam "z" Sbody) ↔ _
  simp

theorem Apply_Sabcl (a b c w : Value) :
    Apply (.closure "z" Sbody [("y", b), ("x", a)]) c w ↔
      ∃ l r, Apply a c l ∧ Apply b c r ∧ Apply l r w := by
  show w ∈ evalC [("z", c), ("y", b), ("x", a)] Sbody ↔ _
  have hx : lookup [("z", c), ("y", b), ("x", a)] "x" = some a := by simp [lookup]
  have hy : lookup [("z", c), ("y", b), ("x", a)] "y" = some b := by simp [lookup]
  have hz : lookup [("z", c), ("y", b), ("x", a)] "z" = some c := by simp [lookup]
  rw [Sbody, mem_evalC_app]
  constructor
  · rintro ⟨cl, av, hcl, hav, hw⟩
    rw [mem_evalC_app_var hx hz] at hcl
    rw [mem_evalC_app_var hy hz] at hav
    exact ⟨cl, av, hcl, hav, hw⟩
  · rintro ⟨l, r, hl, hr, hlr⟩
    exact ⟨l, r, (mem_evalC_app_var hx hz).mpr hl, (mem_evalC_app_var hy hz).mpr hr, hlr⟩

/-! ### Membership through lifted application -/

open scoped LeanExperiments.PartialApp

theorem mem_cc {x z w : Value} : w ∈ ((↑x : Partial Value) ⬝ ↑z) ↔ Apply x z w := by
  rw [PartialApp.mem_applyP]
  constructor
  · rintro ⟨f, a, hf, ha, hw⟩
    rw [PartialApp.mem_coe] at hf ha
    subst hf; subst ha; exact hw
  · intro h; exact ⟨x, z, PartialApp.mem_coe.mpr rfl, PartialApp.mem_coe.mpr rfl, h⟩

theorem mem_ca {p : Partial Value} {z w : Value} :
    w ∈ (p ⬝ (↑z : Partial Value)) ↔ ∃ u, u ∈ p ∧ Apply u z w := by
  rw [PartialApp.mem_applyP]
  constructor
  · rintro ⟨f, a, hf, ha, hw⟩
    rw [PartialApp.mem_coe] at ha
    subst ha; exact ⟨f, hf, hw⟩
  · rintro ⟨u, hu, hw⟩
    exact ⟨u, z, hu, PartialApp.mem_coe.mpr rfl, hw⟩

/-! ### The PCA instance -/

instance : PCA Value where
  k := K
  s := S
  k_eq := by
    intro a b
    apply Partial.ext
    intro w
    rw [PartialApp.mem_coe, mem_ca]
    constructor
    · rintro ⟨u, hu, hub⟩
      rw [mem_cc, Apply_K] at hu
      subst hu
      rw [Apply_Kcl] at hub
      exact hub
    · intro hwa
      subst w
      exact ⟨_, mem_cc.mpr ((Apply_K a _).mpr rfl), (Apply_Kcl a b a).mpr rfl⟩
  s_dom := by
    intro a b
    show ∃ w, w ∈ ((↑S : Partial Value) ⬝ ↑a ⬝ ↑b)
    exact ⟨_, mem_ca.mpr ⟨_, mem_cc.mpr ((Apply_S a _).mpr rfl), (Apply_Sacl a b _).mpr rfl⟩⟩
  s_eq := by
    intro a b c
    apply Partial.ext
    intro w
    rw [mem_ca]
    have hleft : (∃ u, u ∈ ((↑S : Partial Value) ⬝ ↑a ⬝ ↑b) ∧ Apply u c w) ↔
        Apply (.closure "z" Sbody [("y", b), ("x", a)]) c w := by
      constructor
      · rintro ⟨u, hu, huc⟩
        rw [mem_ca] at hu
        obtain ⟨u2, hu2, hu2b⟩ := hu
        rw [mem_cc, Apply_S] at hu2
        subst hu2
        rw [Apply_Sacl] at hu2b
        subst hu2b
        exact huc
      · intro h
        exact ⟨_, by
          rw [mem_ca]
          exact ⟨_, mem_cc.mpr ((Apply_S a _).mpr rfl), (Apply_Sacl a b _).mpr rfl⟩, h⟩
    rw [hleft, Apply_Sabcl, PartialApp.mem_applyP]
    constructor
    · rintro ⟨l, r, hl, hr, hlr⟩
      exact ⟨l, r, mem_cc.mpr hl, mem_cc.mpr hr, hlr⟩
    · rintro ⟨l, r, hl, hr, hlr⟩
      rw [mem_cc] at hl hr
      exact ⟨l, r, hl, hr, hlr⟩

end LeanExperiments.Lambda
