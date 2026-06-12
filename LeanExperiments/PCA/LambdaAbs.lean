import LeanExperiments.PCA.Lambda
import LeanExperiments.PCA.Abstraction

/-!
# Name-preserving abstraction for the closure model

The generic bracket abstraction (`Expr.bracket`) compiles to `s`/`k`, so in the
λ-model the realizer comes out as combinator soup with the parameter name lost.

Here we override abstraction for the closure model: `abs x e` builds a real
`closure "x" body env` — so the name `"x"` (and the names of free variables)
survive into the underlying λ-term.  Constants embedded in `e` are anonymous
`Value`s, so they are captured in the environment under **freshly generated
names** `x#…`, guaranteed distinct from `x` and from each other.
-/

namespace LeanExperiments.Lambda

open LeanExperiments
open scoped LeanExperiments.Partial LeanExperiments.PartialApp

@[simp] theorem lookup_nil (name : Var) : lookup [] name = none := rfl

@[simp] theorem lookup_cons (k : Var) (w : Value) (rest : Env) (name : Var) :
    lookup ((k, w) :: rest) name = if name = k then some w else lookup rest name := rfl

/-! ### Fresh names for captured constants -/

/-- A string of `n` `'#'` characters. -/
def hashes : Nat → String
  | 0 => ""
  | n + 1 => "#" ++ hashes n

@[simp] theorem hashes_length (n : Nat) : (hashes n).length = n := by
  induction n with
  | zero => simp [hashes]
  | succ m ih => rw [hashes, String.length_append, ih]; show 1 + m = m + 1; omega

/-- The name of the `i`-th captured constant when abstracting `x`. -/
def constName (x : String) (i : Nat) : String := x ++ hashes (i + 1)

theorem constName_length (x : String) (i : Nat) :
    (constName x i).length = x.length + (i + 1) := by
  simp [constName, String.length_append]

theorem constName_ne (x : String) (i : Nat) : constName x i ≠ x := by
  intro h
  have := congrArg String.length h
  rw [constName_length] at this
  omega

theorem constName_inj (x : String) {i j : Nat} (h : constName x i = constName x j) : i = j := by
  have := congrArg String.length h
  rw [constName_length, constName_length] at this
  omega

/-! ### Closure conversion -/

/-- Number of constants embedded in an expression. -/
def numConsts : Expr Value → Nat
  | .var _ => 0
  | .const _ => 1
  | .app e₁ e₂ => numConsts e₁ + numConsts e₂

/-- The body term: variables stay, constants become fresh variables. -/
def toBody (x : String) : Nat → Expr Value → Term
  | _, .var y => .var y
  | off, .const _ => .var (constName x off)
  | off, .app e₁ e₂ => .app (toBody x off e₁) (toBody x (off + numConsts e₁) e₂)

/-- The captured environment binding each fresh constant name to its value. -/
def constEnv (x : String) : Nat → Expr Value → Env
  | _, .var _ => []
  | off, .const c => [(constName x off, c)]
  | off, .app e₁ e₂ => constEnv x off e₁ ++ constEnv x (off + numConsts e₁) e₂

/-- The environment `env` correctly binds the constants of `e` (offset `off`). -/
def Binds (x : String) (env : Env) : Nat → Expr Value → Prop
  | _, .var _ => True
  | off, .const c => lookup env (constName x off) = some c
  | off, .app e₁ e₂ => Binds x env off e₁ ∧ Binds x env (off + numConsts e₁) e₂

/-! ### `lookup` and `Binds` lemmas -/

theorem lookup_append_some {env₁ : Env} {name : Var} {v : Value} (env₂ : Env)
    (h : lookup env₁ name = some v) : lookup (env₁ ++ env₂) name = some v := by
  induction env₁ with
  | nil => simp at h
  | cons hd tl ih =>
    obtain ⟨k, w⟩ := hd
    simp only [List.cons_append, lookup_cons] at h ⊢
    by_cases hk : name = k
    · simp only [if_pos hk] at h ⊢; exact h
    · simp only [if_neg hk] at h ⊢; exact ih h

theorem lookup_append_none {env₁ : Env} {name : Var} (env₂ : Env)
    (h : lookup env₁ name = none) : lookup (env₁ ++ env₂) name = lookup env₂ name := by
  induction env₁ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, w⟩ := hd
    simp only [List.cons_append, lookup_cons] at h ⊢
    by_cases hk : name = k
    · simp only [if_pos hk] at h; simp at h
    · simp only [if_neg hk] at h ⊢; exact ih h

theorem lookup_constEnv_none (x : String) :
    ∀ (off m : Nat) (e : Expr Value), (∀ i, i < numConsts e → m ≠ off + i) →
      lookup (constEnv x off e) (constName x m) = none
  | _, _, .var _, _ => rfl
  | off, m, .const c, h => by
    have hne : ¬ (constName x m = constName x off) := by
      intro heq
      have hm := constName_inj x heq
      have := h 0 (by simp [numConsts])
      omega
    simp [constEnv, lookup_cons, hne]
  | off, m, .app e₁ e₂, h => by
    simp only [constEnv]
    rw [lookup_append_none _ (lookup_constEnv_none x off m e₁ (fun i hi => h i (by
      simp only [numConsts]; omega)))]
    exact lookup_constEnv_none x (off + numConsts e₁) m e₂ (fun i hi => by
      have := h (numConsts e₁ + i) (by simp only [numConsts]; omega); omega)

theorem Binds_append_left (x : String) {env₁ : Env} (env₂ : Env) :
    ∀ (off : Nat) (e : Expr Value), Binds x env₁ off e → Binds x (env₁ ++ env₂) off e
  | _, .var _, _ => trivial
  | _, .const _, h => lookup_append_some env₂ h
  | off, .app e₁ e₂, h =>
    ⟨Binds_append_left x env₂ off e₁ h.1, Binds_append_left x env₂ (off + numConsts e₁) e₂ h.2⟩

theorem Binds_append_right (x : String) (env₁ : Env) {env₂ : Env} :
    ∀ (off : Nat) (e : Expr Value),
      (∀ i, i < numConsts e → lookup env₁ (constName x (off + i)) = none) →
      Binds x env₂ off e → Binds x (env₁ ++ env₂) off e
  | _, .var _, _, _ => trivial
  | off, .const c, hd, h => by
    have h0 : lookup env₁ (constName x off) = none := by
      have := hd 0 (by simp [numConsts]); simpa using this
    show lookup (env₁ ++ env₂) (constName x off) = some c
    rw [lookup_append_none _ h0]; exact h
  | off, .app e₁ e₂, hd, h =>
    ⟨Binds_append_right x env₁ off e₁ (fun i hi => hd i (by simp only [numConsts]; omega)) h.1,
     Binds_append_right x env₁ (off + numConsts e₁) e₂
       (fun i hi => by
          have := hd (numConsts e₁ + i) (by simp only [numConsts]; omega)
          simpa [Nat.add_assoc] using this) h.2⟩

theorem binds_constEnv (x : String) :
    ∀ (off : Nat) (e : Expr Value), Binds x (constEnv x off e) off e
  | _, .var _ => trivial
  | off, .const c => by simp [Binds, constEnv, lookup_cons]
  | off, .app e₁ e₂ => by
    refine ⟨Binds_append_left x _ off e₁ (binds_constEnv x off e₁), ?_⟩
    refine Binds_append_right x _ (off + numConsts e₁) e₂ (fun i hi => ?_)
      (binds_constEnv x (off + numConsts e₁) e₂)
    exact lookup_constEnv_none x off (off + numConsts e₁ + i) e₁ (fun j hj => by omega)

/-! ### The interpreter as a partial value -/

/-- The partial value computed by evaluating `t` in `env`. -/
def evalP (env : Env) (t : Term) : Partial Value := Partial.mk (evalC env t)

theorem evalP_var_of_lookup {env : Env} {y : Var} {v : Value} (h : lookup env y = some v) :
    evalP env (.var y) = Partial.pure v := by
  apply Partial.ext
  intro w
  simp only [evalP, Partial.mem_mk, mem_evalC_var, h, Partial.mem_pure, Option.some.injEq]
  exact eq_comm

theorem evalC_app_eq (env : Env) (t₁ t₂ : Term) :
    evalP env (.app t₁ t₂) = (evalP env t₁ ⬝ evalP env t₂ : Partial Value) := by
  apply Partial.ext
  intro w
  rw [PartialApp.mem_applyP]
  simp only [evalP, Partial.mem_mk, mem_evalC_app, app_def]

/-- Applying a closure to an argument runs its body in the extended environment. -/
theorem pure_closure_app (x : Var) (b : Term) (cenv : Env) (a : Value) :
    (Partial.pure (.closure x b cenv) ⬝ Partial.pure a : Partial Value) =
      evalP ((x, a) :: cenv) b := by
  rw [PartialApp.pure_app]; rfl

/-! ### Correctness of closure conversion -/

theorem compile_correct (x : String) (ρ : String → Value) (a : Value) :
    ∀ (e : Expr Value) (off : Nat) (env : Env), Expr.closed1 x e → Binds x env off e →
      evalP ((x, a) :: env) (toBody x off e) = e.denote (Expr.update ρ x a) := by
  intro e
  induction e with
  | var y =>
    intro off env hc _
    have hy : y = x := hc y (by simp [Expr.fvE])
    subst y
    have hl : lookup ((x, a) :: env) x = some a := by simp [lookup_cons]
    rw [show toBody x off (.var x) = .var x from rfl, evalP_var_of_lookup hl,
      Expr.denote_var, Expr.update_same]
  | const c =>
    intro off env _ hb
    have hl : lookup ((x, a) :: env) (constName x off) = some c := by
      rw [lookup_cons, if_neg (constName_ne x off)]; exact hb
    rw [show toBody x off (.const c) = .var (constName x off) from rfl,
      evalP_var_of_lookup hl, Expr.denote_const]
  | app e₁ e₂ ih₁ ih₂ =>
    intro off env hc hb
    obtain ⟨hc₁, hc₂⟩ := Expr.closed1_app hc
    obtain ⟨hb₁, hb₂⟩ := hb
    rw [show toBody x off (.app e₁ e₂)
        = .app (toBody x off e₁) (toBody x (off + numConsts e₁) e₂) from rfl,
      evalC_app_eq, ih₁ off env hc₁ hb₁, ih₂ (off + numConsts e₁) env hc₂ hb₂,
      Expr.denote_app]

/-! ### The name-preserving abstraction -/

/-- Name-preserving abstraction: `λx. e` as a real closure. -/
def absV (x : String) (e : Expr Value) : Value :=
  .closure x (toBody x 0 e) (constEnv x 0 e)

theorem absV_spec (x : String) (e : Expr Value) (hc : Expr.closed1 x e)
    (a : Value) (ρ : String → Value) :
    (Partial.pure (absV x e) ⬝ Partial.pure a : Partial Value) =
      e.denote (Expr.update ρ x a) := by
  rw [absV, pure_closure_app,
    compile_correct x ρ a e 0 (constEnv x 0 e) hc (binds_constEnv x 0 e)]

/-- The closure model has name-preserving abstraction. -/
instance : Abstraction Value where
  abs := absV
  abs_spec := absV_spec

end LeanExperiments.Lambda
