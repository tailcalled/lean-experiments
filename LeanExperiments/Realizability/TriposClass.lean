/-!
# The abstract tripos interface

A **tripos** (Pitts) over the base category `Type u` is a `Type u`-indexed family
of fibres `P I`, each a Heyting prealgebra under an entailment preorder `⊢`,
together with monotone reindexing `subst f` along every map `f : I → J`, each
reindexing possessing *both* adjoints

```
∃_f ⊣ subst f ⊣ ∀_f
```

and a **generic predicate** `generic : P Prop'` through which every predicate
factors (the weak subobject classifier).  This is exactly the structure the
realizability fibres `Pred A I` were shown to carry; factoring it into a class
lets the tripos→topos construction run once, generically.

Following the project's extraction philosophy, entailment `entails φ ψ` is a
*truncated type* — a subsingleton carrying an un-erased realizer — rather than an
erased `Prop`.  So the morphisms of the resulting topos will carry realizer data
that survives to runtime.
-/

namespace LeanExperiments.Realizability

universe u v

/-- A tripos over the base `Type u`: Heyting-prealgebra fibres with reindexing,
both quantifier adjoints, and a generic predicate.  See the module docstring. -/
class Tripos (P : Type u → Type v) where
  /-- Entailment in a fibre: a subsingleton carrying a (un-erased) realizer. -/
  entails : {I : Type u} → P I → P I → Type u
  /-- Entailment is proof-irrelevant: fibres are preorders, not categories. -/
  entails_subsingleton : ∀ {I : Type u} (φ ψ : P I), Subsingleton (entails φ ψ)
  /-- Reflexivity. -/
  le_refl : ∀ {I : Type u} (φ : P I), entails φ φ
  /-- Transitivity. -/
  le_trans : ∀ {I : Type u} {φ ψ θ : P I}, entails φ ψ → entails ψ θ → entails φ θ
  /-- Reindexing a predicate along a function. -/
  subst : {I J : Type u} → (I → J) → P J → P I
  /-- Reindexing is monotone. -/
  subst_mono : ∀ {I J : Type u} (f : I → J) {φ ψ : P J},
    entails φ ψ → entails (subst f φ) (subst f ψ)
  /-- Reindexing is functorial in the identity. -/
  subst_id : ∀ {I : Type u} (φ : P I), subst id φ = φ
  /-- Reindexing is functorial in composition. -/
  subst_comp : ∀ {I J K : Type u} (f : I → J) (g : J → K) (φ : P K),
    subst (g ∘ f) φ = subst f (subst g φ)
  /-- The greatest predicate of each fibre. -/
  top : {I : Type u} → P I
  /-- `⊤` is greatest. -/
  le_top : ∀ {I : Type u} (φ : P I), entails φ top
  /-- The least predicate of each fibre. -/
  bot : {I : Type u} → P I
  /-- `⊥` is least. -/
  bot_le : ∀ {I : Type u} (φ : P I), entails bot φ
  /-- Conjunction. -/
  conj : {I : Type u} → P I → P I → P I
  /-- `φ ∧ ψ ⊢ φ`. -/
  conj_le_left : ∀ {I : Type u} (φ ψ : P I), entails (conj φ ψ) φ
  /-- `φ ∧ ψ ⊢ ψ`. -/
  conj_le_right : ∀ {I : Type u} (φ ψ : P I), entails (conj φ ψ) ψ
  /-- Universal property of `∧`. -/
  le_conj : ∀ {I : Type u} {χ φ ψ : P I}, entails χ φ → entails χ ψ → entails χ (conj φ ψ)
  /-- Disjunction. -/
  disj : {I : Type u} → P I → P I → P I
  /-- `φ ⊢ φ ∨ ψ`. -/
  left_le_disj : ∀ {I : Type u} (φ ψ : P I), entails φ (disj φ ψ)
  /-- `ψ ⊢ φ ∨ ψ`. -/
  right_le_disj : ∀ {I : Type u} (φ ψ : P I), entails ψ (disj φ ψ)
  /-- Universal property of `∨`. -/
  disj_le : ∀ {I : Type u} {φ ψ χ : P I}, entails φ χ → entails ψ χ → entails (disj φ ψ) χ
  /-- Heyting implication. -/
  impl : {I : Type u} → P I → P I → P I
  /-- Currying half of the `· ∧ φ ⊣ φ → ·` adjunction. -/
  curry : ∀ {I : Type u} {χ φ ψ : P I}, entails (conj χ φ) ψ → entails χ (impl φ ψ)
  /-- Uncurrying half of the `· ∧ φ ⊣ φ → ·` adjunction. -/
  uncurry : ∀ {I : Type u} {χ φ ψ : P I}, entails χ (impl φ ψ) → entails (conj χ φ) ψ
  /-- Existential quantification along reindexing. -/
  ex : {I J : Type u} → (I → J) → P I → P J
  /-- `∃_f ⊣ subst f`, forward. -/
  ex_adj_mp : ∀ {I J : Type u} {f : I → J} {φ : P I} {ψ : P J},
    entails (ex f φ) ψ → entails φ (subst f ψ)
  /-- `∃_f ⊣ subst f`, backward. -/
  ex_adj_mpr : ∀ {I J : Type u} {f : I → J} {φ : P I} {ψ : P J},
    entails φ (subst f ψ) → entails (ex f φ) ψ
  /-- Universal quantification along reindexing. -/
  all : {I J : Type u} → (I → J) → P I → P J
  /-- `subst f ⊣ ∀_f`, forward. -/
  all_adj_mp : ∀ {I J : Type u} {f : I → J} {φ : P I} {ψ : P J},
    entails (subst f ψ) φ → entails ψ (all f φ)
  /-- `subst f ⊣ ∀_f`, backward. -/
  all_adj_mpr : ∀ {I J : Type u} {f : I → J} {φ : P I} {ψ : P J},
    entails ψ (all f φ) → entails (subst f ψ) φ
  /-- The object of truth values. -/
  Prop' : Type u
  /-- The generic predicate over `Prop'`. -/
  generic : P Prop'
  /-- The characteristic map of a predicate. -/
  char : {I : Type u} → P I → (I → Prop')
  /-- Comprehension: every predicate is `generic` reindexed along its
  characteristic map. -/
  subst_char : ∀ {I : Type u} (φ : P I), subst (char φ) generic = φ

namespace Tripos

@[inherit_doc] scoped infix:50 " ⊢ " => Tripos.entails

/-- Entailment is a subsingleton, so fibres are genuine preorders. -/
instance instEntailsSubsingleton {P : Type u → Type v} [Tripos P] {I : Type u}
    (φ ψ : P I) : Subsingleton (Tripos.entails φ ψ) :=
  Tripos.entails_subsingleton φ ψ

end Tripos

end LeanExperiments.Realizability
