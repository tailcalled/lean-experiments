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
  /-- Reindexing preserves `⊤`. -/
  subst_top : ∀ {I J : Type u} (f : I → J), subst f (top : P J) = (top : P I)
  /-- Reindexing preserves `⊥`. -/
  subst_bot : ∀ {I J : Type u} (f : I → J), subst f (bot : P J) = (bot : P I)
  /-- Reindexing preserves `∧`. -/
  subst_conj : ∀ {I J : Type u} (f : I → J) (φ ψ : P J),
    subst f (conj φ ψ) = conj (subst f φ) (subst f ψ)
  /-- Reindexing preserves `∨`. -/
  subst_disj : ∀ {I J : Type u} (f : I → J) (φ ψ : P J),
    subst f (disj φ ψ) = disj (subst f φ) (subst f ψ)
  /-- Reindexing preserves `→`. -/
  subst_impl : ∀ {I J : Type u} (f : I → J) (φ ψ : P J),
    subst f (impl φ ψ) = impl (subst f φ) (subst f ψ)
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
  /-- **Frobenius reciprocity**: `∃_f` is a map of `P J`-modules.  The reverse
  entailment is derivable from the adjunction; this — the harder direction — is
  the genuine extra tripos axiom (left adjoints are stable under `∧`). -/
  frobenius : ∀ {I J : Type u} (f : I → J) (φ : P I) (ψ : P J),
    entails (conj ψ (ex f φ)) (ex f (conj (subst f ψ) φ))
  /-- **Beck–Chevalley**: reindexing commutes with `∃` over a pullback square.
  Here the pullback of `f : I → J` and `g : K → J` is the subtype
  `{(k, i) // g k = f i}`.  The reverse entailment is derivable; this direction
  is the genuine axiom. -/
  beck_chevalley : ∀ {I J K : Type u} (f : I → J) (g : K → J) (φ : P I),
    entails (subst g (ex f φ))
      (ex (fun s : { p : K × I // g p.1 = f p.2 } => s.1.1)
          (subst (fun s : { p : K × I // g p.1 = f p.2 } => s.1.2) φ))
  /-- **Beck–Chevalley for `∀`**: reindexing commutes with `∀` over a pullback.
  The genuine extra axiom is this (the reverse is derivable from the adjunction). -/
  all_beck_chevalley : ∀ {I J K : Type u} (f : I → J) (g : K → J) (φ : P I),
    entails (all (fun s : { p : K × I // g p.1 = f p.2 } => s.1.1)
                 (subst (fun s : { p : K × I // g p.1 = f p.2 } => s.1.2) φ))
            (subst g (all f φ))
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

/-! ### Derived lemmas

Standard consequences of the interface, used by the tripos→topos construction.
All are *data* (entailment is a `Type`), so they are `def`s. -/

variable {P : Type u → Type v} [Tripos P]

/-- Reindexing along equal maps gives equal predicates (one direction). -/
def subst_congr {I J : Type u} {f g : I → J} (h : f = g) (φ : P J) :
    entails (subst f φ) (subst g φ) := by rw [h]; exact le_refl _

/-- Trivial reindexing entailment (`φ ⊢ subst id φ`). -/
def subst_id_ge {I : Type u} (φ : P I) : entails φ (subst id φ) := by
  rw [subst_id]; exact le_refl φ

/-- Trivial reindexing entailment (`subst id φ ⊢ φ`). -/
def subst_id_le {I : Type u} (φ : P I) : entails (subst id φ) φ := by
  rw [subst_id]; exact le_refl φ

/-- The unit of `∃_f ⊣ subst f`. -/
def ex_unit {I J : Type u} (f : I → J) (φ : P I) : entails φ (subst f (ex f φ)) :=
  ex_adj_mp (le_refl _)

/-- The counit of `subst f ⊣ ∀_f`. -/
def all_counit {I J : Type u} (f : I → J) (φ : P I) : entails (subst f (all f φ)) φ :=
  all_adj_mpr (le_refl _)

/-- `∃_f` is monotone in its predicate. -/
def ex_mono {I J : Type u} (f : I → J) {φ φ' : P I} (h : entails φ φ') :
    entails (ex f φ) (ex f φ') :=
  ex_adj_mpr (le_trans h (ex_unit f φ'))

/-- `∀_f` is monotone in its predicate. -/
def all_mono {I J : Type u} (f : I → J) {φ φ' : P I} (h : entails φ φ') :
    entails (all f φ) (all f φ') :=
  all_adj_mp (le_trans (all_counit f φ) h)

/-- Product Beck–Chevalley for `∀`: reindexing the kept factor commutes with
universal quantification over the other factor. -/
def all_subst_fst {J K L : Type u} (h : K → J) (φ : P (J × L)) :
    entails (all (Prod.fst : K × L → K) (subst (fun p : K × L => (h p.1, p.2)) φ))
            (subst h (all (Prod.fst : J × L → J) φ)) := by
  refine le_trans (all_adj_mp ?_) (all_beck_chevalley (Prod.fst : J × L → J) h φ)
  have hc := subst_mono
    (fun s : { p : K × (J × L) // h p.1 = Prod.fst p.2 } => (s.1.1, s.1.2.2))
    (all_counit (Prod.fst : K × L → K) (subst (fun p : K × L => (h p.1, p.2)) φ))
  simp only [← subst_comp] at hc
  refine le_trans hc (subst_congr ?_ φ)
  funext s
  exact Prod.ext_iff.mpr ⟨s.2, rfl⟩

/-- Product Beck–Chevalley for `∃`: reindexing the kept factor commutes with
existential quantification over the other factor. -/
def ex_subst_fst {J K L : Type u} (h : K → J) (φ : P (J × L)) :
    entails (subst h (ex (Prod.fst : J × L → J) φ))
            (ex (Prod.fst : K × L → K) (subst (fun p : K × L => (h p.1, p.2)) φ)) := by
  refine le_trans (beck_chevalley (Prod.fst : J × L → J) h φ) (ex_adj_mpr ?_)
  have hu := subst_mono
    (fun s : { p : K × (J × L) // h p.1 = Prod.fst p.2 } => (s.1.1, s.1.2.2))
    (ex_unit (Prod.fst : K × L → K) (subst (fun p : K × L => (h p.1, p.2)) φ))
  simp only [← subst_comp] at hu
  refine le_trans (subst_congr ?_ φ) hu
  funext s
  exact Prod.ext_iff.mpr ⟨s.2.symm, rfl⟩

/-- Instantiate a `∀`: `(∀_f φ)` reindexed along `f ∘ h` entails `φ` reindexed
along `h`.  The workhorse for using a universally-quantified hypothesis at a
specific point. -/
def all_inst {I J K : Type u} (f : I → J) (h : K → I) (φ : P I) :
    entails (subst (fun k => f (h k)) (all f φ)) (subst h φ) := by
  rw [show (fun k => f (h k)) = f ∘ h from rfl, subst_comp]
  exact subst_mono h (all_counit f φ)

/-- `∧` is monotone in both arguments. -/
def conj_mono {I : Type u} {φ φ' ψ ψ' : P I} (h₁ : entails φ φ') (h₂ : entails ψ ψ') :
    entails (conj φ ψ) (conj φ' ψ') :=
  le_conj (le_trans (conj_le_left φ ψ) h₁) (le_trans (conj_le_right φ ψ) h₂)

/-- `∨` is monotone in both arguments. -/
def disj_mono {I : Type u} {φ φ' ψ ψ' : P I} (h₁ : entails φ φ') (h₂ : entails ψ ψ') :
    entails (disj φ ψ) (disj φ' ψ') :=
  disj_le (le_trans h₁ (left_le_disj φ' ψ')) (le_trans h₂ (right_le_disj φ' ψ'))

/-- Symmetric form of `le_conj`: split a conjunction goal. -/
def conj_assoc_left {I : Type u} (φ ψ θ : P I) :
    entails (conj (conj φ ψ) θ) (conj φ (conj ψ θ)) :=
  le_conj (le_trans (conj_le_left _ θ) (conj_le_left φ ψ))
    (le_conj (le_trans (conj_le_left _ θ) (conj_le_right φ ψ)) (conj_le_right _ θ))

/-- `∧` is commutative. -/
def conj_comm {I : Type u} (φ ψ : P I) : entails (conj φ ψ) (conj ψ φ) :=
  le_conj (conj_le_right φ ψ) (conj_le_left φ ψ)

/-- `⊤ ⊢ (φ → φ)`: implication is reflexive. -/
def id_impl {I : Type u} (φ : P I) : entails (top : P I) (impl φ φ) :=
  curry (conj_le_right _ _)

/-- Modus ponens: `(φ → ψ) ∧ φ ⊢ ψ`. -/
def impl_mp {I : Type u} (φ ψ : P I) : entails (conj (impl φ ψ) φ) ψ :=
  uncurry (le_refl _)

/-- Implication composes: `(φ → ψ) ∧ (ψ → θ) ⊢ (φ → θ)`. -/
def impl_trans {I : Type u} (φ ψ θ : P I) :
    entails (conj (impl φ ψ) (impl ψ θ)) (impl φ θ) := by
  apply curry
  have hψ : entails (conj (conj (impl φ ψ) (impl ψ θ)) φ) ψ := uncurry (conj_le_left _ _)
  exact le_trans (le_conj (le_refl _) hψ)
    (uncurry (le_trans (conj_le_left _ _) (conj_le_right _ _)))

/-- `∃` is functorial: `∃_g ∘ ∃_f ⊢ ∃_{g∘f}`. -/
def ex_comp_le {I J K : Type u} (f : I → J) (g : J → K) (φ : P I) :
    entails (ex g (ex f φ)) (ex (g ∘ f) φ) :=
  ex_adj_mpr (ex_adj_mpr (by rw [← subst_comp]; exact ex_unit (g ∘ f) φ))

/-- `∃` is functorial: `∃_{g∘f} ⊢ ∃_g ∘ ∃_f`. -/
def ex_comp_ge {I J K : Type u} (f : I → J) (g : J → K) (φ : P I) :
    entails (ex (g ∘ f) φ) (ex g (ex f φ)) :=
  ex_adj_mpr (by
    rw [subst_comp]
    exact le_trans (ex_unit f φ) (subst_mono f (ex_unit g (ex f φ))))

/-- Frobenius, the adjunction-derivable direction. -/
def frobenius_inv {I J : Type u} (f : I → J) (φ : P I) (ψ : P J) :
    entails (ex f (conj (subst f ψ) φ)) (conj ψ (ex f φ)) :=
  ex_adj_mpr (by
    rw [subst_conj]
    exact conj_mono (le_refl _) (ex_unit f φ))

/-- Eliminate an existential trapped inside a conjunction on the left of an
entailment: to prove `(∃_f φ) ∧ ψ ⊢ θ` it suffices to prove `(subst f ψ) ∧ φ ⊢
subst f θ`.  This is the workhorse for composing functional relations. -/
def conj_ex_elim {I J : Type u} (f : I → J) {φ : P I} {ψ θ : P J}
    (h : entails (conj (subst f ψ) φ) (subst f θ)) :
    entails (conj (ex f φ) ψ) θ :=
  le_trans (conj_comm (ex f φ) ψ) (le_trans (frobenius f φ ψ) (ex_adj_mpr h))

/-- Eliminate a reindexed existential on the left of an entailment, via
Beck–Chevalley: to prove `subst g (∃_f φ) ⊢ ψ` it suffices to prove, over the
pullback, `subst pbI φ ⊢ subst pbK ψ`. -/
def subst_ex_elim {I J K : Type u} (f : I → J) (g : K → J) {φ : P I} {ψ : P K}
    (h : entails (subst (fun s : { p : K × I // g p.1 = f p.2 } => s.1.2) φ)
                 (subst (fun s : { p : K × I // g p.1 = f p.2 } => s.1.1) ψ)) :
    entails (subst g (ex f φ)) ψ :=
  le_trans (beck_chevalley f g φ) (ex_adj_mpr h)

/-- Beck–Chevalley for an existential over the *middle* factor, reindexed along
`g : K → A × C` into the outer product.  `subst g (∃b. φ(a, b, c))` becomes a
clean existential `∃b. φ((g·).1, b, (g·).2)` over `K × B` — no pullback subtype
leaks out, which is what makes composing functional relations manageable. -/
def subst_ex_mid {A B C K : Type u} (g : K → A × C) (φ : P (A × B × C)) :
    entails (subst g (ex (fun d : A × B × C => (d.1, d.2.2)) φ))
            (ex (Prod.fst : K × B → K)
                (subst (fun p : K × B => ((g p.1).1, p.2, (g p.1).2)) φ)) := by
  refine subst_ex_elim (fun d : A × B × C => (d.1, d.2.2)) g ?_
  have hu := subst_mono
    (fun s : { p : K × (A × B × C) // g p.1 = ((fun d : A × B × C => (d.1, d.2.2)) p.2) } =>
      (s.1.1, s.1.2.2.1))
    (ex_unit (Prod.fst : K × B → K) (subst (fun p : K × B => ((g p.1).1, p.2, (g p.1).2)) φ))
  rw [← subst_comp, ← subst_comp] at hu
  refine le_trans ?_ hu
  rw [show (fun s : { p : K × (A × B × C) // g p.1 = ((fun d : A × B × C => (d.1, d.2.2)) p.2) } =>
            s.1.2)
        = ((fun p : K × B => ((g p.1).1, p.2, (g p.1).2)) ∘ fun s => (s.1.1, s.1.2.2.1)) from by
      funext s
      show s.1.2 = ((g s.1.1).1, s.1.2.2.1, (g s.1.1).2)
      rw [s.2]]
  exact le_refl _

end Tripos

end LeanExperiments.Realizability
