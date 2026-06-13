import LeanExperiments.Realizability.TriposClass

/-!
# Tripos → topos (Pitts construction): objects and morphisms

Given any `[Tripos P]`, we build the topos `Set[P]`.  This file establishes the
**category**: objects, morphisms, and (so far) the identity morphism.

* **Objects** are *partial equivalence relations* (PERs): a base type `I` with a
  predicate `ρ : P (I × I)` that is symmetric and transitive.  We read `ρ(x, y)`
  as "`x` and `y` are equal and both exist", and `ρ(x, x)` as "`x` exists".

* **Morphisms** `(I, ρ) → (J, σ)` are *functional relations* `F : P (I × J)`:
  predicates that are strict, relational (extensional), single-valued, and total
  — i.e. the internal-logic description of (the graph of) a function.  Two are
  identified when mutually entailed, so the hom-sets are quotients.

All entailments are `Tripos.entails` data (`⊢`), so realizers survive.  Working
inside `namespace Tripos` lets us name the interface operations directly.
-/

namespace LeanExperiments.Realizability

universe u v

open scoped Tripos

namespace Tripos

variable {P : Type u → Type v} [Tripos P]

/-! ### Objects: partial equivalence relations -/

/-- A **partial equivalence relation** in the tripos: a topos object. -/
structure PER (P : Type u → Type v) [Tripos P] where
  /-- The underlying type. -/
  carrier : Type u
  /-- The (partial) equality predicate; `rel (x, y)` reads "`x = y` and both exist". -/
  rel : P (carrier × carrier)
  /-- Symmetry: `ρ(x, y) ⊢ ρ(y, x)`. -/
  symm : rel ⊢ subst Prod.swap rel
  /-- Transitivity: `ρ(x, y) ∧ ρ(y, z) ⊢ ρ(x, z)`. -/
  trans :
    conj (subst (fun t : carrier × carrier × carrier => (t.1, t.2.1)) rel)
         (subst (fun t : carrier × carrier × carrier => (t.2.1, t.2.2)) rel)
      ⊢ subst (fun t : carrier × carrier × carrier => (t.1, t.2.2)) rel

namespace PER

/-- Symmetry along arbitrary coordinate maps: `ρ(a, b) ⊢ ρ(b, a)`. -/
def symm_at (X : PER P) {K : Type u} (a b : K → X.carrier) :
    subst (fun k => (a k, b k)) X.rel ⊢ subst (fun k => (b k, a k)) X.rel := by
  have h := subst_mono (fun k => (a k, b k)) X.symm
  simp only [← subst_comp] at h
  exact h

/-- Transitivity along arbitrary coordinate maps: `ρ(a, b) ∧ ρ(b, c) ⊢ ρ(a, c)`. -/
def trans_at (X : PER P) {K : Type u} (a b c : K → X.carrier) :
    conj (subst (fun k => (a k, b k)) X.rel) (subst (fun k => (b k, c k)) X.rel)
      ⊢ subst (fun k => (a k, c k)) X.rel := by
  have h := subst_mono (fun k => (a k, (b k, c k))) X.trans
  simp only [subst_conj, ← subst_comp] at h
  exact h

end PER

/-! ### Morphisms: functional relations -/

/-- A **functional relation** `X ⟶ Y`: a topos morphism (before quotienting). -/
structure FunRel (X Y : PER P) where
  /-- The relation; `rel (x, y)` reads "`F x = y`". -/
  rel : P (X.carrier × Y.carrier)
  /-- Strictness (domain): related elements have an existing domain value. -/
  strict_dom : rel ⊢ subst (fun p : X.carrier × Y.carrier => (p.1, p.1)) X.rel
  /-- Strictness (codomain): related elements have an existing codomain value. -/
  strict_cod : rel ⊢ subst (fun p : X.carrier × Y.carrier => (p.2, p.2)) Y.rel
  /-- Relational/extensional: `F(x, y) ∧ ρ(x, x') ∧ σ(y, y') ⊢ F(x', y')`. -/
  cong :
    conj (conj (subst (fun t : X.carrier × X.carrier × Y.carrier × Y.carrier => (t.1, t.2.2.1)) rel)
               (subst (fun t : X.carrier × X.carrier × Y.carrier × Y.carrier => (t.1, t.2.1)) X.rel))
         (subst (fun t : X.carrier × X.carrier × Y.carrier × Y.carrier => (t.2.2.1, t.2.2.2)) Y.rel)
      ⊢ subst (fun t : X.carrier × X.carrier × Y.carrier × Y.carrier => (t.2.1, t.2.2.2)) rel
  /-- Single-valued: `F(x, y) ∧ F(x, y') ⊢ σ(y, y')`. -/
  single :
    conj (subst (fun t : X.carrier × Y.carrier × Y.carrier => (t.1, t.2.1)) rel)
         (subst (fun t : X.carrier × Y.carrier × Y.carrier => (t.1, t.2.2)) rel)
      ⊢ subst (fun t : X.carrier × Y.carrier × Y.carrier => (t.2.1, t.2.2)) Y.rel
  /-- Total: every existing domain value is related to something. -/
  total :
    subst (fun x : X.carrier => (x, x)) X.rel
      ⊢ ex (Prod.fst : X.carrier × Y.carrier → X.carrier) rel

/-! ### The identity morphism -/

/-- The identity functional relation on `X` is the equality predicate `ρ` itself. -/
def idFunRel (X : PER P) : FunRel X X where
  rel := X.rel
  strict_dom :=
    le_trans (le_conj (subst_id_ge X.rel) X.symm)
      (X.trans_at (K := X.carrier × X.carrier) (fun p => p.1) (fun p => p.2) (fun p => p.1))
  strict_cod :=
    le_trans (le_conj X.symm (subst_id_ge X.rel))
      (X.trans_at (K := X.carrier × X.carrier) (fun p => p.2) (fun p => p.1) (fun p => p.2))
  cong := by
    have hsymm := X.symm_at (K := X.carrier × X.carrier × X.carrier × X.carrier)
      (fun t => t.1) (fun t => t.2.1)
    have ht1 := X.trans_at (K := X.carrier × X.carrier × X.carrier × X.carrier)
      (fun t => t.2.1) (fun t => t.1) (fun t => t.2.2.1)
    have ht2 := X.trans_at (K := X.carrier × X.carrier × X.carrier × X.carrier)
      (fun t => t.2.1) (fun t => t.2.2.1) (fun t => t.2.2.2)
    refine le_trans (le_conj (le_trans (le_conj (le_trans ?_ hsymm) ?_) ht1) ?_) ht2
    · exact le_trans (conj_le_left _ _) (conj_le_right _ _)
    · exact le_trans (conj_le_left _ _) (conj_le_left _ _)
    · exact conj_le_right _ _
  single := by
    have hsymm := X.symm_at (K := X.carrier × X.carrier × X.carrier)
      (fun t => t.1) (fun t => t.2.1)
    have ht := X.trans_at (K := X.carrier × X.carrier × X.carrier)
      (fun t => t.2.1) (fun t => t.1) (fun t => t.2.2)
    refine le_trans (le_conj (le_trans ?_ hsymm) ?_) ht
    · exact conj_le_left _ _
    · exact conj_le_right _ _
  total := by
    have h := subst_mono (fun x : X.carrier => (x, x))
      (ex_unit (Prod.fst : X.carrier × X.carrier → X.carrier) X.rel)
    rw [← subst_comp] at h
    exact le_trans h (subst_id_le _)

/-! ### Composition of functional relations -/

variable {X Y Z W : PER P}

/-- The composite relation: `(G ∘ F)(x, z) := ∃y. F(x, y) ∧ G(y, z)`, realized as
an existential over the middle coordinate `y`. -/
def compRel (F : FunRel X Y) (G : FunRel Y Z) : P (X.carrier × Z.carrier) :=
  ex (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.2))
     (conj (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.1)) F.rel)
           (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.2.1, d.2.2)) G.rel))

/-- Composition is monotone in both arguments — hence descends to the quotient. -/
def compRel_mono {F F' : FunRel X Y} {G G' : FunRel Y Z}
    (hF : F.rel ⊢ F'.rel) (hG : G.rel ⊢ G'.rel) :
    compRel F G ⊢ compRel F' G' :=
  ex_mono _ (conj_mono (subst_mono _ hF) (subst_mono _ hG))

/-- Strictness (domain) of the composite. -/
def compRel_strict_dom (F : FunRel X Y) (G : FunRel Y Z) :
    compRel F G ⊢ subst (fun p : X.carrier × Z.carrier => (p.1, p.1)) X.rel := by
  refine ex_adj_mpr (le_trans (conj_le_left _ _) ?_)
  rw [← subst_comp]
  have h := subst_mono (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.1)) F.strict_dom
  rw [← subst_comp] at h
  exact h

/-- Strictness (codomain) of the composite. -/
def compRel_strict_cod (F : FunRel X Y) (G : FunRel Y Z) :
    compRel F G ⊢ subst (fun p : X.carrier × Z.carrier => (p.2, p.2)) Z.rel := by
  refine ex_adj_mpr (le_trans (conj_le_right _ _) ?_)
  rw [← subst_comp]
  have h := subst_mono (fun d : X.carrier × Y.carrier × Z.carrier => (d.2.1, d.2.2)) G.strict_cod
  rw [← subst_comp] at h
  exact h

/-- Totality of the composite: every existing `x` is related to some `z`. -/
def compRel_total (F : FunRel X Y) (G : FunRel Y Z) :
    subst (fun x : X.carrier => (x, x)) X.rel
      ⊢ ex (Prod.fst : X.carrier × Z.carrier → X.carrier) (compRel F G) := by
  -- `key2 : F(x, y) ⊢ ∃z. G(y, z)`, over `E = Xc × Yc`.
  have key2 : F.rel ⊢ ex (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.1))
      (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.2.1, d.2.2)) G.rel) := by
    refine le_trans F.strict_cod ?_
    have hG := subst_mono (Prod.snd : X.carrier × Y.carrier → Y.carrier) G.total
    rw [← subst_comp] at hG
    refine le_trans hG ?_
    refine subst_ex_elim (Prod.fst : Y.carrier × Z.carrier → Y.carrier)
      (Prod.snd : X.carrier × Y.carrier → Y.carrier) ?_
    have hu := subst_mono
      (fun s : { p : (X.carrier × Y.carrier) × (Y.carrier × Z.carrier) //
          Prod.snd p.1 = Prod.fst p.2 } => (s.1.1.1, (s.1.1.2, s.1.2.2)))
      (ex_unit (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.1))
        (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.2.1, d.2.2)) G.rel))
    rw [← subst_comp, ← subst_comp] at hu
    refine le_trans ?_ hu
    rw [show (fun s : { p : (X.carrier × Y.carrier) × (Y.carrier × Z.carrier) //
            Prod.snd p.1 = Prod.fst p.2 } => s.1.2)
          = ((fun d : X.carrier × Y.carrier × Z.carrier => (d.2.1, d.2.2)) ∘
              (fun s => (s.1.1.1, (s.1.1.2, s.1.2.2)))) from by
      funext s
      show s.1.2 = (s.1.1.2, s.1.2.2)
      rw [s.2]]
    exact le_refl _
  -- `key1 : F(x, y) ⊢ ∃z. F(x, y) ∧ G(y, z)`, via Frobenius.
  have key1 : F.rel ⊢ ex (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.1))
      (conj (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.1)) F.rel)
            (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.2.1, d.2.2)) G.rel)) :=
    le_trans (le_conj (le_refl F.rel) key2)
      (frobenius (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.1)) _ F.rel)
  -- Push the outer existential `∃y` and reassociate.
  refine le_trans (le_trans F.total (ex_mono (Prod.fst : X.carrier × Y.carrier → X.carrier) key1))
    (le_trans (ex_comp_le (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.1)) Prod.fst _)
      (ex_comp_ge (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.2)) Prod.fst _))

/-! ### The category structure -/

/-- Two functional relations represent the same morphism iff mutually entailed. -/
def FunRel.equiv {X Y : PER P} (F G : FunRel X Y) : Prop :=
  Nonempty (F.rel ⊢ G.rel) ∧ Nonempty (G.rel ⊢ F.rel)

/-- Mutual entailment is an equivalence on functional relations. -/
instance homSetoid (X Y : PER P) : Setoid (FunRel X Y) where
  r := FunRel.equiv
  iseqv :=
    { refl := fun _ => ⟨⟨le_refl _⟩, ⟨le_refl _⟩⟩
      symm := fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩
      trans := fun ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ =>
        ⟨match h₁, h₃ with | ⟨e₁⟩, ⟨e₃⟩ => ⟨le_trans e₁ e₃⟩,
         match h₄, h₂ with | ⟨e₄⟩, ⟨e₂⟩ => ⟨le_trans e₄ e₂⟩⟩ }

/-- Morphisms of the topos: functional relations up to mutual entailment. -/
def Hom (X Y : PER P) : Type (max u v) := Quotient (homSetoid X Y)

/-- The identity morphism. -/
def Hom.id (X : PER P) : Hom X X := Quotient.mk _ (idFunRel X)

end Tripos

end LeanExperiments.Realizability
