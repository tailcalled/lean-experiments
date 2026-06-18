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

/-- Existence on the left: `ρ(a, b) ⊢ ρ(a, a)`. -/
def refl_left_at (X : PER P) {K : Type u} (a b : K → X.carrier) :
    subst (fun k => (a k, b k)) X.rel ⊢ subst (fun k => (a k, a k)) X.rel :=
  le_trans (le_conj (le_refl _) (X.symm_at a b)) (X.trans_at a b a)

/-- Existence on the right: `ρ(a, b) ⊢ ρ(b, b)`. -/
def refl_right_at (X : PER P) {K : Type u} (a b : K → X.carrier) :
    subst (fun k => (a k, b k)) X.rel ⊢ subst (fun k => (b k, b k)) X.rel :=
  le_trans (le_conj (X.symm_at a b) (le_refl _)) (X.trans_at b a b)

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

/-- Single-valuedness of the composite. -/
def compRel_single (F : FunRel X Y) (G : FunRel Y Z) :
    conj (subst (fun t : X.carrier × Z.carrier × Z.carrier => (t.1, t.2.1)) (compRel F G))
         (subst (fun t : X.carrier × Z.carrier × Z.carrier => (t.1, t.2.2)) (compRel F G))
      ⊢ subst (fun t : X.carrier × Z.carrier × Z.carrier => (t.2.1, t.2.2)) Z.rel := by
  -- Expose `∃y` from the first composite.
  refine le_trans (conj_mono
    (subst_ex_mid (fun t : X.carrier × Z.carrier × Z.carrier => (t.1, t.2.1))
      (conj (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.1)) F.rel)
            (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.2.1, d.2.2)) G.rel)))
    (le_refl _)) ?_
  refine conj_ex_elim Prod.fst ?_
  -- Expose `∃y'` from the second composite.
  rw [← subst_comp (Prod.fst : (X.carrier × Z.carrier × Z.carrier) × Y.carrier →
        X.carrier × Z.carrier × Z.carrier)
      (fun t : X.carrier × Z.carrier × Z.carrier => (t.1, t.2.2)) (compRel F G)]
  refine le_trans (conj_mono
    (subst_ex_mid ((fun t : X.carrier × Z.carrier × Z.carrier => (t.1, t.2.2)) ∘
        (Prod.fst : (X.carrier × Z.carrier × Z.carrier) × Y.carrier →
          X.carrier × Z.carrier × Z.carrier))
      (conj (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.1)) F.rel)
            (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.2.1, d.2.2)) G.rel)))
    (le_refl _)) ?_
  refine conj_ex_elim Prod.fst ?_
  -- Now over `W`, with `x, y, y', z, z'` all present.  Reindexed `F`/`G` laws:
  have hFs : conj (subst (fun w : ((X.carrier × Z.carrier × Z.carrier) × Y.carrier) × Y.carrier =>
                    (w.1.1.1, w.1.2)) F.rel)
                  (subst (fun w => (w.1.1.1, w.2)) F.rel)
              ⊢ subst (fun w => (w.1.2, w.2)) Y.rel := by
    have h := subst_mono (fun w : ((X.carrier × Z.carrier × Z.carrier) × Y.carrier) × Y.carrier =>
      (w.1.1.1, w.1.2, w.2)) F.single
    simp only [subst_conj, ← subst_comp] at h
    exact h
  have hGcod : subst (fun w : ((X.carrier × Z.carrier × Z.carrier) × Y.carrier) × Y.carrier =>
                  (w.1.2, w.1.1.2.1)) G.rel
                ⊢ subst (fun w => (w.1.1.2.1, w.1.1.2.1)) Z.rel := by
    have h := subst_mono (fun w : ((X.carrier × Z.carrier × Z.carrier) × Y.carrier) × Y.carrier =>
      (w.1.2, w.1.1.2.1)) G.strict_cod
    rw [← subst_comp] at h
    exact h
  have hGcong : conj (conj (subst (fun w : ((X.carrier × Z.carrier × Z.carrier) × Y.carrier) ×
                          Y.carrier => (w.1.2, w.1.1.2.1)) G.rel)
                          (subst (fun w => (w.1.2, w.2)) Y.rel))
                     (subst (fun w => (w.1.1.2.1, w.1.1.2.1)) Z.rel)
                 ⊢ subst (fun w => (w.2, w.1.1.2.1)) G.rel := by
    have h := subst_mono (fun w : ((X.carrier × Z.carrier × Z.carrier) × Y.carrier) × Y.carrier =>
      (w.1.2, w.2, w.1.1.2.1, w.1.1.2.1)) G.cong
    simp only [subst_conj, ← subst_comp] at h
    exact h
  have hGs : conj (subst (fun w : ((X.carrier × Z.carrier × Z.carrier) × Y.carrier) × Y.carrier =>
                    (w.2, w.1.1.2.1)) G.rel)
                  (subst (fun w => (w.2, w.1.1.2.2)) G.rel)
              ⊢ subst (fun w => (w.1.1.2.1, w.1.1.2.2)) Z.rel := by
    have h := subst_mono (fun w : ((X.carrier × Z.carrier × Z.carrier) × Y.carrier) × Y.carrier =>
      (w.2, w.1.1.2.1, w.1.1.2.2)) G.single
    simp only [subst_conj, ← subst_comp] at h
    exact h
  -- Expand the two composite conjunctions and assemble.
  simp only [subst_conj, ← subst_comp]
  refine le_trans (le_conj ?_ ?_) hGs
  · refine le_trans (le_conj (le_conj ?_ ?_) ?_) hGcong
    · exact le_trans (conj_le_left _ _) (conj_le_right _ _)
    · exact le_trans (le_conj (le_trans (conj_le_left _ _) (conj_le_left _ _))
        (le_trans (conj_le_right _ _) (conj_le_left _ _))) hFs
    · exact le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _)) hGcod
  · exact le_trans (conj_le_right _ _) (conj_le_right _ _)

/-- Relationality/extensionality of the composite. -/
def compRel_cong (F : FunRel X Y) (G : FunRel Y Z) :
    conj (conj (subst (fun t : X.carrier × X.carrier × Z.carrier × Z.carrier =>
                  (t.1, t.2.2.1)) (compRel F G))
               (subst (fun t => (t.1, t.2.1)) X.rel))
         (subst (fun t => (t.2.2.1, t.2.2.2)) Z.rel)
      ⊢ subst (fun t : X.carrier × X.carrier × Z.carrier × Z.carrier =>
          (t.2.1, t.2.2.2)) (compRel F G) := by
  -- Bring `compRel(x,z)` to the top and expose its `∃y`.
  refine le_trans (conj_assoc_left _ _ _) ?_
  refine le_trans (conj_mono
    (subst_ex_mid (fun t : X.carrier × X.carrier × Z.carrier × Z.carrier => (t.1, t.2.2.1))
      (conj (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.1)) F.rel)
            (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.2.1, d.2.2)) G.rel)))
    (le_refl _)) ?_
  refine conj_ex_elim Prod.fst ?_
  -- `RHS = compRel(x',z')`; reintroduce its `∃y` with the same `y`.
  rw [← subst_comp]
  refine le_trans ?_
    (by
      have h := subst_mono
        (fun p : (X.carrier × X.carrier × Z.carrier × Z.carrier) × Y.carrier =>
          (p.1.2.1, p.2, p.1.2.2.2))
        (ex_unit (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.2))
          (conj (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.1)) F.rel)
                (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.2.1, d.2.2)) G.rel)))
      rw [← subst_comp] at h
      exact h)
  -- Reindexed `F`/`G` laws over `W₂ = (X×X×Z×Z) × Y`.
  have hFcong : conj (conj (subst (fun p : (X.carrier × X.carrier × Z.carrier × Z.carrier) ×
                          Y.carrier => (p.1.1, p.2)) F.rel)
                          (subst (fun p => (p.1.1, p.1.2.1)) X.rel))
                     (subst (fun p => (p.2, p.2)) Y.rel)
                 ⊢ subst (fun p => (p.1.2.1, p.2)) F.rel := by
    have h := subst_mono (fun p : (X.carrier × X.carrier × Z.carrier × Z.carrier) × Y.carrier =>
      (p.1.1, p.1.2.1, p.2, p.2)) F.cong
    simp only [subst_conj, ← subst_comp] at h
    exact h
  have hFcod : subst (fun p : (X.carrier × X.carrier × Z.carrier × Z.carrier) × Y.carrier =>
                  (p.1.1, p.2)) F.rel
                ⊢ subst (fun p => (p.2, p.2)) Y.rel := by
    have h := subst_mono (fun p : (X.carrier × X.carrier × Z.carrier × Z.carrier) × Y.carrier =>
      (p.1.1, p.2)) F.strict_cod
    rw [← subst_comp] at h
    exact h
  have hGcong : conj (conj (subst (fun p : (X.carrier × X.carrier × Z.carrier × Z.carrier) ×
                          Y.carrier => (p.2, p.1.2.2.1)) G.rel)
                          (subst (fun p => (p.2, p.2)) Y.rel))
                     (subst (fun p => (p.1.2.2.1, p.1.2.2.2)) Z.rel)
                 ⊢ subst (fun p => (p.2, p.1.2.2.2)) G.rel := by
    have h := subst_mono (fun p : (X.carrier × X.carrier × Z.carrier × Z.carrier) × Y.carrier =>
      (p.2, p.2, p.1.2.2.1, p.1.2.2.2)) G.cong
    simp only [subst_conj, ← subst_comp] at h
    exact h
  have hGdom : subst (fun p : (X.carrier × X.carrier × Z.carrier × Z.carrier) × Y.carrier =>
                  (p.2, p.1.2.2.1)) G.rel
                ⊢ subst (fun p => (p.2, p.2)) Y.rel := by
    have h := subst_mono (fun p : (X.carrier × X.carrier × Z.carrier × Z.carrier) × Y.carrier =>
      (p.2, p.1.2.2.1)) G.strict_dom
    rw [← subst_comp] at h
    exact h
  -- Expand and assemble.
  simp only [subst_conj, ← subst_comp]
  refine le_conj ?_ ?_
  · refine le_trans (le_conj (le_conj ?_ ?_) ?_) hFcong
    · exact le_trans (conj_le_right _ _) (conj_le_left _ _)
    · exact le_trans (conj_le_left _ _) (conj_le_left _ _)
    · exact le_trans (le_trans (conj_le_right _ _) (conj_le_left _ _)) hFcod
  · refine le_trans (le_conj (le_conj ?_ ?_) ?_) hGcong
    · exact le_trans (conj_le_right _ _) (conj_le_right _ _)
    · exact le_trans (le_trans (conj_le_right _ _) (conj_le_right _ _)) hGdom
    · exact le_trans (conj_le_left _ _) (conj_le_right _ _)

/-- The composite functional relation `G ∘ F`, a genuine morphism `X ⟶ Z`. -/
def compFunRel (F : FunRel X Y) (G : FunRel Y Z) : FunRel X Z where
  rel := compRel F G
  strict_dom := compRel_strict_dom F G
  strict_cod := compRel_strict_cod F G
  cong := compRel_cong F G
  single := compRel_single F G
  total := compRel_total F G

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

/-- Composition of morphisms (`g ∘ f`), well-defined on the quotient by
`compRel_mono`. -/
def Hom.comp {X Y Z : PER P} (g : Hom Y Z) (f : Hom X Y) : Hom X Z :=
  Quotient.liftOn₂ f g (fun F G => (Quotient.mk _ (compFunRel F G) : Hom X Z))
    (fun _ _ _ _ hF hG => Quotient.sound
      ⟨match hF.1, hG.1 with | ⟨a⟩, ⟨b⟩ => ⟨compRel_mono a b⟩,
       match hF.2, hG.2 with | ⟨a⟩, ⟨b⟩ => ⟨compRel_mono a b⟩⟩)

/-! ### Associativity, via a canonical "triple composite" -/

/-- The canonical triple composite `∃(y,z). F(x,y) ∧ G(y,z) ∧ H(z,w)`. -/
def tripleRel (F : FunRel X Y) (G : FunRel Y Z) (H : FunRel Z W) :
    P (X.carrier × W.carrier) :=
  ex (fun e : X.carrier × Y.carrier × Z.carrier × W.carrier => (e.1, e.2.2.2))
    (conj (conj (subst (fun e => (e.1, e.2.1)) F.rel)
                (subst (fun e => (e.2.1, e.2.2.1)) G.rel))
          (subst (fun e => (e.2.2.1, e.2.2.2)) H.rel))

/-- `(H ∘ G) ∘-nested F ⊢ triple`. -/
def tripleRel_left_fwd (F : FunRel X Y) (G : FunRel Y Z) (H : FunRel Z W) :
    compRel F (compFunRel G H) ⊢ tripleRel F G H := by
  refine ex_adj_mpr ?_
  refine le_trans (conj_mono (le_refl _)
    (subst_ex_mid (fun d : X.carrier × Y.carrier × W.carrier => (d.2.1, d.2.2))
      (conj (subst (fun d : Y.carrier × Z.carrier × W.carrier => (d.1, d.2.1)) G.rel)
            (subst (fun d : Y.carrier × Z.carrier × W.carrier => (d.2.1, d.2.2)) H.rel)))) ?_
  refine le_trans (conj_comm _ _) (conj_ex_elim Prod.fst ?_)
  rw [← subst_comp (Prod.fst : (X.carrier × Y.carrier × W.carrier) × Z.carrier →
        X.carrier × Y.carrier × W.carrier)
      (fun d : X.carrier × Y.carrier × W.carrier => (d.1, d.2.2)) (tripleRel F G H)]
  refine le_trans ?_ (by
    have h := subst_mono (fun p : (X.carrier × Y.carrier × W.carrier) × Z.carrier =>
        (p.1.1, p.1.2.1, p.2, p.1.2.2))
      (ex_unit (fun e : X.carrier × Y.carrier × Z.carrier × W.carrier => (e.1, e.2.2.2))
        (conj (conj (subst (fun e => (e.1, e.2.1)) F.rel)
                    (subst (fun e => (e.2.1, e.2.2.1)) G.rel))
              (subst (fun e => (e.2.2.1, e.2.2.2)) H.rel)))
    rw [← subst_comp] at h
    exact h)
  simp only [subst_conj, ← subst_comp]
  refine le_conj (le_conj ?_ ?_) ?_
  · exact conj_le_left _ _
  · exact le_trans (conj_le_right _ _) (conj_le_left _ _)
  · exact le_trans (conj_le_right _ _) (conj_le_right _ _)

/-- `triple ⊢ (H ∘ G) ∘-nested F`. -/
def tripleRel_left_bwd (F : FunRel X Y) (G : FunRel Y Z) (H : FunRel Z W) :
    tripleRel F G H ⊢ compRel F (compFunRel G H) := by
  refine ex_adj_mpr ?_
  refine le_trans ?_ (by
    have h := subst_mono (fun e : X.carrier × Y.carrier × Z.carrier × W.carrier =>
        (e.1, e.2.1, e.2.2.2))
      (ex_unit (fun d : X.carrier × Y.carrier × W.carrier => (d.1, d.2.2))
        (conj (subst (fun d : X.carrier × Y.carrier × W.carrier => (d.1, d.2.1)) F.rel)
              (subst (fun d : X.carrier × Y.carrier × W.carrier => (d.2.1, d.2.2))
                (compRel G H))))
    rw [← subst_comp] at h
    exact h)
  rw [subst_conj]
  refine le_conj ?_ ?_
  · rw [← subst_comp]
    exact le_trans (conj_le_left _ _) (conj_le_left _ _)
  · rw [← subst_comp]
    refine le_trans ?_ (by
      have h := subst_mono (fun e : X.carrier × Y.carrier × Z.carrier × W.carrier =>
          (e.2.1, e.2.2.1, e.2.2.2))
        (ex_unit (fun d : Y.carrier × Z.carrier × W.carrier => (d.1, d.2.2))
          (conj (subst (fun d : Y.carrier × Z.carrier × W.carrier => (d.1, d.2.1)) G.rel)
                (subst (fun d : Y.carrier × Z.carrier × W.carrier => (d.2.1, d.2.2)) H.rel)))
      rw [← subst_comp] at h
      exact h)
    rw [subst_conj, ← subst_comp, ← subst_comp]
    exact le_conj (le_trans (conj_le_left _ _) (conj_le_right _ _)) (conj_le_right _ _)

/-- `(H ∘ G) ∘ F`-right ⊢ triple. -/
def tripleRel_right_fwd (F : FunRel X Y) (G : FunRel Y Z) (H : FunRel Z W) :
    compRel (compFunRel F G) H ⊢ tripleRel F G H := by
  refine ex_adj_mpr ?_
  refine le_trans (conj_mono
    (subst_ex_mid (fun d : X.carrier × Z.carrier × W.carrier => (d.1, d.2.1))
      (conj (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.1)) F.rel)
            (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.2.1, d.2.2)) G.rel)))
    (le_refl _)) (conj_ex_elim Prod.fst ?_)
  rw [← subst_comp (Prod.fst : (X.carrier × Z.carrier × W.carrier) × Y.carrier →
        X.carrier × Z.carrier × W.carrier)
      (fun d : X.carrier × Z.carrier × W.carrier => (d.1, d.2.2)) (tripleRel F G H)]
  refine le_trans ?_ (by
    have h := subst_mono (fun p : (X.carrier × Z.carrier × W.carrier) × Y.carrier =>
        (p.1.1, p.2, p.1.2.1, p.1.2.2))
      (ex_unit (fun e : X.carrier × Y.carrier × Z.carrier × W.carrier => (e.1, e.2.2.2))
        (conj (conj (subst (fun e => (e.1, e.2.1)) F.rel)
                    (subst (fun e => (e.2.1, e.2.2.1)) G.rel))
              (subst (fun e => (e.2.2.1, e.2.2.2)) H.rel)))
    rw [← subst_comp] at h
    exact h)
  simp only [subst_conj, ← subst_comp]
  refine le_conj (le_conj ?_ ?_) ?_
  · exact le_trans (conj_le_right _ _) (conj_le_left _ _)
  · exact le_trans (conj_le_right _ _) (conj_le_right _ _)
  · exact conj_le_left _ _

/-- `triple ⊢ (H ∘ G) ∘ F`-right. -/
def tripleRel_right_bwd (F : FunRel X Y) (G : FunRel Y Z) (H : FunRel Z W) :
    tripleRel F G H ⊢ compRel (compFunRel F G) H := by
  refine ex_adj_mpr ?_
  refine le_trans ?_ (by
    have h := subst_mono (fun e : X.carrier × Y.carrier × Z.carrier × W.carrier =>
        (e.1, e.2.2.1, e.2.2.2))
      (ex_unit (fun d : X.carrier × Z.carrier × W.carrier => (d.1, d.2.2))
        (conj (subst (fun d : X.carrier × Z.carrier × W.carrier => (d.1, d.2.1)) (compRel F G))
              (subst (fun d : X.carrier × Z.carrier × W.carrier => (d.2.1, d.2.2)) H.rel)))
    rw [← subst_comp] at h
    exact h)
  rw [subst_conj]
  refine le_conj ?_ ?_
  · rw [← subst_comp]
    refine le_trans ?_ (by
      have h := subst_mono (fun e : X.carrier × Y.carrier × Z.carrier × W.carrier =>
          (e.1, e.2.1, e.2.2.1))
        (ex_unit (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.2))
          (conj (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.1, d.2.1)) F.rel)
                (subst (fun d : X.carrier × Y.carrier × Z.carrier => (d.2.1, d.2.2)) G.rel)))
      rw [← subst_comp] at h
      exact h)
    rw [subst_conj, ← subst_comp, ← subst_comp]
    exact le_conj (le_trans (conj_le_left _ _) (conj_le_left _ _))
                  (le_trans (conj_le_left _ _) (conj_le_right _ _))
  · rw [← subst_comp]
    exact conj_le_right _ _

/-! ### Category laws -/

/-- Right identity: `f ∘ 𝟙 = f`. -/
theorem Hom.comp_id {X Y : PER P} (f : Hom X Y) : Hom.comp f (Hom.id X) = f := by
  induction f using Quotient.inductionOn with | _ Gf =>
  have hcong : conj (conj (subst (fun d : X.carrier × X.carrier × Y.carrier => (d.2.1, d.2.2)) Gf.rel)
                          (subst (fun d => (d.2.1, d.1)) X.rel))
                    (subst (fun d => (d.2.2, d.2.2)) Y.rel)
                ⊢ subst (fun d => (d.1, d.2.2)) Gf.rel := by
    have h := subst_mono (fun d : X.carrier × X.carrier × Y.carrier => (d.2.1, d.1, d.2.2, d.2.2))
      Gf.cong
    simp only [subst_conj, ← subst_comp] at h
    exact h
  have hcod : subst (fun d : X.carrier × X.carrier × Y.carrier => (d.2.1, d.2.2)) Gf.rel
                ⊢ subst (fun d => (d.2.2, d.2.2)) Y.rel := by
    have h := subst_mono (fun d : X.carrier × X.carrier × Y.carrier => (d.2.1, d.2.2))
      Gf.strict_cod
    rw [← subst_comp] at h
    exact h
  have fwd : compRel (idFunRel X) Gf ⊢ Gf.rel := by
    refine ex_adj_mpr (le_trans (le_conj (le_conj ?_ ?_) ?_) hcong)
    · exact conj_le_right _ _
    · exact le_trans (conj_le_left _ _)
        (X.symm_at (fun d : X.carrier × X.carrier × Y.carrier => d.1) (fun d => d.2.1))
    · exact le_trans (conj_le_right _ _) hcod
  have bwd : Gf.rel ⊢ compRel (idFunRel X) Gf := by
    have h := subst_mono (fun p : X.carrier × Y.carrier => (p.1, p.1, p.2))
      (ex_unit (fun d : X.carrier × X.carrier × Y.carrier => (d.1, d.2.2))
        (conj (subst (fun d : X.carrier × X.carrier × Y.carrier => (d.1, d.2.1)) X.rel)
              (subst (fun d : X.carrier × X.carrier × Y.carrier => (d.2.1, d.2.2)) Gf.rel)))
    rw [← subst_comp] at h
    refine le_trans ?_ (le_trans h (subst_id_le _))
    rw [subst_conj, ← subst_comp, ← subst_comp]
    exact le_conj Gf.strict_dom (subst_id_ge _)
  exact Quotient.sound ⟨⟨fwd⟩, ⟨bwd⟩⟩

/-- Left identity: `𝟙 ∘ f = f`. -/
theorem Hom.id_comp {X Y : PER P} (f : Hom X Y) : Hom.comp (Hom.id Y) f = f := by
  induction f using Quotient.inductionOn with | _ Gf =>
  have hcong : conj (conj (subst (fun d : X.carrier × Y.carrier × Y.carrier => (d.1, d.2.1)) Gf.rel)
                          (subst (fun d => (d.1, d.1)) X.rel))
                    (subst (fun d => (d.2.1, d.2.2)) Y.rel)
                ⊢ subst (fun d => (d.1, d.2.2)) Gf.rel := by
    have h := subst_mono (fun d : X.carrier × Y.carrier × Y.carrier => (d.1, d.1, d.2.1, d.2.2))
      Gf.cong
    simp only [subst_conj, ← subst_comp] at h
    exact h
  have hdom : subst (fun d : X.carrier × Y.carrier × Y.carrier => (d.1, d.2.1)) Gf.rel
                ⊢ subst (fun d => (d.1, d.1)) X.rel := by
    have h := subst_mono (fun d : X.carrier × Y.carrier × Y.carrier => (d.1, d.2.1))
      Gf.strict_dom
    rw [← subst_comp] at h
    exact h
  have fwd : compRel Gf (idFunRel Y) ⊢ Gf.rel := by
    refine ex_adj_mpr (le_trans (le_conj (le_conj ?_ ?_) ?_) hcong)
    · exact conj_le_left _ _
    · exact le_trans (conj_le_left _ _) hdom
    · exact conj_le_right _ _
  have bwd : Gf.rel ⊢ compRel Gf (idFunRel Y) := by
    have h := subst_mono (fun p : X.carrier × Y.carrier => (p.1, p.2, p.2))
      (ex_unit (fun d : X.carrier × Y.carrier × Y.carrier => (d.1, d.2.2))
        (conj (subst (fun d : X.carrier × Y.carrier × Y.carrier => (d.1, d.2.1)) Gf.rel)
              (subst (fun d : X.carrier × Y.carrier × Y.carrier => (d.2.1, d.2.2)) Y.rel)))
    rw [← subst_comp] at h
    refine le_trans ?_ (le_trans h (subst_id_le _))
    rw [subst_conj, ← subst_comp, ← subst_comp]
    exact le_conj (subst_id_ge _) Gf.strict_cod
  exact Quotient.sound ⟨⟨fwd⟩, ⟨bwd⟩⟩

/-- Associativity: `(h ∘ g) ∘ f = h ∘ (g ∘ f)`. -/
theorem Hom.comp_assoc {X Y Z W : PER P} (h : Hom Z W) (g : Hom Y Z) (f : Hom X Y) :
    Hom.comp (Hom.comp h g) f = Hom.comp h (Hom.comp g f) := by
  induction f using Quotient.inductionOn with | _ F =>
  induction g using Quotient.inductionOn with | _ G =>
  induction h using Quotient.inductionOn with | _ H =>
  exact Quotient.sound
    ⟨⟨le_trans (tripleRel_left_fwd F G H) (tripleRel_right_bwd F G H)⟩,
     ⟨le_trans (tripleRel_right_fwd F G H) (tripleRel_left_bwd F G H)⟩⟩

/-! ### Terminal object -/

/-- The terminal object: the point, carrying the top predicate. -/
def terminal : PER P where
  carrier := PUnit
  rel := top
  symm := by simp only [subst_top]; exact le_refl _
  trans := by simp only [subst_top]; exact le_top _

/-- The terminal functional relation `X ⟶ 𝟙`: relate `x` to the point iff `x`
exists.  Its relation is the extent predicate `E_X(x) = ρ(x, x)`. -/
def terminalFunRel (X : PER P) : FunRel X terminal where
  rel := subst (fun p : X.carrier × PUnit => (p.1, p.1)) X.rel
  strict_dom := le_refl _
  strict_cod := by
    show _ ⊢ subst (fun p : X.carrier × PUnit => (p.2, p.2)) (top : P (PUnit × PUnit))
    rw [subst_top]; exact le_top _
  cong := by
    simp only [← subst_comp]
    exact le_trans (le_conj
      (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
        (X.symm_at (K := X.carrier × X.carrier × PUnit × PUnit) (fun t => t.1) (fun t => t.2.1)))
      (le_trans (conj_le_left _ _) (conj_le_right _ _)))
      (X.trans_at (K := X.carrier × X.carrier × PUnit × PUnit)
        (fun t => t.2.1) (fun t => t.1) (fun t => t.2.1))
  single := by
    show _ ⊢ subst (fun t : X.carrier × PUnit × PUnit => (t.2.1, t.2.2)) (top : P (PUnit × PUnit))
    rw [subst_top]; exact le_top _
  total := by
    have h := subst_mono (fun x : X.carrier => (x, PUnit.unit))
      (ex_unit (Prod.fst : X.carrier × PUnit → X.carrier)
        (subst (fun p : X.carrier × PUnit => (p.1, p.1)) X.rel))
    simp only [← subst_comp] at h
    exact le_trans h (subst_id_le _)

/-- The terminal morphism `X ⟶ 𝟙`. -/
def terminalHom (X : PER P) : Hom X terminal := Quotient.mk _ (terminalFunRel X)

/-- Terminality: every morphism into `𝟙` equals the terminal one. -/
theorem terminalHom_unique {X : PER P} (f : Hom X terminal) : f = terminalHom X := by
  induction f using Quotient.inductionOn with | _ F =>
  refine Quotient.sound ⟨⟨F.strict_dom⟩, ⟨?_⟩⟩
  have h := subst_mono (Prod.fst : X.carrier × PUnit → X.carrier) F.total
  rw [← subst_comp] at h
  refine le_trans h (subst_ex_elim (Prod.fst : X.carrier × PUnit → X.carrier)
    (Prod.fst : X.carrier × PUnit → X.carrier) ?_)
  rw [show (fun s : { p : (X.carrier × PUnit) × (X.carrier × PUnit) //
          Prod.fst p.1 = Prod.fst p.2 } => s.1.1)
        = (fun s => s.1.2) from funext fun s => (Prod.ext_iff.mpr ⟨s.2, Subsingleton.elim _ _⟩)]
  exact le_refl _

/-! ### Binary products -/

/-- The product PER: `(x, y) ~ (x', y')` iff `x ~ x'` in `X` and `y ~ y'` in `Y`. -/
def prodPER (X Y : PER P) : PER P where
  carrier := X.carrier × Y.carrier
  rel :=
    conj (subst (fun q : (X.carrier × Y.carrier) × (X.carrier × Y.carrier) => (q.1.1, q.2.1)) X.rel)
         (subst (fun q => (q.1.2, q.2.2)) Y.rel)
  symm := by
    simp only [subst_conj, ← subst_comp]
    exact conj_mono
      (X.symm_at (K := (X.carrier × Y.carrier) × X.carrier × Y.carrier)
        (fun q => q.1.1) (fun q => q.2.1))
      (Y.symm_at (K := (X.carrier × Y.carrier) × X.carrier × Y.carrier)
        (fun q => q.1.2) (fun q => q.2.2))
  trans := by
    simp only [subst_conj, ← subst_comp]
    refine le_conj ?_ ?_
    · exact le_trans (le_conj (le_trans (conj_le_left _ _) (conj_le_left _ _))
        (le_trans (conj_le_right _ _) (conj_le_left _ _)))
        (X.trans_at (K := (X.carrier × Y.carrier) × (X.carrier × Y.carrier) × X.carrier × Y.carrier)
          (fun t => t.1.1) (fun t => t.2.1.1) (fun t => t.2.2.1))
    · exact le_trans (le_conj (le_trans (conj_le_left _ _) (conj_le_right _ _))
        (le_trans (conj_le_right _ _) (conj_le_right _ _)))
        (Y.trans_at (K := (X.carrier × Y.carrier) × (X.carrier × Y.carrier) × X.carrier × Y.carrier)
          (fun t => t.1.2) (fun t => t.2.1.2) (fun t => t.2.2.2))

/-- First projection `X × Y ⟶ X`: relate `(x, y)` to `x'` iff `x ~ x'` and `y`
exists. -/
def proj1 (X Y : PER P) : FunRel (prodPER X Y) X where
  rel := conj (subst (fun p : (X.carrier × Y.carrier) × X.carrier => (p.1.1, p.2)) X.rel)
              (subst (fun p => (p.1.2, p.1.2)) Y.rel)
  strict_dom := by
    simp only [prodPER, subst_conj, ← subst_comp]
    exact conj_mono
      (X.refl_left_at (K := (X.carrier × Y.carrier) × X.carrier) (fun p => p.1.1) (fun p => p.2))
      (le_refl _)
  strict_cod := by
    refine le_trans (conj_le_left _ _) ?_
    exact X.refl_right_at (K := (X.carrier × Y.carrier) × X.carrier) (fun p => p.1.1) (fun p => p.2)
  cong := by
    simp only [prodPER, subst_conj, ← subst_comp]
    refine le_conj ?_ ?_
    · -- ρ_X(p'x, x'') from ρ_X(px,x'), ρ_X(px,p'x), ρ_X(x',x'')
      refine le_trans (le_conj (le_trans (le_conj (le_trans ?_
          (X.symm_at (K := (X.carrier × Y.carrier) × (X.carrier × Y.carrier) × X.carrier × X.carrier)
            (fun t => t.1.1) (fun t => t.2.1.1))) ?_)
          (X.trans_at (K := (X.carrier × Y.carrier) × (X.carrier × Y.carrier) × X.carrier × X.carrier)
            (fun t => t.2.1.1) (fun t => t.1.1) (fun t => t.2.2.1))) ?_)
        (X.trans_at (K := (X.carrier × Y.carrier) × (X.carrier × Y.carrier) × X.carrier × X.carrier)
          (fun t => t.2.1.1) (fun t => t.2.2.1) (fun t => t.2.2.2))
      · exact le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _)) (conj_le_left _ _)
      · exact le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) (conj_le_left _ _)
      · exact conj_le_right _ _
    · -- E_Y(p'y) from ρ_Y(py, p'y)
      refine le_trans (le_conj (le_trans ?_
          (Y.symm_at (K := (X.carrier × Y.carrier) × (X.carrier × Y.carrier) × X.carrier × X.carrier)
            (fun t => t.1.2) (fun t => t.2.1.2))) ?_)
        (Y.trans_at (K := (X.carrier × Y.carrier) × (X.carrier × Y.carrier) × X.carrier × X.carrier)
          (fun t => t.2.1.2) (fun t => t.1.2) (fun t => t.2.1.2))
      · exact le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _)) (conj_le_right _ _)
      · exact le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _)) (conj_le_right _ _)
  single := by
    simp only [subst_conj, ← subst_comp]
    exact le_trans (le_conj
      (le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _))
        (X.symm_at (K := (X.carrier × Y.carrier) × X.carrier × X.carrier)
          (fun s => s.1.1) (fun s => s.2.1)))
      (le_trans (conj_le_right _ _) (conj_le_left _ _)))
      (X.trans_at (K := (X.carrier × Y.carrier) × X.carrier × X.carrier)
        (fun s => s.2.1) (fun s => s.1.1) (fun s => s.2.2))
  total := by
    have h := subst_mono (fun q : X.carrier × Y.carrier => (q, q.1))
      (ex_unit (Prod.fst : (X.carrier × Y.carrier) × X.carrier → X.carrier × Y.carrier)
        (conj (subst (fun p : (X.carrier × Y.carrier) × X.carrier => (p.1.1, p.2)) X.rel)
              (subst (fun p => (p.1.2, p.1.2)) Y.rel)))
    simp only [← subst_comp] at h
    refine le_trans ?_ (le_trans h (subst_id_le _))
    simp only [prodPER, subst_conj, ← subst_comp]
    exact le_refl _

/-- The pairing `⟨f, g⟩ : Z ⟶ X × Y` of `f : Z ⟶ X` and `g : Z ⟶ Y`. -/
def pairFunRel {Z : PER P} (f : FunRel Z X) (g : FunRel Z Y) : FunRel Z (prodPER X Y) where
  rel := conj (subst (fun p : Z.carrier × (X.carrier × Y.carrier) => (p.1, p.2.1)) f.rel)
              (subst (fun p => (p.1, p.2.2)) g.rel)
  strict_dom := by
    refine le_trans (conj_le_left _ _) ?_
    have h := subst_mono (fun p : Z.carrier × (X.carrier × Y.carrier) => (p.1, p.2.1)) f.strict_dom
    rw [← subst_comp] at h; exact h
  strict_cod := by
    simp only [prodPER, subst_conj, ← subst_comp]
    refine conj_mono ?_ ?_
    · have h := subst_mono (fun p : Z.carrier × (X.carrier × Y.carrier) => (p.1, p.2.1)) f.strict_cod
      rw [← subst_comp] at h; exact h
    · have h := subst_mono (fun p : Z.carrier × (X.carrier × Y.carrier) => (p.1, p.2.2)) g.strict_cod
      rw [← subst_comp] at h; exact h
  single := by
    simp only [prodPER, subst_conj, ← subst_comp]
    have hf := subst_mono
      (fun t : Z.carrier × (X.carrier × Y.carrier) × (X.carrier × Y.carrier) =>
        (t.1, t.2.1.1, t.2.2.1)) f.single
    have hg := subst_mono
      (fun t : Z.carrier × (X.carrier × Y.carrier) × (X.carrier × Y.carrier) =>
        (t.1, t.2.1.2, t.2.2.2)) g.single
    simp only [subst_conj, ← subst_comp] at hf hg
    refine le_conj ?_ ?_
    · exact le_trans (le_conj (le_trans (conj_le_left _ _) (conj_le_left _ _))
        (le_trans (conj_le_right _ _) (conj_le_left _ _))) hf
    · exact le_trans (le_conj (le_trans (conj_le_left _ _) (conj_le_right _ _))
        (le_trans (conj_le_right _ _) (conj_le_right _ _))) hg
  cong := by
    simp only [prodPER, subst_conj, ← subst_comp]
    have hf := subst_mono
      (fun t : Z.carrier × Z.carrier × (X.carrier × Y.carrier) × (X.carrier × Y.carrier) =>
        (t.1, t.2.1, t.2.2.1.1, t.2.2.2.1)) f.cong
    have hg := subst_mono
      (fun t : Z.carrier × Z.carrier × (X.carrier × Y.carrier) × (X.carrier × Y.carrier) =>
        (t.1, t.2.1, t.2.2.1.2, t.2.2.2.2)) g.cong
    simp only [subst_conj, ← subst_comp] at hf hg
    refine le_conj ?_ ?_
    · exact le_trans (le_conj (le_conj
        (le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) (conj_le_left _ _))
        (le_trans (conj_le_left _ _) (conj_le_right _ _)))
        (le_trans (conj_le_right _ _) (conj_le_left _ _))) hf
    · exact le_trans (le_conj (le_conj
        (le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) (conj_le_right _ _))
        (le_trans (conj_le_left _ _) (conj_le_right _ _)))
        (le_trans (conj_le_right _ _) (conj_le_right _ _))) hg
  total := by
    have key2 : f.rel ⊢ ex (fun d : Z.carrier × X.carrier × Y.carrier => (d.1, d.2.1))
        (subst (fun d : Z.carrier × X.carrier × Y.carrier => (d.1, d.2.2)) g.rel) := by
      refine le_trans f.strict_dom ?_
      have hg := subst_mono (Prod.fst : Z.carrier × X.carrier → Z.carrier) g.total
      rw [← subst_comp] at hg
      refine le_trans hg ?_
      refine subst_ex_elim (Prod.fst : Z.carrier × Y.carrier → Z.carrier)
        (Prod.fst : Z.carrier × X.carrier → Z.carrier) ?_
      have hu := subst_mono
        (fun s : { p : (Z.carrier × X.carrier) × (Z.carrier × Y.carrier) //
            Prod.fst p.1 = Prod.fst p.2 } => (s.1.1.1, s.1.1.2, s.1.2.2))
        (ex_unit (fun d : Z.carrier × X.carrier × Y.carrier => (d.1, d.2.1))
          (subst (fun d : Z.carrier × X.carrier × Y.carrier => (d.1, d.2.2)) g.rel))
      rw [← subst_comp, ← subst_comp] at hu
      refine le_trans ?_ hu
      rw [show (fun s : { p : (Z.carrier × X.carrier) × (Z.carrier × Y.carrier) //
              Prod.fst p.1 = Prod.fst p.2 } => s.1.2)
            = ((fun d : Z.carrier × X.carrier × Y.carrier => (d.1, d.2.2)) ∘
                fun s => (s.1.1.1, s.1.1.2, s.1.2.2)) from by
          funext s
          show s.1.2 = (s.1.1.1, s.1.2.2)
          rw [s.2]]
      exact le_refl _
    have key1 : f.rel ⊢ ex (fun d : Z.carrier × X.carrier × Y.carrier => (d.1, d.2.1))
        (conj (subst (fun d : Z.carrier × X.carrier × Y.carrier => (d.1, d.2.1)) f.rel)
              (subst (fun d => (d.1, d.2.2)) g.rel)) :=
      le_trans (le_conj (le_refl _) key2)
        (frobenius (fun d : Z.carrier × X.carrier × Y.carrier => (d.1, d.2.1)) _ f.rel)
    exact le_trans (le_trans f.total (ex_mono (Prod.fst : Z.carrier × X.carrier → Z.carrier) key1))
      (ex_comp_le (fun d : Z.carrier × X.carrier × Y.carrier => (d.1, d.2.1)) Prod.fst _)

/-- The pairing morphism `⟨f, g⟩`. -/
def Hom.pair {Z X Y : PER P} (f : Hom Z X) (g : Hom Z Y) : Hom Z (prodPER X Y) :=
  Quotient.liftOn₂ f g (fun F G => (Quotient.mk _ (pairFunRel F G) : Hom Z (prodPER X Y)))
    (fun _ _ _ _ hF hG => Quotient.sound
      ⟨match hF.1, hG.1 with | ⟨a⟩, ⟨b⟩ => ⟨conj_mono (subst_mono _ a) (subst_mono _ b)⟩,
       match hF.2, hG.2 with | ⟨a⟩, ⟨b⟩ => ⟨conj_mono (subst_mono _ a) (subst_mono _ b)⟩⟩)

/-- Second projection `X × Y ⟶ Y`: relate `(x, y)` to `y'` iff `x` exists and
`y ~ y'`. -/
def proj2 (X Y : PER P) : FunRel (prodPER X Y) Y where
  rel := conj (subst (fun p : (X.carrier × Y.carrier) × Y.carrier => (p.1.1, p.1.1)) X.rel)
              (subst (fun p => (p.1.2, p.2)) Y.rel)
  strict_dom := by
    simp only [prodPER, subst_conj, ← subst_comp]
    exact conj_mono (le_refl _)
      (Y.refl_left_at (K := (X.carrier × Y.carrier) × Y.carrier) (fun p => p.1.2) (fun p => p.2))
  strict_cod := by
    refine le_trans (conj_le_right _ _) ?_
    exact Y.refl_right_at (K := (X.carrier × Y.carrier) × Y.carrier) (fun p => p.1.2) (fun p => p.2)
  cong := by
    simp only [prodPER, subst_conj, ← subst_comp]
    refine le_conj ?_ ?_
    · -- E_X(p'x) from ρ_X(px, p'x)
      refine le_trans (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
        (conj_le_left _ _)) ?_
      exact X.refl_right_at
        (K := (X.carrier × Y.carrier) × (X.carrier × Y.carrier) × Y.carrier × Y.carrier)
        (fun t => t.1.1) (fun t => t.2.1.1)
    · -- ρ_Y(p'y, y'') from ρ_Y(py,y'), ρ_Y(py,p'y), ρ_Y(y',y'')
      refine le_trans (le_conj (le_trans (le_conj (le_trans ?_
          (Y.symm_at (K := (X.carrier × Y.carrier) × (X.carrier × Y.carrier) × Y.carrier × Y.carrier)
            (fun t => t.1.2) (fun t => t.2.1.2))) ?_)
          (Y.trans_at (K := (X.carrier × Y.carrier) × (X.carrier × Y.carrier) × Y.carrier × Y.carrier)
            (fun t => t.2.1.2) (fun t => t.1.2) (fun t => t.2.2.1))) ?_)
        (Y.trans_at (K := (X.carrier × Y.carrier) × (X.carrier × Y.carrier) × Y.carrier × Y.carrier)
          (fun t => t.2.1.2) (fun t => t.2.2.1) (fun t => t.2.2.2))
      · exact le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _)) (conj_le_right _ _)
      · exact le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) (conj_le_right _ _)
      · exact conj_le_right _ _
  single := by
    simp only [subst_conj, ← subst_comp]
    exact le_trans (le_conj
      (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
        (Y.symm_at (K := (X.carrier × Y.carrier) × Y.carrier × Y.carrier)
          (fun s => s.1.2) (fun s => s.2.1)))
      (le_trans (conj_le_right _ _) (conj_le_right _ _)))
      (Y.trans_at (K := (X.carrier × Y.carrier) × Y.carrier × Y.carrier)
        (fun s => s.2.1) (fun s => s.1.2) (fun s => s.2.2))
  total := by
    have h := subst_mono (fun q : X.carrier × Y.carrier => (q, q.2))
      (ex_unit (Prod.fst : (X.carrier × Y.carrier) × Y.carrier → X.carrier × Y.carrier)
        (conj (subst (fun p : (X.carrier × Y.carrier) × Y.carrier => (p.1.1, p.1.1)) X.rel)
              (subst (fun p => (p.1.2, p.2)) Y.rel)))
    simp only [← subst_comp] at h
    refine le_trans ?_ (le_trans h (subst_id_le _))
    simp only [prodPER, subst_conj, ← subst_comp]
    exact le_refl _

/-- First projection as a morphism. -/
def Hom.fst (X Y : PER P) : Hom (prodPER X Y) X := Quotient.mk _ (proj1 X Y)

/-- Second projection as a morphism. -/
def Hom.snd (X Y : PER P) : Hom (prodPER X Y) Y := Quotient.mk _ (proj2 X Y)

/-- **Functional relations are determined by containment**: if `F ⊆ F'` then they
are equal as morphisms.  (Totality of `F` plus single-valuedness of `F'` force
the reverse inclusion.)  This is the workhorse for universal properties. -/
def funrel_eq_of_le {A B : PER P} (F F' : FunRel A B) (h : F.rel ⊢ F'.rel) :
    F'.rel ⊢ F.rel := by
  have hFex : F'.rel ⊢ ex (fun d : A.carrier × B.carrier × B.carrier => (d.1, d.2.2))
      (subst (fun d : A.carrier × B.carrier × B.carrier => (d.1, d.2.1)) F.rel) := by
    refine le_trans F'.strict_dom ?_
    have hF := subst_mono (Prod.fst : A.carrier × B.carrier → A.carrier) F.total
    rw [← subst_comp] at hF
    refine le_trans hF ?_
    refine subst_ex_elim (Prod.fst : A.carrier × B.carrier → A.carrier)
      (Prod.fst : A.carrier × B.carrier → A.carrier) ?_
    have hu := subst_mono
      (fun s : { p : (A.carrier × B.carrier) × (A.carrier × B.carrier) //
          Prod.fst p.1 = Prod.fst p.2 } => (s.1.1.1, s.1.2.2, s.1.1.2))
      (ex_unit (fun d : A.carrier × B.carrier × B.carrier => (d.1, d.2.2))
        (subst (fun d : A.carrier × B.carrier × B.carrier => (d.1, d.2.1)) F.rel))
    rw [← subst_comp, ← subst_comp] at hu
    refine le_trans ?_ hu
    rw [show (fun s : { p : (A.carrier × B.carrier) × (A.carrier × B.carrier) //
            Prod.fst p.1 = Prod.fst p.2 } => s.1.2)
          = ((fun d : A.carrier × B.carrier × B.carrier => (d.1, d.2.1)) ∘
              fun s => (s.1.1.1, s.1.2.2, s.1.1.2)) from by
        funext s
        show s.1.2 = (s.1.1.1, s.1.2.2)
        rw [s.2]]
    exact le_refl _
  refine le_trans (le_trans (le_conj (le_refl _) hFex)
    (frobenius (fun d : A.carrier × B.carrier × B.carrier => (d.1, d.2.2)) _ F'.rel))
    (ex_adj_mpr ?_)
  have hh := subst_mono (fun d : A.carrier × B.carrier × B.carrier => (d.1, d.2.1)) h
  have hsingle := subst_mono
    (fun d : A.carrier × B.carrier × B.carrier => (d.1, d.2.1, d.2.2)) F'.single
  have hcong := subst_mono
    (fun d : A.carrier × B.carrier × B.carrier => (d.1, d.1, d.2.1, d.2.2)) F.cong
  have hsd := subst_mono (fun d : A.carrier × B.carrier × B.carrier => (d.1, d.2.1)) F.strict_dom
  simp only [subst_conj, ← subst_comp] at hh hsingle hcong hsd
  exact le_trans (le_conj (le_conj (conj_le_right _ _) (le_trans (conj_le_right _ _) hsd))
    (le_trans (le_conj (le_trans (conj_le_right _ _) hh) (conj_le_left _ _)) hsingle)) hcong

/-- Universal property: `π₁ ∘ ⟨f, g⟩ = f`. -/
theorem Hom.fst_comp_pair {Z X Y : PER P} (f : Hom Z X) (g : Hom Z Y) :
    Hom.comp (Hom.fst X Y) (Hom.pair f g) = f := by
  induction f using Quotient.inductionOn with | _ F =>
  induction g using Quotient.inductionOn with | _ G =>
  have hfwd : compRel (pairFunRel F G) (proj1 X Y) ⊢ F.rel := by
    refine ex_adj_mpr ?_
    simp only [pairFunRel, proj1, subst_conj, ← subst_comp]
    have hcong := subst_mono (fun d : Z.carrier × (X.carrier × Y.carrier) × X.carrier =>
      (d.1, d.1, d.2.1.1, d.2.2)) F.cong
    have hsd := subst_mono (fun d : Z.carrier × (X.carrier × Y.carrier) × X.carrier =>
      (d.1, d.2.1.1)) F.strict_dom
    simp only [subst_conj, ← subst_comp] at hcong hsd
    refine le_trans (le_conj (le_conj ?_ ?_) ?_) hcong
    · exact le_trans (conj_le_left _ _) (conj_le_left _ _)
    · exact le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) hsd
    · exact le_trans (conj_le_right _ _) (conj_le_left _ _)
  exact Quotient.sound
    ⟨⟨hfwd⟩, ⟨funrel_eq_of_le (compFunRel (pairFunRel F G) (proj1 X Y)) F hfwd⟩⟩

/-- Universal property: `π₂ ∘ ⟨f, g⟩ = g`. -/
theorem Hom.snd_comp_pair {Z X Y : PER P} (f : Hom Z X) (g : Hom Z Y) :
    Hom.comp (Hom.snd X Y) (Hom.pair f g) = g := by
  induction f using Quotient.inductionOn with | _ F =>
  induction g using Quotient.inductionOn with | _ G =>
  have hfwd : compRel (pairFunRel F G) (proj2 X Y) ⊢ G.rel := by
    refine ex_adj_mpr ?_
    simp only [pairFunRel, proj2, subst_conj, ← subst_comp]
    have hcong := subst_mono (fun d : Z.carrier × (X.carrier × Y.carrier) × Y.carrier =>
      (d.1, d.1, d.2.1.2, d.2.2)) G.cong
    have hsd := subst_mono (fun d : Z.carrier × (X.carrier × Y.carrier) × Y.carrier =>
      (d.1, d.2.1.2)) G.strict_dom
    simp only [subst_conj, ← subst_comp] at hcong hsd
    refine le_trans (le_conj (le_conj ?_ ?_) ?_) hcong
    · exact le_trans (conj_le_left _ _) (conj_le_right _ _)
    · exact le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _)) hsd
    · exact le_trans (conj_le_right _ _) (conj_le_right _ _)
  exact Quotient.sound
    ⟨⟨hfwd⟩, ⟨funrel_eq_of_le (compFunRel (pairFunRel F G) (proj2 X Y)) G hfwd⟩⟩

/-- Uniqueness (η): every map into a product is the pairing of its projections. -/
theorem Hom.pair_fst_snd {Z X Y : PER P} (h : Hom Z (prodPER X Y)) :
    Hom.pair (Hom.comp (Hom.fst X Y) h) (Hom.comp (Hom.snd X Y) h) = h := by
  induction h using Quotient.inductionOn with | _ H =>
  have fwd : H.rel ⊢
      (pairFunRel (compFunRel H (proj1 X Y)) (compFunRel H (proj2 X Y))).rel := by
    show H.rel ⊢ conj
      (subst (fun p : Z.carrier × (X.carrier × Y.carrier) => (p.1, p.2.1)) (compRel H (proj1 X Y)))
      (subst (fun p => (p.1, p.2.2)) (compRel H (proj2 X Y)))
    refine le_conj ?_ ?_
    · have hu := subst_mono (fun p : Z.carrier × (X.carrier × Y.carrier) => (p.1, p.2, p.2.1))
        (ex_unit (fun d : Z.carrier × (X.carrier × Y.carrier) × X.carrier => (d.1, d.2.2))
          (conj (subst (fun d : Z.carrier × (X.carrier × Y.carrier) × X.carrier => (d.1, d.2.1)) H.rel)
                (subst (fun d => (d.2.1, d.2.2)) (proj1 X Y).rel)))
      rw [← subst_comp] at hu
      refine le_trans ?_ hu
      rw [subst_conj, ← subst_comp, ← subst_comp]
      refine le_conj (subst_id_ge _) ?_
      show H.rel ⊢ subst (fun p : Z.carrier × (X.carrier × Y.carrier) => (p.2, p.2.1))
        (conj (subst (fun q : (X.carrier × Y.carrier) × X.carrier => (q.1.1, q.2)) X.rel)
              (subst (fun q : (X.carrier × Y.carrier) × X.carrier => (q.1.2, q.1.2)) Y.rel))
      have hsc := H.strict_cod
      simp only [prodPER, subst_conj, ← subst_comp] at hsc
      simp only [subst_conj, ← subst_comp]
      exact hsc
    · have hu := subst_mono (fun p : Z.carrier × (X.carrier × Y.carrier) => (p.1, p.2, p.2.2))
        (ex_unit (fun d : Z.carrier × (X.carrier × Y.carrier) × Y.carrier => (d.1, d.2.2))
          (conj (subst (fun d : Z.carrier × (X.carrier × Y.carrier) × Y.carrier => (d.1, d.2.1)) H.rel)
                (subst (fun d => (d.2.1, d.2.2)) (proj2 X Y).rel)))
      rw [← subst_comp] at hu
      refine le_trans ?_ hu
      rw [subst_conj, ← subst_comp, ← subst_comp]
      refine le_conj (subst_id_ge _) ?_
      show H.rel ⊢ subst (fun p : Z.carrier × (X.carrier × Y.carrier) => (p.2, p.2.2))
        (conj (subst (fun q : (X.carrier × Y.carrier) × Y.carrier => (q.1.1, q.1.1)) X.rel)
              (subst (fun q : (X.carrier × Y.carrier) × Y.carrier => (q.1.2, q.2)) Y.rel))
      have hsc := H.strict_cod
      simp only [prodPER, subst_conj, ← subst_comp] at hsc
      simp only [subst_conj, ← subst_comp]
      exact hsc
  exact Quotient.sound
    ⟨⟨funrel_eq_of_le H (pairFunRel (compFunRel H (proj1 X Y)) (compFunRel H (proj2 X Y))) fwd⟩,
     ⟨fwd⟩⟩

/-! ### Subobject classifier (object) -/

/-- The subobject classifier `Ω`: the tripos's object of truth values `Prop'`,
with equality given by *realizable bi-implication* `S ↔ T`.  Every "proposition"
exists (its extent `S ↔ S` is realized by the identity). -/
def omega : PER P where
  carrier := Prop' P
  rel := conj (impl (subst Prod.fst generic) (subst Prod.snd generic))
              (impl (subst Prod.snd generic) (subst Prod.fst generic))
  symm := by
    simp only [subst_conj, subst_impl, ← subst_comp]
    exact conj_comm _ _
  trans := by
    simp only [subst_conj, subst_impl, ← subst_comp]
    refine le_conj ?_ ?_
    · exact le_trans (le_conj (le_trans (conj_le_left _ _) (conj_le_left _ _))
        (le_trans (conj_le_right _ _) (conj_le_left _ _))) (impl_trans _ _ _)
    · exact le_trans (le_conj (le_trans (conj_le_right _ _) (conj_le_right _ _))
        (le_trans (conj_le_left _ _) (conj_le_right _ _))) (impl_trans _ _ _)

/-! ### Subobject classifier (truth map) -/

/-- The truth map `⊤ : 𝟙 → Ω` relates the point to a proposition `S` iff `S` holds
(its relation is the generic predicate at the codomain coordinate). -/
def truthFunRel : FunRel (terminal : PER P) (omega : PER P) where
  rel := subst (fun p => p.2) (@Tripos.generic P _)
  strict_dom := by
    show _ ⊢ subst (fun p : PUnit × Prop' P => (p.1, p.1)) (top : P (PUnit × PUnit))
    rw [subst_top]; exact le_top _
  strict_cod := by
    simp only [omega, subst_conj, subst_impl, ← subst_comp]
    exact le_conj (curry (conj_le_left _ _)) (curry (conj_le_left _ _))
  single := by
    simp only [omega, subst_conj, subst_impl, ← subst_comp]
    exact le_conj
      (curry (le_trans (conj_le_left _ _) (conj_le_right _ _)))
      (curry (le_trans (conj_le_left _ _) (conj_le_left _ _)))
  cong := by
    simp only [omega, subst_conj, subst_impl, ← subst_comp]
    exact le_trans
      (le_conj (le_refl _) (le_trans (conj_le_left _ _) (conj_le_left _ _)))
      (uncurry (le_trans (conj_le_right _ _) (conj_le_left _ _)))
  total := by
    have hu := subst_mono
      (fun x : PUnit => (x, @Tripos.char P _ PUnit (top : P PUnit) x))
      (ex_unit (Prod.fst : PUnit × @Tripos.Prop' P _ → PUnit)
        (subst (fun p => p.2) (@Tripos.generic P _)))
    simp only [← subst_comp] at hu
    refine le_trans ?_ (le_trans hu (subst_id_le _))
    rw [show (Prod.snd ∘ fun x : PUnit => (x, @Tripos.char P _ PUnit (top : P PUnit) x))
          = @Tripos.char P _ PUnit (top : P PUnit) from rfl, subst_char]
    exact le_top _

/-- The truth morphism `⊤ : 𝟙 → Ω`. -/
def Hom.truth : Hom (terminal : PER P) (omega : PER P) := Quotient.mk _ truthFunRel

/-! ### Subobjects and the characteristic morphism -/

/-- A **subobject** of `X`: a predicate that is *strict* (`φ(x) ⊢ x` exists) and
*`ρ_X`-closed* (`φ(x) ∧ x ~ x' ⊢ φ(x')`).  These are exactly the monos into `X`. -/
structure StrictPred (X : PER P) where
  /-- The defining predicate. -/
  pred : P X.carrier
  /-- Strictness: members exist. -/
  strict : pred ⊢ subst (fun x : X.carrier => (x, x)) X.rel
  /-- Closure under `ρ_X`. -/
  closed : conj (subst (Prod.fst : X.carrier × X.carrier → X.carrier) pred) X.rel
    ⊢ subst (Prod.snd : X.carrier × X.carrier → X.carrier) pred

/-- The relation of the characteristic morphism `χ_φ : X → Ω`: relate `x` to the
proposition `S` iff `x` exists and `S ↔ φ(x)`. -/
def charRel (φ : StrictPred X) : P (X.carrier × Prop' P) :=
  conj (subst (fun p : X.carrier × Prop' P => (p.1, p.1)) X.rel)
       (conj (impl (subst Prod.fst φ.pred) (subst Prod.snd (@Tripos.generic P _)))
             (impl (subst Prod.snd (@Tripos.generic P _)) (subst Prod.fst φ.pred)))

/-- `χ_φ` is strict in the domain (its members exist). -/
def charRel_strict_dom (φ : StrictPred X) :
    charRel φ ⊢ subst (fun p : X.carrier × Prop' P => (p.1, p.1)) X.rel :=
  conj_le_left _ _

/-- `χ_φ` is strict in the codomain (lands in `Ω`). -/
def charRel_strict_cod (φ : StrictPred X) :
    charRel φ ⊢ subst (fun p : X.carrier × Prop' P => (p.2, p.2)) (omega : PER P).rel := by
  simp only [charRel, omega, subst_conj, subst_impl, ← subst_comp]
  exact le_conj
    (le_trans (le_conj (le_trans (conj_le_right _ _) (conj_le_right _ _))
      (le_trans (conj_le_right _ _) (conj_le_left _ _))) (impl_trans _ _ _))
    (le_trans (le_conj (le_trans (conj_le_right _ _) (conj_le_right _ _))
      (le_trans (conj_le_right _ _) (conj_le_left _ _))) (impl_trans _ _ _))

/-- `χ_φ` is single-valued. -/
def charRel_single (φ : StrictPred X) :
    conj (subst (fun t : X.carrier × Prop' P × Prop' P => (t.1, t.2.1)) (charRel φ))
         (subst (fun t => (t.1, t.2.2)) (charRel φ))
      ⊢ subst (fun t : X.carrier × Prop' P × Prop' P => (t.2.1, t.2.2)) (omega : PER P).rel := by
  simp only [charRel, omega, subst_conj, subst_impl, ← subst_comp]
  exact le_conj
    (le_trans (le_conj
      (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _)) (conj_le_right _ _))
      (le_trans (le_trans (conj_le_right _ _) (conj_le_right _ _)) (conj_le_left _ _)))
      (impl_trans _ _ _))
    (le_trans (le_conj
      (le_trans (le_trans (conj_le_right _ _) (conj_le_right _ _)) (conj_le_right _ _))
      (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _)) (conj_le_left _ _)))
      (impl_trans _ _ _))

/-- `χ_φ` is total: every existing `x` is sent somewhere (namely to `φ(x)`). -/
def charRel_total (φ : StrictPred X) :
    subst (fun x : X.carrier => (x, x)) X.rel
      ⊢ ex (Prod.fst : X.carrier × Prop' P → X.carrier) (charRel φ) := by
  have hu := subst_mono (fun x : X.carrier => (x, @Tripos.char P _ X.carrier φ.pred x))
    (ex_unit (Prod.fst : X.carrier × Prop' P → X.carrier) (charRel φ))
  simp only [← subst_comp] at hu
  refine le_trans ?_ (le_trans hu (subst_id_le _))
  simp only [charRel, subst_conj, subst_impl, ← subst_comp]
  refine le_conj (le_refl _) ?_
  rw [show (Prod.fst ∘ fun x : X.carrier => (x, @Tripos.char P _ X.carrier φ.pred x)) = id from rfl,
    show (Prod.snd ∘ fun x : X.carrier => (x, @Tripos.char P _ X.carrier φ.pred x))
      = @Tripos.char P _ X.carrier φ.pred from rfl, subst_id, subst_char]
  exact le_trans (le_top _) (le_conj (id_impl _) (id_impl _))

/-- `χ_φ` is relational (extensional): respects `ρ_X` and `↔`. -/
def charRel_cong (φ : StrictPred X) :
    conj (conj (subst (fun t : X.carrier × X.carrier × Prop' P × Prop' P => (t.1, t.2.2.1)) (charRel φ))
               (subst (fun t => (t.1, t.2.1)) X.rel))
         (subst (fun t => (t.2.2.1, t.2.2.2)) (omega : PER P).rel)
      ⊢ subst (fun t : X.carrier × X.carrier × Prop' P × Prop' P => (t.2.1, t.2.2.2)) (charRel φ) := by
  simp only [charRel, omega, subst_conj, subst_impl, ← subst_comp]
  have hclosed1 := subst_mono
    (fun t : X.carrier × X.carrier × Prop' P × Prop' P => (t.1, t.2.1)) φ.closed
  have hclosed2 := subst_mono
    (fun t : X.carrier × X.carrier × Prop' P × Prop' P => (t.2.1, t.1)) φ.closed
  simp only [subst_conj, ← subst_comp] at hclosed1 hclosed2
  refine le_conj ?_ (le_conj ?_ ?_)
  · -- E_X(x')
    exact le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
      (X.refl_right_at (K := X.carrier × X.carrier × Prop' P × Prop' P)
        (fun t => t.1) (fun t => t.2.1))
  · -- impl φx' Sa' : φx' → φx → Sa → Sa'
    exact le_trans (le_conj
      (le_trans (le_conj
        (curry (le_trans (le_conj (conj_le_right _ _)
          (le_trans (conj_le_left _ _) (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
            (X.symm_at (K := X.carrier × X.carrier × Prop' P × Prop' P)
              (fun t => t.1) (fun t => t.2.1))))) hclosed2))
        (le_trans (le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) (conj_le_right _ _))
          (conj_le_left _ _)))
        (impl_trans _ _ _))
      (le_trans (conj_le_right _ _) (conj_le_left _ _)))
      (impl_trans _ _ _)
  · -- impl Sa' φx' : Sa' → Sa → φx → φx'
    exact le_trans (le_conj
      (le_trans (le_conj
        (le_trans (conj_le_right _ _) (conj_le_right _ _))
        (le_trans (le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) (conj_le_right _ _))
          (conj_le_right _ _)))
        (impl_trans _ _ _))
      (curry (le_trans (le_conj (conj_le_right _ _)
        (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (conj_le_right _ _)))) hclosed1)))
      (impl_trans _ _ _)

/-- The characteristic morphism `χ_φ : X → Ω` of a subobject `φ`. -/
def charFunRel (φ : StrictPred X) : FunRel X (omega : PER P) where
  rel := charRel φ
  strict_dom := charRel_strict_dom φ
  strict_cod := charRel_strict_cod φ
  cong := charRel_cong φ
  single := charRel_single φ
  total := charRel_total φ

/-- The characteristic morphism as a `Hom`. -/
def Hom.char (φ : StrictPred X) : Hom X (omega : PER P) := Quotient.mk _ (charFunRel φ)

/-- The predicate recovered from a morphism `χ : X → Ω`: `x` is a member iff
`χ(x)` is a true proposition.  (This is the pullback of `⊤` along `χ`.) -/
def predOfFunRel (χ : FunRel X (omega : PER P)) : P X.carrier :=
  ex (Prod.fst : X.carrier × Prop' P → X.carrier)
     (conj χ.rel (subst (fun p : X.carrier × Prop' P => p.2) (@Tripos.generic P _)))

/-- Classification (one round-trip), `⊢`: recovering a subobject from its own
characteristic map gives back the subobject. -/
def predOfFunRel_char_le (φ : StrictPred X) : predOfFunRel (charFunRel φ) ⊢ φ.pred := by
  refine ex_adj_mpr ?_
  simp only [charFunRel, charRel, subst_conj, subst_impl, ← subst_comp]
  exact le_trans (le_conj
    (le_trans (conj_le_left _ _) (le_trans (conj_le_right _ _) (conj_le_right _ _)))
    (conj_le_right _ _)) (impl_mp _ _)

/-- Classification (one round-trip), `⊇`. -/
def predOfFunRel_char_ge (φ : StrictPred X) : φ.pred ⊢ predOfFunRel (charFunRel φ) := by
  have hu := subst_mono (fun x : X.carrier => (x, @Tripos.char P _ X.carrier φ.pred x))
    (ex_unit (Prod.fst : X.carrier × Prop' P → X.carrier)
      (conj (charFunRel φ).rel (subst (fun p : X.carrier × Prop' P => p.2) (@Tripos.generic P _))))
  simp only [← subst_comp] at hu
  refine le_trans ?_ (le_trans hu (subst_id_le _))
  simp only [charFunRel, charRel, subst_conj, subst_impl, ← subst_comp]
  rw [show (Prod.fst ∘ fun x : X.carrier => (x, @Tripos.char P _ X.carrier φ.pred x)) = id from rfl,
    show (Prod.snd ∘ fun x : X.carrier => (x, @Tripos.char P _ X.carrier φ.pred x))
      = @Tripos.char P _ X.carrier φ.pred from rfl, subst_id, subst_char]
  exact le_conj (le_conj φ.strict (le_trans (le_top _) (le_conj (id_impl _) (id_impl _))))
    (le_refl _)

/-- The recovered predicate is strict: its members exist. -/
def predOfFunRel_strict (χ : FunRel X (omega : PER P)) :
    predOfFunRel χ ⊢ subst (fun x : X.carrier => (x, x)) X.rel := by
  refine ex_adj_mpr ?_
  rw [← subst_comp]
  exact le_trans (conj_le_left _ _) χ.strict_dom

/-- The recovered predicate is `ρ_X`-closed. -/
def predOfFunRel_closed (χ : FunRel X (omega : PER P)) :
    conj (subst (Prod.fst : X.carrier × X.carrier → X.carrier) (predOfFunRel χ)) X.rel
      ⊢ subst (Prod.snd : X.carrier × X.carrier → X.carrier) (predOfFunRel χ) := by
  refine le_trans (conj_mono
    (beck_chevalley (Prod.fst : X.carrier × Prop' P → X.carrier)
      (Prod.fst : X.carrier × X.carrier → X.carrier)
      (conj χ.rel (subst (fun p : X.carrier × Prop' P => p.2) (@Tripos.generic P _))))
    (le_refl _)) (conj_ex_elim _ ?_)
  have hu := subst_mono
    (fun s : { p : (X.carrier × X.carrier) × (X.carrier × Prop' P) // Prod.fst p.1 = Prod.fst p.2 } =>
      (s.1.1.2, s.1.2.2))
    (ex_unit (Prod.fst : X.carrier × Prop' P → X.carrier)
      (conj χ.rel (subst (fun p : X.carrier × Prop' P => p.2) (@Tripos.generic P _))))
  rw [← subst_comp] at hu
  rw [← subst_comp]
  refine le_trans ?_ hu
  have hcong := subst_mono
    (fun s : { p : (X.carrier × X.carrier) × (X.carrier × Prop' P) // Prod.fst p.1 = Prod.fst p.2 } =>
      (s.1.2.1, s.1.1.2, s.1.2.2, s.1.2.2)) χ.cong
  have hcod := subst_mono
    (fun s : { p : (X.carrier × X.carrier) × (X.carrier × Prop' P) // Prod.fst p.1 = Prod.fst p.2 } =>
      s.1.2) χ.strict_cod
  simp only [omega, subst_conj, subst_impl, ← subst_comp] at hcong hcod ⊢
  refine le_conj ?_ (le_trans (conj_le_right _ _) (conj_le_right _ _))
  refine le_trans (le_conj (le_conj ?_ ?_) ?_) hcong
  · exact le_trans (conj_le_right _ _) (conj_le_left _ _)
  · refine le_trans (conj_le_left _ _) (subst_congr ?_ X.rel)
    funext s
    exact Prod.ext_iff.mpr ⟨s.2, rfl⟩
  · exact le_trans (le_trans (conj_le_right _ _) (conj_le_left _ _)) hcod

/-- A morphism `X → Ω` recovers a subobject of `X` (pullback of `⊤`). -/
def subobjOfFunRel (χ : FunRel X (omega : PER P)) : StrictPred X where
  pred := predOfFunRel χ
  strict := predOfFunRel_strict χ
  closed := predOfFunRel_closed χ

/-- Classification (other round-trip): the characteristic map of the subobject
recovered from `χ` is `χ` itself.  With `χ_φ` classifying `φ`, this gives the full
bijection `Hom X Ω ≅ Sub(X)`. -/
theorem Hom.char_subobjOfFunRel (χ : FunRel X (omega : PER P)) :
    Hom.char (subobjOfFunRel χ) = Quotient.mk _ χ := by
  have hbwd : χ.rel ⊢ (charFunRel (subobjOfFunRel χ)).rel := by
    show χ.rel ⊢ charRel (subobjOfFunRel χ)
    refine le_conj χ.strict_dom (le_conj ?_ ?_)
    · -- impl (φ_χ) S, via χ.single
      refine curry ?_
      refine le_trans (conj_comm _ _) (le_trans (conj_mono
        (beck_chevalley (Prod.fst : X.carrier × Prop' P → X.carrier)
          (Prod.fst : X.carrier × Prop' P → X.carrier)
          (conj χ.rel (subst (fun p : X.carrier × Prop' P => p.2) (@Tripos.generic P _))))
        (le_refl _)) (conj_ex_elim _ ?_))
      erw [← subst_comp]
      have hsingle := subst_mono
        (fun s : { p : (X.carrier × Prop' P) × (X.carrier × Prop' P) //
            Prod.fst p.1 = Prod.fst p.2 } => (s.1.1.1, s.1.1.2, s.1.2.2)) χ.single
      simp only [omega, subst_conj, subst_impl, ← subst_comp, Function.comp_def] at hsingle
      simp only [subst_conj, ← subst_comp, Function.comp_def]
      refine le_trans (le_conj (le_trans (le_trans (le_conj (conj_le_left _ _) ?_) hsingle)
        (conj_le_right _ _)) (le_trans (conj_le_right _ _) (conj_le_right _ _))) (impl_mp _ _)
      refine le_trans (le_trans (conj_le_right _ _) (conj_le_left _ _)) (subst_congr ?_ χ.rel)
      funext s
      exact Prod.ext_iff.mpr ⟨s.2.symm, rfl⟩
    · -- impl S (φ_χ), the unit of the existential
      exact curry (ex_unit (Prod.fst : X.carrier × Prop' P → X.carrier)
        (conj χ.rel (subst (fun p : X.carrier × Prop' P => p.2) (@Tripos.generic P _))))
  exact Quotient.sound
    ⟨⟨funrel_eq_of_le χ (charFunRel (subobjOfFunRel χ)) hbwd⟩, ⟨hbwd⟩⟩

/-! ### Images of morphisms as subobjects

The image of `m : S ⟶ X` is the predicate `∃s. m(s, x)` on `X`.  For a *mono* `m`
this is the subobject through which `m` factors as an iso, so its characteristic
map classifies `m`. -/

/-- The image of a functional relation `M : S ⟶ X`, as a strict predicate on `X`. -/
def imageStrictPred {S X : PER P} (M : FunRel S X) : StrictPred X where
  pred := ex (Prod.snd : S.carrier × X.carrier → X.carrier) M.rel
  strict := by
    refine ex_adj_mpr ?_
    rw [← subst_comp]
    exact M.strict_cod
  closed := by
    refine le_trans (conj_mono
      (beck_chevalley (Prod.snd : S.carrier × X.carrier → X.carrier)
        (Prod.fst : X.carrier × X.carrier → X.carrier) M.rel) (le_refl _)) (conj_ex_elim _ ?_)
    have hu := subst_mono
      (fun s : { p : (X.carrier × X.carrier) × (S.carrier × X.carrier) //
          Prod.fst p.1 = Prod.snd p.2 } => (s.1.2.1, s.1.1.2))
      (ex_unit (Prod.snd : S.carrier × X.carrier → X.carrier) M.rel)
    rw [← subst_comp] at hu
    rw [← subst_comp]
    refine le_trans ?_ hu
    have hcong := subst_mono
      (fun s : { p : (X.carrier × X.carrier) × (S.carrier × X.carrier) //
          Prod.fst p.1 = Prod.snd p.2 } => (s.1.2.1, s.1.2.1, s.1.1.1, s.1.1.2)) M.cong
    have hdom := subst_mono
      (fun s : { p : (X.carrier × X.carrier) × (S.carrier × X.carrier) //
          Prod.fst p.1 = Prod.snd p.2 } => s.1.2) M.strict_dom
    simp only [subst_conj, ← subst_comp] at hcong hdom ⊢
    refine le_trans (le_conj (le_conj ?_ ?_) ?_) hcong
    · -- `M(s, x)` from the existential witness (rewriting `x_wit = x` via the constraint)
      refine le_trans (conj_le_right _ _) (subst_congr ?_ M.rel)
      funext s
      exact Prod.ext_iff.mpr ⟨rfl, s.2.symm⟩
    · -- `ρ_S(s, s)` from `M.strict_dom`
      exact le_trans (conj_le_right _ _) hdom
    · -- `ρ_X(x, x')` from the carried `X.rel`
      exact conj_le_left _ _

/-- `charRel` is monotone up to mutual entailment of the predicates. -/
def charRel_mono {X : PER P} {φ ψ : StrictPred X}
    (hle : φ.pred ⊢ ψ.pred) (hge : ψ.pred ⊢ φ.pred) : charRel φ ⊢ charRel ψ := by
  refine conj_mono (le_refl _) (conj_mono ?_ ?_)
  · exact curry (le_trans (conj_mono (le_refl _) (subst_mono _ hge)) (impl_mp _ _))
  · exact curry (le_trans (impl_mp _ _) (subst_mono _ hle))

/-- The characteristic morphism depends only on the predicate up to entailment. -/
theorem Hom.char_congr {X : PER P} {φ ψ : StrictPred X}
    (hle : φ.pred ⊢ ψ.pred) (hge : ψ.pred ⊢ φ.pred) : Hom.char φ = Hom.char ψ :=
  Quotient.sound ⟨⟨charRel_mono hle hge⟩, ⟨charRel_mono hge hle⟩⟩

/-- The characteristic morphism of (the image of) a morphism `m : S ⟶ X`. -/
def Hom.charMono {S X : PER P} (m : Hom S X) : Hom X (omega : PER P) := by
  refine Quotient.liftOn m (fun M => Hom.char (imageStrictPred M)) ?_
  rintro M M' ⟨⟨e⟩, ⟨e'⟩⟩
  exact Hom.char_congr (ex_mono _ e) (ex_mono _ e')

/-- `Hom.charMono` on a representative is the characteristic map of its image. -/
theorem Hom.charMono_mk {S X : PER P} (M : FunRel S X) :
    Hom.charMono (Quotient.mk _ M) = Hom.char (imageStrictPred M) := rfl

/-- Existential introduction via a section: if `g ∘ w = id`, then `ψ` reindexed
along `w` entails `∃_g ψ`.  Packages the `subst`-composition bookkeeping. -/
def ex_intro_section {I J : Type u} (g : I → J) (w : J → I) (hw : g ∘ w = id) (ψ : P I) :
    subst w ψ ⊢ ex g ψ := by
  have h := subst_mono w (ex_unit g ψ)
  rw [← subst_comp, hw, subst_id] at h
  exact h

/-- The composite `truth ∘ ! : S ⟶ Ω` is the "constant true" relation `E_S(s) ∧ prop`. -/
def comp_terminal_truth_ge {S : PER P} :
    conj (subst (fun p : S.carrier × Prop' P => (p.1, p.1)) S.rel)
         (subst (fun p : S.carrier × Prop' P => p.2) (@Tripos.generic P _))
      ⊢ compRel (terminalFunRel S) truthFunRel := by
  refine le_trans ?_ (ex_intro_section (fun e : S.carrier × PUnit × Prop' P => (e.1, e.2.2))
    (fun p : S.carrier × Prop' P => (p.1, (PUnit.unit, p.2))) (by funext p; rfl)
    (conj (subst (fun e : S.carrier × PUnit × Prop' P => (e.1, e.2.1)) (terminalFunRel S).rel)
          (subst (fun e : S.carrier × PUnit × Prop' P => (e.2.1, e.2.2)) truthFunRel.rel)))
  rw [subst_conj]
  refine le_conj ?_ ?_
  · refine le_trans (conj_le_left _ _) ?_
    simp only [terminalFunRel]; erw [← subst_comp, ← subst_comp]; exact le_refl _
  · refine le_trans (conj_le_right _ _) ?_
    simp only [truthFunRel]; erw [← subst_comp, ← subst_comp]; exact le_refl _

/-- Reverse: `truth ∘ !` entails the "constant true" conjunction.  Used to extract the
factoring from the pullback cone. -/
def comp_terminal_truth_le {S : PER P} :
    compRel (terminalFunRel S) truthFunRel
      ⊢ conj (subst (fun p : S.carrier × Prop' P => (p.1, p.1)) S.rel)
             (subst (fun p : S.carrier × Prop' P => p.2) (@Tripos.generic P _)) := by
  refine ex_adj_mpr ?_
  rw [subst_conj]
  refine le_conj ?_ ?_
  · refine le_trans (conj_le_left _ _) ?_
    simp only [terminalFunRel]; erw [← subst_comp, ← subst_comp]; exact le_refl _
  · refine le_trans (conj_le_right _ _) ?_
    simp only [truthFunRel]; erw [← subst_comp, ← subst_comp]; exact le_refl _

/-- `char(im M) ∘ M` factors through `truth ∘ !`. -/
def charMono_to_conj {S X : PER P} (M : FunRel S X) :
    compRel M (charFunRel (imageStrictPred M))
      ⊢ conj (subst (fun p : S.carrier × Prop' P => (p.1, p.1)) S.rel)
             (subst (fun p : S.carrier × Prop' P => p.2) (@Tripos.generic P _)) := by
  refine ex_adj_mpr ?_
  rw [subst_conj]
  refine le_conj ?_ ?_
  · -- E_S(s) from M.strict_dom
    refine le_trans (conj_le_left _ _) ?_
    have := subst_mono (fun d : S.carrier × X.carrier × Prop' P => (d.1, d.2.1)) M.strict_dom
    erw [← subst_comp] at this ⊢
    exact this
  · -- prop from `im M(x) → prop` applied to `im M(x)` (witnessed by `s`)
    have him : conj (subst (fun d : S.carrier × X.carrier × Prop' P => (d.1, d.2.1)) M.rel)
        (subst (fun d : S.carrier × X.carrier × Prop' P => (d.2.1, d.2.2))
          (charFunRel (imageStrictPred M)).rel)
        ⊢ subst (fun d : S.carrier × X.carrier × Prop' P => d.2.1)
            (ex (Prod.snd : S.carrier × X.carrier → X.carrier) M.rel) := by
      refine le_trans (conj_le_left _ _) ?_
      have := subst_mono (fun d : S.carrier × X.carrier × Prop' P => (d.1, d.2.1))
        (ex_unit (Prod.snd : S.carrier × X.carrier → X.carrier) M.rel)
      erw [← subst_comp] at this
      exact this
    refine le_trans (le_conj ?_ him) (impl_mp _ _)
    refine le_trans (conj_le_right _ _) ?_
    show subst (fun d : S.carrier × X.carrier × Prop' P => (d.2.1, d.2.2))
      (charRel (imageStrictPred M)) ⊢ _
    simp only [charRel, imageStrictPred, subst_conj, subst_impl, ← subst_comp]
    exact le_trans (conj_le_right _ _) (conj_le_left _ _)

/-- Commutativity of the classifying square (relation level). -/
def charMono_comm_le {S X : PER P} (M : FunRel S X) :
    compRel M (charFunRel (imageStrictPred M)) ⊢ compRel (terminalFunRel S) truthFunRel :=
  le_trans (charMono_to_conj M) comp_terminal_truth_ge

/-- Commutativity of the classifying square: `char(im m) ∘ m = truth ∘ !`. -/
theorem charMono_comm {S X : PER P} (m : Hom S X) :
    Hom.comp (Hom.charMono m) m = Hom.comp Hom.truth (terminalHom S) := by
  induction m using Quotient.inductionOn with
  | _ M =>
    refine Quotient.sound ⟨⟨charMono_comm_le M⟩,
      ⟨funrel_eq_of_le (compFunRel M (charFunRel (imageStrictPred M)))
        (compFunRel (terminalFunRel S) truthFunRel) (charMono_comm_le M)⟩⟩

/-- Re-encode the image predicate `∃s. M(s,x)` reindexed into `W × X` as the
`uRel`-total `∃`-form.  A Beck–Chevalley shuffle (mirrors `imageStrictPred.closed`). -/
def imgPred_bridge {W X S : PER P} (M : FunRel S X) :
    subst (Prod.snd : W.carrier × X.carrier → X.carrier)
        (ex (Prod.snd : S.carrier × X.carrier → X.carrier) M.rel)
      ⊢ ex (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.1))
          (subst (fun d : W.carrier × X.carrier × S.carrier => (d.2.2, d.2.1)) M.rel) := by
  refine le_trans (beck_chevalley (Prod.snd : S.carrier × X.carrier → X.carrier)
    (Prod.snd : W.carrier × X.carrier → X.carrier) M.rel) (ex_adj_mpr ?_)
  have hu := subst_mono
    (fun s : { p : (W.carrier × X.carrier) × (S.carrier × X.carrier) //
        Prod.snd p.1 = Prod.snd p.2 } => (s.1.1.1, s.1.1.2, s.1.2.1))
    (ex_unit (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.1))
      (subst (fun d : W.carrier × X.carrier × S.carrier => (d.2.2, d.2.1)) M.rel))
  simp only [← subst_comp] at hu
  refine le_trans (subst_congr ?_ M.rel) hu
  funext s
  exact Prod.ext_iff.mpr ⟨rfl, s.2.symm⟩

/-- **The factoring**: from the pullback cone `char(im M) ∘ a = truth ∘ !` (forward
entailment `hcone`), `a` factors through the image of `M`.  Reindex the cone at the
truth value `char(im M)(x)` (whose "holds" is `im M(x)` by comprehension); the
`∃`-introduction uses `x' = x` with a reflexive biimplication. -/
def cone_to_hfac {W X S : PER P} (A : FunRel W X) (M : FunRel S X)
    (hcone : compRel A (charFunRel (imageStrictPred M))
      ⊢ compRel (terminalFunRel W) truthFunRel) :
    A.rel ⊢ ex (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.1))
      (subst (fun d : W.carrier × X.carrier × S.carrier => (d.2.2, d.2.1)) M.rel) := by
  -- comprehension: "char(im M)(x) holds" ⊣⊢ im M(x)
  have heq : subst (fun p : W.carrier × X.carrier =>
        @Tripos.char P _ X.carrier (imageStrictPred M).pred p.2) (@Tripos.generic P _)
      = subst (fun p : W.carrier × X.carrier => p.2) (imageStrictPred M).pred := by
    rw [show (fun p : W.carrier × X.carrier =>
        @Tripos.char P _ X.carrier (imageStrictPred M).pred p.2)
        = (@Tripos.char P _ X.carrier (imageStrictPred M).pred) ∘ (fun p => p.2) from rfl,
      subst_comp, subst_char]
  -- sublemma A: `A.rel ⊢ ν*(char(im M) ∘ a)`, ∃-intro at `x' = x`.
  have subA : A.rel ⊢ subst (fun p : W.carrier × X.carrier =>
        (p.1, @Tripos.char P _ X.carrier (imageStrictPred M).pred p.2))
      (compRel A (charFunRel (imageStrictPred M))) := by
    have hu := subst_mono
      (fun p : W.carrier × X.carrier =>
        (p.1, p.2, @Tripos.char P _ X.carrier (imageStrictPred M).pred p.2))
      (ex_unit (fun e : W.carrier × X.carrier × Prop' P => (e.1, e.2.2))
        (conj (subst (fun e : W.carrier × X.carrier × Prop' P => (e.1, e.2.1)) A.rel)
              (subst (fun e : W.carrier × X.carrier × Prop' P => (e.2.1, e.2.2))
                (charFunRel (imageStrictPred M)).rel)))
    simp only [subst_conj, ← subst_comp] at hu
    refine le_trans ?_ hu
    refine le_conj (subst_id_ge A.rel) ?_
    show A.rel ⊢ subst (fun p : W.carrier × X.carrier =>
      (p.2, @Tripos.char P _ X.carrier (imageStrictPred M).pred p.2)) (charRel (imageStrictPred M))
    simp only [charRel, subst_conj, subst_impl, ← subst_comp, Function.comp_def, heq]
    exact le_conj A.strict_cod
      (le_conj (le_trans (le_top _) (id_impl _)) (le_trans (le_top _) (id_impl _)))
  -- sublemma B: extract `im M(x)` from `ν*(truth ∘ !)`.
  have subB : subst (fun p : W.carrier × X.carrier =>
        (p.1, @Tripos.char P _ X.carrier (imageStrictPred M).pred p.2))
      (compRel (terminalFunRel W) truthFunRel)
      ⊢ ex (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.1))
          (subst (fun d : W.carrier × X.carrier × S.carrier => (d.2.2, d.2.1)) M.rel) := by
    have key : subst (fun p : W.carrier × X.carrier =>
          (p.1, @Tripos.char P _ X.carrier (imageStrictPred M).pred p.2))
        (subst (fun p : W.carrier × Prop' P => p.2) (@Tripos.generic P _))
        = subst (fun p : W.carrier × X.carrier => p.2) (imageStrictPred M).pred := by
      erw [← subst_comp]; exact heq
    refine le_trans (subst_mono _ (le_trans comp_terminal_truth_le (conj_le_right _ _))) ?_
    erw [key]
    exact imgPred_bridge M
  exact le_trans subA (le_trans (subst_mono _ hcone) subB)

/-- The **comprehension object** `{x | φ(x)}` of a subobject `φ`, as a PER: `x ~ x'`
iff `φ(x)` and `x ~_X x'`.  Used (with its inclusion) as the canonical pullback cone in
`char_unique`. -/
def subPER {X : PER P} (φ : StrictPred X) : PER P where
  carrier := X.carrier
  rel := conj (subst (Prod.fst : X.carrier × X.carrier → X.carrier) φ.pred) X.rel
  symm := by
    simp only [subst_conj, ← subst_comp, Function.comp_def]
    exact le_conj φ.closed (le_trans (conj_le_right _ _) X.symm)
  trans := by
    simp only [subst_conj, ← subst_comp, Function.comp_def]
    refine le_conj (le_trans (conj_le_left _ _) (conj_le_left _ _)) ?_
    exact le_trans (le_conj (le_trans (conj_le_left _ _) (conj_le_right _ _))
        (le_trans (conj_le_right _ _) (conj_le_right _ _)))
      (X.trans_at (K := X.carrier × X.carrier × X.carrier)
        (fun t => t.1) (fun t => t.2.1) (fun t => t.2.2))

/-- The inclusion `{x | φ(x)} ↪ X`. -/
def subIncl {X : PER P} (φ : StrictPred X) : FunRel (subPER φ) X where
  rel := conj (subst (Prod.fst : X.carrier × X.carrier → X.carrier) φ.pred) X.rel
  strict_dom := by
    simp only [subPER, subst_conj, ← subst_comp, Function.comp_def]
    exact le_conj (conj_le_left _ _)
      (le_trans (conj_le_right _ _) (idFunRel X).strict_dom)
  strict_cod := le_trans (conj_le_right _ _) (idFunRel X).strict_cod
  cong := by
    have hclosed := subst_mono
      (fun t : X.carrier × X.carrier × X.carrier × X.carrier => (t.1, t.2.1)) φ.closed
    simp only [subst_conj, ← subst_comp, Function.comp_def] at hclosed
    simp only [subPER, subst_conj, ← subst_comp, Function.comp_def]
    refine le_conj ?_ ?_
    · exact le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _)) hclosed
    · exact le_trans (le_conj
        (le_trans (le_conj
          (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
            (le_trans (conj_le_right _ _) (X.symm_at
              (K := X.carrier × X.carrier × X.carrier × X.carrier) (fun t => t.1) (fun t => t.2.1))))
          (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (conj_le_right _ _))))
          (X.trans_at (K := X.carrier × X.carrier × X.carrier × X.carrier)
            (fun t => t.2.1) (fun t => t.1) (fun t => t.2.2.1)))
        (conj_le_right _ _))
        (X.trans_at (K := X.carrier × X.carrier × X.carrier × X.carrier)
          (fun t => t.2.1) (fun t => t.2.2.1) (fun t => t.2.2.2))
  single := by
    simp only [subst_conj, ← subst_comp, Function.comp_def]
    exact le_trans (le_conj
      (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
        (X.symm_at (K := X.carrier × X.carrier × X.carrier) (fun t => t.1) (fun t => t.2.1)))
      (le_trans (conj_le_right _ _) (conj_le_right _ _)))
      (X.trans_at (K := X.carrier × X.carrier × X.carrier)
        (fun t => t.2.1) (fun t => t.1) (fun t => t.2.2))
  total := by
    refine le_trans ?_ (ex_intro_section (Prod.fst : X.carrier × X.carrier → X.carrier)
      (fun x => (x, x)) (by funext x; rfl) _)
    exact le_refl _

/-- The inclusion `subIncl φ` is relationally injective. -/
def subIncl_inj {X : PER P} (φ : StrictPred X) :
    conj (subst (fun p : X.carrier × X.carrier × X.carrier => (p.1, p.2.2)) (subIncl φ).rel)
         (subst (fun p : X.carrier × X.carrier × X.carrier => (p.2.1, p.2.2)) (subIncl φ).rel)
      ⊢ subst (fun p : X.carrier × X.carrier × X.carrier => (p.1, p.2.1)) (subPER φ).rel := by
  simp only [subIncl, subPER, subst_conj, ← subst_comp, Function.comp_def]
  refine le_conj (le_trans (conj_le_left _ _) (conj_le_left _ _)) ?_
  exact le_trans (le_conj
    (le_trans (conj_le_left _ _) (conj_le_right _ _))
    (le_trans (le_trans (conj_le_right _ _) (conj_le_right _ _))
      (X.symm_at (K := X.carrier × X.carrier × X.carrier) (fun p => p.2.1) (fun p => p.2.2))))
    (X.trans_at (K := X.carrier × X.carrier × X.carrier)
      (fun p => p.1) (fun p => p.2.2) (fun p => p.2.1))

/-- The characteristic map of the inclusion of `{χ}` is `χ` itself. -/
theorem charMono_subIncl {X : PER P} (C : FunRel X (omega : PER P)) :
    Hom.charMono (Quotient.mk _ (subIncl (subobjOfFunRel C))) = Quotient.mk _ C := by
  rw [Hom.charMono_mk, ← Hom.char_subobjOfFunRel C]
  refine Hom.char_congr ?_ ?_
  · refine ex_adj_mpr ?_
    exact (subobjOfFunRel C).closed
  · refine le_trans ?_ (ex_intro_section (Prod.snd : X.carrier × X.carrier → X.carrier)
      (fun x => (x, x)) (by funext x; rfl) (subIncl (subobjOfFunRel C)).rel)
    simp only [subIncl]
    erw [subst_conj]
    refine le_conj ?_ (subobjOfFunRel C).strict
    erw [← subst_comp]
    exact subst_id_ge _

/-- `∃s. M(s,x)` reindexed into `X × Prop'`, as an explicit `∃`-form (for eliminating
the `∃s` in `char_unique`'s `comm`-half).  Beck–Chevalley shuffle. -/
def imgM_exX {S X : PER P} (M : FunRel S X) :
    subst (Prod.fst : X.carrier × Prop' P → X.carrier)
        (ex (Prod.snd : S.carrier × X.carrier → X.carrier) M.rel)
      ⊢ ex (fun t : (X.carrier × Prop' P) × S.carrier => t.1)
          (subst (fun t : (X.carrier × Prop' P) × S.carrier => (t.2, t.1.1)) M.rel) := by
  refine le_trans (beck_chevalley (Prod.snd : S.carrier × X.carrier → X.carrier)
    (Prod.fst : X.carrier × Prop' P → X.carrier) M.rel) (ex_adj_mpr ?_)
  have hu := subst_mono
    (fun s : { p : (X.carrier × Prop' P) × (S.carrier × X.carrier) //
        Prod.fst p.1 = Prod.snd p.2 } => (s.1.1, s.1.2.1))
    (ex_unit (fun t : (X.carrier × Prop' P) × S.carrier => t.1)
      (subst (fun t : (X.carrier × Prop' P) × S.carrier => (t.2, t.1.1)) M.rel))
  simp only [← subst_comp] at hu
  refine le_trans (subst_congr ?_ M.rel) hu
  funext s
  exact Prod.ext_iff.mpr ⟨rfl, s.2.symm⟩

/-- `char_unique`, the `comm` half: if `x ∈ im M` and `χ(x) = T`, then `T` holds.
(`χ` here is the FunRel `C`.)  Uses the cone's `comm` realizer `hcomm`. -/
def charUnique_half1 {S X : PER P} (M : FunRel S X) (C : FunRel X (omega : PER P))
    (hcomm : compRel M C ⊢ compRel (terminalFunRel S) truthFunRel) :
    conj C.rel (subst (Prod.fst : X.carrier × Prop' P → X.carrier) (imageStrictPred M).pred)
      ⊢ subst (Prod.snd : X.carrier × Prop' P → Prop' P) (@Tripos.generic P _) := by
  refine le_trans (conj_mono (le_refl _) (imgM_exX M)) ?_
  refine le_trans (frobenius (fun t : (X.carrier × Prop' P) × S.carrier => t.1)
    (subst (fun t : (X.carrier × Prop' P) × S.carrier => (t.2, t.1.1)) M.rel) C.rel) ?_
  refine ex_adj_mpr ?_
  have hgoal : conj (subst (fun t : (X.carrier × Prop' P) × S.carrier => t.1) C.rel)
      (subst (fun t : (X.carrier × Prop' P) × S.carrier => (t.2, t.1.1)) M.rel)
      ⊢ subst (fun t : (X.carrier × Prop' P) × S.carrier => (t.2, t.1.2)) (compRel M C) := by
    have hu := subst_mono (fun t : (X.carrier × Prop' P) × S.carrier => (t.2, t.1.1, t.1.2))
      (ex_unit (fun d : S.carrier × X.carrier × Prop' P => (d.1, d.2.2))
        (conj (subst (fun d : S.carrier × X.carrier × Prop' P => (d.1, d.2.1)) M.rel)
              (subst (fun d : S.carrier × X.carrier × Prop' P => (d.2.1, d.2.2)) C.rel)))
    simp only [subst_conj, ← subst_comp] at hu
    exact le_trans (le_conj (conj_le_right _ _) (conj_le_left _ _)) hu
  refine le_trans hgoal (le_trans (subst_mono _
    (le_trans hcomm (le_trans comp_terminal_truth_le (conj_le_right _ _)))) ?_)
  erw [← subst_comp, ← subst_comp]
  exact le_refl _

/-- A composite `U ; M` factors through the image of `M` (drop the lift `U`). -/
def compRel_to_img {W S X : PER P} (U : FunRel W S) (M : FunRel S X) :
    compRel U M ⊢ subst (Prod.snd : W.carrier × X.carrier → X.carrier) (imageStrictPred M).pred := by
  refine ex_adj_mpr ?_
  refine le_trans (conj_le_right _ _) ?_
  have h := subst_mono (fun d : W.carrier × S.carrier × X.carrier => (d.2.1, d.2.2))
    (ex_unit (Prod.snd : S.carrier × X.carrier → X.carrier) M.rel)
  erw [← subst_comp] at h
  erw [← subst_comp]
  exact h

/-- `char φ` restricted to the comprehension object `{x | φ(x)}` is the true map
(relation level).  The "truth" part is `impl_mp` of `charRel`'s biimplication with
`φ(x)` (recovered from `φ.closed`). -/
def charSubIncl_comm_le {X : PER P} (φ : StrictPred X) :
    compRel (subIncl φ) (charFunRel φ)
      ⊢ compRel (terminalFunRel (subPER φ)) truthFunRel := by
  refine ex_adj_mpr ?_
  have hclosed := subst_mono (fun d : X.carrier × X.carrier × Prop' P => (d.1, d.2.1)) φ.closed
  simp only [subst_conj, ← subst_comp, Function.comp_def] at hclosed
  refine le_trans ?_ (subst_mono (fun d : X.carrier × X.carrier × Prop' P => (d.1, d.2.2))
    (comp_terminal_truth_ge (S := subPER φ)))
  simp only [subIncl, charFunRel, charRel, subPER, omega, subst_conj, subst_impl, ← subst_comp,
    Function.comp_def]
  refine le_conj (le_conj ?_ ?_) ?_
  · exact le_trans (conj_le_left _ _) (conj_le_left _ _)
  · exact le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
      (X.refl_left_at (K := X.carrier × X.carrier × Prop' P) (fun d => d.1) (fun d => d.2.1))
  · exact le_trans (le_conj
      (le_trans (conj_le_right _ _) (le_trans (conj_le_right _ _) (conj_le_left _ _)))
      (le_trans (conj_le_left _ _) hclosed))
      (impl_mp _ _)

/-- The cone condition as a morphism equation. -/
def charSubIncl_comm {X : PER P} (φ : StrictPred X) :
    Hom.comp (Hom.char φ) (Quotient.mk _ (subIncl φ))
      = Hom.comp Hom.truth (terminalHom (subPER φ)) :=
  Quotient.sound ⟨⟨charSubIncl_comm_le φ⟩,
    ⟨funrel_eq_of_le (compFunRel (subIncl φ) (charFunRel φ))
      (compFunRel (terminalFunRel (subPER φ)) truthFunRel) (charSubIncl_comm_le φ)⟩⟩

/-! ### The pullback lift

For the classifying square to be a pullback we must, given `a : W ⟶ X` factoring
through the image of `m`, produce the unique lift `u : W ⟶ S` with `m ∘ u = a`.
The lift relates `w` to `s` iff `a(w) = m(s)`. -/

/-- The pullback lift relation: `u(w, s) := ∃x. a(w, x) ∧ m(s, x)`. -/
def uRel {W X S : PER P} (a : FunRel W X) (m : FunRel S X) : P (W.carrier × S.carrier) :=
  ex (fun t : W.carrier × X.carrier × S.carrier => (t.1, t.2.2))
     (conj (subst (fun t : W.carrier × X.carrier × S.carrier => (t.1, t.2.1)) a.rel)
           (subst (fun t : W.carrier × X.carrier × S.carrier => (t.2.2, t.2.1)) m.rel))

/-- The lift is strict in the domain (from `a`). -/
def uRel_strict_dom {W X S : PER P} (a : FunRel W X) (m : FunRel S X) :
    uRel a m ⊢ subst (fun p : W.carrier × S.carrier => (p.1, p.1)) W.rel := by
  refine ex_adj_mpr (le_trans (conj_le_left _ _) ?_)
  rw [← subst_comp]
  have h := subst_mono (fun t : W.carrier × X.carrier × S.carrier => (t.1, t.2.1)) a.strict_dom
  rw [← subst_comp] at h
  exact h

/-- The lift is strict in the codomain (from `m`). -/
def uRel_strict_cod {W X S : PER P} (a : FunRel W X) (m : FunRel S X) :
    uRel a m ⊢ subst (fun p : W.carrier × S.carrier => (p.2, p.2)) S.rel := by
  refine ex_adj_mpr (le_trans (conj_le_right _ _) ?_)
  rw [← subst_comp]
  have h := subst_mono (fun t : W.carrier × X.carrier × S.carrier => (t.2.2, t.2.1)) m.strict_dom
  rw [← subst_comp] at h
  exact h

/-- The lift is relational (from `a` and `m`). -/
def uRel_cong {W X S : PER P} (a : FunRel W X) (m : FunRel S X) :
    conj (conj (subst (fun t : W.carrier × W.carrier × S.carrier × S.carrier =>
                  (t.1, t.2.2.1)) (uRel a m))
               (subst (fun t => (t.1, t.2.1)) W.rel))
         (subst (fun t => (t.2.2.1, t.2.2.2)) S.rel)
      ⊢ subst (fun t : W.carrier × W.carrier × S.carrier × S.carrier =>
          (t.2.1, t.2.2.2)) (uRel a m) := by
  refine le_trans (conj_assoc_left _ _ _) ?_
  refine le_trans (conj_mono
    (subst_ex_mid (fun t : W.carrier × W.carrier × S.carrier × S.carrier => (t.1, t.2.2.1))
      (conj (subst (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.1)) a.rel)
            (subst (fun d : W.carrier × X.carrier × S.carrier => (d.2.2, d.2.1)) m.rel)))
    (le_refl _)) ?_
  refine conj_ex_elim Prod.fst ?_
  rw [← subst_comp]
  refine le_trans ?_
    (by
      have h := subst_mono
        (fun p : (W.carrier × W.carrier × S.carrier × S.carrier) × X.carrier =>
          (p.1.2.1, p.2, p.1.2.2.2))
        (ex_unit (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.2))
          (conj (subst (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.1)) a.rel)
                (subst (fun d : W.carrier × X.carrier × S.carrier => (d.2.2, d.2.1)) m.rel)))
      rw [← subst_comp] at h
      exact h)
  have hacong : conj (conj (subst (fun p : (W.carrier × W.carrier × S.carrier × S.carrier) ×
                          X.carrier => (p.1.1, p.2)) a.rel)
                          (subst (fun p => (p.1.1, p.1.2.1)) W.rel))
                     (subst (fun p => (p.2, p.2)) X.rel)
                 ⊢ subst (fun p => (p.1.2.1, p.2)) a.rel := by
    have h := subst_mono (fun p : (W.carrier × W.carrier × S.carrier × S.carrier) × X.carrier =>
      (p.1.1, p.1.2.1, p.2, p.2)) a.cong
    simp only [subst_conj, ← subst_comp] at h
    exact h
  have hacod : subst (fun p : (W.carrier × W.carrier × S.carrier × S.carrier) × X.carrier =>
                  (p.1.1, p.2)) a.rel
                ⊢ subst (fun p => (p.2, p.2)) X.rel := by
    have h := subst_mono (fun p : (W.carrier × W.carrier × S.carrier × S.carrier) × X.carrier =>
      (p.1.1, p.2)) a.strict_cod
    rw [← subst_comp] at h
    exact h
  have hmcong : conj (conj (subst (fun p : (W.carrier × W.carrier × S.carrier × S.carrier) ×
                          X.carrier => (p.1.2.2.1, p.2)) m.rel)
                          (subst (fun p => (p.1.2.2.1, p.1.2.2.2)) S.rel))
                     (subst (fun p => (p.2, p.2)) X.rel)
                 ⊢ subst (fun p => (p.1.2.2.2, p.2)) m.rel := by
    have h := subst_mono (fun p : (W.carrier × W.carrier × S.carrier × S.carrier) × X.carrier =>
      (p.1.2.2.1, p.1.2.2.2, p.2, p.2)) m.cong
    simp only [subst_conj, ← subst_comp] at h
    exact h
  simp only [subst_conj, ← subst_comp]
  refine le_conj ?_ ?_
  · refine le_trans (le_conj (le_conj ?_ ?_) ?_) hacong
    · exact le_trans (conj_le_right _ _) (conj_le_left _ _)
    · exact le_trans (conj_le_left _ _) (conj_le_left _ _)
    · exact le_trans (le_trans (conj_le_right _ _) (conj_le_left _ _)) hacod
  · refine le_trans (le_conj (le_conj ?_ ?_) ?_) hmcong
    · exact le_trans (conj_le_right _ _) (conj_le_right _ _)
    · exact le_trans (conj_le_left _ _) (conj_le_right _ _)
    · exact le_trans (le_trans (conj_le_right _ _) (conj_le_left _ _)) hacod

/-- The lift is total, *given that `a` factors through the image of `m`* (`hfac`,
which the pullback cone condition supplies). -/
def uRel_total {W X S : PER P} (a : FunRel W X) (m : FunRel S X)
    (hfac : a.rel ⊢ ex (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.1))
              (subst (fun d : W.carrier × X.carrier × S.carrier => (d.2.2, d.2.1)) m.rel)) :
    subst (fun w : W.carrier => (w, w)) W.rel
      ⊢ ex (Prod.fst : W.carrier × S.carrier → W.carrier) (uRel a m) := by
  have key1 : a.rel ⊢ ex (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.1))
      (conj (subst (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.1)) a.rel)
            (subst (fun d : W.carrier × X.carrier × S.carrier => (d.2.2, d.2.1)) m.rel)) :=
    le_trans (le_conj (le_refl a.rel) hfac)
      (frobenius (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.1)) _ a.rel)
  refine le_trans (le_trans a.total
    (ex_mono (Prod.fst : W.carrier × X.carrier → W.carrier) key1)) ?_
  refine le_trans
    (ex_comp_le (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.1)) Prod.fst _) ?_
  exact ex_comp_ge (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.2)) Prod.fst _

/-- Single-valuedness of the lift, *given relational injectivity of `m`* (`e`).  Two
witnesses `x, x'` for the two `∃`s agree by `a.single`; transporting `m(s₂,x')` to
`m(s₂,x)` by `m.cong`, injectivity `e` then forces `ρ_S(s₁,s₂)`. -/
def uRel_single {W X S : PER P} (a : FunRel W X) (m : FunRel S X)
    (e : conj (subst (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.2)) m.rel)
              (subst (fun p : S.carrier × S.carrier × X.carrier => (p.2.1, p.2.2)) m.rel)
           ⊢ subst (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.1)) S.rel) :
    conj (subst (fun t : W.carrier × S.carrier × S.carrier => (t.1, t.2.1)) (uRel a m))
         (subst (fun t : W.carrier × S.carrier × S.carrier => (t.1, t.2.2)) (uRel a m))
      ⊢ subst (fun t : W.carrier × S.carrier × S.carrier => (t.2.1, t.2.2)) S.rel := by
  refine le_trans (conj_mono
    (subst_ex_mid (fun t : W.carrier × S.carrier × S.carrier => (t.1, t.2.1))
      (conj (subst (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.1)) a.rel)
            (subst (fun d : W.carrier × X.carrier × S.carrier => (d.2.2, d.2.1)) m.rel)))
    (le_refl _)) ?_
  refine conj_ex_elim Prod.fst ?_
  rw [← subst_comp (Prod.fst : (W.carrier × S.carrier × S.carrier) × X.carrier →
        W.carrier × S.carrier × S.carrier)
      (fun t : W.carrier × S.carrier × S.carrier => (t.1, t.2.2)) (uRel a m)]
  refine le_trans (conj_mono
    (subst_ex_mid ((fun t : W.carrier × S.carrier × S.carrier => (t.1, t.2.2)) ∘
        (Prod.fst : (W.carrier × S.carrier × S.carrier) × X.carrier →
          W.carrier × S.carrier × S.carrier))
      (conj (subst (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.1)) a.rel)
            (subst (fun d : W.carrier × X.carrier × S.carrier => (d.2.2, d.2.1)) m.rel)))
    (le_refl _)) ?_
  refine conj_ex_elim Prod.fst ?_
  have hAs : conj (subst (fun w : ((W.carrier × S.carrier × S.carrier) × X.carrier) × X.carrier =>
                    (w.1.1.1, w.1.2)) a.rel)
                  (subst (fun w => (w.1.1.1, w.2)) a.rel)
              ⊢ subst (fun w => (w.1.2, w.2)) X.rel := by
    have h := subst_mono (fun w : ((W.carrier × S.carrier × S.carrier) × X.carrier) × X.carrier =>
      (w.1.1.1, w.1.2, w.2)) a.single
    simp only [subst_conj, ← subst_comp] at h
    exact h
  have hmdom : subst (fun w : ((W.carrier × S.carrier × S.carrier) × X.carrier) × X.carrier =>
                  (w.1.1.2.2, w.2)) m.rel
                ⊢ subst (fun w => (w.1.1.2.2, w.1.1.2.2)) S.rel := by
    have h := subst_mono (fun w : ((W.carrier × S.carrier × S.carrier) × X.carrier) × X.carrier =>
      (w.1.1.2.2, w.2)) m.strict_dom
    rw [← subst_comp] at h
    exact h
  have hmcong : conj (conj (subst (fun w : ((W.carrier × S.carrier × S.carrier) × X.carrier) ×
                          X.carrier => (w.1.1.2.2, w.2)) m.rel)
                          (subst (fun w => (w.1.1.2.2, w.1.1.2.2)) S.rel))
                     (subst (fun w => (w.2, w.1.2)) X.rel)
                 ⊢ subst (fun w => (w.1.1.2.2, w.1.2)) m.rel := by
    have h := subst_mono (fun w : ((W.carrier × S.carrier × S.carrier) × X.carrier) × X.carrier =>
      (w.1.1.2.2, w.1.1.2.2, w.2, w.1.2)) m.cong
    simp only [subst_conj, ← subst_comp] at h
    exact h
  have he : conj (subst (fun w : ((W.carrier × S.carrier × S.carrier) × X.carrier) × X.carrier =>
                    (w.1.1.2.1, w.1.2)) m.rel)
                 (subst (fun w => (w.1.1.2.2, w.1.2)) m.rel)
              ⊢ subst (fun w => (w.1.1.2.1, w.1.1.2.2)) S.rel := by
    have h := subst_mono (fun w : ((W.carrier × S.carrier × S.carrier) × X.carrier) × X.carrier =>
      (w.1.1.2.1, w.1.1.2.2, w.1.2)) e
    simp only [subst_conj, ← subst_comp] at h
    exact h
  simp only [subst_conj, ← subst_comp]
  refine le_trans (le_conj ?_ ?_) he
  · exact le_trans (conj_le_left _ _) (conj_le_right _ _)
  · refine le_trans (le_conj (le_conj ?_ ?_) ?_) hmcong
    · exact le_trans (conj_le_right _ _) (conj_le_right _ _)
    · exact le_trans (le_trans (conj_le_right _ _) (conj_le_right _ _)) hmdom
    · exact le_trans (le_conj
        (le_trans (conj_le_left _ _) (conj_le_left _ _))
        (le_trans (conj_le_right _ _) (conj_le_left _ _)))
        (le_trans hAs (X.symm_at
          (K := ((W.carrier × S.carrier × S.carrier) × X.carrier) × X.carrier)
          (fun w => w.1.2) (fun w => w.2)))

/-! ### Monos are relationally injective

The kernel pair of `m` carries an explicit common-image coordinate `x` and *both*
elements' `m`-conditions, so its PER laws need no `m.cong`.  Its two projections
become equal after composing with `m`, so `Mono m` forces them equal — which is
exactly relational injectivity of `m`. -/

/-- The kernel-pair test object: triples `(s, s', x)` with `m(s,x) ∧ m(s',x)`. -/
def kerPER {S X : PER P} (m : FunRel S X) : PER P where
  carrier := S.carrier × S.carrier × X.carrier
  rel :=
    conj (conj (conj
        (subst (fun t : (S.carrier × S.carrier × X.carrier) × S.carrier × S.carrier × X.carrier =>
          (t.1.1, t.2.1)) S.rel)
        (subst (fun t => (t.1.2.1, t.2.2.1)) S.rel))
        (subst (fun t => (t.1.2.2, t.2.2.2)) X.rel))
      (conj (conj (subst (fun t => (t.1.1, t.1.2.2)) m.rel)
                  (subst (fun t => (t.1.2.1, t.1.2.2)) m.rel))
            (conj (subst (fun t => (t.2.1, t.2.2.2)) m.rel)
                  (subst (fun t => (t.2.2.1, t.2.2.2)) m.rel)))
  symm := by
    simp only [subst_conj, ← subst_comp, Function.comp_def]
    refine le_conj (le_conj (le_conj ?_ ?_) ?_) (le_conj ?_ ?_)
    · exact le_trans (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (conj_le_left _ _)))
        (S.symm_at (K := (S.carrier × S.carrier × X.carrier) × S.carrier × S.carrier × X.carrier)
          (fun t => t.1.1) (fun t => t.2.1))
    · exact le_trans (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (conj_le_right _ _)))
        (S.symm_at (K := (S.carrier × S.carrier × X.carrier) × S.carrier × S.carrier × X.carrier)
          (fun t => t.1.2.1) (fun t => t.2.2.1))
    · exact le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
        (X.symm_at (K := (S.carrier × S.carrier × X.carrier) × S.carrier × S.carrier × X.carrier)
          (fun t => t.1.2.2) (fun t => t.2.2.2))
    · exact le_trans (conj_le_right _ _) (conj_le_right _ _)
    · exact le_trans (conj_le_right _ _) (conj_le_left _ _)
  trans := by
    simp only [subst_conj, ← subst_comp, Function.comp_def]
    refine le_conj (le_conj (le_conj ?_ ?_) ?_) (le_conj ?_ ?_)
    · exact le_trans (le_conj
        (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _)
          (le_trans (conj_le_left _ _) (conj_le_left _ _))))
        (le_trans (conj_le_right _ _) (le_trans (conj_le_left _ _)
          (le_trans (conj_le_left _ _) (conj_le_left _ _)))))
        (S.trans_at (K := (S.carrier × S.carrier × X.carrier) ×
            (S.carrier × S.carrier × X.carrier) × S.carrier × S.carrier × X.carrier)
          (fun t => t.1.1) (fun t => t.2.1.1) (fun t => t.2.2.1))
    · exact le_trans (le_conj
        (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _)
          (le_trans (conj_le_left _ _) (conj_le_right _ _))))
        (le_trans (conj_le_right _ _) (le_trans (conj_le_left _ _)
          (le_trans (conj_le_left _ _) (conj_le_right _ _)))))
        (S.trans_at (K := (S.carrier × S.carrier × X.carrier) ×
            (S.carrier × S.carrier × X.carrier) × S.carrier × S.carrier × X.carrier)
          (fun t => t.1.2.1) (fun t => t.2.1.2.1) (fun t => t.2.2.2.1))
    · exact le_trans (le_conj
        (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (conj_le_right _ _)))
        (le_trans (conj_le_right _ _) (le_trans (conj_le_left _ _) (conj_le_right _ _))))
        (X.trans_at (K := (S.carrier × S.carrier × X.carrier) ×
            (S.carrier × S.carrier × X.carrier) × S.carrier × S.carrier × X.carrier)
          (fun t => t.1.2.2) (fun t => t.2.1.2.2) (fun t => t.2.2.2.2))
    · exact le_trans (conj_le_left _ _) (le_trans (conj_le_right _ _) (conj_le_left _ _))
    · exact le_trans (conj_le_right _ _) (le_trans (conj_le_right _ _) (conj_le_right _ _))

/-- First component-relation extracted from the kernel-pair relation: `ρ_S` on the
two first `S`-components. -/
def kerRel_rhoS1 {S X : PER P} (m : FunRel S X) :
    (kerPER m).rel ⊢ subst (fun q : (kerPER m).carrier × (kerPER m).carrier =>
      (q.1.1, q.2.1)) S.rel :=
  le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (conj_le_left _ _))

/-- Second component-relation: `ρ_S` on the two second `S`-components. -/
def kerRel_rhoS2 {S X : PER P} (m : FunRel S X) :
    (kerPER m).rel ⊢ subst (fun q : (kerPER m).carrier × (kerPER m).carrier =>
      (q.1.2.1, q.2.2.1)) S.rel :=
  le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (conj_le_right _ _))

/-- First kernel-pair projection `(s, s', x) ↦ s`, as a functional relation
(full-extent: the whole kernel-pair extent `E_ker(t)` together with `ρ_S(t.1, s)`).
The full extent makes `strict_dom` trivial and lets `cong` recover `E_ker(t₂)`
from `ρ_ker(t₁, t₂)` via `refl_right_at` — no `m.cong` needed. -/
def kerProj1 {S X : PER P} (m : FunRel S X) : FunRel (kerPER m) S where
  rel := conj (subst (fun p : (kerPER m).carrier × S.carrier => (p.1, p.1)) (kerPER m).rel)
              (subst (fun p : (kerPER m).carrier × S.carrier => (p.1.1, p.2)) S.rel)
  strict_dom := conj_le_left _ _
  strict_cod := le_trans (conj_le_right _ _)
    (S.refl_right_at (K := (kerPER m).carrier × S.carrier) (fun p => p.1.1) (fun p => p.2))
  single := by
    simp only [subst_conj, ← subst_comp]
    exact le_trans (le_conj
      (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
        (S.symm_at (K := (kerPER m).carrier × S.carrier × S.carrier)
          (fun p => p.1.1) (fun p => p.2.1)))
      (le_trans (conj_le_right _ _) (conj_le_right _ _)))
      (S.trans_at (K := (kerPER m).carrier × S.carrier × S.carrier)
        (fun p => p.2.1) (fun p => p.1.1) (fun p => p.2.2))
  cong := by
    simp only [subst_conj, ← subst_comp]
    have hk1 : subst (fun w : (kerPER m).carrier × (kerPER m).carrier × S.carrier × S.carrier =>
        (w.1, w.2.1)) (kerPER m).rel ⊢ subst (fun w => (w.1.1, w.2.1.1)) S.rel := by
      have h := subst_mono
        (fun w : (kerPER m).carrier × (kerPER m).carrier × S.carrier × S.carrier => (w.1, w.2.1))
        (kerRel_rhoS1 m)
      simp only [← subst_comp] at h
      exact h
    refine le_conj ?_ ?_
    · exact le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
        ((kerPER m).refl_right_at
          (K := (kerPER m).carrier × (kerPER m).carrier × S.carrier × S.carrier)
          (fun w => w.1) (fun w => w.2.1))
    · refine le_trans (le_conj
        (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
          (le_trans hk1 (S.symm_at
            (K := (kerPER m).carrier × (kerPER m).carrier × S.carrier × S.carrier)
            (fun w => w.1.1) (fun w => w.2.1.1))))
        (le_trans (le_conj
          (le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) (conj_le_right _ _))
          (conj_le_right _ _))
          (S.trans_at (K := (kerPER m).carrier × (kerPER m).carrier × S.carrier × S.carrier)
            (fun w => w.1.1) (fun w => w.2.2.1) (fun w => w.2.2.2))))
        (S.trans_at (K := (kerPER m).carrier × (kerPER m).carrier × S.carrier × S.carrier)
          (fun w => w.2.1.1) (fun w => w.1.1) (fun w => w.2.2.2))
  total := by
    refine le_trans ?_ (ex_intro_section
      (Prod.fst : (kerPER m).carrier × S.carrier → (kerPER m).carrier)
      (fun t => (t, t.1)) (by funext t; rfl) _)
    simp only [subst_conj, ← subst_comp]
    refine le_conj (le_refl _) ?_
    have h := subst_mono (fun t : (kerPER m).carrier => (t, t)) (kerRel_rhoS1 m)
    simp only [← subst_comp] at h
    exact h

/-- Second kernel-pair projection `(s, s', x) ↦ s'`. -/
def kerProj2 {S X : PER P} (m : FunRel S X) : FunRel (kerPER m) S where
  rel := conj (subst (fun p : (kerPER m).carrier × S.carrier => (p.1, p.1)) (kerPER m).rel)
              (subst (fun p : (kerPER m).carrier × S.carrier => (p.1.2.1, p.2)) S.rel)
  strict_dom := conj_le_left _ _
  strict_cod := le_trans (conj_le_right _ _)
    (S.refl_right_at (K := (kerPER m).carrier × S.carrier) (fun p => p.1.2.1) (fun p => p.2))
  single := by
    simp only [subst_conj, ← subst_comp]
    exact le_trans (le_conj
      (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
        (S.symm_at (K := (kerPER m).carrier × S.carrier × S.carrier)
          (fun p => p.1.2.1) (fun p => p.2.1)))
      (le_trans (conj_le_right _ _) (conj_le_right _ _)))
      (S.trans_at (K := (kerPER m).carrier × S.carrier × S.carrier)
        (fun p => p.2.1) (fun p => p.1.2.1) (fun p => p.2.2))
  cong := by
    simp only [subst_conj, ← subst_comp]
    have hk2 : subst (fun w : (kerPER m).carrier × (kerPER m).carrier × S.carrier × S.carrier =>
        (w.1, w.2.1)) (kerPER m).rel ⊢ subst (fun w => (w.1.2.1, w.2.1.2.1)) S.rel := by
      have h := subst_mono
        (fun w : (kerPER m).carrier × (kerPER m).carrier × S.carrier × S.carrier => (w.1, w.2.1))
        (kerRel_rhoS2 m)
      simp only [← subst_comp] at h
      exact h
    refine le_conj ?_ ?_
    · exact le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
        ((kerPER m).refl_right_at
          (K := (kerPER m).carrier × (kerPER m).carrier × S.carrier × S.carrier)
          (fun w => w.1) (fun w => w.2.1))
    · refine le_trans (le_conj
        (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
          (le_trans hk2 (S.symm_at
            (K := (kerPER m).carrier × (kerPER m).carrier × S.carrier × S.carrier)
            (fun w => w.1.2.1) (fun w => w.2.1.2.1))))
        (le_trans (le_conj
          (le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) (conj_le_right _ _))
          (conj_le_right _ _))
          (S.trans_at (K := (kerPER m).carrier × (kerPER m).carrier × S.carrier × S.carrier)
            (fun w => w.1.2.1) (fun w => w.2.2.1) (fun w => w.2.2.2))))
        (S.trans_at (K := (kerPER m).carrier × (kerPER m).carrier × S.carrier × S.carrier)
          (fun w => w.2.1.2.1) (fun w => w.1.2.1) (fun w => w.2.2.2))
  total := by
    refine le_trans ?_ (ex_intro_section
      (Prod.fst : (kerPER m).carrier × S.carrier → (kerPER m).carrier)
      (fun t => (t, t.2.1)) (by funext t; rfl) _)
    simp only [subst_conj, ← subst_comp]
    refine le_conj (le_refl _) ?_
    have h := subst_mono (fun t : (kerPER m).carrier => (t, t)) (kerRel_rhoS2 m)
    simp only [← subst_comp] at h
    exact h

/-- First `m`-condition of the kernel-pair relation: `m(t₁.1, t₁.2.2)`. -/
def kerRel_m1 {S X : PER P} (m : FunRel S X) :
    (kerPER m).rel ⊢ subst (fun q : (kerPER m).carrier × (kerPER m).carrier =>
      (q.1.1, q.1.2.2)) m.rel :=
  le_trans (conj_le_right _ _) (le_trans (conj_le_left _ _) (conj_le_left _ _))

/-- Second `m`-condition: `m(t₁.2.1, t₁.2.2)`. -/
def kerRel_m2 {S X : PER P} (m : FunRel S X) :
    (kerPER m).rel ⊢ subst (fun q : (kerPER m).carrier × (kerPER m).carrier =>
      (q.1.2.1, q.1.2.2)) m.rel :=
  le_trans (conj_le_right _ _) (le_trans (conj_le_left _ _) (conj_le_right _ _))

/-- The two kernel-pair projections agree after composing with `m`: `m ∘ π₁ = m ∘ π₂`.
This is the cone condition fed to `Mono m`.  Forward entailment; the reverse is free
by `funrel_eq_of_le`.  The `m(t.2.1, x)` leg uses `m.cong`/`m.single`/`m.cong` on the
common image `t.2.2` that `kerPER.rel` records for both `t.1` and `t.2.1`. -/
def kerProj_comm_le {S X : PER P} (m : FunRel S X) :
    compRel (kerProj1 m) m ⊢ compRel (kerProj2 m) m := by
  refine ex_adj_mpr ?_
  have hintro :
      subst (fun d : (kerPER m).carrier × S.carrier × X.carrier => (d.1, d.1.2.1, d.2.2))
          (conj (subst (fun e : (kerPER m).carrier × S.carrier × X.carrier => (e.1, e.2.1))
                  (kerProj2 m).rel)
                (subst (fun e : (kerPER m).carrier × S.carrier × X.carrier => (e.2.1, e.2.2)) m.rel))
        ⊢ subst (fun d : (kerPER m).carrier × S.carrier × X.carrier => (d.1, d.2.2))
            (compRel (kerProj2 m) m) := by
    have hu := subst_mono
      (fun d : (kerPER m).carrier × S.carrier × X.carrier => (d.1, d.1.2.1, d.2.2))
      (ex_unit (fun e : (kerPER m).carrier × S.carrier × X.carrier => (e.1, e.2.2))
        (conj (subst (fun e : (kerPER m).carrier × S.carrier × X.carrier => (e.1, e.2.1))
                (kerProj2 m).rel)
              (subst (fun e : (kerPER m).carrier × S.carrier × X.carrier => (e.2.1, e.2.2)) m.rel)))
    simp only [← subst_comp, Function.comp_def] at hu
    exact hu
  refine le_trans ?_ hintro
  have hmcong1 := subst_mono (fun d : (kerPER m).carrier × S.carrier × X.carrier =>
    (d.2.1, d.1.1, d.2.2, d.2.2)) m.cong
  simp only [subst_conj, ← subst_comp] at hmcong1
  have hmsingle := subst_mono (fun d : (kerPER m).carrier × S.carrier × X.carrier =>
    (d.1.1, d.2.2, d.1.2.2)) m.single
  simp only [subst_conj, ← subst_comp] at hmsingle
  have hmcong2 := subst_mono (fun d : (kerPER m).carrier × S.carrier × X.carrier =>
    (d.1.2.1, d.1.2.1, d.1.2.2, d.2.2)) m.cong
  simp only [subst_conj, ← subst_comp] at hmcong2
  simp only [kerProj1, kerProj2, subst_conj, ← subst_comp]
  refine le_conj (le_conj ?Eker ?r2121) ?mtx
  · exact le_trans (conj_le_left _ _) (conj_le_left _ _)
  · refine le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) ?_
    have h := subst_mono (fun d : (kerPER m).carrier × S.carrier × X.carrier => (d.1, d.1))
      (kerRel_rhoS2 m)
    simp only [← subst_comp, Function.comp_def] at h
    exact h
  · refine le_trans (le_conj (le_conj ?m2122 ?r2121b) ?x22x) hmcong2
    · refine le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) ?_
      have h := subst_mono (fun d : (kerPER m).carrier × S.carrier × X.carrier => (d.1, d.1))
        (kerRel_m2 m)
      simp only [← subst_comp, Function.comp_def] at h
      exact h
    · refine le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) ?_
      have h := subst_mono (fun d : (kerPER m).carrier × S.carrier × X.carrier => (d.1, d.1))
        (kerRel_rhoS2 m)
      simp only [← subst_comp, Function.comp_def] at h
      exact h
    · refine le_trans ?xx22 (X.symm_at
        (K := (kerPER m).carrier × S.carrier × X.carrier) (fun d => d.2.2) (fun d => d.1.2.2))
      refine le_trans (le_conj ?mt1x ?mt1t22) hmsingle
      · refine le_trans (le_conj (le_conj ?msx ?rst1) ?rxx) hmcong1
        · exact conj_le_right _ _
        · exact le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
            (S.symm_at (K := (kerPER m).carrier × S.carrier × X.carrier)
              (fun d => d.1.1) (fun d => d.2.1))
        · refine le_trans (conj_le_right _ _) ?_
          have h := subst_mono (fun d : (kerPER m).carrier × S.carrier × X.carrier => (d.2.1, d.2.2))
            m.strict_cod
          simp only [← subst_comp, Function.comp_def] at h
          exact h
      · refine le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) ?_
        have h := subst_mono (fun d : (kerPER m).carrier × S.carrier × X.carrier => (d.1, d.1))
          (kerRel_m1 m)
        simp only [← subst_comp, Function.comp_def] at h
        exact h

/-- `m ∘ π₁ = m ∘ π₂` as a morphism equation (the kernel-pair cone). -/
def kerProj_comm {S X : PER P} (m : FunRel S X) :
    Hom.comp (Quotient.mk _ m) (Quotient.mk _ (kerProj1 m))
      = Hom.comp (Quotient.mk _ m) (Quotient.mk _ (kerProj2 m)) :=
  Quotient.sound ⟨⟨kerProj_comm_le m⟩, ⟨funrel_eq_of_le _ _ (kerProj_comm_le m)⟩⟩

/-- Relational injectivity from equality of the kernel-pair projections.  This is a
*constructive* function of the realizer `e : kerProj1.rel ⊢ kerProj2.rel`; the
`Mono`-derived version wraps it in `Nonempty` (see `mono_injective`). -/
def kerProj_to_inj {S X : PER P} (m : FunRel S X)
    (e : (kerProj1 m).rel ⊢ (kerProj2 m).rel) :
    conj (subst (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.2)) m.rel)
         (subst (fun p : S.carrier × S.carrier × X.carrier => (p.2.1, p.2.2)) m.rel)
      ⊢ subst (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.1)) S.rel := by
  -- `hker : E_ker(t) ⊢ ρ_S(t.2.1, t.1)`, instantiating `e` at `s := t.1`.
  have hker : subst (fun t : (kerPER m).carrier => (t, t)) (kerPER m).rel
      ⊢ subst (fun t : (kerPER m).carrier => (t.2.1, t.1)) S.rel := by
    have he := subst_mono (fun t : (kerPER m).carrier => (t, t.1)) e
    simp only [kerProj1, kerProj2, subst_conj, ← subst_comp] at he
    refine le_trans ?_ (le_trans he (conj_le_right _ _))
    refine le_conj (le_refl _) ?_
    have h := subst_mono (fun t : (kerPER m).carrier => (t, t)) (kerRel_rhoS1 m)
    simp only [← subst_comp, Function.comp_def] at h
    exact h
  -- Apply `hker` to the kernel-pair element `(s, s', x)` built from `m(s,x) ∧ m(s',x)`.
  have happly : subst (fun p : S.carrier × S.carrier × X.carrier =>
        (((p.1, p.2.1, p.2.2) : (kerPER m).carrier), ((p.1, p.2.1, p.2.2) : (kerPER m).carrier)))
        (kerPER m).rel
      ⊢ subst (fun p : S.carrier × S.carrier × X.carrier => (p.2.1, p.1)) S.rel := by
    have h := subst_mono
      (fun p : S.carrier × S.carrier × X.carrier => ((p.1, p.2.1, p.2.2) : (kerPER m).carrier)) hker
    erw [← subst_comp, ← subst_comp] at h
    exact h
  refine le_trans ?build (le_trans happly
    (S.symm_at (K := S.carrier × S.carrier × X.carrier) (fun p => p.2.1) (fun p => p.1)))
  simp only [kerPER, subst_conj, ← subst_comp]
  refine le_conj (le_conj (le_conj ?ss ?s's') ?xx)
    (le_conj (le_conj ?m1 ?m2) (le_conj ?m1' ?m2'))
  · refine le_trans (conj_le_left _ _) ?_
    have h := subst_mono (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.2)) m.strict_dom
    simp only [← subst_comp, Function.comp_def] at h
    exact h
  · refine le_trans (conj_le_right _ _) ?_
    have h := subst_mono (fun p : S.carrier × S.carrier × X.carrier => (p.2.1, p.2.2)) m.strict_dom
    simp only [← subst_comp, Function.comp_def] at h
    exact h
  · refine le_trans (conj_le_left _ _) ?_
    have h := subst_mono (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.2)) m.strict_cod
    simp only [← subst_comp, Function.comp_def] at h
    exact h
  · exact conj_le_left _ _
  · exact conj_le_right _ _
  · exact conj_le_left _ _
  · exact conj_le_right _ _

/-- A categorical mono is relationally injective — wrapped in `Nonempty`, since the
realizer comes from `Quotient.exact` on `Mono`'s `Prop`-valued equality.  Usable in any
`Prop` goal (e.g. the classifier's `∃`-universal-property) via `Nonempty`-elimination. -/
@[reducible] def mono_injective {S X : PER P} (m : FunRel S X)
    (hmono : ∀ {Z : PER P} (g h : Hom Z S),
      Hom.comp (Quotient.mk _ m) g = Hom.comp (Quotient.mk _ m) h → g = h) :
    Nonempty (conj (subst (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.2)) m.rel)
                   (subst (fun p : S.carrier × S.carrier × X.carrier => (p.2.1, p.2.2)) m.rel)
                ⊢ subst (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.1)) S.rel) :=
  match (Quotient.exact (hmono (Quotient.mk _ (kerProj1 m)) (Quotient.mk _ (kerProj2 m))
      (kerProj_comm m))).1 with
  | ⟨e⟩ => ⟨kerProj_to_inj m e⟩

/-- Relational core of "injective ⇒ mono": if `m` is relationally injective, then
`G ; m ⊢ H ; m` forces `G ⊢ H`. -/
def monoKey {Z S X : PER P} (m : FunRel S X) (G H : FunRel Z S)
    (inj : conj (subst (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.2)) m.rel)
                (subst (fun p : S.carrier × S.carrier × X.carrier => (p.2.1, p.2.2)) m.rel)
             ⊢ subst (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.1)) S.rel)
    (hfwd : compRel G m ⊢ compRel H m) :
    G.rel ⊢ H.rel := by
  have hmtot : G.rel ⊢ ex (fun t : Z.carrier × S.carrier × X.carrier => (t.1, t.2.1))
      (subst (fun t : Z.carrier × S.carrier × X.carrier => (t.2.1, t.2.2)) m.rel) := by
    refine le_trans G.strict_cod ?_
    have hm := subst_mono (Prod.snd : Z.carrier × S.carrier → S.carrier) m.total
    rw [← subst_comp] at hm
    refine le_trans hm ?_
    refine subst_ex_elim (Prod.fst : S.carrier × X.carrier → S.carrier)
      (Prod.snd : Z.carrier × S.carrier → S.carrier) ?_
    have hu := subst_mono
      (fun s : { p : (Z.carrier × S.carrier) × (S.carrier × X.carrier) //
          Prod.snd p.1 = Prod.fst p.2 } => (s.1.1.1, (s.1.1.2, s.1.2.2)))
      (ex_unit (fun t : Z.carrier × S.carrier × X.carrier => (t.1, t.2.1))
        (subst (fun t : Z.carrier × S.carrier × X.carrier => (t.2.1, t.2.2)) m.rel))
    rw [← subst_comp, ← subst_comp] at hu
    refine le_trans ?_ hu
    rw [show (fun s : { p : (Z.carrier × S.carrier) × (S.carrier × X.carrier) //
            Prod.snd p.1 = Prod.fst p.2 } => s.1.2)
          = ((fun t : Z.carrier × S.carrier × X.carrier => (t.2.1, t.2.2)) ∘
              (fun s => (s.1.1.1, (s.1.1.2, s.1.2.2)))) from by
      funext s
      show s.1.2 = (s.1.1.2, s.1.2.2)
      rw [s.2]]
    exact le_refl _
  refine le_trans (le_conj (le_refl G.rel) hmtot) ?_
  refine le_trans (frobenius (fun t : Z.carrier × S.carrier × X.carrier => (t.1, t.2.1))
    (subst (fun t : Z.carrier × S.carrier × X.carrier => (t.2.1, t.2.2)) m.rel) G.rel) ?_
  refine ex_adj_mpr ?_
  have hcg : conj (subst (fun t : Z.carrier × S.carrier × X.carrier => (t.1, t.2.1)) G.rel)
      (subst (fun t : Z.carrier × S.carrier × X.carrier => (t.2.1, t.2.2)) m.rel)
      ⊢ subst (fun t : Z.carrier × S.carrier × X.carrier => (t.1, t.2.2)) (compRel G m) := by
    have hu := subst_mono (fun t : Z.carrier × S.carrier × X.carrier => (t.1, t.2.1, t.2.2))
      (ex_unit (fun d : Z.carrier × S.carrier × X.carrier => (d.1, d.2.2))
        (conj (subst (fun d : Z.carrier × S.carrier × X.carrier => (d.1, d.2.1)) G.rel)
              (subst (fun d : Z.carrier × S.carrier × X.carrier => (d.2.1, d.2.2)) m.rel)))
    simp only [subst_conj, ← subst_comp] at hu
    exact hu
  refine le_trans (le_conj (conj_le_right _ _)
    (le_trans hcg (subst_mono (fun t : Z.carrier × S.carrier × X.carrier => (t.1, t.2.2)) hfwd))) ?_
  refine le_trans (conj_mono (le_refl _)
    (subst_ex_mid (fun t : Z.carrier × S.carrier × X.carrier => (t.1, t.2.2))
      (conj (subst (fun d : Z.carrier × S.carrier × X.carrier => (d.1, d.2.1)) H.rel)
            (subst (fun d : Z.carrier × S.carrier × X.carrier => (d.2.1, d.2.2)) m.rel)))) ?_
  refine le_trans (le_conj (conj_le_right _ _) (conj_le_left _ _)) ?_
  refine conj_ex_elim Prod.fst ?_
  simp only [subst_conj, ← subst_comp, Function.comp_def]
  have hHcong := subst_mono (fun p : (Z.carrier × S.carrier × X.carrier) × S.carrier =>
    (p.1.1, p.1.1, p.2, p.1.2.1)) H.cong
  simp only [subst_conj, ← subst_comp, Function.comp_def] at hHcong
  have hinj := subst_mono (fun p : (Z.carrier × S.carrier × X.carrier) × S.carrier =>
    (p.1.2.1, p.2, p.1.2.2)) inj
  simp only [subst_conj, ← subst_comp, Function.comp_def] at hinj
  have hHdom := subst_mono (fun p : (Z.carrier × S.carrier × X.carrier) × S.carrier =>
    (p.1.1, p.2)) H.strict_dom
  simp only [← subst_comp, Function.comp_def] at hHdom
  refine le_trans (le_conj (le_conj ?_ ?_) ?_) hHcong
  · exact le_trans (conj_le_right _ _) (conj_le_left _ _)
  · exact le_trans (le_trans (conj_le_right _ _) (conj_le_left _ _)) hHdom
  · refine le_trans (le_conj (conj_le_left _ _)
      (le_trans (conj_le_right _ _) (conj_le_right _ _)))
      (le_trans hinj (S.symm_at (K := (Z.carrier × S.carrier × X.carrier) × S.carrier)
        (fun p => p.1.2.1) (fun p => p.2)))

/-! ### Assembling the pullback lift -/

/-- The pullback lift `u : W ⟶ S`, given the factoring `hfac` (from the cone) and
relational injectivity `e` (from `Mono m`). -/
def uFunRel {W X S : PER P} (a : FunRel W X) (m : FunRel S X)
    (hfac : a.rel ⊢ ex (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.1))
              (subst (fun d : W.carrier × X.carrier × S.carrier => (d.2.2, d.2.1)) m.rel))
    (e : conj (subst (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.2)) m.rel)
              (subst (fun p : S.carrier × S.carrier × X.carrier => (p.2.1, p.2.2)) m.rel)
           ⊢ subst (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.1)) S.rel) :
    FunRel W S where
  rel := uRel a m
  strict_dom := uRel_strict_dom a m
  strict_cod := uRel_strict_cod a m
  cong := uRel_cong a m
  single := uRel_single a m e
  total := uRel_total a m hfac

/-- `m ∘ u ⊢ a`: forward direction of the lift property (`m.single` collapses the two
`X`-witnesses, then `a.cong` transports).  Independent of `hfac`/`e`. -/
def m_comp_u_le {W X S : PER P} (a : FunRel W X) (m : FunRel S X)
    (hfac : a.rel ⊢ ex (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.1))
              (subst (fun d : W.carrier × X.carrier × S.carrier => (d.2.2, d.2.1)) m.rel))
    (e : conj (subst (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.2)) m.rel)
              (subst (fun p : S.carrier × S.carrier × X.carrier => (p.2.1, p.2.2)) m.rel)
           ⊢ subst (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.1)) S.rel) :
    compRel (uFunRel a m hfac e) m ⊢ a.rel := by
  refine ex_adj_mpr ?_
  refine le_trans (conj_mono
    (subst_ex_mid (fun d : W.carrier × S.carrier × X.carrier => (d.1, d.2.1))
      (conj (subst (fun t : W.carrier × X.carrier × S.carrier => (t.1, t.2.1)) a.rel)
            (subst (fun t : W.carrier × X.carrier × S.carrier => (t.2.2, t.2.1)) m.rel)))
    (le_refl _)) ?_
  refine conj_ex_elim Prod.fst ?_
  have hmsingle : conj (subst (fun p : (W.carrier × S.carrier × X.carrier) × X.carrier =>
                    (p.1.2.1, p.2)) m.rel)
                  (subst (fun p => (p.1.2.1, p.1.2.2)) m.rel)
              ⊢ subst (fun p => (p.2, p.1.2.2)) X.rel := by
    have h := subst_mono (fun p : (W.carrier × S.carrier × X.carrier) × X.carrier =>
      (p.1.2.1, p.2, p.1.2.2)) m.single
    simp only [subst_conj, ← subst_comp] at h
    exact h
  have hwdom : subst (fun p : (W.carrier × S.carrier × X.carrier) × X.carrier => (p.1.1, p.2)) a.rel
                ⊢ subst (fun p => (p.1.1, p.1.1)) W.rel := by
    have h := subst_mono (fun p : (W.carrier × S.carrier × X.carrier) × X.carrier =>
      (p.1.1, p.2)) a.strict_dom
    rw [← subst_comp] at h
    exact h
  have hacong : conj (conj (subst (fun p : (W.carrier × S.carrier × X.carrier) × X.carrier =>
                    (p.1.1, p.2)) a.rel)
                    (subst (fun p => (p.1.1, p.1.1)) W.rel))
                  (subst (fun p => (p.2, p.1.2.2)) X.rel)
              ⊢ subst (fun p => (p.1.1, p.1.2.2)) a.rel := by
    have h := subst_mono (fun p : (W.carrier × S.carrier × X.carrier) × X.carrier =>
      (p.1.1, p.1.1, p.2, p.1.2.2)) a.cong
    simp only [subst_conj, ← subst_comp] at h
    exact h
  simp only [subst_conj, ← subst_comp]
  refine le_trans (le_conj (le_conj ?_ ?_) ?_) hacong
  · exact le_trans (conj_le_right _ _) (conj_le_left _ _)
  · exact le_trans (le_trans (conj_le_right _ _) (conj_le_left _ _)) hwdom
  · exact le_trans (le_conj (le_trans (conj_le_right _ _) (conj_le_right _ _)) (conj_le_left _ _))
      hmsingle

/-- The lift satisfies `m ∘ u = a` (the reverse entailment is free by
`funrel_eq_of_le`). -/
def m_comp_u {W X S : PER P} (a : FunRel W X) (m : FunRel S X)
    (hfac : a.rel ⊢ ex (fun d : W.carrier × X.carrier × S.carrier => (d.1, d.2.1))
              (subst (fun d : W.carrier × X.carrier × S.carrier => (d.2.2, d.2.1)) m.rel))
    (e : conj (subst (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.2)) m.rel)
              (subst (fun p : S.carrier × S.carrier × X.carrier => (p.2.1, p.2.2)) m.rel)
           ⊢ subst (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.1)) S.rel) :
    Hom.comp (Quotient.mk _ m) (Quotient.mk _ (uFunRel a m hfac e)) = Quotient.mk _ a :=
  Quotient.sound ⟨⟨m_comp_u_le a m hfac e⟩,
    ⟨funrel_eq_of_le (compFunRel (uFunRel a m hfac e) m) a (m_comp_u_le a m hfac e)⟩⟩

/-! ### Exponentials

An element of `Y ^ X` is a *code* `f : X.carrier × Y.carrier → Prop'` for the
relation `subst f generic`.  Two codes are `(Y^X)`-related when each codes a
functional relation and the two relations are extensionally equal. -/

/-- `f(x,y)`: the proposition coded by `f` at `(x, y)`, as a predicate over any
index carrying a code and a point. -/
abbrev ExpCar (X Y : PER P) : Type u := X.carrier × Y.carrier → Prop' P

/-- Strictness of domain, as a predicate on codes. -/
def expStrictDom (X Y : PER P) : P (ExpCar X Y) :=
  all (fun t : ExpCar X Y × X.carrier × Y.carrier => t.1)
    (impl (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => t.1 (t.2.1, t.2.2))
            (@Tripos.generic P _))
          (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => (t.2.1, t.2.1)) X.rel))

/-- Strictness of codomain, as a predicate on codes. -/
def expStrictCod (X Y : PER P) : P (ExpCar X Y) :=
  all (fun t : ExpCar X Y × X.carrier × Y.carrier => t.1)
    (impl (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => t.1 (t.2.1, t.2.2))
            (@Tripos.generic P _))
          (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => (t.2.2, t.2.2)) Y.rel))

/-- Relational/extensional condition, as a predicate on codes. -/
def expCongCond (X Y : PER P) : P (ExpCar X Y) :=
  all (fun t : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier => t.1)
    (impl (conj (conj
        (subst (fun t : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier =>
          t.1 (t.2.1, t.2.2.1)) (@Tripos.generic P _))
        (subst (fun t : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier =>
          (t.2.1, t.2.2.2.1)) X.rel))
        (subst (fun t : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier =>
          (t.2.2.1, t.2.2.2.2)) Y.rel))
      (subst (fun t : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier =>
        t.1 (t.2.2.2.1, t.2.2.2.2)) (@Tripos.generic P _)))

/-- Single-valuedness, as a predicate on codes. -/
def expSingleCond (X Y : PER P) : P (ExpCar X Y) :=
  all (fun t : ExpCar X Y × X.carrier × Y.carrier × Y.carrier => t.1)
    (impl (conj
        (subst (fun t : ExpCar X Y × X.carrier × Y.carrier × Y.carrier =>
          t.1 (t.2.1, t.2.2.1)) (@Tripos.generic P _))
        (subst (fun t : ExpCar X Y × X.carrier × Y.carrier × Y.carrier =>
          t.1 (t.2.1, t.2.2.2)) (@Tripos.generic P _)))
      (subst (fun t : ExpCar X Y × X.carrier × Y.carrier × Y.carrier =>
        (t.2.2.1, t.2.2.2)) Y.rel))

/-- Totality, as a predicate on codes. -/
def expTotalCond (X Y : PER P) : P (ExpCar X Y) :=
  all (fun t : ExpCar X Y × X.carrier => t.1)
    (impl (subst (fun t : ExpCar X Y × X.carrier => (t.2, t.2)) X.rel)
      (ex (fun u : ExpCar X Y × X.carrier × Y.carrier => (u.1, u.2.1))
          (subst (fun u : ExpCar X Y × X.carrier × Y.carrier => u.1 (u.2.1, u.2.2))
            (@Tripos.generic P _))))

/-- A code is a functional relation. -/
def expIsFunc (X Y : PER P) : P (ExpCar X Y) :=
  conj (conj (conj (expStrictDom X Y) (expStrictCod X Y))
             (conj (expCongCond X Y) (expSingleCond X Y))) (expTotalCond X Y)

/-- Body of the extensional-equality predicate: `f(x,y) ↔ g(x,y)`. -/
def expExtBody (X Y : PER P) :
    P ((ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier) :=
  conj (impl (subst (fun t : (ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier =>
                t.1.1 (t.2.1, t.2.2)) (@Tripos.generic P _))
             (subst (fun t : (ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier =>
                t.1.2 (t.2.1, t.2.2)) (@Tripos.generic P _)))
       (impl (subst (fun t : (ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier =>
                t.1.2 (t.2.1, t.2.2)) (@Tripos.generic P _))
             (subst (fun t : (ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier =>
                t.1.1 (t.2.1, t.2.2)) (@Tripos.generic P _)))

/-- Extensional equality of two codes. -/
def expExtEq (X Y : PER P) : P (ExpCar X Y × ExpCar X Y) :=
  all (Prod.fst : (ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier → ExpCar X Y × ExpCar X Y)
    (expExtBody X Y)

/-- Extensional equality is symmetric (`↔` is). -/
def expExtEq_symm (X Y : PER P) : expExtEq X Y ⊢ subst Prod.swap (expExtEq X Y) := by
  refine le_trans (all_mono _ ?_) (all_subst_fst Prod.swap (expExtBody X Y))
  simp only [expExtBody, subst_conj, subst_impl, ← subst_comp]
  exact conj_comm _ _

/-- Extensional equality is transitive (`↔` is). -/
def expExtEq_trans (X Y : PER P) :
    conj (subst (fun t : ExpCar X Y × ExpCar X Y × ExpCar X Y => (t.1, t.2.1)) (expExtEq X Y))
         (subst (fun t : ExpCar X Y × ExpCar X Y × ExpCar X Y => (t.2.1, t.2.2)) (expExtEq X Y))
      ⊢ subst (fun t : ExpCar X Y × ExpCar X Y × ExpCar X Y => (t.1, t.2.2)) (expExtEq X Y) := by
  refine le_trans (all_adj_mp ?_)
    (all_subst_fst (fun t : ExpCar X Y × ExpCar X Y × ExpCar X Y => (t.1, t.2.2))
      (expExtBody X Y))
  have hc1 := subst_mono
    (fun p : (ExpCar X Y × ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier =>
      ((p.1.1, p.1.2.1), p.2))
    (all_counit (Prod.fst : (ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier →
      ExpCar X Y × ExpCar X Y) (expExtBody X Y))
  have hc2 := subst_mono
    (fun p : (ExpCar X Y × ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier =>
      ((p.1.2.1, p.1.2.2), p.2))
    (all_counit (Prod.fst : (ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier →
      ExpCar X Y × ExpCar X Y) (expExtBody X Y))
  simp only [← subst_comp] at hc1 hc2
  simp only [expExtEq, subst_conj, ← subst_comp]
  refine le_trans (conj_mono hc1 hc2) ?_
  simp only [expExtBody, subst_conj, subst_impl, ← subst_comp]
  refine le_conj
    (le_trans (le_conj (le_trans (conj_le_left _ _) (conj_le_left _ _))
      (le_trans (conj_le_right _ _) (conj_le_left _ _))) (impl_trans _ _ _))
    (le_trans (le_conj (le_trans (conj_le_right _ _) (conj_le_right _ _))
      (le_trans (conj_le_left _ _) (conj_le_right _ _))) (impl_trans _ _ _))

/-- The exponential object `Y ^ X`. -/
def expObj (X Y : PER P) : PER P where
  carrier := ExpCar X Y
  rel := conj (conj (subst Prod.fst (expIsFunc X Y)) (subst Prod.snd (expIsFunc X Y)))
              (expExtEq X Y)
  symm := by
    simp only [subst_conj, ← subst_comp]
    refine le_conj (le_conj ?_ ?_) ?_
    · exact le_trans (conj_le_left _ _) (conj_le_right _ _)
    · exact le_trans (conj_le_left _ _) (conj_le_left _ _)
    · exact le_trans (conj_le_right _ _) (expExtEq_symm X Y)
  trans := by
    simp only [subst_conj, ← subst_comp]
    refine le_conj (le_conj ?_ ?_) ?_
    · exact le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) (conj_le_left _ _)
    · exact le_trans (le_trans (conj_le_right _ _) (conj_le_left _ _)) (conj_le_right _ _)
    · exact le_trans (le_conj (le_trans (conj_le_left _ _) (conj_le_right _ _))
        (le_trans (conj_le_right _ _) (conj_le_right _ _))) (expExtEq_trans X Y)

/-! ### Evaluation -/

/-- The evaluation relation `((f, x), y)`: the domain pair exists and `f(x, y)`. -/
def expEvalRel (X Y : PER P) :
    P (((expObj X Y).carrier × X.carrier) × Y.carrier) :=
  conj (subst (fun p : ((expObj X Y).carrier × X.carrier) × Y.carrier => (p.1, p.1))
          (prodPER (expObj X Y) X).rel)
       (subst (fun p : ((expObj X Y).carrier × X.carrier) × Y.carrier => p.1.1 (p.1.2, p.2))
          (@Tripos.generic P _))

/-- Evaluation is strict in the domain (trivially). -/
def expEval_strict_dom (X Y : PER P) :
    expEvalRel X Y ⊢ subst (fun p : ((expObj X Y).carrier × X.carrier) × Y.carrier => (p.1, p.1))
      (prodPER (expObj X Y) X).rel :=
  conj_le_left _ _

/-- Evaluation is strict in the codomain: the value exists (from `f`'s `strictCod`). -/
def expEval_strict_cod (X Y : PER P) :
    expEvalRel X Y ⊢ subst (fun p : ((expObj X Y).carrier × X.carrier) × Y.carrier => (p.2, p.2))
      Y.rel := by
  have hinst := all_inst (fun t : ExpCar X Y × X.carrier × Y.carrier => t.1)
    (fun p : ((expObj X Y).carrier × X.carrier) × Y.carrier => (p.1.1, p.1.2, p.2))
    (impl (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => t.1 (t.2.1, t.2.2))
            (@Tripos.generic P _))
          (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => (t.2.2, t.2.2)) Y.rel))
  simp only [subst_impl, ← subst_comp] at hinst
  refine le_trans (le_conj ?_ (conj_le_right _ _)) (impl_mp _ _)
  refine le_trans (conj_le_left _ _) (le_trans ?_ hinst)
  simp only [prodPER, expObj, expIsFunc, subst_conj, ← subst_comp]
  exact le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _)
    (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (conj_le_right _ _)))))

/-- Evaluation is single-valued (from `f`'s `single`). -/
def expEval_single (X Y : PER P) :
    conj (subst (fun t : ((expObj X Y).carrier × X.carrier) × Y.carrier × Y.carrier => (t.1, t.2.1))
            (expEvalRel X Y))
         (subst (fun t : ((expObj X Y).carrier × X.carrier) × Y.carrier × Y.carrier => (t.1, t.2.2))
            (expEvalRel X Y))
      ⊢ subst (fun t : ((expObj X Y).carrier × X.carrier) × Y.carrier × Y.carrier => (t.2.1, t.2.2))
          Y.rel := by
  have hinst := all_inst (fun t : ExpCar X Y × X.carrier × Y.carrier × Y.carrier => t.1)
    (fun t : ((expObj X Y).carrier × X.carrier) × Y.carrier × Y.carrier =>
      (t.1.1, t.1.2, t.2.1, t.2.2))
    (impl (conj (subst (fun t : ExpCar X Y × X.carrier × Y.carrier × Y.carrier =>
                  t.1 (t.2.1, t.2.2.1)) (@Tripos.generic P _))
                (subst (fun t : ExpCar X Y × X.carrier × Y.carrier × Y.carrier =>
                  t.1 (t.2.1, t.2.2.2)) (@Tripos.generic P _)))
          (subst (fun t : ExpCar X Y × X.carrier × Y.carrier × Y.carrier =>
            (t.2.2.1, t.2.2.2)) Y.rel))
  simp only [subst_impl, subst_conj, ← subst_comp] at hinst
  simp only [expEvalRel, subst_conj, ← subst_comp]
  refine le_trans (le_conj (le_trans ?_ hinst)
    (le_conj (le_trans (conj_le_left _ _) (conj_le_right _ _))
             (le_trans (conj_le_right _ _) (conj_le_right _ _)))) (impl_mp _ _)
  refine le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) ?_
  simp only [prodPER, expObj, expIsFunc, subst_conj, ← subst_comp]
  exact le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _)
    (le_trans (conj_le_left _ _) (le_trans (conj_le_right _ _) (conj_le_right _ _)))))

/-- Evaluation is total (from `f`'s `total`). -/
def expEval_total (X Y : PER P) :
    subst (fun d : (expObj X Y).carrier × X.carrier => (d, d)) (prodPER (expObj X Y) X).rel
      ⊢ ex (Prod.fst : ((expObj X Y).carrier × X.carrier) × Y.carrier →
              (expObj X Y).carrier × X.carrier)
          (expEvalRel X Y) := by
  have hreassoc :
      ex (fun u : ExpCar X Y × X.carrier × Y.carrier => (u.1, u.2.1))
         (subst (fun u : ExpCar X Y × X.carrier × Y.carrier => u.1 (u.2.1, u.2.2))
            (@Tripos.generic P _))
        ⊢ ex (Prod.fst : ((expObj X Y).carrier × X.carrier) × Y.carrier →
                (expObj X Y).carrier × X.carrier)
            (subst (fun p : ((expObj X Y).carrier × X.carrier) × Y.carrier =>
              p.1.1 (p.1.2, p.2)) (@Tripos.generic P _)) := by
    refine ex_adj_mpr ?_
    have h := subst_mono (fun u : ExpCar X Y × X.carrier × Y.carrier => ((u.1, u.2.1), u.2.2))
      (ex_unit (Prod.fst : ((expObj X Y).carrier × X.carrier) × Y.carrier →
          (expObj X Y).carrier × X.carrier)
        (subst (fun p : ((expObj X Y).carrier × X.carrier) × Y.carrier =>
          p.1.1 (p.1.2, p.2)) (@Tripos.generic P _)))
    erw [← subst_comp, ← subst_comp] at h
    exact h
  have hcounit := all_counit (fun t : ExpCar X Y × X.carrier => t.1)
    (impl (subst (fun t : ExpCar X Y × X.carrier => (t.2, t.2)) X.rel)
          (ex (fun u : ExpCar X Y × X.carrier × Y.carrier => (u.1, u.2.1))
              (subst (fun u : ExpCar X Y × X.carrier × Y.carrier => u.1 (u.2.1, u.2.2))
                (@Tripos.generic P _))))
  have htot :
      subst (fun d : (expObj X Y).carrier × X.carrier => (d, d)) (prodPER (expObj X Y) X).rel
        ⊢ ex (fun u : ExpCar X Y × X.carrier × Y.carrier => (u.1, u.2.1))
            (subst (fun u : ExpCar X Y × X.carrier × Y.carrier => u.1 (u.2.1, u.2.2))
              (@Tripos.generic P _)) := by
    refine le_trans (le_conj ?_ ?_)
      (impl_mp (subst (fun t : ExpCar X Y × X.carrier => (t.2, t.2)) X.rel) _)
    · refine le_trans ?_ hcounit
      simp only [prodPER, expObj, expIsFunc, subst_conj, ← subst_comp]
      exact le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _)
        (le_trans (conj_le_left _ _) (conj_le_right _ _)))
    · simp only [prodPER, expObj, expIsFunc, subst_conj, ← subst_comp]
      exact conj_le_right _ _
  refine le_trans (le_conj (le_refl _) (le_trans htot hreassoc)) ?_
  refine le_trans (frobenius (Prod.fst : ((expObj X Y).carrier × X.carrier) × Y.carrier →
      (expObj X Y).carrier × X.carrier)
    (subst (fun p : ((expObj X Y).carrier × X.carrier) × Y.carrier => p.1.1 (p.1.2, p.2))
      (@Tripos.generic P _))
    (subst (fun d : (expObj X Y).carrier × X.carrier => (d, d)) (prodPER (expObj X Y) X).rel))
    (ex_mono _ ?_)
  simp only [expEvalRel]
  refine conj_mono ?_ (le_refl _)
  rw [← subst_comp]
  exact le_refl _

/-- Evaluation is relational (from `f`'s `cong` and `f ≈ f'`). -/
def expEval_cong (X Y : PER P) :
    conj (conj (subst (fun t : ((expObj X Y).carrier × X.carrier) ×
                  ((expObj X Y).carrier × X.carrier) × Y.carrier × Y.carrier => (t.1, t.2.2.1))
                (expEvalRel X Y))
               (subst (fun t : ((expObj X Y).carrier × X.carrier) ×
                  ((expObj X Y).carrier × X.carrier) × Y.carrier × Y.carrier => (t.1, t.2.1))
                (prodPER (expObj X Y) X).rel))
         (subst (fun t : ((expObj X Y).carrier × X.carrier) ×
            ((expObj X Y).carrier × X.carrier) × Y.carrier × Y.carrier => (t.2.2.1, t.2.2.2)) Y.rel)
      ⊢ subst (fun t : ((expObj X Y).carrier × X.carrier) ×
          ((expObj X Y).carrier × X.carrier) × Y.carrier × Y.carrier => (t.2.1, t.2.2.2))
          (expEvalRel X Y) := by
  have hcong := all_inst (fun s : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier => s.1)
    (fun t : ((expObj X Y).carrier × X.carrier) ×
        ((expObj X Y).carrier × X.carrier) × Y.carrier × Y.carrier =>
      (t.1.1, t.1.2, t.2.2.1, t.2.1.2, t.2.2.2))
    (impl (conj (conj
        (subst (fun s : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier =>
          s.1 (s.2.1, s.2.2.1)) (@Tripos.generic P _))
        (subst (fun s : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier =>
          (s.2.1, s.2.2.2.1)) X.rel))
        (subst (fun s : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier =>
          (s.2.2.1, s.2.2.2.2)) Y.rel))
      (subst (fun s : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier =>
        s.1 (s.2.2.2.1, s.2.2.2.2)) (@Tripos.generic P _)))
  have hext := all_inst
    (Prod.fst : (ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier → ExpCar X Y × ExpCar X Y)
    (fun t : ((expObj X Y).carrier × X.carrier) ×
        ((expObj X Y).carrier × X.carrier) × Y.carrier × Y.carrier =>
      ((t.1.1, t.2.1.1), (t.2.1.2, t.2.2.2)))
    (expExtBody X Y)
  simp only [subst_impl, subst_conj, ← subst_comp] at hcong
  simp only [expEvalRel, subst_conj, ← subst_comp]
  refine le_conj ?_ ?_
  · exact le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
      ((prodPER (expObj X Y) X).refl_right_at
        (K := ((expObj X Y).carrier × X.carrier) ×
          ((expObj X Y).carrier × X.carrier) × Y.carrier × Y.carrier)
        (fun t => t.1) (fun t => t.2.1))
  · exact le_trans (le_conj
      (le_trans (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
          (by simp only [prodPER, expObj, expIsFunc, subst_conj, ← subst_comp]
              exact le_trans (conj_le_left _ _) (conj_le_right _ _)))
        (le_trans hext (by
          simp only [expExtBody, subst_conj, subst_impl, ← subst_comp]
          exact conj_le_left _ _)))
      (le_trans (le_conj
          (le_trans (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
              (by simp only [prodPER, expObj, expIsFunc, subst_conj, ← subst_comp]
                  exact le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _)
                    (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _)
                      (le_trans (conj_le_right _ _) (conj_le_left _ _)))))))
            hcong)
          (le_conj (le_conj
              (le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) (conj_le_right _ _))
              (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
                (by simp only [prodPER, subst_conj, ← subst_comp]; exact conj_le_right _ _)))
            (conj_le_right _ _)))
        (impl_mp _ _)))
      (impl_mp _ _)

/-- The evaluation morphism `Y ^ X × X ⟶ Y`. -/
def expEval (X Y : PER P) : FunRel (prodPER (expObj X Y) X) Y where
  rel := expEvalRel X Y
  strict_dom := expEval_strict_dom X Y
  strict_cod := expEval_strict_cod X Y
  cong := expEval_cong X Y
  single := expEval_single X Y
  total := expEval_total X Y

/-- The evaluation morphism as a `Hom`. -/
def Hom.eval (X Y : PER P) : Hom (prodPER (expObj X Y) X) Y := Quotient.mk _ (expEval X Y)

/-! ### Currying (the exponential transpose) -/

/-- Body of the transpose relation: `f(x,y) ↔ g((z,x),y)`. -/
def ΛBody (g : FunRel (prodPER Z X) Y) :
    P ((Z.carrier × ExpCar X Y) × X.carrier × Y.carrier) :=
  conj (impl (subst (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier =>
                q.1.2 (q.2.1, q.2.2)) (@Tripos.generic P _))
             (subst (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier =>
                ((q.1.1, q.2.1), q.2.2)) g.rel))
       (impl (subst (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier =>
                ((q.1.1, q.2.1), q.2.2)) g.rel)
             (subst (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier =>
                q.1.2 (q.2.1, q.2.2)) (@Tripos.generic P _)))

/-- The transpose relation `z ↦ f` where `f` codes `g(z, ·)`. -/
def ΛRel (g : FunRel (prodPER Z X) Y) : P (Z.carrier × ExpCar X Y) :=
  conj (subst (fun p : Z.carrier × ExpCar X Y => (p.1, p.1)) Z.rel)
    (all (Prod.fst : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier → Z.carrier × ExpCar X Y)
      (ΛBody g))

/-- The transpose is strict in the domain (trivially). -/
def Λ_strict_dom (g : FunRel (prodPER Z X) Y) :
    ΛRel g ⊢ subst (fun p : Z.carrier × ExpCar X Y => (p.1, p.1)) Z.rel :=
  conj_le_left _ _

/-- `g` as a predicate over `Z × (X × Y)` (reassociated). -/
def Λcg (g : FunRel (prodPER Z X) Y) : P (Z.carrier × (X.carrier × Y.carrier)) :=
  subst (fun w : Z.carrier × (X.carrier × Y.carrier) => ((w.1, w.2.1), w.2.2)) g.rel

/-- The transpose is total: the witness code for `z` is `char (g(z, ·))`. -/
def Λ_total (g : FunRel (prodPER Z X) Y) :
    subst (fun z : Z.carrier => (z, z)) Z.rel
      ⊢ ex (Prod.fst : Z.carrier × ExpCar X Y → Z.carrier) (ΛRel g) := by
  have hu := subst_mono
    (fun z : Z.carrier => (z, fun p : X.carrier × Y.carrier => Tripos.char (Λcg g) (z, p)))
    (ex_unit (Prod.fst : Z.carrier × ExpCar X Y → Z.carrier) (ΛRel g))
  simp only [← subst_comp] at hu
  refine le_trans ?_ (le_trans hu (subst_id_le _))
  simp only [ΛRel, subst_conj, ← subst_comp]
  refine le_conj (le_refl _) ?_
  refine le_trans (all_adj_mp ?_)
    (all_subst_fst
      (fun z : Z.carrier => (z, fun p : X.carrier × Y.carrier => Tripos.char (Λcg g) (z, p)))
      (ΛBody g))
  simp only [ΛBody, subst_impl, subst_conj, ← subst_comp, Function.comp_def]
  rw [show (fun p : Z.carrier × X.carrier × Y.carrier =>
        Tripos.char (Λcg g) (p.1, (p.2.1, p.2.2)))
      = (Tripos.char (Λcg g)) ∘ (fun p : Z.carrier × X.carrier × Y.carrier =>
          (p.1, (p.2.1, p.2.2))) from rfl, subst_comp, subst_char, Λcg, ← subst_comp]
  refine le_trans (le_top _) (le_conj (id_impl _) (id_impl _))

/-- Extensional equality of `f` with itself (reflexivity of `↔`). -/
def Λ_extEq_refl (g : FunRel (prodPER Z X) Y) :
    ΛRel g ⊢ subst (fun p : Z.carrier × ExpCar X Y => (p.2, p.2)) (expExtEq X Y) := by
  refine le_trans (all_adj_mp ?_)
    (all_subst_fst (fun p : Z.carrier × ExpCar X Y => (p.2, p.2)) (expExtBody X Y))
  simp only [expExtBody, subst_conj, subst_impl, ← subst_comp]
  exact le_trans (le_top _) (le_conj (id_impl _) (id_impl _))

/-- The transposed code `f` inherits strictness-of-domain from `g`. -/
def Λ_strictDom_f (g : FunRel (prodPER Z X) Y) :
    ΛRel g ⊢ subst (fun p : Z.carrier × ExpCar X Y => p.2) (expStrictDom X Y) := by
  refine le_trans (all_adj_mp ?_)
    (all_subst_fst (fun p : Z.carrier × ExpCar X Y => p.2)
      (impl (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => t.1 (t.2.1, t.2.2))
              (@Tripos.generic P _))
            (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => (t.2.1, t.2.1)) X.rel)))
  simp only [ΛRel, subst_impl, subst_conj, ← subst_comp]
  apply curry
  have hg := subst_mono
    (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier => ((q.1.1, q.2.1), q.2.2))
    g.strict_dom
  simp only [← subst_comp] at hg
  refine le_trans (le_conj
    (le_trans (conj_le_left _ _)
      (le_trans (conj_le_right _ _) (le_trans (all_counit _ _) (conj_le_left _ _))))
    (conj_le_right _ _))
    (le_trans (impl_mp _ _) (le_trans hg ?_))
  simp only [prodPER, subst_conj, ← subst_comp]
  exact conj_le_right _ _

/-- The transposed code `f` inherits strictness-of-codomain from `g`. -/
def Λ_strictCod_f (g : FunRel (prodPER Z X) Y) :
    ΛRel g ⊢ subst (fun p : Z.carrier × ExpCar X Y => p.2) (expStrictCod X Y) := by
  refine le_trans (all_adj_mp ?_)
    (all_subst_fst (fun p : Z.carrier × ExpCar X Y => p.2)
      (impl (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => t.1 (t.2.1, t.2.2))
              (@Tripos.generic P _))
            (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => (t.2.2, t.2.2)) Y.rel)))
  simp only [ΛRel, subst_impl, subst_conj, ← subst_comp]
  apply curry
  have hg := subst_mono
    (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier => ((q.1.1, q.2.1), q.2.2))
    g.strict_cod
  erw [← subst_comp] at hg
  exact le_trans (le_conj
    (le_trans (conj_le_left _ _)
      (le_trans (conj_le_right _ _) (le_trans (all_counit _ _) (conj_le_left _ _))))
    (conj_le_right _ _))
    (le_trans (impl_mp _ _) hg)

/-- The transposed code `f` inherits single-valuedness from `g`. -/
def Λ_singleCond_f (g : FunRel (prodPER Z X) Y) :
    ΛRel g ⊢ subst (fun p : Z.carrier × ExpCar X Y => p.2) (expSingleCond X Y) := by
  refine le_trans (all_adj_mp ?_)
    (all_subst_fst (fun p : Z.carrier × ExpCar X Y => p.2)
      (impl (conj (subst (fun t : ExpCar X Y × X.carrier × Y.carrier × Y.carrier =>
                    t.1 (t.2.1, t.2.2.1)) (@Tripos.generic P _))
                  (subst (fun t : ExpCar X Y × X.carrier × Y.carrier × Y.carrier =>
                    t.1 (t.2.1, t.2.2.2)) (@Tripos.generic P _)))
            (subst (fun t : ExpCar X Y × X.carrier × Y.carrier × Y.carrier =>
              (t.2.2.1, t.2.2.2)) Y.rel)))
  simp only [ΛRel, subst_impl, subst_conj, ← subst_comp]
  apply curry
  have hgs := subst_mono
    (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier × Y.carrier =>
      ((q.1.1, q.2.1), q.2.2.1, q.2.2.2)) g.single
  simp only [prodPER, subst_conj, ← subst_comp] at hgs
  have hb1 := all_inst
    (Prod.fst : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier → Z.carrier × ExpCar X Y)
    (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier × Y.carrier => (q.1, (q.2.1, q.2.2.1)))
    (ΛBody g)
  have hb2 := all_inst
    (Prod.fst : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier → Z.carrier × ExpCar X Y)
    (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier × Y.carrier => (q.1, (q.2.1, q.2.2.2)))
    (ΛBody g)
  refine le_trans (le_conj
    (le_trans (le_conj
        (le_trans (conj_le_left _ _) (le_trans (conj_le_right _ _) (le_trans hb1
          (by simp only [ΛBody, subst_conj, subst_impl, ← subst_comp]; exact conj_le_left _ _))))
        (le_trans (conj_le_right _ _) (conj_le_left _ _)))
      (impl_mp _ _))
    (le_trans (le_conj
        (le_trans (conj_le_left _ _) (le_trans (conj_le_right _ _) (le_trans hb2
          (by simp only [ΛBody, subst_conj, subst_impl, ← subst_comp]; exact conj_le_left _ _))))
        (le_trans (conj_le_right _ _) (conj_le_right _ _)))
      (impl_mp _ _)))
    hgs

/-- The transposed code `f` inherits relationality from `g`. -/
def Λ_congCond_f (g : FunRel (prodPER Z X) Y) :
    ΛRel g ⊢ subst (fun p : Z.carrier × ExpCar X Y => p.2) (expCongCond X Y) := by
  refine le_trans (all_adj_mp ?_)
    (all_subst_fst (fun p : Z.carrier × ExpCar X Y => p.2)
      (impl (conj (conj
          (subst (fun t : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier =>
            t.1 (t.2.1, t.2.2.1)) (@Tripos.generic P _))
          (subst (fun t : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier =>
            (t.2.1, t.2.2.2.1)) X.rel))
          (subst (fun t : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier =>
            (t.2.2.1, t.2.2.2.2)) Y.rel))
        (subst (fun t : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier =>
          t.1 (t.2.2.2.1, t.2.2.2.2)) (@Tripos.generic P _))))
  simp only [ΛRel, subst_impl, subst_conj, ← subst_comp]
  apply curry
  have hgc := subst_mono
    (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier × X.carrier × Y.carrier =>
      ((q.1.1, q.2.1), (q.1.1, q.2.2.2.1), q.2.2.1, q.2.2.2.2)) g.cong
  simp only [prodPER, subst_conj, ← subst_comp] at hgc
  have hbf := all_inst
    (Prod.fst : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier → Z.carrier × ExpCar X Y)
    (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier × X.carrier × Y.carrier =>
      (q.1, (q.2.1, q.2.2.1))) (ΛBody g)
  have hbb := all_inst
    (Prod.fst : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier → Z.carrier × ExpCar X Y)
    (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier × X.carrier × Y.carrier =>
      (q.1, (q.2.2.2.1, q.2.2.2.2))) (ΛBody g)
  refine le_trans (le_conj
      (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _)) (le_trans hbb
        (by simp only [ΛBody, subst_conj, subst_impl, ← subst_comp]; exact conj_le_right _ _)))
      (le_trans (le_conj (le_conj
          (le_trans (le_conj
              (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _)) (le_trans hbf
                (by simp only [ΛBody, subst_conj, subst_impl, ← subst_comp]; exact conj_le_left _ _)))
              (le_trans (le_trans (conj_le_right _ _) (conj_le_left _ _)) (conj_le_left _ _)))
            (impl_mp _ _))
          (le_conj
            (le_trans (conj_le_left _ _) (conj_le_left _ _))
            (le_trans (le_trans (conj_le_right _ _) (conj_le_left _ _)) (conj_le_right _ _))))
        (le_trans (conj_le_right _ _) (conj_le_right _ _)))
        hgc))
    (impl_mp _ _)

/-- `∃y. g((z,x),y)` over the common index, for the transpose's totality. -/
def Λgex (g : FunRel (prodPER Z X) Y) :
    P ((Z.carrier × ExpCar X Y) × X.carrier) :=
  ex (Prod.fst : ((Z.carrier × ExpCar X Y) × X.carrier) × Y.carrier →
        (Z.carrier × ExpCar X Y) × X.carrier)
    (subst (fun w : ((Z.carrier × ExpCar X Y) × X.carrier) × Y.carrier =>
      ((w.1.1.1, w.1.2), w.2)) g.rel)

/-- From existence of `z` and `x`, `g` produces some value: `∃y. g((z,x),y)`. -/
def Λgex_total (g : FunRel (prodPER Z X) Y) :
    conj (subst (fun k : (Z.carrier × ExpCar X Y) × X.carrier => (k.1.1, k.1.1)) Z.rel)
         (subst (fun k : (Z.carrier × ExpCar X Y) × X.carrier => (k.2, k.2)) X.rel)
      ⊢ Λgex g := by
  refine le_trans ?_ (le_trans
    (subst_mono (fun k : (Z.carrier × ExpCar X Y) × X.carrier => (k.1.1, k.2)) g.total)
    (ex_subst_fst (fun k : (Z.carrier × ExpCar X Y) × X.carrier => (k.1.1, k.2)) g.rel))
  simp only [prodPER, subst_conj, ← subst_comp]
  exact le_refl _

/-- `∃y. f(code,x,y)` over the common index. -/
def Λfex (g : FunRel (prodPER Z X) Y) :
    P ((Z.carrier × ExpCar X Y) × X.carrier) :=
  ex (Prod.fst : ((Z.carrier × ExpCar X Y) × X.carrier) × Y.carrier →
        (Z.carrier × ExpCar X Y) × X.carrier)
    (subst (fun w : ((Z.carrier × ExpCar X Y) × X.carrier) × Y.carrier =>
      w.1.1.2 (w.1.2, w.2)) (@Tripos.generic P _))

/-- Carry the bi-implication into the existential: `∃y g → ∃y f`. -/
def Λfex_of_gex (g : FunRel (prodPER Z X) Y) :
    conj (subst (Prod.fst : (Z.carrier × ExpCar X Y) × X.carrier → Z.carrier × ExpCar X Y)
            (all (Prod.fst : (Z.carrier × ExpCar X Y) × (X.carrier × Y.carrier) →
                Z.carrier × ExpCar X Y) (ΛBody g)))
         (Λgex g)
      ⊢ Λfex g := by
  refine le_trans (frobenius
    (Prod.fst : ((Z.carrier × ExpCar X Y) × X.carrier) × Y.carrier →
      (Z.carrier × ExpCar X Y) × X.carrier)
    (subst (fun w : ((Z.carrier × ExpCar X Y) × X.carrier) × Y.carrier =>
      ((w.1.1.1, w.1.2), w.2)) g.rel)
    (subst (Prod.fst : (Z.carrier × ExpCar X Y) × X.carrier → Z.carrier × ExpCar X Y)
      (all (Prod.fst : (Z.carrier × ExpCar X Y) × (X.carrier × Y.carrier) → Z.carrier × ExpCar X Y)
        (ΛBody g))))
    (ex_mono _ ?_)
  have hinst := all_inst
    (Prod.fst : (Z.carrier × ExpCar X Y) × (X.carrier × Y.carrier) → Z.carrier × ExpCar X Y)
    (fun w : ((Z.carrier × ExpCar X Y) × X.carrier) × Y.carrier => (w.1.1, (w.1.2, w.2)))
    (ΛBody g)
  simp only [← subst_comp]
  refine le_trans (le_conj
    (le_trans (le_trans (conj_le_left _ _) hinst)
      (by simp only [ΛBody, subst_conj, subst_impl, ← subst_comp]; exact conj_le_right _ _))
    (conj_le_right _ _))
    (impl_mp _ _)

/-- The transposed code `f` inherits totality from `g`. -/
def Λ_totalCond_f (g : FunRel (prodPER Z X) Y) :
    ΛRel g ⊢ subst (fun p : Z.carrier × ExpCar X Y => p.2) (expTotalCond X Y) := by
  refine le_trans (all_adj_mp ?_) (all_subst_fst (fun p : Z.carrier × ExpCar X Y => p.2)
    (impl (subst (fun t : ExpCar X Y × X.carrier => (t.2, t.2)) X.rel)
      (ex (fun u : ExpCar X Y × X.carrier × Y.carrier => (u.1, u.2.1))
          (subst (fun u : ExpCar X Y × X.carrier × Y.carrier => u.1 (u.2.1, u.2.2))
            (@Tripos.generic P _)))))
  simp only [ΛRel, subst_impl, subst_conj, ← subst_comp]
  apply curry
  refine le_trans (le_conj (le_trans (conj_le_left _ _) (conj_le_right _ _))
      (le_trans (le_conj (le_trans (conj_le_left _ _) (conj_le_left _ _)) (conj_le_right _ _))
        (Λgex_total g)))
    (le_trans (Λfex_of_gex g) ?_)
  refine ex_adj_mpr ?_
  have hu := subst_mono
    (fun w : ((Z.carrier × ExpCar X Y) × X.carrier) × Y.carrier => (w.1.1.2, w.1.2, w.2))
    (ex_unit (fun u : ExpCar X Y × X.carrier × Y.carrier => (u.1, u.2.1))
      (subst (fun u : ExpCar X Y × X.carrier × Y.carrier => u.1 (u.2.1, u.2.2)) (@Tripos.generic P _)))
  simp only [← subst_comp] at hu
  erw [← subst_comp]
  exact hu

/-- The transposed code is a functional relation. -/
def Λ_isFunc (g : FunRel (prodPER Z X) Y) :
    ΛRel g ⊢ subst (fun p : Z.carrier × ExpCar X Y => p.2) (expIsFunc X Y) := by
  simp only [expIsFunc, subst_conj]
  exact le_conj (le_conj (le_conj (Λ_strictDom_f g) (Λ_strictCod_f g))
    (le_conj (Λ_congCond_f g) (Λ_singleCond_f g))) (Λ_totalCond_f g)

/-- The transpose is strict in the codomain (lands in `Y ^ X`). -/
def Λ_strict_cod (g : FunRel (prodPER Z X) Y) :
    ΛRel g ⊢ subst (fun p : Z.carrier × ExpCar X Y => (p.2, p.2)) (expObj X Y).rel := by
  simp only [expObj, subst_conj, ← subst_comp]
  exact le_conj (le_conj (Λ_isFunc g) (Λ_isFunc g)) (Λ_extEq_refl g)

/-- A functional relation respects `~` in its first (`Z`) argument:
`g((z,x),y) ∧ z~z' ⊢ g((z',x),y)`. -/
def g_transfer (g : FunRel (prodPER Z X) Y) :
    conj (subst (fun w : Z.carrier × Z.carrier × X.carrier × Y.carrier =>
            ((w.1, w.2.2.1), w.2.2.2)) g.rel)
         (subst (fun w : Z.carrier × Z.carrier × X.carrier × Y.carrier => (w.1, w.2.1)) Z.rel)
      ⊢ subst (fun w : Z.carrier × Z.carrier × X.carrier × Y.carrier =>
          ((w.2.1, w.2.2.1), w.2.2.2)) g.rel := by
  have hgc := subst_mono
    (fun w : Z.carrier × Z.carrier × X.carrier × Y.carrier =>
      ((w.1, w.2.2.1), (w.2.1, w.2.2.1), w.2.2.2, w.2.2.2)) g.cong
  simp only [prodPER, subst_conj, ← subst_comp] at hgc
  have hsd := subst_mono
    (fun w : Z.carrier × Z.carrier × X.carrier × Y.carrier => ((w.1, w.2.2.1), w.2.2.2))
    g.strict_dom
  simp only [prodPER, subst_conj, ← subst_comp] at hsd
  have hsc := subst_mono
    (fun w : Z.carrier × Z.carrier × X.carrier × Y.carrier => ((w.1, w.2.2.1), w.2.2.2))
    g.strict_cod
  erw [← subst_comp] at hsc
  refine le_trans (le_conj (le_conj (conj_le_left _ _)
    (le_conj (conj_le_right _ _) ?_)) ?_) hgc
  · exact le_trans (conj_le_left _ _) (le_trans hsd (conj_le_right _ _))
  · exact le_trans (conj_le_left _ _) hsc

/-- The transpose is single-valued (codes equal up to `≈`). -/
def Λ_single (g : FunRel (prodPER Z X) Y) :
    conj (subst (fun t : Z.carrier × ExpCar X Y × ExpCar X Y => (t.1, t.2.1)) (ΛRel g))
         (subst (fun t : Z.carrier × ExpCar X Y × ExpCar X Y => (t.1, t.2.2)) (ΛRel g))
      ⊢ subst (fun t : Z.carrier × ExpCar X Y × ExpCar X Y => (t.2.1, t.2.2)) (expObj X Y).rel := by
  simp only [expObj, subst_conj, ← subst_comp]
  refine le_conj (le_conj ?_ ?_) ?_
  · have h := subst_mono (fun t : Z.carrier × ExpCar X Y × ExpCar X Y => (t.1, t.2.1)) (Λ_isFunc g)
    erw [← subst_comp] at h
    exact le_trans (conj_le_left _ _) h
  · have h := subst_mono (fun t : Z.carrier × ExpCar X Y × ExpCar X Y => (t.1, t.2.2)) (Λ_isFunc g)
    erw [← subst_comp] at h
    exact le_trans (conj_le_right _ _) h
  · refine le_trans (all_adj_mp ?_)
      (all_subst_fst (fun t : Z.carrier × ExpCar X Y × ExpCar X Y => (t.2.1, t.2.2))
        (expExtBody X Y))
    have hbf := all_inst
      (Prod.fst : (Z.carrier × ExpCar X Y) × (X.carrier × Y.carrier) → Z.carrier × ExpCar X Y)
      (fun s : (Z.carrier × ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier =>
        ((s.1.1, s.1.2.1), s.2)) (ΛBody g)
    have hbf' := all_inst
      (Prod.fst : (Z.carrier × ExpCar X Y) × (X.carrier × Y.carrier) → Z.carrier × ExpCar X Y)
      (fun s : (Z.carrier × ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier =>
        ((s.1.1, s.1.2.2), s.2)) (ΛBody g)
    simp only [ΛRel, expExtBody, subst_conj, subst_impl, ← subst_comp]
    refine le_conj
      (le_trans (le_conj
          (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _)) (le_trans hbf
            (by simp only [ΛBody, subst_conj, subst_impl, ← subst_comp]; exact conj_le_left _ _)))
          (le_trans (le_trans (conj_le_right _ _) (conj_le_right _ _)) (le_trans hbf'
            (by simp only [ΛBody, subst_conj, subst_impl, ← subst_comp]; exact conj_le_right _ _))))
        (impl_trans _ _ _))
      (le_trans (le_conj
          (le_trans (le_trans (conj_le_right _ _) (conj_le_right _ _)) (le_trans hbf'
            (by simp only [ΛBody, subst_conj, subst_impl, ← subst_comp]; exact conj_le_left _ _)))
          (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _)) (le_trans hbf
            (by simp only [ΛBody, subst_conj, subst_impl, ← subst_comp]; exact conj_le_right _ _))))
        (impl_trans _ _ _))

/-- The transpose is relational (respects `~` in `Z` and `≈` in `Y^X`). -/
def Λ_cong (g : FunRel (prodPER Z X) Y) :
    conj (conj (subst (fun t : Z.carrier × Z.carrier × ExpCar X Y × ExpCar X Y => (t.1, t.2.2.1))
                  (ΛRel g))
               (subst (fun t : Z.carrier × Z.carrier × ExpCar X Y × ExpCar X Y => (t.1, t.2.1)) Z.rel))
         (subst (fun t : Z.carrier × Z.carrier × ExpCar X Y × ExpCar X Y => (t.2.2.1, t.2.2.2))
            (expObj X Y).rel)
      ⊢ subst (fun t : Z.carrier × Z.carrier × ExpCar X Y × ExpCar X Y => (t.2.1, t.2.2.2)) (ΛRel g) := by
  simp only [ΛRel, expObj, subst_conj, ← subst_comp]
  refine le_conj ?_ ?_
  · exact le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _))
      (Z.refl_right_at (K := Z.carrier × Z.carrier × ExpCar X Y × ExpCar X Y)
        (fun t => t.1) (fun t => t.2.1))
  · refine le_trans (all_adj_mp ?_)
      (all_subst_fst (fun t : Z.carrier × Z.carrier × ExpCar X Y × ExpCar X Y => (t.2.1, t.2.2.2))
        (ΛBody g))
    have hext := all_inst
      (Prod.fst : (ExpCar X Y × ExpCar X Y) × (X.carrier × Y.carrier) → ExpCar X Y × ExpCar X Y)
      (fun q : (Z.carrier × Z.carrier × ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier =>
        ((q.1.2.2.1, q.1.2.2.2), q.2)) (expExtBody X Y)
    have hΛf := all_inst
      (Prod.fst : (Z.carrier × ExpCar X Y) × (X.carrier × Y.carrier) → Z.carrier × ExpCar X Y)
      (fun q : (Z.carrier × Z.carrier × ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier =>
        ((q.1.1, q.1.2.2.1), q.2)) (ΛBody g)
    have htr := subst_mono
      (fun q : (Z.carrier × Z.carrier × ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier =>
        (q.1.1, q.1.2.1, q.2.1, q.2.2)) (g_transfer g)
    simp only [subst_conj, ← subst_comp] at htr
    have htr' := subst_mono
      (fun q : (Z.carrier × Z.carrier × ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier =>
        (q.1.2.1, q.1.1, q.2.1, q.2.2)) (g_transfer g)
    simp only [subst_conj, ← subst_comp] at htr'
    have hzz' := Z.symm_at
      (K := (Z.carrier × Z.carrier × ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier)
      (fun q => q.1.1) (fun q => q.1.2.1)
    simp only [ΛBody, subst_conj, subst_impl, ← subst_comp]
    refine le_conj ?_ ?_
    · -- impl f'(x,y) g(z',x,y), via f' → f → g(z,·) → g(z',·)
      refine curry ?_
      exact le_trans (le_conj
          (le_trans (le_conj
              (le_trans (le_trans (conj_le_left _ _)
                  (le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) (conj_le_right _ _)))
                (le_trans hΛf
                  (by simp only [ΛBody, subst_conj, subst_impl, ← subst_comp]; exact conj_le_left _ _)))
              (le_trans (le_conj
                  (le_trans (le_trans (conj_le_left _ _) (le_trans (conj_le_right _ _) (conj_le_right _ _)))
                    (le_trans hext
                      (by simp only [expExtBody, subst_conj, subst_impl, ← subst_comp]; exact conj_le_right _ _)))
                  (conj_le_right _ _))
                (impl_mp _ _)))
            (impl_mp _ _))
          (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (conj_le_right _ _))))
        htr
    · -- impl g(z',x,y) f'(x,y), via g(z',·) → g(z,·) → f → f'
      refine curry ?_
      exact le_trans (le_conj
          (le_trans (le_trans (conj_le_left _ _) (le_trans (conj_le_right _ _) (conj_le_right _ _)))
            (le_trans hext
              (by simp only [expExtBody, subst_conj, subst_impl, ← subst_comp]; exact conj_le_left _ _)))
          (le_trans (le_conj
              (le_trans (le_trans (conj_le_left _ _)
                  (le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) (conj_le_right _ _)))
                (le_trans hΛf
                  (by simp only [ΛBody, subst_conj, subst_impl, ← subst_comp]; exact conj_le_right _ _)))
              (le_trans (le_conj (conj_le_right _ _)
                  (le_trans (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (conj_le_right _ _)))
                    hzz'))
                htr'))
            (impl_mp _ _)))
        (impl_mp _ _)

/-- The transpose (currying) functional relation `Z ⟶ Y ^ X`. -/
def ΛFunRel (g : FunRel (prodPER Z X) Y) : FunRel Z (expObj X Y) where
  rel := ΛRel g
  strict_dom := Λ_strict_dom g
  strict_cod := Λ_strict_cod g
  cong := Λ_cong g
  single := Λ_single g
  total := Λ_total g

/-- The transpose as a `Hom`: `Hom.curry g : Z ⟶ Y ^ X`. -/
def Hom.curry (g : FunRel (prodPER Z X) Y) : Hom Z (expObj X Y) := Quotient.mk _ (ΛFunRel g)

/-! ### The exponential adjunction (universal property)

`uncurry h` is `eval ∘ (h × id)` at the relation level: `((z,x),y)` is related iff
`∃f. h(z,f) ∧ f(x,y)`.  Currying and uncurrying are mutually inverse. -/

/-- Uncurrying: `((z,x),y) ↦ ∃f. h(z,f) ∧ f(x,y)`. -/
def uncurryRel (h : FunRel Z (expObj X Y)) : P ((Z.carrier × X.carrier) × Y.carrier) :=
  ex (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => w.1)
    (conj (subst (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => (w.1.1.1, w.2)) h.rel)
          (subst (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y =>
            w.2 (w.1.1.2, w.1.2)) (@Tripos.generic P _)))

/-- β-rule, `⊢` direction: `uncurry (curry g) ⊢ g` (collapse through `f ↔ g(z,·)`). -/
def uncurry_curry_le (g : FunRel (prodPER Z X) Y) : uncurryRel (ΛFunRel g) ⊢ g.rel := by
  refine ex_adj_mpr ?_
  have hinst := all_inst
    (Prod.fst : (Z.carrier × ExpCar X Y) × (X.carrier × Y.carrier) → Z.carrier × ExpCar X Y)
    (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y =>
      ((w.1.1.1, w.2), (w.1.1.2, w.1.2))) (ΛBody g)
  simp only [ΛFunRel, ΛRel, subst_conj, ← subst_comp]
  refine le_trans (le_conj
      (le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _)) (le_trans hinst
        (by simp only [ΛBody, subst_conj, subst_impl, ← subst_comp]; exact conj_le_left _ _)))
      (conj_le_right _ _))
    (impl_mp _ _)

/-- β-rule, `⊇` direction: `g ⊢ uncurry (curry g)` (witness code `char (g(z,·))`). -/
def uncurry_curry_ge (g : FunRel (prodPER Z X) Y) : g.rel ⊢ uncurryRel (ΛFunRel g) := by
  have hu := subst_mono
    (fun p : (Z.carrier × X.carrier) × Y.carrier =>
      (p, fun q : X.carrier × Y.carrier => Tripos.char (Λcg g) (p.1.1, q)))
    (ex_unit (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => w.1)
      (conj (subst (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => (w.1.1.1, w.2))
              (ΛFunRel g).rel)
            (subst (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y =>
              w.2 (w.1.1.2, w.1.2)) (@Tripos.generic P _))))
  simp only [← subst_comp] at hu
  refine le_trans ?_ (le_trans hu (subst_id_le _))
  simp only [ΛFunRel, ΛRel, subst_conj, ← subst_comp]
  refine le_conj (le_conj ?_ ?_) ?_
  · -- E_Z(z)
    have h : g.rel ⊢ _ := g.strict_dom
    simp only [prodPER, subst_conj, ← subst_comp] at h
    exact le_trans h (conj_le_left _ _)
  · -- ΛExt(z, char) — identity ∀-biimplication
    refine le_trans (le_top _) (le_trans (all_adj_mp ?_)
      (all_subst_fst (fun p : (Z.carrier × X.carrier) × Y.carrier =>
        (p.1.1, fun q : X.carrier × Y.carrier => Tripos.char (Λcg g) (p.1.1, q))) (ΛBody g)))
    simp only [ΛBody, subst_top, subst_conj, subst_impl, ← subst_comp, Function.comp_def]
    rw [show (fun s : ((Z.carrier × X.carrier) × Y.carrier) × X.carrier × Y.carrier =>
            Tripos.char (Λcg g) (s.1.1.1, (s.2.1, s.2.2)))
          = (Tripos.char (Λcg g)) ∘ (fun s => (s.1.1.1, (s.2.1, s.2.2))) from rfl,
      subst_comp, subst_char, Λcg, ← subst_comp]
    exact le_conj (id_impl _) (id_impl _)
  · -- char (g(z,·)) (x,y) = g((z,x),y)
    simp only [Function.comp_def]
    rw [show (fun p : (Z.carrier × X.carrier) × Y.carrier =>
            Tripos.char (Λcg g) (p.1.1, (p.1.2, p.2)))
          = (Tripos.char (Λcg g)) ∘ (fun p => (p.1.1, (p.1.2, p.2))) from rfl,
      subst_comp, subst_char, Λcg, ← subst_comp]
    exact subst_id_ge _

/-- If `h : Z ⟶ Y^X` relates `z` to a code `f`, then `f` is a functional relation. -/
def h_isFunc (h : FunRel Z (expObj X Y)) :
    h.rel ⊢ subst (fun p : Z.carrier × ExpCar X Y => p.2) (expIsFunc X Y) := by
  have hsc := h.strict_cod
  simp only [expObj, subst_conj, ← subst_comp] at hsc
  exact le_trans hsc (le_trans (conj_le_left _ _) (conj_le_left _ _))

/-- `uncurry h` is strict in the domain. -/
def uncurry_strict_dom (h : FunRel Z (expObj X Y)) :
    uncurryRel h ⊢ subst (fun p : (Z.carrier × X.carrier) × Y.carrier => (p.1, p.1))
      (prodPER Z X).rel := by
  refine ex_adj_mpr ?_
  have hsd := subst_mono
    (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => (w.1.1.1, w.2)) h.strict_dom
  erw [← subst_comp] at hsd
  have hif := subst_mono
    (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => (w.1.1.1, w.2)) (h_isFunc h)
  erw [← subst_comp] at hif
  have hinst := all_inst
    (fun t : ExpCar X Y × X.carrier × Y.carrier => t.1)
    (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => (w.2, w.1.1.2, w.1.2))
    (impl (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => t.1 (t.2.1, t.2.2))
            (@Tripos.generic P _))
          (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => (t.2.1, t.2.1)) X.rel))
  simp only [subst_impl, ← subst_comp] at hinst
  simp only [prodPER, subst_conj, ← subst_comp]
  refine le_conj (le_trans (conj_le_left _ _) hsd) ?_
  refine le_trans (le_conj (le_trans (conj_le_left _ _) (le_trans (le_trans hif ?_) hinst))
    (conj_le_right _ _)) (impl_mp _ _)
  simp only [expIsFunc, subst_conj]
  exact le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (conj_le_left _ _))

/-- `uncurry h` is strict in the codomain. -/
def uncurry_strict_cod (h : FunRel Z (expObj X Y)) :
    uncurryRel h ⊢ subst (fun p : (Z.carrier × X.carrier) × Y.carrier => (p.2, p.2)) Y.rel := by
  refine ex_adj_mpr ?_
  erw [← subst_comp]
  have hif := subst_mono
    (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => (w.1.1.1, w.2)) (h_isFunc h)
  erw [← subst_comp] at hif
  have hinst := all_inst (fun t : ExpCar X Y × X.carrier × Y.carrier => t.1)
    (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => (w.2, w.1.1.2, w.1.2))
    (impl (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => t.1 (t.2.1, t.2.2))
            (@Tripos.generic P _))
          (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => (t.2.2, t.2.2)) Y.rel))
  simp only [subst_impl, ← subst_comp] at hinst
  refine le_trans (le_conj (le_trans (conj_le_left _ _) (le_trans (le_trans hif ?_) hinst))
    (conj_le_right _ _)) (impl_mp _ _)
  simp only [expIsFunc, subst_conj]
  exact le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (conj_le_right _ _))

/-- The product map `⟨h ∘ π₁, π₂⟩ : Z × X ⟶ Y^X × X`. -/
def prodMap (h : FunRel Z (expObj X Y)) : FunRel (prodPER Z X) (prodPER (expObj X Y) X) :=
  pairFunRel (compFunRel (proj1 Z X) h) (proj2 Z X)

/-- `uncurry h` as a single functional relation, `eval ∘ ⟨h ∘ π₁, π₂⟩`.  Being a
composite of functional relations it is automatically functional. -/
def uncurryFunRel (h : FunRel Z (expObj X Y)) : FunRel (prodPER Z X) Y :=
  compFunRel (prodMap h) (expEval X Y)

/-- The uncurrying (transpose) `Z ⟶ Y^X  ↦  Z × X ⟶ Y`, defined as
`eval ∘ ⟨φ ∘ π₁, π₂⟩`.  As a composite of morphisms it is automatically a
well-defined functional relation, so all five `FunRel` conditions come for free. -/
def Hom.uncurry {Z X Y : PER P} (φ : Hom Z (expObj X Y)) : Hom (prodPER Z X) Y :=
  Hom.comp (Hom.eval X Y)
    (Hom.pair (Hom.comp φ (Quotient.mk _ (proj1 Z X)))
              (Quotient.mk _ (proj2 Z X)))

/-- `Hom.uncurry` on a representative is the class of `uncurryFunRel`. -/
theorem Hom.uncurry_mk (h : FunRel Z (expObj X Y)) :
    Hom.uncurry (Quotient.mk _ h) = Quotient.mk _ (uncurryFunRel h) := rfl

/-- Connection (`⊇`): the simple `uncurryRel h` entails the composite
`(uncurry h).rel = eval ∘ ⟨h∘π₁, π₂⟩`.  Witness the intermediates with `z' = z`,
`x' = x`. -/
def connection_ge (h : FunRel Z (expObj X Y)) :
    uncurryRel h ⊢ (uncurryFunRel h).rel := by
  show uncurryRel h ⊢ compRel (prodMap h) (expEval X Y)
  refine ex_adj_mpr ?_
  -- abbreviate the body index `W = ((Z×X)×Y)×ExpCar`
  -- E_Z(z), E_exp(f), E_X(x) from the body `conj (h(z,f)) (f(x,y))`
  have hEZ : (conj (subst (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y =>
        (w.1.1.1, w.2)) h.rel)
      (subst (fun w => w.2 (w.1.1.2, w.1.2)) (@Tripos.generic P _)))
      ⊢ subst (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => (w.1.1.1, w.1.1.1))
          Z.rel := by
    refine le_trans (conj_le_left _ _) ?_
    have := subst_mono (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y =>
      (w.1.1.1, w.2)) h.strict_dom
    erw [← subst_comp] at this; exact this
  have hEexp : (conj (subst (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y =>
        (w.1.1.1, w.2)) h.rel)
      (subst (fun w => w.2 (w.1.1.2, w.1.2)) (@Tripos.generic P _)))
      ⊢ subst (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => (w.2, w.2))
          (expObj X Y).rel := by
    refine le_trans (conj_le_left _ _) ?_
    have := subst_mono (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y =>
      (w.1.1.1, w.2)) h.strict_cod
    erw [← subst_comp] at this; exact this
  have hEX : (conj (subst (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y =>
        (w.1.1.1, w.2)) h.rel)
      (subst (fun w => w.2 (w.1.1.2, w.1.2)) (@Tripos.generic P _)))
      ⊢ subst (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => (w.1.1.2, w.1.1.2))
          X.rel := by
    have hif := subst_mono (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y =>
      (w.1.1.1, w.2)) (h_isFunc h)
    erw [← subst_comp] at hif
    have hinst := all_inst (fun t : ExpCar X Y × X.carrier × Y.carrier => t.1)
      (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => (w.2, w.1.1.2, w.1.2))
      (impl (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => t.1 (t.2.1, t.2.2))
              (@Tripos.generic P _))
            (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => (t.2.1, t.2.1)) X.rel))
    simp only [subst_impl, ← subst_comp] at hinst
    refine le_trans (le_conj (le_trans (conj_le_left _ _) (le_trans (le_trans hif ?_) hinst))
      (conj_le_right _ _)) (impl_mp _ _)
    simp only [expIsFunc, subst_conj]
    exact le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (conj_le_left _ _))
  -- assemble: witness the composite's intermediate `(f, x)` and inner `z' = z`
  rw [show (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => w.1)
        = (fun d : (Z.carrier × X.carrier) × ((ExpCar X Y × X.carrier) × Y.carrier) =>
            (d.1, d.2.2))
          ∘ fun w => (w.1.1, ((w.2, w.1.1.2), w.1.2)) from rfl, subst_comp]
  refine le_trans ?_ (subst_mono
    (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y =>
      (w.1.1, ((w.2, w.1.1.2), w.1.2)))
    (ex_unit (fun d : (Z.carrier × X.carrier) × ((ExpCar X Y × X.carrier) × Y.carrier) =>
        (d.1, d.2.2))
      (conj (subst (fun d => (d.1, d.2.1)) (prodMap h).rel)
            (subst (fun d => (d.2.1, d.2.2)) (expEval X Y).rel))))
  simp only [prodMap, pairFunRel, prodPER, expObj, subst_conj, ← subst_comp, Function.comp_def]
  refine le_conj (le_conj ?A1 ?A2) ?B
  · -- `h ∘ π₁` at `((z,x), f)`, witnessing `z' = z`
    show _ ⊢ subst (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => (w.1.1, w.2))
      (compFunRel (proj1 Z X) h).rel
    simp only [compFunRel, compRel]
    rw [show (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => (w.1.1, w.2))
          = (fun e : (Z.carrier × X.carrier) × (Z.carrier × ExpCar X Y) => (e.1, e.2.2))
            ∘ fun w => (w.1.1, (w.1.1.1, w.2)) from rfl, subst_comp]
    refine le_trans ?_ (subst_mono
      (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => (w.1.1, (w.1.1.1, w.2)))
      (ex_unit (fun e : (Z.carrier × X.carrier) × (Z.carrier × ExpCar X Y) => (e.1, e.2.2))
        (conj (subst (fun e => (e.1, e.2.1)) (proj1 Z X).rel)
              (subst (fun e => (e.2.1, e.2.2)) h.rel))))
    simp only [proj1, prodPER, subst_conj, ← subst_comp, Function.comp_def]
    exact le_conj (le_conj hEZ hEX) (conj_le_left _ _)
  · -- `π₂` at `((z,x), x)`
    simp only [proj2, prodPER, subst_conj, ← subst_comp, Function.comp_def]
    exact le_conj hEZ hEX
  · -- `eval` at `((f,x), y)`
    simp only [expEval, expEvalRel, prodPER, expObj, subst_conj, ← subst_comp, Function.comp_def]
    have hE := hEexp
    simp only [expObj, subst_conj, ← subst_comp] at hE
    exact le_conj (le_conj hE hEX) (conj_le_right _ _)

/-- **β-rule (Hom level)**: `uncurry (curry g) = g`.  The exponential's universal
property as an equation of morphisms. -/
theorem Hom.uncurry_curry (g : FunRel (prodPER Z X) Y) :
    Hom.uncurry (Hom.curry g) = Quotient.mk _ g := by
  have hge : g.rel ⊢ (uncurryFunRel (ΛFunRel g)).rel :=
    le_trans (uncurry_curry_ge g) (connection_ge (ΛFunRel g))
  exact Quotient.sound ⟨⟨funrel_eq_of_le g (uncurryFunRel (ΛFunRel g)) hge⟩, ⟨hge⟩⟩

/-- `ΛRel` is monotone up to mutual entailment (its body is a bi-implication, so
`g.rel` occurs both co- and contravariantly). -/
def ΛRel_mono (g g' : FunRel (prodPER Z X) Y) (hge : g.rel ⊢ g'.rel) (hle : g'.rel ⊢ g.rel) :
    ΛRel g ⊢ ΛRel g' := by
  refine conj_mono (le_refl _) (all_mono _ ?_)
  refine conj_mono ?_ ?_
  · exact curry (le_trans (impl_mp _ _) (subst_mono _ hge))
  · exact curry (le_trans (conj_mono (le_refl _) (subst_mono _ hle)) (impl_mp _ _))

/-- Currying as a morphism `Z × X ⟶ Y  ↦  Z ⟶ Y^X`, lifted to the quotient. -/
def Hom.curry' {Z X Y : PER P} (φ : Hom (prodPER Z X) Y) : Hom Z (expObj X Y) := by
  refine Quotient.liftOn φ (fun g => Quotient.mk _ (ΛFunRel g)) ?_
  rintro g g' ⟨⟨e⟩, ⟨e'⟩⟩
  exact Quotient.sound ⟨⟨ΛRel_mono g g' e e'⟩, ⟨ΛRel_mono g' g e' e⟩⟩

/-- Composing with the first projection collapses: `(h ∘ π₁)((z,x), f) ⊢ h(z, f)`
(the intermediate `z'` is `≈ z`, closed by `h.cong`). -/
def comp_proj1_le (h : FunRel Z (expObj X Y)) :
    compRel (proj1 Z X) h
      ⊢ subst (fun p : (Z.carrier × X.carrier) × (expObj X Y).carrier => (p.1.1, p.2)) h.rel := by
  refine ex_adj_mpr ?_
  erw [← subst_comp]
  have hcong := subst_mono
    (fun e : (Z.carrier × X.carrier) × (Z.carrier × (expObj X Y).carrier) =>
      (e.2.1, e.1.1, e.2.2, e.2.2)) h.cong
  simp only [subst_conj, ← subst_comp] at hcong
  refine le_trans (le_conj (le_conj (conj_le_right _ _) ?_) ?_) hcong
  · refine le_trans (conj_le_left _ _) ?_
    simp only [proj1, subst_conj, ← subst_comp]
    exact le_trans (conj_le_left _ _)
      (Z.symm_at (K := (Z.carrier × X.carrier) × (Z.carrier × (expObj X Y).carrier))
        (fun e => e.1.1) (fun e => e.2.1))
  · refine le_trans (conj_le_right _ _) ?_
    have hsc := subst_mono (fun e : (Z.carrier × X.carrier) × (Z.carrier × (expObj X Y).carrier) =>
      (e.2.1, e.2.2)) h.strict_cod
    erw [← subst_comp] at hsc
    exact hsc

/-- Connection (`⊆`): the composite `(uncurry h).rel = eval ∘ ⟨h∘π₁, π₂⟩` entails the
simple `uncurryRel h` (collapse the intermediate `(f',x')` to `f' = h(z)`, `x' = x`). -/
def connection_le (h : FunRel Z (expObj X Y)) :
    (uncurryFunRel h).rel ⊢ uncurryRel h := by
  show compRel (prodMap h) (expEval X Y) ⊢ uncurryRel h
  refine ex_adj_mpr ?_
  have heq : subst (fun d : (prodPER Z X).carrier × ((prodPER (expObj X Y) X).carrier × Y.carrier) =>
        (d.1, d.2.2)) (uncurryRel h)
      = subst (fun d : (prodPER Z X).carrier × ((prodPER (expObj X Y) X).carrier × Y.carrier) =>
          ((d.1, d.2.2), d.2.1.1))
        (subst (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => w.1)
          (uncurryRel h)) := by
    rw [← subst_comp]; rfl
  rw [heq]
  refine le_trans ?_ (subst_mono _
    (ex_unit (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => w.1)
      (conj (subst (fun w => (w.1.1.1, w.2)) h.rel)
            (subst (fun w => w.2 (w.1.1.2, w.1.2)) (@Tripos.generic P _)))))
  simp only [prodMap, pairFunRel, prodPER, expObj, subst_conj, ← subst_comp, Function.comp_def]
  refine le_conj ?_ ?_
  · -- h(z, f') via `comp_proj1_le`
    refine le_trans (le_trans (conj_le_left _ _) (conj_le_left _ _)) ?_
    show subst (fun d : (Z.carrier × X.carrier) × ((ExpCar X Y × X.carrier) × Y.carrier) =>
      (d.1, d.2.1.1)) (compFunRel (proj1 Z X) h).rel ⊢ _
    have hp := subst_mono
      (fun d : (Z.carrier × X.carrier) × ((ExpCar X Y × X.carrier) × Y.carrier) => (d.1, d.2.1.1))
      (comp_proj1_le h)
    erw [← subst_comp] at hp
    exact hp
  · -- f'(x, y) via `expCongCond f'`
    have hcong := all_inst
      (fun s : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier => s.1)
      (fun d : (Z.carrier × X.carrier) × ((ExpCar X Y × X.carrier) × Y.carrier) =>
        (d.2.1.1, d.2.1.2, d.2.2, d.1.2, d.2.2))
      (impl (conj (conj
          (subst (fun s : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier =>
            s.1 (s.2.1, s.2.2.1)) (@Tripos.generic P _))
          (subst (fun s : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier =>
            (s.2.1, s.2.2.2.1)) X.rel))
          (subst (fun s : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier =>
            (s.2.2.1, s.2.2.2.2)) Y.rel))
        (subst (fun s : ExpCar X Y × X.carrier × Y.carrier × X.carrier × Y.carrier =>
          s.1 (s.2.2.2.1, s.2.2.2.2)) (@Tripos.generic P _)))
    simp only [subst_impl, subst_conj, ← subst_comp, Function.comp_def] at hcong
    have hsc := all_inst (fun t : ExpCar X Y × X.carrier × Y.carrier => t.1)
      (fun d : (Z.carrier × X.carrier) × ((ExpCar X Y × X.carrier) × Y.carrier) =>
        (d.2.1.1, d.2.1.2, d.2.2))
      (impl (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => t.1 (t.2.1, t.2.2))
              (@Tripos.generic P _))
            (subst (fun t : ExpCar X Y × X.carrier × Y.carrier => (t.2.2, t.2.2)) Y.rel))
    simp only [subst_impl, ← subst_comp, Function.comp_def] at hsc
    refine le_trans (le_conj (le_trans ?cg hcong) (le_conj (le_conj ?fxy ?xx) ?yy))
      (impl_mp
        (conj (conj
          (subst (fun d : (Z.carrier × X.carrier) × ((ExpCar X Y × X.carrier) × Y.carrier) =>
            d.2.1.1 (d.2.1.2, d.2.2)) (@Tripos.generic P _))
          (subst (fun d : (Z.carrier × X.carrier) × ((ExpCar X Y × X.carrier) × Y.carrier) =>
            (d.2.1.2, d.1.2)) X.rel))
          (subst (fun d : (Z.carrier × X.carrier) × ((ExpCar X Y × X.carrier) × Y.carrier) =>
            (d.2.2, d.2.2)) Y.rel))
        (subst (fun d : (Z.carrier × X.carrier) × ((ExpCar X Y × X.carrier) × Y.carrier) =>
          d.2.1.1 (d.1.2, d.2.2)) (@Tripos.generic P _)))
    · -- expCongCond f' from B's `E_exp(f')`
      refine le_trans (conj_le_right _ _) ?_
      simp only [expEval, expEvalRel, prodPER, expObj, expIsFunc, subst_conj, ← subst_comp,
        Function.comp_def]
      exact le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _)
        (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _)
          (le_trans (conj_le_right _ _) (conj_le_left _ _))))))
    · -- f'(x', y) from B
      refine le_trans (conj_le_right _ _) ?_
      simp only [expEval, expEvalRel, prodPER, expObj, subst_conj, ← subst_comp, Function.comp_def]
      exact conj_le_right _ _
    · -- X.rel(x', x) from π₂'s X.rel(x, x')
      refine le_trans (le_trans (conj_le_left _ _) (conj_le_right _ _)) ?_
      simp only [proj2, prodPER, subst_conj, ← subst_comp, Function.comp_def]
      exact le_trans (conj_le_right _ _)
        (X.symm_at (K := (Z.carrier × X.carrier) × ((ExpCar X Y × X.carrier) × Y.carrier))
          (fun d => d.1.2) (fun d => d.2.1.2))
    · -- Y.rel(y, y) from f'(x', y) via expStrictCod f'
      refine le_trans (le_conj (le_trans ?_ hsc) (le_trans (conj_le_right _ _) ?_))
        (impl_mp
          (subst (fun d : (Z.carrier × X.carrier) × ((ExpCar X Y × X.carrier) × Y.carrier) =>
            d.2.1.1 (d.2.1.2, d.2.2)) (@Tripos.generic P _))
          (subst (fun d : (Z.carrier × X.carrier) × ((ExpCar X Y × X.carrier) × Y.carrier) =>
            (d.2.2, d.2.2)) Y.rel))
      · -- expStrictCod f' from B's E_exp(f')
        refine le_trans (conj_le_right _ _) ?_
        simp only [expEval, expEvalRel, prodPER, expObj, expIsFunc, subst_conj, ← subst_comp,
          Function.comp_def]
        exact le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _)
          (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _) (le_trans (conj_le_left _ _)
            (conj_le_right _ _))))))
      · simp only [expEval, expEvalRel, prodPER, expObj, subst_conj, ← subst_comp, Function.comp_def]
        exact conj_le_right _ _

/-- **η-rule (Hom level)**: `curry' (uncurry h) = h`.  Together with `Hom.uncurry_curry`
this gives the adjunction bijection `Hom(Z × X, Y) ≅ Hom(Z, Y^X)`. -/
theorem Hom.curry_uncurry (h : FunRel Z (expObj X Y)) :
    Hom.curry' (Hom.uncurry (Quotient.mk _ h)) = Quotient.mk _ h := by
  rw [Hom.uncurry_mk]
  have hle : h.rel ⊢ ΛRel (uncurryFunRel h) := by
    refine le_conj h.strict_dom (all_adj_mp ?_)
    simp only [ΛBody]
    refine le_conj ?_ ?_
    · -- `f(x,y) → uncurry h` : witness the code `f`, then `connection_ge`
      refine Tripos.curry ?_
      refine le_trans ?_ (subst_mono
        (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier => ((q.1.1, q.2.1), q.2.2))
        (connection_ge h))
      have heq2 : subst (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier =>
            ((q.1.1, q.2.1), q.2.2)) (uncurryRel h)
          = subst (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier =>
              (((q.1.1, q.2.1), q.2.2), q.1.2))
            (subst (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => w.1)
              (uncurryRel h)) := by rw [← subst_comp]; rfl
      rw [heq2]
      refine le_trans ?_ (subst_mono
        (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier =>
          (((q.1.1, q.2.1), q.2.2), q.1.2))
        (ex_unit (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y => w.1)
          (conj (subst (fun w => (w.1.1.1, w.2)) h.rel)
                (subst (fun w => w.2 (w.1.1.2, w.1.2)) (@Tripos.generic P _)))))
      simp only [subst_conj, ← subst_comp]
      exact le_conj (conj_le_left _ _) (conj_le_right _ _)
    · -- `uncurry h → f(x,y)` : `connection_le`, then `h.single` gives `f ≈ f'`
      refine Tripos.curry ?_
      refine le_trans (conj_mono (le_refl _) (le_trans
        (subst_mono (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier =>
          ((q.1.1, q.2.1), q.2.2)) (connection_le h))
        (ex_subst_fst (fun q : (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier =>
          ((q.1.1, q.2.1), q.2.2))
          (conj (subst (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y =>
            (w.1.1.1, w.2)) h.rel)
                (subst (fun w : ((Z.carrier × X.carrier) × Y.carrier) × ExpCar X Y =>
                  w.2 (w.1.1.2, w.1.2)) (@Tripos.generic P _)))))) ?_
      refine le_trans (conj_comm _ _) (conj_ex_elim
        (Prod.fst : (((Z.carrier × ExpCar X Y) × X.carrier × Y.carrier) × ExpCar X Y) →
          (Z.carrier × ExpCar X Y) × X.carrier × Y.carrier) ?_)
      simp only [subst_conj, ← subst_comp, Function.comp_def]
      have hsingle := subst_mono
        (fun p : ((Z.carrier × ExpCar X Y) × X.carrier × Y.carrier) × ExpCar X Y =>
          (p.1.1.1, p.1.1.2, p.2)) h.single
      simp only [expObj, subst_conj, ← subst_comp] at hsingle
      have hext := all_inst
        (Prod.fst : (ExpCar X Y × ExpCar X Y) × X.carrier × Y.carrier → ExpCar X Y × ExpCar X Y)
        (fun p : ((Z.carrier × ExpCar X Y) × X.carrier × Y.carrier) × ExpCar X Y =>
          ((p.1.1.2, p.2), p.1.2.1, p.1.2.2)) (expExtBody X Y)
      simp only [expExtBody, subst_conj, subst_impl, ← subst_comp] at hext
      refine le_trans (le_conj ?_ (le_trans (conj_le_right _ _) (conj_le_right _ _)))
        (impl_mp
          (subst (fun p : ((Z.carrier × ExpCar X Y) × X.carrier × Y.carrier) × ExpCar X Y =>
            p.2 (p.1.2.1, p.1.2.2)) (@Tripos.generic P _))
          (subst (fun p : ((Z.carrier × ExpCar X Y) × X.carrier × Y.carrier) × ExpCar X Y =>
            p.1.1.2 (p.1.2.1, p.1.2.2)) (@Tripos.generic P _)))
      refine le_trans (le_conj (conj_le_left _ _) (le_trans (conj_le_right _ _) (conj_le_left _ _)))
        (le_trans hsingle (le_trans ?_ (le_trans hext (conj_le_right _ _))))
      exact conj_le_right _ _
  exact Quotient.sound ⟨⟨funrel_eq_of_le h (ΛFunRel (uncurryFunRel h)) hle⟩, ⟨hle⟩⟩

/-- β-rule for arbitrary morphisms (lifted from the representative version). -/
theorem Hom.uncurry_curry' {Z X Y : PER P} (φ : Hom (prodPER Z X) Y) :
    Hom.uncurry (Hom.curry' φ) = φ := by
  induction φ using Quotient.inductionOn with
  | _ g => exact Hom.uncurry_curry g

/-- η-rule for arbitrary morphisms (lifted from the representative version). -/
theorem Hom.curry'_uncurry {Z X Y : PER P} (ψ : Hom Z (expObj X Y)) :
    Hom.curry' (Hom.uncurry ψ) = ψ := by
  induction ψ using Quotient.inductionOn with
  | _ h => exact Hom.curry_uncurry h

end Tripos

end LeanExperiments.Realizability
