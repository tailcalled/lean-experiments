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

end Tripos

end LeanExperiments.Realizability
