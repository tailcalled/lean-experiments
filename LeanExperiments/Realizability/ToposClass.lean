import LeanExperiments.Realizability.Topos

/-!
# Abstract elementary topos structure

This file abstracts the categorical structure built concretely in `Topos.lean`
into typeclasses (`Category`, `HasTerminal`, `HasBinaryProducts`,
`CartesianClosed`, `HasSubobjectClassifier`, and `Topos`), and then packages the
realizability construction as instances of these classes.

Everything is computable and `Classical`/`sorry`-free: hom-*types* are honest
`Type`s, the laws are propositional equalities, and the classifier's universal
property is stated with the (`Prop`-valued, choice-free) `∃!`.

The architecture deliberately keeps `Category` abstract so that later work — the
fundamental theorem of topos theory (slices of a topos are topoi) — can be stated
and proved over an arbitrary `[Topos Obj]`.
-/

namespace LeanExperiments.CategoryTheory

universe uo uh u v

/-- A category: objects, hom-types, identities, composition and the three laws. -/
class Category (Obj : Type uo) where
  /-- Morphisms from `X` to `Y`. -/
  Hom : Obj → Obj → Type uh
  /-- The identity morphism. -/
  id : (X : Obj) → Hom X X
  /-- Composition `g ∘ f`. -/
  comp : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id Y) f = f
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id X) = f
  assoc : ∀ {X Y Z W : Obj} (h : Hom Z W) (g : Hom Y Z) (f : Hom X Y),
    comp (comp h g) f = comp h (comp g f)

namespace Category

/-- Diagrammatic-free composition notation `g ⊚ f = g ∘ f`. -/
scoped infixr:80 " ⊚ " => Category.comp

end Category

open Category

/-- A terminal object: a unique morphism into it from every object. -/
class HasTerminal (Obj : Type uo) [Category Obj] where
  /-- The terminal object `⊤`. -/
  term : Obj
  /-- The unique morphism `X ⟶ ⊤`. -/
  toTerm : (X : Obj) → Hom X term
  toTerm_unique : ∀ {X : Obj} (f : Hom X term), f = toTerm X

/-- Binary products: a product object with projections and a universal pairing. -/
class HasBinaryProducts (Obj : Type uo) [Category Obj] where
  /-- The product object `X × Y`. -/
  prod : Obj → Obj → Obj
  /-- First projection `X × Y ⟶ X`. -/
  fst : (X Y : Obj) → Hom (prod X Y) X
  /-- Second projection `X × Y ⟶ Y`. -/
  snd : (X Y : Obj) → Hom (prod X Y) Y
  /-- The pairing `⟨f, g⟩ : Z ⟶ X × Y`. -/
  lift : {Z X Y : Obj} → Hom Z X → Hom Z Y → Hom Z (prod X Y)
  fst_lift : ∀ {Z X Y : Obj} (f : Hom Z X) (g : Hom Z Y), comp (fst X Y) (lift f g) = f
  snd_lift : ∀ {Z X Y : Obj} (f : Hom Z X) (g : Hom Z Y), comp (snd X Y) (lift f g) = g
  lift_proj : ∀ {Z X Y : Obj} (h : Hom Z (prod X Y)),
    lift (comp (fst X Y) h) (comp (snd X Y) h) = h

open HasBinaryProducts

/-- A cartesian-closed category: an exponential object right adjoint to `· × X`,
presented by an evaluation map and a currying operation that are mutually inverse
(β- and η-rules).  `uncurry` is the derived `eval ∘ ⟨h ∘ π₁, π₂⟩`. -/
class CartesianClosed (Obj : Type uo) [Category Obj] [HasBinaryProducts Obj] where
  /-- The exponential object `Y ^ X` (exponent `X`, base `Y`). -/
  exp : Obj → Obj → Obj
  /-- Evaluation `Y^X × X ⟶ Y`. -/
  eval : (X Y : Obj) → Hom (prod (exp X Y) X) Y
  /-- Currying / transpose `(Z × X ⟶ Y) → (Z ⟶ Y^X)`. -/
  curry : {Z X Y : Obj} → Hom (prod Z X) Y → Hom Z (exp X Y)
  /-- β-rule: `eval ∘ ⟨curry φ ∘ π₁, π₂⟩ = φ`. -/
  eval_curry : ∀ {Z X Y : Obj} (φ : Hom (prod Z X) Y),
    comp (eval X Y) (lift (comp (curry φ) (fst Z X)) (snd Z X)) = φ
  /-- η-rule: currying the uncurrying recovers the morphism. -/
  curry_eval : ∀ {Z X Y : Obj} (ψ : Hom Z (exp X Y)),
    curry (comp (eval X Y) (lift (comp ψ (fst Z X)) (snd Z X))) = ψ

/-- A morphism is monic when it is left-cancellable. -/
def Mono {Obj : Type uo} [Category Obj] {X Y : Obj} (m : Hom X Y) : Prop :=
  ∀ {Z : Obj} (g h : Hom Z X), comp m g = comp m h → g = h

/-- The diagonal `Δ : C ⟶ C × C`. -/
def diagonal {Obj : Type uo} [Category Obj] [HasBinaryProducts Obj] (C : Obj) :
    Hom C (HasBinaryProducts.prod C C) :=
  HasBinaryProducts.lift (Category.id C) (Category.id C)

/-- The diagonal is a (split) mono. -/
theorem diagonal_mono {Obj : Type uo} [Category Obj] [HasBinaryProducts Obj] (C : Obj) :
    Mono (diagonal C) := by
  intro Z g h hgh
  have key : comp (HasBinaryProducts.fst C C) (comp (diagonal C) g)
      = comp (HasBinaryProducts.fst C C) (comp (diagonal C) h) := by rw [hgh]
  rw [← assoc, ← assoc,
    show comp (HasBinaryProducts.fst C C) (diagonal C) = Category.id C from
      HasBinaryProducts.fst_lift _ _,
    Category.id_comp, Category.id_comp] at key
  exact key

/-- Composition distributes over pairing: `⟨f, h⟩ ∘ v = ⟨f ∘ v, h ∘ v⟩`. -/
theorem comp_lift {Obj : Type uo} [Category Obj] [HasBinaryProducts Obj] {W Z X Y : Obj}
    (v : Hom W Z) (f : Hom Z X) (h : Hom Z Y) :
    comp (HasBinaryProducts.lift f h) v
      = HasBinaryProducts.lift (comp f v) (comp h v) := by
  rw [← HasBinaryProducts.lift_proj (comp (HasBinaryProducts.lift f h) v), ← assoc, ← assoc,
    HasBinaryProducts.fst_lift, HasBinaryProducts.snd_lift]

/-- `Δ_C ∘ v = ⟨v, v⟩`. -/
theorem comp_diagonal {Obj : Type uo} [Category Obj] [HasBinaryProducts Obj] {W C : Obj}
    (v : Hom W C) : comp (diagonal C) v = HasBinaryProducts.lift v v := by
  rw [diagonal, comp_lift, Category.id_comp]

/-- The square
```
  Pb --p₂--> B
  |          |
  p₁         g
  v          v
  A ---f---> C
```
is a pullback: it commutes and is universal. -/
structure IsPullback {Obj : Type uo} [Category Obj] {Pb A B C : Obj}
    (p₁ : Hom Pb A) (p₂ : Hom Pb B) (f : Hom A C) (g : Hom B C) : Prop where
  comm : comp f p₁ = comp g p₂
  universal : ∀ {W : Obj} (a : Hom W A) (b : Hom W B), comp f a = comp g b →
    ∃ u : Hom W Pb, comp p₁ u = a ∧ comp p₂ u = b ∧
      ∀ u' : Hom W Pb, comp p₁ u' = a → comp p₂ u' = b → u' = u

/-- A subobject classifier: a generic monomorphism `truth : ⊤ ⟶ Ω` such that every
monomorphism is, uniquely, a pullback of it. -/
class HasSubobjectClassifier (Obj : Type uo) [Category Obj] [HasTerminal Obj] where
  /-- The object of truth values `Ω`. -/
  Omega : Obj
  /-- The generic subobject `truth : ⊤ ⟶ Ω`. -/
  truth : Hom (HasTerminal.term) Omega
  /-- The classifying map of a mono. -/
  char : {S X : Obj} → (m : Hom S X) → Mono m → Hom X Omega
  /-- The classifying square is a pullback. -/
  char_isPullback : ∀ {S X : Obj} (m : Hom S X) (hm : Mono m),
    IsPullback m (HasTerminal.toTerm S) (char m hm) truth
  /-- The classifying map is the unique one whose square is a pullback. -/
  char_unique : ∀ {S X : Obj} (m : Hom S X) (hm : Mono m) (χ : Hom X Omega),
    IsPullback m (HasTerminal.toTerm S) χ truth → χ = char m hm
  /-- **Comprehension / representability**: every `χ : X ⟶ Ω` *is* the classifier of an
  actual subobject — the pullback of `truth` along `χ` exists.  Propositionally
  truncated (`Squash`) rather than erased: the object `E` and inclusion `i` survive as
  subsingleton-`Type` data, while the pullback property is the `Prop` part.  This is the
  half of "subobject classifier" that, with finite products, yields all finite limits. -/
  comprehension : ∀ {X : Obj} (χ : Hom X Omega),
    Squash (Σ E : Obj, { i : Hom E X // IsPullback i (HasTerminal.toTerm E) χ truth })

/-- An elementary topos: a category equipped with a terminal object, binary
products, exponentials, and a subobject classifier. -/
class Topos (Obj : Type uo) [Category Obj] where
  [hasTerminal : HasTerminal Obj]
  [hasBinaryProducts : HasBinaryProducts Obj]
  [cartesianClosed : CartesianClosed Obj]
  [hasSubobjectClassifier : HasSubobjectClassifier Obj]

attribute [instance] Topos.hasTerminal Topos.hasBinaryProducts Topos.cartesianClosed
  Topos.hasSubobjectClassifier

/-- **A topos has pullbacks** (propositionally truncated).  The pullback of `f, g` is
the comprehension of `char Δ_C ∘ ⟨f∘π₁, g∘π₂⟩ : A × B ⟶ Ω`. -/
def hasPullback {Obj : Type uo} [Category Obj] [HasTerminal Obj] [HasBinaryProducts Obj]
    [HasSubobjectClassifier Obj] {A B C : Obj} (f : Hom A C) (g : Hom B C) :
    Squash (Σ Pb : Obj, Σ' (p₁ : Hom Pb A) (p₂ : Hom Pb B), IsPullback p₁ p₂ f g) :=
  Squash.lift
    (HasSubobjectClassifier.comprehension
      (comp (HasSubobjectClassifier.char (diagonal C) (diagonal_mono C))
        (HasBinaryProducts.lift (comp f (HasBinaryProducts.fst A B))
          (comp g (HasBinaryProducts.snd A B)))))
    (fun ⟨E, i, hi⟩ => Squash.mk
      ⟨E, comp (HasBinaryProducts.fst A B) i, comp (HasBinaryProducts.snd A B) i,
        by -- commutativity
          have hc := hi.comm
          rw [assoc, comp_lift, assoc, assoc] at hc
          obtain ⟨v, hv, -, -⟩ := (HasSubobjectClassifier.char_isPullback (diagonal C)
            (diagonal_mono C)).universal _ (HasTerminal.toTerm E) hc
          rw [comp_diagonal] at hv
          have e1 := congrArg (comp (HasBinaryProducts.fst C C)) hv
          have e2 := congrArg (comp (HasBinaryProducts.snd C C)) hv
          rw [HasBinaryProducts.fst_lift, HasBinaryProducts.fst_lift] at e1
          rw [HasBinaryProducts.snd_lift, HasBinaryProducts.snd_lift] at e2
          rw [← e1, ← e2],
        by -- universality
          intro W a b hab
          have hcone : comp (comp (HasSubobjectClassifier.char (diagonal C) (diagonal_mono C))
                (HasBinaryProducts.lift (comp f (HasBinaryProducts.fst A B))
                  (comp g (HasBinaryProducts.snd A B)))) (HasBinaryProducts.lift a b)
              = comp HasSubobjectClassifier.truth (HasTerminal.toTerm W) := by
            rw [assoc, comp_lift, assoc, assoc, HasBinaryProducts.fst_lift,
              HasBinaryProducts.snd_lift, hab, ← comp_diagonal, ← assoc,
              (HasSubobjectClassifier.char_isPullback (diagonal C) (diagonal_mono C)).comm,
              assoc, HasTerminal.toTerm_unique (comp (HasTerminal.toTerm C) (comp g b))]
          obtain ⟨u, hu, -, huniq⟩ := hi.universal (HasBinaryProducts.lift a b)
            (HasTerminal.toTerm W) hcone
          refine ⟨u, ?_, ?_, ?_⟩
          · rw [assoc, hu, HasBinaryProducts.fst_lift]
          · rw [assoc, hu, HasBinaryProducts.snd_lift]
          · intro u' h1 h2
            refine huniq u' ?_ (HasTerminal.toTerm_unique _)
            rw [← HasBinaryProducts.lift_proj (comp i u'), ← assoc, ← assoc, h1, h2]⟩)

end LeanExperiments.CategoryTheory

namespace LeanExperiments.Realizability.Tripos

open LeanExperiments.CategoryTheory

variable {P : Type u → Type v} [Tripos P]

/-- The realizability category of PERs and functional relations. -/
instance instCategory : Category (PER P) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

/-- It has a terminal object. -/
instance instHasTerminal : HasTerminal (PER P) where
  term := terminal
  toTerm := terminalHom
  toTerm_unique := terminalHom_unique

/-- It has binary products. -/
instance instHasBinaryProducts : HasBinaryProducts (PER P) where
  prod := prodPER
  fst := Hom.fst
  snd := Hom.snd
  lift := Hom.pair
  fst_lift := Hom.fst_comp_pair
  snd_lift := Hom.snd_comp_pair
  lift_proj := Hom.pair_fst_snd

/-- It is cartesian closed. -/
instance instCartesianClosed : CartesianClosed (PER P) where
  exp := expObj
  eval := Hom.eval
  curry := Hom.curry'
  eval_curry := Hom.uncurry_curry'
  curry_eval := Hom.curry'_uncurry

/-- The classifying square of a mono is a pullback. -/
theorem charMono_isPullback {S X : PER P} (m : Hom S X) (hm : @Mono (PER P) instCategory S X m) :
    @IsPullback (PER P) instCategory S X (terminal : PER P) (omega : PER P)
      m (terminalHom S) (Hom.charMono m) Hom.truth := by
  refine ⟨charMono_comm m, ?_⟩
  intro W a b _hcomm
  obtain ⟨A, rfl⟩ := Quotient.exists_rep a
  obtain ⟨M, rfl⟩ := Quotient.exists_rep m
  have hb : b = terminalHom W := terminalHom_unique b
  subst hb
  have hcomm' : (Quotient.mk (homSetoid W (omega : PER P))
        (compFunRel A (charFunRel (imageStrictPred M)))
      : Hom W (omega : PER P))
      = Quotient.mk _ (compFunRel (terminalFunRel W) truthFunRel) := _hcomm
  obtain ⟨hcone⟩ := (Quotient.exact hcomm').1
  obtain ⟨e⟩ := mono_injective M hm
  refine ⟨Quotient.mk _ (uFunRel A M (cone_to_hfac A M hcone) e), ?_, ?_, ?_⟩
  · exact m_comp_u A M (cone_to_hfac A M hcone) e
  · exact terminalHom_unique _
  · intro u' h1 _
    exact hm u' _ (h1.trans (m_comp_u A M (cone_to_hfac A M hcone) e).symm)

/-- Uniqueness of the classifying map. -/
theorem charMono_unique {S X : PER P} (m : Hom S X)
    (χ : Hom X (omega : PER P))
    (h : @IsPullback (PER P) instCategory S X (terminal : PER P) (omega : PER P)
      m (terminalHom S) χ Hom.truth) :
    χ = Hom.charMono m := by
  obtain ⟨C, rfl⟩ := Quotient.exists_rep χ
  obtain ⟨M, rfl⟩ := Quotient.exists_rep m
  -- `comm` realizer (the goal is a `Prop`, so we may eliminate `Nonempty`).
  have hcc : (Quotient.mk (homSetoid S (omega : PER P)) (compFunRel M C) : Hom S (omega : PER P))
      = Quotient.mk _ (compFunRel (terminalFunRel S) truthFunRel) := h.comm
  obtain ⟨hcomm⟩ := (Quotient.exact hcc).1
  -- The lift of `{χ} ↪ X` through `m`, from the universal property.
  have cone : Hom.comp (Quotient.mk _ C) (Quotient.mk _ (subIncl (subobjOfFunRel C)))
      = Hom.comp Hom.truth (terminalHom (subPER (subobjOfFunRel C))) := by
    rw [← Hom.char_subobjOfFunRel C]
    exact charSubIncl_comm (subobjOfFunRel C)
  obtain ⟨u, hu, _, _⟩ := h.universal (Quotient.mk _ (subIncl (subobjOfFunRel C)))
    (terminalHom (subPER (subobjOfFunRel C))) cone
  obtain ⟨U, rfl⟩ := Quotient.exists_rep u
  have huc : (Quotient.mk (homSetoid (subPER (subobjOfFunRel C)) X) (compFunRel U M)
      : Hom (subPER (subobjOfFunRel C)) X)
      = Quotient.mk _ (subIncl (subobjOfFunRel C)) := hu
  obtain ⟨hlift⟩ := (Quotient.exact huc).2
  have himg : (subIncl (subobjOfFunRel C)).rel
      ⊢ subst (Prod.snd : X.carrier × X.carrier → X.carrier) (imageStrictPred M).pred :=
    le_trans hlift (compRel_to_img U M)
  have himg' : conj (subst (fun p : X.carrier × Prop' P => p.1) (subobjOfFunRel C).pred)
        (subst (fun p : X.carrier × Prop' P => (p.1, p.1)) X.rel)
      ⊢ subst (fun p : X.carrier × Prop' P => p.1) (imageStrictPred M).pred := by
    have hh := subst_mono
      (fun p : X.carrier × Prop' P => ((p.1, p.1) : X.carrier × X.carrier)) himg
    simp only [subIncl] at hh
    erw [subst_conj, ← subst_comp, ← subst_comp] at hh
    exact hh
  -- `half2`: if `χ(x)` holds then `x ∈ im M`.
  have half2 : conj C.rel (subst (Prod.snd : X.carrier × Prop' P → Prop' P) (@Tripos.generic P _))
      ⊢ subst (Prod.fst : X.carrier × Prop' P → X.carrier) (imageStrictPred M).pred :=
    le_trans (le_conj
      (ex_unit (Prod.fst : X.carrier × Prop' P → X.carrier)
        (conj C.rel (subst (Prod.snd : X.carrier × Prop' P → Prop' P) (@Tripos.generic P _))))
      (le_trans (conj_le_left _ _) C.strict_dom)) himg'
  refine Quotient.sound ⟨⟨?_⟩, ⟨funrel_eq_of_le C (charFunRel (imageStrictPred M)) ?_⟩⟩ <;>
    exact le_conj C.strict_dom
      (le_conj (Tripos.curry (charUnique_half1 M C hcomm)) (Tripos.curry half2))

/-- A relationally-injective functional relation is a categorical mono. -/
theorem funrel_mono {S X : PER P} (m : FunRel S X)
    (inj : conj (subst (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.2)) m.rel)
                (subst (fun p : S.carrier × S.carrier × X.carrier => (p.2.1, p.2.2)) m.rel)
             ⊢ subst (fun p : S.carrier × S.carrier × X.carrier => (p.1, p.2.1)) S.rel) :
    @Mono (PER P) instCategory S X (Quotient.mk _ m) := by
  intro Z g h hgh
  obtain ⟨G, rfl⟩ := Quotient.exists_rep g
  obtain ⟨H, rfl⟩ := Quotient.exists_rep h
  have hgh' : (Quotient.mk (homSetoid Z X) (compFunRel G m) : Hom Z X)
      = Quotient.mk _ (compFunRel H m) := hgh
  obtain ⟨hfwd⟩ := (Quotient.exact hgh').1
  exact Quotient.sound ⟨⟨monoKey m G H inj hfwd⟩, ⟨funrel_eq_of_le G H (monoKey m G H inj hfwd)⟩⟩

/-- The realizability category has a subobject classifier. -/
instance instHasSubobjectClassifier : HasSubobjectClassifier (PER P) where
  Omega := omega
  truth := Hom.truth
  char := fun m _ => Hom.charMono m
  char_isPullback := fun m hm => charMono_isPullback m hm
  char_unique := fun m _ χ hpb => charMono_unique m χ hpb
  comprehension := fun {X} χ => by
    refine Quotient.recOnSubsingleton χ (fun C => ?_)
    exact Squash.mk ⟨subPER (subobjOfFunRel C), Quotient.mk _ (subIncl (subobjOfFunRel C)),
      charMono_subIncl C ▸ charMono_isPullback (Quotient.mk _ (subIncl (subobjOfFunRel C)))
        (funrel_mono (subIncl (subobjOfFunRel C)) (subIncl_inj (subobjOfFunRel C)))⟩

/-- **The realizability category `PER P` is an elementary topos** — computable,
`Classical`-free, and `sorry`-free. -/
instance instTopos : Topos (PER P) := {}

end LeanExperiments.Realizability.Tripos
