import LeanExperiments.PCA.Abstraction

/-!
# Assemblies and realizability (over an abstract PCA)

The category of **assemblies** over a partial combinatory algebra `A`.  An
assembly is a set with a realizability relation `a ⊩ x` ("`a` realizes `x`") in
which every element merely has a realizer; a morphism is a function **tracked**
by an element of `A`.

## Extraction and propositional truncation

For *program extraction* the realizers must survive to runtime, so we do **not**
hide them behind `Prop`-valued `∃` (which Lean erases).  Instead:

* a realizer/tracker is produced as **data** — an element of `A` — using the
  name-preserving abstraction `Abstraction.abs` (hence this layer needs
  `[Abstraction A]`, not merely `[PCA A]`: the generic `s`/`k` bracket only
  yields a `Prop`-level `∃`);
* "there *merely* exists a realizer" is a **propositional truncation** `Squash`
  — a subsingleton *type*, so the category is unchanged (`Hom` is determined by
  its function) but the witness is *not* computationally erased.

The realizability relations themselves stay `Prop`: the extractable content is
the realizer *element*, and the output realizer is obtained by *running* the
tracker (the PCA's application), not by projecting a `∃`.

Everything is generic over `A`; nothing here mentions the λ-model.
-/

namespace LeanExperiments.Realizability

open LeanExperiments
open scoped LeanExperiments.Partial LeanExperiments.PartialApp

universe u v

variable {A : Type u} [PCA A]

/-! ### Assemblies -/

/-- An *assembly* over `A`: a carrier with a realizability relation in which
every element *merely* (but un-erasably) has a realizer. -/
structure Assembly (A : Type u) [PCA A] where
  /-- The underlying set. -/
  Carrier : Type v
  /-- `Realizes a x` means "`a` realizes `x`". -/
  Realizes : A → Carrier → Prop
  /-- Every element has a realizer (a truncated, but un-erased, witness). -/
  realized : ∀ x, Squash { a : A // Realizes a x }

namespace Assembly

@[inherit_doc] scoped notation:50 a " ⊩[" X "] " x => Assembly.Realizes X a x

/-- `r` *tracks* `f`: applying `r` to any realizer of `x` yields a realizer of
`f x`. -/
def Tracks (X Y : Assembly A) (r : A) (f : X.Carrier → Y.Carrier) : Prop :=
  ∀ (x : X.Carrier) (a : A), X.Realizes a x →
    ∃ b, b ∈ (Partial.pure r ⬝ Partial.pure a : Partial A) ∧ Y.Realizes b (f x)

end Assembly

/-- A morphism of assemblies: a function with a tracking element.  The tracker
is `Squash`-truncated, so `Hom` is determined by its function yet the tracker
survives extraction. -/
structure Hom (X Y : Assembly A) where
  /-- The underlying function. -/
  toFun : X.Carrier → Y.Carrier
  /-- A (truncated, un-erased) tracking element. -/
  tracked : Squash { r : A // Assembly.Tracks X Y r toFun }

namespace Hom

theorem ext {X Y : Assembly A} : ∀ {f g : Hom X Y}, f.toFun = g.toFun → f = g
  | ⟨_, sf⟩, ⟨_, sg⟩, h => by cases h; exact congrArg _ (Subsingleton.elim sf sg)

/-! ### Tracking elements for identity and composition (as data) -/

section
variable [Abstraction A]

/-- The identity realizer (an element, hence extractable). -/
def idElem : A := Abstraction.abs "x" (Expr.var "x")

theorem idElem_spec (a : A) :
    (Partial.pure (idElem : A) ⬝ Partial.pure a : Partial A) = Partial.pure a := by
  have h := Abstraction.abs_spec (A := A) "x" (Expr.var "x")
    (by simp [Expr.closed1, Expr.fvE]) a (fun _ => PCA.k)
  simpa [Expr.denote_var, Expr.update_same] using h

/-- The realizer for `a ↦ p ⬝ (q ⬝ a)` (an element, hence extractable). -/
def compElem (p q : A) : A :=
  Abstraction.abs "x" (Expr.app (Expr.const p) (Expr.app (Expr.const q) (Expr.var "x")))

theorem compElem_spec (p q a : A) :
    (Partial.pure (compElem p q) ⬝ Partial.pure a : Partial A) =
      Partial.pure p ⬝ (Partial.pure q ⬝ Partial.pure a) := by
  have h := Abstraction.abs_spec (A := A) "x"
    (Expr.app (Expr.const p) (Expr.app (Expr.const q) (Expr.var "x")))
    (by simp [Expr.closed1, Expr.fvE]) a (fun _ => PCA.k)
  simpa [Expr.denote_app, Expr.denote_const, Expr.denote_var, Expr.update_same] using h

/-- The identity morphism, tracked by `idElem`. -/
def id (X : Assembly A) : Hom X X where
  toFun := _root_.id
  tracked := Squash.mk ⟨idElem, fun x a ha =>
    ⟨a, by rw [idElem_spec a]; exact Partial.mem_pure.mpr rfl, ha⟩⟩

/-- Composition of morphisms, tracked by `compElem`. -/
def comp {X Y Z : Assembly A} (g : Hom Y Z) (f : Hom X Y) : Hom X Z where
  toFun := g.toFun ∘ f.toFun
  tracked := Squash.lift f.tracked fun rf => Squash.lift g.tracked fun rg =>
    Squash.mk ⟨compElem rg.1 rf.1, fun x a ha => by
      obtain ⟨b, hb, hb'⟩ := rf.2 x a ha
      obtain ⟨c, hc, hc'⟩ := rg.2 (f.toFun x) b hb'
      refine ⟨c, ?_, hc'⟩
      rw [compElem_spec rg.1 rf.1 a, PartialApp.mem_applyP]
      exact ⟨rg.1, b, Partial.mem_pure.mpr rfl, hb, PartialApp.mem_pure_app.mp hc⟩⟩

/-! ### Category laws -/

theorem id_comp {X Y : Assembly A} (f : Hom X Y) : (id Y).comp f = f := ext rfl

theorem comp_id {X Y : Assembly A} (f : Hom X Y) : f.comp (id X) = f := ext rfl

theorem comp_assoc {X Y Z W : Assembly A} (h : Hom Z W) (g : Hom Y Z) (f : Hom X Y) :
    (h.comp g).comp f = h.comp (g.comp f) := ext rfl

end

end Hom

end LeanExperiments.Realizability
