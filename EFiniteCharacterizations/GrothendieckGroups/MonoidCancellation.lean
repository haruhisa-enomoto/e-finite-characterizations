module

public import EFiniteCharacterizations.GrothendieckGroups.TorsionGrothendieckGroups
public import EFiniteCharacterizations.GrothendieckGroups.TorsionMonoidEmbedding
public import EFiniteCharacterizations.Stability.OppositeAlgebra

/-!
# Cancellation in Grothendieck monoids of torsion and torsion-free classes

Corollary 4.3 (`cor:monoid-cancellation`) of the manuscript:

* `isEFinite_iff_torsionMonoids_cancellative`: since the group completion `K₀(T)`
  embeds into `K₀(mod R)` (Proposition 4.2), the dimension-vector map
  `M(T) → K₀(mod R)` is injective if and only if `M(T)` is cancellative; hence `R`
  is E-finite if and only if every torsion class has a cancellative Grothendieck monoid.
* `isEFinite_iff_torsionFreeMonoids_cancellative`: contravariant `k`-duality exchanges
  torsion classes of `mod Rᵐᵒᵖ` with torsion-free classes of `mod R` and preserves
  Grothendieck monoids (`GrothendieckMonoid.mapAnti`), giving the same criterion for
  torsion-free classes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
universe u v
namespace EFiniteCharacterizations

namespace GrothendieckMonoid

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]

/-- An exact duality carries each inherited exact relation to the relation
with the two outer terms exchanged. -/
noncomputable def mapAnti (E : Cᵒᵖ ≌ D) (T : ObjectProperty C) (U : ObjectProperty D)
    (h : ∀ X, T X → U (E.functor.obj (op X))) : GrothendieckMonoid T →+ GrothendieckMonoid U :=
  lift T (fun X ↦ of U _ (h _ X.property))
    (fun _ hz ↦ of_isZero U _ _ (E.functor.map_isZero hz.op))
    (fun _ _ e ↦ of_iso U _ _ (E.functor.mapIso e.symm.op))
    (fun _ hs a b c ↦ (of_shortExact U _ (hs.op.map_of_exact E.functor)
      (h _ c) (h _ b) (h _ a)).trans (add_comm _ _))

@[simp] theorem mapAnti_of (E : Cᵒᵖ ≌ D) (T : ObjectProperty C) (U : ObjectProperty D)
    (h : ∀ X, T X → U (E.functor.obj (op X))) (X : C) (hx : T X) :
    mapAnti E T U h (of T X hx) = of U _ (h X hx) :=
  lift_of ..

private theorem cancel_of_dual (E : Cᵒᵖ ≌ D) (T : ObjectProperty C)
    [T.IsClosedUnderExtensions] [T.IsClosedUnderIsomorphisms] (h₀ : T 0)
    (U : ObjectProperty D) (h : ∀ X, T X → U (E.functor.obj (op X)))
    (h' : ∀ Y, U Y → T (E.inverse.obj Y).unop) [IsCancelAdd (GrothendieckMonoid U)] :
    IsCancelAdd (GrothendieckMonoid T) := by
  let f := mapAnti E T U h
  let g := mapAnti E.symm.leftOp U T h'
  have left : Function.LeftInverse g f := by
    intro x
    obtain ⟨X,hX,rfl⟩ := exists_representative T h₀ x
    change mapAnti E.symm.leftOp U T h' (mapAnti E T U h (of T X hX)) = _
    rw [mapAnti_of, mapAnti_of E.symm.leftOp U T h']
    exact of_iso T _ _ (E.unitIso.app (op X)).unop
  exact left.injective.isCancelAdd f f.map_add

end GrothendieckMonoid

variable {R : Type u} [Ring R] (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

include k in
/-- **Corollary 4.3 (torsion classes):** `R` is E-finite if and only if every torsion class in
`mod R` has a cancellative Grothendieck monoid. -/
theorem isEFinite_iff_torsionMonoids_cancellative :
    IsEFinite R ↔ ∀ T : ObjectProperty (FGModuleCat.{u} R), T.IsClosedUnderQuotients →
      T.IsClosedUnderExtensions → T 0 → IsCancelAdd (GrothendieckMonoid T) := by
  rw [isEFinite_iff_injective_torsionMonoid k]
  constructor
  · exact fun h T hq he hz ↦ (h T hq he hz).isCancelAdd _ (GrothendieckMonoid.dimensionMap T).map_add
  · intro h T hq he hz
    letI := h T hq he hz
    let incl := ExactClassGroup.inclusion T
    have hi := (intrinsicGroup_on_compositionSupport k T hz (.inl hq)).1
    have eqn := Algebra.GrothendieckAddGroup.lift.symm_apply_apply (GrothendieckMonoid.dimensionMap T)
    intro a b hab
    apply Algebra.GrothendieckAddGroup.of_injective
    apply hi
    exact (DFunLike.congr_fun eqn a).trans (hab.trans (DFunLike.congr_fun eqn b).symm)

private def dualClass {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (E : Cᵒᵖ ≌ D) (T : ObjectProperty C) : ObjectProperty D :=
  fun Y ↦ T (E.inverse.obj Y).unop

section
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (E : Cᵒᵖ ≌ D) (T : ObjectProperty C)

private instance [T.IsClosedUnderExtensions] : (dualClass E T).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hs a c := T.prop_X₂_of_shortExact (hs.map_of_exact E.inverse).unop c a

private instance [T.IsClosedUnderQuotients] : (dualClass E T).IsClosedUnderSubobjects where
  prop_of_mono f _ := T.prop_of_epi (E.inverse.map f).unop

private instance [T.IsClosedUnderSubobjects] : (dualClass E T).IsClosedUnderQuotients where
  prop_of_epi f _ := T.prop_of_mono (E.inverse.map f).unop

private theorem dualClass_zero [T.IsClosedUnderIsomorphisms] (h₀ : T 0) : dualClass E T 0 :=
  T.prop_of_iso ((E.inverse.map_isZero (isZero_zero D)).unop.isoZero.symm) h₀

private theorem cancel_transfer [T.IsClosedUnderExtensions] [T.IsClosedUnderIsomorphisms] (h₀ : T 0)
    [IsCancelAdd (GrothendieckMonoid (dualClass E T))] : IsCancelAdd (GrothendieckMonoid T) :=
  GrothendieckMonoid.cancel_of_dual E T h₀ (dualClass E T) (fun X hx ↦
    T.prop_of_iso (E.unitIso.app (op X)).unop.symm hx) (fun _ hy ↦ hy)
end

include k in
/-- **Corollary 4.3 (torsion-free classes):** `R` is E-finite if and only if every torsion-free
class in `mod R` has a cancellative Grothendieck monoid. -/
theorem isEFinite_iff_torsionFreeMonoids_cancellative :
    IsEFinite R ↔ ∀ T : ObjectProperty (FGModuleCat.{u} R), T.IsClosedUnderSubobjects →
      T.IsClosedUnderExtensions → T 0 → IsCancelAdd (GrothendieckMonoid T) := by
  letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  letI := IsArtinianRing.of_finite k Rᵐᵒᵖ
  rw [isEFinite_iff_opposite k, isEFinite_iff_torsionMonoids_cancellative k]
  constructor
  · intro H T _ _ hz
    let E := Contragredient.dualityEquivalence k R
    have := H (dualClass E T) inferInstance inferInstance (dualClass_zero E T hz)
    exact cancel_transfer E T hz
  · intro H T _ _ hz
    let E := Contragredient.reverseDualityEquivalence k R
    have := H (dualClass E T) inferInstance inferInstance (dualClass_zero E T hz)
    exact cancel_transfer E T hz

end EFiniteCharacterizations
