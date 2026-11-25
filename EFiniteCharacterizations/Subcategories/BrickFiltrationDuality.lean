module

public import EFiniteCharacterizations.Subcategories.BrickFiltrationEquivalences
public import EFiniteCharacterizations.Stability.OppositeAlgebra

/-! # Right approximations by modules filtered by one brick -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

universe u

namespace EFiniteCharacterizations

variable {R S : Type u} [Ring R] [Ring S] [IsNoetherianRing R] [IsNoetherianRing S]

theorem FilteredBy.mapAnti {B X : FGModuleCat.{u} R} (h : FilteredBy B X)
    (E : (FGModuleCat.{u} R)ᵒᵖ ≌ FGModuleCat.{u} S) :
    FilteredBy (E.functor.obj (op B)) (E.functor.obj (op X)) := by
  induction h with
  | zero hz =>
    exact .zero ((IsZero.iff_id_eq_zero _).2 (by
      rw [← E.functor.map_id, ← E.functor.map_zero]
      exact E.functor.congr_map (by simpa using congrArg Quiver.Hom.op ((IsZero.iff_id_eq_zero _).1 hz))))
  | cons row e _ ih =>
    let T := (ShortComplex.mk row.i row.p row.w).op.map E.functor
    have ht : T.ShortExact := row.shortExact.op.map_of_exact E.functor
    exact ih.extension ⟨T.f,T.g,T.zero,ht⟩
      (.cons (ExtensionSequence.idLeft _) (E.functor.mapIso e.symm.op) (.zero (isZero_zero _)))


theorem covariantlyFinite_filteredBy_of_dual {B : FGModuleCat.{u} R}
    (E : (FGModuleCat.{u} R)ᵒᵖ ≌ FGModuleCat.{u} S)
    (h : ContravariantlyFinite (FilteredBy (E.functor.obj (op B)))) :
    CovariantlyFinite (FilteredBy B) := by
  intro X
  obtain ⟨L,p,hL,hp⟩ := h (E.functor.obj (op X))
  let A := (E.inverse.obj L).unop
  let e := E.counitIso.app L
  let q : X ⟶ A := (E.functor.preimage (e.hom ≫ p)).unop
  have hA := hL.mapAnti E.symm.leftOp
  refine ⟨A,q,hA.of_iso ((E.unitIso.app (op B)).unop) (Iso.refl _),?_⟩
  intro Y hY f
  obtain ⟨g,hg⟩ := hp _ (hY.mapAnti E) (E.functor.map f.op)
  refine ⟨(E.functor.preimage (g ≫ e.inv)).unop,?_⟩
  apply Quiver.Hom.op_inj
  apply E.functor.map_injective
  simpa [q, Category.assoc] using hg

variable [IsArtinianRing R] (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
theorem isEFinite_iff_contravariantlyFinite_filteredBy :
    IsEFinite R ↔ ∀ B : FGModuleCat.{u} R, IsBrick B → ContravariantlyFinite (FilteredBy B) := by
  refine ⟨fun he B hb ↦ (functoriallyFinite_filteredBy_of_isEFinite k he B hb).2,fun h ↦ ?_⟩
  let : IsNoetherianRing Rᵐᵒᵖ := isNoetherian_of_tower k inferInstance
  let : IsArtinianRing Rᵐᵒᵖ := isArtinian_of_tower k inferInstance
  apply (isEFinite_iff_opposite k).2
  apply (isEFinite_iff_covariantlyFinite_filteredBy k).2
  intro B hb
  let E := Contragredient.reverseDualityEquivalence k R
  exact covariantlyFinite_filteredBy_of_dual E (h _ (hb.mapAnti E))

end EFiniteCharacterizations
