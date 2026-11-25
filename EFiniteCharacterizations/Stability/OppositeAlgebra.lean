module

public import EFiniteCharacterizations.Modules.Duality.ContragredientDuality
public import EFiniteCharacterizations.Characterizations.HomCharacterizations

/-! # E-finiteness of the opposite algebra -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace EFiniteCharacterizations

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]

/-- The Grothendieck class of the image under an exact duality is additive. -/
noncomputable def GrothendieckGroup.mapAnti (E : Cᵒᵖ ≌ D) :
    GrothendieckGroup C →+ GrothendieckGroup D :=
  lift (fun X ↦ of (E.functor.obj (op X))) fun S h ↦ by
    rw [add_comm]
    exact of_shortExact (S.op.map E.functor) (h.op.map_of_exact E.functor)

theorem IsBrick.mapAnti {X : C} (h : IsBrick X) (E : Cᵒᵖ ≌ D) :
    IsBrick (E.functor.obj (op X)) := by
  constructor
  · intro hz
    apply h.1
    apply (IsZero.iff_id_eq_zero _).2
    apply Quiver.Hom.op_inj
    apply E.functor.map_injective
    exact hz.eq_of_src _ _
  · intro f hf
    let g := E.functor.preimage f
    have hn : g.unop ≠ 0 := by
      intro hz
      have hg : g = 0 := by simpa using congrArg Quiver.Hom.op hz
      exact hf (by rw [← E.functor.map_preimage f, ← show g = E.functor.preimage f from rfl, hg, E.functor.map_zero])
    have : IsIso g.unop := h.2 _ hn
    have : IsIso g := (isIso_unop_iff g).1 ‹_›
    rw [← E.functor.map_preimage f]
    exact E.functor.map_isIso g

theorem EqualClassBrickHom.of_antiEquivalence (E : Cᵒᵖ ≌ D) (h : EqualClassBrickHom D) :
    EqualClassBrickHom C := by
  intro X Y hx hy he
  have he' := congrArg (GrothendieckGroup.mapAnti E) he
  simp only [GrothendieckGroup.mapAnti, GrothendieckGroup.lift_of] at he'
  obtain ⟨f,hf⟩ := h _ _ (hy.mapAnti E) (hx.mapAnti E) he'.symm
  refine ⟨(E.functor.preimage f).unop, fun hz ↦ hf ?_⟩
  have hg : E.functor.preimage f = 0 := by simpa using congrArg Quiver.Hom.op hz
  simpa using E.functor.congr_map hg

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]

include k in
theorem isEFinite_iff_opposite : IsEFinite R ↔ IsEFinite Rᵐᵒᵖ := by
  let : IsNoetherianRing R := isNoetherian_of_tower k inferInstance
  let : IsArtinianRing R := isArtinian_of_tower k inferInstance
  let : IsNoetherianRing Rᵐᵒᵖ := isNoetherian_of_tower k inferInstance
  let : IsArtinianRing Rᵐᵒᵖ := isArtinian_of_tower k inferInstance
  rw [isEFinite_iff_equalClassBrickHom k, isEFinite_iff_equalClassBrickHom k]
  exact ⟨EqualClassBrickHom.of_antiEquivalence (Contragredient.reverseDualityEquivalence k R),
    EqualClassBrickHom.of_antiEquivalence (Contragredient.dualityEquivalence k R)⟩

end EFiniteCharacterizations
