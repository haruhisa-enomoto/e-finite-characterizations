module

public import EFiniteCharacterizations.Presentations.ShiftedProjectiveDuality
public import EFiniteCharacterizations.Silting.Fans.ConeSaturation

/-!
# Duality of the `g`-vector fan for the opposite algebra

Lemma 2.1(3) (`lem:fan-lattice`) of the manuscript: under the shifted projective
duality `Hom_R(-, R)[1]`, the support `Σ(Rᵐᵒᵖ)` of the `g`-vector fan of the opposite
algebra equals `-Σ(R)` (`image_neg_star_fanSupport`), so E-finiteness is left–right
symmetric.
-/

@[expose] public section

open CategoryTheory
open scoped NNReal

universe u

namespace EFiniteCharacterizations

/-- The real-linear identification induced by projective duality on the integral lattice. -/
noncomputable def realProjectiveStar (R : Type u) [Ring R] :
    RealProjectiveSpace R ≃ₗ[ℝ] RealProjectiveSpace Rᵐᵒᵖ :=
  (ProjectiveClass.starEquiv R).toIntLinearEquiv.baseChange ℤ ℝ _ _

namespace TwoTerm

variable {R : Type u} [Ring R]

theorem realClass_shiftedDual (P : TwoTerm R) :
    realProjectiveClass Rᵐᵒᵖ P.shiftedDual.projectiveClass =
      -realProjectiveStar R (realProjectiveClass R P.projectiveClass) := by
  rw [class_shiftedDual, map_neg]
  rfl

private theorem cone_eq_of_iso {P Q : TwoTerm R} (i : P.asArrow ≅ Q.asArrow) :
    P.gVectorCone = Q.gVectorCone := by
  have h {A B : TwoTerm R} (a : A.asArrow ≅ B.asArrow) : A.gVectorCone ≤ B.gVectorCone := by
    apply Submodule.span_le.mpr
    rintro v ⟨T,hT,rfl⟩
    exact PointedCone.subset_hull ⟨T,hT.trans (IsInAdd.of_retraction a.hom a.inv a.hom_inv_id),rfl⟩
  exact le_antisymm (h i) (h i.symm)

/-- Reversing the two dual terms gives the negative of the real-linear identification on
the entire cone of each complex. -/
theorem map_gVectorCone_shiftedDual (P : TwoTerm R) :
    P.gVectorCone.map (-(realProjectiveStar R).toLinearMap) = P.shiftedDual.gVectorCone := by
  let f := -(realProjectiveStar R).toLinearMap
  change Submodule.map (f.restrictScalars ℝ≥0) (Submodule.span _ _) = Submodule.span _ _
  rw [Submodule.map_span]
  apply congrArg (Submodule.span _)
  ext v
  constructor
  · rintro ⟨_,⟨T,hT,rfl⟩,rfl⟩
    exact ⟨T.shiftedDual,(inAdd_shiftedDual_iff T P).2 hT,T.realClass_shiftedDual.symm⟩
  · rintro ⟨U,hU,rfl⟩
    obtain ⟨T,⟨i⟩⟩ := exists_shiftedDual_iso U
    have ht := (IsInAdd.of_retraction i.hom i.inv i.hom_inv_id).trans hU
    exact ⟨_,⟨T,(inAdd_shiftedDual_iff T P).1 ht,rfl⟩,
      T.realClass_shiftedDual.symm.trans (congrArg _ (class_eq_of_arrow_iso i))⟩

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
/-- Under the real identification induced by projective duality, the support of the
opposite algebra's fan is the negative of the original support. -/
theorem image_neg_star_fanSupport :
    (fun x ↦ -realProjectiveStar R x) '' gVectorFanSupport R = gVectorFanSupport Rᵐᵒᵖ := by
  ext y
  constructor
  · rintro ⟨x,⟨P,hP,hx⟩,rfl⟩
    refine ⟨P.shiftedDual,(isPresilting_shiftedDual_iff P).2 hP,?_⟩
    rw [← map_gVectorCone_shiftedDual]
    exact ⟨x,hx,rfl⟩
  · rintro ⟨Q,hQ,hy⟩
    obtain ⟨P,⟨i⟩⟩ := exists_shiftedDual_iso Q
    have hp := (isPresilting_iff_of_term_isos k P.shiftedDual Q
      (Arrow.leftFunc.mapIso i) (Arrow.rightFunc.mapIso i) i.hom.w).2 hQ
    rw [← cone_eq_of_iso i, ← map_gVectorCone_shiftedDual] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    exact ⟨x,⟨P,(isPresilting_shiftedDual_iff P).1 hp,hx⟩,rfl⟩

end TwoTerm
end EFiniteCharacterizations
