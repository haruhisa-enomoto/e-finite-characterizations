module

public import EFiniteCharacterizations.Modules.ProjectiveBiproducts
public import EFiniteCharacterizations.Presentations.BlockDifferential

/-! # Shifted Hom bounds for a two-term extension -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R]

/-- The extension of two two-term complexes given by an off-diagonal map. -/
noncomputable def blockExtension (E L : TwoTerm R) (w : L.source ⟶ E.target) : TwoTerm R := by
  let _ := E.projective_source
  let _ := E.projective_target
  let _ := L.projective_source
  let _ := L.projective_target
  exact ⟨E.source ⊞ L.source, E.target ⊞ L.target,
    FGModuleCat.projective_biprod E.source L.source, FGModuleCat.projective_biprod E.target L.target,
    blockDifferential E.differential L.differential w⟩

@[simp] theorem projectiveClass_blockExtension (E L : TwoTerm R) (w : L.source ⟶ E.target) :
    (E.blockExtension L w).projectiveClass = E.projectiveClass + L.projectiveClass := by
  unfold projectiveClass
  change ProjectiveClass.of (ProjectiveClass.biprod ⟨E.target, E.projective_target⟩ ⟨L.target, L.projective_target⟩) -
    ProjectiveClass.of (ProjectiveClass.biprod ⟨E.source, E.projective_source⟩ ⟨L.source, L.projective_source⟩) = _
  simp only [ProjectiveClass.of_biprod]
  abel

theorem finrank_lt_of_surjective_of_kills_nonzero {k V W : Type*} [Field k]
    [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W] [Module.Finite k V]
    (f : V →ₗ[k] W) (hf : Function.Surjective f) {v : V} (hv : v ≠ 0) (h : f v = 0) :
    Module.finrank k W < Module.finrank k V := by
  have hz : (⟨v, h⟩ : f.ker) ≠ 0 := fun e ↦ hv (congrArg Subtype.val e)
  have hp : 0 < Module.finrank k f.ker := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hz⟩
  have hdim := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top] at hdim
  omega

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

/-- A nonzero extension class lowers the two reverse shifted Hom dimensions.
The forward dimensions stay zero. -/
theorem shiftedHomFinrank_blockExtension_bounds (E L : TwoTerm R) (hE : E.IsPresilting)
    (hL : L.IsPresilting) (hEL : E.shiftedHomFinrank k L = 0) (w : L.source ⟶ E.target)
    (hw : (boundaryLinear k L.differential E.differential).range.mkQ w ≠ 0) :
    let X := E.blockExtension L w
    E.shiftedHomFinrank k X = 0 ∧ X.shiftedHomFinrank k L = 0 ∧
      X.shiftedHomFinrank k E < L.shiftedHomFinrank k E ∧
      L.shiftedHomFinrank k X < L.shiftedHomFinrank k E := by
  have (M N : FGModuleCat.{u} R) : Module.Finite k (M ⟶ N) := finiteModuleHom_isFinite k M N
  have hEE := (shiftedHomFinrank_eq_zero_iff k E E).2 hE
  have hLL := (shiftedHomFinrank_eq_zero_iff k L L).2 hL
  have hEL' : Function.Surjective (boundaryLinear k E.differential L.differential) :=
    (shiftedHomFinrank_eq_zero_iff k E L).1 hEL
  have hEX := LinearMap.finrank_le_finrank_of_surjective
    (blockCokernelInclusion_surjective k E.differential L.differential w E.differential hEL')
  have hXL := LinearMap.finrank_le_finrank_of_surjective
    (blockCokernelProjection_surjective k E.differential L.differential w L.differential hEL')
  refine ⟨Nat.eq_zero_of_le_zero (hEX.trans hEE.le), Nat.eq_zero_of_le_zero (hXL.trans hLL.le), ?_, ?_⟩
  · exact finrank_lt_of_surjective_of_kills_nonzero _
      (blockCokernelProjection_surjective k E.differential L.differential w E.differential hE) hw
      (blockCokernelProjection_extensionClass k E.differential L.differential w)
  · exact finrank_lt_of_surjective_of_kills_nonzero _
      (blockCokernelInclusion_surjective k E.differential L.differential w L.differential hL) hw
      (blockCokernelInclusion_extensionClass k E.differential L.differential w)

/-- A pair of presilting complexes with a nonzero reverse shifted Hom has an
extension of the sum class satisfying the four subdivision estimates. -/
theorem exists_extension_with_shiftedHomFinrank_bounds (E L : TwoTerm R)
    (hE : E.IsPresilting) (hL : L.IsPresilting) (hEL : E.shiftedHomFinrank k L = 0)
    (hLE : 0 < L.shiftedHomFinrank k E) :
    ∃ X : TwoTerm R, X.projectiveClass = E.projectiveClass + L.projectiveClass ∧
      E.shiftedHomFinrank k X = 0 ∧ X.shiftedHomFinrank k L = 0 ∧
      X.shiftedHomFinrank k E < L.shiftedHomFinrank k E ∧
      L.shiftedHomFinrank k X < L.shiftedHomFinrank k E := by
  have := finiteModuleHom_isFinite k L.source E.target
  obtain ⟨z, hz⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hLE
  obtain ⟨w, rfl⟩ := (boundaryLinear k L.differential E.differential).range.mkQ_surjective z
  exact ⟨E.blockExtension L w, projectiveClass_blockExtension E L w,
    shiftedHomFinrank_blockExtension_bounds k E L hE hL hEL w hz⟩

end EFiniteCharacterizations.TwoTerm
