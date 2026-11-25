module

public import EFiniteCharacterizations.Silting.ThickSubcategories.BoundedProjectiveHomotopy
public import EFiniteCharacterizations.Presentations.RigidTerms

/-! # Shifted Hom dimensions along a pencil of projective differentials -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u
namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [IsNoetherianRing R]

/-- Passing to the full bounded-projective category preserves the vector
space of maps into each shift. -/
noncomputable def boundedShiftHomEquiv (P Q : TwoTerm R) (n : ℤ) :
    (P.inBoundedProjectives ⟶ Q.inBoundedProjectives⟦n⟧) ≃ₗ[k]
      (P.homotopyObject ⟶ Q.homotopyObject⟦n⟧) := by
  let F := (boundedProjective R).ι
  let f := F.mapLinearMap k (X := P.inBoundedProjectives) (Y := Q.inBoundedProjectives⟦n⟧)
  exact (LinearEquiv.ofBijective f ⟨F.map_injective,F.map_surjective⟩).trans
    (Linear.homCongr k (Iso.refl _) ((F.commShiftIso n).app Q.inBoundedProjectives))

/-- The degree-one boundary quotient computes the ground-field dimension in
the bounded homotopy category of finite projectives. -/
theorem bounded_shift_one_finrank (P Q : TwoTerm R) :
    Module.finrank k (P.inBoundedProjectives ⟶ Q.inBoundedProjectives⟦(1 : ℤ)⟧) =
      P.shiftedHomFinrank k Q := by
  obtain ⟨φ,hs,hk⟩ := exists_linear_shiftedHom_quotient P Q k
  have he : LinearMap.ker φ = (boundaryLinear k P.differential Q.differential).range := by
    ext f
    exact hk f
  exact ((boundedShiftHomEquiv k P Q 1).trans ((φ.quotKerEquivOfSurjective hs).symm.trans
    (Submodule.quotEquivOfEq _ _ he))).finrank_eq

theorem bounded_shift_finrank_outside (P Q : TwoTerm R) {n : ℤ} (hn : n < -1 ∨ 1 < n) :
    Module.finrank k (P.inBoundedProjectives ⟶ Q.inBoundedProjectives⟦n⟧) = 0 := by
  have := subsingleton_hom_shift_outside P Q hn
  rw [(boundedShiftHomEquiv k P Q n).finrank_eq]
  exact Module.finrank_zero_of_subsingleton

/-- Both pencil inequalities in degree one and in every degree outside the
support of the Hom complex. -/
theorem pencil_hom_finrank_le_of_shift_ne_zero_neg_one [Module.Finite k R]
    {A B : FGModuleCat.{u} R} [Module.Projective R A] [Module.Projective R B]
    (u σ : A ⟶ B) (hu : (ofDifferential u).IsPresilting) (V : TwoTerm R)
    (n : ℤ) (hn : n ≠ 0) (hm : n ≠ -1) :
    let U := (ofDifferential u).inBoundedProjectives
    let S := (ofDifferential σ).inBoundedProjectives
    let W := V.inBoundedProjectives
    Module.finrank k (U ⟶ W⟦n⟧) ≤ Module.finrank k (S ⟶ W⟦n⟧) ∧
      Module.finrank k (W ⟶ U⟦n⟧) ≤ Module.finrank k (W ⟶ S⟦n⟧) := by
  by_cases hd : n = 1
  · subst n
    simpa only [bounded_shift_one_finrank] using shiftedHomFinrank_le_of_rigid k (σ := σ) hu V
  · have hz : n < -1 ∨ 1 < n := by omega
    dsimp only
    simp only [bounded_shift_finrank_outside k _ _ hz,le_refl,and_self]

/-- Changing a rigid differential on fixed terms increases the dimension of
maps out of its cokernel and into its kernel, against every finite module. -/
theorem pencil_kernel_cokernel_finrank_le [Module.Finite k R]
    {A B : FGModuleCat.{u} R} (u σ : A ⟶ B)
    (hu : Function.Surjective (boundaryLinear k u u)) (M : FGModuleCat.{u} R) :
    Module.finrank k (cokernel u ⟶ M) ≤ Module.finrank k (cokernel σ ⟶ M) ∧
      Module.finrank k (M ⟶ kernel u) ≤ Module.finrank k (M ⟶ kernel σ) := by
  have (X Y : FGModuleCat.{u} R) : Module.Finite k (X ⟶ Y) := finiteModuleHom_isFinite k X Y
  have hr := boundaryLinear_rank_le_at_rigid k u σ (0 : M ⟶ M) hu
  have left (f : A ⟶ B) : (boundaryLinear k f (0 : M ⟶ M)).range = (Linear.leftComp k M f).range := by
    ext x
    constructor
    · rintro ⟨⟨a,b⟩,rfl⟩
      exact ⟨-b,by simp [boundaryLinear_apply]⟩
    · rintro ⟨b,rfl⟩
      exact ⟨(0,-b),by simp [boundaryLinear_apply]⟩
  have right (f : A ⟶ B) : (boundaryLinear k (0 : M ⟶ M) f).range = (Linear.rightComp k M f).range := by
    ext x
    constructor
    · rintro ⟨⟨a,b⟩,rfl⟩
      exact ⟨a,by simp [boundaryLinear_apply]⟩
    · rintro ⟨a,rfl⟩
      exact ⟨(a,0),by simp [boundaryLinear_apply]⟩
  obtain ⟨h₁,h₂⟩ := hr
  rw [left,left] at h₁
  rw [right,right] at h₂
  rw [(cokernelHomLinearEquiv k u M).finrank_eq,(cokernelHomLinearEquiv k σ M).finrank_eq,
    (homKernelLinearEquiv k u M).finrank_eq,(homKernelLinearEquiv k σ M).finrank_eq]
  have hl₁ := (Linear.leftComp k M u).finrank_range_add_finrank_ker
  have hl₂ := (Linear.leftComp k M σ).finrank_range_add_finrank_ker
  have hr₁ := (Linear.rightComp k M u).finrank_range_add_finrank_ker
  have hr₂ := (Linear.rightComp k M σ).finrank_range_add_finrank_ker
  omega

theorem bounded_shift_neg_one_finrank (P Q : TwoTerm R) :
    Module.finrank k (P.inBoundedProjectives ⟶ Q.inBoundedProjectives⟦(-1 : ℤ)⟧) =
      Module.finrank k (cokernel P.differential ⟶ kernel Q.differential) :=
  ((boundedShiftHomEquiv k P Q (-1)).trans (negOneHomEquiv P Q k).symm).finrank_eq

/-- Both pencil inequalities for all nonzero shifts, over any field. -/
theorem pencil_hom_finrank_le_of_shift_ne_zero [Module.Finite k R]
    {A B : FGModuleCat.{u} R} [Module.Projective R A] [Module.Projective R B]
    (u σ : A ⟶ B) (hu : (ofDifferential u).IsPresilting) (V : TwoTerm R)
    (n : ℤ) (hn : n ≠ 0) :
    let U := (ofDifferential u).inBoundedProjectives
    let S := (ofDifferential σ).inBoundedProjectives
    let W := V.inBoundedProjectives
    Module.finrank k (U ⟶ W⟦n⟧) ≤ Module.finrank k (S ⟶ W⟦n⟧) ∧
      Module.finrank k (W ⟶ U⟦n⟧) ≤ Module.finrank k (W ⟶ S⟦n⟧) := by
  by_cases hm : n = -1
  · subst n
    simp only [bounded_shift_neg_one_finrank]
    have h := (isPresilting_iff_boundaryLinear_surjective (k := k) (ofDifferential u)).1 hu
    exact ⟨(pencil_kernel_cokernel_finrank_le k u σ h (kernel V.differential)).1,
      (pencil_kernel_cokernel_finrank_le k u σ h (cokernel V.differential)).2⟩
  · exact pencil_hom_finrank_le_of_shift_ne_zero_neg_one k u σ hu V n hn hm

end EFiniteCharacterizations.TwoTerm
