module

public import EFiniteCharacterizations.Silting.Reduction.Bongartz
public import EFiniteCharacterizations.Presentations.SplitBoundary

/-! # Compatible presilting classes on either side of a given class -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R] (k : Type u) [Field k] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

include k in
theorem compatible_of_precompose {P Q : TwoTerm R} (hP : P.IsPresilting)
    (hPQ : Function.Surjective (P.precompose (cokernel Q.differential)))
    (hQP : Function.Surjective (Q.precompose (cokernel P.differential)))
    (hQ : Function.Surjective (Q.precompose (cokernel Q.differential))) :
    (P.directSum Q).IsPresilting := by
  apply (isPresilting_directSum_iff k _ _).2
  exact ⟨hP, (surjective_boundary_iff_surjective_precompose Q Q).2 hQ,
    (shiftedHomFinrank_eq_zero_iff k _ _).2 ((surjective_boundary_iff_surjective_precompose P Q).2 hPQ),
    (shiftedHomFinrank_eq_zero_iff k _ _).2 ((surjective_boundary_iff_surjective_precompose Q P).2 hQP)⟩

/-- A projective class can be added to a nonnegative multiple of a presilting
class while retaining compatibility with the original complex. -/
theorem exists_compatible_add_projective (P : TwoTerm R) (hP : P.IsPresilting)
    (G : FiniteProjective R) :
    ∃ Q : TwoTerm R, (P.directSum Q).IsPresilting ∧ Q.projectiveClass =
      Module.finrank k (P.source ⟶ G.val) • P.projectiveClass + ProjectiveClass.of G := by
  let _ := G.property
  obtain ⟨Q,_,hg,hPQ,hQ,_⟩ := exists_bongartz_at_projective k P hP G.val
  exact ⟨Q, compatible_of_precompose k hP hPQ
    (hQ _ ((surjective_boundary_iff_surjective_precompose P P).1 hP)) (hQ _ hPQ),
    hg.trans (add_comm ..)⟩

/-- For a minimal presentation the positive completion has the g-vector of
its cokernel. There is no contribution from a shifted projective summand. -/
theorem exists_compatible_cokernel_add_projective (P : TwoTerm R) (hP : P.IsPresilting)
    (hm : ∀ a, a ≫ P.differential = P.differential → IsIso a) (G : FiniteProjective R) :
    ∃ Q : TwoTerm R, (P.directSum Q).IsPresilting ∧ moduleProjectiveClass k (cokernel Q.differential) =
      Module.finrank k (P.source ⟶ G.val) • P.projectiveClass + ProjectiveClass.of G := by
  let _ := G.property
  obtain ⟨Q,_,hmin,hg,hPQ,hQ,_⟩ := exists_bongartz_at_projective_rightMinimal k P hP G.val
  exact ⟨Q,compatible_of_precompose k hP hPQ
    (hQ _ ((surjective_boundary_iff_surjective_precompose P P).1 hP)) (hQ _ hPQ),
    (Q.projectiveClass_eq_of_rightMinimal k (hmin hm)).symm.trans (hg.trans (add_comm ..))⟩

/-- The opposite completion uses the universal map from the projective into
copies of the target of the given differential. -/
theorem exists_compatible_sub_projective (P : TwoTerm R) (hP : P.IsPresilting)
    (G : FiniteProjective R) :
    ∃ Q : TwoTerm R, (P.directSum Q).IsPresilting ∧ Q.projectiveClass =
      Module.finrank k (G.val ⟶ P.target) • P.projectiveClass - ProjectiveClass.of G := by
  classical
  let _ := G.property
  have := finiteModuleHom_isFinite k G.val P.target
  let n := Module.finrank k (G.val ⟶ P.target)
  let b : Module.Basis (Fin n) k (G.val ⟶ P.target) := Module.finBasis k _
  let S : Fin n → FGModuleCat.{u} R := fun _ ↦ P.source
  let T : Fin n → FGModuleCat.{u} R := fun _ ↦ P.target
  let H : G.val ⟶ ⨁ T := biproduct.lift b
  let D : (⨁ S) ⟶ ⨁ T := biproduct.map (fun _ ↦ P.differential)
  let d := biprod.desc H D
  let _ := FGModuleCat.projective_biproduct S (fun _ ↦ P.projective_source)
  let _ := FGModuleCat.projective_biproduct T (fun _ ↦ P.projective_target)
  let _ := FGModuleCat.projective_biprod G.val (⨁ S)
  let Q := ofDifferential d
  let X := cokernel P.differential
  let π := cokernel.π P.differential
  have hPX := (surjective_boundary_iff_surjective_precompose P P).1 hP
  have hd : biprod.inr ≫ d = D := biprod.inr_desc H D
  have hD (i : Fin n) : biproduct.ι S i ≫ D = P.differential ≫ biproduct.ι T i := biproduct.ι_map _ _
  have hH (i : Fin n) : H ≫ biproduct.π T i = b i := biproduct.lift_π _ _
  have hgen : IsGeneratedBy X (cokernel d) := by
    have hz (i : Fin n) : P.differential ≫ biproduct.ι T i ≫ cokernel.π d = 0 := by
      rw [← Category.assoc, ← hD, Category.assoc, ← hd, Category.assoc, cokernel.condition, comp_zero, comp_zero]
    let g := biproduct.desc fun i ↦ cokernel.desc P.differential _ (hz i)
    have he : biproduct.map (fun _ : Fin n ↦ π) ≫ g = cokernel.π d := by
      apply biproduct.hom_ext'
      intro i
      rw [← Category.assoc, biproduct.ι_map, Category.assoc, biproduct.ι_desc, cokernel.π_desc]
    exact ⟨n,g,epi_of_epi_fac he⟩
  have hQX : Function.Surjective (Q.precompose X) := by
    intro f
    choose z hz using fun i : Fin n ↦ hPX (biproduct.ι S i ≫ biprod.inr ≫ f)
    let v : (⨁ T) ⟶ X := biproduct.desc z
    have hv : D ≫ v = biprod.inr ≫ f := by
      apply biproduct.hom_ext'
      intro i
      rw [← Category.assoc, hD, Category.assoc, biproduct.ι_desc]
      exact hz i
    obtain ⟨r,hr⟩ := FGModuleCat.exists_lift_of_projective π (biprod.inl ≫ f - H ≫ v)
    let w : (⨁ T) ⟶ X := ∑ i, b.repr r i • (biproduct.π T i ≫ π)
    have hHw : H ≫ w = r ≫ π := by
      simp only [w,Preadditive.comp_sum,Linear.comp_smul,← Category.assoc H,hH,← Linear.smul_comp,
        ← Preadditive.sum_comp,b.sum_repr]
    have hDw : D ≫ w = 0 := by
      have hz (i : Fin n) : D ≫ biproduct.π T i ≫ π = 0 := by
        rw [← Category.assoc, show D ≫ biproduct.π T i = biproduct.π S i ≫ P.differential from biproduct.map_π _ _,
          Category.assoc, cokernel.condition, comp_zero]
      simp only [w, Preadditive.comp_sum, Linear.comp_smul, hz, smul_zero, Finset.sum_const_zero]
    refine ⟨v + w,?_⟩
    change d ≫ (v + w) = f
    apply biprod.hom_ext'
    · rw [← Category.assoc,biprod.inl_desc,Preadditive.comp_add,hHw,hr]
      abel
    · rw [← Category.assoc,hd,Preadditive.comp_add,hv,hDw,add_zero]
  refine ⟨Q, compatible_of_precompose k (Q := Q) hP (P.surjective_precompose_of_generatedBy hPX hgen)
    hQX (Q.surjective_precompose_of_generatedBy hQX hgen),?_⟩
  change ProjectiveClass.of ⟨⨁ T, inferInstance⟩ -
      ProjectiveClass.of (ProjectiveClass.biprod G ⟨⨁ S, inferInstance⟩) = _
  rw [ProjectiveClass.of_biprod, ProjectiveClass.of_copies ⟨P.target, P.projective_target⟩,
    ProjectiveClass.of_copies ⟨P.source, P.projective_source⟩]
  simp only [projectiveClass,nsmul_sub]
  abel

end EFiniteCharacterizations.TwoTerm
