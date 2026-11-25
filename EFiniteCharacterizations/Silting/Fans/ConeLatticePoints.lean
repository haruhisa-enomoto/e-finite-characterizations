module

public import EFiniteCharacterizations.Silting.Fans.PresiltingConeWalls
public import EFiniteCharacterizations.Silting.ThickSubcategories.MaximalPresilting
public import EFiniteCharacterizations.LinearAlgebra.IntegralSeparation
public import EFiniteCharacterizations.LinearAlgebra.IntegralConeRelation

/-! # Positive multiples of integral points of a presilting cone -/

@[expose] public section

open CategoryTheory
open scoped TensorProduct nonZeroDivisors

universe u

namespace EFiniteCharacterizations

private theorem integral_positive_relation {ι G : Type*} [Fintype ι] [AddCommGroup G]
    (g : ι → G) (v : G) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (he : ∑ i, a i ⊗ₜ[ℤ] g i = (1 : ℝ) ⊗ₜ[ℤ] v) :
    ∃ (m : ι → ℕ) (n : ℕ), 0 < n ∧ ∑ i, m i • g i = n • v := by
  classical
  let b (i : Option ι) := i.elim 1 a
  obtain ⟨f,hf⟩ := exists_rat_linear_pos_on_finset (Finset.univ.image b) (by
    rintro _ h
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
    cases i with
    | none => exact zero_lt_one
    | some i => exact ha i)
  obtain ⟨d,z,hd,hz⟩ := Farkas.common_denominator (fun i ↦ f (b i))
  let m (i : Option ι) := (z i).toNat
  have hpos (i) : 0 < z i := by
    have h := mul_pos hd (hf (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
    rw [← hz] at h
    exact_mod_cast h
  have hm (i) : (m i : ℚ) = d * f (b i) := by
    rw [← hz, ← Int.cast_natCast]
    exact congrArg (Int.cast : ℤ → ℚ) (Int.toNat_of_nonneg (hpos i).le)
  let L := TensorProduct.map (f.restrictScalars ℤ) (LinearMap.id : G →ₗ[ℤ] G)
  have hq := congrArg (fun x ↦ d • L x) he
  simp only [map_sum, Finset.smul_sum, L, TensorProduct.map_tmul, LinearMap.restrictScalars_apply,
    LinearMap.id_apply, TensorProduct.smul_tmul', smul_eq_mul] at hq
  have hm₁ : (m none : ℚ) = d * f 1 := hm none
  have hm₂ (i) : (m (some i) : ℚ) = d * f (a i) := hm (some i)
  simp_rw [← hm₁, ← hm₂] at hq
  have ht (r : ℕ) (x : G) : (r : ℚ) ⊗ₜ[ℤ] x = (1 : ℚ) ⊗ₜ[ℤ] (r • x) := by
    simpa only [nsmul_eq_mul, mul_one] using TensorProduct.smul_tmul (R := ℤ) r (1 : ℚ) x
  simp_rw [ht] at hq
  rw [← TensorProduct.tmul_sum] at hq
  let j := TensorProduct.mk ℤ ℚ G 1
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ) j).1 hq
  change s.val • (∑ i, m (some i) • g i) = s.val • (m none • v) at hs
  let p := s.val * s.val
  have hp : 0 < p := mul_self_pos.mpr (nonZeroDivisors.ne_zero s.property)
  have hmul : p • (∑ i, m (some i) • g i) = p • (m none • v) := by
    simpa only [p, mul_smul] using congrArg (fun z ↦ s.val • z) hs
  rw [← Int.toNat_of_nonneg hp.le] at hmul
  simp only [natCast_zsmul, Finset.smul_sum, smul_smul] at hmul
  have hn : 0 < m none := by have := hpos none; dsimp [m]; omega
  exact ⟨_, _, Nat.mul_pos (show 0 < p.toNat by omega) hn, hmul⟩

namespace TwoTerm

variable {R : Type u} [Ring R]

/-- Every integral point in a presilting cone has a positive multiple represented
by an object in the additive closure of its generator. -/
theorem exists_multiple_in_add_of_mem_gVectorCone (P : TwoTerm R) {v : ProjectiveClass R}
    (hv : realProjectiveClass R v ∈ P.gVectorCone) :
    ∃ (n : ℕ) (Q : TwoTerm R), 0 < n ∧ IsInAdd Q.asArrow P.asArrow ∧ Q.projectiveClass = n • v := by
  classical
  obtain ⟨c,hc,hpos,he⟩ := PointedCone.mem_hull_set.mp hv
  choose Q hQ hclass using fun i : c.support ↦ hc i.property
  let a (i : c.support) := c i.val
  have ha (i : c.support) : 0 < a i := lt_of_le_of_ne (hpos i.val) (Finsupp.mem_support_iff.mp i.property).symm
  have he' : ∑ i : c.support, a i ⊗ₜ[ℤ] (Q i).projectiveClass = (1 : ℝ) ⊗ₜ[ℤ] v := by
    change ∑ x ∈ c.support, c x • x = _ at he
    rw [← Finset.sum_coe_sort] at he
    change ∑ i : c.support, c i.val • i.val = (1 : ℝ) ⊗ₜ[ℤ] v at he
    convert he using 1
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = c i.val • realProjectiveClass R (Q i).projectiveClass := by
        change _ = c i.val • ((1 : ℝ) ⊗ₜ[ℤ] (Q i).projectiveClass)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = _ := congrArg (c i.val • ·) (hclass i).symm
  obtain ⟨m,n,hn,hm⟩ := integral_positive_relation _ v a ha he'
  suffices h : ∀ s : Finset (↥c.support), ∃ T : TwoTerm R,
      IsInAdd T.asArrow P.asArrow ∧ T.projectiveClass = ∑ i ∈ s, m i • (Q i).projectiveClass by
    obtain ⟨T,hT,ht⟩ := h Finset.univ
    exact ⟨n,T,hn,hT,ht.trans hm⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨P.copies 0, isInAdd_copies P 0, by simp⟩
  | insert i s hi ih =>
    obtain ⟨T,hT,ht⟩ := ih
    exact ⟨((Q i).copies (m i)).directSum T,
      isInAdd_directSum _ _ _ ((isInAdd_copies _ _).trans (hQ i)) hT,
      by rw [projectiveClass_directSum, projectiveClass_copies, ht, Finset.sum_insert hi]⟩

/-- The sector of a pair is contained in the cone of its direct sum. -/
theorem sectorBetween_subset_gVectorCone (E L : TwoTerm R) :
    sectorBetween (realProjectiveClass R E.projectiveClass) (realProjectiveClass R L.projectiveClass) ⊆
      ((E.directSum L).gVectorCone : Set _) := by
  rintro _ ⟨a,b,ha,hb,rfl⟩
  let C := (E.directSum L).gVectorCone
  have hE : realProjectiveClass R E.projectiveClass ∈ C :=
    PointedCone.subset_hull ⟨E,IsInAdd.of_retraction _ _ (inlDirectSum_fstDirectSum E L),rfl⟩
  have hL : realProjectiveClass R L.projectiveClass ∈ C :=
    PointedCone.subset_hull ⟨L,IsInAdd.of_retraction _ _ (inrDirectSum_sndDirectSum E L),rfl⟩
  exact C.add_mem (C.smul_mem ha hE) (C.smul_mem hb hL)

/-- Both rays of a compatible sector are summands of a common Bongartz
completion. Its thick closure contains every two-term projective complex. -/
theorem sector_subset_completion_cone [IsNoetherianRing R] (k : Type u) [Field k] [Algebra k R]
    [Module.Finite k R] (E L : TwoTerm R) (h : (E.directSum L).IsPresilting) :
    ∃ T : TwoTerm R, T.IsPresilting ∧ (∀ X : TwoTerm R, InThick T X) ∧
      sectorBetween (realProjectiveClass R E.projectiveClass) (realProjectiveClass R L.projectiveClass) ⊆
        (T.gVectorCone : Set _) := by
  let U := E.directSum L
  obtain ⟨B,ht,hgen,_⟩ := exists_bongartz_generator k U h
  refine ⟨U.directSum B,ht,hgen,(sectorBetween_subset_gVectorCone E L).trans ?_⟩
  apply Submodule.span_mono
  rintro x ⟨X,hX,rfl⟩
  exact ⟨X,hX.trans (IsInAdd.of_retraction _ _ (inlDirectSum_fstDirectSum U B)),rfl⟩

end TwoTerm
end EFiniteCharacterizations
