module

public import EFiniteCharacterizations.Stability.EndInvariantSubmodules
public import EFiniteCharacterizations.Silting.Fans.RealProjectiveSpace

/-! # Real projective stability walls -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R]

/-- The Euler pairing with an ambient class extended to the real projective space. -/
noncomputable def realEulerEvaluation (z : GrothendieckGroup (FGModuleCat.{u} R)) :
    RealProjectiveSpace R →+ ℝ :=
  (TensorProduct.lift (LinearMap.mk₂ ℤ (fun r g ↦ r * (projectiveClassWeight k g z : ℝ))
    (fun _ _ _ ↦ add_mul ..) (fun _ _ _ ↦ by simp [zsmul_eq_mul, mul_assoc])
    (fun _ _ _ ↦ by simp [map_add, mul_add]) (fun _ _ _ ↦ by simp [map_zsmul, zsmul_eq_mul]; ring))).toAddMonoidHom

/-- The real stability wall consists of the weights annihilating the total
class and nonpositive on the proper nonzero subobject classes. -/
def realStabilityWall (X : FGModuleCat.{u} R) : Set (RealProjectiveSpace R) :=
  {v | realEulerEvaluation k (GrothendieckGroup.of X) v = 0 ∧
    ∀ z ∈ properSubobjectClasses X, realEulerEvaluation k z v ≤ 0}

theorem realEulerEvaluation_tmul (z : GrothendieckGroup (FGModuleCat.{u} R)) (a : ℝ) (g : ProjectiveClass R) :
    realEulerEvaluation k z (a ⊗ₜ[ℤ] g) = a * (projectiveClassWeight k g z : ℝ) :=
  by unfold realEulerEvaluation; simp

theorem realEulerEvaluation_integral (z : GrothendieckGroup (FGModuleCat.{u} R)) (g : ProjectiveClass R) :
    realEulerEvaluation k z (realProjectiveClass R g) = (projectiveClassWeight k g z : ℝ) := by
  exact (realEulerEvaluation_tmul k z 1 g).trans (one_mul _)

/-- Evaluation at a fixed ambient class as a real linear form. -/
noncomputable def realEulerForm (z : GrothendieckGroup (FGModuleCat.{u} R)) :
    RealProjectiveSpace R →ₗ[ℝ] ℝ where
  __ := realEulerEvaluation k z
  map_smul' a x := by
    change realEulerEvaluation k z (a • x) = a • realEulerEvaluation k z x
    induction x using TensorProduct.inductionOn with
    | tmul b g => simp [TensorProduct.smul_tmul', realEulerEvaluation_tmul, mul_assoc]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem realEulerEvaluation_smul (z : GrothendieckGroup (FGModuleCat.{u} R))
    (a : ℝ) (v : RealProjectiveSpace R) :
    realEulerEvaluation k z (a • v) = a * realEulerEvaluation k z v :=
  (realEulerForm k z).map_smul a v

private theorem semistable_iff_proper (θ : Weight (FGModuleCat.{u} R)) (X : FGModuleCat.{u} R) :
    θ.IsSemistable X ↔ θ.eval X = 0 ∧ ∀ z ∈ properSubobjectClasses X, θ z ≤ 0 := by
  refine ⟨fun h ↦ ⟨h.1, ?_⟩, ?_⟩
  · rintro _ ⟨U,i,hi,_,_,rfl⟩
    exact h.2 i
  · rintro ⟨hz, hn⟩
    refine ⟨hz, fun {U} i hi ↦ ?_⟩
    by_cases hu : IsZero U
    · exact (θ.eval_isZero hu).le
    by_cases he : IsIso i
    · exact ((θ.eval_eq_of_isIso i).trans hz).le
    exact hn _ ⟨U,i,hi,hu,he,rfl⟩

theorem integral_mem_realStabilityWall (X : FGModuleCat.{u} R) (g : ProjectiveClass R) :
    realProjectiveClass R g ∈ realStabilityWall k X ↔ (projectiveClassWeight k g).IsSemistable X := by
  rw [semistable_iff_proper]
  simp [realStabilityWall, realEulerEvaluation_integral, Weight.eval]

noncomputable def realEulerWeight (v : RealProjectiveSpace R) :
    GrothendieckGroup (FGModuleCat.{u} R) →+ ℝ where
  toFun z := realEulerEvaluation k z v
  map_zero' := by
    induction v using TensorProduct.inductionOn with
    | tmul a g => simp [realEulerEvaluation_tmul]
    | add a b ha hb => simp [ha,hb]
  map_add' z z' := by
    induction v using TensorProduct.inductionOn with
    | tmul a g => simp [realEulerEvaluation_tmul, mul_add]
    | add a b ha hb => simp only [map_add, ha, hb]; abel

/-- An integral projective weight realizes any finite system of homogeneous
vanishing and strict negativity tests realized by a real weight. -/
theorem exists_integral_weight_of_real_tests {I J : Type*} [Fintype I] [Fintype J]
    (B : I → GrothendieckGroup (FGModuleCat.{u} R)) (U : J → GrothendieckGroup (FGModuleCat.{u} R))
    (v : RealProjectiveSpace R) (hB : ∀ i, realEulerEvaluation k (B i) v = 0)
    (hU : ∀ j, realEulerEvaluation k (U j) v < 0) :
    ∃ g : ProjectiveClass R, (∀ i, projectiveClassWeight k g (B i) = 0) ∧
      ∀ j, projectiveClassWeight k g (U j) < 0 := by
  obtain ⟨n, q, hq⟩ := exists_injective_projective_weight_coordinates (R := R) k
  rcases Farkas.integral_separation_of_injective_coordinates (fun t ↦ projectiveClassWeight k (q t)) hq B U with
    ⟨w, hw, hu⟩ | ⟨a, c, ha, hp, he⟩
  · exact ⟨∑ t, w t • q t, by simpa only [map_sum, map_zsmul] using hw,
      by simpa only [map_sum, map_zsmul] using hu⟩
  · exfalso
    let θ := realEulerWeight k v
    have hb (i) : θ (B i) = 0 := hB i
    have hu (j) : θ (U j) < 0 := hU j
    have h := congrArg θ he
    simp only [map_sum, map_zsmul, zsmul_eq_mul, hb, mul_zero, Finset.sum_const_zero] at h
    have hpos : ∃ j, 0 < a j := by
      by_contra! hn
      exact hp.not_ge (Finset.sum_nonpos fun j _ ↦ hn j)
    obtain ⟨j, hjp⟩ := hpos
    have hl : ∑ j, (a j : ℝ) * θ (U j) < 0 := Finset.sum_neg' (fun j (_ : j ∈ Finset.univ) ↦
      mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast ha j) (hu j).le)
      ⟨j, Finset.mem_univ _, mul_neg_of_pos_of_neg (by exact_mod_cast hjp) (hu j)⟩
    exact hl.ne h

theorem exists_matching_integral_weight
    {S : Set (GrothendieckGroup (FGModuleCat.{u} R))} (hs : S.Finite) (v : RealProjectiveSpace R) :
    ∃ g : ProjectiveClass R, ∀ x ∈ S,
      (projectiveClassWeight k g x = 0 ↔ realEulerEvaluation k x v = 0) ∧
      (projectiveClassWeight k g x ≤ 0 ↔ realEulerEvaluation k x v ≤ 0) := by
  classical
  let θ := realEulerWeight k v
  let s := hs.toFinset
  let Z := s.filter fun x ↦ θ x = 0
  let N := s.filter fun x ↦ θ x ≠ 0
  let u (j : N) := if θ j.val < 0 then j.val else -j.val
  have hu (j : N) : θ (u j) < 0 := by
    have hn := (Finset.mem_filter.mp j.property).2
    dsimp [u]
    split_ifs with hj
    · exact hj
    · rw [map_neg]
      exact neg_neg_of_pos (lt_of_le_of_ne (le_of_not_gt hj) (Ne.symm hn))
  obtain ⟨g, hg, hn⟩ := exists_integral_weight_of_real_tests k (fun i : Z ↦ i.val) u v
    (fun i ↦ (Finset.mem_filter.mp i.property).2) hu
  refine ⟨g, fun x hx ↦ ?_⟩
  have hxs : x ∈ s := hs.mem_toFinset.mpr hx
  change (_ ↔ θ x = 0) ∧ (_ ↔ θ x ≤ 0)
  by_cases hz : θ x = 0
  · have hg' := hg ⟨x, Finset.mem_filter.mpr ⟨hxs, hz⟩⟩
    simp [hz, hg']
  · let j : N := ⟨x, Finset.mem_filter.mpr ⟨hxs,hz⟩⟩
    have h := hn j
    by_cases hneg : θ x < 0
    · have h' : projectiveClassWeight k g x < 0 := by simpa [u, j, hneg] using h
      simp [hz, h'.ne, h'.le, hneg.le]
    · have h' : 0 < projectiveClassWeight k g x := by simpa [u, j, hneg] using h
      have hθ := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hz)
      simp [hz, h'.ne', h'.not_ge, hθ.not_ge]

/-- Two real walls coincide exactly when they contain the same integral
projective weights. The finite tests include both modules' proper subobjects. -/
theorem realStabilityWall_eq_iff_integral (X Y : FGModuleCat.{u} R) :
    realStabilityWall k X = realStabilityWall k Y ↔ ∀ g : ProjectiveClass R,
      (projectiveClassWeight k g).IsSemistable X ↔ (projectiveClassWeight k g).IsSemistable Y := by
  classical
  constructor
  · intro h g
    rw [← integral_mem_realStabilityWall, h, integral_mem_realStabilityWall]
  intro h
  ext v
  let s := insert (GrothendieckGroup.of X) (insert (GrothendieckGroup.of Y)
    (properSubobjectClasses X ∪ properSubobjectClasses Y))
  have hs : s.Finite := (((finite_properSubobjectClasses k X).union
    (finite_properSubobjectClasses k Y)).insert _).insert _
  obtain ⟨g, hg⟩ := exists_matching_integral_weight k hs v
  have test (M : FGModuleCat.{u} R) (hm : GrothendieckGroup.of M ∈ s) (hu : properSubobjectClasses M ⊆ s) :
      v ∈ realStabilityWall k M ↔ (projectiveClassWeight k g).IsSemistable M := by
    rw [semistable_iff_proper]
    change (_ ∧ _) ↔ _
    exact and_congr ((hg _ hm).1.symm) (forall_congr' fun z ↦ forall_congr' fun hz ↦ (hg z (hu hz)).2.symm)
  exact (test X (by simp [s]) (by intro z hz; simp [s,hz])).trans
    ((h g).trans (test Y (by simp [s]) (by intro z hz; simp [s,hz])).symm)

variable [IsArtinianRing R]

/-- The wall-injectivity criterion of A′ in the real projective space. -/
theorem isEFinite_iff_wall_inj :
    IsEFinite R ↔ ∀ X Y : FGModuleCat.{u} R, IsBrick X → IsBrick Y →
      realStabilityWall k X = realStabilityWall k Y → Nonempty (X ≅ Y) := by
  rw [isEFinite_iff_integral_semistability_locus_injective k]
  simp only [realStabilityWall_eq_iff_integral]

end EFiniteCharacterizations
