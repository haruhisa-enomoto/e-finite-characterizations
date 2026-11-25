module

public import EFiniteCharacterizations.Stability.SubmoduleProfiles
public import EFiniteCharacterizations.Stability.EndInvariantSubmodules
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.TensorProduct.Lift

/-! # The real submodule polytope and its supporting inequalities -/

@[expose] public section

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R]

abbrev RealModuleClassSpace (R : Type u) [Ring R] [IsNoetherianRing R] :=
  ℝ ⊗[ℤ] GrothendieckGroup (FGModuleCat.{u} R)

/-- The convex hull of the ordinary submodule profile in the real Grothendieck group. -/
noncomputable def submodulePolytope (M : FGModuleCat.{u} R) : Set (RealModuleClassSpace R) :=
  convexHull ℝ ((fun z ↦ (1 : ℝ) ⊗ₜ[ℤ] z) '' submoduleProfile M)

def BrickPolytopeInjective (R : Type u) [Ring R] [IsNoetherianRing R] : Prop :=
  ∀ X Y : FGModuleCat.{u} R, IsBrick X → IsBrick Y → submodulePolytope X = submodulePolytope Y →
    Nonempty (X ≅ Y)

theorem brickProfileInjective_of_polytopeInjective (h : BrickPolytopeInjective R) :
    BrickProfileInjective R :=
  fun X Y hx hy he ↦ h X Y hx hy (by simp only [submodulePolytope, he])

/-- An integral upper bound valid throughout the profile is valid at every
integral point of its convex hull. -/
theorem le_of_mem_submodulePolytope {X : FGModuleCat.{u} R}
    (θ : Weight (FGModuleCat.{u} R)) (b : ℤ) (hb : ∀ z ∈ submoduleProfile X, θ z ≤ b)
    {z : GrothendieckGroup (FGModuleCat.{u} R)} (hz : (1 : ℝ) ⊗ₜ[ℤ] z ∈ submodulePolytope X) :
    θ z ≤ b := by
  let w := (((Int.castAddHom ℝ).comp θ).toIntLinearMap).liftBaseChange ℝ
  have bound : submodulePolytope X ⊆ {v | w v ≤ (b : ℝ)} := by
    apply convexHull_min _ (convex_halfSpace_le w.isLinear b)
    rintro _ ⟨a, ha, rfl⟩
    simpa [w] using (show (θ a : ℝ) ≤ b by exact_mod_cast hb a ha)
  have H : w ((1 : ℝ) ⊗ₜ[ℤ] z) ≤ b := bound hz
  simpa [w] using H

private theorem mem_hull_of_profile {X : FGModuleCat.{u} R} {z} (h : z ∈ submoduleProfile X) :
    (1 : ℝ) ⊗ₜ[ℤ] z ∈ submodulePolytope X :=
  subset_convexHull ℝ _ ⟨z, h, rfl⟩

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
theorem class_eq_of_submodulePolytope_eq {X Y : FGModuleCat.{u} R}
    (he : submodulePolytope X = submodulePolytope Y) : GrothendieckGroup.of X = GrothendieckGroup.of Y := by
  obtain ⟨Q, hQ⟩ := exists_injective_projective_hom_coordinates (R := R) k
  apply hQ
  funext i
  let w := projectiveClassWeight k (ProjectiveClass.of (Q i))
  have bound (M : FGModuleCat.{u} R) : ∀ z ∈ submoduleProfile M, w z ≤ w (GrothendieckGroup.of M) := by
    rintro _ ⟨U, f, hf, rfl⟩
    let := (Q i).property
    change (projectiveClassWeight k (ProjectiveClass.of (Q i))).eval U ≤
      (projectiveClassWeight k (ProjectiveClass.of (Q i))).eval M
    rw [projectiveClassWeight_of, projectiveHomWeight_eval, projectiveHomWeight_eval]
    have := finiteModuleHom_isFinite k (Q i).val M
    simp only [homFinrank_eq_finrank]
    exact_mod_cast LinearMap.finrank_le_finrank_of_injective (f := Linear.rightComp k (Q i).val f)
      (fun a b hab ↦ (cancel_mono f).1 hab)
  exact le_antisymm (le_of_mem_submodulePolytope w _ (bound Y)
    (he ▸ mem_hull_of_profile (self_mem_submoduleProfile X)))
    (le_of_mem_submodulePolytope w _ (bound X) (he.symm ▸ mem_hull_of_profile (self_mem_submoduleProfile Y)))

/-- Submodule classes arising from submodules preserved by every endomorphism. -/
def invariantSubmoduleProfile (M : FGModuleCat.{u} R) : Set (GrothendieckGroup (FGModuleCat.{u} R)) :=
  {c | ∃ U : Submodule R (M.obj : Type u), EndInvariant (M := M) U ∧ GrothendieckGroup.of (FGModuleCat.of R U) = c}

theorem invariantSubmoduleProfile_subset (M : FGModuleCat.{u} R) :
    invariantSubmoduleProfile M ⊆ submoduleProfile M := by
  rintro _ ⟨U, _, rfl⟩
  exact ⟨_, FGModuleCat.ofHom U.subtype, (FGModuleCat.mono_iff_injective _).2 Subtype.val_injective, rfl⟩

include k in
theorem submodulePolytope_eq_invariant_hull {M : FGModuleCat.{u} R} (hb : IsBrick M) :
    submodulePolytope M = convexHull ℝ ((fun z ↦ (1 : ℝ) ⊗ₜ[ℤ] z) '' invariantSubmoduleProfile M) := by
  classical
  refine le_antisymm (convexHull_min ?_ (convex_convexHull ..)) (convexHull_mono
    (Set.image_mono (invariantSubmoduleProfile_subset M)))
  rintro _ ⟨z, ⟨U, i, hi, rfl⟩, rfl⟩
  let G := GrothendieckGroup (FGModuleCat.{u} R)
  let z : G := GrothendieckGroup.of U
  let v := TensorProduct.mk ℤ ℝ G 1
  let S := invariantSubmoduleProfile M
  have := Module.Finite.trans (R := k) R (M.obj : Type u)
  have : Finite S := (finite_classes_of_groundFinrank_le (R := R) k (Module.finrank k (M.obj : Type u))).subset (by
    intro c hc
    obtain ⟨V, f, hf, hV⟩ := invariantSubmoduleProfile_subset M hc
    exact ⟨V, LinearMap.finrank_le_finrank_of_injective (f := f.hom.hom.restrictScalars k)
      ((FGModuleCat.mono_iff_injective f).1 hf), hV⟩)
  let := Fintype.ofFinite S
  obtain ⟨n, q, hq⟩ := exists_injective_projective_weight_coordinates (R := R) k
  rcases Farkas.integral_separation_of_injective_coordinates (fun t ↦ projectiveClassWeight k (q t))
    hq (fun _ : Empty ↦ (0 : G)) (fun c : S ↦ c.val - z) with ⟨w, _, hw⟩ | ⟨a, _, ha, hp, he⟩
  · let θ := ∑ t, w t • projectiveClassWeight k (q t)
    obtain ⟨V, hv, hmax⟩ := exists_endInvariant_weight_maximizer k hb θ
    let c : S := ⟨_, V, hv, rfl⟩
    have hlt : θ (c.val - z) < 0 := hw c
    rw [map_sub, sub_neg] at hlt
    let e := LinearEquiv.ofInjective i.hom.hom ((FGModuleCat.mono_iff_injective i).1 hi)
    exact False.elim (hlt.not_ge ((θ.eval_eq_of_isIso e.toFGModuleCatIso.hom).trans_le (hmax i.hom.hom.range)))
  · have he' : ∑ c : S, a c • c.val = (∑ c, a c) • z := by
      simpa only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, Finset.univ_eq_empty,
        Finset.sum_empty, zero_smul, sub_eq_zero] using he
    let A : ℝ := ∑ c, (a c : ℝ)
    have hp' : 0 < A := by dsimp [A]; exact_mod_cast hp
    change v z ∈ convexHull ℝ (v '' S)
    have hsum : (∑ c : S, (a c : ℝ) • v c.val) = A • v z := by
      have h := congrArg v he'
      simpa only [map_sum, map_zsmul, A, ← Int.cast_sum, Int.cast_smul_eq_zsmul] using h
    have h := (convex_convexHull ℝ (v '' S)).sum_mem
      (fun (c : S) (_ : c ∈ Finset.univ) ↦ mul_nonneg (inv_nonneg.mpr hp'.le) (show 0 ≤ (a c : ℝ) by exact_mod_cast ha c))
      (by rw [← Finset.mul_sum]; exact inv_mul_cancel₀ hp'.ne')
      (fun (c : S) _ ↦ subset_convexHull ℝ _ (show v c.val ∈ v '' S from ⟨_, c.property, rfl⟩))
    simpa only [mul_smul, ← Finset.smul_sum, hsum, inv_smul_smul₀ hp'.ne'] using h

variable [IsArtinianRing R]

include k in
theorem brickPolytopeInjective_of_isEFinite (h : IsEFinite R) : BrickPolytopeInjective R := by
  intro X Y hx hy he
  apply iso_of_same_integral_semistability_locus k h hx hy
  intro g
  let θ := projectiveClassWeight (R := R) k g
  have transfer {M N : FGModuleCat.{u} R} (e : submodulePolytope M = submodulePolytope N)
      (hs : θ.IsSemistable M) : θ.IsSemistable N := by
    rw [semistable_iff_profile] at hs ⊢
    refine ⟨(class_eq_of_submodulePolytope_eq k e) ▸ hs.1, fun z hz ↦ ?_⟩
    exact le_of_mem_submodulePolytope θ 0 hs.2 (e.symm ▸ mem_hull_of_profile hz)
  exact ⟨transfer he, transfer he.symm⟩

include k in
theorem isEFinite_iff_poly_inj_of_infinite [Infinite k] : IsEFinite R ↔ BrickPolytopeInjective R :=
  ⟨brickPolytopeInjective_of_isEFinite k, fun h ↦ (isEFinite_iff_prof_inj k).2
    (brickProfileInjective_of_polytopeInjective h)⟩

omit [IsArtinianRing R] in
/-- Over a finite field the exponential witness family contains two distinct
bricks of one weight with the same ordinary (unnormalized) polytope. -/
theorem exists_equalPolytope_stable_pair [Finite k] (hn : ¬ IsEFinite R) :
    ∃ (g : ProjectiveClass R) (X Y : FGModuleCat.{u} R),
      (projectiveClassWeight k g).IsStable X ∧ (projectiveClassWeight k g).IsStable Y ∧
      ¬ Nonempty (X ≅ Y) ∧ submodulePolytope X = submodulePolytope Y := by
  classical
  obtain ⟨P, hp⟩ := FieldExtension.exists_missing_terms k hn
  obtain ⟨G, c, m₀, hc, hg⟩ := FieldExtension.exists_exponential_ground_witnesses k P hp
  obtain ⟨Q, hQ⟩ := exists_injective_projective_hom_coordinates (R := R) k
  let I := ↥(simpleIsomorphismClasses R)
  have : Finite I := finite_simpleIsomorphismClasses k
  let d := Module.finrank k (P.target.obj : Type u)
  let Grid := ∀ i : I, Fin (Module.finrank k ((Q i).val.obj : Type u) * d + 1)
  let := Fintype.ofFinite (Set Grid)
  let Labels := ↥G × Set Grid
  obtain ⟨m, hm, hex⟩ := exists_exp_gt_polynomial_bound (Fintype.card Labels) 2 m₀ hc
  obtain ⟨s, hs, hw⟩ := hg m hm
  choose M g he hG hst hd hr using fun x : s ↦ hw x.val x.property
  let a (x : s) := homFinrank k (M x) (M x)
  let w (i : I) := projectiveClassWeight k (ProjectiveClass.of (Q i))
  let code (x : s) (z : GrothendieckGroup (FGModuleCat.{u} R)) (v : Grid) :=
    ∀ i, w i z = (a x : ℤ) * (v i).val
  let shapes (x : s) := {v : Grid | ∃ z ∈ invariantSubmoduleProfile (M x), code x z v}
  have grid (x : s) {z} (hz : z ∈ invariantSubmoduleProfile (M x)) : ∃ v : Grid, code x z v := by
    obtain ⟨U, hU, rfl⟩ := hz
    choose n hn h using fun i : I ↦ hom_dimension_of_endInvariant k (hst x).isBrick (Q i).val hU
    refine ⟨fun i ↦ ⟨n i, Nat.lt_succ_of_le ((hn i).trans (Nat.mul_le_mul_left _ (hr x)))⟩, fun i ↦ ?_⟩
    let := (Q i).property
    change (projectiveClassWeight k (ProjectiveClass.of (Q i))).eval (FGModuleCat.of R U) = _
    rw [projectiveClassWeight_of, projectiveHomWeight_eval]
    exact_mod_cast h i
  have bound (x : s) : a x < (m + 1)^2 := by
    have h := (homFinrank_le_mul k (M x) (M x)).trans (Nat.mul_le_mul (hd x) (hd x))
    change homFinrank k (M x) (M x) < _
    nlinarith
  let f (x : s) : Labels × Fin ((m + 1)^2) := ((⟨_, hG x⟩, shapes x), ⟨_, bound x⟩)
  have hninj : ¬ Function.Injective f := by
    intro hi
    have hcard : s.card ≤ Fintype.card Labels * (m + 1)^2 := by simpa using Fintype.card_le_of_injective f hi
    exact (not_lt_of_ge (hs.trans (by exact_mod_cast hcard))) hex
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hninj
  have ha : a x = a y := congrArg (fun p : Labels × Fin ((m+1)^2) ↦ p.2.val) hxy
  have hsh : shapes x = shapes y := congrArg (fun p : Labels × Fin ((m+1)^2) ↦ p.1.2) hxy
  have incl {x y : s} (ha : a x = a y) (hsh : shapes x = shapes y) :
      invariantSubmoduleProfile (M x) ⊆ invariantSubmoduleProfile (M y) := by
    intro z hz
    obtain ⟨v, hv⟩ := grid x hz
    have hm : v ∈ shapes x := ⟨z, hz, hv⟩
    obtain ⟨t, ht, hc⟩ := hsh ▸ hm
    have hzt : z = t := hQ (funext fun i ↦ (hv i).trans (ha ▸ (hc i).symm))
    exact hzt ▸ ht
  have hwgt : g x = g y := congrArg (fun p : Labels × Fin ((m+1)^2) ↦ p.1.1.val) hxy
  refine ⟨_, _, _, hst x, hwgt.symm ▸ hst y, ?_, ?_⟩
  · rintro ⟨e⟩
    exact hne (Subtype.ext ((he x).symm.trans ((congr_toSkeleton_of_iso e).trans (he y))))
  · rw [submodulePolytope_eq_invariant_hull k (hst x).isBrick, submodulePolytope_eq_invariant_hull k (hst y).isBrick,
      Set.Subset.antisymm (incl ha hsh) (incl ha.symm hsh.symm)]

include k in
theorem isEFinite_iff_poly_inj : IsEFinite R ↔ BrickPolytopeInjective R := by
  refine ⟨brickPolytopeInjective_of_isEFinite k, fun h ↦ ?_⟩
  rcases finite_or_infinite k with hf | hi
  · by_contra hn
    obtain ⟨_, X, Y, hx, hy, hne, he⟩ := exists_equalPolytope_stable_pair k hn
    exact hne (h X Y hx.isBrick hy.isBrick he)
  · exact (isEFinite_iff_poly_inj_of_infinite k).2 h

end EFiniteCharacterizations
