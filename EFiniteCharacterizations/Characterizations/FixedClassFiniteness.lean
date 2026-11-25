module

public import EFiniteCharacterizations.Characterizations.HomCharacterizations
public import Mathlib.Data.Set.Finite.Powerset

/-! # Fixed-class finiteness of bricks and stable modules -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

theorem exists_projective_weight_stable_of_isEFinite (h : IsEFinite R)
    {X : FGModuleCat.{u} R} (hX : IsBrick X) :
    ∃ g : ProjectiveClass R, (projectiveClassWeight k g).IsStable X := by
  classical
  let x := toSkeleton X
  let e := fromSkeletonToSkeletonIso X
  have hb : IsBrick ((fromSkeleton _).obj x) := by
    refine ⟨fun hz ↦ hX.1 (hz.of_iso e.symm), fun f hf ↦ ?_⟩
    let b := e.inv ≫ f ≫ e.hom
    have he : e.hom ≫ b ≫ e.inv = f := by simp [b]
    have := hX.2 b (fun hb ↦ hf (by simpa [hb] using he.symm))
    rw [← he]
    infer_instance
  have hs : IsSemibrick (C := FGModuleCat.{u} R) ({x} : Set _) := by
    exact ⟨by simpa [brickClasses] using hb, by simp⟩
  obtain ⟨g, hg⟩ := FamilyExtraction.exists_joint_weight_of_equalClassHom k (equalClassHom_of_isEFinite k h) {x}
    (by simpa using hs)
  exact ⟨g, (hg (show x ∈ ({x} : Finset _) by simp)).of_iso e⟩

include k in
theorem finite_brickClassesOfClass_of_isEFinite (h : IsEFinite R)
    (c : GrothendieckGroup (FGModuleCat.{u} R)) : (brickClassesOfClass c).Finite := by
  classical
  choose M he hc hb using fun x : brickClassesOfClass c ↦ x.property
  let d := ((dimensionWeight (R := R) k) c).toNat
  let D := {a : GrothendieckGroup (FGModuleCat.{u} R) | ∃ U : FGModuleCat.{u} R,
    Module.finrank k (U.obj : Type u) ≤ d ∧ GrothendieckGroup.of U = a}
  have hD : D.Finite := finite_classes_of_groundFinrank_le k d
  have hdim (x : brickClassesOfClass c) : Module.finrank k ((M x).obj : Type u) = d := by
    dsimp [d]
    rw [← hc x]
    change _ = ((dimensionWeight (R := R) k).eval (M x)).toNat
    simp
  let F (x : brickClassesOfClass c) := properSubobjectClasses (M x)
  have memD (x : brickClassesOfClass c) : F x ⊆ D := by
    rintro a ⟨U, i, hi, _, _, rfl⟩
    have : Module.Finite k ((M x).obj : Type u) := Module.Finite.trans R _
    exact ⟨U, (LinearMap.finrank_le_finrank_of_injective (f := i.hom.hom.restrictScalars k)
      ((FGModuleCat.mono_iff_injective i).1 hi)).trans (hdim x).le, rfl⟩
  let f (x : brickClassesOfClass c) : ↥(𝒫 D) := ⟨F x, memD x⟩
  have : Finite ↥(𝒫 D) := hD.powerset
  apply Finite.of_injective f
  intro x y hxy
  have hF : F x = F y := congrArg Subtype.val hxy
  obtain ⟨g, hx⟩ := exists_projective_weight_stable_of_isEFinite k h (hb x)
  have hclass := (hc x).trans (hc y).symm
  have hy : (projectiveClassWeight k g).IsStable (M y) := by
    refine ⟨(hb y).1, ?_, fun {U} i hi hn hp ↦ ?_⟩
    · simpa only [Weight.eval, ← hclass] using hx.2.1
    · have hU : GrothendieckGroup.of U ∈ F y := ⟨U, i, hi, hn, hp, rfl⟩
      obtain ⟨V, j, hj, hV, hj', heq⟩ := hF.symm ▸ hU
      simpa only [Weight.eval, ← heq] using hx.2.2 j hV hj'
  obtain ⟨e⟩ := nonempty_iso_of_isEFinite_of_stable_of_class_eq k h g hx hy hclass
  exact Subtype.ext ((he x).symm.trans ((congr_toSkeleton_of_iso e).trans (he y)))

include k in
theorem isEFinite_iff_finite_brickClassesOfClass [Infinite k] :
    IsEFinite R ↔ ∀ c : GrothendieckGroup (FGModuleCat.{u} R), (brickClassesOfClass c).Finite :=
  ⟨finite_brickClassesOfClass_of_isEFinite k, isEFinite_of_finite_brickClassesOfClass k⟩

theorem isEFinite_iff_finite_stableClassesOfClass [Infinite k] :
    IsEFinite R ↔ ∀ (g : ProjectiveClass R) (c : GrothendieckGroup (FGModuleCat.{u} R)),
      (stableClassesOfClass (projectiveClassWeight k g) c).Finite := by
  refine ⟨fun h g c ↦ (finite_brickClassesOfClass_of_isEFinite k h c).subset
    (stableClassesOfClass_subset_brickClassesOfClass _ _), fun h ↦ ?_⟩
  by_contra hn
  obtain ⟨c, g, hs⟩ := exists_infinite_stableClassesOfClass_at_projectiveWeight_of_not_isEFinite k hn
  exact hs (h g c)

/-- The class with the prescribed multiplicity of each simple module. -/
noncomputable def classOfCompositionVector (d : simpleIsomorphismClasses R → ℕ) :
    GrothendieckGroup (FGModuleCat.{u} R) := by
  classical
  let := (finite_simpleIsomorphismClasses (R := R) k).fintype
  exact ∑ i, d i • GrothendieckGroup.of ((fromSkeleton _).obj i.val)

theorem classOfCompositionVector_injective : Function.Injective (classOfCompositionVector (R := R) k) := by
  classical
  let := (finite_simpleIsomorphismClasses (R := R) k).fintype
  intro a b he
  have hz := sub_eq_zero.mpr he
  unfold classOfCompositionVector at hz
  rw [← Finset.sum_sub_distrib] at hz
  simp only [← natCast_zsmul, ← sub_smul] at hz
  funext i
  exact_mod_cast sub_eq_zero.mp (Fintype.linearIndependent_iff.mp (linearIndependent_simple_classes (R := R) k)
    (fun j ↦ (a j : ℤ) - b j) hz i)

theorem exists_compositionVector_of_module (M : FGModuleCat.{u} R) :
    ∃ d, classOfCompositionVector k d = GrothendieckGroup.of M := by
  classical
  let := (finite_simpleIsomorphismClasses (R := R) k).fintype
  obtain ⟨d, _, hd⟩ := exists_simple_multiplicities k M
  exact ⟨d, hd⟩

/-- Brick-discreteness at every composition vector characterizes E-finiteness
over infinite fields. -/
theorem isEFinite_iff_dim_brick [Infinite k] :
    IsEFinite R ↔ ∀ d : simpleIsomorphismClasses R → ℕ,
      (brickClassesOfClass (classOfCompositionVector k d)).Finite := by
  refine ⟨fun h d ↦ finite_brickClassesOfClass_of_isEFinite k h _, fun h ↦ ?_⟩
  apply (isEFinite_iff_finite_brickClassesOfClass k).2
  intro c
  by_cases hn : (brickClassesOfClass c).Nonempty
  · obtain ⟨_, M, _, hc, _⟩ := hn
    obtain ⟨d, hd⟩ := exists_compositionVector_of_module k M
    exact hd.trans hc ▸ h d
  · rw [Set.not_nonempty_iff_eq_empty.mp hn]
    exact Set.finite_empty

/-- Stable-brick discreteness at every integral weight and composition vector
characterizes E-finiteness over infinite fields. -/
theorem isEFinite_iff_dim_stab [Infinite k] :
    IsEFinite R ↔ ∀ (g : ProjectiveClass R) (d : simpleIsomorphismClasses R → ℕ),
      (stableClassesOfClass (projectiveClassWeight k g) (classOfCompositionVector k d)).Finite := by
  refine ⟨fun h g d ↦ (isEFinite_iff_finite_stableClassesOfClass k).1 h g _, fun h ↦ ?_⟩
  apply (isEFinite_iff_finite_stableClassesOfClass k).2
  intro g c
  by_cases hn : (stableClassesOfClass (projectiveClassWeight k g) c).Nonempty
  · obtain ⟨_, M, _, hc, _⟩ := hn
    obtain ⟨d, hd⟩ := exists_compositionVector_of_module k M
    exact hd.trans hc ▸ h g d
  · rw [Set.not_nonempty_iff_eq_empty.mp hn]
    exact Set.finite_empty

theorem not_isEFinite_iff_infinite_bricks_at_one_vector [Infinite k] :
    ¬ IsEFinite R ↔ ∃ d : simpleIsomorphismClasses R → ℕ,
      (brickClassesOfClass (classOfCompositionVector k d)).Infinite := by
  rw [isEFinite_iff_dim_brick k]
  exact not_forall

end EFiniteCharacterizations
