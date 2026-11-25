module

public import EFiniteCharacterizations.LargeModules.GenericBrick
public import EFiniteCharacterizations.Stability.RealWalls
public import EFiniteCharacterizations.Subcategories.TorsionSeparation
public import EFiniteCharacterizations.Presentations.ProjectiveRankBound
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Separation of the finite quotients and submodules of a generic brick -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]

theorem IsGenericBrick.quotient_submodule_hom_zero {G : ModuleCat.{u} R}
    (hG : IsGenericBrick k G) {Q N : FGModuleCat.{u} R}
    (q : G ⟶ Q.obj) (hq : Function.Surjective q.hom)
    (i : N.obj ⟶ G) (hi : Function.Injective i.hom) (f : Q ⟶ N) : f = 0 := by
  let p := i.hom.comp (f.hom.hom.comp q.hom)
  have hp : p = 0 := by
    by_contra hn
    have hs : Function.Surjective i.hom := fun x ↦ by
      obtain ⟨y,hy⟩ := (hG.invertible p hn).2 x
      exact ⟨_,hy⟩
    have : Module.Finite k (N.obj : Type u) := Module.Finite.trans R _
    exact hG.infinite (Module.Finite.of_surjective (i.hom.restrictScalars k) hs)
  ext x
  obtain ⟨y,rfl⟩ := hq x
  apply hi
  exact (LinearMap.congr_fun hp y).trans i.hom.map_zero.symm

variable [IsNoetherianRing R]

/-- A nonempty collection of homogeneous linear inequalities in finite
dimension has a nonzero weak solution if every finite subcollection has a
strict solution. -/
private theorem exists_nonzero_weak_solution {V : Type*} [AddCommGroup V] [Module ℝ V]
    [Module.Finite ℝ V] {I : Type*} [Nonempty I] (L : I → V →ₗ[ℝ] ℝ)
    (h : ∀ s : Finset I, ∃ x, ∀ i ∈ s, L i x < 0) :
    ∃ x ≠ 0, ∀ i, L i x ≤ 0 := by
  classical
  let e := (Module.finBasis ℝ V).equivFun
  let F i := (L i).comp e.symm.toLinearMap
  let T i := {y | F i y ≤ 0}
  have hc i : IsClosed (T i) := isClosed_le (F i).continuous_of_finiteDimensional continuous_const
  obtain ⟨y,hy,ht⟩ := (isCompact_sphere (0 : Fin (Module.finrank ℝ V) → ℝ) 1).inter_iInter_nonempty T hc (by
    intro s
    let j := Classical.arbitrary I
    obtain ⟨x,hx⟩ := h (insert j s)
    have hne : e x ≠ 0 := by
      intro hz
      have := hx j (Finset.mem_insert_self ..)
      simp [e.map_eq_zero_iff.mp hz] at this
    let c := ‖e x‖⁻¹
    refine ⟨c • e x, ?_, Set.mem_iInter.mpr fun i ↦ Set.mem_iInter.mpr fun hi ↦ ?_⟩
    · simpa [Metric.mem_sphere, dist_zero_right, norm_smul, c, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)
    · change F i (c • e x) ≤ 0
      rw [map_smul]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _))
        (by simpa [F] using (hx i (Finset.mem_insert_of_mem hi)).le))
  refine ⟨e.symm y, fun hz ↦ ?_, fun i ↦ (Set.mem_iInter.mp ht i : y ∈ T i)⟩
  have : y = 0 := e.symm.map_eq_zero_iff.mp hz
  simp [this] at hy

/-- Over an algebra satisfying equal-class Hom, a hypothetical generic brick
admits a nonzero real projective weight nonnegative on every finite quotient
and nonpositive on every finite submodule. -/
theorem IsGenericBrick.exists_separating_real_weight [IsArtinianRing R]
    {G : ModuleCat.{u} R} (hG : IsGenericBrick k G) (h : EqualClassHom (FGModuleCat.{u} R)) :
    ∃ v : RealProjectiveSpace R, v ≠ 0 ∧
      (∀ (Q : FGModuleCat.{u} R) (q : G ⟶ Q.obj), Function.Surjective q.hom →
        0 ≤ realEulerEvaluation k (GrothendieckGroup.of Q) v) ∧
      ∀ (N : FGModuleCat.{u} R) (i : N.obj ⟶ G), Function.Injective i.hom →
        realEulerEvaluation k (GrothendieckGroup.of N) v ≤ 0 := by
  classical
  let I := {Q : FGModuleCat.{u} R // ¬ IsZero Q ∧ ∃ q : G ⟶ Q.obj, Function.Surjective q.hom}
  let J := {N : FGModuleCat.{u} R // ¬ IsZero N ∧ ∃ i : N.obj ⟶ G, Function.Injective i.hom}
  have : Nontrivial G := not_subsingleton_iff_nontrivial.mp fun _ ↦ hG.infinite inferInstance
  obtain ⟨x,hx⟩ := exists_ne (0 : G)
  let U := R ∙ x
  let N := FGModuleCat.of R U
  have hn : ¬ IsZero N := by
    intro hz
    have hs := (FGModuleCat.isZero_iff_subsingleton _).mp hz
    exact hx (congrArg Subtype.val (hs.elim (⟨x, Submodule.mem_span_singleton_self x⟩ : U) 0))
  have : Nonempty (I ⊕ J) := ⟨.inr ⟨N, hn, ModuleCat.ofHom U.subtype, Subtype.val_injective⟩⟩
  let L : I ⊕ J → RealProjectiveSpace R →ₗ[ℝ] ℝ :=
    Sum.elim (fun i ↦ -realEulerForm k (GrothendieckGroup.of i.val))
      (fun j ↦ realEulerForm k (GrothendieckGroup.of j.val))
  have := (realProjectiveSpace_rank_bound (R := R) k).1
  obtain ⟨v,hv,hs⟩ := exists_nonzero_weak_solution L (by
    intro s
    let X (i : ↥s.toLeft) := i.val.val
    let Y (j : ↥s.toRight) := j.val.val
    obtain ⟨g,hx,hy⟩ := exists_weight_separating_orthogonal k h X Y
      (fun i ↦ i.val.property.1) (fun j ↦ j.val.property.1) (fun i j f ↦ by
        obtain ⟨q,hq⟩ := i.val.property.2
        obtain ⟨b,hb⟩ := j.val.property.2
        exact hG.quotient_submodule_hom_zero k q hq b hb f)
    refine ⟨realProjectiveClass R g, ?_⟩
    rintro (i | j) hm
    · change -realEulerEvaluation k _ _ < 0
      rw [realEulerEvaluation_integral, neg_lt_zero]
      exact_mod_cast hx ⟨i, Finset.mem_toLeft.mpr hm⟩
    · change realEulerEvaluation k _ _ < 0
      rw [realEulerEvaluation_integral]
      exact_mod_cast hy ⟨j, Finset.mem_toRight.mpr hm⟩)
  have hzero (X : FGModuleCat.{u} R) (hz : IsZero X) :
      realEulerEvaluation k (GrothendieckGroup.of X) v = 0 := by
    rw [GrothendieckGroup.of_isZero hz]
    clear hs hv
    induction v using TensorProduct.inductionOn with
    | tmul => simp [realEulerEvaluation_tmul]
    | add a b ha hb => simp [ha,hb]
  refine ⟨v,hv,fun Q q hq ↦ ?_,fun M i hi ↦ ?_⟩
  · by_cases hz : IsZero Q
    · exact (hzero Q hz).ge
    exact neg_nonpos.mp (hs (.inl ⟨Q,hz,q,hq⟩))
  · by_cases hz : IsZero M
    · exact (hzero M hz).le
    exact hs (.inr ⟨M,hz,i,hi⟩)

end EFiniteCharacterizations
