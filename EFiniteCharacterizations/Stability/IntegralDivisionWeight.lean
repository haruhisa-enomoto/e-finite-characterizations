module

public import EFiniteCharacterizations.LinearAlgebra.RationalProjection
public import EFiniteCharacterizations.Stability.DivisionEulerSeparation
public import EFiniteCharacterizations.LargeModules.GenericBrickSeparation

/-! # Integral weights for generic bricks over their endomorphism rings -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

/-- Integral coefficients preserving all signs on a finite box of dimension
vectors, including the sign of a nonzero coefficient of the original weight. -/
private theorem integral_box_weight {I : Type*} [Fintype I] (a : I → ℝ) (m : I → ℕ)
    (ha : a ≠ 0) :
    ∃ c : I → ℤ, c ≠ 0 ∧ ∀ b : I → ℕ, (∀ i, b i ≤ m i) →
      (∑ i, a i * (b i : ℝ) ≤ 0 → ∑ i, c i * (b i : ℤ) ≤ 0) ∧
      (∑ i, a i * (b i : ℝ) = 0 → ∑ i, c i * (b i : ℤ) = 0) := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, a j ≠ 0 := Function.ne_iff.mp ha
  let val (b : ∀ i, Fin (m i + 1)) := ∑ i, a i * (b i : ℕ)
  let s := insert |a j| (Finset.univ.image fun b ↦ -val b)
  obtain ⟨f,hf⟩ := exists_rat_linear_pos_on_finset (s.filter (0 < ·))
    (fun _ hx ↦ (Finset.mem_filter.mp hx).2)
  have hfj : f (a j) ≠ 0 := by
    have hpos := hf |a j| (Finset.mem_filter.mpr ⟨Finset.mem_insert_self ..,abs_pos.mpr hj⟩)
    rcases le_total 0 (a j) with h | h
    · rw [abs_of_nonneg h] at hpos
      exact hpos.ne'
    · rw [abs_of_nonpos h,map_neg] at hpos
      exact (neg_pos.mp hpos).ne
  obtain ⟨d,c,hd,hc⟩ := Farkas.common_denominator (fun i ↦ f (a i))
  refine ⟨c, fun hz ↦ ?_, fun b hb ↦ ?_⟩
  · have h := hc j
    rw [hz] at h
    exact (mul_ne_zero hd.ne' hfj) (by simpa using h.symm)
  · let x := ∑ i, a i * (b i : ℝ)
    have he : (↑(∑ i, c i * (b i : ℤ)) : ℚ) = d * f x := by
      dsimp [x]
      rw [map_sum,Finset.mul_sum]
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      rw [hc]
      have h := map_nsmul f (b i) (a i)
      simpa [nsmul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using congrArg (d * ·) h.symm
    constructor
    · intro hx
      have hf' : f x ≤ 0 := by
        rcases (show x ≤ 0 from hx).eq_or_lt with heq | hlt
        · simp [heq]
        · let b' (i : I) : Fin (m i + 1) := ⟨b i,Nat.lt_succ_of_le (hb i)⟩
          have hmem : -x ∈ s := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b',Finset.mem_univ _,rfl⟩)
          have hpos := hf (-x) (Finset.mem_filter.mpr ⟨hmem,neg_pos.mpr hlt⟩)
          rw [map_neg] at hpos
          exact (neg_pos.mp hpos).le
      exact_mod_cast he.trans_le (mul_nonpos_of_nonneg_of_nonpos hd.le hf')
    · intro hx
      rw [show x = 0 from hx,map_zero,mul_zero] at he
      exact_mod_cast he

variable {R : Type u} [Ring R] (D : Type u) [DivisionRing D]

/-- Semistability over the commuting division ring, tested on invariant
submodules via injective maps respecting both actions. -/
def DivisionSemistable (g : ProjectiveClass R) (M : ModuleCat.{u} R)
    [Module D M] [SMulCommClass R D M] [Module.Finite D M] : Prop :=
  divisionEuler D M g = 0 ∧ ∀ (N : ModuleCat.{u} R) [Module D N] [SMulCommClass R D N]
    [Module.Finite D N] (i : N →ₗ[R] M), Function.Injective i →
    (∀ (d : D) x, i (d • x) = d • i x) → divisionEuler D N g ≤ 0

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

/-- A simultaneously separating real weight gives a nonzero integral
division-ring semistability weight for a generic brick. -/
theorem IsGenericBrick.exists_divisionSemistable {M : ModuleCat.{u} R} (hM : IsGenericBrick k M)
    (hR : IsEFinite R) : letI := hM.divisionRing k; letI := hM.endofinite
      ∃ g : ProjectiveClass R, g ≠ 0 ∧ DivisionSemistable (Module.End R M) g M := by
  classical
  let D := Module.End R M
  let : DivisionRing D := hM.divisionRing k
  have : Module.Finite D M := hM.endofinite
  let := IsNoetherianRing.of_finite k R
  let := IsArtinianRing.of_finite k R
  obtain ⟨v,hv,hq,hi⟩ := hM.exists_separating_real_weight k (equalClassHom_of_isEFinite k hR)
  let s := Set.range (realProjectiveClass R ∘ ProjectiveClass.of)
  have hs : ⊤ ≤ Submodule.span ℝ s := (span_realProjectiveClasses R).ge
  let I := (linearIndepOn_empty ℝ (id : RealProjectiveSpace R → RealProjectiveSpace R)).extend (Set.empty_subset s)
  let b : Module.Basis I ℝ (RealProjectiveSpace R) := Module.Basis.ofSpan hs
  have := (realProjectiveSpace_rank_bound (R := R) k).1
  have : Finite I := Module.Finite.finite_basis b
  let := Fintype.ofFinite I
  have hP (t : I) : ∃ P : FiniteProjective R, realProjectiveClass R (ProjectiveClass.of P) = b t :=
    Module.Basis.ofSpan_subset hs (Set.mem_range_self t)
  choose P hP using hP
  let a := b.equivFun v
  have ha : a ≠ 0 := fun hz ↦ hv (b.equivFun.map_eq_zero_iff.mp hz)
  have eval (N : FGModuleCat.{u} R) :
      realEulerEvaluation k (GrothendieckGroup.of N) v = ∑ t, a t * homFinrank k (P t).val N := by
    conv_lhs => rw [← b.sum_repr v,map_sum]
    apply Finset.sum_congr rfl
    intro t _
    let := (P t).property
    rw [realEulerEvaluation_smul,← hP t,realEulerEvaluation_integral,projectiveClassWeight_of]
    have h := projectiveHomWeight_eval k (P t).val N
    change _ * (((projectiveHomWeight k (P t).val).eval N : ℤ) : ℝ) = _
    rw [h,Int.cast_natCast]
    rfl
  let m t := Module.finrank D ((P t).val →ₗ[R] M)
  obtain ⟨c,hc,hbox⟩ := integral_box_weight a m ha
  let g := ∑ t, c t • ProjectiveClass.of (P t)
  have hg : g ≠ 0 := by
    intro hz
    have he := congrArg (realProjectiveClass R) hz
    simp only [g,map_sum,map_zsmul,map_zero,hP] at he
    apply hc
    funext t
    have h := congrArg (fun w ↦ b.repr w t) he
    simpa [map_sum,map_zsmul, Finsupp.finsetSum_apply, Finsupp.single_apply] using h
  have hsub (N : ModuleCat.{u} R) [Module D N] [SMulCommClass R D N] [Module.Finite D N]
      (i : N →ₗ[R] M) (hinj : Function.Injective i) :
      ∑ t, a t * Module.finrank D ((P t).val →ₗ[R] N) ≤ 0 := by
    apply divisionEuler_real_nonpos_of_submodule_tests k D N P a hR
    intro X j hj
    rw [← eval]
    exact hi X (j ≫ ModuleCat.ofHom i) (hinj.comp hj)
  have htotal := divisionEuler_real_nonneg_of_quotient_tests k D M P a hR
    (fun X q hs ↦ (hq X q hs).trans_eq (eval X))
  refine ⟨g,hg,?_,?_⟩
  · have he := (hbox m (fun _ ↦ le_rfl)).2 (le_antisymm (hsub M LinearMap.id Function.injective_id) htotal)
    simpa only [g,map_sum,map_zsmul,divisionEuler_of,zsmul_eq_mul,Int.cast_id,m] using he
  · intro N _ _ _ i hinj hlin
    let dim t := Module.finrank D ((P t).val →ₗ[R] N)
    have hle (t) : dim t ≤ m t := by
      let e : ((P t).val →ₗ[R] N) →ₗ[D] ((P t).val →ₗ[R] M) :=
        { toFun f := i.comp f, map_add' := fun _ _ ↦ LinearMap.comp_add _ _ _,
          map_smul' := fun _ _ ↦ LinearMap.ext fun _ ↦ hlin _ _ }
      have := finite_hom_over_division D M (P t).val
      exact LinearMap.finrank_le_finrank_of_injective (f := e) fun f g h ↦
        LinearMap.ext fun x ↦ hinj (LinearMap.congr_fun h x)
    have he := (hbox dim hle).1 (hsub N i hinj)
    simpa only [g,map_sum,map_zsmul,divisionEuler_of,zsmul_eq_mul,Int.cast_id,dim] using he

end EFiniteCharacterizations
