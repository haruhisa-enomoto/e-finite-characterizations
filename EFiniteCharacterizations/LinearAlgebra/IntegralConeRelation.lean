module

public import EFiniteCharacterizations.LinearAlgebra.RationalProjection
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Integral relations from real two-generator cones -/

@[expose] public section

open scoped TensorProduct nonZeroDivisors

namespace EFiniteCharacterizations

private theorem rat_num_natAbs_eq {r : ℚ} (hr : 0 ≤ r) :
    (r.num.natAbs : ℚ) = r * (r.den : ℚ) := by
  rw [← Int.cast_natCast, Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hr)]
  exact (div_eq_iff (by exact_mod_cast r.den_ne_zero)).mp r.num_div_den

private theorem clear_nonnegative_rat_denominators {a b c : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) :
    ∃ d m n p : ℕ, 0 < p ∧ (m : ℚ) = (d : ℚ) * a ∧ (n : ℚ) = (d : ℚ) * b ∧
      (p : ℚ) = (d : ℚ) * c := by
  let d := a.den * b.den * c.den
  let m := a.num.natAbs * b.den * c.den
  let n := a.den * b.num.natAbs * c.den
  let p := a.den * b.den * c.num.natAbs
  have hm : (m : ℚ) = (d : ℚ) * a := by simp only [m, d, Nat.cast_mul, rat_num_natAbs_eq ha]; ring
  have hn : (n : ℚ) = (d : ℚ) * b := by simp only [n, d, Nat.cast_mul, rat_num_natAbs_eq hb]; ring
  have hp : (p : ℚ) = (d : ℚ) * c := by simp only [p, d, Nat.cast_mul, rat_num_natAbs_eq hc.le]; ring
  have hd : 0 < d := Nat.mul_pos (Nat.mul_pos a.den_pos b.den_pos) c.den_pos
  have hp' : (0 : ℚ) < (p : ℚ) := hp ▸ mul_pos (by exact_mod_cast hd) hc
  exact ⟨d, m, n, p, by exact_mod_cast hp', hm, hn, hp⟩

/-- A real nonnegative two-generator relation between integral classes
becomes a relation with natural coefficients after multiplication. Any
torsion in the group of classes is killed by an additional positive factor. -/
theorem exists_nat_relation_of_real_tensor_relation {G : Type*} [AddCommGroup G]
    (x y z : G) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ⊗ₜ[ℤ] x + b ⊗ₜ[ℤ] y = (1 : ℝ) ⊗ₜ[ℤ] z) :
    ∃ m n p : ℕ, 0 < p ∧ m • x + n • y = p • z := by
  obtain ⟨f, hf₁, hfa, hfb⟩ := exists_rat_linear_nonneg_pair ha hb
  let L := TensorProduct.map (f.restrictScalars ℤ) (LinearMap.id : G →ₗ[ℤ] G)
  have hq : (f a ⊗ₜ[ℤ] x) + (f b ⊗ₜ[ℤ] y) = f 1 ⊗ₜ[ℤ] z := by
    simpa only [L, map_add, TensorProduct.map_tmul, LinearMap.restrictScalars_apply, LinearMap.id_apply]
      using congrArg L h
  obtain ⟨d, m, n, p, hp, hm, hn, hpc⟩ := clear_nonnegative_rat_denominators hfa hfb hf₁
  have hmul := congrArg (fun v : ℚ ⊗[ℤ] G ↦ (d : ℚ) • v) hq
  simp only [smul_add, TensorProduct.smul_tmul', smul_eq_mul, ← hm, ← hn, ← hpc] at hmul
  have htmul (r : ℕ) (u : G) : (r : ℚ) ⊗ₜ[ℤ] u = (1 : ℚ) ⊗ₜ[ℤ] (r • u) := by
    simpa only [nsmul_eq_mul, mul_one] using TensorProduct.smul_tmul (R := ℤ) r (1 : ℚ) u
  rw [htmul m, htmul n, htmul p, ← TensorProduct.tmul_add] at hmul
  let i := TensorProduct.mk ℤ ℚ G 1
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ) i).1 hmul
  change s.val • (m • x + n • y) = s.val • (p • z) at hs
  have hs₂ : (s.val * s.val) • (m • x + n • y) = (s.val * s.val) • (p • z) := by
    simpa only [mul_smul] using congrArg (fun v : G ↦ s.val • v) hs
  have hpos : 0 < s.val * s.val := mul_self_pos.mpr (nonZeroDivisors.ne_zero s.property)
  let d' := (s.val * s.val).toNat
  have hd' : (d' : ℤ) = s.val * s.val := Int.toNat_of_nonneg hpos.le
  rw [← hd'] at hs₂
  simp only [natCast_zsmul] at hs₂
  have hdp : 0 < d' := by dsimp [d']; omega
  refine ⟨d' * m, d' * n, d' * p, Nat.mul_pos hdp hp, ?_⟩
  simpa only [smul_add, mul_smul] using hs₂

end EFiniteCharacterizations
