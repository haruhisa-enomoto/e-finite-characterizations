module

public import EFiniteCharacterizations.Characterizations.FixedClassFiniteness
public import EFiniteCharacterizations.LinearAlgebra.WeightSignPatterns

/-!
# Polynomial growth of bricks of bounded composition length

Theorem 5.2 (`thm:walls`, condition `(poly-brick)` in Theorem A(I)) of the manuscript:
over an arbitrary field, `R` is E-finite if and only if the number of isomorphism
classes of bricks of composition length at most `m` is bounded by a polynomial in `m`
(`isEFinite_iff_poly_brick`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]

def bricksOfLengthLE (m : ℕ) : Set (Skeleton (FGModuleCat.{u} R)) :=
  {x | ∃ X : FGModuleCat.{u} R, toSkeleton X = x ∧ IsBrick X ∧ FGModuleCat.moduleLength X ≤ m}

/-- A polynomial upper bound for cumulative brick counts. -/
def PolynomialBrickGrowth (R : Type u) [Ring R] [IsNoetherianRing R] [IsArtinianRing R] : Prop :=
  ∃ A n : ℕ, ∀ m, (bricksOfLengthLE (R := R) m).Finite ∧
    (bricksOfLengthLE (R := R) m).ncard ≤ A * (m + 1) ^ n

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
theorem polynomialBrickGrowth_of_isEFinite (h : IsEFinite R) : PolynomialBrickGrowth R := by
  classical
  let n := (simpleIsomorphismClasses R).ncard
  let e := n * (n + 1)
  refine ⟨(n + 1) * 2 ^ n, e, fun m ↦ ?_⟩
  obtain ⟨S, hSc, hS⟩ := exists_length_bounded_class_cover (R := R) k m
  let B := bricksOfLengthLE (R := R) m
  choose X he hb hl using fun x : B ↦ x.property
  choose g hg using fun x : B ↦ exists_projective_weight_stable_of_isEFinite k h (hb x)
  let w (x : B) := projectiveClassWeight k (g x)
  let v (i : S) := i.val
  let signs (x : B) := Finset.univ.filter fun i : S ↦ w x i.val < 0
  have hsigns (x : B) : signs x ∈ negativePatterns v := by
    change _ ∈ Finset.univ.filter _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, w x, fun i ↦ by simp [signs,v]⟩
  let f (x : B) : ↥S × ↥(negativePatterns v) :=
    (⟨_, hS (X x) (hl x)⟩, ⟨_, hsigns x⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    have hc : GrothendieckGroup.of (X x) = GrothendieckGroup.of (X y) :=
      congrArg (fun z : ↥S × ↥(negativePatterns v) ↦ z.1.val) hxy
    have hs : signs x = signs y := congrArg (fun z : ↥S × ↥(negativePatterns v) ↦ z.2.val) hxy
    have hy : (w x).IsStable (X y) := by
      refine ⟨(hb y).1, ?_, fun {U} i hi hn hp ↦ ?_⟩
      · simpa only [Weight.eval, ← hc] using (hg x).2.1
      · let j : S := ⟨_, hS U ((FGModuleCat.moduleLength_lt_of_mono i hp).le.trans (hl y))⟩
        have hj : j ∈ signs y := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hg y).2.2 i hn hp⟩
        have hjx : j ∈ signs x := hs.symm ▸ hj
        exact (show w x j.val < 0 from (Finset.mem_filter.mp hjx).2)
    obtain ⟨eq⟩ := nonempty_iso_of_isEFinite_of_stable_of_class_eq k h (g x) (hg x) hy hc
    exact Subtype.ext ((he x).symm.trans ((congr_toSkeleton_of_iso eq).trans (he y)))
  have hfin : Finite B := Finite.of_injective f hf
  let := Fintype.ofFinite B
  refine ⟨hfin, ?_⟩
  have hc : B.ncard ≤ S.card * (negativePatterns v).card := by
    simpa using Fintype.card_le_of_injective f hf
  have hp : (negativePatterns v).card ≤ (n + 1) * (S.card + 1) ^ n := by
    simpa using card_negativePatterns_le v n (fun s hi ↦ by
      simpa using card_le_simple_count_of_independent_classes k hi)
  let K := (m + 1) ^ n
  have hk : 1 ≤ K := Nat.one_le_pow _ _ (by omega)
  have hsk : S.card ≤ K := hSc
  have hstep : S.card + 1 ≤ 2 * K := by omega
  calc
    B.ncard ≤ K * ((n + 1) * (2 * K) ^ n) :=
      hc.trans (Nat.mul_le_mul hsk (hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hstep _))))
    _ = (n + 1) * 2 ^ n * (m + 1) ^ e := by
      simp only [mul_pow, e, ← pow_mul, Nat.mul_add, Nat.mul_one, pow_add, K]
      ring

include k in
theorem isEFinite_iff_poly_brick : IsEFinite R ↔ PolynomialBrickGrowth R := by
  refine ⟨polynomialBrickGrowth_of_isEFinite k, ?_⟩
  rintro ⟨A, n, h⟩
  rcases finite_or_infinite k with hfin | hinf
  · by_contra hn
    obtain ⟨c, m₀, hc, hg⟩ := FieldExtension.exists_exponential_brick_finsets_of_not_isEFinite k hn
    obtain ⟨m, hm, hex⟩ := exists_exp_gt_polynomial_bound A n m₀ hc
    obtain ⟨s, hs, hmem⟩ := hg m hm
    have hsub : (s : Set _) ⊆ bricksOfLengthLE (R := R) m := hmem
    have hcard := (Set.ncard_le_ncard hsub (h m).1).trans (h m).2
    rw [Set.ncard_coe_finset] at hcard
    exact (not_lt_of_ge (hs.trans (by exact_mod_cast hcard))) hex
  · apply isEFinite_of_finite_brickClassesOfClass k
    intro c
    apply (h ((FGModuleCat.lengthWeight R c).toNat)).1.subset
    rintro x ⟨M, he, rfl, hb⟩
    refine ⟨M, he, hb, ?_⟩
    change FGModuleCat.moduleLength M ≤ ((FGModuleCat.lengthWeight R).eval M).toNat
    simp

end EFiniteCharacterizations
