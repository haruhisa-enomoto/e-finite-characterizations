module

public import EFiniteCharacterizations.Stability.OppositeAlgebra
public import EFiniteCharacterizations.Stability.PolynomialBrickGrowth
public import EFiniteCharacterizations.LinearAlgebra.NormalizedWeightPatterns

/-!
# Explicit polynomial bound on cumulative brick counts

Second assertion of Theorem 5.2 (`thm:walls`): for an E-finite algebra of rank
`n ≥ 2` over any field, the number of isomorphism classes of bricks of composition
length at most `m` is at most `2(n - 1)(m + 1)^{n(n - 1)}`
(`sharpBrickGrowth_of_isEFinite`, `right_brick_count_le_of_isEFinite`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]
variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
theorem sharpBrickGrowth_of_isEFinite (h : IsEFinite R) (r m : ℕ)
    (hr : (simpleIsomorphismClasses R).ncard = r + 2) :
    (bricksOfLengthLE (R := R) m).ncard ≤ 2 * (r + 1) * (m + 1) ^ ((r + 2) * (r + 1)) := by
  classical
  obtain ⟨_,_,hpoly⟩ := polynomialBrickGrowth_of_isEFinite k h
  let B := bricksOfLengthLE (R := R) m
  let := (hpoly m).1.fintype
  choose X he hb hl using fun x : B ↦ x.property
  choose g hg using fun x : B ↦ exists_projective_weight_stable_of_isEFinite k h (hb x)
  let w (x : B) := projectiveClassWeight k (g x)
  obtain ⟨S,hS,hm⟩ := exists_length_bounded_class_cover (R := R) k m
  let N := (m + 1) ^ (r + 2)
  have hN : S.card ≤ N := by simpa only [N,hr] using hS
  let cls (x : B) := GrothendieckGroup.of (X x)
  have hf (z) (_hz : z ∈ S) : (Finset.univ.filter fun x : B ↦ cls x = z).card ≤ 2 * (r + 1) * N ^ r := by
    let F := Finset.univ.filter fun x : B ↦ cls x = z
    by_cases hn : F.Nonempty
    · obtain ⟨a,ha⟩ := hn
      have hc (x : F) : cls x.val = z := (Finset.mem_filter.mp x.property).2
      have hz (t : ℤ) (ht : t • z = 0) : t = 0 := by
        rw [← hc ⟨a,ha⟩] at ht
        have hh := congrArg (FGModuleCat.lengthWeight R) ht
        change FGModuleCat.lengthWeight R (t • GrothendieckGroup.of (X a)) = _ at hh
        rw [map_zsmul, map_zero, zsmul_eq_mul] at hh
        have hlen : FGModuleCat.lengthWeight R (GrothendieckGroup.of (X a)) = (FGModuleCat.moduleLength (X a) : ℤ) := FGModuleCat.lengthWeight_eval _
        rw [hlen] at hh
        exact (mul_eq_zero.mp hh).resolve_right (by exact_mod_cast mt (FGModuleCat.moduleLength_eq_zero_iff_isZero _).1 (hb a).1)
      have st (x : F) (u : Weight (FGModuleCat.{u} R)) (hu : u z = 0)
          (hs : ∀ i : S, w x.val i.val < 0 → u i.val < 0) : u.IsStable (X x.val) := by
        refine ⟨(hb x.val).1, ?_, fun {Y} f hf hy hi ↦ ?_⟩
        · simpa only [Weight.eval, ← hc x] using hu
        · let j : S := ⟨_,hm Y ((FGModuleCat.moduleLength_lt_of_mono f hi).le.trans (hl x.val))⟩
          exact hs j ((hg x.val).2.2 f hy hi)
      have hcard := card_disjoint_weight_systems_le (X := ↥F) (fun i : S ↦ i.val) z r N hz
        (by simpa using hN) (Nat.pow_pos (Nat.succ_pos _)) (fun p s hi ↦ by
          simpa [hr] using card_le_simple_count_of_independent_classes k hi)
        (fun x ↦ w x.val) (fun x ↦ by rw [← hc x]; exact (hg x.val).2.1) (by
          intro x y u hu hx hy
          obtain ⟨f,hf⟩ := equalClassHom_of_isEFinite k h (X x.val) (X y.val)
            ((hc x).trans (hc y).symm) (FGModuleCat.class_ne_zero (hb x.val).1)
          have := Weight.isIso_of_nonzero (st x u hu hx) (st y u hu hy) f hf
          exact Subtype.ext (Subtype.ext ((he x.val).symm.trans ((congr_toSkeleton_of_iso (asIso f)).trans (he y.val)))))
      simpa only [Fintype.card_coe] using hcard
    · change F.card ≤ _
      simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  have hcount := Finset.card_le_mul_card_image_of_maps_to (s := Finset.univ) (f := cls)
    (fun x _ ↦ hm (X x) (hl x)) _ hf
  calc
    B.ncard ≤ 2 * (r + 1) * N ^ r * S.card := by simpa using hcount
    _ ≤ 2 * (r + 1) * N ^ r * N := Nat.mul_le_mul_left _ hN
    _ = _ := by rw [mul_assoc, ← pow_succ, ← pow_mul]

include k in
omit [IsNoetherianRing R] [IsArtinianRing R] in
/-- **Theorem 5.2 (explicit bound):** For an E-finite algebra of rank `n ≥ 2`, at most
`2(n - 1)(m + 1)^{n(n - 1)}` isomorphism classes of right bricks have composition length `≤ m`. -/
theorem right_brick_count_le_of_isEFinite (h : IsEFinite R) (m : ℕ) :
    let n := (simpleIsomorphismClasses Rᵐᵒᵖ).ncard
    2 ≤ n → (bricksOfLengthLE (R := Rᵐᵒᵖ) m).ncard ≤ 2 * (n - 1) * (m + 1) ^ (n * (n - 1)) := by
  intro n hn
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  have he : n = (n - 2) + 2 := by omega
  have hsub : n - 1 = (n - 2) + 1 := by omega
  have hd := sharpBrickGrowth_of_isEFinite k ((isEFinite_iff_opposite k).1 h) (n - 2) m he
  simpa only [← he, ← hsub] using hd

end EFiniteCharacterizations
