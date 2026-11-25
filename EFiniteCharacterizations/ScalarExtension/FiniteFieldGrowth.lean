module

public import EFiniteCharacterizations.LinearAlgebra.FiniteFieldExtensions
public import EFiniteCharacterizations.ScalarExtension.FinitePresiltingDescent
public import EFiniteCharacterizations.Stability.CommonStableEndolength
public import EFiniteCharacterizations.ScalarExtension.FiniteFieldWitnesses
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Exponential growth from the persistence of a nonpresilting class -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R] [IsArtinianRing R]

include k in
/-- The composition length of a finite module is bounded by its ground dimension. -/
theorem FGModuleCat.moduleLength_le_groundFinrank (M : FGModuleCat.{u} R) :
    moduleLength M ≤ Module.finrank k (M.obj : Type u) := by
  let X := (M.obj : Type u)
  have : Module.Finite k X := Module.Finite.trans R X
  let U : Submodule R X := ⊤
  have h := Submodule.length_le_length_restrictScalars k U
  have hu : Module.length R U = Module.length R X := (LinearEquiv.ofTop U rfl).length_eq
  have hv : Module.length k (U.restrictScalars k) = Module.length k X :=
    (LinearEquiv.ofTop (U.restrictScalars k) (Submodule.restrictScalars_top k R X)).length_eq
  rw [hu, hv, Module.length_eq_finrank] at h
  exact Nat.cast_le.mp ((moduleLength_coe M).trans_le h)

namespace FieldExtension

private theorem square_le_two_pow {n : ℕ} (hn : 4 ≤ n) : n * n ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : 4 ≤ n
    · have hn := ih h
      have hscale := Nat.mul_le_mul_right n h
      rw [pow_succ]
      nlinarith only [hn, hscale, h]
    · have : n = 3 := by omega
      subst n
      decide

variable [Finite k]

/-- The projective terms admit no presilting differential over any finite
extension of the ground field. -/
def NoPresiltingDifferentialAfterFiniteExtension (P : TwoTerm R) : Prop :=
  ∀ (F : Type u) [Field F] [Algebra k F] [Fintype F] [Module.Finite k F],
    ∀ p : (extendTwoTerm k F R P).source ⟶ (extendTwoTerm k F R P).target,
      ¬ ({ extendTwoTerm k F R P with differential := p }).IsPresilting

omit [IsNoetherianRing R] [IsArtinianRing R] in
/-- A missing ground class stays missing on its projective terms after
every finite extension. -/
theorem no_presilting_differential_after_finite_extension (P : TwoTerm R)
    (h : ¬ ∃ Q : TwoTerm R, Q.IsPresilting ∧ Q.projectiveClass = P.projectiveClass) :
    NoPresiltingDifferentialAfterFiniteExtension k P := by
  let _ := Fintype.ofFinite k
  intro F _ _ _ _ p hp
  exact h (exists_presilting_class_of_finite_extension P p hp)

omit [IsNoetherianRing R] [IsArtinianRing R] in
theorem exists_missing_terms (h : ¬ IsEFinite R) :
    ∃ P : TwoTerm R, NoPresiltingDifferentialAfterFiniteExtension k P := by
  obtain ⟨g, hg⟩ := not_forall.mp h
  obtain ⟨P, hP⟩ := ProjectiveClass.exists_twoTerm g
  exact ⟨P, no_presilting_differential_after_finite_extension k P (hP.symm ▸ hg)⟩

omit [IsArtinianRing R] in
/-- A fixed pair of projective terms with no presilting differential over
finite extensions supplies exponentially many stable ground modules up to
each sufficiently large ground-dimension cutoff. -/
theorem exists_exponential_ground_witnesses (P : TwoTerm R)
    (hmissing : NoPresiltingDifferentialAfterFiniteExtension k P) :
    ∃ (G : Finset (ProjectiveClass R)) (c : ℝ) (m₀ : ℕ), 0 < c ∧
      ∀ m ≥ m₀, ∃ s : Finset (Skeleton (FGModuleCat.{u} R)),
        Real.exp (c * m) ≤ s.card ∧
        ∀ x ∈ s, ∃ (M : FGModuleCat.{u} R) (g : ProjectiveClass R),
          toSkeleton M = x ∧ g ∈ G ∧ (projectiveClassWeight k g).IsStable M ∧
          Module.finrank k (M.obj : Type u) ≤ m ∧ endolength k M ≤ Module.finrank k (P.target.obj : Type u) := by
  classical
  obtain ⟨C, G, _, hC⟩ := exists_uniform_ground_witness_bound k P
  let D := max 1 (Module.finrank k (P.target.obj : Type u))
  have hD : 0 < D := (Nat.le_max_left _ _)
  have hD' : 0 < (4 * (D : ℝ)) := by positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let N := max 4 (2 * C)
  refine ⟨G, Real.log 2 / (4 * D), (2 * D) * N, div_pos hlog hD', ?_⟩
  intro m hm
  let n := m / (2 * D)
  have hdiv : 0 < 2 * D := Nat.mul_pos (by decide) hD
  have hn : N ≤ n := (Nat.le_div_iff_mul_le hdiv).2 (by simpa only [Nat.mul_comm N] using hm)
  have hn₄ : 4 ≤ n := (Nat.le_max_left _ _).trans hn
  have hn₁ : 1 ≤ n := by omega
  obtain ⟨F, _, _, hF, hFdeg, hFcard⟩ := exists_finiteFieldExtension k (2 * n) (by omega)
  let _ := Fintype.ofFinite F
  let _ : Module.Finite k F := inferInstance
  obtain ⟨s, hcard, hs⟩ := hC F (hmissing F)
  rw [Fintype.card_eq_nat_card, hFcard, hFdeg] at hcard
  have hmld : 2 * n * D ≤ m := by
    have h := (Nat.le_div_iff_mul_le hdiv).1 (le_refl n)
    exact (by simpa only [n, Nat.mul_assoc, Nat.mul_comm 2 (m / (2 * D)), ← Nat.mul_assoc] using h)
  have hcnt : 2 ^ n ≤ s.card := by
    have h₂ : 2 ≤ Nat.card k := Finite.one_lt_card
    have hCn : C * (2 * n) ≤ 2 ^ n := calc
      C * (2 * n) = (2 * C) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right _ ((Nat.le_max_right _ _).trans hn)
      _ ≤ 2 ^ n := square_le_two_pow hn₄
    apply Nat.le_of_mul_le_mul_left (c := 2 ^ n) _ (Nat.pow_pos (by decide))
    calc
      2 ^ n * 2 ^ n = 2 ^ (2 * n) := by rw [two_mul, pow_add]
      _ ≤ (Nat.card k) ^ (2 * n) := Nat.pow_le_pow_left h₂ _
      _ ≤ C * (2 * n) * s.card := hcard
      _ ≤ 2 ^ n * s.card := Nat.mul_le_mul_right _ hCn
  have hmup : m ≤ (4 * D) * n := by
    have hmod := Nat.mod_lt m hdiv
    have he : 2 * D * n + m % (2 * D) = m := Nat.div_add_mod m (2 * D)
    have hc := Nat.mul_le_mul_left (2 * D) hn₁
    nlinarith only [hmod, he, hc]
  have hreal : (m : ℝ) / (4 * (D : ℝ)) ≤ (n : ℝ) := by
    apply (div_le_iff₀ hD').2
    rw [mul_comm]
    exact_mod_cast hmup
  refine ⟨s, ?_, ?_⟩
  · calc
      Real.exp (Real.log 2 / (4 * D) * m) =
          Real.exp (Real.log 2 * (m / (4 * D))) := by ring_nf
      _ ≤ Real.exp ((n : ℝ) * Real.log 2) := Real.exp_le_exp.2 (by
        rw [mul_comm (n : ℝ)]
        exact mul_le_mul_of_nonneg_left hreal hlog.le)
      _ = (2 : ℝ) ^ n := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ s.card := by exact_mod_cast hcnt
  · intro x hx
    obtain ⟨M, g, he, hg, hst, hd, hen⟩ := hs x hx
    rw [hFdeg] at hd
    refine ⟨M, g, he, hg, hst, hd.trans ?_, hen⟩
    exact (Nat.mul_le_mul_left _ (Nat.le_max_right _ _)).trans hmld

omit [IsArtinianRing R] in
/-- A fixed nonpresilting obstruction over all finite extensions gives
infinitely many ground stable modules at one weight and one positive
endolength. -/
theorem exists_infinite_stableClassesOfEndolength_of_no_presilting_extension
    (P : TwoTerm R) (hmissing : NoPresiltingDifferentialAfterFiniteExtension k P) :
    ∃ (g : ProjectiveClass R) (r : ℕ), 0 < r ∧
      (stableClassesOfEndolength k (projectiveClassWeight k g) r).Infinite := by
  classical
  obtain ⟨G, c, m₀, hc, hgrowth⟩ := exists_exponential_ground_witnesses k P hmissing
  let D := Module.finrank k (P.target.obj : Type u)
  let U := ⋃ g : (G : Set (ProjectiveClass R)), ⋃ r : Fin (D + 1),
    stableClassesOfEndolength k (projectiveClassWeight k g.val) r.val
  by_contra hn
  have hall (g : (G : Set (ProjectiveClass R))) (r : Fin (D + 1)) :
      (stableClassesOfEndolength k (projectiveClassWeight k g.val) r.val).Finite := by
    by_cases hp : 0 < r.val
    · by_contra! h
      exact hn ⟨g.val, r.val, hp, h⟩
    · have he : stableClassesOfEndolength k (projectiveClassWeight k g.val) r.val = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.2
        rintro x ⟨M, _, hM, hst⟩
        exact hp (hM ▸ hst.isBrick.endolength_pos k)
      rw [he]
      exact Set.finite_empty
  have hf : U.Finite := Set.finite_iUnion (fun g ↦ Set.finite_iUnion (hall g))
  obtain ⟨n, hn'⟩ := exists_nat_gt ((U.ncard : ℝ) / c)
  let m := max n m₀
  have hlarge : (U.ncard : ℝ) < c * (m : ℝ) := by
    have h := (div_lt_iff₀ hc).1 hn'
    rw [mul_comm] at h
    exact h.trans_le (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_max_left n m₀) hc.le)
  obtain ⟨s, hs, hmem⟩ := hgrowth m (Nat.le_max_right _ _)
  have hsub : (s : Set (Skeleton (FGModuleCat.{u} R))) ⊆ U := by
    intro x hx
    obtain ⟨M, g, he, hm, hst, _, hend⟩ := hmem x hx
    exact Set.mem_iUnion.2 ⟨⟨g, hm⟩, Set.mem_iUnion.2
      ⟨⟨endolength k M, Nat.lt_succ_of_le hend⟩, M, he, rfl, hst⟩⟩
  have hcd : (s.card : ℝ) ≤ U.ncard := by
    exact_mod_cast (Set.ncard_coe_finset s).symm.trans_le (Set.ncard_le_ncard hsub hf)
  have hcontra := (hs.trans hcd).trans_lt hlarge
  linarith [Real.add_one_le_exp (c * (m : ℝ))]

include k in
/-- Over a finite field, a non-E-finite algebra has exponentially many
distinct brick classes below every sufficiently large composition-length cutoff. -/
theorem exists_exponential_brick_finsets_of_not_isEFinite (h : ¬ IsEFinite R) :
    ∃ (c : ℝ) (m₀ : ℕ), 0 < c ∧
      ∀ m ≥ m₀, ∃ s : Finset (Skeleton (FGModuleCat.{u} R)),
        Real.exp (c * m) ≤ s.card ∧
        ∀ x ∈ s, ∃ M : FGModuleCat.{u} R, toSkeleton M = x ∧ IsBrick M ∧ FGModuleCat.moduleLength M ≤ m := by
  obtain ⟨P, hp⟩ := exists_missing_terms k h
  obtain ⟨_, c, m₀, hc, hgrowth⟩ := exists_exponential_ground_witnesses k P hp
  refine ⟨c, m₀, hc, fun m hm ↦ ?_⟩
  obtain ⟨s, hs, hmem⟩ := hgrowth m hm
  refine ⟨s, hs, fun x hx ↦ ?_⟩
  obtain ⟨M, _, he, _, hst, hl, _⟩ := hmem x hx
  exact ⟨M, he, hst.isBrick, (FGModuleCat.moduleLength_le_groundFinrank k M).trans hl⟩

/-- Over a finite field, a non-E-finite algebra has infinitely many stable
classes at one integral weight and one positive endolength. -/
theorem exists_infinite_stableClassesOfEndolength_of_not_isEFinite (h : ¬ IsEFinite R) :
    ∃ (g : ProjectiveClass R) (r : ℕ), 0 < r ∧
      (stableClassesOfEndolength k (projectiveClassWeight k g) r).Infinite := by
  obtain ⟨P, hp⟩ := exists_missing_terms k h
  exact exists_infinite_stableClassesOfEndolength_of_no_presilting_extension k P hp

end FieldExtension

end EFiniteCharacterizations
