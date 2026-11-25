module

public import EFiniteCharacterizations.Characterizations.FixedClassFiniteness

/-! # Stable weights shared by bricks with the same semistability locus -/

@[expose] public section

open CategoryTheory

universe u v

namespace EFiniteCharacterizations

variable {C : Type u} [Category.{v} C] [Abelian C]

theorem Weight.IsStable.add_of_semistable {θ η : Weight C} {X : C}
    (hθ : θ.IsStable X) (hη : η.IsSemistable X) : (θ + η).IsStable X := by
  refine ⟨hθ.1, ?_, fun i _ hn hi ↦ ?_⟩
  · change θ.eval X + η.eval X = 0
    rw [hθ.2.1, hη.1, zero_add]
  · exact add_neg_of_neg_of_nonpos (hθ.2.2 i hn hi) (hη.2 i)

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

/-- Adding the two individual stability weights gives a common stability
weight whenever the integral semistability loci of two bricks coincide. -/
theorem exists_common_stable_weight_of_same_locus (h : IsEFinite R) {X Y : FGModuleCat.{u} R}
    (hX : IsBrick X) (hY : IsBrick Y)
    (hl : ∀ g : ProjectiveClass R, (projectiveClassWeight k g).IsSemistable X ↔
      (projectiveClassWeight k g).IsSemistable Y) :
    ∃ g : ProjectiveClass R, (projectiveClassWeight k g).IsStable X ∧
      (projectiveClassWeight k g).IsStable Y := by
  obtain ⟨a, ha⟩ := exists_projective_weight_stable_of_isEFinite k h hX
  obtain ⟨b, hb⟩ := exists_projective_weight_stable_of_isEFinite k h hY
  refine ⟨a + b, ?_, ?_⟩
  · rw [map_add]
    exact ha.add_of_semistable ((hl b).mpr hb.isSemistable)
  · rw [add_comm, map_add]
    exact hb.add_of_semistable ((hl a).mp ha.isSemistable)

/-- Proportional ambient classes and the same integral semistability locus
determine a brick up to isomorphism in an E-finite algebra. -/
theorem iso_of_same_locus_of_proportional (h : IsEFinite R) {X Y : FGModuleCat.{u} R}
    (hX : IsBrick X) (hY : IsBrick Y)
    (hl : ∀ g : ProjectiveClass R, (projectiveClassWeight k g).IsSemistable X ↔
      (projectiveClassWeight k g).IsSemistable Y)
    {a b : ℕ} (ha : 0 < a)
    (he : a • GrothendieckGroup.of X = b • GrothendieckGroup.of Y) : Nonempty (X ≅ Y) := by
  obtain ⟨g, hx, hy⟩ := exists_common_stable_weight_of_same_locus k h hX hY hl
  obtain ⟨P, hp, hg⟩ := h g
  rw [← hg, P.projectiveClassWeight_eq_eulerWeight k] at hx hy
  by_contra hn
  obtain ⟨w, hpos, hv⟩ := P.exists_stable_separating_projective_weight k hp hx
  have hz := congrArg (projectiveClassWeight k w) he
  simp only [map_nsmul] at hz
  change a • (projectiveClassWeight k w).eval X = b • (projectiveClassWeight k w).eval Y at hz
  rw [hv _ hy hn, smul_zero, nsmul_eq_mul] at hz
  exact (mul_pos (by exact_mod_cast ha) hpos).ne' hz

omit [IsArtinianRing R] in
include k in
/-- A sufficiently large multiple of a stability weight absorbs any integral
perturbation vanishing on the module class. -/
theorem exists_stable_perturbation {Y : FGModuleCat.{u} R} {θ : Weight (FGModuleCat.{u} R)}
    (hy : θ.IsStable Y) (w : Weight (FGModuleCat.{u} R)) (hw : w.eval Y = 0) :
    ∃ N : ℕ, (N • θ + w).IsStable Y := by
  classical
  let s := ((finite_properSubobjectClasses k Y).image w).toFinset
  let N := (s.image Int.natAbs).sup id + 1
  refine ⟨N, hy.1, ?_, fun {U} i hi hn hp ↦ ?_⟩
  · change N • θ.eval Y + w.eval Y = 0
    simp [hy.2.1, hw]
  · have hu : GrothendieckGroup.of U ∈ properSubobjectClasses Y := ⟨U, i, hi, hn, hp, rfl⟩
    have hs : w.eval U ∈ s := ((finite_properSubobjectClasses k Y).image w).mem_toFinset.mpr ⟨_, hu, rfl⟩
    have hle : (w.eval U).natAbs < N := Nat.lt_succ_of_le
      (Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨_, hs, rfl⟩))
    have hθ := hy.2.2 i hn hp
    have hb : w.eval U < (N : ℤ) := by omega
    change N • θ.eval U + w.eval U < 0
    rw [nsmul_eq_mul]
    have ht : θ.eval U ≤ -1 := by omega
    have hmul := mul_le_mul_of_nonneg_left ht (show (0 : ℤ) ≤ N by positivity)
    linarith

/-- In an E-finite algebra the integral semistability locus determines a
brick up to isomorphism. -/
theorem iso_of_same_integral_semistability_locus (h : IsEFinite R) {X Y : FGModuleCat.{u} R}
    (hX : IsBrick X) (hY : IsBrick Y)
    (hl : ∀ g : ProjectiveClass R, (projectiveClassWeight k g).IsSemistable X ↔
      (projectiveClassWeight k g).IsSemistable Y) : Nonempty (X ≅ Y) := by
  obtain ⟨g, hx, hy⟩ := exists_common_stable_weight_of_same_locus k h hX hY hl
  obtain ⟨P, hp, hg⟩ := h g
  have hx' := hx
  have hy' := hy
  rw [← hg, P.projectiveClassWeight_eq_eulerWeight k] at hx' hy'
  by_contra hn
  obtain ⟨w, hpos, hv⟩ := P.exists_stable_separating_projective_weight k hp hx'
  obtain ⟨N, hN⟩ := exists_stable_perturbation k hy _ (hv Y hy' hn)
  have hY' : (projectiveClassWeight k (N • g + w)).IsSemistable Y := by
    simpa only [map_add, map_nsmul] using hN.isSemistable
  have hzero := ((hl _).mpr hY').1
  rw [map_add, map_nsmul] at hzero
  change N • (projectiveClassWeight k g).eval X + (projectiveClassWeight k w).eval X = 0 at hzero
  simp [hx.2.1, hpos.ne'] at hzero

end EFiniteCharacterizations
