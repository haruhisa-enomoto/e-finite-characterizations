module

public import EFiniteCharacterizations.Stability.CompactWeightChamber

/-! # Rational weights in the open region of a numerical torsion class -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct Topology

universe u
namespace EFiniteCharacterizations

variable {R : Type u} [Ring R]

/-- Weights some positive integral multiple of which comes from the projective lattice. -/
def rationalProjectiveWeights (R : Type u) [Ring R] : AddSubmonoid (RealProjectiveSpace R) where
  carrier := {v | ∃ (n : ℕ) (g : ProjectiveClass R), 0 < n ∧ n • v = realProjectiveClass R g}
  zero_mem' := ⟨1,0,zero_lt_one,by simp⟩
  add_mem' := by
    rintro v w ⟨n,g,hn,hg⟩ ⟨m,h,hm,hh⟩
    refine ⟨m*n,m • g + n • h,Nat.mul_pos hm hn,?_⟩
    rw [smul_add,map_add,map_nsmul,map_nsmul,← hg,← hh,smul_smul,smul_smul,Nat.mul_comm n m]

local instance : TopologicalSpace (RealProjectiveSpace R) := moduleTopology ℝ _
local instance : ContinuousAdd (RealProjectiveSpace R) := ModuleTopology.continuousAdd ℝ _
local instance : ContinuousSMul ℝ (RealProjectiveSpace R) := ModuleTopology.continuousSMul ℝ _

theorem dense_rationalProjectiveWeights : Dense (rationalProjectiveWeights R : Set (RealProjectiveSpace R)) := by
  let A := rationalProjectiveWeights R
  intro v
  change v ∈ A.topologicalClosure
  induction v using TensorProduct.inductionOn with
  | add x y hx hy => exact A.topologicalClosure.add_mem hx hy
  | tmul r g =>
    let path (a : ℝ) := a • realProjectiveClass R g
    have ht : path r = r ⊗ₜ[ℤ] g := by
      change r • ((1 : ℝ) ⊗ₜ[ℤ] g) = _
      rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    rw [← ht]
    apply Rat.denseRange_cast.induction_on (p := fun a : ℝ ↦ path a ∈ A.topologicalClosure) r
    · exact A.isClosed_topologicalClosure.preimage (show Continuous path by dsimp [path]; fun_prop)
    · intro q
      apply A.le_topologicalClosure
      refine ⟨q.den,q.num • g,q.den_pos,?_⟩
      rw [map_zsmul,← Int.cast_smul_eq_zsmul ℝ,← Nat.cast_smul_eq_nsmul ℝ]
      dsimp only [path]
      rw [smul_smul]
      congr 1
      rw [Rat.cast_def]
      field_simp

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R] [IsNoetherianRing R]

theorem integral_classes_of_multiple {w : RealProjectiveSpace R} {n : ℕ} {g : ProjectiveClass R}
    (hn : 0 < n) (hg : n • w = realProjectiveClass R g) :
    (projectiveClassWeight k g).strictTorsionClass = realStrictTorsion k w ∧
      (projectiveClassWeight k g).weakTorsionClass = realWeakTorsion k w := by
  have h (X : FGModuleCat.{u} R) : ((projectiveClassWeight k g).eval X : ℝ) =
      n * realEulerEvaluation k (GrothendieckGroup.of X) w := by
    unfold Weight.eval
    rw [← realEulerEvaluation_integral,← hg,← Nat.cast_smul_eq_nsmul ℝ,realEulerEvaluation_smul]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hpos (X : FGModuleCat.{u} R) : 0 < (projectiveClassWeight k g).eval X ↔
      0 < realEulerEvaluation k (GrothendieckGroup.of X) w := by
    rw [← Int.cast_pos (R := ℝ),h,mul_pos_iff_of_pos_left hn']
  have hnon (X : FGModuleCat.{u} R) : 0 ≤ (projectiveClassWeight k g).eval X ↔
      0 ≤ realEulerEvaluation k (GrothendieckGroup.of X) w := by
    rw [← Int.cast_nonneg_iff (R := ℝ),h,mul_nonneg_iff_of_pos_left hn']
  exact ⟨funext fun M ↦ propext ⟨fun hm _ q _ hQ ↦ (hpos _).1 (hm q hQ),
    fun hm _ q _ hQ ↦ (hpos _).2 (hm q hQ)⟩,funext fun M ↦ propext
    ⟨fun hm _ q _ ↦ (hnon _).1 (hm q),fun hm _ q _ ↦ (hnon _).2 (hm q)⟩⟩

/-- In every neighborhood of a compact strict or cocompact weak weight one finds a rational
weight whose integral multiple has exactly the prescribed torsion class on both sides of
the wall test. Covariant finiteness suffices on either side. Its only semistable module is zero. -/
theorem compact_weight_mem_closure_of_integral_chamber {v : RealProjectiveSpace R}
    {T : ObjectProperty (FGModuleCat.{u} R)}
    (h : (T = realStrictTorsion k v ∧ ((∃ B, T = generatedTorsionClass B) ∨ CovariantlyFinite T)) ∨
      (T = realWeakTorsion k v ∧ ((∃ N : FGModuleCat.{u} R, ∀ M, T M ↔ Subsingleton (M ⟶ N)) ∨ CovariantlyFinite T))) :
    v ∈ closure {w | ∃ (n : ℕ) (g : ProjectiveClass R), 0 < n ∧ n • w = realProjectiveClass R g ∧
      (projectiveClassWeight k g).strictTorsionClass = T ∧ (projectiveClassWeight k g).weakTorsionClass = T ∧
      ∀ M, (projectiveClassWeight k g).IsSemistable M → IsZero M} := by
  obtain ⟨E,hE,_,hv,he⟩ : ∃ E : Set (RealProjectiveSpace R), IsOpen E ∧ E.Nonempty ∧ v ∈ closure E ∧
      ∀ w ∈ E, realStrictTorsion k w = T ∧ realWeakTorsion k w = T := by
    rcases h with ⟨rfl,h⟩ | ⟨rfl,h⟩
    · obtain ⟨B,hB⟩ := h.elim id fun ht ↦ (bicompact_real_torsion_of_covariantlyFinite k v (Or.inl rfl) ht).1
      exact open_chamber_of_compact_strict k hB
    · obtain ⟨N,hN⟩ := h.elim id fun ht ↦ (bicompact_real_torsion_of_covariantlyFinite k v (Or.inr rfl) ht).2
      exact open_chamber_of_cocompact_weak k hN
  apply (closure_minimal ?_ isClosed_closure) hv
  intro w hw
  apply closure_mono ?_ (hE.inter_closure ⟨hw,dense_rationalProjectiveWeights (R := R) w⟩)
  rintro u ⟨hu,n,g,hn,hg⟩
  obtain ⟨hs,ht⟩ := integral_classes_of_multiple k hn hg
  have hstrict := hs.trans (he u hu).1
  have hweak := ht.trans (he u hu).2
  refine ⟨n,g,hn,hg,hstrict,hweak,fun M hm ↦ ?_⟩
  by_contra hM
  have hwk : (projectiveClassWeight k g).weakTorsionClass M := ((Weight.isSemistable_iff_quotients M).1 hm).2
  have hst : (projectiveClassWeight k g).strictTorsionClass M := by
    rw [hstrict,hweak.symm]
    exact hwk
  exact (hst (𝟙 M) hM).ne' hm.1

end EFiniteCharacterizations
