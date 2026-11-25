module

public import EFiniteCharacterizations.Silting.Fans.ClosedPresiltingCones
public import EFiniteCharacterizations.Stability.RationalChamberWeights
public import Mathlib.Data.List.TFAE

/-! # A single presilting cone for an open region of covered rational rays -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Filter
open scoped Topology

universe u
namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R] [IsNoetherianRing R]

namespace TwoTerm

theorem compatible_of_weakTorsionClass_eq {P Q : TwoTerm R} (hp : P.IsPresilting) (hq : Q.IsPresilting)
    (h : (P.eulerWeight k).weakTorsionClass = (Q.eulerWeight k).weakTorsionClass) :
    (P.directSum Q).IsPresilting := by
  have test (A : TwoTerm R) (ha : A.IsPresilting) (M : FGModuleCat.{u} R) :
      (A.eulerWeight k).weakTorsionClass M ↔ Function.Surjective (A.precompose M) :=
    (A.nonneg_eulerWeight_all_quotients_iff k ha M).trans (A.surjective_precompose_iff_no_hom_nakayamaKernel k M).symm
  have self (A : TwoTerm R) (ha : A.IsPresilting) : Function.Surjective (A.precompose (cokernel A.differential)) :=
    (surjective_boundary_iff_surjective_precompose A A).1 ha
  apply compatible_of_precompose k hp _ _ (self Q hq)
  · apply (test P hp _).1
    rw [h]
    exact (test Q hq _).2 (self Q hq)
  · apply (test Q hq _).1
    rw [← h]
    exact (test P hp _).2 (self P hp)

include k in
/-- If a compatible sum has the class of a multiple of P, each summand has its class
in the real cone of P. -/
private theorem class_mem_cone_of_sum_class {P Q Y : TwoTerm R} (hp : P.IsPresilting)
    (h : (Q.directSum Y).IsPresilting) {m : ℕ}
    (he : Q.projectiveClass + Y.projectiveClass = m • P.projectiveClass) :
    realProjectiveClass R Q.projectiveClass ∈ P.gVectorCone := by
  have eqc : (Q.directSum Y).projectiveClass = (P.copies m).projectiveClass := by simpa using he
  obtain ⟨K,hK⟩ := (isInStableAdd_of_isPresilting_of_class_eq k _ _ h (isPresilting_copies k hp m) eqc).1
  have ha := (IsInAdd.of_retraction _ _ (inlDirectSum_fstDirectSum Q Y)).trans hK
  obtain ⟨X,hX,hc⟩ := class_in_add_of_stableAdd k Q (P.copies m) ⟨K,ha⟩
  exact PointedCone.subset_hull ⟨X,hX.trans (isInAdd_copies P m),congrArg _ hc.symm⟩

end TwoTerm

local instance chamberConeTopology : TopologicalSpace (RealProjectiveSpace R) := moduleTopology ℝ _
local instance chamberConeSMul : ContinuousSMul ℝ (RealProjectiveSpace R) := ModuleTopology.continuousSMul ℝ _
local instance chamberConeModuleTopology : IsModuleTopology ℝ (RealProjectiveSpace R) := ⟨rfl⟩

/-- On an open set with constant weak numerical torsion class, coverage of all rational
rays puts the entire closure in one cone. -/
theorem closure_subset_one_cone_of_covered_rational_weights
    {E : Set (RealProjectiveSpace R)} (ho : IsOpen E) (hne : E.Nonempty)
    (hT : ∀ x ∈ E, ∀ y ∈ E, realWeakTorsion k x = realWeakTorsion k y)
    (realize : ∀ x ∈ E, ∀ (n : ℕ) (g : ProjectiveClass R), 0 < n → n • x = realProjectiveClass R g →
      ∃ P : TwoTerm R, P.IsPresilting ∧ P.projectiveClass = g) :
    ∃ P : TwoTerm R, P.IsPresilting ∧ closure E ⊆ (P.gVectorCone : Set (RealProjectiveSpace R)) := by
  let _ := IsModuleTopology.isTopologicalAddGroup ℝ (RealProjectiveSpace R)
  obtain ⟨x,hx,⟨d,a,hd,hda⟩⟩ := dense_rationalProjectiveWeights.inter_open_nonempty E ho hne
  obtain ⟨P,hp,rfl⟩ := realize x hx d a hd hda
  refine ⟨P,hp,closure_minimal (fun w hw ↦ ?_) (P.isClosed_gVectorCone k)⟩
  apply (closure_minimal ?_ (P.isClosed_gVectorCone k)) (ho.inter_closure ⟨hw,dense_rationalProjectiveWeights w⟩)
  rintro u ⟨hu,n,g,hn,hg⟩
  obtain ⟨Q,hq,rfl⟩ := realize u hu n g hn hg
  let z := realProjectiveClass R Q.projectiveClass
  let y (m : ℕ) := x - (m : ℝ)⁻¹ • ((d : ℝ)⁻¹ • z)
  have hy : Tendsto y atTop (𝓝 x) := by
    have hi : Tendsto (fun m : ℕ ↦ (m : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa [y] using (tendsto_const_nhds (x := x)).sub (hi.smul (tendsto_const_nhds (x := (d : ℝ)⁻¹ • z)))
  obtain ⟨m,hm,hmE⟩ := ((eventually_gt_atTop 0).and (hy (ho.mem_nhds hx))).exists
  let b := m • P.projectiveClass - Q.projectiveClass
  have hyb : (m*d) • y m = realProjectiveClass R b := by
    rw [show realProjectiveClass R b = m • realProjectiveClass R P.projectiveClass - z by simp [b,z],← hda,smul_smul]
    rw [← Nat.cast_smul_eq_nsmul ℝ,← Nat.cast_smul_eq_nsmul ℝ]
    simp only [y,smul_sub,smul_smul,Nat.cast_mul]
    rw [show (m : ℝ)*d * ((m : ℝ)⁻¹ * (d : ℝ)⁻¹) = 1 by
      have : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
      have : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
      field_simp,one_smul]
  obtain ⟨Y,hyP,hclass⟩ := realize _ hmE _ b (Nat.mul_pos hm hd) hyb
  have hqT := (integral_classes_of_multiple k hn hg).2
  have hyT := (integral_classes_of_multiple k (Nat.mul_pos hm hd) hyb).2
  rw [Q.projectiveClassWeight_eq_eulerWeight k] at hqT
  rw [← hclass,Y.projectiveClassWeight_eq_eulerWeight k] at hyT
  have comp := TwoTerm.compatible_of_weakTorsionClass_eq k hq hyP (hqT.trans ((hT _ hu _ hmE).trans hyT.symm))
  have eqc : Q.projectiveClass + Y.projectiveClass = m • P.projectiveClass := by rw [hclass]; dsimp [b]; abel
  have hz := TwoTerm.class_mem_cone_of_sum_class k hp comp eqc
  rw [← hg,← Nat.cast_smul_eq_nsmul ℝ] at hz
  change u ∈ P.gVectorCone
  simpa only [smul_smul,inv_mul_cancel₀ (show (n : ℝ) ≠ 0 from Nat.cast_ne_zero.2 hn.ne'),one_smul] using
    P.gVectorCone.smul_mem (inv_nonneg.2 (Nat.cast_nonneg n : (0:ℝ) ≤ n)) hz


/-- The seven conditions in the fixed-weight torsion criterion. -/
def FixedWeightTorsionCriteria (v : RealProjectiveSpace R) : Prop :=
  let strict := realStrictTorsion k v
  let weak := realWeakTorsion k v
  let compact (T : ObjectProperty (FGModuleCat.{u} R)) := ∃ B, T = generatedTorsionClass B
  let cocompact (T : ObjectProperty (FGModuleCat.{u} R)) := ∃ N : FGModuleCat.{u} R, ∀ M, T M ↔ Subsingleton (M ⟶ N)
  List.TFAE [v ∈ TwoTerm.gVectorFanSupport R,FunctoriallyFinite strict,compact strict,
    compact strict ∧ cocompact strict,FunctoriallyFinite weak,cocompact weak,compact weak ∧ cocompact weak]

/-- In a chamber obtained from a compact or cocompact torsion class, only
rational rays with the same torsion class need to have presilting representatives. -/
theorem fixedWeightTorsionCriteria_of_chamber_realization
    (realize : ∀ (g : ProjectiveClass R) (T : ObjectProperty (FGModuleCat.{u} R)),
      (projectiveClassWeight k g).strictTorsionClass = T →
      (projectiveClassWeight k g).weakTorsionClass = T →
      ((∃ B, T = generatedTorsionClass B) ∨
        ∃ N : FGModuleCat.{u} R, ∀ X, T X ↔ Subsingleton (X ⟶ N)) →
      ∃ P : TwoTerm R, P.IsPresilting ∧ P.projectiveClass = g) (v : RealProjectiveSpace R) :
    FixedWeightTorsionCriteria k v := by
  let S := realStrictTorsion k v
  let W := realWeakTorsion k v
  let cover := v ∈ TwoTerm.gVectorFanSupport R
  let compact (T : ObjectProperty (FGModuleCat.{u} R)) := ∃ B, T = generatedTorsionClass B
  let cocompact (T : ObjectProperty (FGModuleCat.{u} R)) := ∃ N : FGModuleCat.{u} R, ∀ M, T M ↔ Subsingleton (M ⟶ N)
  have backward {E : Set (RealProjectiveSpace R)} (ho : IsOpen E) (hn : E.Nonempty) (hv : v ∈ closure E)
      {T : ObjectProperty (FGModuleCat.{u} R)} (he : ∀ x ∈ E, realStrictTorsion k x = T ∧ realWeakTorsion k x = T)
      (finiteTest : compact T ∨ cocompact T) : cover := by
    obtain ⟨P,hp,hh⟩ := closure_subset_one_cone_of_covered_rational_weights k ho hn
      (fun x hx y hy ↦ (he x hx).2.trans (he y hy).2.symm) (fun x hx n g hn hg ↦ by
      obtain ⟨hs,hw⟩ := integral_classes_of_multiple k hn hg
      exact realize g T (hs.trans (he x hx).1) (hw.trans (he x hx).2) finiteTest)
    exact ⟨P,hp,hh hv⟩
  have scov : compact S → cover := by
    rintro ⟨B,hB⟩
    obtain ⟨E,ho,hn,hv,he⟩ := open_chamber_of_compact_strict k hB
    exact backward ho hn hv he (Or.inl ⟨B,hB⟩)
  have wcov : cocompact W → cover := by
    rintro ⟨N,hN⟩
    obtain ⟨E,ho,hn,hv,he⟩ := open_chamber_of_cocompact_weak k hN
    exact backward ho hn hv he (Or.inr ⟨N,hN⟩)
  have fs : cover → FunctoriallyFinite S ∧ compact S ∧ cocompact S :=
    fun h ↦ covered_real_torsion_bicompact k h _ (Set.mem_insert ..)
  have fw : cover → FunctoriallyFinite W ∧ compact W ∧ cocompact W :=
    fun h ↦ covered_real_torsion_bicompact k h _ (Set.mem_insert_of_mem _ rfl)
  apply List.tfae_of_forall (b := cover)
  intro X h
  change X ∈ [cover,FunctoriallyFinite S,compact S,compact S ∧ cocompact S,
    FunctoriallyFinite W,cocompact W,compact W ∧ cocompact W] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact ⟨fun hs ↦ scov (bicompact_real_torsion_of_covariantlyFinite k v (Or.inl rfl) hs.1).1,fun h ↦ (fs h).1⟩
  · exact ⟨scov,fun h ↦ (fs h).2.1⟩
  · exact ⟨fun h ↦ scov h.1,fun h ↦ (fs h).2⟩
  · exact ⟨fun hw ↦ wcov (bicompact_real_torsion_of_covariantlyFinite k v (Or.inr rfl) hw.1).2,fun h ↦ (fw h).1⟩
  · exact ⟨wcov,fun h ↦ (fw h).2.2⟩
  · exact ⟨fun h ↦ wcov h.2,fun h ↦ (fw h).2⟩

/-- It suffices to realize integral classes whose semistable category is zero. -/
theorem fixedWeightTorsionCriteria_of_integral_realization
    (realize : ∀ g : ProjectiveClass R, (∀ M, (projectiveClassWeight k g).IsSemistable M → IsZero M) →
      ∃ P : TwoTerm R, P.IsPresilting ∧ P.projectiveClass = g) (v : RealProjectiveSpace R) :
    FixedWeightTorsionCriteria k v := by
  apply fixedWeightTorsionCriteria_of_chamber_realization k
  intro g T hs hw _
  apply realize g
  intro M hM
  by_contra hnM
  have hstrict : (projectiveClassWeight k g).strictTorsionClass M := by
    rw [hs,← hw]
    exact ((Weight.isSemistable_iff_quotients M).1 hM).2
  exact (hstrict (𝟙 M) hnM).ne' hM.1

/-- Over an E-finite algebra the seven tests characterize coverage even at irrational
weights, without assuming completeness of the fan. -/
theorem fixedWeightTorsionCriteria_of_isEFinite (hR : IsEFinite R) (v : RealProjectiveSpace R) :
    FixedWeightTorsionCriteria k v :=
  fixedWeightTorsionCriteria_of_integral_realization k (fun g _ ↦ hR g) v

end EFiniteCharacterizations
