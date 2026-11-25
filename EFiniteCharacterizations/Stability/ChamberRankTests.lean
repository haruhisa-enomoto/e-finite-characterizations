module

public import EFiniteCharacterizations.Stability.OneSidedDeterminants
public import EFiniteCharacterizations.LargeModules.PrescribedGrain

/-! # Projective representatives from one-sided rank tests in an integral chamber -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra ZeroObject
universe u
namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R]

/-- The two rank conditions on a common differential of class a positive multiple of g. -/
def HasSimultaneousRankTests (g : ProjectiveClass R) : Prop :=
  ∀ B M : FGModuleCat.{u} R, (projectiveClassWeight k g).strictTorsionClass B →
    (∀ {U : FGModuleCat.{u} R} (i : U ⟶ M) [Mono i], ¬ IsZero U → (projectiveClassWeight k g).eval U < 0) →
    ∃ (n : ℕ) (_ : 0 < n) (P : TwoTerm R), P.projectiveClass = n • g ∧
      Function.Surjective (P.precompose B) ∧ Function.Injective (P.precompose M)

/-- A positive multiple realizes both one-sided rank tests over the input field. -/
theorem hasSimultaneousRankTests (g : ProjectiveClass R) : HasSimultaneousRankTests k g := by
  obtain ⟨P,rfl⟩ := g.exists_twoTerm
  intro B M hB hM
  rw [P.projectiveClassWeight_eq_eulerWeight k] at hB hM
  exact P.exists_block_precomposition_tests k B M hB hM

private theorem eval_multiple (P : TwoTerm R) (g : ProjectiveClass R) {n : ℕ}
    (hg : P.projectiveClass = n • g) (X : FGModuleCat.{u} R) :
    (n : ℤ) * (projectiveClassWeight k g).eval X =
      (homFinrank k (cokernel P.differential) X : ℤ) - homFinrank k X (P.nakayamaKernel k) := by
  rw [← P.euler_eq_hom_difference k,← P.eulerWeight_eval k,← P.projectiveClassWeight_eq_eulerWeight k,hg,map_nsmul]
  simp [Weight.eval]

private theorem neg_of_finite_perp (g : ProjectiveClass R) (M : FGModuleCat.{u} R)
    (h : ∀ X, (projectiveClassWeight k g).weakTorsionClass X → Subsingleton (X ⟶ M)) :
    ∀ {U : FGModuleCat.{u} R} (i : U ⟶ M) [Mono i], ¬ IsZero U → (projectiveClassWeight k g).eval U < 0 := by
  have hw := (integral_classes_of_multiple k (n := 1) (g := g) zero_lt_one (one_smul ℕ _)).2
  intro U i _ hU
  have ht := (subobject_negative_iff_rightOrthogonal k (v := realProjectiveClass R g) M).2
    (hw ▸ h) i hU
  rw [realEulerEvaluation_integral] at ht
  exact_mod_cast ht

/-- A positive multiple admitting a surjection test on the torsion generator
supplies the missing finite perpendicular by its Nakayama kernel. -/
private theorem perp_of_generator_test (g : ProjectiveClass R) (B : FGModuleCat.{u} R)
    (hB : (projectiveClassWeight k g).weakTorsionClass = generatedTorsionClass B)
    {n : ℕ} (hn : 0 < n) (P : TwoTerm R) (hg : P.projectiveClass = n • g)
    (hs : Function.Surjective (P.precompose B)) :
    ∀ X, (projectiveClassWeight k g).weakTorsionClass X ↔ Subsingleton (X ⟶ P.nakayamaKernel k) := by
  have hk := (P.surjective_precompose_iff_no_hom_nakayamaKernel k B).1 hs
  intro X
  refine ⟨fun hX ↦ ?_,fun h Y q _ ↦ ?_⟩
  · rw [hB] at hX
    exact ⟨fun f a ↦ (hX _ (fun t ↦ hk.elim t 0) f).trans (hX _ (fun t ↦ hk.elim t 0) a).symm⟩
  · have hzero := (homFinrank_eq_zero_iff k Y _).2 (fun f ↦ (cancel_epi q).1 (by simpa using h.elim (q ≫ f) 0))
    have eq := eval_multiple k P g hg Y
    rw [hzero,Nat.cast_zero,sub_zero] at eq
    exact nonneg_of_mul_nonneg_right (eq.symm ▸ Int.natCast_nonneg _) (Int.natCast_pos.2 hn)

/-- A differential injective on M supplies the missing torsion generator by its cokernel. -/
private theorem generator_of_perp_test (g : ProjectiveClass R) (M : FGModuleCat.{u} R)
    (hM : ∀ X, (projectiveClassWeight k g).strictTorsionClass X ↔ Subsingleton (X ⟶ M))
    {n : ℕ} (hn : 0 < n) (P : TwoTerm R) (hg : P.projectiveClass = n • g)
    (hi : Function.Injective (P.precompose M)) :
    (projectiveClassWeight k g).strictTorsionClass = generatedTorsionClass (cokernel P.differential) := by
  let C := cokernel P.differential
  have hc : Subsingleton (C ⟶ M) := (P.injective_precompose_iff_no_hom_cokernel k M).1 hi
  funext X
  refine propext ⟨fun hx Y hy f ↦ ?_,fun hx ↦ (hM X).2 ?_⟩
  · by_contra hf
    have hnI : ¬ IsZero (Abelian.image f) := fun h ↦ hf (by rw [← Abelian.image.fac f,h.eq_of_src (Abelian.image.ι f) 0,comp_zero])
    have hpos := hx (Abelian.factorThruImage f) hnI
    have eq := eval_multiple k P g hg (Abelian.image f)
    have hp := mul_pos (Int.natCast_pos.2 hn) hpos
    obtain ⟨a,ha⟩ := (homFinrank_pos_iff k C (Abelian.image f)).1 (by dsimp [C]; omega)
    exact ha ((cancel_mono (Abelian.image.ι f)).1 (by simpa using hy (a ≫ Abelian.image.ι f)))
  · exact ⟨fun f a ↦ (hx _ (fun b ↦ hc.elim b 0) f).trans (hx _ (fun b ↦ hc.elim b 0) a).symm⟩

theorem exists_presilting_of_chamber_rank_tests (g : ProjectiveClass R) (rankTests : HasSimultaneousRankTests k g)
    (T : ObjectProperty (FGModuleCat.{u} R)) (hs : (projectiveClassWeight k g).strictTorsionClass = T)
    (hw : (projectiveClassWeight k g).weakTorsionClass = T)
    (finiteTest : (∃ B, T = generatedTorsionClass B) ∨ ∃ M : FGModuleCat.{u} R, ∀ X, T X ↔ Subsingleton (X ⟶ M)) :
    ∃ P : TwoTerm R, P.IsPresilting ∧ P.projectiveClass = g := by
  let := IsArtinianRing.of_finite k R
  have genmem (B : FGModuleCat.{u} R) : generatedTorsionClass B B := fun _ h ↦ h
  have pair : ∃ B M : FGModuleCat.{u} R, T = generatedTorsionClass B ∧ ∀ X, T X ↔ Subsingleton (X ⟶ M) := by
    rcases finiteTest with ⟨B,hB⟩ | ⟨M,hM⟩
    · obtain ⟨n,hn,P,hg,hp,_⟩ := rankTests B 0 (show (projectiveClassWeight k g).strictTorsionClass B by rw [hs,hB]; exact genmem B)
        (neg_of_finite_perp k g 0 (fun _ _ ↦ inferInstance))
      exact ⟨B,P.nakayamaKernel k,hB,hw ▸ perp_of_generator_test k g B (hw.trans hB) hn P hg hp⟩
    · have h0 : (projectiveClassWeight k g).strictTorsionClass (0 : FGModuleCat.{u} R) := by
        rw [hs]
        exact (hM _).2 inferInstance
      obtain ⟨n,hn,P,hg,_,hp⟩ := rankTests 0 M h0 (neg_of_finite_perp k g M (fun X h ↦ (hM X).1 (hw ▸ h)))
      exact ⟨_,M,hs ▸ generator_of_perp_test k g M (hs.symm ▸ hM) hn P hg hp,hM⟩
  obtain ⟨B,M,hB,hM⟩ := pair
  obtain ⟨n,hn,P,hg,hp,hi⟩ := rankTests B M (show (projectiveClassWeight k g).strictTorsionClass B by rw [hs,hB]; exact genmem B)
    (neg_of_finite_perp k g M (fun X h ↦ (hM X).1 (hw ▸ h)))
  have pres := P.isPresilting_of_torsion_pair_tests k B M (hB ▸ hM) hp hi
  obtain ⟨Q,hQ,hgQ⟩ := TwoTerm.exists_in_add_of_presilting_multiple k pres hn hg
  exact ⟨Q,TwoTerm.isPresilting_of_homotopy_isInAdd pres (hQ.map (TwoTerm.doubleFunctor (C := FGModuleCat.{u} R) ⋙ HomotopyCategory.quotient _ _)),hgQ⟩

/-- For every real weight over an arbitrary field the seven fixed-weight torsion tests
are equivalent, including at irrational weights over an E-infinite algebra. -/
theorem fixedWeightTorsionCriteria (v : RealProjectiveSpace R) :
    FixedWeightTorsionCriteria k v :=
  fixedWeightTorsionCriteria_of_chamber_realization k
    (fun g ↦ exists_presilting_of_chamber_rank_tests k g (hasSimultaneousRankTests k g)) v

/-- Every prescribed integral weight outside the fan yields an endofinite kernel with a generic-grain summand. -/
theorem exists_generic_grain_kernel_of_missing_weight [IsArtinianRing R] (γ : ProjectiveClass R)
    (hγ : ¬ ∃ P : TwoTerm R, P.IsPresilting ∧ P.projectiveClass = γ) :
    ∃ N : ModuleCat.{u} R, IsEndofinite N ∧ SplitsOnCogeneratedModules k N ∧
      perpendicularToModule N = (projectiveClassWeight k γ).weakTorsionClass ∧
      cogeneratedByModule N = (fun X ↦ ∀ {U : FGModuleCat.{u} R} (i : U ⟶ X) [Mono i],
        ¬ IsZero U → (projectiveClassWeight k γ).eval U < 0) ∧
      ∃ G : ModuleCat.{u} R, Nonempty (Retract G N) ∧ IsGenericGrain k G :=
  exists_generic_grain_kernel_of_fixedWeightTorsionCriteria k γ hγ (fixedWeightTorsionCriteria k _)

end EFiniteCharacterizations
