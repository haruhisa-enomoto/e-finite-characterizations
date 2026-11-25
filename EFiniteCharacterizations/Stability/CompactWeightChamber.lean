module

public import EFiniteCharacterizations.Stability.CoveredWeightTorsion

/-! # Perturbing real weights with compact numerical torsion classes -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Filter
open scoped Topology ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R] [IsNoetherianRing R]

private abbrev cl (M : FGModuleCat.{u} R) := GrothendieckGroup.of M
private noncomputable abbrev ev (v : RealProjectiveSpace R) (M : FGModuleCat.{u} R) := realEulerEvaluation k (cl M) v

include k in
private theorem finite_quotient_classes (M : FGModuleCat.{u} R) : (nonzeroQuotientClasses M).Finite :=
  (finite_classes_of_groundFinrank_le (R := R) k (Module.finrank k (M.obj : Type u))).subset (by
    rintro _ ⟨Q,q,_,_,rfl⟩
    exact ⟨Q,groundFinrank_le_of_epi k q,rfl⟩)

private theorem generated_le_strict {v : RealProjectiveSpace R} {B : FGModuleCat.{u} R}
    (hB : realStrictTorsion k v B) : generatedTorsionClass B ≤ realStrictTorsion k v := by
  intro M hM
  obtain ⟨g,hg⟩ := exists_matching_integral_weight k ((finite_quotient_classes k B).union (finite_quotient_classes k M)) v
  let θ := projectiveClassWeight k g
  have cmp (X : FGModuleCat.{u} R) (hX : nonzeroQuotientClasses X ⊆ nonzeroQuotientClasses B ∪ nonzeroQuotientClasses M) :
      realStrictTorsion k v X ↔ θ.strictTorsionClass X := by
    have t {Q : FGModuleCat.{u} R} (q : X ⟶ Q) [Epi q] (hn : ¬ IsZero Q) :
        0 < ev k v Q ↔ 0 < θ.eval Q :=
      by simpa only [not_le,ev,cl,θ,Weight.eval] using (not_congr (hg _ (hX ⟨Q,q,inferInstance,hn,rfl⟩)).2.symm)
    exact ⟨fun h _ q _ hn ↦ (t q hn).1 (h q hn),fun h _ q _ hn ↦ (t q hn).2 (h q hn)⟩
  have hb : θ.strictTorsionClass B := (cmp B (fun _ h ↦ Or.inl h)).1 hB
  apply (cmp M (fun _ h ↦ Or.inr h)).2
  rw [strictTorsionClass_eq_leftOrthogonal k θ] at hb ⊢
  exact fun Y hY f ↦ hM Y (hb Y hY) f

private theorem strict_le_weak (v : RealProjectiveSpace R) : realStrictTorsion k v ≤ realWeakTorsion k v := by
  intro X hx Q q _
  by_cases hn : IsZero Q
  · change 0 ≤ realEulerWeight k v (GrothendieckGroup.of Q)
    rw [GrothendieckGroup.of_isZero hn,map_zero]
  · exact (hx q hn).le

private noncomputable def simpleModule (i : ↥(simpleIsomorphismClasses R)) := (fromSkeleton _).obj i.val

omit [IsNoetherianRing R] in
private theorem simpleModule_nonzero (i : ↥(simpleIsomorphismClasses R)) : ¬ IsZero (simpleModule i) := by
  obtain ⟨M,hi,hs⟩ := i.property
  have e : M ≅ simpleModule i := (fromSkeletonToSkeletonIso M).symm ≪≫ (fromSkeleton _).mapIso (eqToIso hi)
  exact fun h ↦ Simple.not_isZero M (h.of_iso e)

private theorem eval_lt_of_simple_lt {v w : RealProjectiveSpace R}
    (h : ∀ i : ↥(simpleIsomorphismClasses R), ev k v (simpleModule i) < ev k w (simpleModule i))
    (M : FGModuleCat.{u} R) (hn : ¬ IsZero M) : ev k v M < ev k w M := by
  classical
  let _ := (finite_simpleIsomorphismClasses (R := R) k).fintype
  obtain ⟨m,_,he⟩ := exists_simple_multiplicities k M
  have hm : ∃ i, m i ≠ 0 := by
    by_contra! hz
    simp only [hz,zero_smul,Finset.sum_const_zero] at he
    have hd := dimensionWeight_pos k M hn
    change 0 < dimensionWeight (R := R) k (GrothendieckGroup.of M) at hd
    rw [← he,map_zero] at hd
    exact hd.false
  obtain ⟨j,hj⟩ := hm
  change realEulerWeight k v (GrothendieckGroup.of M) < realEulerWeight k w (GrothendieckGroup.of M)
  rw [← he,map_sum,map_sum]
  simp only [map_nsmul,nsmul_eq_mul]
  exact Finset.sum_lt_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (h i).le (Nat.cast_nonneg _))
    ⟨j,Finset.mem_univ _,mul_lt_mul_of_pos_left (h j) (Nat.cast_pos.2 (Nat.pos_of_ne_zero hj))⟩

local instance : TopologicalSpace (RealProjectiveSpace R) := moduleTopology ℝ _
local instance : IsModuleTopology ℝ (RealProjectiveSpace R) := ⟨rfl⟩
local instance : ContinuousAdd (RealProjectiveSpace R) := ModuleTopology.continuousAdd ℝ _
local instance : ContinuousSMul ℝ (RealProjectiveSpace R) := ModuleTopology.continuousSMul ℝ _

private theorem continuous_eval (z : GrothendieckGroup (FGModuleCat.{u} R)) :
    Continuous (realEulerEvaluation k z) := IsModuleTopology.continuous_of_linearMap (realEulerForm k z)

theorem isOpen_realStrictTorsion (B : FGModuleCat.{u} R) : IsOpen {v | realStrictTorsion k v B} := by
  have he : {v | realStrictTorsion k v B} =
      ⋂ z ∈ nonzeroQuotientClasses B, {v | 0 < realEulerEvaluation k z v} := by
    ext v
    simp only [Set.mem_iInter,Set.mem_ofPred_eq]
    constructor
    · rintro h _ ⟨Q,q,_,hn,rfl⟩
      exact h q hn
    · intro h Q q _ hn
      exact h _ ⟨Q,q,inferInstance,hn,rfl⟩
  rw [he]
  exact (finite_quotient_classes k B).isOpen_biInter (fun z _ ↦ isOpen_lt continuous_const (continuous_eval k z))

private theorem approach_below (v : RealProjectiveSpace R) {U : Set (RealProjectiveSpace R)} (hu : IsOpen U) (hv : v ∈ U) :
    let E := U ∩ {w | ∀ i : ↥(simpleIsomorphismClasses R), ev k w (simpleModule i) < ev k v (simpleModule i)}
    IsOpen E ∧ v ∈ closure E := by
  let _ := (finite_simpleIsomorphismClasses (R := R) k).fintype
  refine ⟨hu.inter ?_,?_⟩
  · simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun i ↦ isOpen_lt (continuous_eval k _) continuous_const)
  · let G : FiniteProjective R := ⟨FGModuleCat.of R R,inferInstance⟩
    let d := realProjectiveClass R (ProjectiveClass.of G)
    let path (c : ℝ) := v - c • d
    let _ := IsModuleTopology.isTopologicalAddGroup ℝ (RealProjectiveSpace R)
    have hc : Continuous path := by dsimp [path]; fun_prop
    have ht : Tendsto path (𝓝[>] 0) (𝓝 v) := by
      simpa [path] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto ht
    filter_upwards [ht (hu.mem_nhds hv),self_mem_nhdsWithin] with c hc hpos
    refine ⟨hc,fun i ↦ ?_⟩
    have hd : 0 < realEulerEvaluation k (cl (simpleModule i)) d := by
      rw [realEulerEvaluation_integral,projectiveClassWeight_of]
      exact_mod_cast dimensionWeight_pos k _ (simpleModule_nonzero i)
    dsimp only [ev,path]
    rw [map_sub,realEulerEvaluation_smul]
    exact sub_lt_self _ (mul_pos hpos hd)

/-- If one module generates the strict numerical torsion class at v, then v is in the closure
of a nonempty open set throughout which both numerical torsion classes equal that class. -/
theorem open_chamber_of_compact_strict {v : RealProjectiveSpace R} {B : FGModuleCat.{u} R}
    (hb : realStrictTorsion k v = generatedTorsionClass B) :
    ∃ E : Set (RealProjectiveSpace R), IsOpen E ∧ E.Nonempty ∧ v ∈ closure E ∧
      ∀ w ∈ E, realStrictTorsion k w = realStrictTorsion k v ∧ realWeakTorsion k w = realStrictTorsion k v := by
  let U := {w | realStrictTorsion k w B}
  have hv : v ∈ U := by change realStrictTorsion k v B; rw [hb]; exact fun _ hy ↦ hy
  obtain ⟨ho,hc⟩ := approach_below k v (isOpen_realStrictTorsion k B) hv
  refine ⟨_,ho,Set.nonempty_of_mem hc |>.of_closure,hc,?_⟩
  intro w hw
  have ha : realStrictTorsion k v ≤ realStrictTorsion k w := hb ▸ generated_le_strict k hw.1
  have hb' : realWeakTorsion k w ≤ realStrictTorsion k v := fun M hm Q q _ hn ↦
    lt_of_le_of_lt (hm q) (eval_lt_of_simple_lt k hw.2 Q hn)
  exact ⟨le_antisymm ((strict_le_weak k w).trans hb') ha,le_antisymm hb' (ha.trans (strict_le_weak k w))⟩

private def subClassesNeZero (N : FGModuleCat.{u} R) : Set (GrothendieckGroup (FGModuleCat.{u} R)) :=
  {z | ∃ (X : FGModuleCat.{u} R) (i : X ⟶ N), Mono i ∧ ¬ IsZero X ∧ GrothendieckGroup.of X = z}

include k in
private theorem finite_subClassesNeZero (N : FGModuleCat.{u} R) : (subClassesNeZero N).Finite := by
  have : Module.Finite k (N.obj : Type u) := Module.Finite.trans R _
  apply (finite_classes_of_groundFinrank_le (R := R) k (Module.finrank k (N.obj : Type u))).subset
  rintro _ ⟨X,i,hi,_,rfl⟩
  exact ⟨X,LinearMap.finrank_le_finrank_of_injective (f := i.hom.hom.restrictScalars k)
    ((FGModuleCat.mono_iff_injective i).1 hi),rfl⟩

private def subNegative (v : RealProjectiveSpace R) (N : FGModuleCat.{u} R) :=
  ∀ z ∈ subClassesNeZero N, realEulerEvaluation k z v < 0

private theorem hom_zero_of_weak_subNegative {v : RealProjectiveSpace R} {M N : FGModuleCat.{u} R}
    (hm : realWeakTorsion k v M) (hn : subNegative k v N) (f : M ⟶ N) : f = 0 := by
  by_cases hz : IsZero (Abelian.image f)
  · rw [← Abelian.image.fac f,hz.eq_of_src (Abelian.image.ι f) 0,comp_zero]
  · exact False.elim ((hn _ ⟨_,Abelian.image.ι f,inferInstance,hz,rfl⟩).not_ge (hm (Abelian.factorThruImage f)))

/-- A module right orthogonal to the weak numerical torsion class has strictly negative
weight on every nonzero submodule. Choose a nonzero submodule of largest weight. -/
private theorem subNegative_of_hom_zero {v : RealProjectiveSpace R} {N : FGModuleCat.{u} R}
    (orth : ∀ M, realWeakTorsion k v M → Subsingleton (M ⟶ N)) : subNegative k v N := by
  classical
  intro z hz
  by_contra! hpos
  let s := (finite_subClassesNeZero k N).toFinset
  have hzs : z ∈ s := (finite_subClassesNeZero k N).mem_toFinset.2 hz
  obtain ⟨u,hu,hmax⟩ := Finset.exists_max_image s (fun c ↦ realEulerEvaluation k c v) ⟨z,hzs⟩
  obtain ⟨X,i,hi,hn,rfl⟩ := (finite_subClassesNeZero k N).mem_toFinset.1 hu
  have hx : realWeakTorsion k v X := by
    intro Q q _
    let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
    have hs : S.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel q)
      (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
    have he : GrothendieckGroup.of X = GrothendieckGroup.of (kernel q) + GrothendieckGroup.of Q :=
      GrothendieckGroup.of_shortExact S hs
    have hle : realEulerWeight k v (GrothendieckGroup.of (kernel q)) ≤ realEulerWeight k v (GrothendieckGroup.of X) := by
      by_cases hk : IsZero (kernel q)
      · rw [GrothendieckGroup.of_isZero hk,map_zero]
        exact hpos.trans (hmax z hzs)
      · exact hmax _ ((finite_subClassesNeZero k N).mem_toFinset.2 ⟨_,kernel.ι q ≫ i,inferInstance,hk,rfl⟩)
    rw [he,map_add] at hle
    exact (le_add_iff_nonneg_right _).1 hle
  have hi0 : i = 0 := (orth X hx).elim _ _
  exact hn ((IsZero.iff_id_eq_zero X).2 ((cancel_mono i).1 (by simp [hi0])))

/-- Strict negativity on each nonzero subobject characterizes the right
orthogonal of the weak numerical torsion class. -/
theorem subobject_negative_iff_rightOrthogonal {v : RealProjectiveSpace R} (N : FGModuleCat.{u} R) :
    (∀ {U : FGModuleCat.{u} R} (i : U ⟶ N) [Mono i], ¬ IsZero U →
      realEulerEvaluation k (GrothendieckGroup.of U) v < 0) ↔
      ∀ X, realWeakTorsion k v X → Subsingleton (X ⟶ N) := by
  refine ⟨fun h X hx ↦ ?_,fun h _ i _ hi ↦ subNegative_of_hom_zero k h _ ⟨_,i,inferInstance,hi,rfl⟩⟩
  have hn : subNegative k v N := by
    rintro _ ⟨U,i,_,hu,rfl⟩
    exact h i hu
  exact ⟨fun a b ↦ (hom_zero_of_weak_subNegative k hx hn a).trans (hom_zero_of_weak_subNegative k hx hn b).symm⟩

private theorem approach_above (v : RealProjectiveSpace R) {U : Set (RealProjectiveSpace R)} (hu : IsOpen U) (hv : v ∈ U) :
    let E := U ∩ {w | ∀ i : ↥(simpleIsomorphismClasses R), ev k v (simpleModule i) < ev k w (simpleModule i)}
    IsOpen E ∧ v ∈ closure E := by
  let _ := IsModuleTopology.isTopologicalAddGroup ℝ (RealProjectiveSpace R)
  let H := Homeomorph.neg (RealProjectiveSpace R)
  let V := H ⁻¹' U
  have hv' : -v ∈ V := by simpa [V,H] using hv
  obtain ⟨ho,hc⟩ := approach_below k (-v) (hu.preimage H.continuous) hv'
  let F := V ∩ {w | ∀ i : ↥(simpleIsomorphismClasses R), ev k w (simpleModule i) < ev k (-v) (simpleModule i)}
  have he : H ⁻¹' F = U ∩ {w | ∀ i : ↥(simpleIsomorphismClasses R), ev k v (simpleModule i) < ev k w (simpleModule i)} := by
    ext w
    change (-(-w) ∈ U ∧ _) ↔ _
    simp [H,ev]
  refine ⟨he ▸ ho.preimage H.continuous,?_⟩
  rw [← he,← H.preimage_closure]
  exact hc

/-- If the weak class at v is left orthogonal to one module, both numerical classes
agree with it on a nonempty open set whose closure contains v. -/
theorem open_chamber_of_cocompact_weak {v : RealProjectiveSpace R} {N : FGModuleCat.{u} R}
    (hn : ∀ M, realWeakTorsion k v M ↔ Subsingleton (M ⟶ N)) :
    ∃ E : Set (RealProjectiveSpace R), IsOpen E ∧ E.Nonempty ∧ v ∈ closure E ∧
      ∀ w ∈ E, realStrictTorsion k w = realWeakTorsion k v ∧ realWeakTorsion k w = realWeakTorsion k v := by
  let U := {w | subNegative k w N}
  have hu : IsOpen U := by
    change IsOpen {w | ∀ z ∈ subClassesNeZero N, realEulerEvaluation k z w < 0}
    simp only [Set.ofPred_forall]
    exact (finite_subClassesNeZero k N).isOpen_biInter (fun z _ ↦ isOpen_lt (continuous_eval k z) continuous_const)
  obtain ⟨ho,hc⟩ := approach_above k v hu (subNegative_of_hom_zero k (fun M ↦ (hn M).1))
  refine ⟨_,ho,(Set.nonempty_of_mem hc).of_closure,hc,?_⟩
  intro w hw
  have ha : realWeakTorsion k v ≤ realStrictTorsion k w := fun M hm Q q _ hQ ↦
    lt_of_le_of_lt (hm q) (eval_lt_of_simple_lt k hw.2 Q hQ)
  have hb : realWeakTorsion k w ≤ realWeakTorsion k v := fun M hm ↦ (hn M).2
    ⟨fun f g ↦ (hom_zero_of_weak_subNegative k hm hw.1 f).trans (hom_zero_of_weak_subNegative k hm hw.1 g).symm⟩
  exact ⟨le_antisymm ((strict_le_weak k w).trans hb) ha,le_antisymm hb (ha.trans (strict_le_weak k w))⟩


private theorem generated_le_weak {v : RealProjectiveSpace R} {B : FGModuleCat.{u} R}
    (hB : realWeakTorsion k v B) : generatedTorsionClass B ≤ realWeakTorsion k v := by
  intro M hM
  obtain ⟨g,hg⟩ := exists_matching_integral_weight k ((finite_quotient_classes k B).union (finite_quotient_classes k M)) v
  let D := max (Module.finrank k (B.obj : Type u)) (Module.finrank k (M.obj : Type u))
  let θ := projectiveClassWeight k g
  let η := ((D : ℤ) + 1) • θ + dimensionWeight (R := R) k
  have cmp (X : FGModuleCat.{u} R) (hd : Module.finrank k (X.obj : Type u) ≤ D)
      (hX : nonzeroQuotientClasses X ⊆ nonzeroQuotientClasses B ∪ nonzeroQuotientClasses M) :
      realWeakTorsion k v X ↔ η.strictTorsionClass X := by
    have t {Q : FGModuleCat.{u} R} (q : X ⟶ Q) [Epi q] (hn : ¬ IsZero Q) :
        0 ≤ ev k v Q ↔ 0 < η.eval Q := by
      obtain ⟨he,hle⟩ := hg _ (hX ⟨Q,q,inferInstance,hn,rfl⟩)
      have nonneg : 0 ≤ ev k v Q ↔ 0 ≤ θ.eval Q := by
        change 0 ≤ realEulerEvaluation k _ v ↔ 0 ≤ projectiveClassWeight k g _
        rw [le_iff_lt_or_eq,le_iff_lt_or_eq]
        exact or_congr (by simpa only [not_le] using not_congr hle.symm)
          ⟨fun h ↦ (he.2 h.symm).symm,fun h ↦ (he.1 h.symm).symm⟩
      have hp := dimensionWeight_pos k Q hn
      have hb : (dimensionWeight (R := R) k).eval Q ≤ (D : ℤ) := by
        rw [dimensionWeight_eval]; exact_mod_cast (groundFinrank_le_of_epi k q).trans hd
      rw [nonneg]
      change 0 ≤ θ.eval Q ↔ 0 < ((D : ℤ)+1) * θ.eval Q + (dimensionWeight (R := R) k).eval Q
      constructor
      · intro h
        exact add_pos_of_nonneg_of_pos (mul_nonneg (by positivity) h) hp
      · contrapose!
        intro h
        have ht := mul_le_mul_of_nonneg_left (show θ.eval Q ≤ -1 by omega) (show 0 ≤ (D : ℤ)+1 by positivity)
        linarith
    constructor
    · exact fun h _ q _ hn ↦ (t q hn).1 (h q)
    · intro h Q q _
      by_cases hn : IsZero Q
      · change 0 ≤ realEulerWeight k v (GrothendieckGroup.of Q)
        rw [GrothendieckGroup.of_isZero hn,map_zero]
      · exact (t q hn).2 (h q hn)
  have hb : η.strictTorsionClass B := (cmp B (le_max_left ..) (fun _ h ↦ Or.inl h)).1 hB
  apply (cmp M (le_max_right ..) (fun _ h ↦ Or.inr h)).2
  rw [strictTorsionClass_eq_leftOrthogonal k η] at hb ⊢
  exact fun Y hY f ↦ hM Y (hb Y hY) f

/-- Covariant finiteness alone gives both compactness witnesses for either numerical class. -/
theorem bicompact_real_torsion_of_covariantlyFinite (v : RealProjectiveSpace R)
    {T : ObjectProperty (FGModuleCat.{u} R)} (ht : T = realStrictTorsion k v ∨ T = realWeakTorsion k v)
    (h : CovariantlyFinite T) :
    (∃ B, T = generatedTorsionClass B) ∧ ∃ N : FGModuleCat.{u} R, ∀ M, T M ↔ Subsingleton (M ⟶ N) := by
  apply bicompact_of_covariantlyFinite_torsion k T h
  rcases ht with rfl | rfl
  · exact fun _ ↦ generated_le_strict k
  · exact fun _ ↦ generated_le_weak k

end EFiniteCharacterizations
