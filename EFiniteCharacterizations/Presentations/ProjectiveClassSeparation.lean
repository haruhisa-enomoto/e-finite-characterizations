module

public import EFiniteCharacterizations.Stability.StableSeparationWeights

/-! # Detection of projective classes by Hom into simple modules -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- An indecomposable projective has at most one simple quotient up to isomorphism. -/
theorem FGModuleCat.nonempty_iso_of_simple_quotients [IsArtinianRing R]
    {P S T : FGModuleCat.{u} R} [Module.Projective R P] (hP : Indecomposable P)
    (hS : Simple S) (hT : Simple T) (p : P ⟶ S) (q : P ⟶ T) (hp : p ≠ 0) (hq : q ≠ 0) :
    Nonempty (S ≅ T) := by
  by_contra hne
  let θ : Weight (FGModuleCat.{u} R) := 0
  have hP' : θ.IsSemistable P := ⟨rfl, fun _ ↦ le_refl _⟩
  have hS' : θ.IsStable S := (Weight.isStable_zero_iff_simple _).2 hS
  have hT' : θ.IsStable T := (Weight.isStable_zero_iff_simple _).2 hT
  have := Weight.epi_biprod_lift_of_nonisomorphic_stable hP' hS' hT' hne p q hp hq
  obtain ⟨f, hf⟩ := exists_lift_of_projective (biprod.lift p q) (biprod.lift p (0 : P ⟶ T))
  have hfp : f ≫ p = p := by
    simpa only [Category.assoc, biprod.lift_fst] using congrArg (· ≫ biprod.fst) hf
  have hfq : f ≫ q = 0 := by
    simpa only [Category.assoc, biprod.lift_snd] using congrArg (· ≫ biprod.snd) hf
  have := isIso_of_quotient_eq_self hP p hp f hfp
  exact hq (zero_of_epi_comp f hfq)

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
/-- Every simple module is the quotient of an indecomposable projective. -/
theorem FGModuleCat.exists_indecomposable_projective_epi (S : FGModuleCat.{u} R) (hS : Simple S) :
    ∃ (P : FiniteProjective R) (p : P.val ⟶ S), Indecomposable P.val ∧ Epi p := by
  obtain ⟨P, hP, p, hp⟩ := exists_projective_epi S
  have hnon : p ≠ 0 := fun h ↦ Simple.not_isZero S ((IsZero.iff_id_eq_zero S).2
    ((cancel_epi p).1 (by rw [h, zero_comp, zero_comp])))
  obtain ⟨D, a, b, hab, hD, hne⟩ := exists_indecomposable_retract_nonzero_hom k p hnon
  have hproj : Module.Projective R D :=
    Module.Projective.of_split a.hom.hom b.hom.hom (congrArg (fun f : D ⟶ D ↦ f.hom.hom) hab)
  let θ : Weight (FGModuleCat.{u} R) := 0
  have hD' : θ.IsSemistable D := ⟨rfl, fun _ ↦ le_refl _⟩
  have hS' : θ.IsStable S := (Weight.isStable_zero_iff_simple _).2 hS
  exact ⟨⟨D, hproj⟩, a ≫ p, hD, Weight.epi_of_isSemistable_of_isStable hD' hS' _ hne⟩

private theorem exists_simple_projective_tests :
    let I := ↥(simpleIsomorphismClasses R)
    let S (i : I) := (fromSkeleton (FGModuleCat.{u} R)).obj i.val
    ∃ (Q : I → FiniteProjective R) (p : ∀ i, (Q i).val ⟶ S i),
      (∀ i, Simple (S i)) ∧ (∀ i, Indecomposable (Q i).val) ∧ (∀ i, Epi (p i)) ∧
      (∀ i, 0 < homFinrank k (Q i).val (S i)) ∧
      (∀ i j, i ≠ j → homFinrank k (Q i).val (S j) = 0) := by
  classical
  let _ := IsArtinianRing.of_finite k R
  let I := ↥(simpleIsomorphismClasses R)
  let S (i : I) := (fromSkeleton (FGModuleCat.{u} R)).obj i.val
  have hS (i : I) : Simple (S i) := by
    apply (Weight.isStable_zero_iff_simple (S i)).1
    have hmem : i.val ∈ simpleIsomorphismClasses R := i.property
    exact (congrArg (fun s : Set _ ↦ i.val ∈ s) (stableClasses_zero (R := R))).mpr hmem
  choose Q p hQ hp using fun i ↦ FGModuleCat.exists_indecomposable_projective_epi k (S i) (hS i)
  have hpos (i : I) : 0 < homFinrank k (Q i).val (S i) := by
    have hp' : p i ≠ 0 := fun hf ↦ Simple.not_isZero (S i) ((IsZero.iff_id_eq_zero _).2
      ((cancel_epi (p i)).1 (by rw [hf, zero_comp, zero_comp])))
    exact (homFinrank_pos_iff k _ _).2 ⟨_, hp'⟩
  have hvan (i j : I) (hij : i ≠ j) : homFinrank k (Q i).val (S j) = 0 := by
    apply (homFinrank_eq_zero_iff k _ _).2
    intro q
    by_contra hq
    let _ := (Q i).property
    obtain ⟨p', hp'⟩ := (homFinrank_pos_iff k _ _).1 (hpos i)
    obtain ⟨e⟩ := FGModuleCat.nonempty_iso_of_simple_quotients (hQ i) (hS i) (hS j) p' q hp' hq
    exact hij (Subtype.ext ((toSkeleton_fromSkeleton_obj i.val).symm.trans
      ((congr_toSkeleton_of_iso e).trans (toSkeleton_fromSkeleton_obj j.val))))
  exact ⟨Q, p, hS, hQ, hp, hpos, hvan⟩

/-- A projective class is determined by the evaluations of its Euler
weight on the simple modules. -/
theorem ProjectiveClass.eq_of_eval_eq_on_simples {a b : ProjectiveClass R}
    (h : ∀ S : FGModuleCat.{u} R, Simple S →
      (projectiveClassWeight k a).eval S = (projectiveClassWeight k b).eval S) : a = b := by
  classical
  let _ := IsArtinianRing.of_finite k R
  let I := simpleIsomorphismClasses R
  have hfin : Finite I := finite_simpleIsomorphismClasses k
  let _ := Fintype.ofFinite I
  let S (i : I) := (fromSkeleton (FGModuleCat.{u} R)).obj i.val
  obtain ⟨Q, p, hS, hQ, hp, hpos, hvan⟩ := exists_simple_projective_tests (R := R) k
  let g (i : I) := of (Q i)
  have hclass (P : FiniteProjective R) : ∃ c : I → ℤ, of P = ∑ i, c i • g i := by
    apply of_induction_on k P (motive := fun v ↦ ∃ c : I → ℤ, v = ∑ i, c i • g i)
    · exact ⟨0, by simp⟩
    · rintro x y ⟨c, rfl⟩ ⟨d, rfl⟩
      exact ⟨fun i ↦ c i + d i, by simp [add_smul, Finset.sum_add_distrib]⟩
    · intro T hT
      let _ := T.property
      obtain ⟨S', p', hS', hp'⟩ := FGModuleCat.exists_simple_quotient hT.1
      let j : I := ⟨toSkeleton S', S', rfl, hS'⟩
      let e := fromSkeletonToSkeletonIso S'
      let _ := (Q j).property
      let _ := hp j
      obtain ⟨i⟩ := FGModuleCat.nonempty_iso_of_common_quotient hT (hQ j) p' (p j ≫ e.hom)
        (Simple.not_isZero S')
      refine ⟨fun i ↦ if i = j then 1 else 0, (of_eq_of_iso T (Q j) i).trans ?_⟩
      simp [g]
  obtain ⟨A, B, hAB⟩ := exists_sub (a - b)
  obtain ⟨c, hA⟩ := hclass A
  obtain ⟨d, hB⟩ := hclass B
  let z (i : I) := c i - d i
  have hz : a - b = ∑ i, z i • g i := by
    rw [← hAB, hA, hB, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ ↦ (sub_smul _ _ _).symm)
  have hzi (i : I) : z i = 0 := by
    have he := congrArg (fun v : ProjectiveClass R ↦ (projectiveClassWeight k v).eval (S i)) hz
    have hL : (projectiveClassWeight k (a - b)).eval (S i) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (h _ (hS i))
    rw [hL] at he
    simp only [Weight.eval, map_sum, map_zsmul, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply] at he
    change (0 : ℤ) = ∑ j, z j • (projectiveClassWeight k (g j)).eval (S i) at he
    have hdiag (j : I) : (projectiveClassWeight k (g j)).eval (S i) =
        homFinrank k (Q j).val (S i) := by
      let _ := (Q j).property
      dsimp only [g]
      rw [projectiveClassWeight_of]
      exact projectiveHomWeight_eval k _ _
    simp only [hdiag] at he
    rw [Finset.sum_eq_single i] at he
    · rw [zsmul_eq_mul] at he
      exact (mul_eq_zero.mp he.symm).resolve_right (Int.natCast_ne_zero.mpr (hpos i).ne')
    · intro j _ hji
      rw [hvan j i hji, Nat.cast_zero, smul_zero]
    · simp
  apply sub_eq_zero.mp
  rw [hz]
  simp [hzi]

include k in
theorem linearIndependent_simple_classes :
    LinearIndependent ℤ (fun i : ↥(simpleIsomorphismClasses R) ↦ GrothendieckGroup.of ((fromSkeleton _).obj i.val)) := by
  classical
  let := (finite_simpleIsomorphismClasses (R := R) k).fintype
  obtain ⟨Q, _, _, _, _, hpos, hvan⟩ := exists_simple_projective_tests (R := R) k
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let := (Q i).property
  let w := projectiveHomWeight k (Q i).val
  have hz := congrArg w hc
  simp only [map_sum, map_zsmul, map_zero] at hz
  have hw (j : ↥(simpleIsomorphismClasses R)) :
      w (GrothendieckGroup.of ((fromSkeleton _).obj j.val)) =
        homFinrank k (Q i).val ((fromSkeleton _).obj j.val) := projectiveHomWeight_eval k _ _
  simp only [hw, zsmul_eq_mul] at hz
  rw [Finset.sum_eq_single i] at hz
  · exact (mul_eq_zero.mp hz).resolve_right (by exact_mod_cast (hpos i).ne')
  · intro j _ hji
    exact mul_eq_zero_of_right _ (by exact_mod_cast hvan i j hji.symm)
  · simp

/-- Finitely many integral projective weights jointly distinguish all
ambient Grothendieck classes over an arbitrary field. -/
theorem exists_injective_projective_hom_coordinates :
    ∃ g : ↥(simpleIsomorphismClasses R) → FiniteProjective R,
      Function.Injective (fun (x : GrothendieckGroup (FGModuleCat.{u} R)) t ↦ projectiveClassWeight k (ProjectiveClass.of (g t)) x) := by
  classical
  let _ := IsArtinianRing.of_finite k R
  let I := simpleIsomorphismClasses R
  have hfin : Finite I := finite_simpleIsomorphismClasses k
  let _ := Fintype.ofFinite I
  let S (i : I) := (fromSkeleton (FGModuleCat.{u} R)).obj i.val
  obtain ⟨Q, _, _, _, _, hpos, hvan⟩ := exists_simple_projective_tests (R := R) k
  let g (i : I) := ProjectiveClass.of (Q i)
  refine ⟨Q, fun x y hxy ↦ sub_eq_zero.mp ?_⟩
  obtain ⟨c, hc⟩ := exists_simple_class_coefficients k (x - y)
  change x - y = ∑ i : I, c i • GrothendieckGroup.of (S i) at hc
  have hz (i : I) : c i = 0 := by
    let w := projectiveClassWeight k (g i)
    have h := congrFun hxy i
    have hw : w (x - y) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact h
    rw [hc, map_sum] at hw
    have hval (j : I) : w (GrothendieckGroup.of (S j)) = homFinrank k (Q i).val (S j) := by
      let _ := (Q i).property
      change (projectiveClassWeight k (ProjectiveClass.of (Q i))).eval (S j) = _
      rw [projectiveClassWeight_of]
      exact projectiveHomWeight_eval k _ _
    simp only [map_zsmul, hval, zsmul_eq_mul] at hw
    rw [Finset.sum_eq_single i] at hw
    · exact (mul_eq_zero.mp hw).resolve_right (Int.natCast_ne_zero.mpr (hpos i).ne')
    · intro j _ hji
      exact mul_eq_zero_of_right _ (by exact_mod_cast hvan i j hji.symm)
    · simp
  simpa [hz] using hc

theorem exists_injective_simple_projective_coordinates :
    ∃ g : ↥(simpleIsomorphismClasses R) → ProjectiveClass R,
      Function.Injective (fun (x : GrothendieckGroup (FGModuleCat.{u} R)) t ↦ projectiveClassWeight k (g t) x) := by
  obtain ⟨Q, hQ⟩ := exists_injective_projective_hom_coordinates (R := R) k
  exact ⟨fun i ↦ ProjectiveClass.of (Q i), hQ⟩

theorem exists_injective_projective_weight_coordinates :
    ∃ (n : ℕ) (g : Fin n → ProjectiveClass R),
      Function.Injective (fun (x : GrothendieckGroup (FGModuleCat.{u} R)) t ↦ projectiveClassWeight k (g t) x) := by
  classical
  let := (finite_simpleIsomorphismClasses (R := R) k).fintype
  let e := Fintype.equivFin ↥(simpleIsomorphismClasses R)
  obtain ⟨g, hg⟩ := exists_injective_simple_projective_coordinates (R := R) k
  exact ⟨_, fun t ↦ g (e.symm t), fun x y h ↦ hg (funext fun i ↦ by simpa using congrFun h (e i))⟩

include k in
/-- A family spanning the projective classes of finite projectives has at
least as many members as there are simple modules. -/
theorem simple_count_le_card_of_spanning_projectives {J : Type*} [Fintype J] (v : J → ProjectiveClass R)
    (hv : ∀ G : FiniteProjective R, ProjectiveClass.of G ∈ Submodule.span ℤ (Set.range v)) :
    (simpleIsomorphismClasses R).ncard ≤ Fintype.card J := by
  classical
  let I := ↥(simpleIsomorphismClasses R)
  let _ : Fintype I := (finite_simpleIsomorphismClasses (R := R) k).fintype
  let S (i : I) := (fromSkeleton (FGModuleCat.{u} R)).obj i.val
  obtain ⟨Q,_,_,_,_,hpos,hzero⟩ := exists_simple_projective_tests (R := R) k
  let W := Submodule.span ℤ (Set.range v)
  let a (i : I) : W := ⟨ProjectiveClass.of (Q i),hv _⟩
  have hi : LinearIndependent ℤ a := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    let w : ProjectiveClass R →+ ℤ := {
      toFun := fun g ↦ (projectiveClassWeight k g).eval (S i)
      map_zero' := by simp [Weight.eval]
      map_add' := by intros; simp [Weight.eval] }
    have hz := congrArg (w.comp W.subtype.toAddMonoidHom) hc
    simp only [map_sum,map_zsmul,map_zero] at hz
    have hval (j : I) : (w.comp W.subtype.toAddMonoidHom) (a j) = homFinrank k (Q j).val (S i) := by
      change (projectiveClassWeight k (ProjectiveClass.of (Q j))).eval (S i) = (homFinrank k (Q j).val (S i) : ℤ)
      rw [projectiveClassWeight_of,projectiveHomWeight_eval]
    simp only [hval,zsmul_eq_mul] at hz
    rw [Finset.sum_eq_single i] at hz
    · exact (mul_eq_zero.mp hz).resolve_right (by exact_mod_cast (hpos i).ne')
    · intro j _ hji
      exact mul_eq_zero_of_right _ (by exact_mod_cast hzero j i hji)
    · simp
  let _ : Module.Finite ℤ W := Module.Finite.span_of_finite ℤ (Set.finite_range v)
  simpa [I] using hi.fintype_card_le_finrank.trans (finrank_range_le_card (R := ℤ) v)

include k in
theorem card_le_simple_count_of_independent_classes {I : Type*} [Fintype I]
    {v : I → GrothendieckGroup (FGModuleCat.{u} R)} (hv : LinearIndependent ℤ v) :
    Fintype.card I ≤ (simpleIsomorphismClasses R).ncard := by
  classical
  let := (finite_simpleIsomorphismClasses (R := R) k).fintype
  obtain ⟨g, hg⟩ := exists_injective_simple_projective_coordinates (R := R) k
  let f := LinearMap.pi (fun i ↦ (projectiveClassWeight k (g i)).toIntLinearMap)
  have hi : Function.Injective f := hg
  have h := (hv.map' f (LinearMap.ker_eq_bot.mpr hi)).fintype_card_le_finrank
  simpa using h

end EFiniteCharacterizations
