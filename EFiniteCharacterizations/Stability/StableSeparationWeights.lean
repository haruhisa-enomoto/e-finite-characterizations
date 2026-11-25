module

public import EFiniteCharacterizations.Presentations.TauRigid
public import EFiniteCharacterizations.Presentations.PresiltingCompletions
public import EFiniteCharacterizations.Presentations.ProjectiveRankBound
public import EFiniteCharacterizations.Stability.StableFiniteness

/-! # Integral weights separating stable classes at a covered weight -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- Two nonzero maps to nonisomorphic stable objects are jointly epic on a
semistable source at the same weight. -/
theorem Weight.epi_biprod_lift_of_nonisomorphic_stable
    {θ : Weight (FGModuleCat.{u} R)} {X S T : FGModuleCat.{u} R}
    (hX : θ.IsSemistable X) (hS : θ.IsStable S) (hT : θ.IsStable T) (hst : ¬ Nonempty (S ≅ T))
    (p : X ⟶ S) (q : X ⟶ T) (hp : p ≠ 0) (hq : q ≠ 0) :
    Epi (biprod.lift p q) := by
  let _ := Weight.epi_of_isSemistable_of_isStable hX hS p hp
  let i := kernel.ι p
  have hq' : i ≫ q ≠ 0 := by
    intro hz
    let g := Abelian.epiDesc p q hz
    have hg : g = 0 := Weight.hom_eq_zero_of_not_iso hS hT hst g
    exact hq ((Abelian.comp_epiDesc p q hz).symm.trans ((congrArg (p ≫ ·) hg).trans comp_zero))
  let _ := Weight.epi_of_isSemistable_of_isStable (hX.kernel_of_epi hS.isSemistable p) hT (i ≫ q) hq'
  apply Preadditive.epi_of_cancel_zero
  intro Y f hf
  let a := biprod.inl ≫ f
  let b := biprod.inr ≫ f
  have hfb : biprod.desc a b = f := biprod.hom_ext' _ _ (by simp [a]) (by simp [b])
  have hz : p ≫ a + q ≫ b = 0 := by rw [← biprod.lift_desc, hfb, hf]
  have hb : b = 0 := by
    apply zero_of_epi_comp (i ≫ q)
    have h := congrArg (i ≫ ·) hz
    change kernel.ι p ≫ (p ≫ a + q ≫ b) = kernel.ι p ≫ 0 at h
    simpa only [Preadditive.comp_add, ← Category.assoc, kernel.condition, zero_comp, zero_add, comp_zero] using h
  have ha : a = 0 := by
    apply zero_of_epi_comp p
    simpa only [hb, comp_zero, add_zero] using hz
  rw [← hfb, ha, hb]
  exact biprod.hom_ext' _ _ (by rw [biprod.inl_desc, comp_zero]) (by rw [biprod.inr_desc, comp_zero])

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
/-- A nonzero map from a finite module remains nonzero on an indecomposable
direct summand. -/
theorem FGModuleCat.exists_indecomposable_retract_nonzero_hom {B M : FGModuleCat.{u} R}
    (f : B ⟶ M) (hf : f ≠ 0) :
    ∃ (D : FGModuleCat.{u} R) (s : D ⟶ B) (r : B ⟶ D),
      s ≫ r = 𝟙 D ∧ Indecomposable D ∧ s ≫ f ≠ 0 := by
  classical
  let A (n : ℕ) := ∃ (D : FGModuleCat.{u} R) (s : D ⟶ B) (r : B ⟶ D),
    s ≫ r = 𝟙 D ∧ s ≫ f ≠ 0 ∧ Module.finrank k (D.obj : Type u) = n
  have hA : ∃ n, A n := ⟨_, B, 𝟙 B, 𝟙 B, by simp, by simpa, rfl⟩
  obtain ⟨D, s, r, hsr, hnon, hdim⟩ := Nat.find_spec hA
  refine ⟨D, s, r, hsr, ⟨fun hz ↦ hnon (hz.eq_of_src _ _), ?_⟩, hnon⟩
  intro U V e
  by_contra! ⟨hu, hv⟩
  have hd := ((FGModuleCat.isoToLinearEquiv e).restrictScalars k).finrank_eq.trans
    (FGModuleCat.finrank_biprod k U V)
  change Module.finrank k (D.obj : Type u) =
    Module.finrank k (U.obj : Type u) + Module.finrank k (V.obj : Type u) at hd
  have hdu := dimensionWeight_pos k U hu
  have hdv := dimensionWeight_pos k V hv
  rw [dimensionWeight_eval, Int.natCast_pos] at hdu hdv
  have hmin (C : FGModuleCat.{u} R) (a : C ⟶ D) (b : D ⟶ C) (hab : a ≫ b = 𝟙 C)
      (hc : Module.finrank k (C.obj : Type u) < Module.finrank k (D.obj : Type u)) :
      a ≫ s ≫ f = 0 := by
    by_contra hne
    have hn : A (Module.finrank k (C.obj : Type u)) := ⟨C, a ≫ s, r ≫ b,
      by simp only [Category.assoc, ← Category.assoc s, hsr, Category.id_comp, hab],
      by simpa only [Category.assoc] using hne, rfl⟩
    exact (not_lt_of_ge (Nat.find_min' hA hn)) (hc.trans_eq hdim)
  have hau := hmin U (biprod.inl ≫ e.inv) (e.hom ≫ biprod.fst) (by simp) (by omega)
  have hav := hmin V (biprod.inr ≫ e.inv) (e.hom ≫ biprod.snd) (by simp) (by omega)
  apply hnon
  apply zero_of_epi_comp e.inv
  exact biprod.hom_ext' _ _ (by simpa only [Category.assoc, comp_zero] using hau)
    (by simpa only [Category.assoc, comp_zero] using hav)

namespace TwoTerm

include k in
/-- The Euler semistable objects of a presilting complex are closed under
binary direct sums. -/
theorem isSemistable_eulerWeight_biprod (P : TwoTerm R) (hP : P.IsPresilting)
    {S T : FGModuleCat.{u} R} (hS : (P.eulerWeight k).IsSemistable S)
    (hT : (P.eulerWeight k).IsSemistable T) :
    (P.eulerWeight k).IsSemistable (S ⊞ T) := by
  rw [P.isSemistable_eulerWeight_iff_perpendicular k hP] at hS hT ⊢
  exact ⟨⟨fun _ _ ↦ biprod.hom_ext _ _ (hS.1.elim _ _) (hT.1.elim _ _)⟩,
    ⟨fun _ _ ↦ biprod.hom_ext' _ _ (hS.2.elim _ _) (hT.2.elim _ _)⟩⟩

include k in
/-- A summand of a Bongartz completion detects one stable class and is
perpendicular to every other stable class at the original weight. -/
theorem exists_stable_separating_summand (P : TwoTerm R) (hP : P.IsPresilting)
    {S : FGModuleCat.{u} R} (hS : (P.eulerWeight k).IsStable S) :
    ∃ V : TwoTerm R, (P.directSum V).IsPresilting ∧ 0 < (V.eulerWeight k).eval S ∧
      ∀ T : FGModuleCat.{u} R, (P.eulerWeight k).IsStable T → ¬ Nonempty (S ≅ T) →
        (V.eulerWeight k).IsSemistable T := by
  let _ := IsArtinianRing.of_finite k R
  obtain ⟨Q, hb, hQ, hgen⟩ := P.exists_bongartz_complement k hP
  let B := cokernel Q.differential
  have hs := ((P.isSemistable_eulerWeight_iff_perpendicular k hP _).1 hS.isSemistable).2
  have hgenS := (hgen S).1 ((P.surjective_precompose_iff_no_hom_nakayamaKernel k S).2 hs)
  obtain ⟨f, hf⟩ := hgenS.exists_nonzero_hom hS.1
  obtain ⟨D, s, r, hsr, hind, hnon⟩ := FGModuleCat.exists_indecomposable_retract_nonzero_hom k f hf
  obtain ⟨G, p, hp, hG, hdesc, hproj, hlift⟩ :=
    P.exists_semistable_projective_quotient_of_retract k hP Q hb hQ s r hsr
  obtain ⟨u, hu⟩ := hdesc hS.isSemistable (s ≫ f)
  have hnu : u ≠ 0 := fun hz ↦ hnon (hu.symm.trans ((congrArg (p ≫ ·) hz).trans comp_zero))
  obtain ⟨m⟩ := MinimalPresentation.nonempty_minimalPresentation k D
  let V := m.twoTerm
  have transfer {M : FGModuleCat.{u} R} (hm : Function.Surjective (P.precompose M)) :
      Function.Surjective (V.precompose M) :=
    m.surjective_precompose_of_presentation_retract s r hsr Q (cokernel.π _)
      (cokernel.condition _) (ShortComplex.exact_cokernel _) (hQ M hm)
  have : Epi r := epi_of_epi_fac hsr
  have hD := (P.surjective_precompose_iff_no_hom_nakayamaKernel k _).1 hb
  have hPV := P.surjective_precompose_of_iso m.cokernelIso.symm
    ((P.surjective_precompose_iff_no_hom_nakayamaKernel k D).2
      ⟨fun _ _ ↦ (cancel_epi r).1 (hD.elim _ _)⟩)
  have hVV := transfer hPV
  have hv := (surjective_boundary_iff_surjective_precompose V V).2 hVV
  have hker {T : FGModuleCat.{u} R} (ht : (P.eulerWeight k).IsSemistable T) :
      Subsingleton (T ⟶ V.nakayamaKernel k) :=
    (V.surjective_precompose_iff_no_hom_nakayamaKernel k T).1
      (transfer ((P.surjective_precompose_iff_no_hom_nakayamaKernel k T).2
        ((P.isSemistable_eulerWeight_iff_perpendicular k hP T).1 ht).2))
  refine ⟨V,compatible_of_precompose k hP hPV
    (transfer ((surjective_boundary_iff_surjective_precompose P P).1 hP)) hVV,?_,?_⟩
  · rw [V.eulerWeight_eq_perpendicular_difference k,
      (homFinrank_eq_zero_iff k _ _).2 (fun f ↦ (hker hS.isSemistable).elim f 0),Nat.cast_zero,sub_zero]
    apply Int.natCast_pos.mpr
    apply (homFinrank_pos_iff k _ _).2
    exact ⟨m.cokernelIso.hom ≫ s ≫ f,fun hz ↦ hnon (zero_of_epi_comp _ hz)⟩
  intro T hT hst
  apply (V.isSemistable_eulerWeight_iff_perpendicular k hv T).2
  suffices hh : ∀ a : D ⟶ T, a = 0 from
    ⟨⟨fun f g ↦ (cancel_epi m.cokernelIso.inv).1 ((hh _).trans (hh _).symm)⟩,hker hT.isSemistable⟩
  intro a
  by_contra hna
  obtain ⟨v, hv⟩ := hdesc hT.isSemistable a
  have hn : v ≠ 0 := fun hz ↦ hna (hv.symm.trans ((congrArg (p ≫ ·) hz).trans comp_zero))
  let q := biprod.lift u v
  have : Epi q := Weight.epi_biprod_lift_of_nonisomorphic_stable hG hS hT hst u v hnu hn
  have hW := P.isSemistable_eulerWeight_biprod k hP hS.isSemistable hT.isSemistable
  obtain ⟨b, hq⟩ := hproj q hG hW (biprod.lift u 0)
  have hbu : b ≫ u = u := by
    simpa only [q, Category.assoc, biprod.lift_fst] using congrArg (· ≫ biprod.fst) hq
  have hbv : b ≫ v = 0 := by
    simpa only [q, Category.assoc, biprod.lift_snd] using congrArg (· ≫ biprod.snd) hq
  obtain ⟨e, he⟩ := hlift b
  have hpe : e ≫ p ≫ u = p ≫ u := by rw [← Category.assoc, he, Category.assoc, hbu]
  have hpa : p ≫ u ≠ 0 := hu ▸ hnon
  have : IsIso e := FGModuleCat.isIso_of_quotient_eq_self hind (p ≫ u) hpa e hpe
  have hz : e ≫ a = 0 := by rw [← hv, ← Category.assoc, he, Category.assoc, hbv, comp_zero]
  exact hna (zero_of_epi_comp e hz)

include k in
/-- Each stable isomorphism class at a presilting weight is separated from
all the other stable classes by an integral projective weight. -/
theorem exists_stable_separating_projective_weight (P : TwoTerm R) (hP : P.IsPresilting)
    {S : FGModuleCat.{u} R} (hS : (P.eulerWeight k).IsStable S) :
    ∃ g : ProjectiveClass R, 0 < (projectiveClassWeight k g).eval S ∧
      ∀ T : FGModuleCat.{u} R, (P.eulerWeight k).IsStable T → ¬ Nonempty (S ≅ T) →
        (projectiveClassWeight k g).eval T = 0 := by
  obtain ⟨V,_,hpos,hsem⟩ := P.exists_stable_separating_summand k hP hS
  refine ⟨V.projectiveClass,?_,?_⟩
  · rwa [V.projectiveClassWeight_eq_eulerWeight k]
  · intro T hT hst
    rw [V.projectiveClassWeight_eq_eulerWeight k]
    exact (hsem T hT hst).1

include k in
/-- The exact Grothendieck classes of stable modules at a covered weight
are integrally linearly independent. -/
theorem linearIndependent_stableClasses_eulerWeight (P : TwoTerm R) (hP : P.IsPresilting) :
    LinearIndependent ℤ (fun x : stableClasses (P.eulerWeight k) ↦
      GrothendieckGroup.of ((fromSkeleton (FGModuleCat.{u} R)).obj x.val)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc x hx
  let S (y : stableClasses (P.eulerWeight k)) := (fromSkeleton (FGModuleCat.{u} R)).obj y.val
  have hS (y : stableClasses (P.eulerWeight k)) : (P.eulerWeight k).IsStable (S y) := y.property
  obtain ⟨g, hg, hvan⟩ := P.exists_stable_separating_projective_weight k hP (hS x)
  let w := projectiveClassWeight k g
  have hz := congrArg w hc
  simp only [map_sum, map_zsmul, map_zero] at hz
  change (∑ y ∈ s, c y • w.eval (S y)) = 0 at hz
  have he := Finset.sum_eq_single x (f := fun y ↦ c y • w.eval (S y)) (s := s)
    (fun y _ hy ↦ by
      have hne : ¬ Nonempty (S x ≅ S y) := by
        rintro ⟨i⟩
        apply hy
        apply Subtype.ext
        exact (toSkeleton_fromSkeleton_obj y.val).symm.trans
          ((congr_toSkeleton_of_iso i.symm).trans (toSkeleton_fromSkeleton_obj x.val))
      rw [hvan _ (hS y) hne, smul_zero])
    (fun hn ↦ (hn hx).elim)
  have hmul := he.symm.trans hz
  rw [zsmul_eq_mul] at hmul
  exact (mul_eq_zero.mp hmul).resolve_right hg.ne'

end TwoTerm

/-- In an E-finite algebra the stable classes at every integral projective
weight are integrally linearly independent in the ambient group. -/
theorem linearIndependent_stableClasses_of_isEFinite (h : IsEFinite R) (g : ProjectiveClass R) :
    LinearIndependent ℤ (fun x : stableClasses (projectiveClassWeight (R := R) k g) ↦
      GrothendieckGroup.of ((fromSkeleton (FGModuleCat.{u} R)).obj x.val)) := by
  obtain ⟨P, hP, hg⟩ := h g
  rw [← hg, P.projectiveClassWeight_eq_eulerWeight k]
  exact P.linearIndependent_stableClasses_eulerWeight k hP

/-- At a fixed integral projective weight, a stable module of a given
ambient class is unique up to isomorphism in an E-finite algebra. -/
theorem nonempty_iso_of_isEFinite_of_stable_of_class_eq (h : IsEFinite R) (g : ProjectiveClass R)
    {S T : FGModuleCat.{u} R} (hS : (projectiveClassWeight k g).IsStable S)
    (hT : (projectiveClassWeight k g).IsStable T)
    (he : GrothendieckGroup.of S = GrothendieckGroup.of T) : Nonempty (S ≅ T) := by
  obtain ⟨P, hP, hg⟩ := h g
  rw [← hg, P.projectiveClassWeight_eq_eulerWeight k] at hS hT
  by_contra hn
  obtain ⟨w, hp, hz⟩ := P.exists_stable_separating_projective_weight k hP hS
  have hq := hz T hT hn
  rw [Weight.eval, he] at hp
  exact (ne_of_gt hp) hq

end EFiniteCharacterizations
