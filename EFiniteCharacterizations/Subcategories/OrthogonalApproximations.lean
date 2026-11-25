module

public import EFiniteCharacterizations.Subcategories.TorsionApproximations
public import EFiniteCharacterizations.Presentations.MinimalPresentations

/-! # Approximations for the Hom-orthogonal of a torsion class -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R] [IsNoetherianRing R]

/-- Dualizing a projective presentation of a left approximation produces a
map into the Nakayama module. Maps from the orthogonal factor through it,
and its composites from the approximating class vanish. -/
theorem exists_nakayama_approximation (T : ObjectProperty (FGModuleCat.{u} R))
    {P B : FGModuleCat.{u} R} [Module.Projective R P] (a : P ⟶ B)
    (ha : ∀ Y, T Y → ∀ f : P ⟶ Y, ∃ b, a ≫ b = f) :
    ∃ (C : FGModuleCat.{u} R) (p : C ⟶ nakayamaObject k P),
      (∀ Y, T Y → ∀ f : Y ⟶ C, f ≫ p = 0) ∧
      ∀ Y, rightHomOrthogonal B Y → ∀ f : Y ⟶ nakayamaObject k P, ∃ t, t ≫ p = f := by
  obtain ⟨m⟩ := MinimalPresentation.nonempty_minimalPresentation k B
  let D := m.twoTerm
  let _ := m.cover.epi_hom
  let _ := D.projective_source
  let _ := D.projective_target
  let q : D.target ⟶ B := m.cover.hom
  have : Epi q := m.cover.epi_hom
  obtain ⟨u, hu⟩ := FGModuleCat.exists_lift_of_projective q a
  let d := D.differential
  let νd := nakayamaMorphism k d
  let νu := nakayamaMorphism k u
  let C := pullback νd νu
  let p := pullback.snd νd νu
  refine ⟨C, p, ?_, ?_⟩
  · intro Y hY f
    let b := (nakayamaPairing k D.source Y).symm (f ≫ pullback.fst νd νu)
    let c := (nakayamaPairing k P Y).symm (f ≫ p)
    have eq : (Linear.leftComp k Y d).dualMap b = (Linear.leftComp k Y u).dualMap c := by
      apply (nakayamaPairing k D.target Y).injective
      simp only [nakayamaPairing_dual_leftComp, b, c, LinearEquiv.apply_symm_apply, Category.assoc]
      exact congrArg (f ≫ ·) pullback.condition
    have hz : c = 0 := by
      ext v
      obtain ⟨w, hw⟩ := ha Y hY v
      have H := congrArg (fun (z : Module.Dual k (D.target ⟶ Y)) ↦ z (q ≫ w)) eq
      change b (d ≫ q ≫ w) = c (u ≫ q ≫ w) at H
      rw [← Category.assoc d, show d ≫ q = 0 from m.differential_comp_cover, zero_comp, map_zero,
        ← Category.assoc u, hu, hw] at H
      exact H.symm
    exact (show nakayamaPairing k P Y c = f ≫ p from LinearEquiv.apply_symm_apply ..).symm.trans
      (by rw [hz, map_zero])
  · intro Y hY f
    have hi : Function.Injective (Linear.leftComp k Y d) := by
      apply LinearMap.ker_eq_bot.mp
      apply le_antisymm _ bot_le
      intro b hb
      have hz : D.differential ≫ b = 0 := hb
      let g := cokernel.desc D.differential b hz
      have h0 := hY (m.cokernelIso.inv ≫ g)
      have hg : g = 0 := (cancel_epi m.cokernelIso.inv).1 (h0.trans comp_zero.symm)
      change b = 0
      rw [← cokernel.π_desc D.differential b hz]
      exact (congrArg (cokernel.π D.differential ≫ ·) hg).trans comp_zero
    obtain ⟨b, hb⟩ := (LinearMap.dualMap_surjective_iff.mpr hi)
      ((Linear.leftComp k Y u).dualMap ((nakayamaPairing k P Y).symm f))
    have he := congrArg (nakayamaPairing k D.target Y) hb
    simp only [nakayamaPairing_dual_leftComp, LinearEquiv.apply_symm_apply] at he
    exact ⟨pullback.lift (nakayamaPairing k D.source Y b) f he, pullback.lift_snd ..⟩

namespace Weight

private theorem eval_kernel_epi (w : Weight (FGModuleCat.{u} R)) {X Y : FGModuleCat.{u} R}
    (p : X ⟶ Y) [Epi p] : w.eval X = w.eval (kernel p) + w.eval Y := by
  let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  exact w.eval_shortExact S (ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p)
    (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance))

private theorem eval_cokernel_mono (w : Weight (FGModuleCat.{u} R)) {X Y : FGModuleCat.{u} R}
    (i : X ⟶ Y) [Mono i] : w.eval Y = w.eval X + w.eval (cokernel i) := by
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  exact w.eval_shortExact S (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i)
    (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance))

def strictTorsionClass (θ : Weight (FGModuleCat.{u} R)) : ObjectProperty (FGModuleCat.{u} R) :=
  fun X ↦ ∀ {N : FGModuleCat.{u} R} (q : X ⟶ N) [Epi q], ¬ IsZero N → 0 < θ.eval N

def weakTorsionFreeClass (θ : Weight (FGModuleCat.{u} R)) : ObjectProperty (FGModuleCat.{u} R) :=
  fun X ↦ ∀ {U : FGModuleCat.{u} R} (i : U ⟶ X) [Mono i], θ.eval U ≤ 0

include k in
/-- Minimizing a small perturbation of the weight on the quotients gives
the strict torsion submodule and a weak torsion-free quotient. -/
theorem exists_strict_torsion_decomposition (θ : Weight (FGModuleCat.{u} R)) (X : FGModuleCat.{u} R) :
    ∃ (Q : FGModuleCat.{u} R) (p : X ⟶ Q), Epi p ∧ θ.strictTorsionClass (kernel p) ∧
      θ.weakTorsionFreeClass Q := by
  classical
  let D := Module.finrank k (X.obj : Type u)
  let dim := dimensionWeight (R := R) k
  let η := ((D : ℤ) + 1) • θ - dim
  let A := {z | ∃ (Y : FGModuleCat.{u} R) (q : X ⟶ Y), Epi q ∧ GrothendieckGroup.of Y = z}
  have hfin : A.Finite := (finite_classes_of_groundFinrank_le (R := R) k D).subset (by
    rintro _ ⟨Y, q, hq, rfl⟩
    exact ⟨Y, groundFinrank_le_of_epi k q, rfl⟩)
  have hne : hfin.toFinset.Nonempty := ⟨_, hfin.mem_toFinset.2 ⟨X, 𝟙 X, inferInstance, rfl⟩⟩
  obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image hfin.toFinset η hne
  obtain ⟨Q,p,hp,he⟩ := hfin.mem_toFinset.1 hz
  have hle {Y : FGModuleCat.{u} R} (q : X ⟶ Y) [Epi q] : η.eval Q ≤ η.eval Y := by
    change η (GrothendieckGroup.of Q) ≤ _
    rw [he]
    exact hmin _ (hfin.mem_toFinset.2 ⟨Y, q, inferInstance, rfl⟩)
  refine ⟨Q,p,hp,?_,?_⟩
  · intro N q _ hn
    let j := kernel.ι q ≫ kernel.ι p
    have h := hle (cokernel.π j)
    have hN : 0 ≤ η.eval N := by
      linarith only [h, eval_kernel_epi η p, eval_kernel_epi η q, eval_cokernel_mono η j]
    change 0 ≤ ((D : ℤ) + 1) * θ.eval N - dim.eval N at hN
    have hd : 0 < dim.eval N := dimensionWeight_pos k _ hn
    by_contra! hn'
    have hm := mul_nonpos_of_nonneg_of_nonpos (show (0 : ℤ) ≤ (D : ℤ) + 1 by positivity) hn'
    omega
  · intro U i _
    have h := hle (p ≫ cokernel.π i)
    have hu : η.eval U ≤ 0 := by linarith only [h, eval_cokernel_mono η i]
    change ((D : ℤ) + 1) * θ.eval U - dim.eval U ≤ 0 at hu
    have : Module.Finite k (Q.obj : Type u) := Module.Finite.trans R _
    have hdim := (LinearMap.finrank_le_finrank_of_injective (f := i.hom.hom.restrictScalars k)
      ((FGModuleCat.mono_iff_injective _).1 inferInstance)).trans (groundFinrank_le_of_epi k p)
    have hd : dim.eval U ≤ (D : ℤ) := by rw [show dim = dimensionWeight (R := R) k from rfl, dimensionWeight_eval]; exact_mod_cast hdim
    by_contra! hn
    have hpos : 1 ≤ θ.eval U := hn
    have hm := mul_le_mul_of_nonneg_left hpos (show (0 : ℤ) ≤ (D : ℤ) + 1 by positivity)
    omega

theorem strict_weak_hom_zero {θ : Weight (FGModuleCat.{u} R)} {X Y : FGModuleCat.{u} R}
    (hX : θ.strictTorsionClass X) (hY : θ.weakTorsionFreeClass Y) (f : X ⟶ Y) : f = 0 := by
  by_cases hz : IsZero (Abelian.image f)
  · rw [← Abelian.image.fac f, hz.eq_of_src (Abelian.image.ι f) 0, comp_zero]
  · exact False.elim ((hX (Abelian.factorThruImage f) hz).not_ge (hY (Abelian.image.ι f)))

private theorem weakFree_quotient {θ : Weight (FGModuleCat.{u} R)} {X S : FGModuleCat.{u} R}
    (hX : θ.weakTorsionFreeClass X) (hS : θ.eval S = 0) (i : S ⟶ X) [Mono i] :
    θ.weakTorsionFreeClass (cokernel i) := by
  intro U j _
  let q := cokernel.π i ≫ cokernel.π j
  have hn := hX (kernel.ι q)
  linarith only [eval_cokernel_mono θ i, eval_cokernel_mono θ j, eval_kernel_epi θ q, hn, hS]

include k in
/-- Only finitely many pairwise nonisomorphic stable modules map nontrivially
to a fixed module in the weak torsion-free class. -/
theorem finite_stable_sources {θ : Weight (FGModuleCat.{u} R)} (X : FGModuleCat.{u} R)
    (hX : θ.weakTorsionFreeClass X) :
    {x ∈ stableClasses θ | ∃ f : (fromSkeleton _).obj x ⟶ X, f ≠ 0}.Finite := by
  classical
  generalize hd : Module.finrank k (X.obj : Type u) = n
  induction n using Nat.strong_induction_on generalizing X with
  | h n ih =>
    let A (Y : FGModuleCat.{u} R) := {x ∈ stableClasses θ | ∃ f : (fromSkeleton _).obj x ⟶ Y, f ≠ 0}
    change (A X).Finite
    by_cases hn : (A X).Nonempty
    · obtain ⟨x, hx, f, hf⟩ := hn
      let S := (fromSkeleton _).obj x
      have hs : θ.IsStable S := hx
      let e := Abelian.factorThruImage f
      let i := Abelian.image.ι f
      have he := ((Weight.isSemistable_iff_quotients S).1 hs.isSemistable).2 e
      have hI : θ.IsSemistable (Abelian.image f) :=
        hs.isSemistable.of_epi_of_eval_zero e (le_antisymm (hX i) he)
      have hne : e ≠ 0 := fun hz ↦ hf (by rw [← Abelian.image.fac f]; exact (congrArg (· ≫ i) hz).trans zero_comp)
      have := mono_of_isStable_of_isSemistable hs hI e hne
      have : Mono f := Abelian.image.fac f ▸ (inferInstanceAs (Mono (e ≫ i)))
      have hQ : θ.weakTorsionFreeClass (cokernel f) := weakFree_quotient hX hs.2.1 f
      have hdim := eval_cokernel_mono (dimensionWeight (R := R) k) f
      have hpos := dimensionWeight_pos k S hs.1
      simp only [dimensionWeight_eval] at hdim hpos
      have hd' : Module.finrank k ((cokernel f).obj : Type u) < n := by
        change (0 : ℤ) < (Module.finrank k (((fromSkeleton _).obj x).obj : Type u) : ℤ) at hpos
        omega
      apply ((ih _ hd' _ hQ rfl).insert x).subset
      rintro y ⟨hy, g, hg⟩
      by_cases hyx : y = x
      · exact Or.inl hyx
      refine Or.inr ⟨hy, g ≫ cokernel.π f, fun hz ↦ ?_⟩
      let t := Abelian.monoLift f g hz
      have ht : t ≠ 0 := fun h ↦ hg ((Abelian.monoLift_comp f g hz).symm.trans ((congrArg (· ≫ f) h).trans zero_comp))
      have := Weight.isIso_of_nonzero hy hs t ht
      exact hyx ((toSkeleton_fromSkeleton_obj y).symm.trans ((congr_toSkeleton_of_iso (asIso t)).trans
        (toSkeleton_fromSkeleton_obj x)))
    · rw [Set.not_nonempty_iff_eq_empty.mp hn]
      exact Set.finite_empty

end Weight

include k in
/-- A left approximation by the strict torsion class at one weight suffices
for finiteness of its stable isomorphism classes. -/
theorem finite_stableClasses_of_covariantlyFinite_strictTorsion (θ : Weight (FGModuleCat.{u} R))
    (h : CovariantlyFinite θ.strictTorsionClass) : (stableClasses θ).Finite := by
  let P := FGModuleCat.of R R
  let _ : Module.Projective R P := inferInstanceAs (Module.Projective R R)
  obtain ⟨B, a, hB, ha⟩ := h P
  obtain ⟨C, p, hp, hfac⟩ := exists_nakayama_approximation k θ.strictTorsionClass a ha
  obtain ⟨Q, q, hq, hK, hQ⟩ := θ.exists_strict_torsion_decomposition k C
  let b := Abelian.epiDesc q p (hp _ hK (kernel.ι q))
  have hb : q ≫ b = p := Abelian.comp_epiDesc ..
  apply (Weight.finite_stable_sources k Q hQ).subset
  intro x hx
  let S := (fromSkeleton _).obj x
  have hs : θ.IsStable S := hx
  have horth : rightHomOrthogonal B S := fun f ↦ Weight.strict_weak_hom_zero hB hs.isSemistable.2 f
  have hdim := dimensionWeight_pos k S hs.1
  rw [dimensionWeight, projectiveHomWeight_eval, Int.natCast_pos, homFinrank_eq_finrank] at hdim
  have := finiteModuleHom_isFinite k P S
  have he : Module.finrank k (S ⟶ nakayamaObject k P) = Module.finrank k (P ⟶ S) :=
    (nakayamaPairing k P S).finrank_eq.symm.trans (Subspace.dual_finrank_eq ..)
  obtain ⟨f, hf⟩ := (homFinrank_pos_iff k S _).1 (by rw [homFinrank_eq_finrank, he]; exact hdim)
  obtain ⟨t, ht⟩ := hfac S horth f
  exact ⟨hx, t ≫ q, fun hz ↦ hf (by rw [← ht, ← hb, ← Category.assoc, hz, zero_comp])⟩

include k in
theorem isEFinite_iff_functoriallyFinite_strictTorsion [IsArtinianRing R] :
    IsEFinite R ↔ ∀ g : ProjectiveClass R, FunctoriallyFinite ((projectiveClassWeight k g).strictTorsionClass) := by
  refine ⟨fun h g ↦ functoriallyFinite_strictTorsion_of_isEFinite k h g, fun h ↦ ?_⟩
  apply (isEFinite_iff_stableFiniteAtAllIntegralWeights_allFields k).2
  intro g
  let θ := projectiveClassWeight (R := R) k g
  exact finite_stableClasses_of_covariantlyFinite_strictTorsion k θ (h g).1

end EFiniteCharacterizations
