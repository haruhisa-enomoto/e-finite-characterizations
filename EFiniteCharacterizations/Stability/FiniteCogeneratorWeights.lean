module

public import EFiniteCharacterizations.LargeModules.EndofiniteCogenerator
public import EFiniteCharacterizations.LargeModules.GenericKernelWeight
public import EFiniteCharacterizations.Subcategories.OrthogonalApproximations
public import EFiniteCharacterizations.Stability.OppositeAlgebra

/-! # Stable classes at weights with a finite cogenerator -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ModuleCat.Algebra
universe u
namespace EFiniteCharacterizations
variable {R S : Type u} [Ring R] [Ring S] [IsNoetherianRing R] [IsNoetherianRing S]

private noncomputable def dualPower (E : (FGModuleCat.{u} S)ᵒᵖ ≌ FGModuleCat.{u} R)
    (B : FGModuleCat.{u} S) (n : ℕ) :
    E.functor.obj (op (⨁ fun _ : Fin n ↦ B)) ≅ FGModuleCat.of R (Fin n → E.functor.obj (op B)) := by
  classical
  let A := fun _ : Fin n ↦ B
  let D := fun _ : Fin n ↦ E.functor.obj (op B)
  let π (i : Fin n) := E.functor.map (biproduct.ι A i).op
  let ι (i : Fin n) := E.functor.map (biproduct.π A i).op
  let F := forget₂ (FGModuleCat R) (ModuleCat.{u} R)
  let _ : PreservesBiproduct D F := preservesBiproduct_of_preservesCoproduct F
  have := E.functor.additive_of_preserves_binary_products
  let j : (⨁ D) ≅ FGModuleCat.of R (Fin n → E.functor.obj (op B)) :=
    F.preimageIso ((F.mapBiproduct D).trans (ModuleCat.biproductIsoPi (fun _ : Fin n ↦ (E.functor.obj (op B)).obj)))
  refine Iso.trans ?_ j
  refine ⟨biproduct.lift π,biproduct.desc ι,?_,?_⟩
  · rw [biproduct.lift_desc]
    simp only [π,ι,← E.functor.map_comp,← op_comp, ← E.functor.map_sum, ← op_sum,
      biproduct.total, op_id,E.functor.map_id]
    rfl
  · apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    by_cases hij : i = j
    · subst j; simp [A,D,π,ι,← E.functor.map_comp,← op_comp]
    · simp [π,ι,← E.functor.map_comp,← op_comp,Ne.symm hij,hij]

private theorem generated_iff_dual_cogenerated (E : (FGModuleCat.{u} S)ᵒᵖ ≌ FGModuleCat.{u} R)
    (B X : FGModuleCat.{u} S) :
    IsGeneratedBy B X ↔ cogeneratedByModule (E.functor.obj (op B)).obj (E.functor.obj (op X)) := by
  constructor
  · rintro ⟨n,q,hq⟩
    let f := E.functor.map q.op ≫ (dualPower E B n).hom
    exact ⟨n,f.hom.hom,(FGModuleCat.mono_iff_injective f).1 inferInstance⟩
  · rintro ⟨n,f,hf⟩
    let a : E.functor.obj (op X) ⟶ FGModuleCat.of R (Fin n → E.functor.obj (op B)) := FGModuleCat.ofHom f
    have : Mono a := (FGModuleCat.mono_iff_injective a).2 hf
    let q := E.functor.preimage (a ≫ (dualPower E B n).inv)
    have : Mono (E.functor.map q) := by dsimp [q]; rw [E.functor.map_preimage]; infer_instance
    have : Mono q := E.functor.mono_of_mono_map inferInstance
    exact ⟨n,q.unop,inferInstance⟩

noncomputable def dualWeight (E : (FGModuleCat.{u} S)ᵒᵖ ≌ FGModuleCat.{u} R)
    (θ : Weight (FGModuleCat.{u} R)) : Weight (FGModuleCat.{u} S) := -(θ.comp (GrothendieckGroup.mapAnti E))

private theorem eval_dual (E : (FGModuleCat.{u} S)ᵒᵖ ≌ FGModuleCat.{u} R)
    (θ : Weight (FGModuleCat.{u} R)) (X : FGModuleCat.{u} S) :
    (dualWeight E θ).eval X = -θ.eval (E.functor.obj (op X)) := by
  simp [dualWeight,Weight.eval,GrothendieckGroup.mapAnti,GrothendieckGroup.lift_of]

private theorem dual_isZero_iff (E : (FGModuleCat.{u} S)ᵒᵖ ≌ FGModuleCat.{u} R)
    (X : FGModuleCat.{u} S) : IsZero (E.functor.obj (op X)) ↔ IsZero X := by
  simp only [IsZero.iff_id_eq_zero]
  constructor
  · intro h
    apply Quiver.Hom.op_inj
    apply E.functor.map_injective
    simpa using h
  · intro h
    rw [← E.functor.map_id,← E.functor.map_zero]
    exact E.functor.congr_map (by simpa using congrArg Quiver.Hom.op h)

private def strictFree (θ : Weight (FGModuleCat.{u} R)) (X : FGModuleCat.{u} R) : Prop :=
  ∀ {U : FGModuleCat.{u} R} (i : U ⟶ X) [Mono i], ¬ IsZero U → θ.eval U < 0

private theorem strict_dual_iff (E : (FGModuleCat.{u} S)ᵒᵖ ≌ FGModuleCat.{u} R)
    (θ : Weight (FGModuleCat.{u} R)) (X : FGModuleCat.{u} S) :
    (dualWeight E θ).strictTorsionClass X ↔ strictFree θ (E.functor.obj (op X)) := by
  constructor
  · intro ht U i _ hn
    let A := (E.inverse.obj U).unop
    let e := E.counitIso.app U
    let t : op A ⟶ op X := E.functor.preimage (e.hom ≫ i)
    have : Mono (E.functor.map t) := by dsimp [t]; rw [E.functor.map_preimage]; infer_instance
    have : Mono t := E.functor.mono_of_mono_map inferInstance
    have hA : ¬ IsZero A := fun hz ↦ hn (((dual_isZero_iff E A).2 hz).of_iso e.symm)
    have h := ht t.unop hA
    rw [eval_dual] at h
    have eq : θ.eval (E.functor.obj (op A)) = θ.eval U := θ.eval_eq_of_isIso e.hom
    change 0 < -θ.eval (E.functor.obj (op A)) at h
    rw [eq] at h
    omega
  · intro hf Q q _ hn
    have h := hf (E.functor.map q.op) (fun hz ↦ hn ((dual_isZero_iff E Q).1 hz))
    rw [eval_dual]; omega

theorem stable_dual (E : (FGModuleCat.{u} S)ᵒᵖ ≌ FGModuleCat.{u} R)
    (θ : Weight (FGModuleCat.{u} R)) (X : FGModuleCat.{u} S)
    (hx : θ.IsStable (E.functor.obj (op X))) : (dualWeight E θ).IsStable X := by
  refine ⟨fun hz ↦ hx.1 ((dual_isZero_iff E X).2 hz),by rw [eval_dual,hx.2.1,neg_zero],?_⟩
  intro U i _ hn hi
  let q := E.functor.map i.op
  have hq : ¬ IsIso q := fun hh ↦ hi (by
    have := isIso_of_reflects_iso i.op E.functor
    exact (isIso_op_iff i).1 ‹_›)
  have hk : ¬ IsZero (kernel q) := fun hz ↦ hq (by
    have := Abelian.mono_of_kernel_ι_eq_zero q (hz.eq_of_src _ _)
    exact isIso_of_mono_of_epi q)
  have hp : ¬ IsIso (kernel.ι q) := fun hh ↦ hn ((dual_isZero_iff E U).1
    ((IsZero.iff_id_eq_zero _).2 ((cancel_epi q).1 (by
      have hzero : q = 0 := (cancel_epi (kernel.ι q)).1 (by simp)
      simp [hzero]))))
  have hneg := hx.2.2 (kernel.ι q) hk hp
  let T := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hseq := θ.eval_shortExact T (ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel q)
    (by dsimp [T]; infer_instance) (by dsimp [T]; infer_instance))
  change θ.eval (E.functor.obj (op X)) = θ.eval (kernel q) + θ.eval (E.functor.obj (op U)) at hseq
  rw [hx.2.1] at hseq
  rw [eval_dual]
  omega

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R] [IsArtinianRing R]

include k in
omit [IsArtinianRing R] in
/-- If the strictly negative subobject test at a weight is cogenerated by a
finite module, there are only finitely many stable isomorphism classes there. -/
theorem finite_stableClasses_of_finite_cogenerator (θ : Weight (FGModuleCat.{u} R))
    (M : FGModuleCat.{u} R)
    (hM : cogeneratedByModule M.obj = (fun X ↦ ∀ {U : FGModuleCat.{u} R} (i : U ⟶ X)
      [Mono i], ¬ IsZero U → θ.eval U < 0)) : (stableClasses θ).Finite := by
  classical
  let : IsNoetherianRing Rᵐᵒᵖ := isNoetherian_of_tower k inferInstance
  let E := Contragredient.reverseDualityEquivalence k R
  let B := (E.inverse.obj M).unop
  let η := dualWeight E θ
  let e := E.counitIso.app M
  have hc (X : FGModuleCat.{u} R) : cogeneratedByModule (E.functor.obj (op B)).obj X ↔
      cogeneratedByModule M.obj X := by
    constructor
    · rintro ⟨n,f,hf⟩
      exact ⟨n,LinearMap.pi (fun i ↦ e.hom.hom.hom.comp ((LinearMap.proj i).comp f)),
        fun x y h ↦ hf (funext (fun i ↦ ((FGModuleCat.mono_iff_injective e.hom).1 inferInstance) (congrFun h i)))⟩
    · rintro ⟨n,f,hf⟩
      exact ⟨n,LinearMap.pi (fun i ↦ e.inv.hom.hom.comp ((LinearMap.proj i).comp f)),
        fun x y h ↦ hf (funext (fun i ↦ ((FGModuleCat.mono_iff_injective e.inv).1 inferInstance) (congrFun h i)))⟩
  have heq : η.strictTorsionClass = IsGeneratedBy B := by
    funext X
    apply propext
    rw [generated_iff_dual_cogenerated E,strict_dual_iff,hc,hM]
    rfl
  have hfin := finite_stableClasses_of_covariantlyFinite_strictTorsion k η
    (heq ▸ (functoriallyFinite_generatedBy k B).1)
  let objs (x : Skeleton (FGModuleCat.{u} Rᵐᵒᵖ)) :=
    toSkeleton (E.functor.obj (op ((fromSkeleton _).obj x)))
  apply (hfin.image objs).subset
  intro x hx
  let X := (fromSkeleton (FGModuleCat.{u} R)).obj x
  let A := (E.inverse.obj X).unop
  let j := fromSkeletonToSkeletonIso A
  let f : E.functor.obj (op ((fromSkeleton _).obj (toSkeleton A))) ≅ X :=
    E.functor.mapIso j.symm.op ≪≫ E.counitIso.app X
  exact ⟨toSkeleton A,stable_dual E θ _ ((show θ.IsStable X from hx).of_iso f.symm),
    (congr_toSkeleton_of_iso f).trans (toSkeleton_fromSkeleton_obj x)⟩

include k in
/-- One missing weight over an E-infinite algebra forces a generic grain
summand in every endofinite splitting witness for its numerical pair. -/
theorem exists_weight_forcing_grain_retract (hn : ¬ IsEFinite R) :
    ∃ γ : ProjectiveClass R, (¬ ∃ P : TwoTerm R, P.IsPresilting ∧ P.projectiveClass = γ) ∧
      ∀ (N : ModuleCat.{u} R), IsEndofinite N →
      SplitsOnCogeneratedModules k N →
      cogeneratedByModule N = (fun X ↦ ∀ {U : FGModuleCat.{u} R} (i : U ⟶ X)
        [Mono i], ¬ IsZero U → (projectiveClassWeight k γ).eval U < 0) →
      ∃ G : ModuleCat.{u} R, Nonempty (Retract G N) ∧ IsGenericGrain k G := by
  obtain ⟨γ,r,_,hr⟩ := exists_infinite_stableClassesOfEndolength_allFields k hn
  refine ⟨γ,?_,fun N he hs hc ↦ ?_⟩
  · rintro ⟨P,hP,rfl⟩
    rw [P.projectiveClassWeight_eq_eulerWeight k] at hr
    exact hr ((P.finite_stableClasses_eulerWeight k hP).subset (stableClassesOfEndolength_subset_stableClasses k _ r))
  apply (finite_cogenerator_or_grain_retract k he hs).resolve_left
  rintro ⟨M,_,hM⟩
  exact hr ((finite_stableClasses_of_finite_cogenerator k _ M (hM.symm.trans hc)).subset
    (stableClassesOfEndolength_subset_stableClasses k _ r))

/-- An injective tensor boundary for a suitable tuple in a division ring
over the ground field suffices for existence of a generic grain. -/
theorem exists_generic_grain_of_injective_boundaries
    (coefficients : ∀ (V : Type u) [Fintype V], ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra k D)
      (a : V → D), Function.Injective (freeTensorBoundary k a))
    (hn : ¬ IsEFinite R) : ∃ G : ModuleCat.{u} R, IsGenericGrain k G := by
  obtain ⟨γ,_,hg⟩ := exists_weight_forcing_grain_retract k hn
  obtain ⟨N,he,hs,_,hc⟩ := exists_endofinite_kernel_of_commutators (k := k) (R := R) (fun V _ ↦ by
    obtain ⟨D,_,_,a,ha⟩ := coefficients V
    exact ⟨D,inferInstance,inferInstance,a,simultaneous_commutators_of_injective_boundary k a ha⟩) γ
  obtain ⟨G,_,hG⟩ := hg N he hs hc
  exact ⟨G,hG⟩

/-- Division-ring universal localizations of finitely generated free algebras
suffice to produce a generic grain over any E-infinite algebra. -/
theorem exists_generic_grain_of_free_localizations
    (freeLoc : ∀ (V : Type u) [Fintype V], ∃ (K : Type u) (_ : DivisionRing K) (_ : Algebra k K)
      (g : FreeAlgebra k V →ₐ[k] K) (ι : Type u) (φ : ι → TwoTerm (FreeAlgebra k V)),
        IsUniversalLocalization φ g.toRingHom)
    (hn : ¬ IsEFinite R) : ∃ G : ModuleCat.{u} R, IsGenericGrain k G := by
  obtain ⟨γ,_,hg⟩ := exists_weight_forcing_grain_retract k hn
  obtain ⟨N,he,hs,_,hc⟩ := exists_endofinite_kernel_of_free_localizations freeLoc γ
  obtain ⟨G,_,hG⟩ := hg N he hs hc
  exact ⟨G,hG⟩

include k in
open scoped DirectSum in
/-- Over an E-infinite algebra one integral weight forces a generic grain in
every endofinite splitting witness with a finite list of indecomposable types. -/
theorem exists_weight_forcing_generic_grain (hn : ¬ IsEFinite R) :
    ∃ γ : ProjectiveClass R, (¬ ∃ P : TwoTerm R, P.IsPresilting ∧ P.projectiveClass = γ) ∧
      ∀ (N : ModuleCat.{u} R), IsEndofinite N →
      SplitsOnCogeneratedModules k N →
      cogeneratedByModule N = (fun X ↦ ∀ {U : FGModuleCat.{u} R} (i : U ⟶ X)
        [Mono i], ¬ IsZero U → (projectiveClassWeight k γ).eval U < 0) →
      ∀ {ι J : Type u} [Fintype J] (label : ι → J), Function.Surjective label →
        ∀ (D : J → ModuleCat.{u} R), (∀ j, Indecomposable (D j)) →
        (N ≃ₗ[R] ⨁ i, D (label i)) →
        ∃ G : ModuleCat.{u} R, Nonempty (Retract G N) ∧ IsGenericGrain k G := by
  obtain ⟨γ,hγ,h⟩ := exists_weight_forcing_grain_retract k hn
  exact ⟨γ,hγ,fun N he hs hc _ _ _ _ _ _ _ _ ↦ h N he hs hc⟩

open scoped DirectSum in
/-- The free-field localization and endofinite decomposition theorems suffice
for the implication from E-infiniteness to existence of a generic grain. -/
theorem exists_generic_grain_of_free_localizations_and_decomposition
    (freeLoc : ∀ (V : Type u) [Fintype V], ∃ (K : Type u) (_ : DivisionRing K) (_ : Algebra k K)
      (g : FreeAlgebra k V →ₐ[k] K) (ι : Type u) (φ : ι → TwoTerm (FreeAlgebra k V)),
        IsUniversalLocalization φ g.toRingHom)
    (_decompose : ∀ N : ModuleCat.{u} R, IsEndofinite N →
      ∃ (ι J : Type u) (_ : Fintype J) (label : ι → J), Function.Surjective label ∧
        ∃ D : J → ModuleCat.{u} R, (∀ j, Indecomposable (D j)) ∧ Nonempty (N ≃ₗ[R] ⨁ i, D (label i)))
    (hn : ¬ IsEFinite R) : ∃ G : ModuleCat.{u} R, IsGenericGrain k G :=
  exists_generic_grain_of_free_localizations k freeLoc hn

end EFiniteCharacterizations
