module

public import EFiniteCharacterizations.Subcategories.ExactAbelianApproximations

/-!
# Functorial finiteness of wide subcategories

Theorem 5.1 (`thm:wide`, condition `(wide)` in Theorem A(I)): studies simple objects of
wide subcategories and establishes `isEFinite_iff_functoriallyFinite_wideClasses`,
showing over an arbitrary field that `R` is E-finite if and only if every wide
subcategory of `mod R` is functorially finite.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u v

namespace EFiniteCharacterizations

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace IsWideClass

theorem image_mem {W : ObjectProperty C} (h : IsWideClass W) {X Y : C} (f : X ⟶ Y)
    (hx : W X) (hy : W Y) : W (Abelian.image f) :=
  h.toExactAbelianClass.image_mem f hx hy

theorem IsSimpleMember.of_iso {W : ObjectProperty C} (h : IsWideClass W) {X Y : C}
    (hx : IsSimpleMember W X) (e : X ≅ Y) : IsSimpleMember W Y :=
  h.toExactAbelianClass.simpleMember_of_iso hx e

theorem isIso_of_simpleMember_hom {W : ObjectProperty C} (h : IsWideClass W) {X Y : C}
    (hx : IsSimpleMember W X) (hy : IsSimpleMember W Y) (f : X ⟶ Y) (hf : f ≠ 0) : IsIso f :=
  h.toExactAbelianClass.isIso_of_simpleMember_hom hx hy f hf

theorem isSemibrick_simpleMemberClasses {W : ObjectProperty C} (h : IsWideClass W) :
    IsSemibrick (simpleMemberClasses W) :=
  h.toExactAbelianClass.isSemibrick_simpleMemberClasses

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]
  {W : ObjectProperty (FGModuleCat.{u} R)}

theorem exists_simpleMember_subobject (h : IsWideClass W) {X} (hx : W X) (hn : ¬ IsZero X) :
    ∃ (U : FGModuleCat.{u} R) (i : U ⟶ X), Mono i ∧ IsSimpleMember W U :=
  h.toExactAbelianClass.exists_simpleMember_subobject hx hn

/-- Induction on a filtration of a wide object by simple members. -/
theorem extension_induction (h : IsWideClass W) (P : ObjectProperty (FGModuleCat.{u} R))
    (hz : ∀ X, IsZero X → P X)
    (step : ∀ (S : ShortComplex (FGModuleCat.{u} R)), S.ShortExact →
      IsSimpleMember W S.X₁ → W S.X₃ → P S.X₃ → P S.X₂) {X} (hx : W X) : P X :=
  h.toExactAbelianClass.extension_induction P hz step hx

/-- If the simple members are stable at one weight, a semistable subobject
of a wide object also belongs to the wide subcategory. -/
theorem mem_of_semistable_subobject (h : IsWideClass W) {θ : Weight (FGModuleCat.{u} R)}
    (hstable : ∀ X, IsSimpleMember W X → θ.IsStable X) (hsem : ∀ X, W X → θ.IsSemistable X)
    {X U} (hx : W X) (hu : θ.IsSemistable U) (i : U ⟶ X) [Mono i] : W U := by
  let P (Y : FGModuleCat.{u} R) := ∀ (V : FGModuleCat.{u} R), θ.IsSemistable V →
    ∀ j : V ⟶ Y, Mono j → W V
  suffices P X from this _ hu i inferInstance
  apply h.extension_induction P _ _ hx
  · intro Y hz V _ j hj
    exact h.zero_mem V (hz.of_mono j)
  · intro S hs h₁ h₃ ih V hv j hj
    let f := j ≫ S.g
    let p := Abelian.factorThruImage f
    let m := Abelian.image.ι f
    have he : p ≫ m = f := Abelian.image.fac f
    have hI := hv.image (hsem _ h₃) f
    have hIW := ih _ hI m inferInstance
    let a := kernel.ι p
    have hzero : (a ≫ j) ≫ S.g = 0 := by
      rw [Category.assoc]
      change a ≫ f = 0
      exact (congrArg (a ≫ ·) he.symm).trans (by rw [← Category.assoc, kernel.condition, zero_comp])
    obtain ⟨b,hb⟩ := KernelFork.IsLimit.lift' hs.fIsKernel (a ≫ j) hzero
    have hm : Mono b := mono_of_mono_fac hb
    have hK : W (kernel p) := by
      by_cases hz : b = 0
      · exact h.zero_mem _ ((IsZero.iff_id_eq_zero _).2 ((cancel_mono b).mp (by simp [hz])))
      have := Weight.epi_of_isSemistable_of_isStable (hv.kernel_of_epi hI p) (hstable _ h₁) b hz
      have := isIso_of_mono_of_epi b
      exact h.iso_mem (asIso b).symm h₁.1
    let E := ShortComplex.mk a p (kernel.condition p)
    exact h.extension_mem E (ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p)
      (by dsimp [E,a]; infer_instance) (by dsimp [E,p]; infer_instance)) hK hIW

theorem mem_of_semistable_quotient (h : IsWideClass W) {θ : Weight (FGModuleCat.{u} R)}
    (hstable : ∀ X, IsSimpleMember W X → θ.IsStable X) (hsem : ∀ X, W X → θ.IsSemistable X)
    {X Q} (hx : W X) (hq : θ.IsSemistable Q) (p : X ⟶ Q) [Epi p] : W Q := by
  have hk := h.mem_of_semistable_subobject hstable hsem hx ((hsem _ hx).kernel_of_epi hq p) (kernel.ι p)
  exact h.iso_mem (asIso (Abelian.factorThruCoimage p)) (h.cokernel_mem (kernel.ι p) hk hx)

/-- A semistable module has a largest quotient in the wide subcategory. -/
theorem exists_wide_quotient (h : IsWideClass W) {θ : Weight (FGModuleCat.{u} R)}
    (hstable : ∀ X, IsSimpleMember W X → θ.IsStable X) (hsem : ∀ X, W X → θ.IsSemistable X)
    {X} (hx : θ.IsSemistable X) :
    ∃ (L : FGModuleCat.{u} R) (q : X ⟶ L), W L ∧
      ∀ Y, W Y → ∀ f : X ⟶ Y, ∃ g, q ≫ g = f :=
  h.toExactAbelianClass.largest_quotient (h.mem_of_semistable_subobject hstable hsem) hsem hx

/-- A semistable module has a largest subobject in the wide subcategory. -/
theorem exists_wide_subobject (h : IsWideClass W) {θ : Weight (FGModuleCat.{u} R)}
    (hstable : ∀ X, IsSimpleMember W X → θ.IsStable X) (hsem : ∀ X, W X → θ.IsSemistable X)
    {X} (hx : θ.IsSemistable X) :
    ∃ (L : FGModuleCat.{u} R) (i : L ⟶ X), W L ∧
      ∀ Y, W Y → ∀ f : Y ⟶ X, ∃ g, g ≫ i = f :=
  h.toExactAbelianClass.largest_subobject (h.mem_of_semistable_quotient hstable hsem) hsem hx

end IsWideClass

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

theorem exists_weight_stabilizing_wide_simples (he : IsEFinite R)
    {W : ObjectProperty (FGModuleCat.{u} R)} (h : IsWideClass W) :
    ∃ g : ProjectiveClass R, (∀ X, IsWideClass.IsSimpleMember W X → (projectiveClassWeight k g).IsStable X) ∧
      ∀ X, W X → (projectiveClassWeight k g).IsSemistable X :=
  exists_weight_stabilizing_exactAbelian_simples k he h.toExactAbelianClass

include k in
theorem isEFinite_of_functoriallyFinite_wideClasses
    (h : ∀ W : ObjectProperty (FGModuleCat.{u} R), IsWideClass W → FunctoriallyFinite W) : IsEFinite R :=
  (isEFinite_iff_functoriallyFinite_semistable k).2 (fun g ↦ h _ (projectiveClassWeight k g).isWideClass_semistable)

include k in
theorem isEFinite_iff_functoriallyFinite_wideClasses :
    IsEFinite R ↔ ∀ W : ObjectProperty (FGModuleCat.{u} R), IsWideClass W → FunctoriallyFinite W :=
  ⟨fun he _ h ↦ functoriallyFinite_exactAbelianClass k he h.toExactAbelianClass,
    isEFinite_of_functoriallyFinite_wideClasses k⟩

include k in
theorem isEFinite_iff_covariantlyFinite_wideClasses :
    IsEFinite R ↔ ∀ W : ObjectProperty (FGModuleCat.{u} R), IsWideClass W → CovariantlyFinite W := by
  refine ⟨fun he W h ↦ ((isEFinite_iff_functoriallyFinite_wideClasses k).1 he W h).1, fun h ↦ ?_⟩
  apply (isEFinite_iff_stableFiniteAtAllIntegralWeights_allFields k).2
  intro g
  let θ := projectiveClassWeight (R := R) k g
  obtain ⟨L,a,hL,ha⟩ := h _ θ.isWideClass_semistable (FGModuleCat.of R R)
  exact finite_stableClasses_of_regular_approximation k hL a (fun S hs ↦ ha S hs.isSemistable)

include k in
theorem isEFinite_iff_contravariantlyFinite_wideClasses :
    IsEFinite R ↔ ∀ W : ObjectProperty (FGModuleCat.{u} R), IsWideClass W → ContravariantlyFinite W := by
  refine ⟨fun he W h ↦ ((isEFinite_iff_functoriallyFinite_wideClasses k).1 he W h).2, fun h ↦ ?_⟩
  apply (isEFinite_iff_stableFiniteAtAllIntegralWeights_allFields k).2
  intro g
  let θ := projectiveClassWeight (R := R) k g
  let P := FGModuleCat.of R R
  let _ : Module.Projective R P := inferInstanceAs (Module.Projective R R)
  obtain ⟨L,a,hL,ha⟩ := h _ θ.isWideClass_semistable (nakayamaObject k P)
  apply (Weight.finite_stable_sources k L hL.2).subset
  intro x hx
  let S := (fromSkeleton _).obj x
  have hs : θ.IsStable S := hx
  have hdim := dimensionWeight_pos k S hs.1
  rw [dimensionWeight, projectiveHomWeight_eval, Int.natCast_pos, homFinrank_eq_finrank] at hdim
  have := finiteModuleHom_isFinite k P S
  have he : Module.finrank k (S ⟶ nakayamaObject k P) = Module.finrank k (P ⟶ S) :=
    (nakayamaPairing k P S).finrank_eq.symm.trans (Subspace.dual_finrank_eq ..)
  obtain ⟨f,hf⟩ := (homFinrank_pos_iff k S _).1 (by rw [homFinrank_eq_finrank, he]; exact hdim)
  obtain ⟨b,hb⟩ := ha S hs.isSemistable f
  exact ⟨hx,b,fun hz ↦ hf (by rw [← hb,hz,zero_comp])⟩

end EFiniteCharacterizations
