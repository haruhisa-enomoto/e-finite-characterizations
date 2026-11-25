module

public import EFiniteCharacterizations.GrothendieckGroups.TorsionMonoid
public import EFiniteCharacterizations.Characterizations.HomCharacterizations
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono

/-! # Dimension-vector embeddings for torsion-class monoids -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u
namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]
local notation "μ" => GrothendieckMonoid.of
local notation "cl" => GrothendieckGroup.of

private theorem replace_kernel_class (T : ObjectProperty (FGModuleCat.{u} R)) [T.IsClosedUnderQuotients]
    [T.IsClosedUnderExtensions] (hom : EqualClassHom (FGModuleCat.{u} R)) (L : (FGModuleCat.{u} R)) (S : ShortComplex (FGModuleCat.{u} R))
    (hs : S.ShortExact) (hl : T L) (hy : T S.X₂) (hr : T S.X₃)
    (he : cl S.X₁ = cl L) : μ T S.X₂ hy = μ T L hl + μ T S.X₃ hr := by
  classical
  by_cases hz : IsZero L
  · have hk : IsZero S.X₁ := by
      by_contra hn
      exact FGModuleCat.class_ne_zero hn (he.trans (GrothendieckGroup.of_isZero hz))
    have := hs.isIso_g_iff.mpr hk
    rw [GrothendieckMonoid.of_isZero _ _ _ hz,zero_add]
    exact GrothendieckMonoid.of_iso T hy hr (asIso S.g)
  obtain ⟨f,hf⟩ := hom S.X₁ L he (he ▸ FGModuleCat.class_ne_zero hz)
  let _ := hs.mono_f
  let g := pushout.inl S.f f
  let i := pushout.inr S.f f
  let sq := IsPushout.of_hasPushout S.f f
  let V := pushout S.f f
  let S₁ := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have h₁ : S₁.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i)
    (by dsimp [S₁,i]; infer_instance) (by dsimp [S₁]; infer_instance)
  have := isIso_cokernel_map_of_isPushout sq
  let er : cokernel i ≅ S.X₃ :=
    (asIso (cokernel.map _ _ _ _ sq.w)).symm ≪≫
      (cokernelIsCokernel S.f).coconePointUniqueUpToIso hs.gIsCokernel
  have hr' : T (cokernel i) := T.prop_of_epi er.inv hr
  have hv : T V := T.prop_X₂_of_shortExact h₁ hl hr'
  let j := image.ι g
  let D := cokernel j
  let p := cokernel.π j
  let S₂ := ShortComplex.mk j p (cokernel.condition j)
  have h₂ : S₂.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel j)
    (by dsimp [S₂,j]; infer_instance) (by dsimp [S₂,p]; infer_instance)
  let e := factorThruImage g
  have hI := T.prop_of_epi e hy
  have hd := T.prop_of_epi p hv
  have hgp : g ≫ p = 0 := by
    calc
      g ≫ p = (e ≫ j) ≫ p := congrArg (· ≫ p) (image.fac g).symm
      _ = 0 := by
        simp [Category.assoc,j,p]
  let q := i ≫ p
  have hq : Epi q := ⟨fun a b hab ↦ by
    apply (cancel_epi p).mp
    apply pushout.hom_ext
    · simp only [← Category.assoc,show pushout.inl S.f f ≫ p = 0 from hgp,zero_comp]
    · exact (Category.assoc ..).symm.trans (hab.trans (Category.assoc ..))⟩
  have hfq : f ≫ q = 0 := by
    change f ≫ pushout.inr S.f f ≫ p = 0
    rw [← Category.assoc,← pushout.condition,Category.assoc,hgp,comp_zero]
  have dec : FGModuleCat.moduleLength D < FGModuleCat.moduleLength L :=
    FGModuleCat.moduleLength_lt_of_epi q (fun hiso ↦ hf ((cancel_mono q).mp (hfq.trans zero_comp.symm)))
  let S₃ := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
  have h₃ : S₃.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel e)
    (by dsimp [S₃]; infer_instance) (by dsimp [S₃,e]; infer_instance)
  have hker : cl (kernel e) = cl D := by
    have a := GrothendieckGroup.of_shortExact S hs
    have b : cl V = cl L + cl (cokernel i) := GrothendieckGroup.of_shortExact S₁ h₁
    have c : cl V = cl (image g) + cl D := GrothendieckGroup.of_shortExact S₂ h₂
    have d : cl S.X₂ = cl (kernel e) + cl (image g) := GrothendieckGroup.of_shortExact S₃ h₃
    have r := GrothendieckGroup.of_eq_of_iso er
    grind
  have ih := replace_kernel_class T hom D S₃ h₃ hd hy hI hker
  have b : μ T V hv = μ T L hl + μ T (cokernel i) hr' := GrothendieckMonoid.of_shortExact T S₁ h₁ ..
  have c : μ T V hv = μ T (image g) hI + μ T D hd := GrothendieckMonoid.of_shortExact T S₂ h₂ ..
  change μ T S.X₂ hy = μ T D hd + μ T (image g) hI at ih
  rw [ih,add_comm,← c,b,GrothendieckMonoid.of_iso T hr' hr er]
termination_by FGModuleCat.moduleLength L

/-- Equal-class Hom nonvanishing forces injectivity for every torsion class. -/
theorem torsionMonoid_injective_of_equalClassHom (hom : EqualClassHom (FGModuleCat.{u} R))
    (T : ObjectProperty (FGModuleCat.{u} R)) [T.IsClosedUnderQuotients] [T.IsClosedUnderExtensions] (h₀ : T 0) :
    Function.Injective (GrothendieckMonoid.dimensionMap T) := by
  apply (GrothendieckMonoid.dimensionMap_injective_iff T h₀).2
  intro X Y hx hy he
  let S := ShortComplex.mk (𝟙 X) (0 : X ⟶ (0 : (FGModuleCat.{u} R))) (by simp)
  have hs : S.ShortExact := ShortComplex.ShortExact.mk' ((S.exact_iff_epi (by simp [S])).2 (by dsimp [S]; infer_instance))
    (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
  have h := replace_kernel_class T hom Y S hs hy hx h₀ he
  simpa [S,GrothendieckMonoid.of_isZero T _ h₀ (isZero_zero (FGModuleCat.{u} R))] using h

namespace Weight

variable (θ : Weight (FGModuleCat.{u} R))

instance : θ.weakTorsionClass.IsClosedUnderQuotients where
  prop_of_epi p _ h _ q _ := h (p ≫ q)

instance : θ.weakTorsionClass.IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hs h₁ h₃ Q q _ := by
    let f := S.f ≫ q
    let j := image.ι f
    let p := cokernel.π j
    have hz : S.f ≫ q ≫ p = 0 := by
      change S.f ≫ q ≫ cokernel.π (image.ι f) = 0
      rw [← Category.assoc]
      exact (congrArg (· ≫ p) (image.fac f).symm).trans (by rw [Category.assoc,cokernel.condition,comp_zero])
    obtain ⟨u,hu⟩ := CokernelCofork.IsColimit.desc' hs.gIsCokernel (q ≫ p) hz
    have : Epi u := epi_of_epi_fac hu
    have a := h₁ (factorThruImage f)
    have b := h₃ u
    let D := ShortComplex.mk j p (cokernel.condition j)
    have hd : D.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel j)
      (by dsimp [D,j]; infer_instance) (by dsimp [D,p]; infer_instance)
    exact (θ.eval_shortExact D hd).ge.trans' (add_nonneg a b)

theorem weakTorsionClass_zero : θ.weakTorsionClass 0 := by
  intro Q q hq
  have h : IsZero Q := (IsZero.iff_id_eq_zero _).2 ((cancel_epi q).1 ((isZero_zero _).eq_of_src _ _))
  exact (θ.eval_isZero h).ge

end Weight

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

/-- The dimension-vector criterion restricted to weak torsion classes of integral weights. -/
theorem isEFinite_iff_injective_weakTorsionMonoid :
    IsEFinite R ↔ ∀ g : ProjectiveClass R, Function.Injective
      (GrothendieckMonoid.dimensionMap (projectiveClassWeight k g).weakTorsionClass) := by
  refine ⟨fun he g ↦ ?_, isEFinite_of_injective_weakTorsionMonoid k⟩
  exact torsionMonoid_injective_of_equalClassHom ((isEFinite_iff_equalClassHom k).1 he) _
    (projectiveClassWeight k g).weakTorsionClass_zero

include k in
/-- Injectivity of the ambient class map for every torsion class characterizes E-finiteness.
A torsion class in the finite module category contains zero and is closed under
quotients and extensions. -/
theorem isEFinite_iff_injective_torsionMonoid :
    IsEFinite R ↔ ∀ T : ObjectProperty (FGModuleCat.{u} R), T.IsClosedUnderQuotients →
      T.IsClosedUnderExtensions → T 0 → Function.Injective (GrothendieckMonoid.dimensionMap T) := by
  refine ⟨fun he _ _ _ h₀ ↦ torsionMonoid_injective_of_equalClassHom
    ((isEFinite_iff_equalClassHom k).1 he) _ h₀, fun h ↦ ?_⟩
  exact (isEFinite_iff_injective_weakTorsionMonoid k).2
    (fun g ↦ h _ inferInstance inferInstance (projectiveClassWeight k g).weakTorsionClass_zero)

end EFiniteCharacterizations
