module

public import EFiniteCharacterizations.Subcategories.ExactAbelianClasses
public import EFiniteCharacterizations.Stability.StableSubobjects
public import EFiniteCharacterizations.Modules.AbelianCompositionFactors
public import Mathlib.CategoryTheory.Limits.FullSubcategory

/-! # Functorial finiteness of full exact abelian subcategories -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra ZeroObject

universe u v w
namespace EFiniteCharacterizations

namespace IsExactAbelianClass

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]
  {W : ObjectProperty (FGModuleCat.{u} R)} (h : IsExactAbelianClass W)
  {θ : Weight (FGModuleCat.{u} R)}
  (stable : ∀ X, IsWideClass.IsSimpleMember W X → θ.IsStable X)

include h stable

private theorem mem_of_stable_hom {X S : FGModuleCat.{u} R} (hx : W X)
    (hs : θ.IsStable S) (f : S ⟶ X) (hn : f ≠ 0) : W S := by
  apply h.extension_induction (fun Y ↦ ∀ g : S ⟶ Y, g ≠ 0 → W S) _ _ hx f hn
  · intro Y hz g hg
    exact (hg (hz.eq_of_tgt _ _)).elim
  · intro A ha h₁ _ ih g hg
    by_cases hz : g ≫ A.g = 0
    · obtain ⟨b,hb⟩ := KernelFork.IsLimit.lift' ha.fIsKernel g hz
      have hn' : b ≠ 0 := fun eq ↦ hg (by simp [← hb,eq])
      have := Weight.isIso_of_nonzero hs (stable _ h₁) b hn'
      exact h.iso_mem (asIso b).symm h₁.1
    · exact ih _ hz

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k

/-- A semistable subobject of a member lies in the exact abelian subcategory.
Removing a common stable subobject identifies the two successive quotients. -/
theorem mem_of_semistable_subobject {X U : FGModuleCat.{u} R} (hx : W X)
    (hu : θ.IsSemistable U) (i : U ⟶ X) [Mono i] : W U := by
  classical
  by_cases hz : IsZero U
  · exact h.zero_mem U hz
  obtain ⟨S,j,hj,hs⟩ := hu.exists_stable_subobject k hz
  have hn : j ≫ i ≠ 0 := fun eq ↦ hs.1 ((IsZero.iff_id_eq_zero _).2
    ((cancel_mono (j ≫ i)).1 (by simp [eq])))
  have hS := h.mem_of_stable_hom stable hx hs (j ≫ i) hn
  let top := ExtensionSequence.idLeft S
  let bottom := ExtensionSequence.quotient i
  let a := ExtensionSequence.quotient j
  let b := ExtensionSequence.quotient (j ≫ i)
  let c := ExtensionSequence.idRight (cokernel i)
  let row := ExtensionSequence.quotientRows top bottom a b c
    (by simp [top,bottom,a,b,ExtensionSequence.idLeft,ExtensionSequence.quotient])
    (by simp [top,bottom,b,c,ExtensionSequence.idLeft,ExtensionSequence.idRight,ExtensionSequence.quotient])
  have hl := FGModuleCat.moduleLength_shortExact _ a.shortExact
  change FGModuleCat.moduleLength U = FGModuleCat.moduleLength S + FGModuleCat.moduleLength (cokernel j) at hl
  have hp := mt (FGModuleCat.moduleLength_eq_zero_iff_isZero S).1 hs.1
  have dec : FGModuleCat.moduleLength (cokernel j) < FGModuleCat.moduleLength U := by omega
  have hb : W (cokernel (j ≫ i)) := h.cokernel_mem _ hS hx
  have ha : W (cokernel j) := mem_of_semistable_subobject hb (hs.isSemistable.cokernel_of_mono hu j) row.i
  have hc := h.iso_mem ((cokernelIsCokernel row.i).coconePointUniqueUpToIso row.shortExact.gIsCokernel)
    (h.cokernel_mem row.i ha hb)
  exact h.iso_mem ((kernelIsKernel bottom.p).conePointUniqueUpToIso bottom.shortExact.fIsKernel)
    (h.kernel_mem bottom.p hx hc)
termination_by FGModuleCat.moduleLength U

theorem mem_of_semistable_quotient (sem : ∀ X, W X → θ.IsSemistable X)
    {X Q : FGModuleCat.{u} R} (hx : W X) (hq : θ.IsSemistable Q) (p : X ⟶ Q) [Epi p] : W Q := by
  have hk := h.mem_of_semistable_subobject stable k hx ((sem _ hx).kernel_of_epi hq p) (kernel.ι p)
  exact h.iso_mem (asIso (Abelian.factorThruCoimage p)) (h.cokernel_mem (kernel.ι p) hk hx)

end IsExactAbelianClass

section
variable {A : Type v} [Category.{w} A] [Abelian A] {C : Type*} [Category C] [Abelian C]

/-- The essential image of a fully faithful exact functor is closed under
kernels, cokernels and finite sums. -/
theorem IsExactAbelianClass.essImage (F : A ⥤ C) [F.Full] [F.Faithful]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] : IsExactAbelianClass F.essImage := by
  constructor
  · intro X hx
    exact ⟨0,⟨(F.map_isZero (isZero_zero A)).iso hx⟩⟩
  · exact Functor.essImage.ofIso
  · intro X Y f hx hy
    apply F.essImage.prop_limit (parallelPair f 0)
    rintro (_|_) <;> assumption
  · intro X Y f hx hy
    apply F.essImage.prop_colimit (parallelPair f 0)
    rintro (_|_) <;> assumption
  · intro X Y hx hy
    apply Functor.essImage.ofIso (biprod.isoProd X Y).symm
    apply F.essImage.prop_limit (pair X Y)
    rintro ⟨__|__⟩ <;> assumption

theorem IsExactAbelianClass.inverseImage {W : ObjectProperty C} (h : IsExactAbelianClass W)
    (F : A ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    IsExactAbelianClass (fun X ↦ W (F.obj X)) where
  zero_mem X hz := h.zero_mem _ (F.map_isZero hz)
  iso_mem e hx := h.iso_mem (F.mapIso e) hx
  kernel_mem f hx hy := h.iso_mem (PreservesKernel.iso F f).symm (h.kernel_mem _ hx hy)
  cokernel_mem f hx hy := h.iso_mem (PreservesCokernel.iso F f).symm (h.cokernel_mem _ hx hy)
  biprod_mem {X Y} hx hy := by
    let := preservesBinaryBiproducts_of_preservesBinaryProducts F
    exact h.iso_mem (F.mapBiprod X Y).symm (h.biprod_mem hx hy)

end

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

include k

theorem functoriallyFinite_exactAbelianClass (he : IsEFinite R) {W : ObjectProperty (FGModuleCat.{u} R)}
    (h : IsExactAbelianClass W) : FunctoriallyFinite W := by
  obtain ⟨g,hs,hw⟩ := exists_weight_stabilizing_exactAbelian_simples k he h
  have H := (isEFinite_iff_functoriallyFinite_semistable k).1 he g
  constructor
  · intro X
    obtain ⟨V,a,hV,ha⟩ := H.1 X
    obtain ⟨L,q,hL,hq⟩ := h.largest_quotient (h.mem_of_semistable_subobject hs k) hw hV
    refine ⟨L,a ≫ q,hL,fun Y hy f ↦ ?_⟩
    obtain ⟨v,hv⟩ := ha Y (hw _ hy) f
    obtain ⟨b,hb⟩ := hq Y hy v
    exact ⟨b,by rw [Category.assoc,hb,hv]⟩
  · intro X
    obtain ⟨V,a,hV,ha⟩ := H.2 X
    obtain ⟨L,i,hL,hi⟩ := h.largest_subobject (h.mem_of_semistable_quotient hs k hw) hw hV
    refine ⟨L,i ≫ a,hL,fun Y hy f ↦ ?_⟩
    obtain ⟨v,hv⟩ := ha Y (hw _ hy) f
    obtain ⟨b,hb⟩ := hi Y hy v
    exact ⟨b,by rw [← Category.assoc,hb,hv]⟩

/-- Every full exact abelian embedding into the finite module category of an
E-finite algebra has functorially finite essential image. -/
theorem functoriallyFinite_of_full_exact_embedding (he : IsEFinite R)
    {A : Type v} [Category.{w} A] [Abelian A] (F : A ⥤ FGModuleCat.{u} R) [F.Full] [F.Faithful]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] : FunctoriallyFinite F.essImage :=
  functoriallyFinite_exactAbelianClass k he (.essImage F)

end EFiniteCharacterizations
