module

public import EFiniteCharacterizations.Modules.AbelianCompositionFactors
public import EFiniteCharacterizations.Subcategories.WideSubcategories
public import Mathlib.CategoryTheory.Abelian.Subcategory

/-! # The Grothendieck group of a wide subcategory -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

namespace EFiniteCharacterizations.IsWideClass

variable {C : Type u} [Category.{v} C] [Abelian C] {W : ObjectProperty C}

scoped instance [h : Fact (IsWideClass W)] : W.ContainsZero :=
  ⟨⟨0, isZero_zero C, h.out.zero_mem _ (isZero_zero C)⟩⟩

scoped instance [h : Fact (IsWideClass W)] : W.IsClosedUnderIsomorphisms :=
  ⟨h.out.iso_mem⟩

scoped instance [h : Fact (IsWideClass W)] : W.IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, _, hk, hx, hy⟩
    exact h.out.iso_mem ((kernelIsKernel f).conePointUniqueUpToIso hk) (h.out.kernel_mem f hx hy)

scoped instance [h : Fact (IsWideClass W)] : W.IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, _, hk, hx, hy⟩
    exact h.out.iso_mem ((cokernelIsCokernel f).coconePointUniqueUpToIso hk) (h.out.cokernel_mem f hx hy)

scoped instance [h : Fact (IsWideClass W)] : W.IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    let A := p.diag.obj (.mk .left)
    let B := p.diag.obj (.mk .right)
    have hw : W (A ⊞ B) := h.out.extension_mem _ (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact
      (p.prop_diag_obj _) (p.prop_diag_obj _)
    exact h.out.iso_mem ((biprod.isoProd A B) ≪≫ IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)) hw

scoped instance [Fact (IsWideClass W)] : W.IsClosedUnderFiniteProducts := .mk'

scoped instance preservesLimitsOfWide [Fact (IsWideClass W)] : PreservesFiniteLimits W.ι := by
  have := W.preservesKernels_ι
  exact Functor.preservesFiniteLimits_of_preservesKernels W.ι

scoped instance preservesColimitsOfWide [Fact (IsWideClass W)] : PreservesFiniteColimits W.ι := by
  have := W.preservesCokernels_ι
  exact Functor.preservesFiniteColimits_of_preservesCokernels W.ι

/-- The morphism on intrinsic Grothendieck groups induced by inclusion. -/
noncomputable def inclusionK₀ (h : IsWideClass W) :
    GrothendieckGroup W.FullSubcategory →+ GrothendieckGroup C := by
  let _ : Fact (IsWideClass W) := ⟨h⟩
  exact GrothendieckGroup.map W.ι (fun _ hs ↦ hs.map_of_exact _)

@[simp] theorem inclusionK₀_of (h : IsWideClass W) (X : W.FullSubcategory) :
    h.inclusionK₀ (GrothendieckGroup.of X) = GrothendieckGroup.of X.obj :=
  by simp [inclusionK₀, GrothendieckGroup.map]

/-- A short exact sequence between members lifts to the full wide subcategory. -/
def liftExtension [Fact (IsWideClass W)] (S : ShortComplex C) (hs : S.ShortExact)
    (h₁ : W S.X₁) (h₂ : W S.X₂) (h₃ : W S.X₃) :
    ExtensionSequence (⟨S.X₁,h₁⟩ : W.FullSubcategory) ⟨S.X₂,h₂⟩ ⟨S.X₃,h₃⟩ := by
  let T := ShortComplex.mk (W.homMk (X := ⟨_,h₁⟩) (Y := ⟨_,h₂⟩) S.f) (W.homMk (Y := ⟨_,h₃⟩) S.g)
    (W.ι.map_injective S.zero)
  have hm : (T.map W.ι).ShortExact := hs
  exact ⟨T.f,T.g,T.zero,ShortComplex.ShortExact.mk' ((T.exact_map_iff_of_faithful W.ι).1 hm.exact)
    (W.ι.mono_of_mono_map hs.mono_f) (W.ι.epi_of_epi_map hs.epi_g)⟩

private theorem intrinsic_class_shortExact (h : IsWideClass W) (S : ShortComplex C) (hs : S.ShortExact)
    (h₁ : W S.X₁) (h₂ : W S.X₂) (h₃ : W S.X₃) :
    GrothendieckGroup.of (⟨S.X₂,h₂⟩ : W.FullSubcategory) =
    GrothendieckGroup.of (⟨S.X₁,h₁⟩ : W.FullSubcategory) + GrothendieckGroup.of (⟨S.X₃,h₃⟩ : W.FullSubcategory) := by
  let _ : Fact (IsWideClass W) := ⟨h⟩
  let t := liftExtension (W := W) S hs h₁ h₂ h₃
  exact GrothendieckGroup.of_shortExact (ShortComplex.mk t.i t.p t.w) t.shortExact

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]

private theorem span_intrinsic_simples {W : ObjectProperty (FGModuleCat.{u} R)} (h : IsWideClass W)
    (s : Finset (Skeleton (FGModuleCat.{u} R))) (hs : (s : Set _) = simpleMemberClasses W)
    (B : s → W.FullSubcategory) (hB : ∀ i, (B i).obj = (fromSkeleton _).obj i.val) :
    Function.Surjective (Finsupp.linearCombination ℤ (fun i ↦ GrothendieckGroup.of (B i))) := by
  classical
  let _ : Fact (IsWideClass W) := ⟨h⟩
  let L := Finsupp.linearCombination ℤ (fun i ↦ GrothendieckGroup.of (B i))
  let P (X : FGModuleCat.{u} R) := ∀ hx : W X, GrothendieckGroup.of (⟨X,hx⟩ : W.FullSubcategory) ∈ L.range
  have hgen (X : W.FullSubcategory) : GrothendieckGroup.of X ∈ L.range := by
    apply h.extension_induction P _ _ X.property X.property
    · intro Z hz hw
      have hzero : IsZero (⟨Z,hw⟩ : W.FullSubcategory) :=
        (IsZero.iff_id_eq_zero _).2 (W.ι.map_injective ((IsZero.iff_id_eq_zero _).1 hz))
      rw [GrothendieckGroup.of_isZero hzero]
      exact L.range.zero_mem
    · intro S hS hu hv ih hw
      let e := fromSkeletonToSkeletonIso S.X₁
      have ht : toSkeleton S.X₁ ∈ simpleMemberClasses W := hu.of_iso h e.symm
      let t : s := ⟨_,(hs ▸ ht : toSkeleton S.X₁ ∈ (s : Set _))⟩
      have e' : (B t).obj ≅ S.X₁ := eqToIso (hB t) ≪≫ e
      have he := GrothendieckGroup.of_eq_of_iso (W.isoMk (Y := ⟨_,hu.1⟩) e')
      rw [h.intrinsic_class_shortExact S hS hu.1 hw hv, ← he]
      exact L.range.add_mem ⟨Finsupp.single t 1, by simp [L]⟩ (ih hv)
  intro z
  obtain ⟨a,rfl⟩ := QuotientAddGroup.mk'_surjective (exactRelations W.FullSubcategory) z
  change (QuotientAddGroup.mk' (exactRelations W.FullSubcategory)) a ∈ L.range
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp
  | of X => exact hgen X
  | neg X ih => simpa using L.range.neg_mem ih
  | add a b ha hb => simpa using L.range.add_mem ha hb

theorem inclusionK₀_injective_of_isEFinite (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]
    (he : IsEFinite R) {W : ObjectProperty (FGModuleCat.{u} R)} (h : IsWideClass W) :
    Function.Injective h.inclusionK₀ := by
  classical
  have hf := (isEFinite_iff_finite_semibricks k).1 he _ h.isSemibrick_simpleMemberClasses
  let s := hf.toFinset
  have hs : (s : Set _) = simpleMemberClasses W := hf.coe_toFinset
  let B (i : s) : W.FullSubcategory := ⟨(fromSkeleton _).obj i.val,
    (show IsSimpleMember W _ from (hs ▸ i.property : i.val ∈ simpleMemberClasses W)).1⟩
  let v (i : s) := GrothendieckGroup.of (B i)
  have hin := FamilyExtraction.independent_semibrick_of_equalClassHom (equalClassHom_of_isEFinite k he)
    s (hs ▸ h.isSemibrick_simpleMemberClasses)
  have hsurr := h.span_intrinsic_simples s hs B (fun _ ↦ rfl)
  intro x y hxy
  obtain ⟨a,rfl⟩ := hsurr x
  obtain ⟨b,rfl⟩ := hsurr y
  have hh (c : s →₀ ℤ) : h.inclusionK₀ (Finsupp.linearCombination ℤ v c) =
      Finsupp.linearCombination ℤ (fun i : s ↦ GrothendieckGroup.of ((fromSkeleton _).obj i.val)) c := by
    simp [Finsupp.linearCombination_apply, Finsupp.sum, v, B]
  change h.inclusionK₀ (Finsupp.linearCombination ℤ v a) = h.inclusionK₀ (Finsupp.linearCombination ℤ v b) at hxy
  rw [hh, hh] at hxy
  exact congrArg _ (hin hxy)

end EFiniteCharacterizations.IsWideClass
