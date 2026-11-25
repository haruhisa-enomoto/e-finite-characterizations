module

public import EFiniteCharacterizations.Subcategories.OrthogonalApproximations
public import EFiniteCharacterizations.Stability.SemistableApproximations
public import EFiniteCharacterizations.Characterizations.HomCharacterizations

/-! # Exact abelian subcategories of finite modules -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u v

namespace EFiniteCharacterizations

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A replete full subcategory containing zero and closed under binary sums,
kernels and cokernels of maps between its objects. -/
structure IsExactAbelianClass (W : ObjectProperty C) : Prop where
  zero_mem (X : C) : IsZero X → W X
  iso_mem {X Y : C} : (X ≅ Y) → W X → W Y
  kernel_mem {X Y : C} (f : X ⟶ Y) : W X → W Y → W (kernel f)
  cokernel_mem {X Y : C} (f : X ⟶ Y) : W X → W Y → W (cokernel f)
  biprod_mem {X Y : C} : W X → W Y → W (X ⊞ Y)

/-- A replete full subcategory containing zero and closed under extensions,
kernels and cokernels of maps between its objects. -/
structure IsWideClass (W : ObjectProperty C) : Prop where
  zero_mem (X : C) : IsZero X → W X
  iso_mem {X Y : C} : (X ≅ Y) → W X → W Y
  kernel_mem {X Y : C} (f : X ⟶ Y) : W X → W Y → W (kernel f)
  cokernel_mem {X Y : C} (f : X ⟶ Y) : W X → W Y → W (cokernel f)
  extension_mem (S : ShortComplex C) : S.ShortExact → W S.X₁ → W S.X₃ → W S.X₂

theorem IsWideClass.toExactAbelianClass {W : ObjectProperty C} (h : IsWideClass W) : IsExactAbelianClass W :=
  ⟨h.zero_mem,h.iso_mem,h.kernel_mem,h.cokernel_mem,
    fun hx hy ↦ h.extension_mem _ (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact hx hy⟩

theorem Weight.isWideClass_semistable (θ : Weight C) : IsWideClass θ.IsSemistable where
  zero_mem X h := ⟨θ.eval_isZero h, fun i ↦ (θ.eval_isZero (h.of_mono i)).le⟩
  iso_mem e h := h.of_iso e
  kernel_mem f hx hy := by
    let p := Abelian.factorThruImage f
    let j := Abelian.image.ι f
    let e := (kernelCompMono p j).symm ≪≫ kernelIsoOfEq (Abelian.image.fac f)
    exact (hx.kernel_of_epi (hx.image hy f) p).of_iso e
  cokernel_mem f hx hy := by
    let p := Abelian.factorThruImage f
    let j := Abelian.image.ι f
    let e := (cokernelEpiComp p j).symm ≪≫ cokernelIsoOfEq (Abelian.image.fac f)
    exact ((hx.image hy f).cokernel_of_mono hy j).of_iso e
  extension_mem _ h := Weight.IsSemistable.of_shortExact h

namespace IsWideClass

/-- A nonzero member with no proper nonzero subobject in the wide subcategory. -/
def IsSimpleMember (W : ObjectProperty C) (X : C) : Prop :=
  W X ∧ ¬ IsZero X ∧ ∀ {U : C}, W U → ∀ i : U ⟶ X, Mono i → ¬ IsZero U → IsIso i

def simpleMemberClasses (W : ObjectProperty C) : Set (Skeleton C) :=
  {x | IsSimpleMember W ((fromSkeleton _).obj x)}

end IsWideClass

namespace IsExactAbelianClass
open IsWideClass

theorem image_mem {W : ObjectProperty C} (h : IsExactAbelianClass W) {X Y : C} (f : X ⟶ Y)
    (hx : W X) (hy : W Y) : W (Abelian.image f) :=
  h.kernel_mem (cokernel.π f) hy (h.cokernel_mem f hx hy)

theorem simpleMember_of_iso {W : ObjectProperty C} (h : IsExactAbelianClass W) {X Y : C}
    (hx : IsSimpleMember W X) (e : X ≅ Y) : IsSimpleMember W Y := by
  refine ⟨h.iso_mem e hx.1, fun hz ↦ hx.2.1 (hz.of_iso e), fun hU i hi hn ↦ ?_⟩
  have := hx.2.2 hU (i ≫ e.inv) inferInstance hn
  exact IsIso.of_isIso_comp_right i e.inv

theorem isIso_of_simpleMember_hom {W : ObjectProperty C} (h : IsExactAbelianClass W) {X Y : C}
    (hx : IsSimpleMember W X) (hy : IsSimpleMember W Y) (f : X ⟶ Y) (hf : f ≠ 0) : IsIso f := by
  let i := Abelian.image.ι f
  have hn : ¬ IsZero (Abelian.image f) := by
    intro hz
    apply hf
    rw [← Abelian.image.fac f, hz.eq_of_src (Abelian.image.ι f) 0, comp_zero]
  have := hy.2.2 (h.image_mem f hx.1 hy.1) i inferInstance hn
  have hm : Mono f := by
    apply Abelian.mono_of_kernel_ι_eq_zero
    by_contra hne
    have := hx.2.2 (h.kernel_mem f hx.1 hy.1) (kernel.ι f) inferInstance
      (fun hz ↦ hne (hz.eq_of_src _ _))
    exact hf (zero_of_epi_comp (kernel.ι f) (kernel.condition f))
  have he : Epi f := by rw [← Abelian.image.fac f]; exact epi_comp _ i
  exact isIso_of_mono_of_epi f

theorem isSemibrick_simpleMemberClasses {W : ObjectProperty C} (h : IsExactAbelianClass W) :
    IsSemibrick (simpleMemberClasses W) := by
  refine ⟨fun x (hx : IsSimpleMember W _) ↦ ⟨hx.2.1, h.isIso_of_simpleMember_hom hx hx⟩, ?_⟩
  intro x hx y hy hn f
  by_contra hf
  have := h.isIso_of_simpleMember_hom hx hy f hf
  exact hn ((toSkeleton_fromSkeleton_obj x).symm.trans
    ((congr_toSkeleton_of_iso (asIso f)).trans (toSkeleton_fromSkeleton_obj y)))

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]
  {W : ObjectProperty (FGModuleCat.{u} R)}

theorem exists_simpleMember_subobject (_h : IsExactAbelianClass W) {X} (hx : W X) (hn : ¬ IsZero X) :
    ∃ (U : FGModuleCat.{u} R) (i : U ⟶ X), Mono i ∧ IsSimpleMember W U := by
  classical
  let P (n : ℕ) := ∃ (U : FGModuleCat.{u} R) (i : U ⟶ X), Mono i ∧ W U ∧ ¬ IsZero U ∧ FGModuleCat.moduleLength U = n
  have H : ∃ n, P n := ⟨_, X, 𝟙 X, inferInstance, hx, hn, rfl⟩
  obtain ⟨U, i, hi, hu, hne, hd⟩ := Nat.find_spec H
  refine ⟨U, i, hi, hu, hne, fun {V} hv j hj hn ↦ ?_⟩
  by_contra hni
  have H' : P (FGModuleCat.moduleLength V) := ⟨V, j ≫ i, inferInstance, hv, hn, rfl⟩
  exact (Nat.not_lt_of_ge (Nat.find_min' H H')) ((FGModuleCat.moduleLength_lt_of_mono j hni).trans_eq hd)

/-- Induction on a filtration of a wide object by simple members. -/
theorem extension_induction (h : IsExactAbelianClass W) (P : ObjectProperty (FGModuleCat.{u} R))
    (hz : ∀ X, IsZero X → P X)
    (step : ∀ (S : ShortComplex (FGModuleCat.{u} R)), S.ShortExact →
      IsSimpleMember W S.X₁ → W S.X₃ → P S.X₃ → P S.X₂) {X} (hx : W X) : P X := by
  classical
  induction hn : FGModuleCat.moduleLength X using Nat.strong_induction_on generalizing X with
  | h n ih =>
    by_cases hzero : IsZero X
    · exact hz X hzero
    obtain ⟨U, i, hi, hu⟩ := h.exists_simpleMember_subobject hx hzero
    let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have hs : S.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) hi (by dsimp [S]; infer_instance)
    have hq := h.cokernel_mem i hu.1 hx
    have hl := FGModuleCat.moduleLength_shortExact S hs
    change FGModuleCat.moduleLength X = FGModuleCat.moduleLength U + FGModuleCat.moduleLength (cokernel i) at hl
    have hpos := mt (FGModuleCat.moduleLength_eq_zero_iff_isZero U).1 hu.2.1
    exact step S hs hu hq (ih (FGModuleCat.moduleLength (cokernel i)) (by omega) hq rfl)

private theorem length_le_epi {A B : FGModuleCat.{u} R} (p : A ⟶ B) [Epi p] :
    FGModuleCat.moduleLength B ≤ FGModuleCat.moduleLength A := by
  by_cases hi : IsIso p
  · exact (FGModuleCat.moduleLength_eq_of_iso (asIso p)).ge
  · exact (FGModuleCat.moduleLength_lt_of_epi p hi).le

private theorem length_le_mono {A B : FGModuleCat.{u} R} (i : A ⟶ B) [Mono i] :
    FGModuleCat.moduleLength A ≤ FGModuleCat.moduleLength B := by
  by_cases hi : IsIso i
  · exact (FGModuleCat.moduleLength_eq_of_iso (asIso i)).le
  · exact (FGModuleCat.moduleLength_lt_of_mono i hi).le

/-- A semistable module has a largest quotient in the subcategory. -/
theorem largest_quotient (h : IsExactAbelianClass W) {θ : Weight (FGModuleCat.{u} R)}
    (sub : ∀ {A B : FGModuleCat.{u} R}, W B → θ.IsSemistable A → ∀ (i : A ⟶ B) [Mono i], W A) (hsem : ∀ X, W X → θ.IsSemistable X)
    {X} (hx : θ.IsSemistable X) :
    ∃ (L : FGModuleCat.{u} R) (q : X ⟶ L), W L ∧
      ∀ Y, W Y → ∀ f : X ⟶ Y, ∃ g, q ≫ g = f := by
  classical
  let P (n : ℕ) := ∃ (L : FGModuleCat.{u} R) (q : X ⟶ L), Epi q ∧ W L ∧ FGModuleCat.moduleLength L = n
  let Z := (ProjectiveClass.zeroProjective R).val
  have hz : IsZero Z := ProjectiveClass.zeroProjective_isZero
  let z : X ⟶ Z := 0
  have : Epi z := ⟨fun f g _ ↦ hz.eq_of_src f g⟩
  have hinit : P (FGModuleCat.moduleLength Z) := ⟨Z,z,inferInstance,h.zero_mem _ hz,rfl⟩
  obtain ⟨L,q,hq,hL,hd⟩ := Nat.findGreatest_spec (length_le_epi z) hinit
  refine ⟨L,q,hL,fun Y hY f ↦ ?_⟩
  let t := biprod.lift q f
  let e := Abelian.factorThruImage t
  let j := Abelian.image.ι t
  have hw := h.biprod_mem hL hY
  have hI := sub hw (hx.image (hsem _ hw) t) j
  have hle : FGModuleCat.moduleLength (Abelian.image t) ≤ FGModuleCat.moduleLength L := hd ▸
    Nat.le_findGreatest (length_le_epi e) (show P _ from ⟨_,e,inferInstance,hI,rfl⟩)
  let r := j ≫ biprod.fst
  have hr : e ≫ r = q := by rw [show e ≫ r = (e ≫ j) ≫ biprod.fst from (Category.assoc ..).symm,
    Abelian.image.fac, biprod.lift_fst]
  have : Epi r := epi_of_epi_fac hr
  have : IsIso r := by by_contra hn; exact hle.not_gt (FGModuleCat.moduleLength_lt_of_epi r hn)
  exact ⟨inv r ≫ j ≫ biprod.snd, by rw [← hr, Category.assoc, IsIso.hom_inv_id_assoc,
    ← Category.assoc, Abelian.image.fac, biprod.lift_snd]⟩

/-- A semistable module has a largest subobject in the subcategory. -/
theorem largest_subobject (h : IsExactAbelianClass W) {θ : Weight (FGModuleCat.{u} R)}
    (quot : ∀ {A B : FGModuleCat.{u} R}, W A → θ.IsSemistable B → ∀ (p : A ⟶ B) [Epi p], W B) (hsem : ∀ X, W X → θ.IsSemistable X)
    {X} (hx : θ.IsSemistable X) :
    ∃ (L : FGModuleCat.{u} R) (i : L ⟶ X), W L ∧
      ∀ Y, W Y → ∀ f : Y ⟶ X, ∃ g, g ≫ i = f := by
  classical
  let P (n : ℕ) := ∃ (L : FGModuleCat.{u} R) (i : L ⟶ X), Mono i ∧ W L ∧ FGModuleCat.moduleLength L = n
  let Z := (ProjectiveClass.zeroProjective R).val
  have hz : IsZero Z := ProjectiveClass.zeroProjective_isZero
  let z : Z ⟶ X := 0
  have : Mono z := ⟨fun f g _ ↦ hz.eq_of_tgt f g⟩
  have hinit : P (FGModuleCat.moduleLength Z) := ⟨Z,z,inferInstance,h.zero_mem _ hz,rfl⟩
  obtain ⟨L,i,hi,hL,hd⟩ := Nat.findGreatest_spec (length_le_mono z) hinit
  refine ⟨L,i,hL,fun Y hY f ↦ ?_⟩
  let t := biprod.desc i f
  let e := Abelian.factorThruImage t
  let j := Abelian.image.ι t
  have hw := h.biprod_mem hL hY
  have hI := quot hw ((hsem _ hw).image hx t) e
  have hle : FGModuleCat.moduleLength (Abelian.image t) ≤ FGModuleCat.moduleLength L := hd ▸
    Nat.le_findGreatest (length_le_mono j) (show P _ from ⟨_,j,inferInstance,hI,rfl⟩)
  let r := biprod.inl ≫ e
  have hr : r ≫ j = i := by rw [show r ≫ j = biprod.inl ≫ e ≫ j from Category.assoc ..,
    Abelian.image.fac, biprod.inl_desc]
  have : Mono r := mono_of_mono_fac hr
  have : IsIso r := by by_contra hn; exact hle.not_gt (FGModuleCat.moduleLength_lt_of_mono r hn)
  exact ⟨(biprod.inr ≫ e) ≫ inv r, by rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc,
    Category.assoc, Abelian.image.fac, biprod.inr_desc]⟩

end IsExactAbelianClass

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

theorem exists_weight_stabilizing_exactAbelian_simples (he : IsEFinite R)
    {W : ObjectProperty (FGModuleCat.{u} R)} (h : IsExactAbelianClass W) :
    ∃ g : ProjectiveClass R, (∀ X, IsWideClass.IsSimpleMember W X → (projectiveClassWeight k g).IsStable X) ∧
      ∀ X, W X → (projectiveClassWeight k g).IsSemistable X := by
  classical
  let s := IsWideClass.simpleMemberClasses W
  have hs := h.isSemibrick_simpleMemberClasses
  have hf := (isEFinite_iff_finite_semibricks k).1 he s hs
  obtain ⟨g, hg⟩ := FamilyExtraction.exists_joint_weight_of_equalClassHom k (equalClassHom_of_isEFinite k he)
    hf.toFinset (by simpa using hs)
  have hstab X (hx : IsWideClass.IsSimpleMember W X) : (projectiveClassWeight k g).IsStable X := by
    let e := fromSkeletonToSkeletonIso X
    have hx' : toSkeleton X ∈ s := h.simpleMember_of_iso hx e.symm
    exact (hg (by simpa using hx')).of_iso e
  exact ⟨g, hstab, fun X hx ↦ h.extension_induction _ (projectiveClassWeight k g).isWideClass_semistable.zero_mem
    (fun S hs hu _ hq ↦ Weight.IsSemistable.of_shortExact hs (hstab _ hu).isSemistable hq) hx⟩

end EFiniteCharacterizations
