module

public import EFiniteCharacterizations.ScalarExtension.GroundFieldWitnesses

/-! # Simple objects in the full semistable subcategory -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace EFiniteCharacterizations

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] (θ : Weight C)

abbrev Weight.semistableCategory := ObjectProperty.FullSubcategory θ.IsSemistable

theorem Weight.isStable_iff_simple (X : θ.semistableCategory) :
    θ.IsStable X.obj ↔ Simple X := by
  let W : ObjectProperty C := θ.IsSemistable
  constructor
  · intro hs
    constructor
    intro Y f hf
    constructor
    · intro hi hz
      apply hs.1
      apply (IsZero.iff_id_eq_zero _).2
      have h := (IsIso.inv_hom_id f).symm.trans ((congrArg (inv f ≫ ·) hz).trans comp_zero)
      exact congrArg (fun a : X ⟶ X ↦ a.hom) h
    · intro hn
      have hn' : f.hom ≠ 0 := fun h ↦ hn (W.ι.map_injective h)
      have hE := Weight.epi_of_isSemistable_of_isStable Y.property hs f.hom hn'
      let K : W.FullSubcategory := ⟨kernel f.hom, Y.property.kernel_of_epi X.property f.hom⟩
      let i : K ⟶ Y := W.homMk (kernel.ι f.hom)
      have hi : i ≫ f = 0 := W.ι.map_injective (kernel.condition f.hom)
      have hz : i = 0 := (cancel_mono f).1 (hi.trans zero_comp.symm)
      have hm := Abelian.mono_of_kernel_ι_eq_zero f.hom (congrArg (fun j : K ⟶ Y ↦ j.hom) hz)
      have hi := isIso_of_mono_of_epi f.hom
      exact (isIso_iff_of_reflects_iso f W.ι).mp hi
  · intro h
    have hn : ¬ IsZero X.obj := by
      intro hz
      apply Simple.not_isZero X
      exact (IsZero.iff_id_eq_zero _).2 (W.ι.map_injective ((IsZero.iff_id_eq_zero _).1 hz))
    refine ⟨hn, X.property.1, fun {U} i hi hU hni ↦ ?_⟩
    refine lt_of_le_of_ne (X.property.2 i) ?_
    intro hz
    let Y : W.FullSubcategory := ⟨U, X.property.of_mono_of_eval_zero i hz⟩
    let j : Y ⟶ X := W.homMk i
    have : Mono j := W.ι.mono_of_mono_map hi
    have hne : j ≠ 0 := by
      intro hj
      have hiz : i = 0 := congrArg (fun a : Y ⟶ X ↦ a.hom) hj
      apply hU
      exact (IsZero.iff_id_eq_zero _).2 ((cancel_mono i).1 (by simp [hiz]))
    have := isIso_of_mono_of_nonzero hne
    exact hni (W.ι.map_isIso j)

/-- Simple isomorphism classes in the semistable category, counted internally. -/
def semistableSimpleClasses : Set (Skeleton θ.semistableCategory) :=
  {x | Simple ((fromSkeleton _).obj x)}

theorem semistableSimpleClasses_image :
    ∃ f : Skeleton θ.semistableCategory → Skeleton C, Function.Injective f ∧
      f '' semistableSimpleClasses θ = stableClasses θ := by
  let W : ObjectProperty C := θ.IsSemistable
  let f (x : Skeleton θ.semistableCategory) := toSkeleton (((fromSkeleton _).obj x).obj)
  have hf : Function.Injective f := by
    intro x y he
    obtain ⟨e⟩ := toSkeleton_eq_toSkeleton_iff.1 he
    exact (toSkeleton_fromSkeleton_obj x).symm.trans ((congr_toSkeleton_of_iso (W.isoMk e)).trans
      (toSkeleton_fromSkeleton_obj y))
  have him : f '' semistableSimpleClasses θ = stableClasses θ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hs := (θ.isStable_iff_simple _).2 hy
      exact hs.of_iso (fromSkeletonToSkeletonIso _).symm
    · intro hx
      have hs : θ.IsStable ((fromSkeleton _).obj x) := hx
      let Y : θ.semistableCategory := ⟨_, hs.isSemistable⟩
      let e := fromSkeletonToSkeletonIso Y
      have : Simple Y := (θ.isStable_iff_simple Y).1 hs
      exact ⟨toSkeleton Y, Simple.of_iso e, (congr_toSkeleton_of_iso (W.ι.mapIso e)).trans
        (toSkeleton_fromSkeleton_obj x)⟩
  exact ⟨f,hf,him⟩

theorem finite_semistableSimpleClasses_iff : (semistableSimpleClasses θ).Finite ↔ (stableClasses θ).Finite := by
  obtain ⟨f,hf,him⟩ := semistableSimpleClasses_image θ
  rw [← him]
  exact ⟨fun h ↦ h.image f, fun h ↦ h.of_finite_image hf.injOn⟩

theorem ncard_semistableSimpleClasses : (semistableSimpleClasses θ).ncard = (stableClasses θ).ncard := by
  obtain ⟨f,hf,him⟩ := semistableSimpleClasses_image θ
  rw [← him,Set.ncard_image_of_injective _ hf]

end Abelian

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

theorem isEFinite_iff_finite_semistable_simples :
    IsEFinite R ↔ ∀ g : ProjectiveClass R, (semistableSimpleClasses (C := FGModuleCat.{u} R) (projectiveClassWeight (R := R) k g)).Finite := by
  simp only [finite_semistableSimpleClasses_iff]
  exact isEFinite_iff_stableFiniteAtAllIntegralWeights_allFields k

end EFiniteCharacterizations
