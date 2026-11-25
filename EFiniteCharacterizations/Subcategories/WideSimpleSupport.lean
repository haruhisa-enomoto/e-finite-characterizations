module

public import EFiniteCharacterizations.GrothendieckGroups.WideGrothendieck

/-! # Wide subcategories supported on a set of simple objects -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.IsWideClass

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]
  {W : ObjectProperty (FGModuleCat.{u} R)} [hW : Fact (IsWideClass W)]

omit [IsArtinianRing R] in
theorem simple_iff_simpleMember (X : W.FullSubcategory) : Simple X ↔ IsSimpleMember W X.obj := by
  have := W.preservesMonomorphisms_ι_of_isNormalEpiCategory
  constructor
  · intro hs
    refine ⟨X.property, fun hz ↦ Simple.not_isZero X ((IsZero.iff_id_eq_zero _).2
      (W.ι.map_injective ((IsZero.iff_id_eq_zero _).1 hz))), fun {U} hu i hi hn ↦ ?_⟩
    let j := W.homMk (X := ⟨_,hu⟩) (Y := X) i
    have : Mono j := W.ι.mono_of_mono_map hi
    have hne : j ≠ 0 := by
      intro hj
      have he : i = 0 := congrArg (fun f : (⟨_,hu⟩ : W.FullSubcategory) ⟶ X ↦ f.hom) hj
      exact hn ((IsZero.iff_id_eq_zero _).2 ((cancel_mono i).1 (by simp [he])))
    have := isIso_of_mono_of_nonzero hne
    exact W.ι.map_isIso j
  · intro hs
    constructor
    intro Y f hf
    constructor
    · intro hi hz
      apply hs.2.1
      have he := congrArg (fun g : Y ⟶ X ↦ inv f ≫ g) hz
      exact (IsZero.iff_id_eq_zero _).2 (W.ι.congr_map (by simpa using he : 𝟙 X = 0))
    · intro hn
      have hne : ¬ IsZero Y.obj := fun hz ↦ hn (W.ι.map_injective (hz.eq_of_src _ _))
      exact (isIso_iff_of_reflects_iso f W.ι).mp (hs.2.2 Y.property f.hom (W.ι.map_mono f) hne)

theorem exists_intrinsic_factors (X : W.FullSubcategory) : ∃ l, HasCompositionFactors X l := by
  let P (Y : FGModuleCat.{u} R) := ∀ hy : W Y, ∃ l, HasCompositionFactors (⟨Y,hy⟩ : W.FullSubcategory) l
  apply hW.out.extension_induction P _ _ X.property X.property
  · intro Z hz hw
    exact ⟨_,.zero ((IsZero.iff_id_eq_zero _).2 (W.ι.map_injective ((IsZero.iff_id_eq_zero _).1 hz)))⟩
  · intro S hs hu hv ih hx
    obtain ⟨l,hl⟩ := ih hv
    exact ⟨_,.cons (liftExtension S hs hu.1 hx hv) ((simple_iff_simpleMember _).2 hu) hl⟩

/-- Members of a wide subcategory whose simple factors belong to the given
set of ambient isomorphism classes. -/
def supportedOn (W : ObjectProperty (FGModuleCat.{u} R)) [Fact (IsWideClass W)]
    (s : Set (Skeleton (FGModuleCat.{u} R))) : ObjectProperty (FGModuleCat.{u} R) :=
  fun X ↦ ∃ (hx : W X) (l : Multiset (Skeleton W.FullSubcategory)), HasCompositionFactors (⟨X,hx⟩ : W.FullSubcategory) l ∧
    ∀ x ∈ l, W.ι.mapSkeleton.obj x ∈ s

variable (s : Set (Skeleton (FGModuleCat.{u} R)))

theorem supportedOn_iff_of_simpleMember {X} (hx : IsSimpleMember W X) :
    supportedOn W s X ↔ toSkeleton X ∈ s := by
  let Y : W.FullSubcategory := ⟨_,hx.1⟩
  have : Simple Y := (simple_iff_simpleMember Y).2 hx
  obtain ⟨l,hl⟩ := exists_intrinsic_factors Y
  have he := hl.eq_singleton_of_simple
  constructor
  · rintro ⟨_,q,hq,hs⟩
    have hh : q = {toSkeleton Y} := (hq.unique hl).trans he
    simpa [Y,Functor.mapSkeleton_obj_toSkeleton] using hs (toSkeleton Y) (by simp [hh])
  · intro h
    exact ⟨hx.1,l,hl,by simpa [he,Y,Functor.mapSkeleton_obj_toSkeleton] using h⟩

theorem supportedOn_shortExact (T : ShortComplex (FGModuleCat.{u} R)) (ht : T.ShortExact)
    (ha : W T.X₁) (hb : W T.X₂) (hc : W T.X₃) :
    supportedOn W s T.X₂ ↔ supportedOn W s T.X₁ ∧ supportedOn W s T.X₃ := by
  obtain ⟨l,hl⟩ := exists_intrinsic_factors (⟨_,hb⟩ : W.FullSubcategory)
  obtain ⟨a,c,hia,hic,he⟩ := hl.split (liftExtension T ht ha hb hc)
  constructor
  · rintro ⟨_,q,hq,hs⟩
    rw [hq.unique hl,he] at hs
    exact ⟨⟨ha,a,hia,fun _ hi ↦ hs _ (Multiset.mem_add.mpr (Or.inl hi))⟩,
      ⟨hc,c,hic,fun _ hi ↦ hs _ (Multiset.mem_add.mpr (Or.inr hi))⟩⟩
  · rintro ⟨⟨_,a',ha',haS⟩,⟨_,c',hc',hcS⟩⟩
    refine ⟨hb,l,hl,fun x hx ↦ ?_⟩
    rw [he, hia.unique ha', hic.unique hc', Multiset.mem_add] at hx
    exact hx.elim (haS x) (hcS x)

theorem supportedOn_of_mono {X Y} (i : X ⟶ Y) [Mono i] (hx : W X) (hy : supportedOn W s Y) :
    supportedOn W s X := by
  let t := ExtensionSequence.quotient i
  exact ((supportedOn_shortExact s _ t.shortExact hx hy.choose (hW.out.cokernel_mem i hx hy.choose)).1 hy).1

theorem supportedOn_of_epi {X Y} (p : X ⟶ Y) [Epi p] (hx : supportedOn W s X) (hy : W Y) :
    supportedOn W s Y := by
  let T := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  have ht : T.ShortExact := .mk' (ShortComplex.exact_kernel p) (by dsimp [T]; infer_instance) (by dsimp [T]; infer_instance)
  exact ((supportedOn_shortExact s T ht (hW.out.kernel_mem p hx.choose hy) hx.choose hy).1 hx).2

theorem isWideClass_supportedOn : IsWideClass (supportedOn W s) where
  zero_mem X hz := ⟨hW.out.zero_mem _ hz,0,.zero ((IsZero.iff_id_eq_zero _).2
    (W.ι.map_injective ((IsZero.iff_id_eq_zero _).1 hz))),by simp⟩
  iso_mem e hx := supportedOn_of_epi s e.hom hx (hW.out.iso_mem e hx.choose)
  kernel_mem f hx hy := supportedOn_of_mono s (kernel.ι f) (hW.out.kernel_mem f hx.choose hy.choose) hx
  cokernel_mem f hx hy := supportedOn_of_epi s (cokernel.π f) hy (hW.out.cokernel_mem f hx.choose hy.choose)
  extension_mem T ht ha hc := (supportedOn_shortExact s T ht ha.choose
    (hW.out.extension_mem T ht ha.choose hc.choose) hc.choose).2 ⟨ha,hc⟩

theorem simpleMember_supportedOn_iff {X} :
    IsSimpleMember (supportedOn W s) X ↔ IsSimpleMember W X ∧ toSkeleton X ∈ s := by
  constructor
  · intro hx
    have hw : IsSimpleMember W X := ⟨hx.1.choose,hx.2.1,fun hu i hi hn ↦
      hx.2.2 (supportedOn_of_mono s i hu hx.1) i hi hn⟩
    exact ⟨hw,(supportedOn_iff_of_simpleMember s hw).1 hx.1⟩
  · rintro ⟨hw,hs⟩
    exact ⟨(supportedOn_iff_of_simpleMember s hw).2 hs,hw.2.1,fun hu i hi hn ↦ hw.2.2 hu.choose i hi hn⟩

end EFiniteCharacterizations.IsWideClass
