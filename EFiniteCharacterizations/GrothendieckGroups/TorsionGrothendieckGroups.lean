module

public import EFiniteCharacterizations.GrothendieckGroups.TorsionFreeClassGroup
public import EFiniteCharacterizations.Subcategories.WideSubcategories
public import EFiniteCharacterizations.Presentations.ProjectiveClassSeparation

/-!
# Grothendieck groups of torsion and torsion-free classes

Proposition 4.2 (`thm:K0-tors`) of the manuscript. For any torsion class or
torsion-free class `T` in `mod R` over any field, the natural homomorphism
`K₀(T) → K₀(mod R)` from its exact Grothendieck group is injective, and its image is
the free abelian subgroup spanned by the classes of simple modules occurring as
composition factors of objects in `T` (`intrinsicGroup_on_compositionSupport`).
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u
namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]

theorem FGModuleCat.exists_compositionSeries (X : (FGModuleCat.{u} R)) : ∃ l, HasCompositionFactors X l := by
  let W : ObjectProperty (FGModuleCat.{u} R) := ⊤
  have hw : IsWideClass W := ⟨by simp [W],by simp [W],by simp [W],by simp [W],by simp [W]⟩
  apply hw.extension_induction (fun Y ↦ ∃ l, HasCompositionFactors Y l) _ _ (X := X) trivial
  · intro Y hy
    exact ⟨_,.zero hy⟩
  · rintro S hs hu _ ⟨l,hl⟩
    have sim : Simple S.X₁ := by
      constructor
      intro U i hi
      constructor
      · intro iso hz
        exact hu.2.1 ((IsZero.iff_id_eq_zero _).2 ((cancel_epi i).mp (by simp [hz])))
      · intro hn
        exact hu.2.2 trivial i hi (fun h ↦ hn (h.eq_of_src _ _))
    exact ⟨_,.cons ⟨S.f,S.g,S.zero,hs⟩ sim hl⟩

/-- The simple indices occurring in composition series of members. -/
def compositionSupport (T : ObjectProperty (FGModuleCat.{u} R)) : Set ↥(simpleIsomorphismClasses R) :=
  {i | ∃ (X : (FGModuleCat.{u} R)) (l : Multiset (Skeleton (FGModuleCat.{u} R))), T X ∧ HasCompositionFactors X l ∧ i.val ∈ l}

/-- Send a finitely supported integer vector on the support to its ambient simple-class sum. -/
noncomputable def supportCoordinates (T : ObjectProperty (FGModuleCat.{u} R)) :
    (compositionSupport T →₀ ℤ) →ₗ[ℤ] GrothendieckGroup (FGModuleCat.{u} R) :=
  Finsupp.linearCombination ℤ (fun i ↦ GrothendieckGroup.of ((fromSkeleton _).obj i.val.val))

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
omit [IsArtinianRing R] in
theorem supportCoordinates_injective (T : ObjectProperty (FGModuleCat.{u} R)) : Function.Injective (supportCoordinates T) :=
  (linearIndependent_simple_classes (R := R) k).comp _ Subtype.val_injective

omit [IsArtinianRing R] in
private theorem simple_of_compositionFactor {X : (FGModuleCat.{u} R)} {l} (h : HasCompositionFactors X l)
    {s : Skeleton (FGModuleCat.{u} R)} (hs : s ∈ l) : s ∈ simpleIsomorphismClasses R := by
  induction h with
  | zero => simp at hs
  | cons row hS hq ih =>
    rcases Multiset.mem_cons.mp hs with rfl | hm
    · exact ⟨_,rfl,hS⟩
    · exact ih hm

private theorem supportCoordinates_range (T : ObjectProperty (FGModuleCat.{u} R)) :
    (supportCoordinates T).range.toAddSubgroup = ExactClassGroup.supportSubgroup T := by
  rw [supportCoordinates,Finsupp.range_linearCombination,Submodule.span_int_eq_addSubgroupClosure,
    ExactClassGroup.supportSubgroup]
  congr 1
  ext z
  constructor
  · rintro ⟨i,rfl⟩
    obtain ⟨X,l,hx,h,hmem⟩ := i.property
    exact ⟨_,X,l,hx,h,by rwa [toSkeleton_fromSkeleton_obj],rfl⟩
  · rintro ⟨S,X,l,hx,h,hs,rfl⟩
    let j : ↥(simpleIsomorphismClasses R) := ⟨_,simple_of_compositionFactor h hs⟩
    exact ⟨⟨j,X,l,hx,h,hs⟩,GrothendieckGroup.of_eq_of_iso (fromSkeletonToSkeletonIso S)⟩

include k in
/-- The inclusion and the coordinate sum give two injective presentations of
the same subgroup, for a torsion class or a torsion-free class. -/
theorem intrinsicGroup_on_compositionSupport (T : ObjectProperty (FGModuleCat.{u} R)) [T.IsClosedUnderExtensions] (h₀ : T 0)
    (h : T.IsClosedUnderQuotients ∨ T.IsClosedUnderSubobjects) :
    Function.Injective (ExactClassGroup.inclusion T) ∧ Function.Injective (supportCoordinates T) ∧
      (ExactClassGroup.inclusion T).range = (supportCoordinates T).range.toAddSubgroup := by
  have result : Function.Injective (ExactClassGroup.inclusion T) ∧
      (ExactClassGroup.inclusion T).range = ExactClassGroup.supportSubgroup T := by
    rcases h with h | h
    · exact ExactClassGroup.torsion_identifies_support T h₀ FGModuleCat.exists_compositionSeries
    · exact ExactClassGroup.torsionFree_identifies_support T h₀ FGModuleCat.exists_compositionSeries
  exact ⟨result.1,supportCoordinates_injective k T,result.2.trans (supportCoordinates_range T).symm⟩

end EFiniteCharacterizations
