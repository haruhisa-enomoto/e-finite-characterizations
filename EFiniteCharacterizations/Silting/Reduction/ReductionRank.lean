module

public import EFiniteCharacterizations.Silting.Reduction.PerpendicularAlgebra
public import EFiniteCharacterizations.Characterizations.HomCharacterizations
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # E-finiteness and the rank of a reduction algebra -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

/-- A fully faithful functor preserving zero maps sends semibricks to semibricks. -/
theorem IsSemibrick.image {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesZeroMorphisms] {s : Set (Skeleton C)}
    (hs : IsSemibrick s) : IsSemibrick (F.mapSkeleton.obj '' s) := by
  let H := F ⋙ toSkeletonFunctor D ⋙ fromSkeleton D
  let : H.Full := inferInstanceAs (F ⋙ (skeletonEquivalence D).inverse ⋙ (skeletonEquivalence D).functor).Full
  let : H.Faithful := inferInstanceAs (F ⋙ (skeletonEquivalence D).inverse ⋙ (skeletonEquivalence D).functor).Faithful
  let : H.PreservesZeroMorphisms := inferInstanceAs (F ⋙ (skeletonEquivalence D).inverse ⋙ (skeletonEquivalence D).functor).PreservesZeroMorphisms
  constructor
  · rintro _ ⟨x,hx,rfl⟩
    let X := (fromSkeleton C).obj x
    change IsBrick (H.obj X)
    obtain ⟨hn,hb⟩ := hs.1 hx
    constructor
    · intro hz
      exact hn ((IsZero.iff_id_eq_zero _).2 (H.map_injective (by
        rw [H.map_id,H.map_zero]; exact (IsZero.iff_id_eq_zero _).1 hz)))
    · intro f hf
      have hp : H.preimage f ≠ 0 := fun h ↦ hf (by simpa using congrArg H.map h)
      have := hb (H.preimage f) hp
      simpa using (show IsIso (H.map (H.preimage f)) from inferInstance)
  · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hne f
    change H.obj ((fromSkeleton C).obj x) ⟶ H.obj ((fromSkeleton C).obj y) at f
    change f = (0 : H.obj ((fromSkeleton C).obj x) ⟶ H.obj ((fromSkeleton C).obj y))
    simpa using congrArg H.map (hs.2 x hx y hy (fun e ↦ hne (congrArg _ e)) (H.preimage f))

variable (k : Type u) [Field k] {R B : Type u} [Ring R] [Ring B] [Algebra k R] [Algebra k B]
  [Module.Finite k R] [Module.Finite k B]

/-- Restriction along a map of finite-dimensional algebras preserves finiteness. -/
noncomputable def finiteRestriction (f : R →ₐ[k] B) : FGModuleCat.{u} B ⥤ FGModuleCat.{u} R := by
  let F := ModuleCat.restrictScalars f.toRingHom
  have fin (M : FGModuleCat.{u} B) : Module.Finite R (F.obj M.obj) := by
    let e : F.obj M.obj ≃ₗ[k] M.obj :=
      { toEquiv := Equiv.refl _
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun c x ↦ by
          change f (algebraMap k R c) • x = algebraMap k B c • x
          rw [f.commutes] }
    have : Module.Finite B M := M.property
    have : Module.Finite k M := Module.Finite.trans B _
    have := Module.Finite.equiv e.symm
    exact Module.Finite.of_restrictScalars_finite k R _
  exact { obj := fun M ↦ ⟨F.obj M.obj,fin M⟩
          map := fun g ↦ ObjectProperty.homMk (F.map g.hom)
          map_id := fun _ ↦ rfl
          map_comp := fun _ _ ↦ rfl }

instance (f : R →ₐ[k] B) : (finiteRestriction k f).Faithful where
  map_injective {X Y} _ _ h := FGModuleCat.hom_ext (LinearMap.ext fun x ↦
    congrArg (fun g : (finiteRestriction k f).obj X ⟶ (finiteRestriction k f).obj Y ↦ g.hom.hom x) h)

instance (f : R →ₐ[k] B) : (finiteRestriction k f).PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩

variable [IsNoetherianRing R] [IsArtinianRing R] [IsNoetherianRing B] [IsArtinianRing B]

include k in
/-- E-finiteness descends along any fully faithful zero-preserving embedding
of finite module categories. -/
theorem isEFinite_of_full_embedding (F : FGModuleCat.{u} B ⥤ FGModuleCat.{u} R)
    [F.Full] [F.Faithful] [F.PreservesZeroMorphisms] (h : IsEFinite R) : IsEFinite B := by
  apply (isEFinite_iff_finite_semibricks k).2
  intro s hs
  exact ((isEFinite_iff_finite_semibricks k).1 h _ (hs.image F)).of_finite_image F.mapSkeleton_injective.injOn

omit [IsArtinianRing B] in
include k in
/-- If the image misses a simple object, the embedding strictly decreases the
number of simple classes. -/
theorem simple_count_lt_of_full_embedding (F : FGModuleCat.{u} B ⥤ FGModuleCat.{u} R)
    [F.Full] [F.Faithful] [F.PreservesZeroMorphisms] (h : IsEFinite R)
    (hmiss : ¬ simpleIsomorphismClasses R ⊆ F.mapSkeleton.obj '' simpleIsomorphismClasses B) :
    (simpleIsomorphismClasses B).ncard < (simpleIsomorphismClasses R).ncard := by
  classical
  let s := F.mapSkeleton.obj '' simpleIsomorphismClasses B
  have hs : IsSemibrick s := isSemibrick_simpleIsomorphismClasses.image F
  have hf : s.Finite := (finite_simpleIsomorphismClasses k).image _
  have hc : s.ncard = (simpleIsomorphismClasses B).ncard := Set.ncard_image_of_injective _ F.mapSkeleton_injective
  have he := equalClassHom_of_isEFinite k h
  have ht : IsSemibrick (C := FGModuleCat.{u} R) (↑hf.toFinset) := by rwa [hf.coe_toFinset]
  have hle := card_le_simple_count_of_independent_classes k
    (FamilyExtraction.independent_semibrick_of_equalClassHom he _ ht)
  have hc' : Fintype.card hf.toFinset = s.ncard := by rw [Fintype.card_coe, ← Set.ncard_coe_finset, hf.coe_toFinset]
  rw [hc',hc] at hle
  apply lt_of_le_of_ne hle
  intro hEq
  exact hmiss (FamilyExtraction.fullSize_semibrick_eq_simples_of_equalClassHom k he hs (hc.trans hEq)).ge

omit [IsNoetherianRing R] [IsArtinianRing R] [IsNoetherianRing B] [IsArtinianRing B] in
/-- A simple object whose skeleton class lies in the image is isomorphic
to the restriction of an object in the source. -/
private theorem exists_iso_of_mem_image (F : FGModuleCat.{u} B ⥤ FGModuleCat.{u} R)
    {X : FGModuleCat.{u} R} (h : toSkeleton X ∈ F.mapSkeleton.obj '' simpleIsomorphismClasses B) :
    ∃ Y, Nonempty (F.obj Y ≅ X) := by
  obtain ⟨y,_,hy⟩ := h
  let Y := (fromSkeleton _).obj y
  change toSkeleton (F.obj Y) = toSkeleton X at hy
  exact ⟨Y,⟨(fromSkeletonToSkeletonIso _).symm ≪≫ (fromSkeleton _).mapIso (eqToIso hy) ≪≫
    fromSkeletonToSkeletonIso _⟩⟩

omit [Module.Finite k R] [IsNoetherianRing R] [IsArtinianRing R] [IsNoetherianRing B] [IsArtinianRing B] in
/-- An R-linear map of restricted finite modules comes from the target
whenever it commutes with the target action. -/
theorem finiteRestriction_full (f : R →ₐ[k] B)
    (h : ∀ (M N : FGModuleCat.{u} B) (p : (finiteRestriction k f).obj M ⟶ (finiteRestriction k f).obj N)
      (b : B) (x : M), let l : M → N := p.hom.hom; l (b • x) = b • l x) : (finiteRestriction k f).Full where
  map_surjective {M N} p := by
    let q : M →ₗ[B] N :=
      { toFun := p.hom.hom
        map_add' := p.hom.hom.map_add
        map_smul' := h M N p }
    exact ⟨FGModuleCat.ofHom q, FGModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)⟩

namespace TwoTerm.PointedReflection

variable {P : TwoTerm R} (A : PointedReflection P)

include k in
/-- The finite-dimensional localization at a presilting differential of
nonzero class inherits E-finiteness and has fewer simple classes. -/
theorem reduction_invariants (h : IsEFinite R) (hp : P.IsPresilting) (hc : P.projectiveClass ≠ 0) :
    IsEFinite A.Target ∧ (simpleIsomorphismClasses A.Target).ncard < (simpleIsomorphismClasses R).ncard := by
  let := A.finite_target k
  let := IsArtinianRing.of_finite k A.Target
  let := IsNoetherianRing.of_finite k A.Target
  let f := A.algebraMapToTarget k
  let F := finiteRestriction k f
  let : F.Full := finiteRestriction_full k f fun M N p b x ↦
    A.map_smul_of_restricted_linear (M := M) (N := N) p.hom.hom b x
  let : F.Faithful := inferInstanceAs (finiteRestriction k f).Faithful
  let : F.PreservesZeroMorphisms := inferInstanceAs (finiteRestriction k f).PreservesZeroMorphisms
  refine ⟨isEFinite_of_full_embedding k F h, simple_count_lt_of_full_embedding k F h ?_⟩
  intro hall
  apply hc
  apply ProjectiveClass.eq_of_eval_eq_on_simples k
  intro X hX
  obtain ⟨Y,⟨e⟩⟩ := exists_iso_of_mem_image F (hall (show toSkeleton X ∈ simpleIsomorphismClasses R from ⟨X,rfl,hX⟩))
  have hi : P.InvertedOn (F.obj Y).obj :=
    ((P.invertedOn_restrictions_iff_regular A.ringMap).2 A.invertedOn_regular) Y
  have hz := ((P.invertedOn_iff_semistable k hp (F.obj Y)).1 hi).1
  rw [P.projectiveClassWeight_eq_eulerWeight k, map_zero]
  change (P.eulerWeight k) (GrothendieckGroup.of X) = 0
  rw [← GrothendieckGroup.of_eq_of_iso e]
  exact hz

end TwoTerm.PointedReflection

include k in
/-- A quotient excluding a simple module inherits E-finiteness and has
strictly fewer simple classes. -/
theorem quotient_reduction_invariants (h : IsEFinite R) (I : TwoSidedIdeal R)
    (hmiss : ∃ (S : Type u) (_ : AddCommGroup S) (_ : Module R S),
      IsSimpleModule R S ∧ ¬ I ≤ (Module.annihilator R S).toTwoSided) :
    IsEFinite (R ⧸ I.asIdeal) ∧
      (simpleIsomorphismClasses (R ⧸ I.asIdeal)).ncard < (simpleIsomorphismClasses R).ncard := by
  let B := R ⧸ I.asIdeal
  let := IsNoetherianRing.of_finite k (R ⧸ I.asIdeal)
  let := IsArtinianRing.of_finite k (R ⧸ I.asIdeal)
  let f : R →ₐ[k] B := Ideal.Quotient.mkₐ k I.asIdeal
  let F := finiteRestriction k f
  let : F.Full := finiteRestriction_full k f (by
    intro M N p b x
    obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective b
    exact p.hom.hom.map_smul r x)
  let : F.Faithful := inferInstanceAs (finiteRestriction k f).Faithful
  let : F.PreservesZeroMorphisms := inferInstanceAs (finiteRestriction k f).PreservesZeroMorphisms
  refine ⟨isEFinite_of_full_embedding k F h, simple_count_lt_of_full_embedding k F h ?_⟩
  obtain ⟨S,_,_,hS,hw⟩ := hmiss
  let X := FGModuleCat.of R S
  let G := forget₂ (FGModuleCat R) (ModuleCat.{u} R)
  have : Simple (G.obj X) := (simple_iff_isSimpleModule' _).2 hS
  have hx : Simple X := G.simple_of_simple_obj X
  intro hall
  obtain ⟨Y,⟨e⟩⟩ := exists_iso_of_mem_image F (hall (show toSkeleton X ∈ simpleIsomorphismClasses R from ⟨X,rfl,hx⟩))
  apply hw
  intro r hr
  apply Ideal.mem_toTwoSided.mpr
  apply Module.mem_annihilator.mpr
  intro x
  apply (FGModuleCat.isoToLinearEquiv e).symm.injective
  rw [map_smul,map_zero]
  let y : Y := (FGModuleCat.isoToLinearEquiv e).symm x
  change f r • y = (0 : Y)
  rw [show f r = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hr,zero_smul]

/-- Every noninvertible differential over an E-finite algebra gives a
smaller-rank E-finite algebra through which all inverting maps factor uniquely. -/
theorem TwoTerm.exists_smaller_reduction (h : IsEFinite R) (Q : TwoTerm R)
    (hd : ¬ IsIso Q.differential) :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B) (f : R →ₐ[k] B),
      IsEFinite B ∧ (simpleIsomorphismClasses B).ncard < (simpleIsomorphismClasses R).ncard ∧
      ∀ (T : Type u) [Ring T] (g : R →+* T),
        (letI := Module.compHom T g; Q.InvertedOn (ModuleCat.of R T)) →
          ∃! q : B →+* T, q.comp f.toRingHom = g := by
  by_cases hc : Q.projectiveClass = 0
  · obtain ⟨I,hm,hI⟩ := Q.exists_quotient_inverting_of_class_zero hc hd
    obtain ⟨hB,hr⟩ := quotient_reduction_invariants k h I hm
    exact ⟨R ⧸ I.asIdeal,inferInstance,inferInstance,inferInstance,Ideal.Quotient.mkₐ k I.asIdeal,
      hB,hr,fun T _ g hg ↦ (hI T g).1 ((Q.invertedOn_restrictions_iff_regular g).2 hg)⟩
  · obtain ⟨P,hp,hclass,hPQ⟩ := exists_presilting_invertedOn_of_isEFinite k h Q
    obtain ⟨L,e,hL,he⟩ := exists_finite_pointed_perpendicular k h P hp
    let A : PointedReflection P := ⟨L,e,hL,he⟩
    obtain ⟨hB,hr⟩ := A.reduction_invariants k h hp (hclass ▸ hc)
    refine ⟨A.Target,inferInstance,inferInstance,A.finite_target k,A.algebraMapToTarget k,hB,hr,?_⟩
    intro T _ g hg
    let := Module.compHom T g
    exact A.existsUnique_factor g (hPQ (ModuleCat.of R T) hg)

end EFiniteCharacterizations
