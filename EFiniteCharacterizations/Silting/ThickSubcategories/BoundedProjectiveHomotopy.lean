module

public import EFiniteCharacterizations.Silting.ThickSubcategories.ThickGenerationCriterion
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# Presilting generation of thick subcategories inside `Kᵇ(proj R)`

Proposition 7.5 (`prop:thick-generation`) and the `(thick-gen)` characterization in
Theorem A(I) / Theorem 7.8:

* `bounded_thick_iff`: compares thick closure inside `Kᵇ(proj R)` with the ambient
  homotopy envelope on two-term complexes.
* `exists_maximum_basic_thick_generator` (**Proposition 7.5**): over an E-finite
  algebra, any basic presilting object `U ∈ H` with the maximum number of
  indecomposable summands satisfies `H = thick(U) ∩ K^{[-1,0]}(proj R)`.
* `isEFinite_iff_boundedProjectiveThickGeneration`: full equivalence `(E-fin) ⇔ (thick-gen)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex

universe u
namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R] [IsNoetherianRing R]


/-- A representative bounded in both directions with projective terms in every degree. -/
structure BoundedProjectiveTerms (L : CochainComplex (FGModuleCat.{u} R) ℤ) : Prop where
  bounded : ∃ l m : ℤ, ∀ j, j < l ∨ m < j → IsZero (L.X j)
  projective : ∀ j, Module.Projective R (L.X j)

/-- The full subcategory on bounded complexes of finite projectives, with morphisms
taken modulo chain homotopy. -/
def boundedProjective (R : Type u) [Ring R] [IsNoetherianRing R] : ObjectProperty (HomotopyCategory (FGModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  fun X ↦ BoundedProjectiveTerms X.as

omit [IsNoetherianRing R] in
private theorem projective_iso {X Y : FGModuleCat.{u} R} (e : X ≅ Y)
    (h : Module.Projective R Y) : Module.Projective R X :=
  Module.Projective.of_split e.hom.hom.hom e.inv.hom.hom (congrArg (fun f : X ⟶ X ↦ f.hom.hom) e.hom_inv_id)

omit [IsNoetherianRing R] in
private theorem projective_zero {X : FGModuleCat.{u} R} (h : IsZero X) : Module.Projective R X :=
  projective_iso (h.iso ProjectiveClass.zeroProjective_isZero) (ProjectiveClass.zeroProjective R).property

theorem boundedProjective_homotopyObject (P : TwoTerm R) : boundedProjective R P.homotopyObject := by
  refine ⟨⟨-1,0,fun j hj ↦ isZero_double_X _ adjacent j (by omega) (by omega)⟩,?_⟩
  intro j
  by_cases h₁ : j = -1
  · subst j
    exact projective_iso (doubleXIso₀ _ adjacent) P.projective_source
  by_cases h₀ : j = 0
  · subst j
    exact projective_iso (doubleXIso₁ _ adjacent (by decide)) P.projective_target
  exact projective_zero (isZero_double_X _ adjacent j h₁ h₀)

instance : (boundedProjective R).ContainsZero where
  exists_zero := ⟨_,isZero_contractible (ProjectiveClass.zeroProjective R), boundedProjective_homotopyObject _⟩

instance : (boundedProjective R).IsStableUnderShift ℤ where
  isStableUnderShiftBy t := ⟨by
    intro X hX
    obtain ⟨L,rfl⟩ := X.quotient_obj_surjective
    change BoundedProjectiveTerms L at hX
    obtain ⟨l,m,hb⟩ := hX.bounded
    rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj]
    change BoundedProjectiveTerms (L⟦t⟧)
    exact ⟨⟨l-t,m-t,fun j hj ↦ IsZero.of_iso (hb (j+t) (by omega)) (CochainComplex.shiftFunctorObjXIso L t j (j+t) rfl)⟩,
      fun j ↦ projective_iso (CochainComplex.shiftFunctorObjXIso L t j (j+t) rfl) (hX.projective _)⟩⟩

set_option backward.isDefEq.respectTransparency false in
instance : (boundedProjective R).IsTriangulatedClosed₃ where
  ext₃' T ht h₁ h₂ := by
    change BoundedProjectiveTerms T.obj₁.as at h₁
    change BoundedProjectiveTerms T.obj₂.as at h₂
    obtain ⟨l,m,hm⟩ := h₁.bounded
    obtain ⟨s,t,ht'⟩ := h₂.bounded
    obtain ⟨f,hf⟩ := (HomotopyCategory.quotient _ _).map_surjective T.mor₁
    let L := CochainComplex.mappingCone f
    refine ⟨(HomotopyCategory.quotient _ _).obj L,?_,
      ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ ht (HomotopyCategory.mappingCone_triangleh_distinguished f)
        (Iso.refl _) (Iso.refl _) (by simp [hf]))⟩⟩
    change BoundedProjectiveTerms L
    refine ⟨⟨min (l-1) s,max m t,fun j hj ↦ (CochainComplex.mappingCone.isZero_X_iff f j).2
      ⟨hm _ (by omega),ht' _ (by omega)⟩⟩,?_⟩
    intro j
    have := h₁.projective (j+1)
    have := h₂.projective j
    exact projective_iso (homotopyCofiber.XIsoBiprod f j (j+1) rfl) (FGModuleCat.projective_biprod _ _)

instance : (boundedProjective R).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- A two-term complex as an object of the bounded homotopy category of projectives. -/
noncomputable abbrev inBoundedProjectives (P : TwoTerm R) : (boundedProjective R).FullSubcategory :=
  ⟨P.homotopyObject, boundedProjective_homotopyObject P⟩

/-- Membership in a presilting generator's thick closure can be computed either
in the bounded homotopy category of finite projectives or in finite modules.
In fact the comparison holds for every two-term generator. -/
theorem bounded_thick_iff (U X : TwoTerm R) :
    (ObjectProperty.singleton U.inBoundedProjectives).triangEnvelope X.inBoundedProjectives ↔ InThick U X := by
  let F := (boundedProjective R).ι
  let A := (ObjectProperty.singleton U.inBoundedProjectives).triangEnvelope
  let B := (ObjectProperty.singleton U.homotopyObject).triangEnvelope
  have hA : A U.inBoundedProjectives := (ObjectProperty.singleton _).le_triangEnvelope _ (.mk ())
  constructor
  · intro h
    have : (B.inverseImage F).IsStableUnderRetracts := ⟨fun r hY ↦ B.prop_of_retract (r.map F) hY⟩
    have hU : (B.inverseImage F) U.inBoundedProjectives := inThick_self U
    exact ((ObjectProperty.triangEnvelope_le_iff (ObjectProperty.singleton U.inBoundedProjectives) (Q := B.inverseImage F)).2
      (ObjectProperty.singleton_le_iff.2 hU)) X.inBoundedProjectives h
  · intro h
    let I := A.map F
    have : I.retractClosure.IsTriangulatedClosed₂ := Presilting.extension_closed_retractClosure I
    have : I.retractClosure.IsTriangulated := {}
    have hU : I.retractClosure U.homotopyObject := ObjectProperty.le_retractClosure I _ (A.prop_map_obj F hA)
    obtain ⟨Y,⟨L,hL,⟨j⟩⟩,⟨r⟩⟩ := ((ObjectProperty.triangEnvelope_le_iff _ (Q := I.retractClosure)).2
      (ObjectProperty.singleton_le_iff.2 hU)) _ h
    let t : Retract (F.obj X.inBoundedProjectives) (F.obj L) := r.trans j.symm.retract
    apply A.prop_of_retract (Y := L) _ hL
    exact ⟨F.preimage t.i, F.preimage t.r, F.map_injective (by simp [t.retract])⟩

/-- Summand closure and two-out-of-three stated entirely inside the bounded
homotopy category of finite projectives. -/
structure IsBoundedTwoTermThick (H : TwoTerm R → Prop) : Prop where
  zero : H (contractible (ProjectiveClass.zeroProjective R))
  triangles : ∀ (A B C : TwoTerm R) (f : A.inBoundedProjectives ⟶ B.inBoundedProjectives)
    (g : B.inBoundedProjectives ⟶ C.inBoundedProjectives) (h : C.inBoundedProjectives ⟶ A.inBoundedProjectives⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang _ → (H A → (H B ↔ H C)) ∧ (H C → (H B ↔ H A))
  retracts : ∀ (P Q : TwoTerm R), Retract P.inBoundedProjectives Q.inBoundedProjectives → H Q → H P

theorem isBoundedTwoTermThick_iff (H : TwoTerm R → Prop) : IsBoundedTwoTermThick H ↔ IsTwoTermThick H := by
  let F := (boundedProjective R).ι
  constructor
  · intro h
    refine ⟨h.zero, ?_, fun P Q r ↦ h.retracts P Q ?_⟩
    · intro A B C f g d ht
      let f' : A.inBoundedProjectives ⟶ B.inBoundedProjectives := F.preimage f
      let g' : B.inBoundedProjectives ⟶ C.inBoundedProjectives := F.preimage g
      let d' : C.inBoundedProjectives ⟶ A.inBoundedProjectives⟦(1 : ℤ)⟧ :=
        F.preimage (d ≫ (F.commShiftIso (1 : ℤ)).inv.app A.inBoundedProjectives)
      apply h.triangles A B C f' g' d'
      change F.mapTriangle.obj (Triangle.mk f' g' d') ∈ distTriang _
      change Triangle.mk (F.map f') (F.map g') (F.map d' ≫ (F.commShiftIso (1 : ℤ)).hom.app _) ∈ distTriang _
      have hd : F.map d' ≫ (F.commShiftIso (1 : ℤ)).hom.app A.inBoundedProjectives = d := by
        rw [show F.map d' = _ from F.map_preimage _, Category.assoc, Iso.inv_hom_id_app]
        exact Category.comp_id _
      rwa [hd, show F.map f' = f from F.map_preimage _, show F.map g' = g from F.map_preimage _]
    · exact ⟨F.preimage r.i,F.preimage r.r,F.map_injective (by simp [r.retract]; rfl)⟩
  · intro h
    exact ⟨h.zero, fun A B C f g d ht ↦ h.triangles A B C (F.map f) (F.map g)
      (F.map d ≫ (F.commShiftIso (1 : ℤ)).hom.app A.inBoundedProjectives) (F.map_distinguished _ ht),
      fun P Q r ↦ h.retracts P Q (r.map F)⟩

/-- A presilting member maximal under compatible adjunction generates the
given two-term thick subcategory inside the bounded projective homotopy category. -/
theorem bounded_thick_of_maximal_presilting (k : Type u) [Field k] [Algebra k R]
    [Module.Finite k R] (he : IsEFinite R) {H : TwoTerm R → Prop}
    (hH : IsBoundedTwoTermThick H) (U : TwoTerm R) (hU : H U) (hu : U.IsPresilting)
    (hmax : ∀ P : TwoTerm R, H P → (U.directSum P).IsPresilting →
      IsInAdd P.homotopyObject U.homotopyObject) (X : TwoTerm R) :
    H X ↔ (ObjectProperty.singleton U.inBoundedProjectives).triangEnvelope X.inBoundedProjectives := by
  rw [bounded_thick_iff]
  exact inThick_iff_of_maximal_presilting k he ((isBoundedTwoTermThick_iff H).1 hH) U hU hu hmax X

/-- The thick-generation proposition for the paper's choice of any basic
presilting member with the largest possible number of indecomposable summands. -/
theorem bounded_thick_of_maximum_summands (k : Type u) [Field k] [Algebra k R]
    [Module.Finite k R] (he : IsEFinite R) {H : TwoTerm R → Prop}
    (hH : IsBoundedTwoTermThick H) (U : TwoTerm R) (hU : H U) (hu : U.IsPresilting)
    (l : List (HomotopyCategory (FGModuleCat.{u} R) (ComplexShape.up ℤ))) (hl : BasicDecomposition U l)
    (hmax : ∀ T t, H T → T.IsPresilting → BasicDecomposition T t → t.length ≤ l.length)
    (X : TwoTerm R) :
    H X ↔ (ObjectProperty.singleton U.inBoundedProjectives).triangEnvelope X.inBoundedProjectives := by
  rw [bounded_thick_iff]
  exact inThick_iff_of_maximum_summands k he ((isBoundedTwoTermThick_iff H).1 hH) U hU hu l hl hmax X

/-- Every two-term thick subcategory admits a basic presilting member of
largest summand count, and under E-finiteness this member generates it. -/
theorem exists_maximum_basic_thick_generator (k : Type u) [Field k] [Algebra k R]
    [Module.Finite k R] (he : IsEFinite R) {H : TwoTerm R → Prop} (hH : IsBoundedTwoTermThick H) :
    ∃ U l, H U ∧ U.IsPresilting ∧ BasicDecomposition U l ∧
      (∀ T t, H T → T.IsPresilting → BasicDecomposition T t → t.length ≤ l.length) ∧
      ∀ X : TwoTerm R, H X ↔ (ObjectProperty.singleton U.inBoundedProjectives).triangEnvelope X.inBoundedProjectives := by
  obtain ⟨U,l,hU,hu,hl,hmax⟩ := exists_maximum_basic_presilting k ((isBoundedTwoTermThick_iff H).1 hH)
  exact ⟨U,l,hU,hu,hl,hmax,bounded_thick_of_maximum_summands k he hH U hU hu l hl hmax⟩

end EFiniteCharacterizations.TwoTerm

namespace EFiniteCharacterizations

universe v
variable (k : Type v) [Field k] {R : Type v} [Ring R] [Algebra k R] [Module.Finite k R] [IsNoetherianRing R]

include k in
/-- The thick-generation characterization with both sides of the closure
comparison taken inside the bounded homotopy category of finite projectives. -/
theorem isEFinite_iff_boundedProjectiveThickGeneration :
    IsEFinite R ↔ ∀ H : TwoTerm R → Prop, TwoTerm.IsBoundedTwoTermThick H →
      ∃ U : TwoTerm R, U.IsPresilting ∧ ∀ X : TwoTerm R,
        H X ↔ (ObjectProperty.singleton U.inBoundedProjectives).triangEnvelope X.inBoundedProjectives := by
  rw [isEFinite_iff_twoTermThickGeneration k]
  simp only [TwoTerm.isBoundedTwoTermThick_iff, TwoTerm.bounded_thick_iff, TwoTermThickGeneration]

end EFiniteCharacterizations
