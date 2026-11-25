module

public import EFiniteCharacterizations.GrothendieckGroups.GrothendieckGroup
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.GroupTheory.Congruence.Hom
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-! # Grothendieck monoid of a subcategory with its inherited exact sequences -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

namespace EFiniteCharacterizations

variable {C : Type u} [Category.{v} C] [Abelian C] (T : ObjectProperty C)

namespace GrothendieckMonoid

/-- Relations on finite formal sums of objects in the subcategory. -/
inductive Relation : Multiset {X : C // T X} → Multiset {X : C // T X} → Prop
  | zero (X) (h : IsZero X.val) : Relation {X} 0
  | iso (X Y) (e : X.val ≅ Y.val) : Relation {X} {Y}
  | exact (S : ShortComplex C) (h : S.ShortExact) (a : T S.X₁) (b : T S.X₂) (c : T S.X₃) :
      Relation {⟨S.X₂,b⟩} ({⟨S.X₁,a⟩} + {⟨S.X₃,c⟩})

end GrothendieckMonoid

abbrev GrothendieckMonoid := (addConGen (GrothendieckMonoid.Relation T)).Quotient

namespace GrothendieckMonoid

def of (X : C) (hX : T X) : GrothendieckMonoid T :=
  (addConGen (Relation T)).mk' {⟨X,hX⟩}

theorem of_isZero (X : C) (hX : T X) (hz : IsZero X) : of T X hX = 0 :=
  (addConGen (Relation T)).eq.mpr (AddConGen.Rel.of _ _ (.zero _ hz))

theorem of_iso {X Y : C} (hx : T X) (hy : T Y) (e : X ≅ Y) : of T X hx = of T Y hy :=
  (addConGen (Relation T)).eq.mpr (AddConGen.Rel.of _ _ (.iso _ _ e))

theorem of_shortExact (S : ShortComplex C) (hs : S.ShortExact)
    (a : T S.X₁) (b : T S.X₂) (c : T S.X₃) :
    of T S.X₂ b = of T S.X₁ a + of T S.X₃ c :=
  (addConGen (Relation T)).eq.mpr (AddConGen.Rel.of _ _ (.exact S hs a b c))

/-- Finite sums of exact-category classes can be represented by a single object. -/
theorem exists_representative [T.IsClosedUnderExtensions] (h₀ : T 0) (m : GrothendieckMonoid T) :
    ∃ (X : C) (hX : T X), of T X hX = m := by
  obtain ⟨s,rfl⟩ := (addConGen (Relation T)).mk'_surjective m
  induction s using Multiset.induction_on with
  | empty => exact ⟨0,h₀,of_isZero T _ h₀ (isZero_zero C)⟩
  | cons X s ih =>
    obtain ⟨Y,hy,he⟩ := ih
    let S := (ShortComplex.Splitting.ofHasBinaryBiproduct X.val Y).shortExact
    have hb := T.prop_X₂_of_shortExact S X.property hy
    refine ⟨_,hb,?_⟩
    rw [of_shortExact T _ S X.property hb hy, he]
    rfl

variable {A : Type*} [AddCommMonoid A]

def formalSum (f : (X : {X : C // T X}) → A) : Multiset {X : C // T X} →+ A where
  toFun s := (s.map f).sum
  map_zero' := rfl
  map_add' _ _ := by simp

omit [Abelian C] in
private theorem formalSum_singleton (f : {X : C // T X} → A) (X : {X : C // T X}) :
    formalSum T f {X} = f X := by
  change (Multiset.map f {X}).sum = _
  simp

/-- Any additive invariant of the inherited exact sequences descends to the monoid. -/
noncomputable def lift (f : {X : C // T X} → A)
    (hz : ∀ X, IsZero X.val → f X = 0)
    (hi : ∀ X Y, (X.val ≅ Y.val) → f X = f Y)
    (he : ∀ (S : ShortComplex C) (_ : S.ShortExact) (a : T S.X₁) (b : T S.X₂) (c : T S.X₃),
      f ⟨S.X₂,b⟩ = f ⟨S.X₁,a⟩ + f ⟨S.X₃,c⟩) : GrothendieckMonoid T →+ A :=
  (addConGen (Relation T)).lift (formalSum T f) (AddCon.addConGen_le.mpr (by
    intro x y h
    change formalSum T f x = formalSum T f y
    cases h with
    | zero X h => simpa only [formalSum_singleton, map_zero] using hz X h
    | iso X Y e => simpa only [formalSum_singleton] using hi X Y e
    | exact S h a b c => simpa only [formalSum_singleton, map_add] using he S h a b c))

@[simp] theorem lift_of (f : {X : C // T X} → A) (hz hi he) (X : C) (hX : T X) :
    lift T f hz hi he (of T X hX) = f ⟨X,hX⟩ :=
  formalSum_singleton T f _

/-- The canonical homomorphism taking a module to its ambient class. -/
noncomputable def dimensionMap : GrothendieckMonoid T →+ GrothendieckGroup C :=
  lift T (fun X ↦ GrothendieckGroup.of X.val) (fun _ ↦ GrothendieckGroup.of_isZero)
    (fun _ _ ↦ GrothendieckGroup.of_eq_of_iso) (fun S h _ _ _ ↦ GrothendieckGroup.of_shortExact S h)

@[simp] theorem dimensionMap_of (X : C) (hX : T X) :
    dimensionMap T (of T X hX) = GrothendieckGroup.of X :=
  lift_of ..

theorem dimensionMap_injective_iff [T.IsClosedUnderExtensions] (h₀ : T 0) :
    Function.Injective (dimensionMap T) ↔
      ∀ (X Y : C) (hx : T X) (hy : T Y), GrothendieckGroup.of X = GrothendieckGroup.of Y →
        of T X hx = of T Y hy := by
  constructor
  · intro h X Y hx hy e
    exact h (by simpa using e)
  · intro h a b e
    obtain ⟨X,hx,rfl⟩ := exists_representative T h₀ a
    obtain ⟨Y,hy,rfl⟩ := exists_representative T h₀ b
    exact h X Y hx hy (by simpa using e)

end GrothendieckMonoid
end EFiniteCharacterizations
