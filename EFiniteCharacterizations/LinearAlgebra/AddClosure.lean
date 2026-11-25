module

public import Mathlib.CategoryTheory.Preadditive.Basic

/-! # Additive closure in a preadditive category -/

@[expose] public section

open CategoryTheory

namespace EFiniteCharacterizations

variable {C : Type*} [Category C] [Preadditive C]

/-- The object `X` belongs to the additive closure of `Y` if its identity is
a finite sum of compositions through `Y`. In a category with finite direct
sums, this means that `X` is a direct summand of a finite sum of copies of `Y`. -/
def IsInAdd (X Y : C) : Prop :=
  ∃ l : List ((X ⟶ Y) × (Y ⟶ X)), (l.map (fun p ↦ p.1 ≫ p.2)).sum = 𝟙 X

theorem IsInAdd.of_retraction {X Y : C} (a : X ⟶ Y) (b : Y ⟶ X) (h : a ≫ b = 𝟙 X) : IsInAdd X Y :=
  ⟨[(a, b)], by simpa using h⟩

theorem IsInAdd.refl (X : C) : IsInAdd X X := of_retraction (𝟙 X) (𝟙 X) (Category.id_comp _)

private theorem exists_comp_factors {X Y Z : C} (hYZ : IsInAdd Y Z) (a : X ⟶ Y) (b : Y ⟶ X) :
    ∃ s : List ((X ⟶ Z) × (Z ⟶ X)), (s.map (fun p ↦ p.1 ≫ p.2)).sum = a ≫ b := by
  obtain ⟨t, ht⟩ := hYZ
  use t.map (fun p ↦ (a ≫ p.1, p.2 ≫ b))
  let f := (Preadditive.rightComp X b).comp (Preadditive.leftComp Y a)
  have h := congrArg f ht
  rw [map_list_sum, List.map_map] at h
  change (t.map (fun p ↦ (a ≫ (p.1 ≫ p.2)) ≫ b)).sum = (a ≫ 𝟙 Y) ≫ b at h
  rw [List.map_map]
  change (t.map (fun p ↦ (a ≫ p.1) ≫ (p.2 ≫ b))).sum = a ≫ b
  simpa only [Category.assoc, Category.comp_id] using h

theorem IsInAdd.trans {X Y Z : C} (hXY : IsInAdd X Y) (hYZ : IsInAdd Y Z) : IsInAdd X Z := by
  obtain ⟨l, hl⟩ := hXY
  suffices ∃ s : List ((X ⟶ Z) × (Z ⟶ X)),
      (s.map (fun p ↦ p.1 ≫ p.2)).sum = (l.map (fun p ↦ p.1 ≫ p.2)).sum from
    ⟨this.choose, this.choose_spec.trans hl⟩
  clear hl
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons p l ih =>
    obtain ⟨t', ht'⟩ := exists_comp_factors hYZ p.1 p.2
    obtain ⟨s, hs⟩ := ih
    exact ⟨t' ++ s, by simp [ht', hs]⟩

theorem IsInAdd.of_total {X U V Y : C} (hU : IsInAdd U Y) (hV : IsInAdd V Y)
    (p : X ⟶ U) (i : U ⟶ X) (q : X ⟶ V) (j : V ⟶ X) (h : p ≫ i + q ≫ j = 𝟙 X) :
    IsInAdd X Y := by
  obtain ⟨a, ha⟩ := exists_comp_factors hU p i
  obtain ⟨b, hb⟩ := exists_comp_factors hV q j
  exact ⟨a ++ b, by rw [List.map_append, List.sum_append, ha, hb, h]⟩

end EFiniteCharacterizations
