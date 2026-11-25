module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.RingTheory.Nilpotent.Defs

/-! # Extracting a summand from iterated extensions of a cone -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open scoped ZeroObject

namespace EFiniteCharacterizations.Presilting

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (H : ObjectProperty C) [H.IsClosedUnderIsomorphisms] [H.IsTriangulatedClosed₂]

/-- The octahedral axiom closes maps with cones in an extension-closed
subcategory under composition. -/
private theorem compose_cones {W X T : C} {f : W ⟶ X} {g : X ⟶ T}
    (hf : H.trW f) (hg : H.trW g) : H.trW (f ≫ g) := by
  obtain ⟨Y,u,v,hy,hY⟩ := hf
  obtain ⟨Z,s,t,hz,hZ⟩ := hg
  obtain ⟨D,p,q,hd⟩ := distinguished_cocone_triangle (f ≫ g)
  exact ⟨D,p,q,hd,H.ext_of_isTriangulatedClosed₂ _ (someOctahedron rfl hy hz hd).mem hY hZ⟩

omit [IsTriangulated C] [H.IsClosedUnderIsomorphisms] [H.IsTriangulatedClosed₂] in
/-- Add a split complement to the source of a map while keeping its cone.
The new target retracts onto the old one in a commuting square. -/
private theorem extend_along_section {W X T : C} (f : W ⟶ X) (hf : H.trW f)
    (s : W ⟶ T) (p : T ⟶ W) (hsp : s ≫ p = 𝟙 W) :
    ∃ (T' : C) (j : T ⟶ T') (u : X ⟶ T') (v : T' ⟶ X),
      H.trW j ∧ u ≫ v = 𝟙 X ∧ j ≫ v = p ≫ f := by
  obtain ⟨Y,g,t,ht,hy⟩ := hf
  obtain ⟨T',j,g',ht'⟩ := distinguished_cocone_triangle₂ (t ≫ s⟦(1 : ℤ)⟧')
  obtain ⟨a,ha₁,ha₂⟩ := complete_distinguished_triangle_morphism₂ _ _ ht ht'
    s (𝟙 Y) (by simp)
  obtain ⟨b,hb₁,hb₂⟩ := complete_distinguished_triangle_morphism₂ _ _ ht' ht
    p (𝟙 Y) (by dsimp; simp [Category.assoc,← Functor.map_comp,hsp])
  dsimp at ha₁ ha₂ hb₁ hb₂
  let φ := Triangle.homMk (Triangle.mk f g t) (Triangle.mk f g t) (𝟙 W) (a ≫ b) (𝟙 Y)
    (by dsimp; grind) (by dsimp; grind)
  have : IsIso (a ≫ b) := isIso₂_of_isIso₁₃ φ ht ht (IsIso.id _) (IsIso.id _)
  refine ⟨T',j,inv (a ≫ b) ≫ a,b,⟨Y,g',_,ht',hy⟩,by simp,?_⟩
  simpa using hb₁

/-- A retract of W on which the projected component of f eventually vanishes
belongs to the extension- and summand-closed subcategory containing its cone. -/
theorem mem_retract_of_component_power [H.ContainsZero] [H.IsStableUnderRetracts]
    {N W X : C} (f : W ⟶ X) (p : X ⟶ W) (s : W ⟶ X) (hs : s ≫ p = 𝟙 W)
    (hf : H.trW f) (r : Retract N W) (m : ℕ) (hm : let a : End W := f ≫ p; (a ^ m : End W) ≫ r.r = 0) : H N := by
  let a : End W := f ≫ p
  have iter (n : ℕ) : ∃ (T : C) (i : W ⟶ T) (q : T ⟶ W) (e : W ⟶ T),
      H.trW i ∧ e ≫ q = 𝟙 W ∧ i ≫ q = (a ^ n : End W) := by
    induction n with
    | zero => exact ⟨W,𝟙 _,𝟙 _,𝟙 _,H.trW.id_mem _,by simp,by simp⟩
    | succ n ih =>
      obtain ⟨T,i,q,e,hi,he,ha⟩ := ih
      obtain ⟨T',j,u,v,hj,hu,hjv⟩ := extend_along_section H f hf e q he
      refine ⟨T',i ≫ j,v ≫ p,s ≫ u,compose_cones H hi hj,by simp [hu,hs,← Category.assoc u],?_⟩
      rw [Category.assoc,← Category.assoc j,hjv,Category.assoc q,← Category.assoc i,ha,pow_succ']
      rfl
  obtain ⟨T,i,q,e,hi,he,ha⟩ := iter m
  obtain ⟨Y,g,t,ht,hy⟩ := hi
  have hz : i ≫ q ≫ r.r = 0 := by rw [← Category.assoc, ha]; exact hm
  obtain ⟨b,hb⟩ := Triangle.yoneda_exact₂ _ ht (q ≫ r.r) hz
  change q ≫ r.r = g ≫ b at hb
  refine H.prop_of_retract (Retract.mk (r.i ≫ e ≫ g) b ?_) hy
  rw [Category.assoc, Category.assoc, ← hb, ← Category.assoc e, he, Category.id_comp, r.retract]

/-- If a map from W has cone in H and its component on a split copy of
W in the target is nilpotent, then W belongs to H. -/
theorem mem_of_nilpotent_component [H.ContainsZero] [H.IsStableUnderRetracts]
    {W X : C} (f : W ⟶ X) (p : X ⟶ W) (s : W ⟶ X) (hs : s ≫ p = 𝟙 W)
    (hf : H.trW f) (hn : IsNilpotent (R := End W) (f ≫ p)) : H W := by
  obtain ⟨m,hm⟩ := hn
  exact mem_retract_of_component_power H f p s hs hf (Retract.refl W) m (by
    let a : End W := f ≫ p
    change (a ^ m : End W) ≫ 𝟙 W = 0
    rw [Category.comp_id, hm])

end EFiniteCharacterizations.Presilting
