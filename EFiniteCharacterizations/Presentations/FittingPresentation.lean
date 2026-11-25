module

public import EFiniteCharacterizations.LinearAlgebra.AddClosure
public import EFiniteCharacterizations.Silting.ThickSubcategories.NilpotentCone

/-! # Removing the invertible component of a presentation triangle -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace EFiniteCharacterizations.Presilting

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

set_option backward.isDefEq.respectTransparency false in
/-- In a triangle W → W ⊕ V → Y, suppose the identity of W is the sum of
a map through N and the product of the W-component with a commuting
endomorphism. If Hom(Y,N[1]) vanishes, Y belongs to add(N ⊕ V). -/
theorem isInAdd_of_biprod_presentation {W V Y N U : C} [HasBinaryBiproduct W V]
    (f : W ⟶ W ⊞ V) (p : W ⊞ V ⟶ Y) (δ : Y ⟶ W⟦(1 : ℤ)⟧)
    (ht : Triangle.mk f p δ ∈ distTriang C)
    (r : W ⟶ N) (i : N ⟶ W) (c : W ⟶ W)
    (hcomm : c ≫ (f ≫ biprod.fst) = (f ≫ biprod.fst) ≫ c)
    (htotal : r ≫ i + c ≫ (f ≫ biprod.fst) = 𝟙 W)
    (hz : Subsingleton (Y ⟶ N⟦(1 : ℤ)⟧)) (hN : IsInAdd N U) (hV : IsInAdd V U) :
    IsInAdd Y U := by
  let T := Triangle.mk f p δ
  let F := shiftFunctor C (1 : ℤ)
  have hδf : δ ≫ F.map f = 0 := comp_distTriang_mor_zero₃₁ T ht
  have hδr : δ ≫ F.map r = 0 := hz.elim _ _
  have hδ : δ = 0 := by
    have h := congrArg (fun a : W ⟶ W ↦ δ ≫ F.map a) (hcomm ▸ htotal)
    simp only [F.map_add, F.map_comp, F.map_id, Preadditive.comp_add] at h
    exact (Category.comp_id δ).symm.trans (by
      simpa only [← Category.assoc, hδr, hδf, zero_comp, add_zero] using h.symm)
  obtain ⟨s,hs⟩ := Triangle.coyoneda_exact₃ T ht (𝟙 Y) (by change 𝟙 Y ≫ δ = 0; simp [hδ])
  change 𝟙 Y = s ≫ p at hs
  let a := f ≫ biprod.fst
  let b := f ≫ biprod.snd
  let x := biprod.inl ≫ p
  let y := biprod.inr ≫ p
  have hdecomp (D : C) (g : D ⟶ W ⊞ V) : (g ≫ biprod.fst) ≫ x + (g ≫ biprod.snd) ≫ y = g ≫ p := by
    have h := congrArg (fun z : W ⊞ V ⟶ W ⊞ V ↦ g ≫ z ≫ p) (biprod.total (X := W) (Y := V))
    simpa only [Preadditive.add_comp, Preadditive.comp_add, Category.id_comp, Category.assoc, x,y] using h
  have hab : a ≫ x + b ≫ y = 0 := (hdecomp W f).trans (comp_distTriang_mor_zero₁₂ T ht)
  have hx : x = r ≫ i ≫ x - c ≫ b ≫ y := by
    have h := congrArg (fun z : W ⟶ W ↦ z ≫ x) htotal
    simp only [Preadditive.add_comp, Category.id_comp, Category.assoc] at h
    rw [← Category.assoc f biprod.fst x, show (f ≫ biprod.fst) ≫ x = -(b ≫ y) from eq_neg_of_add_eq_zero_left hab,
      Preadditive.comp_neg, ← sub_eq_add_neg] at h
    exact h.symm
  refine IsInAdd.of_total hN hV (s ≫ biprod.fst ≫ r) (i ≫ x)
    (s ≫ biprod.snd - s ≫ biprod.fst ≫ c ≫ b) y ?_
  have h := (hdecomp Y s).trans hs.symm
  rw [hx] at h
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc] at h ⊢
  rw [← h]
  abel

end EFiniteCharacterizations.Presilting
