module

public import EFiniteCharacterizations.Presentations.StableAdd
public import Mathlib.CategoryTheory.Preadditive.Comma

/-! # Precomposition on summands of projective maps -/

@[expose] public section

open CategoryTheory

namespace EFiniteCharacterizations

variable {C : Type*} [Category C] [Preadditive C] {Q P : Arrow C}

private theorem comp_decompose (F : Arrow C ⥤ C) [F.Additive] {M : C} (f : F.obj Q ⟶ M)
    {l : List ((Q ⟶ P) × (P ⟶ Q))} (h : (l.map (fun p ↦ p.1 ≫ p.2)).sum = 𝟙 Q) :
    (l.map (fun p ↦ F.map p.1 ≫ F.map p.2 ≫ f)).sum = f := by
  let ev := (Preadditive.rightComp _ f).comp (F.mapAddHom (X := Q) (Y := Q))
  have he := congrArg ev h
  simpa [ev,Preadditive.rightComp,map_list_sum,List.map_map,Function.comp_def] using he

theorem IsInAdd.injective_precomp (h : IsInAdd Q P) {M : C}
    (hp : Function.Injective (fun f : P.right ⟶ M ↦ P.hom ≫ f)) :
    Function.Injective (fun f : Q.right ⟶ M ↦ Q.hom ≫ f) := by
  obtain ⟨l,hl⟩ := h
  intro f g he
  change Q.hom ≫ f = Q.hom ≫ g at he
  have heq (p : (Q ⟶ P) × (P ⟶ Q)) : p.2.right ≫ f = p.2.right ≫ g := by
    apply hp
    change P.hom ≫ p.2.right ≫ f = P.hom ≫ p.2.right ≫ g
    rw [← Arrow.w_assoc,← Arrow.w_assoc,he]
  rw [← comp_decompose Arrow.rightFunc f hl,← comp_decompose Arrow.rightFunc g hl]
  change (l.map (fun p ↦ p.1.right ≫ p.2.right ≫ f)).sum = (l.map (fun p ↦ p.1.right ≫ p.2.right ≫ g)).sum
  simp only [heq]

theorem IsInAdd.surjective_precomp (h : IsInAdd Q P) {M : C}
    (hp : Function.Surjective (fun f : P.right ⟶ M ↦ P.hom ≫ f)) :
    Function.Surjective (fun f : Q.right ⟶ M ↦ Q.hom ≫ f) := by
  obtain ⟨l,hl⟩ := h
  intro f
  choose lift hLift using fun p : (Q ⟶ P) × (P ⟶ Q) ↦ hp (p.2.left ≫ f)
  refine ⟨(l.map (fun p ↦ p.1.right ≫ lift p)).sum, ?_⟩
  change Q.hom ≫ _ = f
  rw [← comp_decompose Arrow.leftFunc f hl]
  let pre := Preadditive.leftComp M Q.hom
  change pre _ = _
  simp only [map_list_sum,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro p _
  change Q.hom ≫ p.1.right ≫ lift p = _
  rw [← Arrow.w_assoc]
  exact congrArg (p.1.left ≫ ·) (hLift p)

end EFiniteCharacterizations
