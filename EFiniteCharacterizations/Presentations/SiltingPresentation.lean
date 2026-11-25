module

public import EFiniteCharacterizations.Silting.ThickSubcategories.ThickBongartz

/-! # Presentation triangles for two-term complexes -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ModuleCat.Algebra

namespace EFiniteCharacterizations

section Additive

variable {C : Type*} [Category C] [Preadditive C] {X Y Z : C}

private theorem all_zero (h : ∀ f : X ⟶ Y, f = 0) : Subsingleton (X ⟶ Y) :=
  ⟨fun f g ↦ (h f).trans (h g).symm⟩

theorem subsingleton_from_add (h : IsInAdd X Y) (hz : Subsingleton (Y ⟶ Z)) :
    Subsingleton (X ⟶ Z) := by
  obtain ⟨l, hl⟩ := h
  apply all_zero
  intro f
  have e := congrArg (Preadditive.rightComp X f) hl
  rw [map_list_sum, List.map_map] at e
  change (l.map (fun p ↦ (p.1 ≫ p.2) ≫ f)).sum = 𝟙 X ≫ f at e
  have hz' (a : Y ⟶ X) : a ≫ f = 0 := hz.elim _ _
  simpa [Category.assoc, hz'] using e.symm

theorem subsingleton_to_add (h : IsInAdd Y Z) (hz : Subsingleton (X ⟶ Z)) :
    Subsingleton (X ⟶ Y) := by
  obtain ⟨l, hl⟩ := h
  apply all_zero
  intro f
  have e := congrArg (Preadditive.leftComp Y f) hl
  rw [map_list_sum, List.map_map] at e
  change (l.map (fun p ↦ f ≫ p.1 ≫ p.2)).sum = f ≫ 𝟙 Y at e
  have hz' (a : Y ⟶ Z) : f ≫ a = 0 := hz.elim _ _
  simpa [← Category.assoc, hz'] using e.symm

end Additive

namespace Presilting

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- The cone of a right approximation, shifted back one degree, belongs to
add(T) under the two vanishing conditions used in the Bongartz presentation. -/
theorem firstTerm_inAdd_of_approximation (T A B Y : C) (i : A ⟶ B) (p : B ⟶ Y)
    (δ : Y ⟶ A⟦(1 : ℤ)⟧) (ht : Triangle.mk i p δ ∈ distTriang _)
    (hT : ∀ n : ℤ, 0 < n → Subsingleton (T ⟶ T⟦n⟧)) (hB : IsInAdd B T)
    (hY : (ObjectProperty.singleton T).triangEnvelope Y)
    (hTY : ∀ n : ℤ, 0 < n → Subsingleton (T ⟶ Y⟦n⟧))
    (hYT : ∀ n : ℤ, 1 < n → Subsingleton (Y ⟶ T⟦n⟧))
    (hp : ∀ f : T ⟶ Y, ∃ g : T ⟶ B, g ≫ p = f) : IsInAdd A T := by
  let D := (ObjectProperty.singleton T).triangEnvelope
  let K := Triangle.mk i p δ
  have hB' : D B := mem_thick_of_isInAdd T B hB
  have hA : D A := D.ext_of_isTriangulatedClosed₁ K ht hB' hY
  have hTB (n : ℤ) (hn : 0 < n) : Subsingleton (T ⟶ B⟦n⟧) :=
    subsingleton_to_add (hB.map (shiftFunctor C n)) (hT n hn)
  apply isInAdd_of_mem_thick T hT hA
  · intro n hn
    rcases eq_or_lt_of_le (show 1 ≤ n by omega) with rfl | hn'
    · apply all_zero
      intro f
      obtain ⟨g,hg⟩ := Triangle.coyoneda_exact₁ K ht f ((hTB 1 (by decide)).elim _ _)
      obtain ⟨g',rfl⟩ := hp g
      change f = (g' ≫ p) ≫ δ at hg
      rw [hg, Category.assoc, show p ≫ δ = 0 from comp_distTriang_mor_zero₂₃ K ht, comp_zero]
    · let L := K.rotate.rotate⟦n-1⟧
      have hl : L ∈ distTriang C := Triangle.shift_distinguished _ (rot_of_distTriang _ (rot_of_distTriang K ht)) _
      let e := (shiftFunctorAdd' C 1 (n-1) n (by omega)).app B
      have := hTB n hn
      have h₃ : Subsingleton (T ⟶ L.obj₃) := (Iso.homCongr (Iso.refl T) e).symm.injective.subsingleton
      have h₂ : Subsingleton (T ⟶ L.obj₂) := all_zero fun f ↦ by
        obtain ⟨g,hg⟩ := Triangle.coyoneda_exact₂ L hl f (h₃.elim _ _)
        exact hg.trans ((congrArg (· ≫ L.mor₁) ((hTY (n-1) (by omega)).elim g 0)).trans (zero_comp))
      have : Subsingleton (T ⟶ (shiftFunctor C (1 : ℤ) ⋙ shiftFunctor C (n-1)).obj A) := h₂
      exact (Iso.homCongr (Iso.refl T) ((shiftFunctorAdd' C 1 (n-1) n (by omega)).app A)).injective.subsingleton
  · intro n hn
    have h₁ : Subsingleton (Y⟦(-1 : ℤ)⟧ ⟶ T⟦n⟧) := between_shifts (hYT _ (by omega))
    have h₃ := subsingleton_from_add hB (hT n hn)
    apply all_zero
    intro f
    obtain ⟨g,hg⟩ := Triangle.yoneda_exact₂ K.invRotate (inv_rot_of_distTriang K ht) f (h₁.elim _ _)
    change f = i ≫ g at hg
    simpa [h₃.elim g 0] using hg

/-- A basis of the finite-dimensional Hom space gives a right approximation
by a finite sum of T. Its fiber gives a presentation with both terms in add(T). -/
theorem exists_presentation (k : Type*) [Field k] [Linear k C] [HasFiniteBiproducts C]
    (T Y : C) [Module.Finite k (T ⟶ Y)]
    (ht : ∀ n : ℤ, 0 < n → Subsingleton (T ⟶ T⟦n⟧)) (hy : (ObjectProperty.singleton T).triangEnvelope Y)
    (hTY : ∀ n : ℤ, 0 < n → Subsingleton (T ⟶ Y⟦n⟧))
    (hYT : ∀ n : ℤ, 1 < n → Subsingleton (Y ⟶ T⟦n⟧)) :
    ∃ (A B : C) (i : A ⟶ B) (p : B ⟶ Y) (δ : Y ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk i p δ ∈ distTriang C ∧ IsInAdd A T ∧ IsInAdd B T := by
  classical
  let b := Module.finBasis k (T ⟶ Y)
  let objects (_ : Fin (Module.finrank k (T ⟶ Y))) := T
  let B := ⨁ objects
  let p : B ⟶ Y := biproduct.desc b
  have hB : IsInAdd B T := ⟨List.ofFn (fun j ↦ (biproduct.π objects j, biproduct.ι objects j)), by
    rw [List.map_ofFn, Fin.sum_ofFn]
    exact biproduct.total⟩
  obtain ⟨A,i,δ,hA⟩ := distinguished_cocone_triangle₁ p
  refine ⟨A,B,i,p,δ,hA,firstTerm_inAdd_of_approximation T A B Y i p δ hA ht hB hy hTY hYT ?_,hB⟩
  intro f
  refine ⟨∑ j, b.repr f j • biproduct.ι objects j, ?_⟩
  simpa only [p, Preadditive.sum_comp, Linear.smul_comp, biproduct.ι_desc] using b.sum_repr f

end Presilting

namespace TwoTerm
universe u
variable (k : Type u) [Field k] {R : Type u} [Ring R] [IsNoetherianRing R] [Algebra k R] [Module.Finite k R]

theorem homotopyHom_finite (T Y : TwoTerm R) : Module.Finite k (T.homotopyObject ⟶ Y.homotopyObject) := by
  have (X Z : FGModuleCat.{u} R) : Module.Finite k (X ⟶ Z) := finiteModuleHom_isFinite k X Z
  let ev (j : ℤ) : (T.toCochainComplex ⟶ Y.toCochainComplex) →ₗ[k]
      (T.toCochainComplex.X j ⟶ Y.toCochainComplex.X j) :=
    { toFun := fun f ↦ f.f j, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have : Module.Finite k (T.toCochainComplex ⟶ Y.toCochainComplex) :=
    Module.Finite.of_injective ((ev (-1)).prod (ev 0)) (by
      intro a b hab
      exact HomologicalComplex.from_double_hom_ext (congrArg Prod.fst hab) (congrArg Prod.snd hab))
  let F := HomotopyCategory.quotient (FGModuleCat R) (ComplexShape.up ℤ)
  exact Module.Finite.of_surjective (F.mapLinearMap k (X := T.toCochainComplex) (Y := Y.toCochainComplex)) F.map_surjective

include k in
/-- Every right-orthogonal Y has a presentation by the Bongartz completion of U.
One completion works for all such Y. -/
theorem exists_bongartz_presentation (U : TwoTerm R) (hu : U.IsPresilting) :
    ∃ B : TwoTerm R, let T := U.directSum B
      T.IsPresilting ∧ (∀ X : TwoTerm R, InThick T X) ∧
      ∀ Y : TwoTerm R, Function.Surjective (homotopyBoundary U Y) →
        ∃ (A D : HomotopyCategory (FGModuleCat R) (ComplexShape.up ℤ))
          (i : A ⟶ D) (p : D ⟶ Y.homotopyObject) (δ : Y.homotopyObject ⟶ A⟦(1 : ℤ)⟧),
          Triangle.mk i p δ ∈ distTriang _ ∧ IsInAdd A T.homotopyObject ∧ IsInAdd D T.homotopyObject := by
  obtain ⟨B,hT,hgen,horth⟩ := exists_bongartz_generator k U hu
  let T := U.directSum B
  refine ⟨B,hT,hgen,?_⟩
  intro Y hY
  have := homotopyHom_finite k T Y
  exact Presilting.exists_presentation k T.homotopyObject Y.homotopyObject
    ((isPresilting_iff_homotopy T).1 hT) (hgen Y) ((surjective_boundary_iff_homotopy T Y).1 (horth Y hY))
    (fun _ hn ↦ subsingleton_hom_shift_of_one_lt Y T hn)

end TwoTerm
end EFiniteCharacterizations
