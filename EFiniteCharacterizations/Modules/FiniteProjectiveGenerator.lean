module

public import Mathlib.CategoryTheory.Abelian.Yoneda
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
public import Mathlib.Algebra.Category.FGModuleCat.Abelian

/-! # Finite module categories represented by a projective generator -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
universe v u
namespace EFiniteCharacterizations.FiniteProjectiveGenerator

variable {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C] (G : C)

private theorem detect (gen : ∀ X : C, ∃ (n : ℕ) (p : (⨁ fun _ : Fin n ↦ G) ⟶ X), Epi p)
    {X Y : C} {f g : X ⟶ Y} (h : ∀ a : G ⟶ X, a ≫ f = a ≫ g) : f = g := by
  obtain ⟨n,p,_⟩ := gen X
  apply (cancel_epi p).1
  apply biproduct.hom_ext'
  intro j
  simpa only [Category.assoc] using h (biproduct.ι (fun _ : Fin n ↦ G) j ≫ p)

/-- The action of a module map out of Hom(G,X) on a map from a finite sum
of G is determined by its restrictions to the summands. -/
private theorem descend_on_sum {X Y : C} {n : ℕ} (p : (⨁ fun _ : Fin n ↦ G) ⟶ X)
    (a : (preadditiveCoyonedaObj G).obj X ⟶ (preadditiveCoyonedaObj G).obj Y)
    (t : G ⟶ ⨁ fun _ : Fin n ↦ G) :
    t ≫ biproduct.desc (fun i ↦ a.hom (biproduct.ι (fun _ : Fin n ↦ G) i ≫ p)) = a.hom (t ≫ p) := by
  let A := fun _ : Fin n ↦ G
  have eq {Z : C} (w : (⨁ A) ⟶ Z) : t ≫ w = ∑ j, (t ≫ biproduct.π A j) ≫ biproduct.ι A j ≫ w := by
    conv_lhs => rw [← Category.id_comp w,← biproduct.total (f := A)]
    simp only [Preadditive.comp_sum,Preadditive.sum_comp,Category.assoc]
  rw [eq p]
  have hadd : a.hom (∑ j, (t ≫ biproduct.π A j) ≫ biproduct.ι A j ≫ p) =
      ∑ j, a.hom ((t ≫ biproduct.π A j) ≫ biproduct.ι A j ≫ p) :=
    map_sum a.hom _ _
  refine Eq.trans ?_ hadd.symm
  have sum : t = ∑ j, (t ≫ biproduct.π A j) ≫ biproduct.ι A j := by
    exact (Category.comp_id t).symm.trans ((eq (𝟙 _)).trans (by simp))
  conv_lhs => rw [sum]
  rw [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  have hι : biproduct.ι A j ≫ biproduct.desc (fun i ↦ a.hom (biproduct.ι A i ≫ p)) =
      a.hom (biproduct.ι A j ≫ p) := biproduct.ι_desc _ j
  rw [Category.assoc,hι]
  exact (a.hom.map_smul (MulOpposite.op (t ≫ biproduct.π A j)) (biproduct.ι A j ≫ p)).symm

theorem fullyFaithful [Projective G]
    (gen : ∀ X : C, ∃ (n : ℕ) (p : (⨁ fun _ : Fin n ↦ G) ⟶ X), Epi p) :
    (preadditiveCoyonedaObj G).Full ∧ (preadditiveCoyonedaObj G).Faithful := by
  classical
  constructor
  · constructor
    intro X Y a
    obtain ⟨n,p,_⟩ := gen X
    let A := fun _ : Fin n ↦ G
    let h := biproduct.desc (fun i ↦ a.hom (biproduct.ι A i ≫ p))
    have kill : kernel.ι p ≫ h = 0 := by
      apply detect G gen
      intro t
      rw [← Category.assoc,comp_zero]
      rw [show (t ≫ kernel.ι p) ≫ h = a.hom ((t ≫ kernel.ι p) ≫ p) from descend_on_sum G p a _]
      rw [Category.assoc,kernel.condition,comp_zero]
      exact a.hom.map_zero
    let f := Abelian.epiDesc p h kill
    refine ⟨f,?_⟩
    apply ModuleCat.hom_ext
    ext t
    let e := Projective.factorThru t p
    have he : e ≫ p = t := Projective.factorThru_comp t p
    change t ≫ f = a.hom t
    rw [← he,Category.assoc,Abelian.comp_epiDesc]
    exact descend_on_sum G p a e
  · constructor
    intro X Y f g h
    exact detect G gen (fun t ↦ congrArg (fun z ↦ ModuleCat.Hom.hom z t) h)

private noncomputable def regularIso :
    (preadditiveCoyonedaObj G).obj G ≅ ModuleCat.of (End G)ᵐᵒᵖ (End G)ᵐᵒᵖ :=
  LinearEquiv.toModuleIso
    { toFun := MulOpposite.op
      invFun := MulOpposite.unop
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

private noncomputable def powerIso (n : ℕ) :
    (preadditiveCoyonedaObj G).obj (⨁ fun _ : Fin n ↦ G) ≅ ModuleCat.of (End G)ᵐᵒᵖ (Fin n → (End G)ᵐᵒᵖ) :=
  (preadditiveCoyonedaObj G).mapBiproduct _ ≪≫
    biproduct.mapIso (fun _ ↦ regularIso G) ≪≫ ModuleCat.biproductIsoPi _

theorem hom_is_finite [Projective G]
    (gen : ∀ X : C, ∃ (n : ℕ) (p : (⨁ fun _ : Fin n ↦ G) ⟶ X), Epi p) (X : C) :
    Module.Finite (End G)ᵐᵒᵖ ((preadditiveCoyonedaObj G).obj X) := by
  obtain ⟨n,p,_⟩ := gen X
  let q := (powerIso G n).inv ≫ (preadditiveCoyonedaObj G).map p
  exact Module.Finite.of_surjective q.hom ((ModuleCat.epi_iff_surjective _).1 inferInstance)

private theorem finite_mem_essImage [Projective G] [IsNoetherianRing (End G)ᵐᵒᵖ]
    (gen : ∀ X : C, ∃ (n : ℕ) (p : (⨁ fun _ : Fin n ↦ G) ⟶ X), Epi p)
    (M : FGModuleCat.{v} (End G)ᵐᵒᵖ) : (preadditiveCoyonedaObj G).essImage M.obj := by
  let F := preadditiveCoyonedaObj G
  let A := (End G)ᵐᵒᵖ
  have ff := fullyFaithful G gen
  let _ : F.Full := ff.1
  let _ : F.Faithful := ff.2
  let _ := M.property
  obtain ⟨n,p,hp⟩ := Module.Finite.exists_fin' A M
  obtain ⟨m,q,hq⟩ := Module.Finite.exists_fin' A p.ker
  let f : ModuleCat.of A (Fin m → A) ⟶ ModuleCat.of A (Fin n → A) :=
    ModuleCat.ofHom (p.ker.subtype.comp q)
  have im (d : ℕ) : F.essImage (ModuleCat.of A (Fin d → A)) :=
    ⟨_,⟨powerIso G d⟩⟩
  have hc : F.essImage (cokernel f) := by
    apply F.essImage.prop_colimit (parallelPair f 0)
    intro j
    cases j
    · exact im m
    · exact im n
  have hr : LinearMap.range f.hom = p.ker := by
    change LinearMap.range (p.ker.subtype.comp q) = p.ker
    rw [LinearMap.range_comp,LinearMap.range_eq_top.mpr hq,Submodule.map_top,Submodule.range_subtype]
  let e : cokernel f ≅ M.obj := ModuleCat.cokernelIsoRangeQuotient f ≪≫
    ((Submodule.quotEquivOfEq _ _ hr).trans (p.quotKerEquivOfSurjective hp)).toModuleIso
  exact F.essImage.prop_of_iso e hc

/-- A projective generator whose finite sums cover every object represents
the abelian category by finite right modules over its endomorphism ring. -/
noncomputable def equivalence [Projective G] [IsNoetherianRing (End G)ᵐᵒᵖ]
    (gen : ∀ X : C, ∃ (n : ℕ) (p : (⨁ fun _ : Fin n ↦ G) ⟶ X), Epi p) :
    C ≌ FGModuleCat.{v} (End G)ᵐᵒᵖ := by
  let F := preadditiveCoyonedaObj G
  let _ : F.Full := (fullyFaithful G gen).1
  let _ : F.Faithful := (fullyFaithful G gen).2
  let T := (ModuleCat.isFG (End G)ᵐᵒᵖ).lift F (hom_is_finite G gen)
  let _ : T.EssSurj := ⟨fun M ↦ by
    obtain ⟨X,⟨e⟩⟩ := finite_mem_essImage G gen M
    exact ⟨X,⟨(ModuleCat.isFG (End G)ᵐᵒᵖ).ι.preimageIso e⟩⟩⟩
  let _ : T.Full := ⟨fun f ↦ by
    obtain ⟨a,ha⟩ := F.map_surjective f.hom
    exact ⟨a,(ModuleCat.isFG _).ι.map_injective ha⟩⟩
  let _ : T.Faithful := ⟨fun h ↦ F.map_injective (congrArg (fun z ↦ z.hom) h)⟩
  let _ : T.IsEquivalence := {}
  exact T.asEquivalence

end EFiniteCharacterizations.FiniteProjectiveGenerator
