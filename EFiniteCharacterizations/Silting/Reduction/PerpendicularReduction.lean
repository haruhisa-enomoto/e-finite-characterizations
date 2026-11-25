module

public import EFiniteCharacterizations.Silting.Reduction.BongartzEndomorphisms
public import EFiniteCharacterizations.Modules.FiniteProjectiveGenerator
public import EFiniteCharacterizations.ScalarExtension.FieldExtensionTower
public import EFiniteCharacterizations.GrothendieckGroups.WideGrothendieck
public import EFiniteCharacterizations.Subcategories.ExactAbelianClasses

/-!
# Equivalence of the `τ`-perpendicular category with modules over the reduction algebra

First part of Lemma 2.2 (`lem:perpendicular`, after Jasso and DIRRT): for a two-term
presilting complex `P` with Bongartz completion `T`, `Hom(G, -)` (where `G` is `H⁰(T)`
modulo the trace of `H⁰(P)`) defines an exact equivalence between the
`τ`-perpendicular category `J(P)` and `mod(End(H⁰(T)) / [H⁰(P)])`
(`perpendicular_equivalence_of_bongartz`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped EFiniteCharacterizations.IsWideClass

universe u

namespace EFiniteCharacterizations.TwoTerm

private noncomputable def finiteModuleEquiv {A B : Type u} [Ring A] [Ring B] (e : A ≃+* B) :
    FGModuleCat.{u} B ≌ FGModuleCat.{u} A := by
  let _ : (ModuleCat.isFG.{u} A).IsClosedUnderIsomorphisms :=
    ⟨fun {X Y} f hf ↦ (Module.Finite.equiv_iff f.toLinearEquiv).1 hf⟩
  exact (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).congrFullSubcategory
    (FieldExtension.isFG_restrict_equiv e)

private def wideEndEquiv {C : Type*} [Category* C] [Preadditive C]
    (W : ObjectProperty C) (G : W.FullSubcategory) : End G ≃+* End G.obj where
  toFun f := f.hom
  invFun := W.homMk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R]

/-- The semistable perpendicular category is equivalent to the category of
finite right modules over the Bongartz endomorphism ring modulo the ideal
of maps factoring through the original cokernel. -/
theorem exists_perpendicular_module_equivalence (P Q : TwoTerm R) (hp : P.IsPresilting)
    (hb : Function.Surjective (P.precompose (cokernel Q.differential)))
    (hQ : ∀ X : FGModuleCat.{u} R, Function.Surjective (P.precompose X) → Function.Surjective (Q.precompose X))
    (gen : ∀ X : FGModuleCat.{u} R, Function.Surjective (P.precompose X) →
      IsGeneratedBy (cokernel Q.differential) X) :
    ∃ (I : Ideal (End (cokernel Q.differential))) (_ : I.IsTwoSided),
      (∀ f, f ∈ I ↔ ∃ (n : ℕ) (a : cokernel Q.differential ⟶ ⨁ fun _ : Fin n ↦ cokernel P.differential)
          (b : (⨁ fun _ : Fin n ↦ cokernel P.differential) ⟶ cokernel Q.differential), a ≫ b = f) ∧
      Nonempty (ObjectProperty.FullSubcategory (P.eulerWeight k).IsSemistable ≌
        FGModuleCat.{u} (End (cokernel Q.differential) ⧸ I)ᵐᵒᵖ) := by
  classical
  obtain ⟨G,p,_,hg,covers,lifts,φ,hφ,_,ker⟩ := exists_bongartz_end_quotient k P Q hp hb hQ gen
  let W : ObjectProperty (FGModuleCat.{u} R) := (P.eulerWeight k).IsSemistable
  let _ : Fact (IsWideClass W) := ⟨(P.eulerWeight k).isWideClass_semistable⟩
  let G' : W.FullSubcategory := ⟨G,hg⟩
  let _ : HasFiniteBiproducts W.FullSubcategory := HasFiniteBiproducts.of_hasFiniteProducts
  let _ : Projective G' := ⟨fun {X Y} f q _ ↦ by
    let _ : Epi q.hom := W.ι.map_epi q
    obtain ⟨a,ha⟩ := lifts q.hom X.property Y.property f.hom
    exact ⟨W.homMk a,W.ι.map_injective ha⟩⟩
  have gen' (X : W.FullSubcategory) : ∃ (n : ℕ) (q : (⨁ fun _ : Fin n ↦ G') ⟶ X), Epi q := by
    obtain ⟨n,q,hq⟩ := covers X.obj X.property
    let e := W.ι.mapBiproduct (fun _ : Fin n ↦ G')
    let a := W.ι.preimage (e.hom ≫ q)
    exact ⟨n,a,W.ι.epi_of_epi_map (by change Epi (W.ι.map (W.ι.preimage (e.hom ≫ q))); rw [Functor.map_preimage]; infer_instance)⟩
  let e := wideEndEquiv W G'
  let _ : Module.Finite k (End G) := finiteModuleHom_isFinite k G G
  let _ : IsNoetherianRing (End G)ᵐᵒᵖ := IsNoetherianRing.of_finite k _
  let _ : IsNoetherianRing (End G')ᵐᵒᵖ := isNoetherianRing_of_ringEquiv _ e.symm.op
  exact ⟨RingHom.ker φ,inferInstance,ker,
    ⟨(FiniteProjectiveGenerator.equivalence G' gen').trans
      (finiteModuleEquiv ((φ.quotientKerEquivOfSurjective hφ).trans e.symm).op)⟩⟩

/-- For the Bongartz completion characterized by its torsion class, the
Hom-perpendicular category has the module category of the reduction algebra
as its exact model. -/
theorem perpendicular_equivalence_of_bongartz (P T : TwoTerm R)
    (hp : P.IsPresilting) (ht : T.IsPresilting)
    (bongartz : ∀ M : FGModuleCat.{u} R, IsGeneratedBy (cokernel T.differential) M ↔
      Subsingleton (M ⟶ P.nakayamaKernel k)) :
    ∃ (I : Ideal (End (cokernel T.differential))) (_ : I.IsTwoSided),
      (∀ f, f ∈ I ↔ ∃ (n : ℕ) (a : cokernel T.differential ⟶ ⨁ fun _ : Fin n ↦ cokernel P.differential)
          (b : (⨁ fun _ : Fin n ↦ cokernel P.differential) ⟶ cokernel T.differential), a ≫ b = f) ∧
      Nonempty (ObjectProperty.FullSubcategory
        (fun M : FGModuleCat.{u} R ↦ Subsingleton (cokernel P.differential ⟶ M) ∧
          Subsingleton (M ⟶ P.nakayamaKernel k)) ≌ FGModuleCat.{u} (End (cokernel T.differential) ⧸ I)ᵐᵒᵖ) := by
  let B := cokernel T.differential
  have gen (M : FGModuleCat.{u} R) : IsGeneratedBy B M ↔ Function.Surjective (P.precompose M) :=
    (bongartz M).trans (P.surjective_precompose_iff_no_hom_nakayamaKernel k M).symm
  have hb := (gen B).1 ⟨1,biproduct.π (fun _ : Fin 1 ↦ B) 0,inferInstance⟩
  have hT := (surjective_boundary_iff_surjective_precompose T T).1 ht
  have eq : (P.eulerWeight k).IsSemistable = _ := funext fun M ↦
    propext (P.isSemistable_eulerWeight_iff_perpendicular k hp M)
  obtain ⟨I,hI,hker,he⟩ := exists_perpendicular_module_equivalence k P T hp hb
    (fun M h ↦ T.surjective_precompose_of_generatedBy hT ((gen M).2 h)) (fun M ↦ (gen M).2)
  exact ⟨I,hI,hker,eq ▸ he⟩

end EFiniteCharacterizations.TwoTerm
