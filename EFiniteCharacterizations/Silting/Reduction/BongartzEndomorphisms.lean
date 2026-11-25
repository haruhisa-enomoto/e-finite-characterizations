module

public import EFiniteCharacterizations.Silting.Reduction.PerpendicularGenerator
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The endomorphism quotient of a Bongartz generator -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
universe u
namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R]

private theorem kernel_precompose_of_lifting (P : TwoTerm R) {Y I : FGModuleCat.{u} R}
    (q : Y ⟶ I) (hy : Function.Surjective (P.precompose Y))
    (lift : ∀ f : cokernel P.differential ⟶ I, ∃ a, a ≫ q = f) :
    Function.Surjective (P.precompose (kernel q)) := by
  intro f
  obtain ⟨a,ha⟩ := hy (f ≫ kernel.ι q)
  change P.differential ≫ a = f ≫ kernel.ι q at ha
  have w : P.differential ≫ (a ≫ q) = 0 := by rw [← Category.assoc,ha,Category.assoc,kernel.condition,comp_zero]
  obtain ⟨b,hb⟩ := lift (cokernel.desc _ _ w)
  have eq : (a - cokernel.π P.differential ≫ b) ≫ q = 0 := by
    rw [Preadditive.sub_comp,Category.assoc,hb,cokernel.π_desc,sub_self]
  refine ⟨kernel.lift q _ eq,(cancel_mono (kernel.ι q)).mp ?_⟩
  change (P.differential ≫ kernel.lift q _ eq) ≫ kernel.ι q = _
  rw [Category.assoc,kernel.lift_ι,Preadditive.comp_sub,cokernel.condition_assoc,zero_comp,sub_zero,ha]

include k in
/-- Every map from the Bongartz cokernel to a quotient of copies of the
original cokernel factors through a finite sum of that original cokernel. -/
theorem factor_to_generated_from_bongartz (P Q : TwoTerm R) (hp : P.IsPresilting)
    (hQ : ∀ X : FGModuleCat.{u} R, Function.Surjective (P.precompose X) → Function.Surjective (Q.precompose X))
    {I : FGModuleCat.{u} R} (hI : IsGeneratedBy (cokernel P.differential) I) (f : cokernel Q.differential ⟶ I) :
    ∃ (n : ℕ) (a : cokernel Q.differential ⟶ ⨁ fun _ : Fin n ↦ cokernel P.differential)
      (b : (⨁ fun _ : Fin n ↦ cokernel P.differential) ⟶ I), a ≫ b = f := by
  classical
  let C := cokernel P.differential
  have := finiteModuleHom_isFinite k C I
  let b := Module.finBasis k (C ⟶ I)
  let A := fun _ : Fin (Module.finrank k (C ⟶ I)) ↦ C
  let q : (⨁ A) ⟶ I := biproduct.desc b
  have lift (g : C ⟶ I) : ∃ a : C ⟶ ⨁ A, a ≫ q = g := by
    refine ⟨∑ j, b.repr g j • biproduct.ι A j,?_⟩
    simp [q,Preadditive.sum_comp,Linear.smul_comp,b.sum_repr]
  have epi : Epi q := Abelian.epi_of_cokernel_π_eq_zero q (hI.hom_eq_zero _ (fun g ↦ by
    obtain ⟨a,rfl⟩ := lift g
    rw [Category.assoc,cokernel.condition,comp_zero]))
  have hy := P.surjective_precompose_of_generatedBy
    ((surjective_boundary_iff_surjective_precompose P P).1 hp)
    (show IsGeneratedBy C (⨁ A) from ⟨_,𝟙 _,inferInstance⟩)
  obtain ⟨a,ha⟩ := Q.exists_cokernel_hom_lift (kernel.condition q) (ShortComplex.exact_kernel q)
    (hQ _ (kernel_precompose_of_lifting P q hy lift)) f
  exact ⟨_,a,q,ha⟩

private noncomputable def inducedEnd {B G : FGModuleCat.{u} R} (p : B ⟶ G) [Epi p]
    (desc : ∀ a : End B, ∃ b : End G, p ≫ b = a ≫ p) : End B →+* End G where
  toFun a := (desc a).choose
  map_one' := (cancel_epi p).mp (by rw [(desc 1).choose_spec]; simp)
  map_zero' := (cancel_epi p).mp (by rw [(desc 0).choose_spec]; simp)
  map_add' a b := (cancel_epi p).mp (by
    rw [(desc _).choose_spec,Preadditive.comp_add,(desc a).choose_spec,(desc b).choose_spec,Preadditive.add_comp])
  map_mul' a b := (cancel_epi p).mp (by
    change p ≫ _ = p ≫ (desc b).choose ≫ (desc a).choose
    rw [(desc _).choose_spec,← Category.assoc,(desc b).choose_spec,Category.assoc,(desc a).choose_spec]
    simp [End.mul_def])

/-- The semistable projective generator is the trace quotient of a Bongartz
cokernel. Its endomorphism ring is the quotient by all maps that factor
through the additive closure of the original cokernel. -/
theorem exists_bongartz_end_quotient (P Q : TwoTerm R) (hp : P.IsPresilting)
    (hb : Function.Surjective (P.precompose (cokernel Q.differential)))
    (hQ : ∀ X : FGModuleCat.{u} R, Function.Surjective (P.precompose X) → Function.Surjective (Q.precompose X))
    (gen : ∀ X : FGModuleCat.{u} R, Function.Surjective (P.precompose X) →
      IsGeneratedBy (cokernel Q.differential) X) :
    ∃ (G : FGModuleCat.{u} R) (p : cokernel Q.differential ⟶ G), Epi p ∧ (P.eulerWeight k).IsSemistable G ∧
      (∀ X, (P.eulerWeight k).IsSemistable X → IsGeneratedBy G X) ∧
      (∀ {X Y : FGModuleCat.{u} R} (q : X ⟶ Y) [Epi q], (P.eulerWeight k).IsSemistable X →
        (P.eulerWeight k).IsSemistable Y → ∀ f : G ⟶ Y, ∃ a, a ≫ q = f) ∧
      ∃ φ : End (cokernel Q.differential) →+* End G, Function.Surjective φ ∧
        (∀ f, p ≫ φ f = f ≫ p) ∧
        ∀ f, φ f = 0 ↔ ∃ (n : ℕ) (a : cokernel Q.differential ⟶ ⨁ fun _ : Fin n ↦ cokernel P.differential)
          (b : (⨁ fun _ : Fin n ↦ cokernel P.differential) ⟶ cokernel Q.differential), a ≫ b = f := by
  let B := cokernel Q.differential
  obtain ⟨G,p,hep,hG,hdesc,hproj,honto⟩ := P.exists_semistable_projective_quotient_of_retract k hp Q hb hQ
    (𝟙 B) (𝟙 B) (Category.id_comp _)
  let desc (a : End B) := hdesc hG (a ≫ p)
  let φ := inducedEnd p desc
  have act (a) : p ≫ φ a = a ≫ p := (desc a).choose_spec
  refine ⟨G,p,hep,hG,?_,hproj,φ,?_,act,?_⟩
  · intro X hX
    have hg := gen X ((P.surjective_precompose_iff_no_hom_nakayamaKernel k X).2
      ((P.isSemistable_eulerWeight_iff_perpendicular k hp X).1 hX).2)
    obtain ⟨I,i,_,hi,hkill⟩ := exists_generated_subobject_killing_hom k G X
    have hz : cokernel.π i = 0 := hg.hom_eq_zero _ (fun g ↦ by
      obtain ⟨a,ha⟩ := hdesc hX g
      rw [← ha,Category.assoc,hkill,comp_zero])
    have := Abelian.epi_of_cokernel_π_eq_zero _ hz
    exact hi.of_epi i
  · intro a
    obtain ⟨f,hf⟩ := honto a
    exact ⟨f,(cancel_epi p).mp ((act f).trans hf)⟩
  · intro f
    constructor
    · intro hf
      obtain ⟨I,i,_,hI,hs⟩ := P.exists_semistable_quotient_of_no_hom_nakayamaKernel k hp B
        ((P.surjective_precompose_iff_no_hom_nakayamaKernel k B).1 hb)
      obtain ⟨b,hb⟩ := hdesc hs (cokernel.π i)
      have hz : f ≫ cokernel.π i = 0 := by
        rw [← hb,← Category.assoc,← act,hf,comp_zero,zero_comp]
      obtain ⟨n,a,c,hc⟩ := factor_to_generated_from_bongartz k P Q hp hQ hI (Abelian.monoLift i f hz)
      exact ⟨n,a,c ≫ i,by rw [← Category.assoc,hc,Abelian.monoLift_comp]⟩
    · rintro ⟨n,a,b,rfl⟩
      have hs := ((P.isSemistable_eulerWeight_iff_perpendicular k hp G).1 hG).1
      have hz : b ≫ p = 0 := by
        apply biproduct.hom_ext'
        intro j
        exact hs.elim _ _
      apply (cancel_epi p).mp
      rw [act,Category.assoc,hz,comp_zero,comp_zero]

end EFiniteCharacterizations.TwoTerm
