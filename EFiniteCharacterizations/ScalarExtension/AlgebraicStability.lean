module

public import EFiniteCharacterizations.ScalarExtension.AlgebraicSemistability
public import EFiniteCharacterizations.ScalarExtension.StableSplittingField
public import EFiniteCharacterizations.Presentations.GroundEulerWeights
public import EFiniteCharacterizations.ScalarExtension.FieldExtensionRigidity
public import EFiniteCharacterizations.Presentations.SplitBoundary

/-! # Absolute stability over a finite ground field -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R] [IsNoetherianRing R]

private theorem stable_of_strict_expansion {P : TwoTerm R} {M : FGModuleCat.{u} R}
    (hreg : Retract (FGModuleCat.of R R) P.target) (hn : ¬ IsZero M) (hz : (P.eulerWeight k).eval M = 0)
    (h : ∀ (U : Submodule k (P.target ⟶ M)) (V : Submodule k (P.source ⟶ M)),
      (∀ (p : P.source ⟶ P.target) (f : U), p ≫ f.val ∈ V) →
      0 < Module.finrank k U → Module.finrank k U < homFinrank k P.target M → Module.finrank k U < Module.finrank k V) :
    (P.eulerWeight k).IsStable M := by
  refine ⟨hn,hz,?_⟩
  intro T i hi ht hp
  let U := LinearMap.range (Linear.rightComp k P.target i)
  let V := LinearMap.range (Linear.rightComp k P.source i)
  have hr (X : FGModuleCat.{u} R) :
      Module.finrank k (LinearMap.range (Linear.rightComp k X i)) = homFinrank k X T := by
    rw [homFinrank_eq_finrank]
    exact LinearMap.finrank_range_of_inj (fun _ _ eq ↦ (cancel_mono i).1 eq)
  have hu : 0 < Module.finrank k U := by
    rw [show Module.finrank k U = _ from hr P.target,homFinrank_pos_iff]
    have : Nontrivial T := not_subsingleton_iff_nontrivial.mp (ht ∘ (FGModuleCat.isZero_iff_subsingleton T).2)
    obtain ⟨x,hx⟩ := exists_ne (0 : T)
    let g : FGModuleCat.of R R ⟶ T := FGModuleCat.ofHom (LinearMap.toSpanSingleton R T x)
    refine ⟨hreg.r ≫ g,fun eq ↦ hx ?_⟩
    have hg : g = 0 := by simpa using congrArg (hreg.i ≫ ·) eq
    exact (LinearMap.toSpanSingleton_apply_one R T x).symm.trans
      (congrArg (fun z : FGModuleCat.of R R ⟶ T ↦ z.hom.hom 1) hg)
  have := finiteModuleHom_isFinite k P.target M
  have hproper : U ≠ ⊤ := by
    intro eq
    apply hp
    apply (FGModuleCat.isIso_iff_bijective i).2
    refine ⟨(FGModuleCat.mono_iff_injective i).1 hi,fun x ↦ ?_⟩
    let g : FGModuleCat.of R R ⟶ M := FGModuleCat.ofHom (LinearMap.toSpanSingleton R M x)
    obtain ⟨l,hl⟩ := LinearMap.range_eq_top.1 eq (hreg.r ≫ g)
    have hh : (hreg.i ≫ l) ≫ i = g := by
      change l ≫ i = _ at hl
      simp [hl]
    exact ⟨(hreg.i ≫ l).hom.hom 1,(congrArg (fun z : FGModuleCat.of R R ⟶ M ↦ z.hom.hom 1) hh).trans
      (LinearMap.toSpanSingleton_apply_one R M x)⟩
  have hlt := h U V (fun p ⟨_,g,hg⟩ ↦ ⟨p ≫ g,by change (p ≫ g) ≫ i = _; rw [Category.assoc]; exact congrArg (p ≫ ·) hg⟩)
    hu ((Submodule.finrank_lt hproper).trans_eq (homFinrank_eq_finrank k _ _).symm)
  change Module.finrank k (LinearMap.range _) < Module.finrank k (LinearMap.range _) at hlt
  rw [hr,hr] at hlt
  rw [P.eulerWeight_eval k]
  omega

namespace FieldExtension

variable (F : Type u) [Field F] [Algebra k F] [IsNoetherianRing (ExtendedAlgebra k F R)]

/-- Over a finite extension of finite fields a stable module with scalar
endomorphisms remains stable. -/
theorem isStable_extendObj_of_end_dimension_one [Finite k] [Module.Finite k F]
    (P : TwoTerm R) {M : FGModuleCat.{u} R} (hs : (P.eulerWeight k).IsStable M) (h1 : homFinrank k M M = 1) :
    ((extendTwoTerm k F R P).eulerWeight F).IsStable (extendObj k F R M) := by
  let _ : Finite F := Module.finite_of_finite k
  obtain ⟨n,B,hn,⟨e⟩,hb,_,_,_,hnum⟩ := finite_galois_constituent_dimensions k F R P M hs
  have hd := (hnum ⟨0,hn⟩).2.1
  rw [h1] at hd
  obtain rfl : n = 1 := Nat.eq_one_of_dvd_one ⟨_,hd⟩
  let a : (⨁ B) ≅ B 0 :=
    { hom := biproduct.π B 0
      inv := biproduct.ι B 0
      hom_inv_id := by
        apply biproduct.hom_ext'
        intro j
        obtain rfl := Subsingleton.elim j (0 : Fin 1)
        simp
      inv_hom_id := by simp }
  exact (hb 0).of_iso (e.trans a).symm

/-- Stability of all finite intermediate extensions implies stability over the
algebraic extension. Adding a contractible regular summand makes the projective
Hom spaces detect every proper nonzero submodule. -/
theorem isStable_extendObj_of_finite_models [Algebra.IsAlgebraic k F] (P : TwoTerm R) (M : FGModuleCat.{u} R)
    (hs : (P.eulerWeight k).IsStable M)
    (hall : ∀ (E : IntermediateField k F) [Module.Finite k E], letI := IsNoetherianRing.of_finite E (ExtendedAlgebra k E R)
      ((extendTwoTerm k E R P).eulerWeight E).IsStable (extendObj k E R M)) :
    ((extendTwoTerm k F R P).eulerWeight F).IsStable (extendObj k F R M) := by
  let G : FiniteProjective R := ⟨FGModuleCat.of R R,inferInstance⟩
  let Q := P.directSum (TwoTerm.contractible G)
  have hclass : Q.projectiveClass = P.projectiveClass := by
    rw [show Q.projectiveClass = _ from TwoTerm.projectiveClass_directSum ..]
    simp [TwoTerm.projectiveClass]
  have eqWeight (L : Type u) [Field L] [Algebra k L] [IsNoetherianRing (ExtendedAlgebra k L R)] :
      (extendTwoTerm k L R Q).eulerWeight L = (extendTwoTerm k L R P).eulerWeight L := by
    simp only [← TwoTerm.projectiveClassWeight_eq_eulerWeight,projectiveClass_extendTwoTerm,hclass]
  rw [← eqWeight F]
  have dpos := hs.isBrick.endolength_pos k |>.trans_le (endolength_le_groundFinrank k _)
  have hn : ¬ IsZero (extendObj k F R M) := by
    intro hz
    have he := (dimensionWeight (R := ExtendedAlgebra k F R) F).eval_isZero hz
    rw [dimensionWeight_eval,finrank_extendObj] at he
    omega
  let r : Retract (FGModuleCat.of R R) Q.target := ⟨biprod.inr,biprod.snd,biprod.inr_snd⟩
  obtain ⟨a⟩ := nonempty_extend_regular_iso k F R
  let re : Retract (FGModuleCat.of (ExtendedAlgebra k F R) (ExtendedAlgebra k F R)) (extendObj k F R Q.target) :=
    (show Retract _ _ from ⟨a.inv,a.hom,a.inv_hom_id⟩).trans (r.map (extend k F R))
  apply stable_of_strict_expansion F re hn
  · rw [eqWeight]
    exact (isSemistable_extendObj_of_algebraic k F P M hs.isSemistable).1
  let test (r s : ℕ) := 0 < r → r < homFinrank k Q.target M → r < s
  have strict (L : Type u) [Field L] [Algebra k L] [IsNoetherianRing (ExtendedAlgebra k L R)]
      (hstable : ((extendTwoTerm k L R Q).eulerWeight L).IsStable (extendObj k L R M))
      (U : Submodule L (extendObj k L R Q.target ⟶ extendObj k L R M))
      (V : Submodule L (extendObj k L R Q.source ⟶ extendObj k L R M))
      (huv : ∀ (p : extendObj k L R Q.source ⟶ extendObj k L R Q.target) (f : U), p ≫ f.val ∈ V) :
      test (Module.finrank L U) (Module.finrank L V) := by
    intro hpos hproper
    have h0 : U ≠ ⊥ := by rintro rfl; simp at hpos
    have ht : U ≠ ⊤ := by
      rintro rfl
      rw [finrank_top,← homFinrank_eq_finrank,homFinrank_extendObj] at hproper
      omega
    exact TwoTerm.strict_expansion_of_stable L hstable U V h0 ht huv
  have transfer := hom_subspace_test_of_finite_models k F Q M test (by
    intro E hE
    let _ := IsNoetherianRing.of_finite E (ExtendedAlgebra k E R)
    exact strict E ((eqWeight E).symm ▸ hall E))
  intro U V huv hpos hproper
  apply transfer U V huv hpos
  change Module.finrank F U < homFinrank F (extendObj k F R Q.target) (extendObj k F R M) at hproper
  rwa [homFinrank_extendObj] at hproper

/-- Over a finite field, scalar endomorphisms suffice for stability after
every algebraic extension, in particular after extension to the algebraic closure. -/
theorem isStable_extendObj_of_algebraic_of_end_dimension_one [Finite k] [Algebra.IsAlgebraic k F]
    (P : TwoTerm R) {M : FGModuleCat.{u} R} (hs : (P.eulerWeight k).IsStable M) (h1 : homFinrank k M M = 1) :
    ((extendTwoTerm k F R P).eulerWeight F).IsStable (extendObj k F R M) := by
  apply isStable_extendObj_of_finite_models k F P M hs
  intro E hE
  let _ := IsNoetherianRing.of_finite E (ExtendedAlgebra k E R)
  exact isStable_extendObj_of_end_dimension_one k E P hs h1

/-- A stable module over a finite field is geometrically stable exactly when its
endomorphism algebra has ground dimension one. -/
theorem isStable_extendObj_algClosure_iff [Finite k] [IsAlgClosed F] [Algebra.IsAlgebraic k F]
    (P : TwoTerm R) {M : FGModuleCat.{u} R} (hs : (P.eulerWeight k).IsStable M) :
    ((extendTwoTerm k F R P).eulerWeight F).IsStable (extendObj k F R M) ↔ homFinrank k M M = 1 := by
  refine ⟨fun ha ↦ ?_,isStable_extendObj_of_algebraic_of_end_dimension_one k F P hs⟩
  let B := extendObj k F R M
  let D := Module.End (ExtendedAlgebra k F R) (B.obj : Type u)
  let _ : DivisionRing D := ha.isBrick.endomorphismDivisionRing F
  let _ : Module.Finite F (B.obj : Type u) := Module.Finite.trans (ExtendedAlgebra k F R) _
  let v := LinearEquiv.ofBijective (Algebra.linearMap F D) (show Function.Bijective (algebraMap F D) from IsAlgClosed.algebraMap_bijective_of_isIntegral)
  rw [← homFinrank_extendObj k F R,homFinrank_eq_finrank,(finiteModuleHomLinearEquiv F B B).finrank_eq]
  exact v.finrank_eq.symm.trans (Module.finrank_self F)

/-- Over every algebraic extension, a direct sum of distinct stable modules with
scalar endomorphisms retains its decomposition, stability and multiplicities. -/
theorem algebraic_extension_of_split_stable_sum [Finite k] [Algebra.IsAlgebraic k F]
    (P : TwoTerm R) {n : ℕ} {B : Fin n → FGModuleCat.{u} R} {X : FGModuleCat.{u} R}
    (e : X ≅ ⨁ B) (hb : ∀ i, (P.eulerWeight k).IsStable (B i))
    (hd : Function.Injective (toSkeleton ∘ B)) (h1 : ∀ i, homFinrank k (B i) (B i) = 1) :
    let C := fun i ↦ extendObj k F R (B i)
    Nonempty (extendObj k F R X ≅ ⨁ C) ∧ Function.Injective (toSkeleton ∘ C) ∧
      ∀ i, ((extendTwoTerm k F R P).eulerWeight F).IsStable (C i) ∧ homFinrank F (C i) (C i) = 1 ∧
        Module.finrank F ((C i).obj : Type u) = Module.finrank k ((B i).obj : Type u) := by
  classical
  let G := extend k F R
  let _ : PreservesBiproduct B G := preservesBiproduct_of_preservesCoproduct G
  have stable i := isStable_extendObj_of_algebraic_of_end_dimension_one k F P (hb i) (h1 i)
  refine ⟨⟨(G.mapIso e).trans (G.mapBiproduct B)⟩,?_,fun i ↦ ⟨stable i,
    (homFinrank_extendObj k F R _ _).trans (h1 i),finrank_extendObj k F R _⟩⟩
  intro i j hij
  obtain ⟨f⟩ := toSkeleton_eq_toSkeleton_iff.1 hij
  have hf : f.hom ≠ 0 := fun hz ↦ (stable i).1 ((IsZero.iff_id_eq_zero _).2 (by rw [← f.hom_inv_id,hz,zero_comp]))
  have hpos := (homFinrank_pos_iff F _ _).2 ⟨f.hom,hf⟩
  change 0 < homFinrank F (extendObj k F R (B i)) (extendObj k F R (B j)) at hpos
  rw [homFinrank_extendObj] at hpos
  obtain ⟨g,hg⟩ := (homFinrank_pos_iff k _ _).1 hpos
  have := Weight.isIso_of_nonzero (hb i) (hb j) g hg
  exact hd (congr_toSkeleton_of_iso (asIso g))

end FieldExtension
end EFiniteCharacterizations
