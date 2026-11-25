module

public import EFiniteCharacterizations.ScalarExtension.FieldExtensionTower
public import EFiniteCharacterizations.ScalarExtension.AlgebraicStability
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The geometric stable constituents of a ground stable module -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

private theorem stable_of_equivalence {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (E : C ≌ D) {θ : Weight C} {η : Weight D} (he : ∀ X, θ.eval X = η.eval (E.functor.obj X))
    {X : C} (hs : η.IsStable (E.functor.obj X)) : θ.IsStable X := by
  refine ⟨fun hz ↦ hs.1 (E.functor.map_isZero hz),(he X).trans hs.2.1,?_⟩
  intro U i _ hU hi
  rw [he]
  apply hs.2.2 (E.functor.map i)
  · exact fun hz ↦ hU ((E.inverse.map_isZero hz).of_iso (E.unitIso.app U))
  · exact fun h ↦ hi (isIso_of_reflects_iso i E.functor)

/-- Two modules over the extended algebra are Galois conjugate if an additive
bijection intertwines the algebra action and twists the extension scalars by one
ground-field automorphism. -/
def GaloisConjugate (k L R : Type u) [Field k] [Field L] [Algebra k L] [Ring R] [Algebra k R]
    (X Y : FGModuleCat.{u} (ExtendedAlgebra k L R)) : Prop :=
  ∃ (σ : Gal(L/k)) (v : X ≃+ Y), ∀ (c : L) (r : R) (x : X),
    v ((c ⊗ₜ[k] r : ExtendedAlgebra k L R) • x) = (σ c ⊗ₜ[k] r : ExtendedAlgebra k L R) • v x

section Conjugacy

variable {k L R : Type u} [Field k] [Field L] [Algebra k L] [Ring R] [Algebra k R]
  {X Y Z : FGModuleCat.{u} (ExtendedAlgebra k L R)}

theorem GaloisConjugate.refl (X : FGModuleCat.{u} (ExtendedAlgebra k L R)) : GaloisConjugate k L R X X :=
  ⟨AlgEquiv.refl,(AddEquiv.refl X),fun _ _ _ ↦ rfl⟩

theorem GaloisConjugate.symm (h : GaloisConjugate k L R X Y) : GaloisConjugate k L R Y X := by
  obtain ⟨σ,v,hv⟩ := h
  refine ⟨σ.symm,v.symm,fun c r y ↦ v.injective ?_⟩
  rw [v.apply_symm_apply,hv,σ.apply_symm_apply,v.apply_symm_apply]

theorem GaloisConjugate.trans (h : GaloisConjugate k L R X Y) (h' : GaloisConjugate k L R Y Z) :
    GaloisConjugate k L R X Z := by
  obtain ⟨σ,v,hv⟩ := h
  obtain ⟨τ,w,hw⟩ := h'
  exact ⟨σ.trans τ,v.trans w,fun c r x ↦ (congrArg w (hv c r x)).trans (hw _ _ _)⟩

end Conjugacy

section Tower

variable (k K L R : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [Ring R] [Algebra k R] [Module.Finite k R]
local notation "RK" => ExtendedAlgebra k K R
local notation "RL" => ExtendedAlgebra k L R
local notation "T" => ExtendedAlgebra K L RK

omit [Module.Finite k R] in
private theorem homFinrank_tower (X Y : FGModuleCat.{u} T) :
    let E := towerEquivalence k K L R
    homFinrank L (E.functor.obj X) (E.functor.obj Y) = homFinrank L X Y := by
  let E := towerEquivalence k K L R
  let _ : E.functor.Additive := inferInstanceAs (restrictAlgEquivalence (towerAlgebraEquiv k K L R)).functor.Additive
  let _ : E.functor.Linear L := inferInstanceAs ((restrictAlgEquivalence (towerAlgebraEquiv k K L R)).functor.Linear L)
  let v := LinearEquiv.ofBijective (E.functor.mapLinearMap L (X := X) (Y := Y))
    ⟨E.functor.map_injective,E.functor.map_surjective⟩
  simpa only [homFinrank_eq_finrank] using v.finrank_eq.symm

variable [IsNoetherianRing (ExtendedAlgebra k L R)] [IsNoetherianRing (ExtendedAlgebra K L (ExtendedAlgebra k K R))]

/-- The stability tests for the direct and the iterated scalar extension of the
same projective weight agree under the canonical equivalence. -/
theorem isStable_tower_iff (P : TwoTerm R) (X : FGModuleCat.{u} T) :
    let E := towerEquivalence k K L R
    ((extendTwoTerm k L R P).eulerWeight L).IsStable (E.functor.obj X) ↔
      ((extendTwoTerm K L RK (extendTwoTerm k K R P)).eulerWeight L).IsStable X := by
  let E := towerEquivalence k K L R
  let θ := (extendTwoTerm K L RK (extendTwoTerm k K R P)).eulerWeight L
  let η := (extendTwoTerm k L R P).eulerWeight L
  have hh (Q : FGModuleCat.{u} R) (Y : FGModuleCat.{u} T) :
      homFinrank L (extendObj K L RK (extendObj k K R Q)) Y =
      homFinrank L (extendObj k L R Q) (E.functor.obj Y) := by
    rw [← homFinrank_tower k K L R _ Y,homFinrank_eq_finrank,homFinrank_eq_finrank]
    exact (Linear.homCongr L (towerExtendIso k K L R Q).symm (Iso.refl _)).finrank_eq
  have he (Y : FGModuleCat.{u} T) : θ.eval Y = η.eval (E.functor.obj Y) := by
    simp only [θ,η,TwoTerm.eulerWeight_eval,extendTwoTerm,hh]
  refine ⟨stable_of_equivalence E he, fun hs ↦ ?_⟩
  apply stable_of_equivalence E.symm (θ := η) (η := θ)
  · intro Y
    exact (η.eval_eq_of_isIso (E.counitIso.app Y).hom).symm.trans (he _).symm
  · exact hs.of_iso (E.unitIso.app X)


omit [IsNoetherianRing (ExtendedAlgebra k L R)] [IsNoetherianRing (ExtendedAlgebra K L (ExtendedAlgebra k K R))] in
private theorem conjugate_tower [Module.Finite k K] [Normal k L] {X Y : FGModuleCat.{u} RK}
    (τ : Gal(K/k)) (f : restrictObj k K R X ⟶ restrictObj k K R Y)
    (hτ : IsGaloisHom k K R τ f) (hf : Function.Bijective f.hom.hom) :
    let E := towerEquivalence k K L R
    GaloisConjugate k L R (E.functor.obj (extendObj K L RK X)) (E.functor.obj (extendObj K L RK Y)) := by
  let σ := τ.liftNormal L
  let _ : RingHomInvPair τ.toRingEquiv.toRingHom τ.toRingEquiv.symm.toRingHom := RingHomInvPair.of_ringEquiv τ.toRingEquiv
  let _ : RingHomInvPair τ.toRingEquiv.symm.toRingHom τ.toRingEquiv.toRingHom := RingHomInvPair.of_ringEquiv_symm τ.toRingEquiv
  let a : L ≃ₛₗ[τ.toRingEquiv.toRingHom] L :=
    { σ.toEquiv with
      map_add' := σ.map_add
      map_smul' := fun c x ↦ by
        change σ (c • x) = (τ c) • σ x
        simp only [Algebra.smul_def]
        rw [map_mul,show σ (algebraMap K L c) = _ from τ.liftNormal_commutes L c] }
  let g : X.obj →ₛₗ[τ.toRingEquiv.toRingHom] Y.obj :=
    { toFun := f.hom.hom, map_add' := f.hom.hom.map_add, map_smul' := hτ }
  let v := LinearEquiv.ofBijective g hf
  let t := TensorProduct.congr a v
  let E := towerEquivalence k K L R
  let X' := E.functor.obj (extendObj K L RK X)
  let Y' := E.functor.obj (extendObj K L RK Y)
  let w : X' ≃+ Y' := t.toAddEquiv
  refine ⟨σ,w,fun c r z ↦ ?_⟩
  have act (B : FGModuleCat.{u} RK) (d b : L) (y : B) :
      (d ⊗ₜ[k] r : RL) • (show E.functor.obj (extendObj K L RK B) from b ⊗ₜ[K] y) =
        (d*b) ⊗ₜ[K] ((1 ⊗ₜ[k] r : RK) • y) :=
    extendObj_smul_tmul K L RK B d b _ y
  have onTensor (b : L) (x : X) : w (b ⊗ₜ[K] x) = σ b ⊗ₜ[K] (v x) := rfl
  change L ⊗[K] (X.obj : Type u) at z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro b x
    rw [act,onTensor,onTensor,act,map_mul]
    exact congrArg (fun y : Y ↦ (σ c * σ b) ⊗ₜ[K] y) (f.hom.hom.map_smul r x)
  · intro z z' hz hz'
    let d : RL := c ⊗ₜ[k] r
    let d' : RL := σ c ⊗ₜ[k] r
    exact (congrArg w (smul_add d (show X' from z) (show X' from z'))).trans
      ((w.map_add _ _).trans ((congrArg₂ (· + ·) hz hz').trans
        ((smul_add d' (w z) (w z')).symm.trans (congrArg (d' • ·) (w.map_add _ _).symm))))

end Tower

variable (k L R : Type u) [Field k] [Finite k] [Field L] [Algebra k L] [IsAlgClosed L]
  [Algebra.IsAlgebraic k L] [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsNoetherianRing (ExtendedAlgebra k L R)]

/-- Over the algebraic closure a stable ground module is a direct sum of exactly
as many pairwise nonisomorphic stable modules as its endomorphism degree. Each
geometric constituent has dimension equal to the endolength of the ground module. -/
theorem geometric_stable_constituents (P : TwoTerm R) (S : FGModuleCat.{u} R)
    (hs : (P.eulerWeight k).IsStable S) :
    ∃ B : Fin (homFinrank k S S) → FGModuleCat.{u} (ExtendedAlgebra k L R),
      Nonempty (extendObj k L R S ≅ ⨁ B) ∧ Function.Injective (toSkeleton ∘ B) ∧
      (∀ i j, GaloisConjugate k L R (B i) (B j)) ∧
      ∀ i, ((extendTwoTerm k L R P).eulerWeight L).IsStable (B i) ∧
        Module.finrank L ((B i).obj : Type u) = endolength k S ∧ homFinrank L (B i) (B i) = 1 ∧
        Module.finrank k (S.obj : Type u) = homFinrank k S S * Module.finrank L ((B i).obj : Type u) := by
  classical
  obtain ⟨K,_,_,_,_,deg,B,⟨e⟩,hb,hd,ho,hnum⟩ := exists_stable_splitting_field k P S hs
  let _ : IsAlgClosure k L := ⟨inferInstance,inferInstance⟩
  let emb : K →ₐ[k] L := IsAlgClosed.lift
  let _ : Algebra K L := emb.toRingHom.toAlgebra
  let _ : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq (fun c ↦ (emb.commutes c).symm)
  let _ : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_top (K := k) K
  let _ : Finite K := Module.finite_of_finite k
  let _ := IsNoetherianRing.of_finite K (ExtendedAlgebra k K R)
  let _ := IsNoetherianRing.of_finite L (ExtendedAlgebra K L (ExtendedAlgebra k K R))
  let E := towerEquivalence k K L R
  let C := fun i ↦ extendObj K L (ExtendedAlgebra k K R) (B i)
  obtain ⟨⟨f⟩,hinj,hC⟩ := algebraic_extension_of_split_stable_sum K L (extendTwoTerm k K R P) e hb hd (fun i ↦ (hnum i).1)
  let _ : PreservesBiproduct C E.functor := preservesBiproduct_of_preservesCoproduct E.functor
  rw [← deg]
  refine ⟨fun i ↦ E.functor.obj (C i),⟨(towerExtendIso k K L R S).trans ((E.functor.mapIso f).trans (E.functor.mapBiproduct C))⟩,
    fun i j hij ↦ hinj ?_, ?_, fun i ↦ ?_⟩
  · obtain ⟨v⟩ := toSkeleton_eq_toSkeleton_iff.1 hij
    exact congr_toSkeleton_of_iso (E.functor.preimageIso v)
  · intro i j
    obtain ⟨τ,v,hτ,hv⟩ := ho i j
    exact conjugate_tower k K L R τ v hτ hv
  · have hdim := (finrank_restrictAlgEquivalence (towerAlgebraEquiv k K L R) (C i)).trans (hC i).2.2
    exact ⟨(isStable_tower_iff k K L R P (C i)).2 (hC i).1,hdim.trans (hnum i).2.1.symm,
      (homFinrank_tower k K L R (C i) (C i)).trans (hC i).2.1,((hnum i).2.2).trans (congrArg (Module.finrank k K * ·) hdim.symm)⟩

omit [Finite k] [IsAlgClosed L] [Algebra.IsAlgebraic k L] [IsNoetherianRing R]
    [IsNoetherianRing (ExtendedAlgebra k L R)] in
theorem exists_map_of_conjugate {S : FGModuleCat.{u} R} {X Y : FGModuleCat.{u} (ExtendedAlgebra k L R)}
    (hc : GaloisConjugate k L R X Y) (p : extendObj k L R S ⟶ X) (hp : p ≠ 0) :
    ∃ q : extendObj k L R S ⟶ Y, q ≠ 0 := by
  obtain ⟨σ,v,hv⟩ := hc
  let unit : S →+ extendObj k L R S := (TensorProduct.mk k L (S.obj : Type u) 1).toAddMonoidHom
  let target := (ModuleCat.restrictScalars (algebraInclusion k L R).toRingHom).obj Y.obj
  let f : S.obj →ₗ[R] target :=
    { (v.toAddMonoidHom.comp p.hom.hom.toAddMonoidHom).comp unit with
      map_smul' := fun r x ↦ by
        let t : ExtendedAlgebra k L R := 1 ⊗ₜ[k] r
        have hu : unit (r • x) = t • unit x :=
          (one_mul (1 : L) ▸ extendObj_smul_tmul k L R S 1 1 r x).symm
        change v (p.hom.hom (unit (r • x))) = t • v (p.hom.hom (unit x))
        rw [hu,map_smul]
        simpa only [t,map_one] using hv 1 r (p.hom.hom (unit x)) }
  refine ⟨extendLinearOfRestrict k L R f,fun h ↦ hp (extend_hom_ext k L R fun x ↦ ?_)⟩
  have hzero := congrArg (fun g : extendObj k L R S ⟶ Y ↦ g.hom.hom ((1 : L) ⊗ₜ[k] (x : S.obj))) h
  rw [extendLinearOfRestrict_one_tmul] at hzero
  exact v.injective (hzero.trans v.map_zero.symm)

/-- For each ground stable module, all stable geometric quotients of its extension
form exactly one absolute Galois orbit. -/
theorem geometric_stable_orbit (P : TwoTerm R) (S : FGModuleCat.{u} R)
    (hs : (P.eulerWeight k).IsStable S) :
    ∃ X : FGModuleCat.{u} (ExtendedAlgebra k L R), ((extendTwoTerm k L R P).eulerWeight L).IsStable X ∧
      Nonempty (Retract X (extendObj k L R S)) ∧
      ∀ Y : FGModuleCat.{u} (ExtendedAlgebra k L R), ((extendTwoTerm k L R P).eulerWeight L).IsStable Y →
        ((∃ p : extendObj k L R S ⟶ Y, p ≠ 0) ↔ GaloisConjugate k L R X Y) := by
  classical
  obtain ⟨B,⟨e⟩,_,ho,hb⟩ := geometric_stable_constituents k L R P S hs
  have hn : 0 < homFinrank k S S := (homFinrank_pos_iff k S S).2
    ⟨𝟙 S,fun h ↦ hs.1 ((IsZero.iff_id_eq_zero S).2 h)⟩
  let i : Fin (homFinrank k S S) := ⟨0,hn⟩
  let a : Retract (B i) (extendObj k L R S) := ⟨biproduct.ι B i ≫ e.inv,e.hom ≫ biproduct.π B i,by simp⟩
  have hp : a.r ≠ 0 := fun h ↦ (hb i).1.1 ((IsZero.iff_id_eq_zero _).2 (by rw [← a.retract,h,comp_zero]))
  refine ⟨B i,(hb i).1,⟨a⟩,fun Y hy ↦ ⟨?_,fun hc ↦ exists_map_of_conjugate k L R hc a.r hp⟩⟩
  rintro ⟨p,hp⟩
  have h : ∃ j, biproduct.ι B j ≫ e.inv ≫ p ≠ 0 := by
    by_contra! he
    apply hp
    apply (cancel_epi e.inv).1
    apply biproduct.hom_ext'
    simpa using he
  obtain ⟨j,hj⟩ := h
  let q := biproduct.ι B j ≫ e.inv ≫ p
  have _ := Weight.isIso_of_nonzero (hb j).1 hy q hj
  let d := FGModuleCat.isoToLinearEquiv (asIso q)
  obtain ⟨σ,v,hv⟩ := ho i j
  exact ⟨σ,v.trans d.toAddEquiv,fun c r x ↦ (congrArg d (hv c r x)).trans (d.map_smul _ _)⟩

/-- A geometric stable quotient of an extended ground stable object is a summand. -/
theorem retract_of_geometric_stable_quotient (P : TwoTerm R) {S : FGModuleCat.{u} R}
    (hs : (P.eulerWeight k).IsStable S) {Y : FGModuleCat.{u} (ExtendedAlgebra k L R)}
    (hy : ((extendTwoTerm k L R P).eulerWeight L).IsStable Y) (f : extendObj k L R S ⟶ Y) (hf : f ≠ 0) :
    Nonempty (Retract Y (extendObj k L R S)) := by
  classical
  obtain ⟨B,⟨e⟩,_,_,hb⟩ := geometric_stable_constituents k L R P S hs
  obtain ⟨j,hj⟩ : ∃ j, biproduct.ι B j ≫ e.inv ≫ f ≠ 0 := by
    by_contra! h
    apply hf
    apply (cancel_epi e.inv).1
    apply biproduct.hom_ext'
    simpa using h
  let q := biproduct.ι B j ≫ e.inv ≫ f
  have _ := Weight.isIso_of_nonzero (hb j).1 hy q hj
  exact ⟨⟨inv q ≫ biproduct.ι B j ≫ e.inv,e.hom ≫ biproduct.π B j ≫ q,by simp⟩⟩

omit [Finite k] [IsAlgClosed L] [Algebra.IsAlgebraic k L] [IsNoetherianRing (ExtendedAlgebra k L R)] in
/-- Distinct stable ground modules have disjoint sets of nonzero summands after
any scalar extension. A shared summand would yield a nonzero Hom over the extension
and hence already over the ground field. -/
theorem ground_iso_of_common_constituent (P : TwoTerm R) {S T : FGModuleCat.{u} R}
    (hs : (P.eulerWeight k).IsStable S) (ht : (P.eulerWeight k).IsStable T)
    {Y : FGModuleCat.{u} (ExtendedAlgebra k L R)} (hy : ¬ IsZero Y)
    (a : Retract Y (extendObj k L R S)) (b : Retract Y (extendObj k L R T)) : Nonempty (S ≅ T) := by
  have hne : a.r ≫ b.i ≠ 0 := by
    intro eq
    apply hy ((IsZero.iff_id_eq_zero _).2 ?_)
    simpa using congrArg (fun f ↦ a.i ≫ f ≫ b.r) eq
  have hpos := (homFinrank_pos_iff L _ _).2 ⟨_,hne⟩
  rw [homFinrank_extendObj] at hpos
  obtain ⟨f,hf⟩ := (homFinrank_pos_iff k _ _).1 hpos
  have := Weight.isIso_of_nonzero hs ht f hf
  exact ⟨asIso f⟩

end EFiniteCharacterizations.FieldExtension
