module

public import EFiniteCharacterizations.Stability.StableDeterminant
public import EFiniteCharacterizations.Presentations.GroundEulerWeights
public import EFiniteCharacterizations.ScalarExtension.FieldExtensionInduction
public import Mathlib.CategoryTheory.HomCongr

/-! # Ground projective differentials that invert geometric stable modules -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations

theorem TwoTerm.invertedOn_of_commuting_isos {R : Type u} [Ring R] {P Q : TwoTerm R}
    (s : P.source ≅ Q.source) (t : P.target ≅ Q.target)
    (h : P.differential ≫ t.hom = s.hom ≫ Q.differential)
    {M : ModuleCat.{u} R} (hQ : Q.InvertedOn M) : P.InvertedOn M := by
  let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  let es := Iso.homCongr (U.mapIso s).symm (Iso.refl M)
  let et := Iso.homCongr (U.mapIso t) (Iso.refl M)
  have hw : P.differential.hom ≫ t.hom.hom = s.hom.hom ≫ Q.differential.hom :=
    congrArg (fun z ↦ z.hom) h
  have he : (fun g : P.target.obj ⟶ M ↦ P.differential.hom ≫ g) =
      es ∘ (fun g : Q.target.obj ⟶ M ↦ Q.differential.hom ≫ g) ∘ et := by
    funext g
    change _ = s.hom.hom ≫ (Q.differential.hom ≫ (t.inv.hom ≫ g) ≫ 𝟙 M) ≫ 𝟙 M
    simp only [Category.comp_id, ← Category.assoc, ← hw]
    have ht : t.hom.hom ≫ t.inv.hom = 𝟙 _ := (U.mapIso t).hom_inv_id
    simp only [Category.assoc, ht, Category.id_comp]
  unfold TwoTerm.InvertedOn
  rw [he]
  exact es.bijective.comp (hQ.comp et.bijective)

namespace FieldExtension

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R]

local notation "B" => ExtendedAlgebra k F R

private theorem extend_block_square (P : TwoTerm R) {m : ℕ}
    (p : Fin m → Fin m → (P.source ⟶ P.target)) :
    let D := extend k F R
    let s := D.mapBiproduct (fun _ : Fin m ↦ P.source)
    let t := D.mapBiproduct (fun _ : Fin m ↦ P.target)
    D.map (P.blockDifferentialOnCopies p).differential ≫ t.hom =
      s.hom ≫ ((extendTwoTerm k F R P).blockDifferentialOnCopies
        (fun i j ↦ extendMap k F R (p i j))).differential := by
  intro D s t
  change D.map (biproduct.matrix p) ≫ t.hom = s.hom ≫
    biproduct.matrix (f := D.obj ∘ fun _ : Fin m ↦ P.source)
      (g := D.obj ∘ fun _ : Fin m ↦ P.target) (fun i j ↦ D.map (p i j))
  apply (cancel_epi s.inv).1
  rw [Iso.inv_hom_id_assoc]
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro j
  simp only [s,t,Category.assoc,Functor.mapBiproduct_inv,Functor.mapBiproduct_hom]
  rw [biproduct.ι_desc_assoc]
  erw [biproduct.lift_π]
  change D.map (biproduct.ι _ i) ≫
      (D.map (biproduct.matrix p) ≫ D.map (biproduct.π _ j)) = _
  rw [← D.map_comp, ← D.map_comp]
  simp [D]

/-- A stable geometric module at an extended Euler weight inverts an
induced ground differential of a positive multiple of that projective class. -/
theorem exists_ground_block_invertedOn [Algebra.IsAlgebraic k F] [IsAlgClosed F]
    [IsNoetherianRing (ExtendedAlgebra k F R)] (P : TwoTerm R) (M : FGModuleCat.{u} B)
    (hs : ((extendTwoTerm k F R P).eulerWeight F).IsStable M) :
    ∃ (m : ℕ) (_ : 0 < m) (p : Fin m → Fin m → (P.source ⟶ P.target)),
      ((P.blockDifferentialOnCopies p).induce (algebraInclusion k F R).toRingHom).InvertedOn M.obj := by
  classical
  let Q := extendTwoTerm k F R P
  have := finiteModuleHom_isFinite k P.source P.target
  let b := Module.finBasis k (P.source ⟶ P.target)
  let bF := (Algebra.TensorProduct.basis F b).map (homTensorEquiv k F R P.source P.target)
  have hb i : bF i = extendMap k F R (b i) := by
    change homTensorMap k F R P.source P.target ((Algebra.TensorProduct.basis F b) i) = _
    simp [Algebra.TensorProduct.basis_apply, homTensorMap_tmul]
  obtain ⟨m,hm,x,hx⟩ := Q.exists_ground_inverting_power_of_stable F k M hs bF
  let p i j := ∑ l, x (i,l,j) • b l
  let T := P.blockDifferentialOnCopies p
  refine ⟨m,hm,p,?_⟩
  have hp (i j : Fin m) : extendMap k F R (p i j) =
      ∑ l, algebraMap k F (x (i,l,j)) • bF l := by
    let := isScalarTower_ground_extension_hom k F R (extendObj k F R P.source) (extendObj k F R P.target)
    change extendMapLinear k F R P.source P.target (∑ l, x (i,l,j) • b l) = _
    simp only [map_sum,map_smul,hb]
    exact Finset.sum_congr rfl (fun l _ ↦ (IsScalarTower.algebraMap_smul F (x (i,l,j)) _).symm)
  have hmaps : (fun i j ↦ extendMap k F R (p i j)) =
      (fun i j ↦ ∑ l, algebraMap k F (x (i,l,j)) • bF l) := funext fun i ↦ funext (hp i)
  have he : (Q.blockDifferentialOnCopies
      (fun i j ↦ extendMap k F R (p i j))).InvertedOn M.obj := by
    rw [hmaps]
    exact hx
  apply TwoTerm.invertedOn_of_commuting_isos (Q := extendTwoTerm k F R T)
    (inductionIso k F R T.source) (inductionIso k F R T.target)
    (inductionIso_differential k F R T)
  exact TwoTerm.invertedOn_of_commuting_isos (Q := Q.blockDifferentialOnCopies _)
    ((extend k F R).mapBiproduct (fun _ : Fin m ↦ P.source))
    ((extend k F R).mapBiproduct (fun _ : Fin m ↦ P.target))
    (extend_block_square k F R P p) he

/-- Inducing a block of ground maps scales the extended Euler weight by
the number of copies. -/
theorem eulerWeight_induce_block [IsNoetherianRing (ExtendedAlgebra k F R)] (P : TwoTerm R) {m : ℕ}
    (p : Fin m → Fin m → (P.source ⟶ P.target)) :
    (((P.blockDifferentialOnCopies p).induce (algebraInclusion k F R).toRingHom).eulerWeight F) =
      m • (extendTwoTerm k F R P).eulerWeight F := by
  let T := P.blockDifferentialOnCopies p
  let A := T.induce (algebraInclusion k F R).toRingHom
  let U := extendTwoTerm k F R T
  have h : A.projectiveClass = U.projectiveClass := by
    unfold TwoTerm.projectiveClass
    exact congrArg₂ (· - ·)
      (ProjectiveClass.of_eq_of_iso _ _ (inductionIso k F R T.target))
      (ProjectiveClass.of_eq_of_iso _ _ (inductionIso k F R T.source))
  change A.eulerWeight F = _
  rw [← TwoTerm.projectiveClassWeight_eq_eulerWeight F A, h]
  change projectiveClassWeight F (extendTwoTerm k F R T).projectiveClass = _
  rw [projectiveClass_extendTwoTerm k F R]
  dsimp only [T]
  rw [TwoTerm.projectiveClass_blockDifferentialOnCopies, map_nsmul, map_nsmul,
    ← projectiveClass_extendTwoTerm k F R, TwoTerm.projectiveClassWeight_eq_eulerWeight]

end FieldExtension
end EFiniteCharacterizations
