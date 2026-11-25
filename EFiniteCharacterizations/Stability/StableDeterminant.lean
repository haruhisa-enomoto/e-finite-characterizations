module

public import EFiniteCharacterizations.Silting.Reduction.Bongartz
public import EFiniteCharacterizations.Stability.ProjectiveMatrixSpaces
public import EFiniteCharacterizations.LinearAlgebra.DeterminantDescent
public import EFiniteCharacterizations.LargeModules.LargePerpendicular

/-! # Projective determinantal witnesses for stable modules -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Matrix
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R]

private theorem finrank_range_of_left_inverse {V : Type*} [AddCommGroup V] [Module k V]
    {n : Type*} [Fintype n] {r : ℕ}
    (e : V ≃ₗ[k] (n → k)) (X : Matrix n (Fin r) k) (L : Matrix (Fin r) n k) (h : L * X = 1) :
    Module.finrank k (LinearMap.range (e.symm.toLinearMap.comp X.mulVecLin)) = r := by
  have hi : Function.Injective X.mulVecLin := by
    intro a b he
    have hh := congrArg L.mulVec he
    change L *ᵥ (X *ᵥ a) = L *ᵥ (X *ᵥ b) at hh
    simpa only [Matrix.mulVec_mulVec,h,Matrix.one_mulVec] using hh
  rw [LinearMap.finrank_range_of_inj (f := e.symm.toLinearMap.comp X.mulVecLin) (e.symm.injective.comp hi),Module.finrank_pi,Fintype.card_fin]

omit [Module.Finite k R] [IsNoetherianRing R] in
theorem hom_subspaces_of_matrix_pair {P : TwoTerm R} {M : FGModuleCat.{u} R}
    {a n m : Type*} [Fintype a] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (b : Module.Basis a k (P.source ⟶ P.target))
    (u : Module.Basis n k (P.target ⟶ M)) (v : Module.Basis m k (P.source ⟶ M))
    (r s : ℕ) (hp : HasMatrixSubspacePair
      (fun j ↦ LinearMap.toMatrix u v (Linear.leftComp k M (b j))) r s) :
    ∃ (U : Submodule k (P.target ⟶ M)) (V : Submodule k (P.source ⟶ M)),
      Module.finrank k U = r ∧ Module.finrank k V = s ∧
      ∀ (p : P.source ⟶ P.target) (f : U), p ≫ f.val ∈ V := by
  obtain ⟨X,Y,LX,LY,B,hX,hY,hB⟩ := hp
  let U := LinearMap.range (u.equivFun.symm.toLinearMap.comp X.mulVecLin)
  let V := LinearMap.range (v.equivFun.symm.toLinearMap.comp Y.mulVecLin)
  have hu : Module.finrank k U = r := finrank_range_of_left_inverse k u.equivFun X LX hX
  have hv : Module.finrank k V = s := finrank_range_of_left_inverse k v.equivFun Y LY hY
  have hmaps (j) (f : U) : b j ≫ f.val ∈ V := by
    obtain ⟨z,hz⟩ := f.property
    refine ⟨(B j).mulVec z,?_⟩
    apply v.equivFun.injective
    change v.equivFun (v.equivFun.symm (Y *ᵥ ((B j) *ᵥ z))) = v.equivFun (b j ≫ f.val)
    rw [v.equivFun.apply_symm_apply,Matrix.mulVec_mulVec,← hB,← Matrix.mulVec_mulVec]
    have hcoord : u.equivFun f.val = X *ᵥ z := by
      rw [← hz]
      exact u.equivFun.apply_symm_apply _
    rw [← hcoord]
    exact LinearMap.toMatrix_mulVec_repr u v _ _
  have hUV (p : P.source ⟶ P.target) (f : U) : p ≫ f.val ∈ V := by
    rw [← b.sum_repr p,Preadditive.sum_comp]
    apply V.sum_mem
    intro j _
    rw [Linear.smul_comp]
    exact V.smul_mem _ (hmaps j f)
  exact ⟨U,V,hu,hv,hUV⟩

private theorem matrix_pairs_of_stable {P : TwoTerm R} {M : FGModuleCat.{u} R}
    (hs : (P.eulerWeight k).IsStable M)
    {a n : Type*} [Fintype a] [Fintype n] [DecidableEq n]
    (b : Module.Basis a k (P.source ⟶ P.target))
    (u : Module.Basis n k (P.target ⟶ M)) (v : Module.Basis n k (P.source ⟶ M))
    (r s : ℕ) (hp : HasMatrixSubspacePair
      (fun j ↦ LinearMap.toMatrix u v (Linear.leftComp k M (b j))) r s) (hr : 0 < r) :
    (r < Fintype.card n → r < s) ∧ (r = Fintype.card n → r ≤ s) := by
  obtain ⟨U,V,hu,hv,hUV⟩ := hom_subspaces_of_matrix_pair k b u v r s hp
  constructor
  · intro hlt
    rw [← hu,← hv]
    apply strict_expansion_of_stable k hs U V _ _ hUV
    · rintro he
      rw [he,finrank_bot] at hu
      omega
    · rintro he
      have htop := Module.finrank_eq_card_basis u
      rw [he,finrank_top,htop] at hu
      omega
  · intro _
    rw [← hu,← hv]
    exact ((P.isSemistable_iff_no_shrunk_subspace k M).1 hs.isSemistable).2 U V hUV

/-- The differential specified by a square array of maps on fixed terms. -/
noncomputable def blockDifferentialOnCopies (P : TwoTerm R) {t : ℕ}
    (p : Fin t → Fin t → (P.source ⟶ P.target)) : TwoTerm R where
  source := ⨁ fun _ : Fin t ↦ P.source
  target := ⨁ fun _ : Fin t ↦ P.target
  projective_source := FGModuleCat.projective_biproduct _ fun _ ↦ P.projective_source
  projective_target := FGModuleCat.projective_biproduct _ fun _ ↦ P.projective_target
  differential := biproduct.matrix (f := fun _ ↦ P.source) (g := fun _ ↦ P.target) p

omit [IsNoetherianRing R] in
@[simp] theorem projectiveClass_blockDifferentialOnCopies (P : TwoTerm R) {t : ℕ}
    (p : Fin t → Fin t → (P.source ⟶ P.target)) :
    (P.blockDifferentialOnCopies p).projectiveClass = t • P.projectiveClass := by
  change ProjectiveClass.of _ - ProjectiveClass.of _ = t • (ProjectiveClass.of _ - ProjectiveClass.of _)
  rw [nsmul_sub]
  exact congrArg₂ (· - ·) (ProjectiveClass.of_copies ⟨P.target,P.projective_target⟩ t)
    (ProjectiveClass.of_copies ⟨P.source,P.projective_source⟩ t)

noncomputable def homCoordinates {X M : FGModuleCat.{u} R} {n : Type*} [Fintype n]
    (b : Module.Basis n k (X ⟶ M)) (t : ℕ) :
    ((⨁ fun _ : Fin t ↦ X) ⟶ M) ≃ (Fin t × n → k) where
  toFun f j := b.equivFun (biproduct.ι (fun _ : Fin t ↦ X) j.1 ≫ f) j.2
  invFun z := biproduct.desc (fun j ↦ b.equivFun.symm (fun i ↦ z (j,i)))
  left_inv f := by apply biproduct.hom_ext'; intro i; simp
  right_inv z := by
    funext j
    dsimp only
    rw [biproduct.ι_desc]
    exact congrFun (b.equivFun.apply_symm_apply _) j.2

omit [Module.Finite k R] [IsNoetherianRing R] in
theorem block_coordinates {P : TwoTerm R} {M : FGModuleCat.{u} R}
    {a n m : Type*} [Fintype a] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] (t : ℕ)
    (b : Module.Basis a k (P.source ⟶ P.target))
    (u : Module.Basis n k (P.target ⟶ M)) (v : Module.Basis m k (P.source ⟶ M))
    (x : Fin t × (a × Fin t) → k) (z : Fin t × n → k) :
    let p i j := ∑ l, x (i,l,j) • b l
    let Q := P.blockDifferentialOnCopies p
    homCoordinates k v t (Q.precompose M ((homCoordinates k u t).symm z)) =
      (blockFamily (fun j ↦ LinearMap.toMatrix u v (Linear.leftComp k M (b j))) x).mulVec z := by
  classical
  intro p Q
  let f j := u.equivFun.symm (fun i ↦ z (j,i))
  funext ⟨i,l⟩
  change v.equivFun (biproduct.ι (fun _ : Fin t ↦ P.source) i ≫ biproduct.matrix p ≫ biproduct.desc f) l = _
  rw [← Category.assoc,biproduct.ι_matrix,biproduct.lift_desc]
  simp only [p, Preadditive.sum_comp,Linear.smul_comp,map_sum,map_smul,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul]
  change (∑ j, ∑ m, x (i,m,j) * v.equivFun (b m ≫ f j) l) =
    ∑ j : Fin t × n, (∑ m, x (i,m,j.1) * LinearMap.toMatrix u v (Linear.leftComp k M (b m)) l j.2) * z j
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm (s := (Finset.univ : Finset n))]
  apply Finset.sum_congr rfl
  intro m _
  have he := LinearMap.toMatrix_mulVec_repr u v (Linear.leftComp k M (b m)) (f j)
  have hz : ((u.repr (f j)) : n → k) = fun h ↦ z (j,h) := u.equivFun.apply_symm_apply _
  rw [hz] at he
  have hh := congrFun he l
  change ∑ h, LinearMap.toMatrix u v (Linear.leftComp k M (b m)) l h * z (j,h) =
    v.equivFun (b m ≫ f j) l at hh
  rw [← hh,Finset.mul_sum]
  simp only [mul_assoc]

omit [Module.Finite k R] [IsNoetherianRing R] in
private theorem invertedOn_block_of_det_ne_zero {P : TwoTerm R} {M : FGModuleCat.{u} R}
    {a n : Type*} [Fintype a] [Fintype n] [DecidableEq n] {t : ℕ}
    (b : Module.Basis a k (P.source ⟶ P.target))
    (u : Module.Basis n k (P.target ⟶ M)) (v : Module.Basis n k (P.source ⟶ M))
    (x : Fin t × (a × Fin t) → k)
    (hx : (blockFamily (fun j ↦ LinearMap.toMatrix u v (Linear.leftComp k M (b j))) x).det ≠ 0) :
    (P.blockDifferentialOnCopies (fun i j ↦ ∑ l, x (i,l,j) • b l)).InvertedOn M.obj := by
  classical
  let D j := LinearMap.toMatrix u v (Linear.leftComp k M (b j))
  let p i j := ∑ l, x (i,l,j) • b l
  let Q := P.blockDifferentialOnCopies p
  change Q.InvertedOn M.obj
  have hbij : Function.Bijective (blockFamily D x).mulVecLin :=
    ⟨Matrix.mulVec_injective_of_det_ne_zero hx,LinearMap.surjective_of_injective
      (Matrix.mulVec_injective_of_det_ne_zero hx)⟩
  have hc : Function.Bijective (Q.precompose M) := by
    have hcomp : (homCoordinates k v t) ∘ (Q.precompose M) ∘ (homCoordinates k u t).symm =
        (blockFamily D x).mulVecLin := funext (block_coordinates k t b u v x)
    erw [← hcomp,Equiv.comp_bijective,Equiv.bijective_comp] at hbij
    exact hbij
  let e (X : FGModuleCat.{u} R) : (X ⟶ M) ≃ (X.obj ⟶ M.obj) := InducedCategory.homEquiv
  exact (e Q.source).bijective.comp (hc.comp (e Q.target).symm.bijective)

/-- Over an algebraically closed field, every module stable at an integral
projective weight inverts a differential on equal multiples of its two terms. -/
theorem exists_inverting_power_of_stable [IsAlgClosed k] (P : TwoTerm R) (M : FGModuleCat.{u} R)
    (hs : (P.eulerWeight k).IsStable M) (t : ℕ) (ht : (homFinrank k P.target M)^2 < t) :
    ∃ p : Fin t → Fin t → (P.source ⟶ P.target), (P.blockDifferentialOnCopies p).InvertedOn M.obj := by
  classical
  have := finiteModuleHom_isFinite k P.source P.target
  have := finiteModuleHom_isFinite k P.target M
  have := finiteModuleHom_isFinite k P.source M
  let b := Module.finBasis k (P.source ⟶ P.target)
  let u := Module.finBasis k (P.target ⟶ M)
  have he := ((P.isSemistable_iff_no_shrunk_subspace k M).1 hs.isSemistable).1
  simp only [homFinrank_eq_finrank] at he ht
  let v := (Module.finBasis k (P.source ⟶ M)).reindex (finCongr he.symm)
  let D j := LinearMap.toMatrix u v (Linear.leftComp k M (b j))
  obtain ⟨x,hx⟩ := exists_invertible_blockFamily (t := Fin t) D (matrix_pairs_of_stable k hs b u v)
    (by simpa using ht)
  exact ⟨_,invertedOn_block_of_det_ne_zero k b u v x hx⟩

set_option maxHeartbeats 800000 in
/-- A geometric stable module inverts a block differential with coefficients
in any algebraic ground field, relative to a prescribed basis of maps. -/
theorem exists_ground_inverting_power_of_stable (K : Type*) [Field K] [Algebra K k]
    [Algebra.IsAlgebraic K k] [IsAlgClosed k] (P : TwoTerm R) (M : FGModuleCat.{u} R)
    (hs : (P.eulerWeight k).IsStable M) {a : Type*} [Fintype a]
    (b : Module.Basis a k (P.source ⟶ P.target)) :
    ∃ (m : ℕ) (_ : 0 < m) (x : Fin m × (a × Fin m) → K),
      (P.blockDifferentialOnCopies (fun i j ↦ ∑ l, algebraMap K k (x (i,l,j)) • b l)).InvertedOn M.obj := by
  classical
  have := finiteModuleHom_isFinite k P.target M
  have := finiteModuleHom_isFinite k P.source M
  let u := Module.finBasis k (P.target ⟶ M)
  have he := ((P.isSemistable_iff_no_shrunk_subspace k M).1 hs.isSemistable).1
  simp only [homFinrank_eq_finrank] at he
  let v := (Module.finBasis k (P.source ⟶ M)).reindex (finCongr he.symm)
  let D j := LinearMap.toMatrix u v (Linear.leftComp k M (b j))
  let t := (Module.finrank k (P.target ⟶ M))^2 + 1
  obtain ⟨z,hz⟩ := exists_invertible_blockFamily (t := Fin t) D (matrix_pairs_of_stable k hs b u v)
    (by simp [t])
  obtain ⟨m,hm,x,hx⟩ := exists_ground_invertible_block K D (t := t) (Nat.zero_lt_succ _) z hz
  exact ⟨m,hm,x,invertedOn_block_of_det_ne_zero k b u v (fun j ↦ algebraMap K k (x j)) hx⟩

end EFiniteCharacterizations.TwoTerm
