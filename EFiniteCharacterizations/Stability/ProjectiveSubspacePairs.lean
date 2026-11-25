module

public import EFiniteCharacterizations.Stability.ProjectiveMatrixSpaces
public import EFiniteCharacterizations.LinearAlgebra.MatrixSubspaceDescent

/-! # Matrix subspace pairs for an integral projective weight -/

@[expose] public section
open CategoryTheory Module Matrix
open scoped ModuleCat.Algebra
universe u

namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]
  {a n m : Type*} [Fintype a] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

private theorem injective_toLin_of_leftInverse {d : ℕ} {Z : Type*} [AddCommGroup Z] [Module k Z] {l : Type*} [Fintype l]
    [DecidableEq l] (w : Basis l k Z) (A : Matrix l (Fin d) k) (L : Matrix (Fin d) l k) (hh : L * A = 1) :
    Function.Injective (Matrix.toLin (Pi.basisFun k (Fin d)) w A) := by
  let D := Pi.basisFun k (Fin d)
  have e := congrArg (Matrix.toLin D D) hh
  rw [Matrix.toLin_mul D w D, Matrix.toLin_one] at e
  exact Function.LeftInverse.injective (g := Matrix.toLin w D L) fun z ↦ LinearMap.congr_fun e z

omit [IsNoetherianRing R] in
/-- Tests depending on the two dimensions can be expressed by matrices over the field. -/
theorem hom_subspace_test_iff_matrix_pairs (P : TwoTerm R) (M : FGModuleCat.{u} R)
    (b : Basis a k (P.source ⟶ P.target))
    (u : Basis n k (P.target ⟶ M)) (v : Basis m k (P.source ⟶ M)) (test : ℕ → ℕ → Prop) :
    (∀ (U : Submodule k (P.target ⟶ M)) (V : Submodule k (P.source ⟶ M)),
      (∀ (p : P.source ⟶ P.target) (f : U), p ≫ f.val ∈ V) → test (Module.finrank k U) (Module.finrank k V)) ↔
      ∀ r s, HasMatrixSubspacePair (fun j ↦ LinearMap.toMatrix u v (Linear.leftComp k M (b j))) r s → test r s := by
  classical
  constructor
  · rintro h r s ⟨X,Y,LX,LY,B,hX,hY,hB⟩
    let bu := Pi.basisFun k (Fin r)
    let bv := Pi.basisFun k (Fin s)
    let x := Matrix.toLin bu u X
    let y := Matrix.toLin bv v Y
    have hx := LinearMap.finrank_range_of_inj (injective_toLin_of_leftInverse k u X LX hX)
    have hy := LinearMap.finrank_range_of_inj (injective_toLin_of_leftInverse k v Y LY hY)
    have hc (j : a) (z : Fin r → k) : b j ≫ x z = y ((Matrix.toLin bu bv (B j)) z) := by
      have e := congrArg (Matrix.toLin bu v) (hB j)
      rw [Matrix.toLin_mul bu u v,Matrix.toLin_toMatrix,Matrix.toLin_mul bu bv v] at e
      exact LinearMap.congr_fun e z
    have hh := h (LinearMap.range x) (LinearMap.range y) (by
      rintro p ⟨_,z,rfl⟩
      rw [← b.sum_repr p,Preadditive.sum_comp]
      exact Submodule.sum_mem _ (fun j _ ↦ by rw [Linear.smul_comp]; exact Submodule.smul_mem _ _ ⟨_,(hc j z).symm⟩))
    simpa only [x,y,bu,bv,hx,hy,Module.finrank_pi,Fintype.card_fin] using hh
  · intro h U V hUV
    have := finiteModuleHom_isFinite k P.target M
    have := finiteModuleHom_isFinite k P.source M
    let bu := Module.finBasis k U
    let bv := Module.finBasis k V
    obtain ⟨l,hl⟩ := U.subtype.exists_leftInverse_of_injective U.ker_subtype
    obtain ⟨l',hl'⟩ := V.subtype.exists_leftInverse_of_injective V.ker_subtype
    let D j := Linear.leftComp k M (b j)
    let B j := ((D j).comp U.subtype).codRestrict V (fun f ↦ hUV (b j) f)
    apply h
    refine ⟨LinearMap.toMatrix bu u U.subtype,LinearMap.toMatrix bv v V.subtype,
      LinearMap.toMatrix u bu l,LinearMap.toMatrix v bv l',fun j ↦ LinearMap.toMatrix bu bv (B j),?_,?_,?_⟩
    · rw [← LinearMap.toMatrix_comp,hl,LinearMap.toMatrix_id]
    · rw [← LinearMap.toMatrix_comp,hl',LinearMap.toMatrix_id]
    · intro j
      rw [← LinearMap.toMatrix_comp,← LinearMap.toMatrix_comp]
      rfl

/-- An integral weight is semistable exactly when the two projective Hom
spaces have the same dimension and their matrix family has no shrunk pair. -/
theorem semistable_iff_matrix_pairs (P : TwoTerm R) (M : FGModuleCat.{u} R)
    (b : Basis a k (P.source ⟶ P.target))
    (u : Basis n k (P.target ⟶ M)) (v : Basis m k (P.source ⟶ M)) :
    (P.eulerWeight k).IsSemistable M ↔ Fintype.card n = Fintype.card m ∧
      ∀ r s, HasMatrixSubspacePair (fun j ↦ LinearMap.toMatrix u v (Linear.leftComp k M (b j))) r s → r ≤ s := by
  rw [P.isSemistable_iff_no_shrunk_subspace k M,homFinrank_eq_finrank,homFinrank_eq_finrank,
    Module.finrank_eq_card_basis u,Module.finrank_eq_card_basis v]
  exact and_congr_right fun _ ↦ P.hom_subspace_test_iff_matrix_pairs k M b u v (· ≤ ·)

end EFiniteCharacterizations.TwoTerm
