module

public import EFiniteCharacterizations.Modules.HomDimension
public import EFiniteCharacterizations.LinearAlgebra.RankSeparation
public import Mathlib.LinearAlgebra.StdBasis

/-! # Polynomial matrices for precomposition on finite free modules -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.FreeHom

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]

abbrev freeModule (R : Type u) [Ring R] (a : ℕ) := FGModuleCat.of R (Fin a → R)

variable {ι : Type*} [Fintype ι] (bR : Module.Basis ι k R)

/-- Coordinates for the action of a ground algebra basis on a module of
dimension `d` over a commuting field of scalars. -/
abbrev Variables (ι : Type*) (d : ℕ) := ι × Fin d × Fin d

noncomputable def precomposeMatrix {a b : ℕ} (d : ℕ) (f : freeModule R b ⟶ freeModule R a) :
    Matrix (Fin b × Fin d) (Fin a × Fin d) (MvPolynomial (Variables ι d) k) :=
  fun row col ↦ ∑ t, MvPolynomial.C (bR.repr (f.hom.hom (Pi.single row.1 1) col.1) t) *
    MvPolynomial.X (t,row.2,col.2)

variable {D : Type u} [Field D] [Algebra k D] {X : FGModuleCat.{u} R}
  [Module D (X.obj : Type u)] [SMulCommClass R D (X.obj : Type u)]
  [IsScalarTower k D (X.obj : Type u)] {d : ℕ} (bX : Module.Basis (Fin d) D (X.obj : Type u))

noncomputable def evalAction : MvPolynomial (Variables ι d) k →+* D :=
  MvPolynomial.eval₂Hom (algebraMap k D) (fun t ↦ bX.repr (bR t.1 • bX t.2.2) t.2.1)

noncomputable def coordinates {a : ℕ} :
    (freeModule R a ⟶ X) ≃ (Fin a × Fin d → D) :=
  let e : (freeModule R a ⟶ X) ≃ ((Fin a → R) →ₗ[R] (X.obj : Type u)) :=
    ⟨fun f ↦ f.hom.hom, FGModuleCat.ofHom, fun _ ↦ rfl, fun _ ↦ rfl⟩
  let b := Pi.basisFun R (Fin a)
  (e.trans (b.constr (M' := (X.obj : Type u)) ℕ).symm.toEquiv).trans
    ((Equiv.piCongrRight (fun _ : Fin a ↦ bX.equivFun.toEquiv)).trans (Equiv.curry _ _ _).symm)

omit [SMulCommClass R D (X.obj : Type u)] in
theorem coordinates_apply {a : ℕ} (g : freeModule R a ⟶ X) (u : Fin a × Fin d) :
    coordinates bX g u = bX.repr (g.hom.hom (Pi.single u.1 1)) u.2 := by
  change bX.equivFun (g.hom.hom ((Pi.basisFun R (Fin a)) u.1)) u.2 = _
  rw [Module.Basis.equivFun_apply, Pi.basisFun_apply]

omit [SMulCommClass R D (X.obj : Type u)] in
@[simp] theorem coordinates_zero (a : ℕ) : coordinates bX (0 : freeModule R a ⟶ X) = 0 := by
  ext z
  change bX.equivFun 0 z.2 = 0
  simp

omit [SMulCommClass R D (X.obj : Type u)] in
private theorem action_entry (r : R) (i j : Fin d) :
    bX.repr (r • bX j) i =
      ∑ t, algebraMap k D (bR.repr r t) * bX.repr (bR t • bX j) i := by
  conv_lhs => rw [← bR.sum_repr r, Finset.sum_smul, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro t _
  rw [smul_assoc, ← IsScalarTower.algebraMap_smul D (bR.repr r t), map_smul]
  rfl

private theorem coords_action (r : R) (x : X.obj) (i : Fin d) :
    bX.repr (r • x) i = ∑ j, bX.repr (r • bX j) i * bX.repr x j := by
  conv_lhs => rw [← bX.sum_repr x, Finset.smul_sum, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_comm, map_smul, mul_comm]
  rfl

/-- Evaluation of the polynomial matrix computes the categorical Hom map
in the free generators and the chosen basis of the target. -/
theorem precomposeMatrix_mulVec {a b : ℕ} (f : freeModule R b ⟶ freeModule R a)
    (g : freeModule R a ⟶ X) :
    ((precomposeMatrix bR d f).map (evalAction bR bX)).mulVec (coordinates bX g) =
      coordinates bX (f ≫ g) := by
  classical
  funext ⟨i,j⟩
  let x := f.hom.hom (Pi.single i 1)
  rw [coordinates_apply]
  change (∑ col : Fin a × Fin d, evalAction bR bX ((precomposeMatrix bR d f) (i,j) col) * (coordinates bX g) col) =
    bX.repr (g.hom.hom x) j
  have hg : g.hom.hom x = ∑ p, x p • g.hom.hom (Pi.single p 1) := by
    have he := congrArg g.hom.hom ((Pi.basisFun R (Fin a)).sum_repr x).symm
    simpa [Pi.basisFun_apply] using he
  rw [hg, map_sum, Finsupp.finsetSum_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  rw [coords_action]
  apply Finset.sum_congr rfl
  intro l _
  rw [coordinates_apply]
  congr 1
  rw [action_entry bR bX]
  simp [precomposeMatrix, evalAction, x]

end EFiniteCharacterizations.FreeHom
