module

public import EFiniteCharacterizations.Geometry.KingEvaluationDensity
public import Mathlib.LinearAlgebra.Matrix.Block

/-! # Regular determinants on the fixed vertex representation variety -/

@[expose] public section

universe u
namespace EFiniteCharacterizations.VertexRepresentation

variable {k R I J : Type u} [Field k] [Ring R] [Algebra k R]
    [Fintype I] [DecidableEq I] [Fintype J]
    (b : Module.Basis J k R) (d : I → ℕ) (e : I → R)

noncomputable def totalVertexBasis : Module.Basis (Σ i, Fin (d i)) k (VertexSpace k d) :=
  (Pi.basisFun k _).map (LinearEquiv.piCurry k (fun i (_ : Fin (d i)) ↦ k))

/-- Individual coefficients of the action of any algebra element, as regular
functions in the original affine coordinates. -/
noncomputable def actionEntry (r : R) (a l : Σ i, Fin (d i)) : coordinateAlgebra b d e :=
  ⟨fun ρ ↦ LinearMap.toMatrix (totalVertexBasis d) (totalVertexBasis d) (ρ.val r) a l, by
    let q := ∑ j, MvPolynomial.C (b.repr r j) * MvPolynomial.X (j,a,l)
    refine ⟨q, funext fun ρ ↦ ?_⟩
    have hb (j : J) : affineCoordinates b ρ (j,a,l) =
        LinearMap.toMatrix (totalVertexBasis d) (totalVertexBasis d) (ρ.val (b j)) a l := by
      simp only [affineCoordinates,actionMatrices,LinearMap.toMatrix_apply,vertexBasis,
        Module.Basis.map_apply,Module.Basis.map_repr,LinearEquiv.trans_apply,LinearEquiv.symm_trans_apply,
        LinearEquiv.symm_symm,Algebra.lsmul_apply,coordinates_smul,LinearEquiv.apply_symm_apply,totalVertexBasis]
    change MvPolynomial.aeval (fun j η ↦ affineCoordinates b η j) q ρ = _
    simp only [q,map_sum,map_mul,MvPolynomial.aeval_C,MvPolynomial.aeval_X,Finset.sum_apply,
      Pi.mul_apply,Algebra.algebraMap_eq_smul_one,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one,hb]
    conv_rhs => rw [← b.sum_repr r]
    simp only [map_sum,map_smul,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]⟩

omit [Fintype J] in
/-- The determinant of a square matrix of regular functions is regular,
and its value is the determinant of the evaluated matrix. -/
theorem regular_det_apply {N : Type*} [Fintype N] [DecidableEq N]
    (M : Matrix N N (coordinateAlgebra b d e)) (ρ : VertexRepresentation (k := k) d e) :
    M.det.val ρ = (M.map (fun f ↦ f.val ρ)).det := by
  let ev := (Pi.evalRingHom (fun _ : VertexRepresentation (k := k) d e ↦ k) ρ).comp
    (coordinateAlgebra b d e).val.toRingHom
  exact RingHom.map_det ev M

/-- An array of algebra elements gives a regular matrix on vertex spaces
by taking the specified source and target blocks of their actions. -/
noncomputable def vertexBlockMatrix {S T : Type*} (s : S → I) (t : T → I) (r : T → S → R) :
    Matrix (Σ i, Fin (d (t i))) (Σ j, Fin (d (s j))) (coordinateAlgebra b d e) :=
  fun i j ↦ actionEntry b d e (r i.1 j.1) ⟨t i.1,i.2⟩ ⟨s j.1,j.2⟩

/-- The linear map from vertex j to vertex i induced by an algebra element. -/
noncomputable def vertexActionBlock (ρ : VertexRepresentation (k := k) d e) (r : R) (i j : I) :
    (Fin (d j) → k) →ₗ[k] (Fin (d i) → k) :=
  (LinearMap.proj i).comp ((ρ.val r).comp (LinearMap.single k _ j))

omit [Fintype I] in
theorem vertexActionBlock_changeBasis (G : BaseChange k d)
    (ρ : VertexRepresentation (k := k) d e) (r : R) (i j : I) :
    vertexActionBlock d e (G • ρ) r i j =
      (G i).toLinearMap.comp ((vertexActionBlock d e ρ r i j).comp (G j).symm.toLinearMap) := by
  apply LinearMap.ext
  intro v
  let F := LinearEquiv.piCongrRight G
  change G i ((ρ.val r (F.symm (Pi.single j v))) i) =
    G i ((ρ.val r (Pi.single j ((G j).symm v))) i)
  suffices F.symm (Pi.single j v) = Pi.single j ((G j).symm v) by rw [this]
  funext a
  by_cases h : a = j
  · subst a; simp [F,LinearEquiv.piCongrRight_symm]
  · simp [F,LinearEquiv.piCongrRight_symm,Pi.single_eq_of_ne h]

theorem actionEntry_vertexActionBlock (ρ : VertexRepresentation (k := k) d e)
    (r : R) (i j : I) (a : Fin (d i)) (l : Fin (d j)) :
    (actionEntry b d e r ⟨i,a⟩ ⟨j,l⟩).val ρ =
      LinearMap.toMatrix' (vertexActionBlock d e ρ r i j) a l := by
  change LinearMap.toMatrix (totalVertexBasis d) (totalVertexBasis d) (ρ.val r) ⟨i,a⟩ ⟨j,l⟩ = _
  simp only [LinearMap.toMatrix_apply,totalVertexBasis,Module.Basis.map_apply,Module.Basis.map_repr,
    Pi.basisFun_apply,LinearEquiv.piCurry_apply,
    LinearMap.toMatrix'_apply,vertexActionBlock,LinearMap.comp_apply,LinearMap.proj_apply,LinearMap.single_apply]
  change (ρ.val r (Sigma.curry (Pi.single ⟨j,l⟩ 1))) i a = _
  suffices (Sigma.curry (Pi.single ⟨j,l⟩ (1 : k)) : VertexSpace k d) =
      Pi.single j (Pi.single l 1) by rw [this]
  funext a h
  by_cases ha : a = j
  · subst a
    simp [Sigma.curry,Pi.single_apply]
  · simp [Sigma.curry,Pi.single_eq_of_ne ha, Pi.single_eq_of_ne (show (⟨a,h⟩ : Σ i, Fin (d i)) ≠ ⟨j,l⟩ from fun he ↦ ha (congrArg Sigma.fst he))]

/-- Determinants multiply across the diagonal blocks even when the vertex
dimensions of the summands differ. -/
theorem det_dependent_blocks {S : Type*} [Fintype S] [DecidableEq S] {n : S → ℕ}
    (M : ∀ s, Matrix (Fin (n s)) (Fin (n s)) k) :
    (Matrix.blockDiagonal' M).det = ∏ s, (M s).det := by
  classical
  let := LinearOrder.lift' (Fintype.equivFin S) (Fintype.equivFin S).injective
  have h : (Matrix.blockDiagonal' M).BlockTriangular Sigma.fst := by
    rintro ⟨a,i⟩ ⟨b,j⟩ hab
    exact Matrix.blockDiagonal'_apply_ne M _ _ (Ne.symm hab.ne)
  rw [h.det_fintype]
  apply Finset.prod_congr rfl
  intro a _
  let E : Fin (n a) ≃ {z : Σ j, Fin (n j) // z.1 = a} :=
    { toFun i := ⟨⟨a,i⟩,rfl⟩
      invFun z := z.property ▸ z.val.2
      left_inv _ := rfl
      right_inv := by rintro ⟨⟨j,i⟩,hj⟩; change j = a at hj; subst j; rfl }
  rw [← Matrix.det_reindex_self E.symm]
  congr 1
  ext i j
  exact Matrix.blockDiagonal'_apply_eq M a i j

section Covariance

variable {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (s : S → I) (t : T → I) (r : T → S → R)

noncomputable def blockBaseMatrix (G : BaseChange k d) :
    Matrix (Σ j, Fin (d (s j))) (Σ j, Fin (d (s j))) k :=
  Matrix.blockDiagonal' (fun j ↦ LinearMap.toMatrix' (G (s j)).toLinearMap)

/-- The two changes of basis on a projective block matrix act by left and
right multiplication. -/
theorem vertexBlockMatrix_covariance (G : BaseChange k d) (ρ : VertexRepresentation (k := k) d e) :
    (vertexBlockMatrix b d e s t r).map (fun f ↦ f.val (G • ρ)) =
      blockBaseMatrix d t G * (vertexBlockMatrix b d e s t r).map (fun f ↦ f.val ρ) *
        blockBaseMatrix d s G⁻¹ := by
  ext ⟨a,i⟩ ⟨l,j⟩
  change (actionEntry b d e (r a l) ⟨t a,i⟩ ⟨s l,j⟩).val (G • ρ) = _
  rw [actionEntry_vertexActionBlock,vertexActionBlock_changeBasis,LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_comp, ← Matrix.mul_assoc]
  simp only [Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma,
    blockBaseMatrix, Matrix.map_apply, vertexBlockMatrix]
  rw [Finset.sum_eq_single l]
  · apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_eq_single a]
    · simp only [Matrix.blockDiagonal'_apply_eq,actionEntry_vertexActionBlock]
      rfl
    · intro z _ hz
      simp [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hz)]
    · simp
  · intro z _ hz
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ hz]
  · simp

/-- Multiplicity of a vertex in an indexed family of vertex spaces. -/
def vertexMultiplicity (s : S → I) (i : I) : ℕ := ∑ j, if s j = i then 1 else 0

omit [DecidableEq S] in
theorem vertexCharacter_multiplicity (G : BaseChange k d) :
    vertexCharacter d (fun i ↦ (vertexMultiplicity s i : ℤ)) G =
      ∏ j, LinearEquiv.det (G (s j)) := by
  change ∏ i, LinearEquiv.det (G i) ^ (vertexMultiplicity s i : ℤ) = _
  simp only [zpow_natCast,vertexMultiplicity,← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  simp [apply_ite]

theorem blockBaseMatrix_det (G : BaseChange k d) :
    (blockBaseMatrix d s G).det = ↑(vertexCharacter d (fun i ↦ (vertexMultiplicity s i : ℤ)) G) := by
  rw [vertexCharacter_multiplicity, blockBaseMatrix, det_dependent_blocks, Units.coe_prod]
  simp [LinearMap.det_toMatrix']

variable (h : (Σ j, Fin (d (s j))) ≃ (Σ i, Fin (d (t i))))

/-- A square projective block determinant is a degree-one semi-invariant of
the difference between source and target vertex multiplicities. -/
noncomputable def vertexBlockDeterminant :
    KingPiece b d e (fun i ↦ (vertexMultiplicity s i : ℤ) - vertexMultiplicity t i) 1 := by
  let M := vertexBlockMatrix b d e s t r
  refine ⟨(M.submatrix h id).det, fun G ρ ↦ ?_⟩
  rw [regular_det_apply,regular_det_apply,pow_one]
  let B := M.map (fun f ↦ f.val ρ)
  let U := blockBaseMatrix d t G⁻¹
  let V := blockBaseMatrix d s G
  change ((M.map (fun f ↦ f.val (G⁻¹ • ρ))).submatrix h id).det = _
  rw [vertexBlockMatrix_covariance,inv_inv]
  change ((U * B * V).submatrix h id).det = _ * (B.submatrix h id).det
  rw [← Matrix.submatrix_mul_equiv (U * B) V h (Equiv.refl _) id,
      ← Matrix.submatrix_mul_equiv U B h h (Equiv.refl _),Matrix.det_mul,Matrix.det_mul,
      Matrix.det_submatrix_equiv_self]
  change U.det * (B.submatrix h id).det * V.det = _
  rw [show U.det = _ from blockBaseMatrix_det d t G⁻¹, show V.det = _ from blockBaseMatrix_det d s G]
  have hχ : vertexCharacter d (fun i ↦ (vertexMultiplicity s i : ℤ) - vertexMultiplicity t i) G =
      vertexCharacter d (fun i ↦ (vertexMultiplicity s i : ℤ)) G *
        (vertexCharacter d (fun i ↦ (vertexMultiplicity t i : ℤ)) G)⁻¹ := by
    simp [vertexCharacter,zpow_sub,Finset.prod_mul_distrib]
  rw [hχ,map_inv,Units.val_mul]
  ring

end Covariance

end EFiniteCharacterizations.VertexRepresentation
