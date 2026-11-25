module

public import EFiniteCharacterizations.Geometry.VertexInversionChart

/-! # Regular sections on a vertex determinant chart -/

@[expose] public section

universe u
namespace EFiniteCharacterizations.VertexRepresentation

variable {k R I J : Type u} [Field k] [Ring R] [Algebra k R] [Fintype I] [DecidableEq I]
  [Fintype J] {b : Module.Basis J k R} {d : I → ℕ} {e : I → R} {w : I → ℤ}
  (g : KingPiece b d e w 1)

abbrev chartLocus := {x : VertexRepresentation (k := k) d e // g.val.val x ≠ 0}

/-- Regular functions on the chart identified by their values there. -/
noncomputable def chartRestriction :
    chartFunctions g →ₐ[k] (chartLocus g → k) where
  toFun f x := f.val x.val
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

noncomputable abbrev chartSections := (chartRestriction g).range

noncomputable def restrictCoordinate : coordinateAlgebra b d e →ₐ[k] chartSections g where
  toFun p := ⟨fun x ↦ p.val x.val,⟨⟨p.val,regular_mem_chartFunctions g p⟩,rfl⟩⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

omit [Fintype J] in
theorem isUnit_chart_equation : IsUnit (restrictCoordinate g g.val) := by
  let v : chartSections g := ⟨fun x ↦ (g.val.val x.val)⁻¹,
    ⟨⟨_,inv_mem_chartFunctions g⟩,rfl⟩⟩
  apply isUnit_iff_exists_inv.mpr
  exact ⟨v,Subtype.ext (funext fun x ↦ mul_inv_cancel₀ x.property)⟩

omit [Fintype J] in
/-- The presentation matrix is invertible over the ring of regular chart
sections, before evaluation at any individual representation. -/
theorem isUnit_chart_matrix {N : Type*} [Fintype N] [DecidableEq N]
    (M : Matrix N N (coordinateAlgebra b d e)) (h : M.det = g.val) :
    IsUnit (M.map (restrictCoordinate g)) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  change IsUnit ((restrictCoordinate g).mapMatrix M).det
  rw [← (restrictCoordinate g).map_det,h]
  exact isUnit_chart_equation g

noncomputable def sectionEvaluation (x : chartLocus g) : chartSections g →ₐ[k] k :=
  (Pi.evalAlgHom k (fun _ : chartLocus g ↦ k) x).comp (chartSections g).val

omit [Fintype J] in
theorem sectionMatrix_ext {N : Type*} [Fintype N] [DecidableEq N]
    {A B : Matrix N N (chartSections g)}
    (h : ∀ x, (sectionEvaluation g x).mapMatrix A = (sectionEvaluation g x).mapMatrix B) :
    A = B := by
  ext i j x
  exact congrArg (fun C : Matrix N N k ↦ C i j) (h x)

noncomputable def groundMatrix (r : R) :
    Matrix (Σ i, Fin (d i)) (Σ i, Fin (d i)) (chartSections g) :=
  fun i j ↦ restrictCoordinate g (actionEntry b d e r i j)

theorem groundMatrix_eval (x : chartLocus g) (r : R) :
    (sectionEvaluation g x).mapMatrix (groundMatrix g r) =
      (LinearMap.toMatrixAlgEquiv (totalVertexBasis d)) (x.val.val r) := rfl

/-- The simultaneous algebra action on the fixed vertex space with regular
chart sections as coefficients. Evaluation recovers each representation. -/
noncomputable def chartGroundAction : R →ₐ[k] Matrix (Σ i, Fin (d i)) (Σ i, Fin (d i)) (chartSections g) where
  toFun := groundMatrix g
  map_zero' := sectionMatrix_ext g (fun x ↦ by rw [groundMatrix_eval,map_zero,map_zero,map_zero])
  map_one' := sectionMatrix_ext g (fun x ↦ by rw [groundMatrix_eval,map_one,map_one,map_one])
  map_add' a b := sectionMatrix_ext g (fun x ↦ by simp only [map_add,groundMatrix_eval])
  map_mul' a b := sectionMatrix_ext g (fun x ↦ by simp only [map_mul,groundMatrix_eval])
  commutes' a := sectionMatrix_ext g (fun x ↦ by
    rw [groundMatrix_eval,AlgHom.commutes,AlgEquiv.commutes,AlgHom.commutes])

theorem chartGroundAction_eval (x : chartLocus g) (r : R) :
    (sectionEvaluation g x).mapMatrix (chartGroundAction g r) =
      (LinearMap.toMatrixAlgEquiv (totalVertexBasis d)) (x.val.val r) := rfl

theorem exists_separating_forms_of_section (v : chartSections g)
    (hinv : ∀ (G : BaseChange k d) (x y : chartLocus g), y.val = G⁻¹ • x.val → v.val y = v.val x)
    (x y : chartLocus g) (hxy : v.val x ≠ v.val y) :
    ∃ (m : ℕ), 0 < m ∧ ∃ f q : KingPiece b d e w m,
      q.val.val x.val ≠ 0 ∧ q.val.val y.val ≠ 0 ∧
        f.val.val x.val * q.val.val y.val ≠ f.val.val y.val * q.val.val x.val := by
  obtain ⟨f,hf⟩ := v.property
  have he (z : chartLocus g) : f.val z.val = v.val z := congrFun hf z
  apply exists_separating_forms_of_chartFunction g f.property _ x.property y.property
    (by simpa only [he] using hxy)
  intro G z hz
  have hy : g.val.val (G⁻¹ • z) ≠ 0 := by
    rw [g.property G z,pow_one]
    exact mul_ne_zero (Units.ne_zero _) hz
  exact (he ⟨_,hy⟩).trans ((hinv G ⟨z,hz⟩ ⟨_,hy⟩ rfl).trans (he ⟨z,hz⟩).symm)

theorem not_subsingleton_closedPoints_of_section (v : chartSections g)
    (hinv : ∀ (G : BaseChange k d) (x y : chartLocus g), y.val = G⁻¹ • x.val → v.val y = v.val x)
    (x y : chartLocus g) (hxy : v.val x ≠ v.val y) :
    ¬ Set.Subsingleton {p : ProjectiveSpectrum (kingGrading b d e w) |
      IsClosed ({p} : Set (ProjectiveSpectrum (kingGrading b d e w)))} := by
  obtain ⟨m,hm,f,q,hx,hy,hs⟩ := exists_separating_forms_of_section g v hinv x y hxy
  exact not_subsingleton_closedPoints_of_ratio b d e w x.val y.val hm f q hx hy hs

variable {B : Type u} [Ring B] (f : R →+* B)
    (L : B →+* Matrix (Σ i, Fin (d i)) (Σ i, Fin (d i)) (chartSections g))

noncomputable def sectionActionAt (x : chartLocus g) : B →+* Module.End k (VertexSpace k d) :=
  (LinearMap.toMatrixAlgEquiv (totalVertexBasis d)).symm.toRingEquiv.toRingHom.comp
    (((sectionEvaluation g x).mapMatrix.toRingHom).comp L)

theorem sectionActionAt_ground (hf : L.comp f = (chartGroundAction g).toRingHom)
    (x : chartLocus g) (r : R) : sectionActionAt g L x (f r) = x.val.val r := by
  change (LinearMap.toMatrixAlgEquiv (totalVertexBasis d)).symm ((sectionEvaluation g x).mapMatrix (L (f r))) = _
  rw [show L (f r) = chartGroundAction g r from DFunLike.congr_fun hf r,chartGroundAction_eval,
    AlgEquiv.symm_apply_apply]

omit [Fintype J] in
theorem sectionActionAt_trace (x : chartLocus g) (z : B) :
    LinearMap.trace k _ (sectionActionAt g L x z) = (L z).trace.val x := by
  rw [LinearMap.trace_eq_matrix_trace k (totalVertexBasis d)]
  change ((LinearMap.toMatrixAlgEquiv (totalVertexBasis d))
    ((LinearMap.toMatrixAlgEquiv (totalVertexBasis d)).symm _)).trace = _
  rw [AlgEquiv.apply_symm_apply]
  exact (AddMonoidHom.map_trace (sectionEvaluation g x) (L z)).symm

/-- When the chart action extends across a ring epimorphism, every trace
in the extended algebra is invariant under vertexwise base change. -/
theorem sectionAction_trace_invariant (hepi : IsRingEpimorphism f)
    (hf : L.comp f = (chartGroundAction g).toRingHom) (z : B) (G : BaseChange k d)
    (x y : chartLocus g) (hy : y.val = G⁻¹ • x.val) : (L z).trace.val y = (L z).trace.val x := by
  let E := LinearEquiv.piCongrRight G⁻¹
  let H := (E.conjAlgEquiv k).toRingEquiv.toRingHom.comp (sectionActionAt g L x)
  have ha : sectionActionAt g L y = H := by
    apply hepi
    ext r : 1
    change sectionActionAt g L y (f r) = E.conjAlgEquiv k (sectionActionAt g L x (f r))
    rw [sectionActionAt_ground g f L hf,sectionActionAt_ground g f L hf,hy]
    rfl
  rw [← sectionActionAt_trace g L y,← sectionActionAt_trace g L x,ha]
  exact LinearMap.trace_conj' _ E

end EFiniteCharacterizations.VertexRepresentation
