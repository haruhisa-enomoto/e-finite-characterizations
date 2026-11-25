module

public import EFiniteCharacterizations.Geometry.KingChartSections

/-! # Inversion of vertex differentials on a regular matrix module -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra
universe u
namespace EFiniteCharacterizations.VertexRepresentation.SplitBasicVertices

variable {k R I : Type u} [Field k] [Ring R] [Algebra k R] [Fintype I] [DecidableEq I]
  (P : SplitBasicVertices k R I) {d : I → ℕ} {C : Type u} [CommRing C]
abbrev vertexRows (d : I → ℕ) := Σ i, Fin (d i)
abbrev vertexMatrices (d : I → ℕ) (C : Type u) := Matrix (vertexRows d) (vertexRows d) C
variable (φ : R →+* (vertexMatrices d C))
variable [Module R (vertexMatrices d C)] (act : ∀ (r : R) (m : (vertexMatrices d C)), r • m = φ r * m)

variable (proj : ∀ (i : I) (m : (vertexMatrices d C)) (a b : (vertexRows d)), (φ (P.vertex i) * m) a b =
    if a.1 = i then m a b else 0)
variable {S T : Type u} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
  (s : S → I) (t : T → I)

noncomputable def termMatrixCoordinates :
    ((P.vertexTerm s).val →ₗ[R] (vertexMatrices d C)) ≃ Matrix (Σ j, Fin (d (s j))) (vertexRows d) C where
  toFun f a b := f (P.termGenerator s a.1) ⟨s a.1,a.2⟩ b
  invFun m := LinearMap.lsum R (fun j ↦ vertexIdeal P.vertex (s j)) ℤ fun j ↦
    (LinearMap.toSpanSingleton R (vertexMatrices d C) (fun a b ↦ if h : a.1 = s j then m ⟨j,h ▸ a.2⟩ b else 0)).comp
      (vertexIdeal P.vertex (s j)).subtype
  left_inv f := by
    apply LinearMap.pi_ext
    intro j z
    have hs : P.vertex (s j) • f (P.termGenerator s j) = f (P.termGenerator s j) := by
      rw [← f.map_smul]
      apply congrArg f
      change P.vertex (s j) • Pi.single j _ = Pi.single j _
      change _ = (Pi.single (M := fun j ↦ vertexIdeal P.vertex (s j)) j _)
      refine ((LinearMap.single R (fun j ↦ vertexIdeal P.vertex (s j)) j).map_smul _ _).symm.trans ?_
      exact congrArg (Pi.single j) (Subtype.ext (P.complete.idem _))
    have hm : (fun (a b : (vertexRows d)) ↦ if h : a.1 = s j then
        f (P.termGenerator s j) ⟨s j,h ▸ a.2⟩ b else 0) = f (P.termGenerator s j) := by
      funext a b
      have he := congrFun (congrFun hs a) b
      rw [act] at he
      rw [proj] at he
      split
      next h => exact congrArg (fun v : (vertexRows d) ↦ f (P.termGenerator s j) v b) (Sigma.ext h.symm (by cases a; cases h; rfl))
      next h => simpa [h] using he
    rw [LinearMap.lsum_piSingle]
    change z.val • _ = f (Pi.single j z)
    rw [hm,← f.map_smul]
    apply congrArg f
    change z.val • Pi.single j _ = Pi.single j _
    refine ((LinearMap.single R (fun j ↦ vertexIdeal P.vertex (s j)) j).map_smul _ _).symm.trans ?_
    exact congrArg (Pi.single j) (Subtype.ext (vertexIdeal_mul_idempotent _ _ (P.complete.idem _) z))
  right_inv m := by
    ext ⟨j,l⟩ b
    change (LinearMap.lsum (M := vertexMatrices d C) R (fun j ↦ vertexIdeal P.vertex (s j)) ℤ _ (Pi.single j (vertexGenerator P.vertex (s j)))) _ _ = _
    rw [LinearMap.lsum_piSingle]
    change (P.vertex (s j) • (_ : (vertexMatrices d C))) ⟨s j,l⟩ b = _
    let m' : vertexMatrices d C := fun a b ↦ if h : a.1 = s j then m ⟨j,h ▸ a.2⟩ b else 0
    change (P.vertex (s j) • m') ⟨s j,l⟩ b = _
    rw [act _ m']
    exact (proj (s j) m' ⟨s j,l⟩ b).trans (by simp [m'])

noncomputable def sectionBlock (p : (P.vertexTerm t).val ⟶ (P.vertexTerm s).val) :
    Matrix (Σ a, Fin (d (t a))) (Σ j, Fin (d (s j))) C :=
  fun a j ↦ φ (P.differentialEntries s t p a.1 j.1) ⟨t a.1,a.2⟩ ⟨s j.1,j.2⟩

theorem precomp_termMatrix (p : (P.vertexTerm t).val ⟶ (P.vertexTerm s).val)
    (m : Matrix (Σ j, Fin (d (s j))) (vertexRows d) C) :
    P.termMatrixCoordinates φ act proj t
      (((P.termMatrixCoordinates φ act proj s).symm m).comp p.hom.hom) =
      P.sectionBlock φ s t p * m := by
  ext ⟨a,l⟩ b
  let z : ∀ j, vertexIdeal P.vertex (s j) := p.hom.hom (P.termGenerator t a)
  let v (j : S) : vertexMatrices d C := fun u b ↦ if h : u.1 = s j then m ⟨j,h ▸ u.2⟩ b else 0
  change (LinearMap.lsum R (fun j ↦ vertexIdeal P.vertex (s j)) ℤ
    (fun j ↦ (LinearMap.toSpanSingleton R _ (v j)).comp (vertexIdeal P.vertex (s j)).subtype) z)
    ⟨t a,l⟩ b = _
  rw [LinearMap.lsum_apply,LinearMap.sum_apply,Matrix.mul_apply,Fintype.sum_sigma]
  change (∑ j, (z j).val • v j) ⟨t a,l⟩ b = _
  simp only [Matrix.sum_apply,act,Matrix.mul_apply,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (s j)]
  · apply Finset.sum_congr rfl
    intro u _
    simp [v,sectionBlock,differentialEntries,z]
  · intro i _ hi
    simp [v,hi]
  · simp

include act proj in
/-- A square unit block makes precomposition bijective on the regular matrix module. -/
theorem invertedOn_matrix_of_unit (p : (P.vertexTerm t).val ⟶ (P.vertexTerm s).val)
    (h : (Σ j, Fin (d (s j))) ≃ (Σ a, Fin (d (t a))))
    (hu : IsUnit ((P.sectionBlock φ s t p).submatrix h id)) :
    (P.chartComplex s t p).InvertedOn (ModuleCat.of R (vertexMatrices d C)) := by
  apply ((P.chartComplex s t p).invertedOn_iff_linear _).2
  let U := P.termMatrixCoordinates φ act proj s
  let V := P.termMatrixCoordinates φ act proj t
  let W := Matrix.reindex (α := C) h.symm (Equiv.refl (vertexRows d))
  let B := (P.sectionBlock φ s t p).submatrix h id
  have he (m) : W (V ((U.symm m).comp p.hom.hom)) = B * m := by
    change W (P.termMatrixCoordinates φ act proj t (((P.termMatrixCoordinates φ act proj s).symm m).comp p.hom.hom)) = _
    rw [P.precomp_termMatrix φ act proj s t p]
    rfl
  obtain ⟨u,hu⟩ := hu
  let E := Equiv.ofBijective (fun m : Matrix (Σ j, Fin (d (s j))) (vertexRows d) C ↦ B * m)
    (show Function.Bijective _ from by
      refine ⟨fun x y hxy ↦ ?_,fun y ↦ ⟨(u⁻¹.val) * y,?_⟩⟩
      · have hz := congrArg (fun m ↦ (u⁻¹.val) * m) hxy
        simpa [B,← hu,← Matrix.mul_assoc] using hz
      · simp [B,← hu,← Matrix.mul_assoc])
  have eq : (fun f : (P.vertexTerm s).val →ₗ[R] vertexMatrices d C ↦ f.comp p.hom.hom) =
      V.symm ∘ W.symm ∘ E ∘ U := by
    funext f
    apply V.injective
    apply W.injective
    simpa [E] using he (U f)
  rw [eq]
  exact V.symm.bijective.comp (W.symm.bijective.comp (E.bijective.comp U.bijective))

variable {J : Type u} [Fintype J] (b : Module.Basis J k R)
variable (p : (P.vertexTerm t).val ⟶ (P.vertexTerm s).val)
    (h : (Σ j, Fin (d (s j))) ≃ (Σ a, Fin (d (t a))))

local notation "g" => vertexBlockDeterminant b d P.vertex s t (P.differentialEntries s t p) h

theorem chartGroundAction_vertex (i : I) :
    chartGroundAction g (P.vertex i) =
      Matrix.diagonal (fun a : vertexRows d ↦ if a.1 = i then 1 else 0) := by
  apply sectionMatrix_ext g
  intro x
  rw [chartGroundAction_eval,x.val.property]
  ext ⟨a,l⟩ ⟨j,q⟩
  change (LinearMap.toMatrix (totalVertexBasis d) (totalVertexBasis d) (vertexProjection d i)) _ _ =
    sectionEvaluation g x (Matrix.diagonal _ _ _)
  simp only [LinearMap.toMatrix_apply,totalVertexBasis,Module.Basis.map_apply,Module.Basis.map_repr,
    Pi.basisFun_apply,LinearEquiv.piCurry_apply,vertexProjection,LinearMap.comp_apply,
    LinearMap.single_apply,LinearMap.proj_apply]
  change (Pi.single (M := fun a ↦ Fin (d a) → k) i (fun l ↦ (Pi.single (⟨j,q⟩ : vertexRows d) (1 : k) : vertexRows d → k) ⟨i,l⟩)) a l =
    sectionEvaluation g x (Matrix.diagonal (fun u : vertexRows d ↦ if u.1 = i then 1 else 0) ⟨a,l⟩ ⟨j,q⟩)
  by_cases ha : a = i
  · subst a
    simp [Pi.single_apply,Matrix.diagonal_apply,apply_ite,Sigma.ext_iff]
    split
    next h => exact Sigma.ext_iff.mp h
    next h => exact fun e hq ↦ h (Sigma.ext e hq)
  · simp [Matrix.diagonal_apply,ha]

/-- The regular action on a determinant chart extends to the universal localization. -/
theorem exists_chart_localized_action {B : Type u} [Ring B] (f : R →+* B)
    (hf : IsUniversalLocalization (fun _ : Unit ↦ P.chartComplex s t p) f) :
    ∃ L : B →+* vertexMatrices d (chartSections g), L.comp f = (chartGroundAction g).toRingHom := by
  let φ := (chartGroundAction g).toRingHom
  let := Module.compHom (vertexMatrices d (chartSections g)) φ
  obtain ⟨L,hL,_⟩ := hf.desc _ φ (fun _ ↦ ((P.chartComplex s t p).isIso_induce_iff_regular φ).2 (by
    apply P.invertedOn_matrix_of_unit φ (fun _ _ ↦ rfl) _ s t p h
    · apply isUnit_chart_matrix g
        ((vertexBlockMatrix b d P.vertex s t (P.differentialEntries s t p)).submatrix h id) rfl
    · intro i m a c
      change (chartGroundAction g (P.vertex i) * m) a c = _
      rw [P.chartGroundAction_vertex s t b p h,Matrix.diagonal_mul]
      split <;> simp_all))
  exact ⟨L,hL⟩

variable [IsNoetherianRing R] [Module.Finite k R]

/-- A missing class produces a ratio of semi-invariants that varies on one irreducible component. -/
theorem exists_separating_forms_on_component [IsAlgClosed k] (hn : ¬ IsEFinite R) :
    ∃ (a : ProjectiveClass R) (d : I → ℕ)
      (C : Set (VertexRepresentation (k := k) d P.vertex)),
      C ∈ @irreducibleComponents _ (zariski (d := d) (e := P.vertex) b) ∧
      ∃ x ∈ C, ∃ y ∈ C, ∃ (m : ℕ), 0 < m ∧
      ∃ f q : KingPiece b d P.vertex (P.characterExponents a) m,
        q.val.val x ≠ 0 ∧ q.val.val y ≠ 0 ∧
          f.val.val x * q.val.val y ≠ f.val.val y * q.val.val x := by
  obtain ⟨S,T,_,_,_,_,s,t,p,θ,c,hi⟩ := P.exists_explicit_vertex_chart hn
  obtain ⟨d,h,x,y,⟨C,hC,hCx,hCy⟩,hne,hsx,hsy,hx,hy⟩ := P.exists_stable_points_on_component s t p b hi
  let Q := P.chartComplex s t p
  let chart := vertexBlockDeterminant b d P.vertex s t (P.differentialEntries s t p) h
  obtain ⟨B,_,_,f,hf⟩ := exists_algebra_universalLocalization k (fun _ : PUnit.{u+1} ↦ Q)
  have hu : IsUniversalLocalization (fun _ : Unit ↦ Q) f.toRingHom :=
    ⟨fun _ ↦ hf.inverts PUnit.unit,fun Z _ a ha ↦ hf.desc Z a (fun _ ↦ ha ())⟩
  obtain ⟨L,hL⟩ := P.exists_chart_localized_action s t b p h f.toRingHom hu
  obtain ⟨mX,mY,tX,tY,hX,hY,z,hzX,hzY⟩ := exists_separating_localized_actions k Q f hu
    x.moduleObj y.moduleObj hne hsx ((P.vertexBlockDeterminant_ne_zero_iff s t x b p h).1 hx)
    hsy ((P.vertexBlockDeterminant_ne_zero_iff s t y b p h).1 hy)
  have tr (a : chartLocus chart) (m : Module B a.val.moduleObj) (tower : IsScalarTower k B a.val.moduleObj)
      (hm : ∀ r (v : a.val.moduleObj), f r • v = r • v) :
      (L z).trace.val a = LinearMap.trace k _ (Algebra.lsmul k k a.val.moduleObj z) := by
    let E := a.val.coordinates
    let H := (E.conjAlgEquiv k).toAlgHom.comp (Algebra.lsmul k k a.val.moduleObj (A := B))
    have he : sectionActionAt chart L a = H.toRingHom := by
      apply hu.epic
      ext r : 1
      change sectionActionAt chart L a (f r) = E.conjAlgEquiv k (Algebra.lsmul k k a.val.moduleObj (f r))
      refine (sectionActionAt_ground chart f.toRingHom L hL a r).trans ?_
      apply LinearMap.ext
      intro v
      change a.val.val r v = E (f r • E.symm v)
      rw [hm,a.val.coordinates_smul]
      exact congrArg (a.val.val r) (E.apply_symm_apply v).symm
    rw [← sectionActionAt_trace chart L,he]
    exact LinearMap.trace_conj' _ E
  let w := fun i ↦ (vertexMultiplicity s i : ℤ) - vertexMultiplicity t i
  refine ⟨∑ j, w j • ProjectiveClass.of (P.vertexProjective j),d,C,hC,x,hCx,y,hCy,?_⟩
  rw [P.characterExponents_vertex_sum]
  apply exists_separating_forms_of_section chart (L z).trace
    (sectionAction_trace_invariant chart f.toRingHom L hu.epic hL z) ⟨x,hx⟩ ⟨y,hy⟩
  rw [tr ⟨x,hx⟩ mX tX hX,tr ⟨y,hy⟩ mY tY hY,hzX,hzY]
  exact one_ne_zero

theorem exists_king_counterexample [IsAlgClosed k] (hn : ¬ IsEFinite R) :
    ∃ (a : ProjectiveClass R) (d : I → ℕ), ¬ P.atMostOneKingClosedPoint b d a := by
  obtain ⟨a,d,_,_,x,_,y,_,m,hm,f,q,hx,hy,hs⟩ := P.exists_separating_forms_on_component b hn
  exact ⟨a,d,not_subsingleton_closedPoints_of_ratio b d P.vertex _ x y hm f q hx hy hs⟩

end EFiniteCharacterizations.VertexRepresentation.SplitBasicVertices
