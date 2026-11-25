module

public import EFiniteCharacterizations.Geometry.VertexProjectiveTerms

/-! # Coordinates of precomposition with a vertex-projective differential -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra
universe u
namespace EFiniteCharacterizations.VertexRepresentation.SplitBasicVertices

variable {k R I S T : Type u} [Field k] [Ring R] [Algebra k R] [Fintype I] [DecidableEq I]
    (P : SplitBasicVertices k R I) [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (s : S → I) (t : T → I)

/-- The distinguished generator of a particular summand of the vertex term. -/
noncomputable def termGenerator (j : S) : (P.vertexTerm s).val :=
  Pi.single (M := fun j ↦ vertexIdeal P.vertex (s j)) j (vertexGenerator P.vertex (s j))

theorem vertexTermHomEquiv_apply {M : FGModuleCat.{u} R} (f : (P.vertexTerm s).val ⟶ M) (j : S) :
    ((P.vertexTermHomEquiv s M f j).val : M) = f.hom.hom (P.termGenerator s j) := rfl

/-- A homomorphism out of the vertex term is evaluated by summing the
actions of its argument's coordinates on the images of the generators. -/
theorem vertexTermHom_apply {M : FGModuleCat.{u} R} (f : (P.vertexTerm s).val ⟶ M)
    (z : ∀ j, vertexIdeal P.vertex (s j)) :
    f.hom.hom z = ∑ j, (z j).val • f.hom.hom (P.termGenerator s j) := by
  have hz : z = ∑ j, (z j).val • P.termGenerator s j := by
    change z = ∑ j, (z j).val • Pi.single (M := fun j ↦ vertexIdeal P.vertex (s j)) j (vertexGenerator P.vertex (s j))
    apply funext
    intro a
    rw [Finset.sum_apply,Finset.sum_eq_single a]
    · change z a = (z a).val • Pi.single (M := fun j ↦ vertexIdeal P.vertex (s j)) a (vertexGenerator P.vertex (s a)) a
      rw [Pi.single_eq_same]
      exact Subtype.ext (vertexIdeal_mul_idempotent _ _ (P.complete.idem _) _).symm
    · intro j _ hja
      change (z j).val • Pi.single (M := fun j ↦ vertexIdeal P.vertex (s j)) j (vertexGenerator P.vertex (s j)) a = 0
      rw [Pi.single_eq_of_ne hja.symm,smul_zero]
    · simp
  conv_lhs => rw [hz]
  simp only [map_sum,map_smul]

/-- Coefficients of a differential from t to s, in the order for its
contravariant action on Hom. -/
noncomputable def differentialEntries (p : (P.vertexTerm t).val ⟶ (P.vertexTerm s).val)
    (a : T) (j : S) : R := (p.hom.hom (P.termGenerator t a) j).val

theorem precomp_vertexTerm_apply {M : FGModuleCat.{u} R}
    (p : (P.vertexTerm t).val ⟶ (P.vertexTerm s).val) (f : (P.vertexTerm s).val ⟶ M) (a : T) :
    (P.vertexTermHomEquiv t M (p ≫ f) a).val =
      ∑ j, P.differentialEntries s t p a j • (P.vertexTermHomEquiv s M f j).val :=
  P.vertexTermHom_apply s f (p.hom.hom (P.termGenerator t a))

variable {d : I → ℕ} (ρ : VertexRepresentation (k := k) d P.vertex)

noncomputable def termCoordinates :
    ((P.vertexTerm s).val ⟶ ρ.moduleObj) ≃ₗ[k] ((Σ j, Fin (d (s j))) → k) :=
  P.vertexTermHomEquiv s ρ.moduleObj ≪≫ₗ
    LinearEquiv.piCongrRight (fun j ↦ vertexCoordinateEquiv ρ (s j)) ≪≫ₗ
    (LinearEquiv.piCurry k (fun j (_ : Fin (d (s j))) ↦ k)).symm

private theorem supported_coordinates (i : I) (z : vertexPart (k := k) P.vertex ρ.moduleObj i) :
    ρ.coordinates z.val = Pi.single i (vertexCoordinateEquiv ρ i z) := by
  obtain ⟨m,hm⟩ := z.property
  change P.vertex i • m = z.val at hm
  change ρ.coordinates z.val = Pi.single i ((ρ.coordinates z.val) i)
  rw [← hm,coordinates_smul,ρ.property]
  change Pi.single i ((ρ.coordinates m) i) = Pi.single (M := fun a ↦ Fin (d a) → k) i ((Pi.single (M := fun a ↦ Fin (d a) → k) i ((ρ.coordinates m) i)) i)
  rw [Pi.single_eq_same]

/-- Evaluation of the regular block matrix on a representation computes
precomposition in the coordinates of its projective Hom spaces. -/
theorem evaluated_differential_mulVec {J : Type u} [Fintype J] (b : Module.Basis J k R)
    (p : (P.vertexTerm t).val ⟶ (P.vertexTerm s).val) (f : (P.vertexTerm s).val ⟶ ρ.moduleObj) :
    ((vertexBlockMatrix b d P.vertex s t (P.differentialEntries s t p)).map (fun q ↦ q.val ρ)).mulVec
      (P.termCoordinates s ρ f) = P.termCoordinates t ρ (p ≫ f) := by
  funext ⟨a,l⟩
  let z := P.vertexTermHomEquiv s ρ.moduleObj f
  let r := P.differentialEntries s t p
  change (∑ j : Σ j, Fin (d (s j)), (actionEntry b d P.vertex (r a j.1)
    ⟨t a,l⟩ ⟨s j.1,j.2⟩).val ρ * (vertexCoordinateEquiv ρ (s j.1) (z j.1)) j.2) =
    ρ.coordinates (P.vertexTermHomEquiv t ρ.moduleObj (p ≫ f) a).val (t a) l
  rw [P.precomp_vertexTerm_apply,map_sum,Finset.sum_apply,Finset.sum_apply,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  simp only [actionEntry_vertexActionBlock]
  change (LinearMap.toMatrix' (vertexActionBlock d P.vertex ρ (r a j) (t a) (s j))).mulVec
    (vertexCoordinateEquiv ρ (s j) (z j)) l = ρ.coordinates (r a j • (z j).val) (t a) l
  rw [LinearMap.toMatrix'_mulVec,coordinates_smul,P.supported_coordinates ρ (s j) (z j)]
  rfl

/-- Nonvanishing of the determinant is exactly inversion of the differential. -/
theorem vertexBlockDeterminant_ne_zero_iff {J : Type u} [Fintype J] (b : Module.Basis J k R)
    (p : (P.vertexTerm t).val ⟶ (P.vertexTerm s).val)
    (h : (Σ j, Fin (d (s j))) ≃ (Σ a, Fin (d (t a)))) :
    (vertexBlockDeterminant b d P.vertex s t (P.differentialEntries s t p) h).val.val ρ ≠ 0 ↔
      (TwoTerm.mk (P.vertexTerm t).val (P.vertexTerm s).val (P.vertexTerm t).property
        (P.vertexTerm s).property p).InvertedOn ρ.moduleObj.obj := by
  let M := vertexBlockMatrix b d P.vertex s t (P.differentialEntries s t p)
  let B := (M.map (fun q ↦ q.val ρ)).submatrix h id
  change (M.submatrix h id).det.val ρ ≠ 0 ↔ _
  rw [regular_det_apply]
  change B.det ≠ 0 ↔ _
  rw [← isUnit_iff_ne_zero,← LinearMap.det_toLin',← LinearMap.isUnit_iff_isUnit_det,Module.End.isUnit_iff]
  let U := (P.termCoordinates s ρ).toEquiv
  let V := (P.termCoordinates t ρ).toEquiv.trans (Equiv.arrowCongr h.symm (Equiv.refl k))
  let C := fun f : (P.vertexTerm s).val ⟶ ρ.moduleObj ↦ p ≫ f
  have he : (B.toLin' : _ → _) = V ∘ C ∘ U.symm := by
    funext v
    have hz := P.evaluated_differential_mulVec s t ρ b p (U.symm v)
    change (M.map (fun q ↦ q.val ρ)).mulVec (U (U.symm v)) = _ at hz
    rw [U.apply_symm_apply] at hz
    exact funext fun i ↦ congrFun hz (h i)
  rw [he,Equiv.comp_bijective,Equiv.bijective_comp]
  let E : ((P.vertexTerm s).val ⟶ ρ.moduleObj) ≃ _ := InducedCategory.homEquiv
  let F : ((P.vertexTerm t).val ⟶ ρ.moduleObj) ≃ _ := InducedCategory.homEquiv
  change Function.Bijective C ↔ Function.Bijective (F ∘ C ∘ E.symm)
  rw [Equiv.comp_bijective,Equiv.bijective_comp]

end EFiniteCharacterizations.VertexRepresentation.SplitBasicVertices
