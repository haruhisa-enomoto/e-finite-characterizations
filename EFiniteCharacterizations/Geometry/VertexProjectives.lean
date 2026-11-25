module

public import EFiniteCharacterizations.Geometry.KingChartFunctions

/-! # Projective modules represented by vertex idempotents -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra
universe u
namespace EFiniteCharacterizations.VertexRepresentation

variable {k R I : Type u} [Field k] [Ring R] [Algebra k R]
variable (e : I → R) (i : I)

abbrev vertexIdeal := (LinearMap.toSpanSingleton R R (e i)).range

noncomputable def vertexGenerator : vertexIdeal e i :=
  ⟨e i,1,one_smul R _⟩

theorem vertexIdeal_mul_idempotent (hi : IsIdempotentElem (e i)) (z : vertexIdeal e i) :
    z.val * e i = z.val := by
  obtain ⟨a,ha⟩ := z.property
  change a * e i = z.val at ha
  rw [← ha,mul_assoc,hi]

theorem vertexIdeal_projective (hi : IsIdempotentElem (e i)) :
    Module.Projective R (vertexIdeal e i) :=
  Module.Projective.of_split (vertexIdeal e i).subtype (LinearMap.toSpanSingleton R R (e i)).rangeRestrict
    (LinearMap.ext fun z ↦ Subtype.ext (vertexIdeal_mul_idempotent e i hi z))

/-- Evaluation at the idempotent identifies maps from its principal left
ideal with vectors in the corresponding vertex space. -/
noncomputable def vertexIdealHomEquiv (hi : IsIdempotentElem (e i)) (M : FGModuleCat.{u} R) :
    (vertexIdeal e i →ₗ[R] M) ≃ₗ[k] vertexPart (k := k) e M i where
  toFun f := ⟨f (vertexGenerator e i),f (vertexGenerator e i),by
    change e i • f _ = f _
    rw [← f.map_smul]
    exact congrArg f (Subtype.ext hi)⟩
  invFun z := (LinearMap.toSpanSingleton R M z.val).comp (vertexIdeal e i).subtype
  left_inv f := by
    ext z
    change z.val • f (vertexGenerator e i) = f z
    rw [← f.map_smul]
    exact congrArg f (Subtype.ext (vertexIdeal_mul_idempotent e i hi z))
  right_inv z := by
    apply Subtype.ext
    obtain ⟨m,hm⟩ := z.property
    change e i • (z : M) = z.val
    change e i • m = z.val at hm
    rw [← hm,smul_smul,hi]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [IsNoetherianRing R] [Module.Finite k R] [Fintype I] [DecidableEq I]

namespace SplitBasicVertices

variable (P : SplitBasicVertices k R I)

noncomputable def vertexProjective (j : I) : FiniteProjective R :=
  ⟨FGModuleCat.of R (vertexIdeal P.vertex j),vertexIdeal_projective P.vertex j (P.complete.idem j)⟩

omit [IsNoetherianRing R] [Module.Finite k R] in
theorem vertexProjective_homFinrank (j : I) (M : FGModuleCat.{u} R) :
    homFinrank k (P.vertexProjective j).val M = Module.finrank k (vertexPart (k := k) P.vertex M j) := by
  rw [homFinrank_eq_finrank]
  exact ((finiteModuleHomLinearEquiv k _ M).trans
    (vertexIdealHomEquiv P.vertex j (P.complete.idem j) M)).finrank_eq

/-- Every integral vertex character is realized by a projective class over
the split basic presentation. -/
theorem characterExponents_vertex_sum (w : I → ℤ) :
    P.characterExponents (∑ j, w j • ProjectiveClass.of (P.vertexProjective j)) = w := by
  funext i
  let S := (fromSkeleton _).obj (P.simpleIndex.symm i).val
  change (projectiveClassWeight k (∑ j, w j • ProjectiveClass.of (P.vertexProjective j))).eval S = w i
  simp only [Weight.eval,map_sum,map_zsmul,AddMonoidHom.finsetSum_apply,AddMonoidHom.zsmul_apply,
    projectiveClassWeight_of,zsmul_eq_mul]
  let _ (j : I) := (P.vertexProjective j).property
  have he (j : I) : projectiveHomWeight k (P.vertexProjective j).val (GrothendieckGroup.of S) =
      (if i = j then 1 else 0 : ℤ) := by
    let := (P.vertexProjective j).property
    rw [show projectiveHomWeight k (P.vertexProjective j).val (GrothendieckGroup.of S) =
      (homFinrank k (P.vertexProjective j).val S : ℤ) from projectiveHomWeight_eval k _ _,
      P.vertexProjective_homFinrank]
    simp [S,P.simple_dimension]
  simp [he,mul_ite]

theorem exists_kingWeight_of_separating_chart {J : Type u} [Fintype J]
    (b : Module.Basis J k R) (d : I → ℕ) (w : I → ℤ)
    (g : KingPiece b d P.vertex w 1)
    {v : VertexRepresentation (k := k) d P.vertex → k} (hv : v ∈ chartFunctions g)
    (hinv : ∀ (G : BaseChange k d) x, g.val.val x ≠ 0 → v (G⁻¹ • x) = v x)
    {x y : VertexRepresentation (k := k) d P.vertex} (hx : g.val.val x ≠ 0)
    (hy : g.val.val y ≠ 0) (hxy : v x ≠ v y) :
    ∃ a : ProjectiveClass R, ¬ P.atMostOneKingClosedPoint b d a := by
  refine ⟨∑ j, w j • ProjectiveClass.of (P.vertexProjective j),?_⟩
  unfold atMostOneKingClosedPoint kingModuli
  rw [P.characterExponents_vertex_sum]
  exact not_subsingleton_closedPoints_of_chartFunction g hv hinv hx hy hxy

end SplitBasicVertices

end EFiniteCharacterizations.VertexRepresentation
