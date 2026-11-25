module

public import EFiniteCharacterizations.Geometry.KingNumericalSemistability

/-! # Evaluation ideals under splitting of weight-zero extensions -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u
namespace EFiniteCharacterizations.VertexRepresentation

variable {k R I J : Type u} [Field k] [Ring R] [Algebra k R]
    [Fintype I] [DecidableEq I] [Fintype J]
    (b : Module.Basis J k R) {d : I → ℕ} {e : I → R} (w : I → ℤ)

theorem kingEvaluationIdeal_eq_of_iso {ρ η : VertexRepresentation (k := k) d e}
    (i : ρ.moduleObj ≅ η.moduleObj) : kingEvaluationIdeal b w ρ = kingEvaluationIdeal b w η := by
  obtain ⟨G,hG⟩ := (MulAction.mem_orbit_iff).1 ((mem_orbit_iff ρ η).2 ((sameOrbit_iff_iso ρ η).2 ⟨i⟩))
  rw [← hG, kingEvaluationIdeal_smul]

theorem kingEvaluationIdeal_eq_of_equal_values {ρ η : VertexRepresentation (k := k) d e}
    (he : ∀ m (f : KingPiece b d e w m), f.val.val ρ = f.val.val η) :
    kingEvaluationIdeal b w ρ = kingEvaluationIdeal b w η := by
  apply HomogeneousIdeal.toIdeal_injective
  ext a
  let D := kingGrading b d e w
  rw [(kingEvaluationIdeal b w ρ).isHomogeneous.mem_iff D,
      (kingEvaluationIdeal b w η).isHomogeneous.mem_iff D]
  apply forall_congr'
  intro i
  obtain ⟨f,hf⟩ := (DirectSum.decompose D a i).property
  rw [← hf]
  change kingEvaluation b w ρ (DirectSum.of (KingPiece b d e w) i f) = 0 ↔
    kingEvaluation b w η (DirectSum.of (KingPiece b d e w) i f) = 0
  rw [kingEvaluation_of,kingEvaluation_of,he]

variable {P Q : I → Type u} [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    [∀ i, AddCommGroup (Q i)] [∀ i, Module k (Q i)] [∀ i, Module.Finite k (P i)]
    [∀ i, Module.Finite k (Q i)] (E : ∀ i, (Fin (d i) → k) ≃ₗ[k] (P i × Q i))
    (ρ : VertexRepresentation (k := k) d e)

/-- Splitting a weight-zero invariant summand preserves the entire evaluation ideal. -/
theorem kingEvaluationIdeal_blockCurve_zero [Infinite k]
    (h : PreservesFirstSummand (splitAction E ρ)) (hw : ∑ i, (Module.finrank k (P i) : ℤ) * w i = 0) :
    kingEvaluationIdeal b w (blockCurve E ρ h 0) = kingEvaluationIdeal b w ρ := by
  apply kingEvaluationIdeal_eq_of_equal_values
  exact eval_special_of_character_one b w ρ (blockCurve_polynomial b E ρ h) (blockBaseChange E)
    (blockCurve_at_unit E ρ h) (fun t ↦ by rw [blockBaseChange_character,hw,zpow_zero])

/-- A polynomial degeneration along a one-parameter subgroup of character one. -/
def WeightZeroDegeneration (x y : VertexRepresentation (k := k) d e) : Prop :=
  ∃ (c : k → VertexRepresentation (k := k) d e) (G : kˣ →* BaseChange k d),
    IsPolynomialCurve b c ∧ (∀ t : kˣ, c t = G t • x) ∧
      (∀ t, vertexCharacter d w (G t) = 1) ∧ c 0 = y

theorem WeightZeroDegeneration.evaluation_eq [Infinite k] {x y : VertexRepresentation (k := k) d e}
    (h : WeightZeroDegeneration b w x y) : kingEvaluationIdeal b w y = kingEvaluationIdeal b w x := by
  obtain ⟨c,G,hc,hG,hw,rfl⟩ := h
  apply kingEvaluationIdeal_eq_of_equal_values
  exact eval_special_of_character_one b w x hc G hG hw

namespace SplitBasicVertices

variable [Module.Finite k R] [IsNoetherianRing R] (A : SplitBasicVertices k R I)
    (S : ShortComplex (FGModuleCat.{u} R)) (hs : S.ShortExact)
    (η : VertexRepresentation (k := k) d A.vertex) (eM : S.X₂ ≅ η.moduleObj)

include hs
private theorem exists_vertex_split (i : I) :
    ∃ H : vertexPart (k := k) A.vertex S.X₂ i ≃ₗ[k]
        vertexPart (k := k) A.vertex S.X₁ i × vertexPart (k := k) A.vertex S.X₃ i,
      (∀ x, H (partMap S.f i x) = (x,0)) ∧
      ∀ y, (H y).2 = partMap S.g i y := by
  let a := partMap (k := k) (e := A.vertex) S.f i
  let c := partMap (k := k) (e := A.vertex) S.g i
  obtain ⟨ha,hc,he⟩ := partMap_shortExact (k := k) A.vertex i (A.complete.idem i) S hs
  obtain ⟨l,hl⟩ := a.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr ha)
  have hx : Function.Exact a c := LinearMap.exact_iff.mpr he
  obtain ⟨H,hf,hg⟩ := hx.splitInjectiveEquiv hc ⟨l,hl⟩
  refine ⟨H,fun x ↦ (H.symm_apply_eq.mp ?_).symm, fun y ↦ (LinearMap.congr_fun hg y).symm⟩
  exact (LinearMap.congr_fun hf x).symm

/-- Split the underlying vertex spaces of a short exact sequence. In these
coordinates its injection and surjection are the first inclusion and second projection. -/
theorem exists_vertex_splitting_of_shortExact :
    ∃ H : ∀ i, (Fin (d i) → k) ≃ₗ[k]
        vertexPart (k := k) A.vertex S.X₁ i × vertexPart (k := k) A.vertex S.X₃ i,
      (∀ x : S.X₁, vertexSplitting H (η.coordinates (eM.hom.hom.hom (S.f.hom.hom x))) =
        (VertexRepresentation.decompose (k := k) A.complete S.X₁ x,0)) ∧
      ∀ y : S.X₂, (vertexSplitting H (η.coordinates (eM.hom.hom.hom y))).2 =
        VertexRepresentation.decompose (k := k) A.complete S.X₃ (S.g.hom.hom y) := by
  choose K h₁ h₂ using fun i ↦ exists_vertex_split A S hs i
  let H i := (((vertexCoordinateEquiv η i).symm.trans (partEquiv (e := A.vertex) eM.symm i)).trans (K i))
  let D := VertexRepresentation.decompose (k := k) A.complete
  have hcoord (y : S.X₂) (i : I) :
      H i (η.coordinates (eM.hom.hom.hom y) i) = K i (D S.X₂ y i) := by
    let z := D S.X₂ y i
    have he' : vertexCoordinateEquiv η i (partMap eM.hom i z) = η.coordinates (eM.hom.hom.hom y) i := by
      change η.coordinates (eM.hom.hom.hom (A.vertex i • y)) i = _
      rw [eM.hom.hom.hom.map_smul,coordinates_smul,η.property]
      simp [vertexProjection]
    rw [← he']
    change K i (partEquiv (e := A.vertex) eM.symm i ((vertexCoordinateEquiv η i).symm ((vertexCoordinateEquiv η i) _))) = _
    rw [LinearEquiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    exact (FGModuleCat.isoToLinearEquiv eM).symm_apply_apply z.val
  refine ⟨H,fun x ↦ ?_,fun y ↦ ?_⟩
  · have hx (i : I) : H i (η.coordinates (eM.hom.hom.hom (S.f.hom.hom x)) i) = (D S.X₁ x i,0) := by
      rw [hcoord,← h₁]
      congr 1
      exact Subtype.ext (S.f.hom.hom.map_smul _ _).symm
    exact Prod.ext (funext fun i ↦ congrArg Prod.fst (hx i)) (funext fun i ↦ congrArg Prod.snd (hx i))
  · funext i
    change (H i (η.coordinates (eM.hom.hom.hom y) i)).2 = _
    rw [hcoord,h₂]
    exact Subtype.ext (S.g.hom.hom.map_smul _ _)

include eM in
omit [Fintype J] in
/-- A weight-zero short exact sequence and its split sequence are the
endpoints of a weight-zero degeneration on the fixed vertex spaces. -/
theorem exists_split_point_degeneration [IsArtinianRing R]
    (g : ProjectiveClass R) (hw : (projectiveClassWeight k g).eval S.X₁ = 0) :
    ∃ ξ : VertexRepresentation (k := k) d A.vertex,
      Nonempty (ξ.moduleObj ≅ S.X₁ ⊞ S.X₃) ∧
      WeightZeroDegeneration b (A.characterExponents g) η ξ := by
  classical
  let D := VertexRepresentation.decompose (k := k) A.complete
  obtain ⟨H,hf,hg⟩ := exists_vertex_splitting_of_shortExact A S hs η eM
  let F := vertexSplitting H
  let c := (FGModuleCat.isoToLinearEquiv eM).restrictScalars k
  let T := (c.trans η.coordinates).trans F
  let α := splitAction H η
  have act (r : R) (y : S.X₂) : α r (T y) = T (r • y) := by
    change F (η.val r (F.symm (F _))) = F (η.coordinates (eM.hom.hom.hom (r • y)))
    rw [F.symm_apply_apply,eM.hom.hom.hom.map_smul,coordinates_smul]
    rfl
  have first (r : R) (x : S.X₁) : α r (D S.X₁ x,0) = (D S.X₁ (r • x),0) := by
    rw [← hf x,← hf (r • x),S.f.hom.hom.map_smul]
    exact act r (S.f.hom.hom x)
  have hi : PreservesFirstSummand α := by
    intro r u
    obtain ⟨x,rfl⟩ := (D S.X₁).surjective u
    rw [first]
  have second (r : R) (u v) : (α r (u,v)).2 = D S.X₃ (r • (D S.X₃).symm v) := by
    obtain ⟨y,hy⟩ := T.surjective (u,v)
    have hv : D S.X₃ (S.g.hom.hom y) = v := (hg y).symm.trans (congrArg Prod.snd hy)
    rw [← hy,act,← hv,LinearEquiv.symm_apply_apply,← S.g.hom.hom.map_smul]
    exact hg (r • y)
  let ξ := blockCurve H η hi 0
  let L := (ξ.coordinates.trans F).trans ((D S.X₁).symm.prodCongr (D S.X₃).symm)
  have hlin (r : R) (z : ξ.moduleObj) : L (r • z) = r • L z := by
    have hz := ξ.coordinates_smul r z
    change ((D S.X₁).symm.prodCongr (D S.X₃).symm) (F (ξ.coordinates (r • z))) = _
    rw [hz]
    change ((D S.X₁).symm.prodCongr (D S.X₃).symm) (F (F.symm
      (scaleExtensionBlock α 0 hi r (F (ξ.coordinates z))))) = _
    rw [F.apply_symm_apply,scaleExtensionBlock_apply,zero_smul,add_zero,second]
    have hh (u) : (α r (u,0)).1 = D S.X₁ (r • (D S.X₁).symm u) := by
      obtain ⟨x,rfl⟩ := (D S.X₁).surjective u
      rw [first,LinearEquiv.symm_apply_apply]
    rw [hh,LinearEquiv.prodCongr_apply,LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
    rfl
  let L' : ξ.moduleObj ≃ₗ[R] (↑S.X₁.obj × ↑S.X₃.obj) :=
    { L.toAddEquiv with map_smul' := hlin }
  let B := ((FGModuleCat.forgetBiprodIso S.X₁ S.X₃).trans (ModuleCat.biprodIsoProd S.X₁.obj S.X₃.obj)).toLinearEquiv
  let iso := (L'.trans B.symm).toFGModuleCatIso
  let : Module.Finite R (S.X₁.obj : Type u) := S.X₁.property
  let : Module.Finite R (S.X₃.obj : Type u) := S.X₃.property
  let : Module.Finite k (S.X₁.obj : Type u) := Module.Finite.trans R _
  let : Module.Finite k (S.X₃.obj : Type u) := Module.Finite.trans R _
  refine ⟨ξ,⟨iso⟩,blockCurve H η hi,blockBaseChangeHom H,blockCurve_polynomial b H η hi,
    blockCurve_at_unit H η hi,fun t ↦ ?_,rfl⟩
  change vertexCharacter d _ (blockBaseChange H t) = _
  rw [blockBaseChange_character]
  suffices ∑ i, (Module.finrank k (vertexPart (k := k) A.vertex S.X₁ i) : ℤ) * A.characterExponents g i = 0 by
    rw [this,zpow_zero]
  let := (finite_simpleIsomorphismClasses (R := R) k).fintype
  rw [Weight.eval,← A.class_eq_of_vertex_finrank S.X₁,classOfCompositionVector,map_sum] at hw
  simp only [map_nsmul,nsmul_eq_mul] at hw
  have eq := A.simpleIndex.sum_comp (fun i ↦ (Module.finrank k (vertexPart (k := k) A.vertex S.X₁ i) : ℤ) * A.characterExponents g i)
  exact eq.symm.trans (by simpa [characterExponents,Weight.eval] using hw)

include eM in
/-- A weight-zero short exact sequence and its split sequence determine the
same homogeneous evaluation ideal on the fixed representation variety. -/
theorem exists_split_point_same_evaluation [Infinite k] [IsArtinianRing R]
    (g : ProjectiveClass R) (hw : (projectiveClassWeight k g).eval S.X₁ = 0) :
    ∃ ξ : VertexRepresentation (k := k) d A.vertex,
      Nonempty (ξ.moduleObj ≅ S.X₁ ⊞ S.X₃) ∧
      kingEvaluationIdeal b (A.characterExponents g) ξ = kingEvaluationIdeal b (A.characterExponents g) η := by
  obtain ⟨ξ,iso,h⟩ := exists_split_point_degeneration b A S hs η eM g hw
  exact ⟨ξ,iso,h.evaluation_eq b _⟩

end SplitBasicVertices

end EFiniteCharacterizations.VertexRepresentation
