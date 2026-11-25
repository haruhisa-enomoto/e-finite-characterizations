module

public import EFiniteCharacterizations.Algebra.BasicReduction
public import EFiniteCharacterizations.Geometry.VertexDimensions
public import Mathlib.Algebra.Category.ModuleCat.Simple

/-! # Simple modules of a split basic algebra -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations
namespace SplitBasicIdempotents

variable {k R I : Type u} [Field k] [Ring R] [Algebra k R] [Fintype I] [DecidableEq I]
    (P : SplitBasicIdempotents (k := k) (A := R) (ι := I))

/-- The character of the semisimple quotient at a vertex. -/
noncomputable def character (i : I) : R →ₐ[k] k :=
  ((Pi.evalAlgHom k (fun _ : I ↦ k) i).comp P.quotientEquiv.toAlgHom).comp (Ideal.Quotient.mkₐ k _)

/-- The one-dimensional module afforded by a vertex character. -/
noncomputable def vertexSimple (i : I) : FGModuleCat.{u} R := by
  let _ : Module R k := Module.compHom k (P.character i).toRingHom
  have : IsScalarTower k R k := IsScalarTower.of_algebraMap_smul fun c z ↦
    congrArg (· * z) ((P.character i).commutes c)
  have : Module.Finite R k := Module.Finite.of_restrictScalars_finite k _ _
  exact FGModuleCat.of R k

noncomputable def scalarCoordinates (i : I) : ((P.vertexSimple i).obj : Type u) ≃ₗ[k] k where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c z := congrArg (· * (show k from z)) ((P.character i).commutes c)

theorem simple_vertexSimple [IsNoetherianRing R] (i : I) : Simple (P.vertexSimple i) := by
  let F := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  have : Simple (F.obj (P.vertexSimple i)) := simple_of_finrank_eq_one (k := k)
    (by change Module.finrank k ((P.vertexSimple i).obj : Type u) = 1; simpa using (P.scalarCoordinates i).finrank_eq)
  exact F.simple_of_simple_obj _

private theorem simpleModule {M : FGModuleCat.{u} R} [IsNoetherianRing R] (h : Simple M) : IsSimpleModule R M := by
  have : Nontrivial M := not_subsingleton_iff_nontrivial.mp fun h ↦ Simple.not_isZero M ((FGModuleCat.isZero_iff_subsingleton M).2 h)
  have : Module.Finite R M := M.property
  apply (isSimpleModule_iff R M).mpr
  constructor
  intro N
  let Y := FGModuleCat.of R N
  let f : Y ⟶ M := FGModuleCat.ofHom N.subtype
  have : Mono f := (FGModuleCat.mono_iff_injective f).2 N.subtype_injective
  by_cases hz : f = 0
  · exact Or.inl (N.range_subtype ▸ LinearMap.range_eq_bot.mpr (congrArg (fun g : Y ⟶ M ↦ g.hom.hom) hz))
  · have := isIso_of_mono_of_nonzero hz
    exact Or.inr (N.range_subtype ▸ LinearMap.range_eq_top.mpr ((FGModuleCat.epi_iff_surjective f).1 inferInstance))

private theorem char_action_on_vertex [IsNoetherianRing R] {M : FGModuleCat.{u} R} (hs : Simple M)
    (r : R) (i : I) (m : M) : r • (P.idempotent i • m) = P.character i r • (P.idempotent i • m) := by
  have : IsSimpleModule R M := simpleModule hs
  let q := Ideal.Quotient.mkₐ k (Ring.jacobson R)
  have hJ : r * P.idempotent i - P.character i r • P.idempotent i ∈ Ring.jacobson R := by
    apply (Ideal.Quotient.eq_zero_iff_mem).1
    apply P.quotientEquiv.injective
    change P.quotientEquiv (q _) = _
    simp only [map_sub,map_mul,map_smul,map_zero]
    ext j
    change P.quotientEquiv (q r) j * P.quotientEquiv (q (P.idempotent i)) j -
      P.character i r * P.quotientEquiv (q (P.idempotent i)) j = 0
    simp only [q,Ideal.Quotient.mkₐ_eq_mk,P.quotientEquiv_mk_idempotent]
    split <;> simp_all [character]
  have hzero := Module.mem_annihilator.mp (IsSemisimpleModule.jacobson_le_annihilator (R := R) (M := M) hJ) m
  simpa only [sub_smul,mul_smul,smul_assoc,sub_eq_zero] using hzero

theorem exists_vertexSimple_iso [IsNoetherianRing R] (M : FGModuleCat.{u} R) (hs : Simple M) :
    ∃ i, Nonempty (P.vertexSimple i ≅ M) := by
  classical
  have : Nontrivial M := not_subsingleton_iff_nontrivial.mp fun h ↦ Simple.not_isZero M ((FGModuleCat.isZero_iff_subsingleton M).2 h)
  obtain ⟨v,hv⟩ := exists_ne (0 : M)
  obtain ⟨i,hi⟩ : ∃ i, P.idempotent i • v ≠ 0 := by
    by_contra! h
    exact hv (by simpa [← Finset.sum_smul,P.complete.complete] using Finset.sum_eq_zero (s := Finset.univ) (fun i _ ↦ h i))
  let m := P.idempotent i • v
  let l := (LinearMap.toSpanSingleton k (M.obj : Type u) m).comp (P.scalarCoordinates i).toLinearMap
  have hlinear (r : R) (z : P.vertexSimple i) : l (r • z) = r • l z := by
    change ((P.character i r) * (P.scalarCoordinates i z)) • m = r • (P.scalarCoordinates i z • m)
    rw [smul_comm r (P.scalarCoordinates i z),mul_comm (P.character i r)]
    change _ = (P.scalarCoordinates i z) • (r • (P.idempotent i • v))
    rw [P.char_action_on_vertex hs,smul_smul]
  let g : (P.vertexSimple i).obj →ₗ[R] M.obj := { l.toAddHom with map_smul' := hlinear }
  let f : P.vertexSimple i ⟶ M := ConcreteCategory.ofHom (X := P.vertexSimple i) (Y := M) g
  have hn : f ≠ 0 := by
    intro hz
    apply hi
    have h := congrArg (fun a : P.vertexSimple i ⟶ M ↦ a.hom.hom ((P.scalarCoordinates i).symm 1)) hz
    change P.scalarCoordinates i ((P.scalarCoordinates i).symm 1) • m = 0 at h
    simpa using h
  have := Weight.isIso_of_nonzero ((Weight.isStable_zero_iff_simple _).2 (P.simple_vertexSimple i))
    ((Weight.isStable_zero_iff_simple _).2 hs) f hn
  exact ⟨i,⟨asIso f⟩⟩

open VertexRepresentation in
theorem vertexSimple_dimension (i j : I) :
    Module.finrank k (vertexPart (k := k) P.idempotent (P.vertexSimple i) j) = if i = j then 1 else 0 := by
  have act (z : P.vertexSimple i) :
      P.scalarCoordinates i (P.idempotent j • z) = (if j = i then 1 else 0) * P.scalarCoordinates i z := by
    change P.character i (P.idempotent j) * _ = _
    rw [show P.character i (P.idempotent j) = _ from P.quotientEquiv_mk_idempotent j i]
    rfl
  by_cases hij : i = j
  · subst j
    have hs : vertexPart (k := k) P.idempotent (P.vertexSimple i) i = ⊤ :=
      LinearMap.range_eq_top.mpr fun z ↦ ⟨z,(P.scalarCoordinates i).injective (by simpa using act z)⟩
    rw [hs,finrank_top]
    simpa using (P.scalarCoordinates i).finrank_eq
  · have hs : vertexPart (k := k) P.idempotent (P.vertexSimple i) j = ⊥ :=
      LinearMap.range_eq_bot.mpr (LinearMap.ext fun z ↦ (P.scalarCoordinates i).injective
        (by simpa [Ne.symm hij] using act z))
    rw [hs]
    simp [hij]

variable [IsNoetherianRing R] [Module.Finite k R]

/-- A split basic quotient with lifted coordinate idempotents supplies the
vertex presentation indexed by the simple finite modules. -/
noncomputable def toSplitBasicVertices : VertexRepresentation.SplitBasicVertices k R I := by
  classical
  let s (i : I) : simpleIsomorphismClasses R :=
    ⟨toSkeleton (P.vertexSimple i),P.vertexSimple i,rfl,P.simple_vertexSimple i⟩
  let w j := VertexRepresentation.vertexWeight (k := k) P.idempotent j (P.complete.idem j)
  have hw i j : w j (GrothendieckGroup.of (P.vertexSimple i)) = (if i = j then (1 : ℤ) else 0) := by
    simp [w,VertexRepresentation.vertexWeight,GrothendieckGroup.lift_of,P.vertexSimple_dimension,apply_ite Nat.cast]
  have hs : Function.Bijective s := by
    constructor
    · intro i j h
      obtain ⟨f⟩ := toSkeleton_eq_toSkeleton_iff.1 (congrArg Subtype.val h : toSkeleton (P.vertexSimple i) = _)
      have he := congrArg (w i) (GrothendieckGroup.of_eq_of_iso f)
      by_contra hn
      simp [hw,Ne.symm hn] at he
    · rintro ⟨x,M,hM,hSimple⟩
      obtain ⟨i,⟨f⟩⟩ := P.exists_vertexSimple_iso M hSimple
      exact ⟨i,Subtype.ext ((congr_toSkeleton_of_iso f).trans hM)⟩
  let E := Equiv.ofBijective s hs
  refine ⟨P.idempotent,P.complete,E.symm,?_⟩
  intro x j
  obtain ⟨i,rfl⟩ := E.surjective x
  have iso := fromSkeletonToSkeletonIso (P.vertexSimple i)
  have h := congrArg (w j) (GrothendieckGroup.of_eq_of_iso iso)
  rw [hw] at h
  simp only [Equiv.symm_apply_apply]
  change Module.finrank k (VertexRepresentation.vertexPart (k := k) P.idempotent _ j) = _
  change Module.finrank k (VertexRepresentation.vertexPart (k := k) P.idempotent ((fromSkeleton _).obj (toSkeleton (P.vertexSimple i))) j) = _
  change (Module.finrank k _ : ℤ) = _ at h
  by_cases hij : i = j <;> simp only [hij,ite_true,ite_false] at h ⊢ <;> exact_mod_cast h

end SplitBasicIdempotents
end EFiniteCharacterizations
