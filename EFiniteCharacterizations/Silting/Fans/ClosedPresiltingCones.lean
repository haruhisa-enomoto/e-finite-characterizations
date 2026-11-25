module

public import EFiniteCharacterizations.Silting.Fans.ConeSaturation
public import EFiniteCharacterizations.Presentations.ProjectiveRankBound
public import EFiniteCharacterizations.LinearAlgebra.Farkas
public import Mathlib.Data.Pi.Interval

/-! # Finite generators and closedness of the real cones of projective differentials -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra NNReal

universe u
namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R] (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

namespace TwoTerm

/-- Integral projective classes of direct summands of one copy of a differential. -/
def retractClasses (P : TwoTerm R) : Set (ProjectiveClass R) :=
  {v | ∃ Q : TwoTerm R, Nonempty (Retract Q.asArrow P.asArrow) ∧ Q.projectiveClass = v}

omit [IsNoetherianRing R] in
private theorem homFinrank_le_of_retract {X Y : FGModuleCat.{u} R} (r : Retract X Y) (S : FGModuleCat.{u} R) :
    homFinrank k X S ≤ homFinrank k Y S := by
  have := finiteModuleHom_isFinite k Y S
  simp only [homFinrank_eq_finrank]
  exact LinearMap.finrank_le_finrank_of_injective (f := Linear.leftComp k S r.r)
    (fun _ _ h ↦ (cancel_epi r.r).1 h)

include k in
theorem finite_retractClasses (P : TwoTerm R) : P.retractClasses.Finite := by
  classical
  let I := ↥(simpleIsomorphismClasses R)
  let _ := (finite_simpleIsomorphismClasses (R := R) k).fintype
  let S (i : I) := (fromSkeleton _).obj i.val
  let f (g : ProjectiveClass R) (i : I) := (projectiveClassWeight k g).eval (S i)
  have hf : Function.Injective f := by
    intro g h eq
    apply ProjectiveClass.eq_of_eval_eq_on_simples k
    intro M hm
    let i : I := ⟨toSkeleton M,M,rfl,hm⟩
    let e := fromSkeletonToSkeletonIso M
    exact ((projectiveClassWeight k g).eval_eq_of_isIso e.hom).symm.trans
      ((congrFun eq i).trans ((projectiveClassWeight k h).eval_eq_of_isIso e.hom))
  let lo (i : I) : ℤ := -(homFinrank k P.source (S i) : ℤ)
  let hi (i : I) : ℤ := homFinrank k P.target (S i)
  apply Set.Finite.of_finite_image (f := f) _ hf.injOn
  apply (Set.finite_Icc lo hi).subset
  rintro _ ⟨_,⟨Q,⟨r⟩,rfl⟩,rfl⟩
  have bound (i : I) : lo i ≤ f Q.projectiveClass i ∧ f Q.projectiveClass i ≤ hi i := by
    dsimp only [lo,hi,f]
    rw [projectiveClassWeight_eq_eulerWeight,eulerWeight_eval]
    have h₁ := homFinrank_le_of_retract k (r.map Arrow.leftFunc) (S i)
    have h₀ := homFinrank_le_of_retract k (r.map Arrow.rightFunc) (S i)
    change homFinrank k Q.source (S i) ≤ homFinrank k P.source (S i) at h₁
    change homFinrank k Q.target (S i) ≤ homFinrank k P.target (S i) at h₀
    omega
  exact ⟨fun i ↦ (bound i).1,fun i ↦ (bound i).2⟩

include k in
/-- Retracts of a single copy generate the full cone, including all classes arising from
retracts of arbitrary finite sums. -/
theorem gVectorCone_eq_hull_retracts (P : TwoTerm R) :
    P.gVectorCone = PointedCone.hull ℝ (realProjectiveClass R '' P.retractClasses) := by
  let C := PointedCone.hull ℝ (realProjectiveClass R '' P.retractClasses)
  have gen (X : TwoTerm R) (hX : IsInAdd X.asArrow P.asArrow) : realProjectiveClass R X.projectiveClass ∈ C := by
    generalize he : X.arrowEndDim k = n
    induction n using Nat.strong_induction_on generalizing X with
    | h n ih =>
      by_cases hz : X.projectiveClass = 0
      · rw [hz,map_zero]; exact C.zero_mem
      obtain ⟨A,r,ha,hlocal⟩ := exists_local_summand k hz
      have hA := (IsInAdd.of_retraction r.i r.r r.retract).trans hX
      let D := contractible (ProjectiveClass.zeroProjective R)
      have hs : A.IsInStableAdd P := ⟨_,hA.trans (IsInAdd.of_retraction _ _ (inlDirectSum_fstDirectSum P D))⟩
      obtain ⟨t⟩ := retract_of_local_stableAdd ha hs
      obtain ⟨B,s,_,hab,hlt⟩ := strict_complement k r
      have hb := ih _ ((hlt ha).trans_eq he) B ((IsInAdd.of_retraction s.i s.r s.retract).trans hX) rfl
      rw [hab,map_add]
      exact C.add_mem (PointedCone.subset_hull ⟨_,⟨A,⟨t⟩,rfl⟩,rfl⟩) hb
  apply le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨X,hX,rfl⟩
    exact gen X hX
  · rintro _ ⟨_,⟨Q,⟨r⟩,rfl⟩,rfl⟩
    exact PointedCone.subset_hull ⟨Q,IsInAdd.of_retraction r.i r.r r.retract,rfl⟩

end TwoTerm

section FiniteHull
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
  [TopologicalSpace V] [IsModuleTopology ℝ V]

/-- In finite dimension a finitely generated real cone is closed. Farkas certificates
describe its complement by strict inequalities in the coordinates of the test point. -/
theorem isClosed_hull_finite {s : Set V} (hs : s.Finite) : IsClosed (PointedCone.hull ℝ s : Set V) := by
  classical
  let _ := hs.fintype
  let n := Fintype.card s
  let v (j : Fin n) : V := ((Fintype.equivFin s).symm j).val
  have hr : Set.range v = s := by
    ext x
    exact ⟨fun ⟨j,hj⟩ ↦ hj ▸ ((Fintype.equivFin s).symm j).property,
      fun hx ↦ ⟨Fintype.equivFin s ⟨x,hx⟩,by simp [v]⟩⟩
  let d := Module.finrank ℝ V
  let e := Module.finBasis ℝ V
  let I := Fin n ⊕ (Fin d ⊕ Fin d)
  let A : I → Fin n → ℝ := Sum.elim (fun j ↦ Pi.single j 1)
    (Sum.elim (fun i j ↦ e.coord i (v j)) (fun i j ↦ -e.coord i (v j)))
  let b (x : V) : I → ℝ := Sum.elim (fun _ ↦ 0) (Sum.elim (fun i ↦ e.coord i x) (fun i ↦ -e.coord i x))
  have hb (i : I) : Continuous (fun x ↦ b x i) := by
    rcases i with j | (t | t)
    · exact continuous_const
    · exact IsModuleTopology.continuous_of_linearMap (e.coord t)
    · exact (IsModuleTopology.continuous_of_linearMap (e.coord t)).neg
  have hf (x : V) : x ∈ PointedCone.hull ℝ s ↔ Farkas.Feasible A (b x) := by
    rw [← hr,PointedCone.hull,Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c,rfl⟩
      refine ⟨fun j ↦ (c j : ℝ),fun i ↦ ?_⟩
      rcases i with j | (t | t)
      · simpa [A,b,Pi.single_apply] using (c j).property
      · simp [A,b,← Nonneg.coe_smul,mul_comm]
      · simp [A,b,← Nonneg.coe_smul,mul_comm,Finset.sum_neg_distrib]
    · rintro ⟨c,hc⟩
      have hpos (j : Fin n) : 0 ≤ c j := by simpa [A,b,Pi.single_apply] using hc (.inl j)
      refine ⟨fun j ↦ ⟨c j,hpos j⟩, e.ext_elem_iff.2 fun t ↦ ?_⟩
      change e.coord t (∑ j, (c j) • v j) = e.coord t x
      rw [map_sum]
      simp only [map_smul,smul_eq_mul]
      apply le_antisymm
      · simpa [A,b,Finset.sum_neg_distrib,mul_comm] using hc (.inr (.inr t))
      · simpa [A,b,mul_comm] using hc (.inr (.inl t))
  let cert := {y : I → ℝ // (∀ i, 0 ≤ y i) ∧ ∀ j, ∑ i, y i * A i j = 0}
  have heq : (PointedCone.hull ℝ s : Set V) = ⋂ y : cert, {x | ∑ i, y.val i * b x i ≤ 0} := by
    ext x
    rw [Set.mem_iInter]
    constructor
    · intro hx y
      exact le_of_not_gt fun hy ↦ Farkas.not_feasible_and_certificate A (b x)
        ⟨(hf x).1 hx,y.val,y.property.1,y.property.2,hy⟩
    · intro h
      apply (hf x).2
      rcases Farkas.farkas n A (b x) with hfeas | ⟨y,hy,ha,hp⟩
      · exact hfeas
      · exact False.elim (hp.not_ge (h ⟨y,hy,ha⟩))
  rw [heq]
  exact isClosed_iInter (fun y ↦ isClosed_le (continuous_finsetSum _ fun i _ ↦ continuous_const.mul (hb i)) continuous_const)

end FiniteHull

local instance closedConeTopology : TopologicalSpace (RealProjectiveSpace R) := moduleTopology ℝ _
local instance closedConeModuleTopology : IsModuleTopology ℝ (RealProjectiveSpace R) := ⟨rfl⟩

include k in
theorem TwoTerm.isClosed_gVectorCone (P : TwoTerm R) : IsClosed (P.gVectorCone : Set (RealProjectiveSpace R)) := by
  let _ := (realProjectiveSpace_rank_bound (R := R) k).1
  rw [P.gVectorCone_eq_hull_retracts k]
  exact isClosed_hull_finite ((finite_retractClasses k P).image _)

end EFiniteCharacterizations
