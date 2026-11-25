module

public import EFiniteCharacterizations.Subcategories.NakayamaTorsionPair
public import EFiniteCharacterizations.Silting.ThickSubcategories.BoundedProjectiveHomotopy
public import EFiniteCharacterizations.Silting.ThickSubcategories.ThickInversion
public import EFiniteCharacterizations.Silting.Fans.FourQuadrants
public import EFiniteCharacterizations.Stability.RationalExtraction
public import EFiniteCharacterizations.Stability.StableSeparationWeights

/-! # Numerical torsion pairs on the interior of a presilting cone -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra TensorProduct

universe u
namespace EFiniteCharacterizations

private theorem torsionPair_tests {C : Type*} [Category C] [Abelian C]
    {T F : ObjectProperty C} (pair : IsTorsionPair T F) (pos neg : C → Prop)
    (ht : ∀ X, T X → pos X) (hf : ∀ X, F X → neg X)
    (hdis : ∀ X, pos X → neg X → IsZero X)
    (quot : ∀ {X Y : C} (q : X ⟶ Y) [Epi q], T X → T Y)
    (sub : ∀ {X Y : C} (i : X ⟶ Y) [Mono i], F Y → F X) (M : C) :
    ((∀ {Q : C} (q : M ⟶ Q) [Epi q], pos Q) ↔ T M) ∧
      ((∀ {U : C} (i : U ⟶ M) [Mono i], neg U) ↔ F M) := by
  obtain ⟨L,Q,i,p,w,hL,hQ,hs⟩ := pair.2 M
  have := hs.epi_g
  have := hs.mono_f
  refine ⟨⟨fun h ↦ ?_,fun h _ q _ ↦ ht _ (quot q h)⟩,⟨fun h ↦ ?_,fun h _ i _ ↦ hf _ (sub i h)⟩⟩
  · have := hs.isIso_f_iff.2 (hdis Q (h p) (hf Q hQ))
    exact quot i hL
  · have := hs.isIso_g_iff.2 (hdis L (ht L hL) (h i))
    exact sub p hQ

namespace TwoTerm
variable {R : Type u} [Ring R] [IsNoetherianRing R] (k : Type u) [Field k]
  [Algebra k R] [Module.Finite k R]

local instance coneTorsionTopology : TopologicalSpace (RealProjectiveSpace R) := moduleTopology ℝ _
local instance coneTorsionContinuousAdd : ContinuousAdd (RealProjectiveSpace R) := ModuleTopology.continuousAdd ℝ _
local instance coneTorsionContinuousSMul : ContinuousSMul ℝ (RealProjectiveSpace R) := ModuleTopology.continuousSMul ℝ _

private theorem pos_on_generated (P : TwoTerm R) (hp : P.IsPresilting) {v : RealProjectiveSpace R}
    (hv : v ∈ intrinsicInterior ℝ (P.gVectorCone : Set _)) (M : FGModuleCat.{u} R)
    (hg : IsGeneratedBy (cokernel P.differential) M) (hn : ¬ IsZero M) :
    0 < realEulerEvaluation k (GrothendieckGroup.of M) v := by
  have hs := P.surjective_precompose_of_generatedBy ((surjective_boundary_iff_surjective_precompose P P).1 hp) hg
  let l := realEulerForm k (GrothendieckGroup.of M)
  apply neg_lt_zero.mp (neg_on_intrinsicInterior (-l)
    (fun w hw ↦ neg_nonpos.mpr (P.cone_eval_nonneg_of_surjective k M hs hw)) P.class_mem_gVectorCone ?_ hv)
  change -realEulerForm k _ _ < 0
  rw [eval_class,neg_lt_zero]
  exact_mod_cast (P.pos_eulerWeight_nonzero_quotients_iff k hp M).2 hg (𝟙 M) hn

private theorem neg_on_perp_of_nonzero_map (P : TwoTerm R) {v : RealProjectiveSpace R}
    (hv : v ∈ intrinsicInterior ℝ (P.gVectorCone : Set _)) (M : FGModuleCat.{u} R)
    (hm : Subsingleton (cokernel P.differential ⟶ M)) (hy : ¬ Subsingleton (M ⟶ P.nakayamaKernel k)) :
    realEulerEvaluation k (GrothendieckGroup.of M) v < 0 := by
  have hin := (P.injective_precompose_iff_no_hom_cokernel k M).2 hm
  apply neg_on_intrinsicInterior (realEulerForm k _) (fun _ hw ↦ P.cone_eval_nonpos_of_injective k M hin hw)
    P.class_mem_gVectorCone _ hv
  rw [eval_class]
  have hx := (homFinrank_eq_zero_iff k _ _).2 (fun f ↦ hm.elim f 0)
  have hpos : 0 < homFinrank k M (P.nakayamaKernel k) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have h := (homFinrank_eq_zero_iff k _ _).1 hz
    exact hy ⟨fun f g ↦ (h f).trans (h g).symm⟩
  have hneg : (P.eulerWeight k).eval M < 0 := by rw [P.eulerWeight_eq_perpendicular_difference k,hx]; omega
  exact_mod_cast hneg

/-- All four numerical torsion and torsion-free classes, and the semistable
subcategory, at an arbitrary real weight in the relative interior of C(P). -/
theorem cone_interior_torsion_identities (P : TwoTerm R) (hp : P.IsPresilting) {v : RealProjectiveSpace R}
    (hv : v ∈ intrinsicInterior ℝ (P.gVectorCone : Set _)) (M : FGModuleCat.{u} R) :
    let θ (X : FGModuleCat.{u} R) := realEulerEvaluation k (GrothendieckGroup.of X) v
    ((∀ {Q : FGModuleCat.{u} R} (q : M ⟶ Q) [Epi q], ¬ IsZero Q → 0 < θ Q) ↔
      IsGeneratedBy (cokernel P.differential) M) ∧
    ((∀ {Q : FGModuleCat.{u} R} (q : M ⟶ Q) [Epi q], 0 ≤ θ Q) ↔ Subsingleton (M ⟶ P.nakayamaKernel k)) ∧
    ((∀ {U : FGModuleCat.{u} R} (i : U ⟶ M) [Mono i], θ U ≤ 0) ↔ Subsingleton (cokernel P.differential ⟶ M)) ∧
    ((∀ {U : FGModuleCat.{u} R} (i : U ⟶ M) [Mono i], ¬ IsZero U → θ U < 0) ↔
      cogeneratedByModule (P.nakayamaKernel k).obj M) ∧
    (v ∈ realStabilityWall k M ↔ Subsingleton (cokernel P.differential ⟶ M) ∧ Subsingleton (M ⟶ P.nakayamaKernel k)) := by
  let θ (X : FGModuleCat.{u} R) := realEulerEvaluation k (GrothendieckGroup.of X) v
  let A := cokernel P.differential
  let Y := P.nakayamaKernel k
  have pair : IsTorsionPair (IsGeneratedBy A) (fun N ↦ Subsingleton (A ⟶ N)) := by
    constructor
    · exact fun f hg hf ↦ hg.hom_eq_zero f (fun a ↦ hf.elim _ 0)
    · intro N
      obtain ⟨T,i,hi,hT,hQ⟩ := P.exists_generated_subobject_cokernel_hom_zero k hp N
      exact ⟨T,cokernel i,i,cokernel.π i,cokernel.condition i,hT,hQ,
        ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) hi (by dsimp; infer_instance)⟩
  have first := torsionPair_tests pair (fun X ↦ ¬ IsZero X → 0 < θ X) (fun X ↦ θ X ≤ 0)
    (pos_on_generated k P hp hv)
    (fun X h ↦ P.cone_eval_nonpos_of_injective k X ((P.injective_precompose_iff_no_hom_cokernel k X).2 h)
      (intrinsicInterior_subset hv))
    (fun _ ht hf ↦ Classical.byContradiction fun hn ↦ (ht hn).not_ge hf)
    (fun q _ h ↦ h.of_epi q)
    (fun i _ h ↦ ⟨fun f g ↦ (cancel_mono i).1 (h.elim _ _)⟩) M
  have second := torsionPair_tests (P.nakayamaKernel_torsionPair k hp) (fun X ↦ 0 ≤ θ X) (fun X ↦ ¬ IsZero X → θ X < 0)
    (fun X h ↦ P.cone_eval_nonneg_of_surjective k X ((P.surjective_precompose_iff_no_hom_nakayamaKernel k X).2 h)
      (intrinsicInterior_subset hv))
    (fun X hc hn ↦ neg_on_perp_of_nonzero_map k P hv X
      (hom_zero_of_cogenerated ((P.isPresilting_iff_no_hom_nakayamaKernel k).1 hp) hc)
      (fun h ↦ hn ((IsZero.iff_id_eq_zero X).2 ((hom_zero_of_cogenerated h hc).elim _ _))))
    (fun _ ht hf ↦ Classical.byContradiction fun hn ↦ (hf hn).not_ge ht)
    (fun q _ h ↦ ⟨fun f g ↦ (cancel_epi q).1 (h.elim _ _)⟩)
    (fun i _ ⟨n,t,ht⟩ ↦ ⟨n,t.comp i.hom.hom,ht.comp ((FGModuleCat.mono_iff_injective i).1 inferInstance)⟩) M
  exact ⟨first.1,second.1,first.2,second.2,(P.mem_wall_iff_semistable_of_mem_cone_interior k hp M hv).trans
    (P.isSemistable_eulerWeight_iff_perpendicular k hp M)⟩

/-- The ambient rational Grothendieck classes of the stable modules at a
real interior weight are linearly independent. -/
theorem rationally_independent_stable_classes_in_cone (P : TwoTerm R) (hp : P.IsPresilting)
    {v : RealProjectiveSpace R} (hv : v ∈ intrinsicInterior ℝ (P.gVectorCone : Set _)) :
    LinearIndependent ℚ (fun x : {c : Skeleton (FGModuleCat.{u} R) // RealStableAt k v ((fromSkeleton _).obj c)} ↦
      (1 : ℚ) ⊗ₜ[ℤ] GrothendieckGroup.of ((fromSkeleton _).obj x.val)) := by
  let _ : IsArtinianRing R := isArtinian_of_tower k inferInstance
  let f (x : {c : Skeleton (FGModuleCat.{u} R) // RealStableAt k v ((fromSkeleton _).obj c)}) :
      stableClasses (P.eulerWeight k) :=
    ⟨x.val,(P.realStableAt_iff_stable_of_mem_cone_interior k hp _ hv).1 x.property⟩
  apply (rationalClass_independent_iff _).2
  exact (P.linearIndependent_stableClasses_eulerWeight k hp).comp f
    (fun _ _ he ↦ Subtype.ext (congrArg (fun t : stableClasses (P.eulerWeight k) ↦ t.val) he))

/-- An interior weight of a two-term silting cone strictly separates the
nonzero generated modules from their right orthogonal. -/
theorem silting_interior_signs (P : TwoTerm R) (hp : P.IsPresilting)
    (hgen : ∀ Z : (boundedProjective R).FullSubcategory,
      (ObjectProperty.singleton P.inBoundedProjectives).triangEnvelope Z)
    {v : RealProjectiveSpace R} (hv : v ∈ intrinsicInterior ℝ (P.gVectorCone : Set _)) :
    let T := IsGeneratedBy (cokernel P.differential)
    let F (Y : FGModuleCat.{u} R) := ∀ X, T X → Subsingleton (X ⟶ Y)
    let θ (X : FGModuleCat.{u} R) := realEulerEvaluation k (GrothendieckGroup.of X) v
    (∀ X, T X → ¬ IsZero X → 0 < θ X) ∧ (∀ Y, F Y → ¬ IsZero Y → θ Y < 0) ∧
      ∀ X Y, T X → ¬ IsZero X → F Y → GrothendieckGroup.of X ≠ GrothendieckGroup.of Y := by
  let A := cokernel P.differential
  have ha : IsGeneratedBy A A := ⟨1,biproduct.π (fun _ : Fin 1 ↦ A) 0,inferInstance⟩
  refine ⟨pos_on_generated k P hp hv,fun Y hF hn ↦ ?_,fun X Y hT hn hF he ↦ ?_⟩
  · apply neg_on_perp_of_nonzero_map k P hv Y (hF A ha)
    intro hy
    have hsem := (P.isSemistable_eulerWeight_iff_perpendicular k hp Y).2 ⟨hF A ha,hy⟩
    let G : FiniteProjective R := ⟨FGModuleCat.of R R,inferInstance⟩
    let _ := G.property
    let Q := inDegreeZero G.val
    have hQ := invertedOn_of_inThick ((P.bounded_thick_iff Q).1 (hgen Q.inBoundedProjectives))
      Y.obj ((P.invertedOn_iff_semistable k hp Y).2 hsem)
    have hz := ((Q.invertedOn_iff_semistable k (isPresilting_inDegreeZero G.val) Y).1 hQ).1
    rw [← projectiveClassWeight_eq_eulerWeight,projectiveClass_inDegreeZero G,projectiveClassWeight_of] at hz
    exact (dimensionWeight_pos k Y hn).ne' hz
  · have hpos := pos_on_generated k P hp hv X hT hn
    rw [he] at hpos
    exact hpos.not_ge (P.cone_eval_nonpos_of_injective k Y
      ((P.injective_precompose_iff_no_hom_cokernel k Y).2 (hF A ha)) (intrinsicInterior_subset hv))

end TwoTerm
end EFiniteCharacterizations
