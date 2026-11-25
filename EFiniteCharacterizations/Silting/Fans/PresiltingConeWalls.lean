module

public import EFiniteCharacterizations.Silting.Fans.WallFaces

/-! # Semistability on a presilting cone -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R] (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R]

omit [IsNoetherianRing R] in
theorem class_mem_gVectorCone (P : TwoTerm R) :
    realProjectiveClass R P.projectiveClass ∈ P.gVectorCone :=
  PointedCone.subset_hull ⟨P,IsInAdd.refl _,rfl⟩

omit [IsNoetherianRing R] in
private theorem cone_nonpos (P : TwoTerm R) (l : RealProjectiveSpace R →ₗ[ℝ] ℝ)
    (h : ∀ Q : TwoTerm R, IsInAdd Q.asArrow P.asArrow →
      l (realProjectiveClass R Q.projectiveClass) ≤ 0) :
    ∀ v ∈ P.gVectorCone, l v ≤ 0 := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨Q,hQ,rfl⟩ := hx; exact h Q hQ
  | zero => simp
  | add x y _ _ hx hy => simpa using add_nonpos hx hy
  | smul c x _ hx =>
    change l ((c : ℝ) • x) ≤ 0
    rw [map_smul]
    exact mul_nonpos_of_nonneg_of_nonpos c.property hx

theorem cone_eval_nonpos_of_injective (P : TwoTerm R) (X : FGModuleCat.{u} R)
    (h : Function.Injective (P.precompose X)) {v : RealProjectiveSpace R} (hv : v ∈ P.gVectorCone) :
    realEulerEvaluation k (GrothendieckGroup.of X) v ≤ 0 := by
  apply P.cone_nonpos (realEulerForm k _) _ v hv
  intro Q hQ
  change realEulerEvaluation k _ _ ≤ 0
  rw [realEulerEvaluation_integral]
  have ht := finiteModuleHom_isFinite k Q.source X
  have he := LinearMap.finrank_le_finrank_of_injective (f := Linear.leftComp k X Q.differential)
    (hQ.injective_precomp (M := X) h)
  change (((projectiveClassWeight k Q.projectiveClass).eval X : ℤ) : ℝ) ≤ 0
  rw [Q.projectiveClassWeight_eq_eulerWeight k,Q.eulerWeight_eval k,homFinrank_eq_finrank k,homFinrank_eq_finrank k]
  rw [Int.cast_sub,sub_nonpos]
  exact_mod_cast he

theorem cone_eval_nonneg_of_surjective (P : TwoTerm R) (X : FGModuleCat.{u} R)
    (h : Function.Surjective (P.precompose X)) {v : RealProjectiveSpace R} (hv : v ∈ P.gVectorCone) :
    0 ≤ realEulerEvaluation k (GrothendieckGroup.of X) v := by
  apply neg_nonpos.mp
  apply P.cone_nonpos (-(realEulerForm k _)) _ v hv
  intro Q hQ
  change -realEulerEvaluation k _ _ ≤ 0
  rw [neg_nonpos,realEulerEvaluation_integral]
  have ht := finiteModuleHom_isFinite k Q.target X
  have he := LinearMap.finrank_le_finrank_of_surjective (f := Linear.leftComp k X Q.differential)
    (hQ.surjective_precomp (M := X) h)
  change 0 ≤ (((projectiveClassWeight k Q.projectiveClass).eval X : ℤ) : ℝ)
  rw [Q.projectiveClassWeight_eq_eulerWeight k,Q.eulerWeight_eval k,homFinrank_eq_finrank k,homFinrank_eq_finrank k]
  rw [Int.cast_sub,sub_nonneg]
  exact_mod_cast he

/-- A module semistable at a presilting class has the entire cone in its wall. -/
theorem gVectorCone_subset_wall_of_semistable (P : TwoTerm R) (hp : P.IsPresilting)
    (X : FGModuleCat.{u} R) (hx : (P.eulerWeight k).IsSemistable X) :
    (P.gVectorCone : Set (RealProjectiveSpace R)) ⊆ realStabilityWall k X := by
  have h := (P.invertedOn_iff_semistable k hp X).2 hx
  have hb : Function.Bijective (P.precompose X) := by
    let e (A : FGModuleCat.{u} R) : (A ⟶ X) ≃ (A.obj ⟶ X.obj) := InducedCategory.homEquiv
    exact (e _).symm.bijective.comp (h.comp (e _).bijective)
  intro v hv
  refine ⟨le_antisymm (P.cone_eval_nonpos_of_injective k X hb.1 hv)
    (P.cone_eval_nonneg_of_surjective k X hb.2 hv),?_⟩
  rintro _ ⟨U,i,hi,_,_,rfl⟩
  apply P.cone_eval_nonpos_of_injective k U _ hv
  intro f g hfg
  change P.differential ≫ f = P.differential ≫ g at hfg
  apply (cancel_mono i).1
  apply hb.1
  change P.differential ≫ f ≫ i = P.differential ≫ g ≫ i
  simpa only [← Category.assoc] using congrArg (· ≫ i) hfg

open scoped Topology

theorem neg_on_intrinsicInterior {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] {s : Set V}
    (l : V →ₗ[ℝ] ℝ) (h : ∀ x ∈ s, l x ≤ 0) {x v : V} (hx : x ∈ s) (hn : l x < 0)
    (hv : v ∈ intrinsicInterior ℝ s) : l v < 0 := by
  refine (h v (intrinsicInterior_subset hv)).lt_of_ne fun hz ↦ ?_
  obtain ⟨y,hy,rfl⟩ := mem_intrinsicInterior.mp hv
  let p (t : ℝ) : affineSpan ℝ s := ⟨AffineMap.lineMap (y : V) x t,
    AffineMap.lineMap_mem t y.property (subset_affineSpan ℝ s hx)⟩
  have hc : Continuous p := Continuous.subtype_mk (by
    change Continuous (fun t : ℝ ↦ AffineMap.lineMap (y : V) x t)
    simp only [AffineMap.lineMap_apply_module]
    fun_prop) _
  have hp : p 0 = y := Subtype.ext (AffineMap.lineMap_apply_zero ..)
  have hmem : ∀ᶠ t in 𝓝[<] (0:ℝ), (p t : V) ∈ s :=
    nhdsWithin_le_nhds ((hc.continuousAt.tendsto) (hp ▸ mem_interior_iff_mem_nhds.mp hy))
  obtain ⟨t,hp',ht⟩ := (hmem.and (self_mem_nhdsWithin : ∀ᶠ t in 𝓝[<] (0:ℝ), t ∈ Set.Iio 0)).exists
  have hle := h _ hp'
  change l (AffineMap.lineMap (y : V) x t) ≤ 0 at hle
  rw [AffineMap.lineMap_apply_module,map_add,map_smul,map_smul,hz,smul_zero,zero_add] at hle
  exact (mul_pos_of_neg_of_neg ht hn).not_ge hle

local instance : TopologicalSpace (RealProjectiveSpace R) := moduleTopology ℝ _
local instance : ContinuousAdd (RealProjectiveSpace R) := ModuleTopology.continuousAdd ℝ _
local instance : ContinuousSMul ℝ (RealProjectiveSpace R) := ModuleTopology.continuousSMul ℝ _

theorem eval_class (P : TwoTerm R) (X : FGModuleCat.{u} R) :
    realEulerForm k (GrothendieckGroup.of X) (realProjectiveClass R P.projectiveClass) =
      ((P.eulerWeight k).eval X : ℝ) := by
  change realEulerEvaluation _ _ _ = _
  rw [realEulerEvaluation_integral,P.projectiveClassWeight_eq_eulerWeight k]
  rfl

/-- Throughout the relative interior of a presilting cone the semistable
modules are exactly those at the integral class of the presilting complex. -/
theorem mem_wall_iff_semistable_of_mem_cone_interior (P : TwoTerm R) (hp : P.IsPresilting)
    (X : FGModuleCat.{u} R) {v : RealProjectiveSpace R}
    (hv : v ∈ intrinsicInterior ℝ (P.gVectorCone : Set (RealProjectiveSpace R))) :
    v ∈ realStabilityWall k X ↔ (P.eulerWeight k).IsSemistable X := by
  refine ⟨fun hw ↦ ?_,fun h ↦ P.gVectorCone_subset_wall_of_semistable k hp X h (intrinsicInterior_subset hv)⟩
  let A := cokernel P.differential
  have hsurj : Function.Surjective (P.precompose A) :=
    (surjective_boundary_iff_surjective_precompose P P).1 hp
  have hz : ∀ f : A ⟶ X, f = 0 := by
    intro f
    by_contra hf
    let N := Abelian.image f
    let i := Abelian.image.ι f
    have hgen : IsGeneratedBy A N := ⟨1,biproduct.π (fun _ : Fin 1 ↦ A) 0 ≫ Abelian.factorThruImage f,inferInstance⟩
    have hn : ¬ IsZero N := fun h ↦ hf (by rw [← Abelian.image.fac f,h.eq_of_tgt (Abelian.factorThruImage f) 0,zero_comp])
    have hpos := (P.pos_eulerWeight_nonzero_quotients_iff k hp N).2 hgen (𝟙 N) hn
    let l := realEulerForm k (GrothendieckGroup.of N)
    have hl := neg_on_intrinsicInterior (-l) (fun w hw ↦ neg_nonpos.mpr
      (P.cone_eval_nonneg_of_surjective k N (P.surjective_precompose_of_generatedBy hsurj hgen) hw))
      P.class_mem_gVectorCone (by
        change -realEulerForm k _ _ < 0
        rw [eval_class,neg_lt_zero]
        exact_mod_cast hpos) hv
    have hle : l v ≤ 0 := by
      by_cases he : IsIso i
      · have he' : GrothendieckGroup.of N = GrothendieckGroup.of X := GrothendieckGroup.of_eq_of_iso (asIso i)
        change realEulerEvaluation k (GrothendieckGroup.of N) v ≤ 0
        exact he' ▸ hw.1.le
      · exact hw.2 _ ⟨N,i,inferInstance,hn,he,rfl⟩
    exact (neg_lt_zero.mp hl).not_ge hle
  have hinj : Function.Injective (P.precompose X) := by
    apply (AddMonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro f hf
    have he := cokernel.π_desc P.differential f hf
    rwa [hz (cokernel.desc _ f hf),comp_zero,eq_comm] at he
  have hle := P.cone_eval_nonpos_of_injective k X hinj P.class_mem_gVectorCone
  have he : (P.eulerWeight k).eval X = 0 := by
    change realEulerForm k _ _ ≤ 0 at hle
    rw [eval_class] at hle
    by_contra hne
    have hneg : (P.eulerWeight k).eval X < 0 := lt_of_le_of_ne (by exact_mod_cast hle) hne
    have hvneg := neg_on_intrinsicInterior (realEulerForm k (GrothendieckGroup.of X))
      (fun w hw ↦ P.cone_eval_nonpos_of_injective k X hinj hw) P.class_mem_gVectorCone
      (by rw [eval_class]; exact_mod_cast hneg) hv
    exact hvneg.ne hw.1
  refine ⟨he, fun {U} i hi ↦ ?_⟩
  have hsub : Function.Injective (P.precompose U) := by
    intro a b hab
    apply (cancel_mono i).1
    apply hinj
    change P.differential ≫ a = P.differential ≫ b at hab
    simpa only [TwoTerm.precompose,AddMonoidHom.coe_mk,ZeroHom.coe_mk,← Category.assoc] using congrArg (· ≫ i) hab
  have hs := P.cone_eval_nonpos_of_injective k U hsub P.class_mem_gVectorCone
  change realEulerForm k _ _ ≤ 0 at hs
  rw [eval_class] at hs
  exact_mod_cast hs

/-- Stability, including the isomorphism classes of all stable modules, is
constant throughout the relative interior of the cone. -/
theorem realStableAt_iff_stable_of_mem_cone_interior (P : TwoTerm R) (hp : P.IsPresilting)
    (X : FGModuleCat.{u} R) {v : RealProjectiveSpace R}
    (hv : v ∈ intrinsicInterior ℝ (P.gVectorCone : Set (RealProjectiveSpace R))) :
    RealStableAt k v X ↔ (P.eulerWeight k).IsStable X := by
  rw [← P.projectiveClassWeight_eq_eulerWeight k,← realStableAt_integral]
  simp only [realStableAt_iff_no_proper_semistable,
    P.mem_wall_iff_semistable_of_mem_cone_interior k hp _ hv,
    integral_mem_realStabilityWall,P.projectiveClassWeight_eq_eulerWeight k]

end EFiniteCharacterizations.TwoTerm

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R]

/-- The real wall-face endpoint can be checked at one integral presilting
weight for each brick, with the same codimension requirement. -/
theorem wall_face_iff_unique_stable_presilting_facet :
    BrickWallFaces (R := R) k ↔ ∀ X : FGModuleCat.{u} R, IsBrick X → ∃ P : TwoTerm R,
      P.IsPresilting ∧ Module.finrank ℝ (Submodule.span ℝ (P.gVectorCone : Set (RealProjectiveSpace R))) + 1 =
        Module.finrank ℝ (RealProjectiveSpace R) ∧ (P.eulerWeight k).IsStable X ∧
      ∀ Y : FGModuleCat.{u} R, (P.eulerWeight k).IsStable Y → Nonempty (X ≅ Y) := by
  constructor
  · intro h X hx
    obtain ⟨P,hp,hd,_,hface⟩ := h X hx
    obtain ⟨v,hv⟩ := P.gVectorCone_interior_nonempty k
    obtain ⟨hst,hu⟩ := hface v hv
    exact ⟨P,hp,hd,(P.realStableAt_iff_stable_of_mem_cone_interior k hp X hv).1 hst,
      fun Y hy ↦ hu _ ((P.realStableAt_iff_stable_of_mem_cone_interior k hp Y hv).2 hy)⟩
  · intro h X hx
    obtain ⟨P,hp,hd,hst,hu⟩ := h X hx
    refine ⟨P,hp,hd,P.gVectorCone_subset_wall_of_semistable k hp X hst.isSemistable,fun v hv ↦ ?_⟩
    exact ⟨(P.realStableAt_iff_stable_of_mem_cone_interior k hp X hv).2 hst,
      fun Y hy ↦ hu _ ((P.realStableAt_iff_stable_of_mem_cone_interior k hp Y hv).1 hy)⟩

end EFiniteCharacterizations
