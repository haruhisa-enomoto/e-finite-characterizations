module

public import EFiniteCharacterizations.Silting.Fans.ConeSaturation

/-!
# Relative interiors of two-term presilting cones

Second assertion of Lemma 2.1(1) (`lem:fan-lattice`): the `g`-vector of any two-term
complex lies in the relative interior of its `g`-vector cone
(`class_mem_intrinsicInterior_gVectorCone`), and every vector in the fan support
`Σ(R)` lies in the relative interior of `C(P)` for some two-term presilting complex `P`
(`mem_fanSupport_iff_cone_interior`).
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped Topology

universe u
namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R] [IsNoetherianRing R] (k : Type u) [Field k] [Algebra k R]
  [Module.Finite k R]

omit [IsNoetherianRing R] in
private theorem strict_retract_copies {Q P : TwoTerm R} (h : IsInAdd Q.asArrow P.asArrow) :
    ∃ n, Nonempty (Retract Q.asArrow (P.copies n).asArrow) := by
  obtain ⟨l,hl⟩ := h
  have lift (l : List ((Q.asArrow ⟶ P.asArrow) × (P.asArrow ⟶ Q.asArrow))) :
      ∃ (n : ℕ) (a : Q.asArrow ⟶ (P.copies n).asArrow) (b : (P.copies n).asArrow ⟶ Q.asArrow),
        a ≫ b = (l.map (fun p ↦ p.1 ≫ p.2)).sum := by
    induction l with
    | nil => exact ⟨0,0,0,by simp⟩
    | cons p l ih =>
      obtain ⟨n,a,b,he⟩ := ih
      let Z := P.copies n
      have h₁ : inlDirectSum P Z ≫ sndDirectSum P Z = 0 := by apply Arrow.hom_ext <;> exact biprod.inl_snd
      have h₂ : inrDirectSum P Z ≫ fstDirectSum P Z = 0 := by apply Arrow.hom_ext <;> exact biprod.inr_fst
      let i : Q.asArrow ⟶ (P.directSum Z).asArrow := p.1 ≫ inlDirectSum P Z + a ≫ inrDirectSum P Z
      let j : (P.directSum Z).asArrow ⟶ Q.asArrow := fstDirectSum P Z ≫ p.2 + sndDirectSum P Z ≫ b
      exact ⟨n+1,i,j,show i ≫ j = _ by
          simp [i,j,Preadditive.add_comp,Preadditive.comp_add,Category.assoc,reassoc_of% h₁,reassoc_of% h₂,
            reassoc_of% (inlDirectSum_fstDirectSum P Z),reassoc_of% (inrDirectSum_sndDirectSum P Z),he]⟩
  obtain ⟨n,a,b,he⟩ := lift l
  exact ⟨n,⟨⟨a,b,he.trans hl⟩⟩⟩

include k in
private theorem cone_dominated_by_class (P : TwoTerm R) (x : RealProjectiveSpace R) (hx : x ∈ P.gVectorCone) :
    ∃ t : ℝ, 0 ≤ t ∧ t • realProjectiveClass R P.projectiveClass - x ∈ P.gVectorCone := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Q,hQ,rfl⟩ := hx
    obtain ⟨n,⟨r⟩⟩ := strict_retract_copies hQ
    obtain ⟨Y,s,_,hclass,_⟩ := strict_complement k r
    have hy : realProjectiveClass R Y.projectiveClass ∈ P.gVectorCone :=
      PointedCone.subset_hull ⟨Y,(IsInAdd.of_retraction _ _ s.retract).trans (isInAdd_copies P n),rfl⟩
    rw [projectiveClass_copies] at hclass
    refine ⟨n,by positivity,?_⟩
    rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, hclass, map_add, add_sub_cancel_left]
    exact hy
  | zero => exact ⟨0,le_rfl,by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a,ha,hx⟩ := hx
    obtain ⟨b,hb,hy⟩ := hy
    refine ⟨a+b,add_nonneg ha hb,?_⟩
    convert P.gVectorCone.add_mem hx hy using 1
    rw [add_smul]; abel
  | smul c x _ hx =>
    obtain ⟨a,ha,hx⟩ := hx
    exact ⟨c.val*a,mul_nonneg c.property ha,by
      simpa only [smul_sub,smul_smul,← Nonneg.coe_smul] using P.gVectorCone.smul_mem c.property hx⟩

local instance : TopologicalSpace (RealProjectiveSpace R) := moduleTopology ℝ _
local instance : ContinuousAdd (RealProjectiveSpace R) := ModuleTopology.continuousAdd ℝ _
local instance : ContinuousSMul ℝ (RealProjectiveSpace R) := ModuleTopology.continuousSMul ℝ _

omit [IsNoetherianRing R] in
private theorem interior_of_domination (C : PointedCone ℝ (RealProjectiveSpace R))
    {v x : RealProjectiveSpace R} {t : ℝ} (hv : v ∈ C)
    (hx : x ∈ intrinsicInterior ℝ (C : Set _)) (ht : 0 < t) (hdiff : t • v - x ∈ C) :
    v ∈ intrinsicInterior ℝ (C : Set _) := by
  let _ : IsModuleTopology ℝ (RealProjectiveSpace R) := ⟨rfl⟩
  let _ := IsModuleTopology.isTopologicalAddGroup ℝ (RealProjectiveSpace R)
  let A := affineSpan ℝ (C : Set (RealProjectiveSpace R))
  obtain ⟨z,hz,rfl⟩ := mem_intrinsicInterior.mp hx
  let p : A := ⟨v,subset_affineSpan ℝ _ hv⟩
  let F (y : A) : A := ⟨t • ((y : RealProjectiveSpace R) - v) + z.val,
    AffineSubspace.vadd_mem_of_mem_direction (A.direction.smul_mem t
      (AffineSubspace.vsub_mem_direction y.property p.property)) z.property⟩
  have hf : Continuous F := Continuous.subtype_mk (by
    have hval : Continuous (fun y : A ↦ (y : RealProjectiveSpace R)) := continuous_subtype_val
    exact ((continuous_const (y := t)).smul (hval.sub (continuous_const (y := v)))).add
      (continuous_const (y := z.val))) _
  have he : F p = z := Subtype.ext (by simp [F,p])
  refine mem_intrinsicInterior.mpr ⟨p,mem_interior_iff_mem_nhds.mpr ?_,rfl⟩
  have hnear : ∀ᶠ y in 𝓝 p, (F y).val ∈ C :=
    hf.continuousAt.tendsto (he ▸ mem_interior_iff_mem_nhds.mp hz)
  filter_upwards [hnear] with y hy
  have eq : (F y).val + (t • v - z.val) = t • y.val := by dsimp [F]; rw [smul_sub]; abel
  have h := C.add_mem hy hdiff
  rw [eq] at h
  exact (by simpa only [smul_smul, inv_mul_cancel₀ ht.ne',one_smul] using C.smul_mem (inv_pos.mpr ht).le h :
    y.val ∈ C)

include k in
theorem class_mem_intrinsicInterior_gVectorCone (P : TwoTerm R) :
    realProjectiveClass R P.projectiveClass ∈ intrinsicInterior ℝ (P.gVectorCone : Set _) := by
  let v := realProjectiveClass R P.projectiveClass
  let C := P.gVectorCone
  obtain ⟨x,hx⟩ := P.gVectorCone_interior_nonempty k
  obtain ⟨a,ha,hd⟩ := cone_dominated_by_class k P x (intrinsicInterior_subset hx)
  let t := a+1
  have ht : 0 < t := by dsimp [t]; linarith
  have hdiff : t • v - x ∈ C := by
    convert C.add_mem hd P.class_mem_gVectorCone using 1
    dsimp [t,v]; rw [add_smul,one_smul]; abel
  exact interior_of_domination C P.class_mem_gVectorCone hx ht hdiff

omit [IsNoetherianRing R] in
theorem gVectorCone_mono {P Q : TwoTerm R} (h : IsInAdd P.asArrow Q.asArrow) :
    P.gVectorCone ≤ Q.gVectorCone := by
  apply Submodule.span_le.mpr
  rintro _ ⟨T,hT,rfl⟩
  exact PointedCone.subset_hull ⟨T,hT.trans h,rfl⟩

include k in
/-- A point of a cone lies in the relative interior of the cone of an additive summand.
For a positive sum of generators, take their direct sum. -/
theorem exists_inAdd_cone_interior (P : TwoTerm R) {x : RealProjectiveSpace R} (hx : x ∈ P.gVectorCone) :
    ∃ Q : TwoTerm R, IsInAdd Q.asArrow P.asArrow ∧ x ∈ intrinsicInterior ℝ (Q.gVectorCone : Set _) := by
  let Supports (v : RealProjectiveSpace R) := ∃ Q : TwoTerm R, IsInAdd Q.asArrow P.asArrow ∧
    v ∈ Q.gVectorCone ∧ ∃ t : ℝ, 0 < t ∧ ∀ s ≥ t, s • v - realProjectiveClass R Q.projectiveClass ∈ Q.gVectorCone
  have hz : Supports 0 := by
    refine ⟨P.copies 0,isInAdd_copies P 0,Submodule.zero_mem _,1,zero_lt_one,fun s _ ↦ ?_⟩
    simp [projectiveClass_copies]
  have hs : Supports x := by
    induction hx using Submodule.span_induction with
    | mem v h =>
      obtain ⟨Q,hQ,rfl⟩ := h
      refine ⟨Q,hQ,Q.class_mem_gVectorCone,1,zero_lt_one,fun s hs ↦ ?_⟩
      simpa only [sub_smul,one_smul] using Q.gVectorCone.smul_mem (sub_nonneg.2 hs) Q.class_mem_gVectorCone
    | zero => exact hz
    | add v w _ _ hv hw =>
      obtain ⟨A,hA,hv,a,ha,hda⟩ := hv
      obtain ⟨B,hB,hw,b,hb,hdb⟩ := hw
      let Q := A.directSum B
      have hl : A.gVectorCone ≤ Q.gVectorCone :=
        gVectorCone_mono (IsInAdd.of_retraction _ _ (inlDirectSum_fstDirectSum A B))
      have hr : B.gVectorCone ≤ Q.gVectorCone :=
        gVectorCone_mono (IsInAdd.of_retraction _ _ (inrDirectSum_sndDirectSum A B))
      refine ⟨Q,isInAdd_directSum _ _ _ hA hB,Q.gVectorCone.add_mem (hl hv) (hr hw),
        max a b,lt_max_of_lt_left ha,fun s hs ↦ ?_⟩
      have h := Q.gVectorCone.add_mem (hl (hda s (le_trans (le_max_left _ _) hs)))
        (hr (hdb s (le_trans (le_max_right _ _) hs)))
      convert h using 1
      dsimp [Q]; rw [projectiveClass_directSum,map_add,smul_add]; abel
    | smul c v _ hv =>
      by_cases hc : c.val = 0
      · simpa [show c = 0 from Subtype.ext hc] using hz
      obtain ⟨Q,hQ,hv,t,ht,hd⟩ := hv
      have hp := lt_of_le_of_ne c.property (Ne.symm hc)
      refine ⟨Q,hQ,Q.gVectorCone.smul_mem c.property hv,t/c.val,div_pos ht hp,fun s hs ↦ ?_⟩
      change s • (c.val • v) - _ ∈ _
      rw [smul_smul]
      exact hd _ ((div_le_iff₀ hp).1 hs)
  obtain ⟨Q,hQ,hx,t,ht,hd⟩ := hs
  exact ⟨Q,hQ,interior_of_domination _ hx (class_mem_intrinsicInterior_gVectorCone k Q) ht (hd t le_rfl)⟩

include k in
theorem mem_fanSupport_iff_cone_interior (x : RealProjectiveSpace R) :
    x ∈ gVectorFanSupport R ↔ ∃ P : TwoTerm R, P.IsPresilting ∧ x ∈ intrinsicInterior ℝ (P.gVectorCone : Set _) := by
  constructor
  · rintro ⟨P,hP,hx⟩
    obtain ⟨Q,hQ,hx⟩ := exists_inAdd_cone_interior k P hx
    exact ⟨Q,isPresilting_of_homotopy_isInAdd hP
      (hQ.map (doubleFunctor (C := FGModuleCat.{u} R) ⋙ HomotopyCategory.quotient _ _)),hx⟩
  · rintro ⟨P,hP,hx⟩
    exact ⟨P,hP,intrinsicInterior_subset hx⟩

end EFiniteCharacterizations.TwoTerm
