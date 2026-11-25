module

public import EFiniteCharacterizations.Silting.Fans.BrickFacets
public import EFiniteCharacterizations.Stability.PolystableClasses

/-!
# Realization of wide subcategories as `τ`-perpendicular categories

First assertion of Theorem 5.1 (`thm:wide`): over an E-finite algebra, the simple
objects of any wide subcategory `W ⊆ mod R` form a finite semibrick jointly stable
at an integral weight; choosing a presilting cone `C(P)` of maximal dimension whose
interior stabilizes those simples realizes `W` as the `τ`-perpendicular category
`J(P)` (`exists_presilting_perpendicular_of_wide`), which is functorially finite.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits

universe u
namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

open IsWideClass in
/-- If the algebra is E-finite, every wide subcategory is the full
perpendicular category of one two-term presilting complex. -/
theorem exists_presilting_perpendicular_of_wide (he : IsEFinite R)
    {W : ObjectProperty (FGModuleCat.{u} R)} (hw : IsWideClass W) :
    ∃ P : TwoTerm R, P.IsPresilting ∧ ∀ X, W X ↔
      Subsingleton (cokernel P.differential ⟶ X) ∧ Subsingleton (X ⟶ P.nakayamaKernel k) := by
  classical
  have := (realProjectiveSpace_rank_bound (R := R) k).1
  let stabilizes (P : TwoTerm R) := ∀ X, IsSimpleMember W X → (P.eulerWeight k).IsStable X
  let attainable (n : ℕ) := ∃ P : TwoTerm R, P.IsPresilting ∧ stabilizes P ∧
    Module.finrank ℝ P.gVectorConeSpan = n
  obtain ⟨g,hg,_⟩ := exists_weight_stabilizing_wide_simples k he hw
  obtain ⟨U,hu,rfl⟩ := he g
  rw [U.projectiveClassWeight_eq_eulerWeight k] at hg
  have start : attainable (Module.finrank ℝ U.gVectorConeSpan) := ⟨U,hu,hg,rfl⟩
  obtain ⟨P,hp,hstab,hmax⟩ := Nat.findGreatest_spec (Submodule.finrank_le U.gVectorConeSpan) start
  let θ := P.eulerWeight k
  have belongs (S : FGModuleCat.{u} R) (hs : θ.IsStable S) : W S := by
    by_contra hS
    obtain ⟨V,hPV,hpos,hV⟩ := P.exists_stable_separating_summand k hp hs
    have hstab' : stabilizes (P.directSum V) := by
      intro T hT
      have hne : ¬ Nonempty (S ≅ T) := fun ⟨e⟩ ↦ hS (hw.iso_mem e.symm hT.1)
      have hsum := (hstab T hT).add_of_semistable (hV T (hstab T hT) hne)
      simpa only [← TwoTerm.projectiveClassWeight_eq_eulerWeight k,TwoTerm.projectiveClass_directSum,map_add] using hsum
    let Q := P.directSum V
    have hQ : attainable (Module.finrank ℝ Q.gVectorConeSpan) := ⟨Q,hPV,hstab',rfl⟩
    have hle := Nat.le_findGreatest (Submodule.finrank_le Q.gVectorConeSpan) hQ
    have heq := Submodule.eq_of_le_of_finrank_le (P.gVectorConeSpan_le_directSum V) (hle.trans_eq hmax.symm)
    have hv : realProjectiveClass R V.projectiveClass ∈ P.gVectorConeSpan := by
      rw [heq]
      apply Submodule.subset_span
      exact PointedCone.subset_hull ⟨V,IsInAdd.of_retraction _ _ (TwoTerm.inrDirectSum_sndDirectSum P V),rfl⟩
    have hker : P.gVectorConeSpan ≤ LinearMap.ker (realEulerForm k (GrothendieckGroup.of S)) :=
      Submodule.span_le.2 (fun x hx ↦ (P.gVectorCone_subset_wall_of_semistable k hp S hs.isSemistable hx).1)
    have hz := hker hv
    change realEulerEvaluation k _ _ = 0 at hz
    rw [realEulerEvaluation_integral,Int.cast_eq_zero,V.projectiveClassWeight_eq_eulerWeight k] at hz
    exact hpos.ne' hz
  let T : ObjectProperty (FGModuleCat.{u} R) := θ.IsSemistable
  let : Fact (IsWideClass T) := ⟨θ.isWideClass_semistable⟩
  refine ⟨P,hp,fun X ↦ ?_⟩
  rw [← P.isSemistable_eulerWeight_iff_perpendicular k hp X]
  constructor
  · exact hw.extension_induction T θ.isWideClass_semistable.zero_mem
      (fun row hr h _ ih ↦ θ.isWideClass_semistable.extension_mem row hr (hstab _ h).isSemistable ih)
  · apply θ.isWideClass_semistable.extension_induction W hw.zero_mem
    intro row hr h _ ih
    have hs := (θ.isStable_iff_simple ⟨_,h.1⟩).2 ((simple_iff_simpleMember (W := T) _).2 h)
    exact hw.extension_mem row hr (belongs _ hs) ih

end EFiniteCharacterizations
