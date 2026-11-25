module

public import EFiniteCharacterizations.Geometry.BlockDegeneration

/-! # Numerical semistability of the homogeneous evaluation locus -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra
universe u
namespace EFiniteCharacterizations.VertexRepresentation.SplitBasicVertices

variable {k R I J : Type u} [Field k] [Infinite k] [Ring R] [Algebra k R] [Module.Finite k R]
    [IsNoetherianRing R] [IsArtinianRing R] [Fintype I] [DecidableEq I] [Fintype J]
    (P : SplitBasicVertices k R I) (b : Module.Basis J k R) {d : I → ℕ}
    (ρ : VertexRepresentation (k := k) d P.vertex) (g : ProjectiveClass R)

omit [Infinite k] [Fintype J] in
/-- Testing total weight and the weights of all invariant first summands suffices
for numerical semistability. -/
theorem semistable_of_block_weights
    (hz : (projectiveClassWeight k g).eval ρ.moduleObj = 0)
    (hblocks : ∀ (U Q : (i : I) → Submodule k (Fin (d i) → k))
      (hQ : ∀ i, IsCompl (U i) (Q i)),
      PreservesFirstSummand (splitAction (fun i ↦ (Submodule.prodEquivOfIsCompl (U i) (Q i) (hQ i)).symm) ρ) →
        ∑ i, (Module.finrank k (U i) : ℤ) * P.characterExponents g i ≤ 0) :
    (projectiveClassWeight k g).IsSemistable ρ.moduleObj := by
  classical
  refine ⟨hz, fun {M} φ hφ ↦ ?_⟩
  let μ := ρ.coordinates.toLinearMap.comp (φ.hom.hom.restrictScalars k)
  have hμ (r : R) (z : M) : μ (r • z) = ρ.val r (μ z) := by
    change ρ.coordinates (φ.hom.hom (r • z)) = _
    rw [φ.hom.hom.map_smul,coordinates_smul]
    rfl
  let V (i : I) := vertexPart (k := k) P.vertex M i
  let D := VertexRepresentation.decompose (k := k) P.complete M
  let a (i : I) := (LinearMap.proj i).comp (μ.comp (V i).subtype)
  have had (z : M) (i : I) : a i (D z i) = μ z i := by
    change μ (P.vertex i • z) i = _
    rw [hμ,ρ.property]
    simp [vertexProjection]
  have hai (i : I) : Function.Injective (a i) := by
    apply (LinearMap.ker_eq_bot).1
    rw [LinearMap.ker_eq_bot']
    rintro ⟨v,z,rfl⟩ hv
    apply Subtype.ext
    apply (FGModuleCat.mono_iff_injective φ).1 hφ
    apply ρ.coordinates.injective
    simp only [Submodule.coe_zero, map_zero]
    change μ (P.vertex i • z) = 0
    change a i (D z i) = 0 at hv
    rw [had] at hv
    rw [hμ,ρ.property]
    simp [vertexProjection,hv]
  let U (i : I) := LinearMap.range (a i)
  choose Q hQ using fun i ↦ (U i).exists_isCompl
  let E (i : I) := (Submodule.prodEquivOfIsCompl (U i) (Q i) (hQ i)).symm
  have hsplit : PreservesFirstSummand (splitAction E ρ) := by
    intro r u
    choose z hz using fun i ↦ (u i).property
    let v := D.symm z
    have he (i : I) : μ v i = (u i).val := by
      rw [← had, D.apply_symm_apply]
      exact hz i
    have hv : (vertexSplitting E).symm (u,0) = μ v := by
      funext i
      change Submodule.prodEquivOfIsCompl (U i) (Q i) (hQ i) (u i,0) = μ v i
      simpa using (he i).symm
    funext i
    change (E i ((ρ.val r ((vertexSplitting E).symm (u,0))) i)).2 = 0
    rw [hv,← hμ]
    apply (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero (U i) (Q i) (hQ i)).2
    exact ⟨D (r • v) i, had _ _⟩
  have hnon := hblocks U Q hQ hsplit
  have heval : (projectiveClassWeight k g).eval M =
      ∑ i, (Module.finrank k (V i) : ℤ) * P.characterExponents g i := by
    let := (finite_simpleIsomorphismClasses (R := R) k).fintype
    rw [Weight.eval, ← P.class_eq_of_vertex_finrank M, classOfCompositionVector, map_sum]
    simp only [map_nsmul,nsmul_eq_mul]
    simpa [V,characterExponents,Weight.eval] using P.simpleIndex.sum_comp
      (fun i ↦ (Module.finrank k (V i) : ℤ) * P.characterExponents g i)
  rw [heval]
  simpa only [U,LinearMap.finrank_range_of_inj (hai _)] using hnon

theorem semistable_of_nonvanishing_semiInvariant (m : ℕ) (hm : 0 < m)
    (f : KingPiece b d P.vertex (P.characterExponents g) m) (hf : f.val.val ρ ≠ 0) :
    (projectiveClassWeight k g).IsSemistable ρ.moduleObj := by
  apply P.semistable_of_block_weights ρ g (P.eval_zero_of_nonvanishing_semiInvariant b g ρ m hm f hf)
  intro U Q hQ hsplit
  exact block_weight_nonpos_of_nonvanishing b _ ρ (P.characterExponents g) hsplit m hm f hf

end EFiniteCharacterizations.VertexRepresentation.SplitBasicVertices
