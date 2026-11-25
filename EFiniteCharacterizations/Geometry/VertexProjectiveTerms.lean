module

public import EFiniteCharacterizations.Geometry.StableLocalization
public import EFiniteCharacterizations.Geometry.VertexProjectives
public import EFiniteCharacterizations.Presentations.ProjectiveClassSeparation

/-! # Two-term presentations on explicit sums of vertex projectives -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra
universe u
namespace EFiniteCharacterizations.VertexRepresentation.SplitBasicVertices

variable {k R I : Type u} [Field k] [Ring R] [Algebra k R] [Fintype I] [DecidableEq I]
    (P : SplitBasicVertices k R I)
variable {S : Type u} [Fintype S] [DecidableEq S] (s : S → I)

/-- The direct sum of the vertex projectives listed by s. -/
noncomputable def vertexTerm : FiniteProjective R := by
  let V j := vertexIdeal P.vertex (s j)
  let inc : (∀ j, V j) →ₗ[R] (S → R) := LinearMap.piMap (fun j ↦ (V j).subtype)
  let ret : (S → R) →ₗ[R] (∀ j, V j) := LinearMap.piMap
    (fun j ↦ (LinearMap.toSpanSingleton R R (P.vertex (s j))).rangeRestrict)
  exact ⟨FGModuleCat.of R (∀ j, V j),Module.Projective.of_split inc ret
    (LinearMap.ext fun z ↦ funext fun j ↦ Subtype.ext
      (vertexIdeal_mul_idempotent _ _ (P.complete.idem _) (z j)))⟩

noncomputable def vertexTermHomEquiv (M : FGModuleCat.{u} R) :
    ((P.vertexTerm s).val ⟶ M) ≃ₗ[k] ∀ j, vertexPart (k := k) P.vertex M (s j) :=
  (finiteModuleHomLinearEquiv k _ M) ≪≫ₗ (LinearMap.lsum R (fun j ↦ vertexIdeal P.vertex (s j)) k).symm
    ≪≫ₗ LinearEquiv.piCongrRight (fun j ↦ vertexIdealHomEquiv P.vertex (s j) (P.complete.idem _) M)

variable [IsNoetherianRing R] [Module.Finite k R]

theorem characterExponents_vertexTerm :
    P.characterExponents (ProjectiveClass.of (P.vertexTerm s)) =
      fun i ↦ (vertexMultiplicity s i : ℤ) := by
  funext i
  let M := (fromSkeleton _).obj (P.simpleIndex.symm i).val
  let : Module.Finite k M := Module.Finite.trans R _
  let := (P.vertexTerm s).property
  change (projectiveClassWeight k (ProjectiveClass.of (P.vertexTerm s))).eval M = _
  rw [projectiveClassWeight_of,projectiveHomWeight_eval,homFinrank_eq_finrank,
    (P.vertexTermHomEquiv s M).finrank_eq,Module.finrank_pi_fintype]
  simp [M,P.simple_dimension,vertexMultiplicity,eq_comm]

theorem characterExponents_injective : Function.Injective P.characterExponents := by
  intro a b h
  apply ProjectiveClass.eq_of_eval_eq_on_simples k
  intro M hM
  let j : simpleIsomorphismClasses R := ⟨toSkeleton M,M,rfl,hM⟩
  have he := congrFun h (P.simpleIndex j)
  simp only [characterExponents,Equiv.symm_apply_apply] at he
  let f := fromSkeletonToSkeletonIso M
  exact ((projectiveClassWeight k a).eval_eq_of_isIso f.hom).symm.trans
    (he.trans ((projectiveClassWeight k b).eval_eq_of_isIso f.hom))

/-- A vertex list containing precisely the prescribed number of copies. -/
abbrev vertexCopies (n : I → ℕ) := Σ i, Fin (n i)

theorem vertexMultiplicity_copies (n : I → ℕ) (i : I) :
    vertexMultiplicity (Sigma.fst : vertexCopies n → I) i = n i := by
  unfold vertexMultiplicity
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [hji]
  · simp

/-- For the inversion construction one may start with the positive and
negative parts of the character, with all summands in explicit coordinates. -/
noncomputable def vertexPresentation (g : ProjectiveClass R) : TwoTerm R :=
  let w := P.characterExponents g
  let A := P.vertexTerm (Sigma.fst : vertexCopies (fun i ↦ (-w i).toNat) → I)
  let B := P.vertexTerm (Sigma.fst : vertexCopies (fun i ↦ (w i).toNat) → I)
  ⟨A.val,B.val,A.property,B.property,0⟩

theorem projectiveClass_vertexPresentation (g : ProjectiveClass R) :
    (P.vertexPresentation g).projectiveClass = g := by
  apply P.characterExponents_injective
  funext i
  let w := P.characterExponents g
  let s := (Sigma.fst : vertexCopies (fun i ↦ (-w i).toNat) → I)
  let t := (Sigma.fst : vertexCopies (fun i ↦ (w i).toNat) → I)
  let M := (fromSkeleton _).obj (P.simpleIndex.symm i).val
  change (projectiveClassWeight k (ProjectiveClass.of (P.vertexTerm t) -
    ProjectiveClass.of (P.vertexTerm s))).eval M = w i
  simp only [Weight.eval,map_sub,AddMonoidHom.sub_apply]
  change P.characterExponents (ProjectiveClass.of (P.vertexTerm t)) i -
    P.characterExponents (ProjectiveClass.of (P.vertexTerm s)) i = w i
  rw [P.characterExponents_vertexTerm,P.characterExponents_vertexTerm]
  simp only [s,t,vertexMultiplicity_copies]
  omega

/-- E-infiniteness yields a common stable chart whose projective terms are
copies of the explicit vertex sums for a single weight. -/
theorem exists_infinite_vertex_chart [IsAlgClosed k] (hn : ¬ IsEFinite R) :
    ∃ (g : ProjectiveClass R) (n : ℕ)
      (p : Fin n → Fin n → ((P.vertexPresentation g).source ⟶ (P.vertexPresentation g).target))
      (c : GrothendieckGroup (FGModuleCat.{u} R)),
      (((P.vertexPresentation g).blockDifferentialOnCopies p).stableInvertingClasses k ∩
        stableClassesOfClass (projectiveClassWeight k g) c).Infinite := by
  classical
  let := IsArtinianRing.of_finite k R
  obtain ⟨c,g,hc⟩ := exists_infinite_stableClassesOfClass_at_projectiveWeight_of_not_isEFinite k hn
  let A := P.vertexPresentation g
  have hg : A.projectiveClass = g := P.projectiveClass_vertexPresentation g
  have hw : projectiveClassWeight k g = A.eulerWeight k := hg ▸ A.projectiveClassWeight_eq_eulerWeight k
  let J := Σ t : ℕ, (0 < t) ×' (Fin t → Fin t → (A.source ⟶ A.target))
  let Q (j : J) := A.blockDifferentialOnCopies j.2.2
  obtain ⟨j,hj⟩ := exists_infinite_fixed_class_chart_of_pointwise_inversion k _ c hc Q
    (fun j M hM ↦ by
      rw [← (Q j).projectiveClassWeight_eq_eulerWeight k]
      change (projectiveClassWeight k (A.blockDifferentialOnCopies j.2.2).projectiveClass).IsStable M
      rw [TwoTerm.projectiveClass_blockDifferentialOnCopies,map_nsmul,hg]
      exact (stable_nsmul_iff _ M j.2.1).2 hM)
    (fun M _ hM ↦ by
      let n := (homFinrank k A.target M)^2
      obtain ⟨p,hp⟩ := A.exists_inverting_power_of_stable k M (hw ▸ hM) (n+1) (Nat.lt_succ_self n)
      exact ⟨⟨n+1,Nat.succ_pos _,p⟩,hp⟩)
  exact ⟨g,j.1,j.2.2,c,hj⟩

end EFiniteCharacterizations.VertexRepresentation.SplitBasicVertices
