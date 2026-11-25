module

public import EFiniteCharacterizations.Geometry.KingSplitting
public import EFiniteCharacterizations.Geometry.KingEvaluationDensity

/-! # Splitting composition series in a fixed vertex representation variety -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace EFiniteCharacterizations

variable {C : Type*} [Category* C] [Abelian C]

/-- Adjoining a fixed summand to the middle and quotient of an extension. -/
noncomputable def ExtensionSequence.addRight {U X Q : C} (s : ExtensionSequence U X Q) (Z : C) :
    ExtensionSequence U (X ⊞ Z) (Q ⊞ Z) := by
  let i := s.i ≫ biprod.inl (Y := Z)
  let p := biprod.map s.p (𝟙 Z)
  have hi : Mono i := by dsimp [i]; infer_instance
  have hp : Epi p := by dsimp [p]; infer_instance
  have he : i ≫ p = 0 := by simp [i,p,← Category.assoc s.i s.p,s.w]
  let T := ShortComplex.mk i p he
  refine ⟨i,p,he,ShortComplex.ShortExact.mk' (T.exact_of_f_is_kernel ?_) hi hp⟩
  apply KernelFork.IsLimit.ofι'
  intro W h hh
  change h ≫ p = 0 at hh
  have h₁ : (h ≫ biprod.fst) ≫ s.p = 0 := by
    simpa [p,Category.assoc] using congrArg (fun f ↦ f ≫ biprod.fst) hh
  have h₂ : h ≫ biprod.snd = 0 := by
    simpa [p,Category.assoc] using congrArg (fun f ↦ f ≫ biprod.snd) hh
  let F := KernelFork.ofι (h ≫ biprod.fst) h₁
  refine ⟨s.shortExact.fIsKernel.lift F, biprod.hom_ext _ _ ?_ ?_⟩
  · simpa [T,i,F,Category.assoc] using s.shortExact.fIsKernel.fac F WalkingParallelPair.zero
  · simp [T,i,h₂]

namespace VertexRepresentation.SplitBasicVertices

universe u
variable {k R I J : Type u} [Field k] [Infinite k] [Ring R] [Algebra k R] [Module.Finite k R]
    [IsNoetherianRing R] [IsArtinianRing R] [Fintype I] [DecidableEq I] [Fintype J]
    (P : SplitBasicVertices k R I) (b : Module.Basis J k R) {d : I → ℕ} (g : ProjectiveClass R)

omit [Infinite k] [Fintype J] in
open IsWideClass in
/-- Every semistable representation degenerates to a polystable one by a finite
sequence of weight-zero degenerations on the same vertex spaces. -/
theorem exists_polystable_degeneration (η : VertexRepresentation (k := k) d P.vertex)
    (hη : (projectiveClassWeight k g).IsSemistable η.moduleObj) :
    ∃ ξ : VertexRepresentation (k := k) d P.vertex, (projectiveClassWeight k g).IsPolystable ξ.moduleObj ∧
      Relation.ReflTransGen (WeightZeroDegeneration b (P.characterExponents g)) η ξ := by
  let θ := projectiveClassWeight k g
  let W : ObjectProperty (FGModuleCat.{u} R) := θ.IsSemistable
  let : Fact (IsWideClass W) := ⟨θ.isWideClass_semistable⟩
  let X : W.FullSubcategory := ⟨_,hη⟩
  obtain ⟨m,hm⟩ := exists_intrinsic_factors X
  have aux {Y : W.FullSubcategory} {n} (hn : HasCompositionFactors Y n) :
      ∀ (l : List (stableClasses θ)) (ρ : VertexRepresentation (k := k) d P.vertex),
        (Y.obj ⊞ θ.stableSum l ≅ ρ.moduleObj) →
        ∃ ξ : VertexRepresentation (k := k) d P.vertex, θ.IsPolystable ξ.moduleObj ∧
          Relation.ReflTransGen (WeightZeroDegeneration b (P.characterExponents g)) ρ ξ := by
    intro l ρ e
    induction hn generalizing l ρ with
    | zero hz =>
      have hz' := W.ι.map_isZero hz
      exact ⟨ρ,⟨l,⟨(isoZeroBiprod hz') ≪≫ e⟩⟩,.refl⟩
    | @cons S Y Q n s hs hq ih =>
      let T := (ShortComplex.mk s.i s.p s.w).map W.ι
      have ht : T.ShortExact := s.shortExact.map_of_exact _
      let row : ExtensionSequence S.obj Y.obj Q.obj := ⟨T.f,T.g,T.zero,ht⟩
      let row' := row.addRight (θ.stableSum l)
      let T' := ShortComplex.mk row'.i row'.p row'.w
      obtain ⟨ξ,⟨eξ⟩,he⟩ := exists_split_point_degeneration b P T' row'.shortExact ρ e g S.property.1
      have hS := (θ.isStable_iff_simple S).2 hs
      let a : stableClasses θ := ⟨toSkeleton S.obj,hS.of_iso (fromSkeletonToSkeletonIso _).symm⟩
      let swap : Q.obj ⊞ θ.stableSum (a :: l) ≅ S.obj ⊞ (Q.obj ⊞ θ.stableSum l) :=
        biprod.mapIso (Iso.refl _) (biprod.mapIso (fromSkeletonToSkeletonIso _) (Iso.refl _)) ≪≫
        (biprod.associator _ _ _).symm ≪≫ biprod.mapIso (biprod.braiding _ _) (Iso.refl _) ≪≫
        biprod.associator _ _ _
      obtain ⟨p,hp,hpe⟩ := ih (a :: l) ξ (swap ≪≫ eξ.symm)
      exact ⟨p,hp,hpe.head he⟩
  exact aux hm [] η (isoBiprodZero (isZero_zero _)).symm

open IsWideClass in
/-- Every semistable representation has the evaluation ideal of a polystable
representation on the same prescribed vertex spaces. -/
theorem exists_polystable_same_evaluation (η : VertexRepresentation (k := k) d P.vertex)
    (hη : (projectiveClassWeight k g).IsSemistable η.moduleObj) :
    ∃ ξ : VertexRepresentation (k := k) d P.vertex, (projectiveClassWeight k g).IsPolystable ξ.moduleObj ∧
      kingEvaluationIdeal b (P.characterExponents g) ξ = kingEvaluationIdeal b (P.characterExponents g) η := by
  obtain ⟨ξ,hξ,h⟩ := P.exists_polystable_degeneration b g η hη
  refine ⟨ξ,hξ,?_⟩
  clear hξ
  induction h with
  | refl => rfl
  | tail _ h ih => exact (h.evaluation_eq b _).trans ih

/-- E-finiteness implies the King closed-point condition for all projective
weights and all vertex dimension vectors in a split basic presentation. -/
theorem atMostOneKingClosedPoint_of_isEFinite (hR : IsEFinite R) :
    P.atMostOneKingClosedPoint b d g := by
  rw [P.atMostOneKingClosedPoint_iff_evaluationPoints]
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  obtain ⟨m,hm,f,hf⟩ := hx
  obtain ⟨n,hn,q,hq⟩ := hy
  obtain ⟨X,hX,eX⟩ := P.exists_polystable_same_evaluation b g x
    (P.semistable_of_nonvanishing_semiInvariant b x g m hm f hf)
  obtain ⟨Y,hY,eY⟩ := P.exists_polystable_same_evaluation b g y
    (P.semistable_of_nonvanishing_semiInvariant b y g n hn q hq)
  obtain ⟨e⟩ := (isEFinite_iff_unique_polystable_class k).1 hR g _ _ hX hY
    ((P.class_of_point X).trans (P.class_of_point Y).symm)
  exact ProjectiveSpectrum.ext (eX.symm.trans ((kingEvaluationIdeal_eq_of_iso b _ e).trans eY))

end VertexRepresentation.SplitBasicVertices

end EFiniteCharacterizations
