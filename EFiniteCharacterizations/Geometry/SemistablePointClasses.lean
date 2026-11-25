module

public import EFiniteCharacterizations.Geometry.VertexDimensions
public import EFiniteCharacterizations.Stability.SEquivalence

/-!
# S-equivalence classes on representation varieties

Identifies the quotient of the semistable locus `SemistablePoints` by equality of
Jordan–Hölder factors in the semistable category with the intrinsic set of
S-equivalence classes (`quotientPointFactorsEquiv`), and characterizes E-finiteness
over an algebraically closed field by having at most one S-equivalence class in
every `rep(A, d)` and integral weight (`isEFinite_iff_subsingleton_semistable_point_quotients`).
-/

@[expose] public section

open CategoryTheory
universe u
namespace EFiniteCharacterizations.VertexRepresentation.SplitBasicVertices

variable {k R I : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
    [IsNoetherianRing R] [IsArtinianRing R] [Fintype I] [DecidableEq I]
    (P : SplitBasicVertices k R I) (θ : Weight (FGModuleCat.{u} R))
    (q : simpleIsomorphismClasses R → ℕ)

/-- Points of the fixed-vector variety whose modules are semistable. -/
abbrev SemistablePoints :=
  {ρ : VertexRepresentation (k := k) (q ∘ P.simpleIndex.symm) P.vertex // θ.IsSemistable ρ.moduleObj}

noncomputable def pointFactors (x : P.SemistablePoints θ q) :
    Multiset (Skeleton θ.semistableCategory) := θ.stableFactors ⟨x.val.moduleObj,x.property⟩

theorem range_pointFactors :
    Set.range (P.pointFactors θ q) = sEquivalenceClasses θ (classOfCompositionVector k q) := by
  ext l
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨⟨x.val.moduleObj,x.property⟩,by simpa [Function.comp_def] using P.class_of_point x.val,rfl⟩
  · rintro ⟨X,hc,rfl⟩
    obtain ⟨ρ,⟨e⟩⟩ := P.exists_point_of_class X.obj q hc
    let x : P.SemistablePoints θ q := ⟨ρ, X.property.of_iso e.symm⟩
    exact ⟨x,θ.stableFactors_eq_of_iso (ObjectProperty.isoMk (P := θ.IsSemistable) (X := ⟨x.val.moduleObj,x.property⟩) (Y := X) e)⟩

/-- The quotient of semistable based representations by equality of stable
factors is in bijection with the intrinsic S-equivalence classes. -/
noncomputable def quotientPointFactorsEquiv :
    Quotient (Setoid.ker (P.pointFactors θ q)) ≃
      ↥(sEquivalenceClasses θ (classOfCompositionVector k q)) :=
  (Setoid.quotientKerEquivRange _).trans (Equiv.cast (congrArg (fun s : Set (Multiset (Skeleton θ.semistableCategory)) ↦ ↥s) (P.range_pointFactors θ q)))

theorem isEFinite_iff_subsingleton_semistable_point_quotients :
    IsEFinite R ↔ ∀ (g : ProjectiveClass R) (d : simpleIsomorphismClasses R → ℕ),
      Subsingleton (Quotient (Setoid.ker (P.pointFactors (projectiveClassWeight k g) d))) := by
  rw [isEFinite_iff_subsingleton_sEquivalenceClasses k]
  apply forall_congr'
  intro g
  apply forall_congr'
  intro d
  rw [← Set.subsingleton_coe]
  exact (P.quotientPointFactorsEquiv (projectiveClassWeight k g) d).symm.subsingleton_congr

end EFiniteCharacterizations.VertexRepresentation.SplitBasicVertices
