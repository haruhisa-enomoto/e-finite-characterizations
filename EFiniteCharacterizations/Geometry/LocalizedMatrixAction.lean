module

public import EFiniteCharacterizations.Geometry.TautologicalRepresentation
public import EFiniteCharacterizations.LinearAlgebra.SimpleModuleDensity
public import EFiniteCharacterizations.RingEpimorphisms.GeometricLocalizationCharts

/-! # Matrix actions of a localization on geometric stable modules -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

variable {k F R B C : Type u} [Field k] [Field F] [IsAlgClosed F] [Algebra k F]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring B] [Algebra k B] [Ring C] [Algebra F C]

/-- A stable geometric module inverting the ground differential admits a
compatible based action of the ground localization with full geometric span. -/
theorem exists_full_span_localized_action [IsNoetherianRing (ExtendedAlgebra k F R)]
    (P : TwoTerm R) (f : R →ₐ[k] B)
    (hf : IsUniversalLocalization (fun _ : Unit ↦ P) f.toRingHom)
    (g : ExtendedAlgebra k F R →ₐ[F] C)
    (hg : IsUniversalLocalization (fun _ : Unit ↦ P.induce (algebraInclusion k F R).toRingHom) g.toRingHom)
    (X : FGModuleCat.{u} (ExtendedAlgebra k F R)) {n : Type*} [Fintype n] [DecidableEq n]
    (v : Module.Basis n F (X.obj : Type u))
    (hs : ((P.induce (algebraInclusion k F R).toRingHom).eulerWeight F).IsStable X)
    (hi : (P.induce (algebraInclusion k F R).toRingHom).InvertedOn X.obj) :
    ∃ ρ : B →ₐ[k] Matrix n n F,
      (∀ r, ρ (f r) = basedAction v (1 ⊗ₜ[k] r)) ∧ Submodule.span F (Set.range ρ) = ⊤ := by
  let := Algebra.compHom C (algebraMap k F)
  let : IsScalarTower k F C := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨p,hp,hspan⟩ := exists_spanning_ground_action k F f hf g hg
  obtain ⟨m,hsimp,ht,hm⟩ := hg.exists_simple_action F _ g X hs hi
  let := m
  let : IsSimpleModule C X := hsimp
  let : IsScalarTower F C X := ht
  have : Module.Finite F (X.obj : Type u) := Module.Finite.trans (ExtendedAlgebra k F R) _
  let α := (LinearMap.toMatrixAlgEquiv v).toAlgHom.comp (Algebra.lsmul F F (X.obj : Type u) (A := C))
  let ρ := (α.restrictScalars k).comp p
  refine ⟨ρ,?_,?_⟩
  · intro r
    change α (p (f r)) = _
    rw [hp]
    apply congrArg (LinearMap.toMatrixAlgEquiv v)
    exact LinearMap.ext (hm _)
  · have hsur : Function.Surjective α :=
      (LinearMap.toMatrixAlgEquiv v).surjective.comp (simple_action_surjective (F := F) (B := C) (M := X))
    have he := congrArg (Submodule.map α.toLinearMap) hspan
    rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr hsur] at he
    rw [← he]
    congr 1
    ext z
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨_,⟨b,rfl⟩,rfl⟩
    · rintro ⟨_,⟨b,rfl⟩,rfl⟩
      exact ⟨b,rfl⟩

end EFiniteCharacterizations.FieldExtension
