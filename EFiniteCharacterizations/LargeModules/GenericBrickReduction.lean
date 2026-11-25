module

public import EFiniteCharacterizations.LargeModules.GenericBrick
public import EFiniteCharacterizations.Silting.Reduction.ReductionRank

/-! # Descent of generic bricks through presilting reduction -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]

/-- The action of the reflection algebra on an inverting generic brick
preserves its underlying ground vector space and its endomorphism actions. -/
theorem TwoTerm.PointedReflection.genericBrick {P : TwoTerm R} (A : P.PointedReflection)
    {G : ModuleCat.{u} R} (hG : IsGenericBrick k G) (hi : P.InvertedOn G) :
    ∃ M : ModuleCat.{u} A.Target, IsGenericBrick k M := by
  let := A.moduleOfInverted hi
  let M := ModuleCat.of A.Target G
  have hc (r : R) (x : G) : A.ringMap r • x = r • x := A.moduleOfInverted_compatible hi r x
  let e : G ≃ₗ[k] M :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c x ↦ by
        change algebraMap k R c • x = algebraMap k A.Target c • x
        rw [← (A.algebraMapToTarget k).commutes c]
        exact (hc _ _).symm }
  let forget (p : Module.End A.Target M) : Module.End R G :=
    { toFun := p
      map_add' := p.map_add
      map_smul' := fun r x ↦ (congrArg p (hc r x).symm).trans ((p.map_smul _ _).trans (hc r (p x))) }
  have extend (p : Module.End R G) (b : A.Target) (x : G) : p (b • x) = b • p x := by
    let G' := (ModuleCat.restrictScalars A.ringMap).obj M
    let p' : Module.End R G' :=
      { toFun := p
        map_add' := p.map_add
        map_smul' := fun r x ↦ by
          change p (A.ringMap r • (x : G)) = A.ringMap r • p x
          exact (congrArg p (hc r x)).trans ((p.map_smul r x).trans (hc r (p x)).symm) }
    exact A.map_smul_of_restricted_linear p' b x
  let φ : Module.End R G →+* Module.End A.Target M :=
    { toFun p := { toFun := p, map_add' := p.map_add, map_smul' := extend p }
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  let d : G →ₛₗ[φ] M :=
    { toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have : RingHomSurjective φ := ⟨fun p ↦ ⟨forget p,rfl⟩⟩
  have := hG.endofinite
  refine ⟨M,fun hm ↦ hG.infinite (Module.Finite.equiv e.symm),fun p hp ↦ ?_,
    Module.Finite.of_surjective d Function.surjective_id⟩
  exact hG.invertible (forget p) (fun hz ↦ hp (LinearMap.ext (fun x ↦ show p x = 0 from LinearMap.congr_fun hz x)))

/-- A generic brick inverting a presilting differential of nonzero class
gives a generic brick over an E-finite algebra of strictly smaller rank. -/
theorem IsGenericBrick.exists_smaller_of_inverted [Module.Finite k R]
    (hR : IsEFinite R) {G : ModuleCat.{u} R} (hG : IsGenericBrick k G)
    {P : TwoTerm R} (hp : P.IsPresilting) (hc : P.projectiveClass ≠ 0) (hi : P.InvertedOn G) :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      IsEFinite B ∧ (simpleIsomorphismClasses B).ncard < (simpleIsomorphismClasses R).ncard ∧
      ∃ M : ModuleCat.{u} B, IsGenericBrick k M := by
  let := IsArtinianRing.of_finite k R
  let := IsNoetherianRing.of_finite k R
  obtain ⟨L,e,hL,he⟩ := TwoTerm.exists_finite_pointed_perpendicular k hR P hp
  let A : P.PointedReflection := ⟨L,e,hL,he⟩
  obtain ⟨hef,hr⟩ := A.reduction_invariants k hR hp hc
  exact ⟨A.Target,inferInstance,inferInstance,A.finite_target k,hef,hr,A.genericBrick k hG hi⟩

end EFiniteCharacterizations
