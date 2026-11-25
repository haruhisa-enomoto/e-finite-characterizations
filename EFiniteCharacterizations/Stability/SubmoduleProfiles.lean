module

public import EFiniteCharacterizations.Stability.BrickWalls
public import Mathlib.Data.Set.Finite.Powerset

/-! # Submodule profiles of bricks -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- The ordinary Grothendieck classes of all submodules, including zero and the whole module. -/
def submoduleProfile (M : FGModuleCat.{u} R) : Set (GrothendieckGroup (FGModuleCat.{u} R)) :=
  {c | ∃ (U : FGModuleCat.{u} R) (i : U ⟶ M), Mono i ∧ GrothendieckGroup.of U = c}

omit [IsNoetherianRing R] in
theorem self_mem_submoduleProfile (M : FGModuleCat.{u} R) :
    GrothendieckGroup.of M ∈ submoduleProfile M := ⟨M, 𝟙 M, inferInstance, rfl⟩

def BrickProfileInjective (R : Type u) [Ring R] [IsNoetherianRing R] : Prop :=
  ∀ X Y : FGModuleCat.{u} R, IsBrick X → IsBrick Y → submoduleProfile X = submoduleProfile Y →
    Nonempty (X ≅ Y)

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

private noncomputable abbrev dim (M : FGModuleCat.{u} R) := Module.finrank k (M.obj : Type u)

private theorem dim_le_of_mono {U X : FGModuleCat.{u} R} (i : U ⟶ X) [Mono i] :
    dim k U ≤ dim k X := by
  have : Module.Finite k (X.obj : Type u) := Module.Finite.trans R _
  exact LinearMap.finrank_le_finrank_of_injective (f := i.hom.hom.restrictScalars k)
    ((FGModuleCat.mono_iff_injective i).mp inferInstance)

private theorem dim_eq_of_class_eq {U X : FGModuleCat.{u} R}
    (he : GrothendieckGroup.of U = GrothendieckGroup.of X) : dim k U = dim k X := by
  have h := congrArg (dimensionWeight (R := R) k) he
  change (dimensionWeight (R := R) k).eval U = (dimensionWeight (R := R) k).eval X at h
  simpa using h

include k in
theorem class_eq_of_submoduleProfile_eq {X Y : FGModuleCat.{u} R}
    (h : submoduleProfile X = submoduleProfile Y) : GrothendieckGroup.of X = GrothendieckGroup.of Y := by
  obtain ⟨U, i, hi, hu⟩ := h ▸ self_mem_submoduleProfile X
  obtain ⟨V, j, hj, hv⟩ := h.symm ▸ self_mem_submoduleProfile Y
  have hd := (dim_eq_of_class_eq k hv).symm.trans_le (dim_le_of_mono k j)
  have : IsIso i := by
    by_contra hn
    exact (not_lt_of_ge (hd.trans_eq (dim_eq_of_class_eq k hu).symm))
      (groundFinrank_lt_of_mono_not_iso k i hn)
  exact hu.symm.trans (GrothendieckGroup.of_eq_of_iso (asIso i))

theorem semistable_iff_profile (θ : Weight (FGModuleCat.{u} R)) (X : FGModuleCat.{u} R) :
    θ.IsSemistable X ↔ θ (GrothendieckGroup.of X) = 0 ∧ ∀ c ∈ submoduleProfile X, θ c ≤ 0 := by
  constructor
  · rintro ⟨hz, h⟩
    refine ⟨hz, ?_⟩
    rintro c ⟨U, i, hi, rfl⟩
    exact h i
  · rintro ⟨hz, h⟩
    exact ⟨hz, fun i _ ↦ h _ ⟨_, i, inferInstance, rfl⟩⟩

variable [IsArtinianRing R]

include k in
theorem brickProfileInjective_of_isEFinite (h : IsEFinite R) : BrickProfileInjective R := by
  intro X Y hx hy he
  apply iso_of_same_integral_semistability_locus k h hx hy
  intro g
  simp only [semistable_iff_profile, class_eq_of_submoduleProfile_eq k he, he]

include k in
theorem isEFinite_iff_prof_inj [Infinite k] : IsEFinite R ↔ BrickProfileInjective R := by
  classical
  refine ⟨brickProfileInjective_of_isEFinite k, fun hinj ↦ ?_⟩
  apply isEFinite_of_finite_brickClassesOfClass k
  intro c
  let d := ((dimensionWeight (R := R) k) c).toNat
  obtain ⟨S, _, hS⟩ := exists_bounded_class_cover (R := R) k d
  choose M he hc hb using fun x : brickClassesOfClass c ↦ x.property
  have hd (x : brickClassesOfClass c) : dim k (M x) = d := by
    dsimp [d]
    rw [← hc x]
    change _ = ((dimensionWeight (R := R) k).eval (M x)).toNat
    simp [dim]
  let T := 𝒫 (S : Set (GrothendieckGroup (FGModuleCat.{u} R)))
  have : Finite T := S.finite_toSet.powerset
  let f (x : brickClassesOfClass c) : T := ⟨submoduleProfile (M x), by
    rintro _ ⟨U, i, _, rfl⟩
    exact hS U ((dim_le_of_mono k i).trans_eq (hd x))⟩
  apply Finite.of_injective f
  intro x y hxy
  obtain ⟨e⟩ := hinj _ _ (hb x) (hb y) (congrArg Subtype.val hxy)
  exact Subtype.ext ((he x).symm.trans ((congr_toSkeleton_of_iso e).trans (he y)))

end EFiniteCharacterizations
