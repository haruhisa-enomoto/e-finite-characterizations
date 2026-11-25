module

public import EFiniteCharacterizations.Presentations.ProjectiveHomWeight
public import EFiniteCharacterizations.Stability.SemistableExact

/-! # Stable subobjects of nonzero semistable modules -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

include k in
/-- A proper submodule of a finite module has smaller ground dimension. -/
theorem groundFinrank_lt_of_mono_not_iso {X Y : FGModuleCat.{u} R}
    (i : X ⟶ Y) [Mono i] (hi : ¬ IsIso i) :
    Module.finrank k (X.obj : Type u) < Module.finrank k (Y.obj : Type u) := by
  have : Module.Finite k (Y.obj : Type u) := Module.Finite.trans R (Y.obj : Type u)
  let a := i.hom.hom.restrictScalars k
  have hinj : Function.Injective a := (FGModuleCat.mono_iff_injective i).1 inferInstance
  have hproper : LinearMap.range a ≠ ⊤ := by
    intro h
    have hs : Function.Surjective a := LinearMap.range_eq_top.1 h
    exact hi ((FGModuleCat.isIso_iff_bijective i).2 ⟨hinj, hs⟩)
  exact (LinearMap.finrank_range_of_inj hinj).symm.trans_lt (Submodule.finrank_lt hproper)

include k in
/-- A nonzero semistable module admits a stable subobject at the same weight. -/
theorem Weight.IsSemistable.exists_stable_subobject {θ : Weight (FGModuleCat.{u} R)}
    {M : FGModuleCat.{u} R} (hM : θ.IsSemistable M) (hn : ¬ IsZero M) :
    ∃ (S : FGModuleCat.{u} R) (i : S ⟶ M), Mono i ∧ θ.IsStable S := by
  classical
  let A (n : ℕ) := ∃ (S : FGModuleCat.{u} R) (i : S ⟶ M), Mono i ∧ ¬ IsZero S ∧
    θ.eval S = 0 ∧ Module.finrank k (S.obj : Type u) = n
  have hA : ∃ n, A n := ⟨_, M, 𝟙 M, inferInstance, hn, hM.1, rfl⟩
  obtain ⟨S, i, hi, hS, hz, hdim⟩ := Nat.find_spec hA
  refine ⟨S, i, hi, hS, hz, ?_⟩
  intro U j _ hU hj
  have hweak := hM.2 (j ≫ i)
  apply lt_of_le_of_ne hweak
  intro he
  have ha : A (Module.finrank k (U.obj : Type u)) := ⟨U, j ≫ i, inferInstance, hU, he, rfl⟩
  exact (not_lt_of_ge (Nat.find_min' hA ha)) ((groundFinrank_lt_of_mono_not_iso k j hj).trans_eq hdim)

end EFiniteCharacterizations
