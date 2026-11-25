module

public import EFiniteCharacterizations.Stability.PolystableClasses

/-!
# Uniqueness of S-equivalence classes at fixed weight and dimension vector

Companion characterization of E-finiteness: at a fixed integral weight, linear
independence of the classes of stable bricks means that the dimension vector of a
semistable module uniquely determines its multiset of Jordan–Hölder factors in the
semistable category (`isEFinite_iff_subsingleton_sEquivalenceClasses`).
-/

@[expose] public section

open CategoryTheory

universe u
namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]

noncomputable def Weight.stableFactors (θ : Weight (FGModuleCat.{u} R)) (X : θ.semistableCategory) :
    Multiset (Skeleton θ.semistableCategory) := by
  let W : ObjectProperty (FGModuleCat.{u} R) := θ.IsSemistable
  let : Fact (IsWideClass W) := ⟨θ.isWideClass_semistable⟩
  exact (IsWideClass.exists_intrinsic_factors (W := W) X).choose

open IsWideClass in
theorem Weight.stableFactors_eq_of_iso (θ : Weight (FGModuleCat.{u} R))
    {X Y : θ.semistableCategory} (e : X ≅ Y) : θ.stableFactors X = θ.stableFactors Y := by
  let W : ObjectProperty (FGModuleCat.{u} R) := θ.IsSemistable
  let : Fact (IsWideClass W) := ⟨θ.isWideClass_semistable⟩
  exact ((exists_intrinsic_factors (W := W) X).choose_spec.of_iso e).unique
    (exists_intrinsic_factors (W := W) Y).choose_spec

/-- S-equivalence classes of semistable modules of ambient class c, identified
by their Jordan–Hölder factors in the semistable category. -/
def sEquivalenceClasses (θ : Weight (FGModuleCat.{u} R))
    (c : GrothendieckGroup (FGModuleCat.{u} R)) : Set (Multiset (Skeleton θ.semistableCategory)) :=
  {l | ∃ X : θ.semistableCategory, GrothendieckGroup.of X.obj = c ∧ θ.stableFactors X = l}

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

open IsWideClass in
theorem isEFinite_iff_subsingleton_sEquivalenceClasses :
    IsEFinite R ↔ ∀ (g : ProjectiveClass R) (d : simpleIsomorphismClasses R → ℕ),
      (sEquivalenceClasses (projectiveClassWeight k g) (classOfCompositionVector k d)).Subsingleton := by
  constructor
  · rintro he g d _ ⟨X,hX,rfl⟩ _ ⟨Y,hY,rfl⟩
    let θ := projectiveClassWeight k g
    let W : ObjectProperty (FGModuleCat.{u} R) := θ.IsSemistable
    let : Fact (IsWideClass W) := ⟨θ.isWideClass_semistable⟩
    exact stable_factors_eq_of_isEFinite k he θ X Y (hX.trans hY.symm) _ _
      (IsWideClass.exists_intrinsic_factors (W := W) X).choose_spec
      (IsWideClass.exists_intrinsic_factors (W := W) Y).choose_spec
  · intro h
    by_contra hn
    obtain ⟨g,X,Y,hX,hY,hne,hc⟩ := exists_equalClass_stable_pair_allFields k hn
    let θ := projectiveClassWeight k g
    let W : ObjectProperty (FGModuleCat.{u} R) := θ.IsSemistable
    let : Fact (IsWideClass W) := ⟨θ.isWideClass_semistable⟩
    let U : θ.semistableCategory := ⟨X,hX.isSemistable⟩
    let V : θ.semistableCategory := ⟨Y,hY.isSemistable⟩
    let : Simple U := (θ.isStable_iff_simple U).1 hX
    let : Simple V := (θ.isStable_iff_simple V).1 hY
    obtain ⟨d,hd⟩ := exists_compositionVector_of_module k X
    have he := h g d ⟨U,hd.symm,rfl⟩ ⟨V,hc.symm.trans hd.symm,rfl⟩
    have hU : θ.stableFactors U = {toSkeleton U} :=
      (IsWideClass.exists_intrinsic_factors (W := W) U).choose_spec.eq_singleton_of_simple
    have hV : θ.stableFactors V = {toSkeleton V} :=
      (IsWideClass.exists_intrinsic_factors (W := W) V).choose_spec.eq_singleton_of_simple
    change θ.stableFactors U = θ.stableFactors V at he
    rw [hU,hV] at he
    obtain ⟨e⟩ := toSkeleton_eq_toSkeleton_iff.1 (Multiset.singleton_inj.mp he)
    exact hne ⟨W.ι.mapIso e⟩

end EFiniteCharacterizations
