module

public import EFiniteCharacterizations.GrothendieckGroups.GrothendieckGroup
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Simple

/-! # Integral weights and stable objects -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace EFiniteCharacterizations

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An integer-valued additive weight on objects. -/
abbrev Weight (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :=
  GrothendieckGroup C →+ ℤ

namespace Weight

/-- Evaluation on the class of an object. -/
def eval (θ : Weight C) (X : C) : ℤ := θ (GrothendieckGroup.of X)

theorem eval_shortExact (θ : Weight C) (S : ShortComplex C) (hS : S.ShortExact) :
    θ.eval S.X₂ = θ.eval S.X₁ + θ.eval S.X₃ := by
  unfold eval
  rw [GrothendieckGroup.of_shortExact S hS, map_add]

theorem eval_isZero (θ : Weight C) {X : C} (hX : IsZero X) : θ.eval X = 0 := by
  rw [eval, GrothendieckGroup.of_isZero hX, map_zero]

theorem eval_eq_of_isIso (θ : Weight C) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    θ.eval X = θ.eval Y := by
  rw [eval, eval, GrothendieckGroup.of_eq_of_iso (asIso f)]

/-- A semistable object has weight zero and all its subobjects have nonpositive weight. -/
def IsSemistable (θ : Weight C) (X : C) : Prop :=
  θ.eval X = 0 ∧ ∀ {U : C} (i : U ⟶ X) [Mono i], θ.eval U ≤ 0

/-- A stable object is nonzero, has weight zero and has negative weight on every
proper nonzero subobject. -/
def IsStable (θ : Weight C) (X : C) : Prop :=
  ¬ IsZero X ∧ θ.eval X = 0 ∧
    ∀ {U : C} (i : U ⟶ X) [Mono i], ¬ IsZero U → ¬ IsIso i → θ.eval U < 0

theorem IsStable.of_iso {θ : Weight C} {X Y : C} (hX : θ.IsStable X) (e : X ≅ Y) :
    θ.IsStable Y := by
  refine ⟨fun hz ↦ hX.1 (hz.of_iso e), (θ.eval_eq_of_isIso e.hom).symm.trans hX.2.1, ?_⟩
  intro U i _ hU hi
  apply hX.2.2 (i ≫ e.inv) hU
  intro hc
  apply hi
  have : IsIso ((i ≫ e.inv) ≫ e.hom) := inferInstance
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using this

theorem IsStable.isSemistable {θ : Weight C} {X : C} (h : θ.IsStable X) :
    θ.IsSemistable X := by
  classical
  refine ⟨h.2.1, ?_⟩
  intro U i _
  by_cases hz : IsZero U
  · rw [θ.eval_isZero hz]
  by_cases hi : IsIso i
  · rw [θ.eval_eq_of_isIso i, h.2.1]
  exact (h.2.2 i hz hi).le

/-- At weight zero the stable objects are precisely the ordinary simples. -/
theorem isStable_zero_iff_simple (X : C) : (0 : Weight C).IsStable X ↔ Simple X := by
  constructor
  · intro h
    constructor
    intro U i _
    constructor
    · intro hi hz
      have hzX : 𝟙 X = 0 := by
        calc
          𝟙 X = inv i ≫ i := (IsIso.inv_hom_id i).symm
          _ = inv i ≫ (0 : U ⟶ X) := congrArg (fun m ↦ inv i ≫ m) hz
          _ = 0 := comp_zero
      exact h.1 ((IsZero.iff_id_eq_zero X).mpr hzX)
    · intro hz
      by_contra hi
      have hn : ¬ IsZero U := fun he ↦ hz (he.eq_of_src _ _)
      exact (lt_irrefl (0 : ℤ)) (h.2.2 i hn hi)
  · intro h
    refine ⟨Simple.not_isZero X, rfl, ?_⟩
    intro U i _ hU hi
    have hz : i = 0 := by
      by_contra hn
      exact hi ((Simple.mono_isIso_iff_nonzero i).2 hn)
    have hzU : 𝟙 U = 0 := by
      rw [← cancel_mono i, Category.id_comp, zero_comp, hz]
    exact (hU ((IsZero.iff_id_eq_zero U).mpr hzU)).elim

/-- A nonzero map between stable objects of the same weight is invertible. -/
theorem isIso_of_nonzero {θ : Weight C} {X Y : C} (hX : θ.IsStable X)
    (hY : θ.IsStable Y) (f : X ⟶ Y) (hf : f ≠ 0) : IsIso f := by
  classical
  let p := Abelian.factorThruImage f
  let i := Abelian.image.ι f
  have hp : p ≠ 0 := by
    intro h
    apply hf
    rw [← Abelian.image.fac f, ← show p = Abelian.factorThruImage f from rfl, h, zero_comp]
  have hi_nonzero : ¬ IsZero (Abelian.image f) :=
    fun h ↦ hp (h.eq_of_tgt p 0)
  have hk_not_iso : ¬ IsIso (kernel.ι p) := by
    intro h
    apply hp
    rw [← cancel_epi (kernel.ι p), kernel.condition, comp_zero]
  let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p)
    (by dsimp [S]; infer_instance) (by dsimp [S, p]; infer_instance)
  have hsum : θ.eval X = θ.eval (kernel p) + θ.eval (Abelian.image f) :=
    θ.eval_shortExact S hS
  have hk : θ.eval (kernel p) ≤ 0 := by
    by_cases hz : IsZero (kernel p)
    · rw [θ.eval_isZero hz]
    · exact (hX.2.2 (kernel.ι p) hz hk_not_iso).le
  have hi_iso : IsIso i := by
    by_contra h
    have hneg := hY.2.2 i hi_nonzero h
    have hx := hX.2.1
    omega
  have hi_weight : θ.eval (Abelian.image f) = 0 :=
    (θ.eval_eq_of_isIso i).trans hY.2.1
  have hk_zero : IsZero (kernel p) := by
    by_contra h
    have hneg := hX.2.2 (kernel.ι p) h hk_not_iso
    have hx := hX.2.1
    omega
  have : Mono p := Abelian.mono_of_kernel_ι_eq_zero _ (hk_zero.eq_of_src _ _)
  have : IsIso p := isIso_of_mono_of_epi p
  rw [← Abelian.image.fac f]
  exact inferInstance

end Weight

theorem stable_nsmul_iff {C : Type*} [Category* C] [Abelian C]
    (θ : Weight C) (X : C) {p : ℕ} (hp : 0 < p) : (p • θ).IsStable X ↔ θ.IsStable X := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  simp only [Weight.IsStable, Weight.eval, AddMonoidHom.nsmul_apply, nsmul_eq_mul,
    mul_eq_zero, hp'.ne', false_or, Int.mul_neg_iff, hp', not_lt_of_ge hp'.le, false_and, true_and, or_false]

end EFiniteCharacterizations
