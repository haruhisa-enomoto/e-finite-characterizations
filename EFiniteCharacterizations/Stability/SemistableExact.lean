module

public import EFiniteCharacterizations.Stability.Weights

/-! # Subobjects and quotients at one semistable weight -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace EFiniteCharacterizations.Weight

variable {C : Type*} [Category C] [Abelian C] {θ : Weight C}

/-- Semistability can also be tested by nonnegative weight on all quotients. -/
theorem isSemistable_iff_quotients (X : C) :
    θ.IsSemistable X ↔ θ.eval X = 0 ∧ ∀ {Q : C} (q : X ⟶ Q) [Epi q], 0 ≤ θ.eval Q := by
  constructor
  · rintro ⟨hzero, hsub⟩
    refine ⟨hzero, ?_⟩
    intro Q q _
    let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
    have hS : S.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel q)
      (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
    have hsum := θ.eval_shortExact S hS
    change θ.eval X = θ.eval (kernel q) + θ.eval Q at hsum
    have hn := hsub (kernel.ι q)
    omega
  · rintro ⟨hzero, hquot⟩
    refine ⟨hzero, ?_⟩
    intro U i _
    let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have hS : S.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i)
      (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
    have hsum := θ.eval_shortExact S hS
    change θ.eval X = θ.eval U + θ.eval (cokernel i) at hsum
    have hp := hquot (cokernel.π i)
    omega

theorem IsSemistable.of_mono_of_eval_zero {U X : C} (hX : θ.IsSemistable X)
    (i : U ⟶ X) [Mono i] (hU : θ.eval U = 0) : θ.IsSemistable U :=
  ⟨hU, fun j ↦ hX.2 (j ≫ i)⟩

theorem IsSemistable.of_epi_of_eval_zero {X Q : C} (hX : θ.IsSemistable X)
    (q : X ⟶ Q) [Epi q] (hQ : θ.eval Q = 0) : θ.IsSemistable Q :=
  (isSemistable_iff_quotients Q).2
    ⟨hQ, fun p ↦ ((isSemistable_iff_quotients X).1 hX).2 (q ≫ p)⟩

theorem IsSemistable.kernel_of_epi {X Y : C} (hX : θ.IsSemistable X)
    (hY : θ.IsSemistable Y) (f : X ⟶ Y) [Epi f] : θ.IsSemistable (kernel f) := by
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel f)
    (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
  have hsum := θ.eval_shortExact S hS
  change θ.eval X = θ.eval (kernel f) + θ.eval Y at hsum
  exact hX.of_mono_of_eval_zero (kernel.ι f) (by rw [hX.1, hY.1, add_zero] at hsum; exact hsum.symm)

theorem IsSemistable.cokernel_of_mono {X Y : C} (hX : θ.IsSemistable X)
    (hY : θ.IsSemistable Y) (f : X ⟶ Y) [Mono f] : θ.IsSemistable (cokernel f) := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel f)
    (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
  have hsum := θ.eval_shortExact S hS
  change θ.eval Y = θ.eval X + θ.eval (cokernel f) at hsum
  exact hY.of_epi_of_eval_zero (cokernel.π f) (by rw [hX.1, hY.1, zero_add] at hsum; exact hsum.symm)

theorem IsSemistable.image {X Y : C} (hX : θ.IsSemistable X)
    (hY : θ.IsSemistable Y) (f : X ⟶ Y) : θ.IsSemistable (Abelian.image f) := by
  have hlo := ((isSemistable_iff_quotients X).1 hX).2 (Abelian.factorThruImage f)
  have hhi := hY.2 (Abelian.image.ι f)
  exact hY.of_mono_of_eval_zero (Abelian.image.ι f) (le_antisymm hhi hlo)

theorem IsSemistable.of_iso {X Y : C} (hX : θ.IsSemistable X) (e : X ≅ Y) :
    θ.IsSemistable Y :=
  ⟨(θ.eval_eq_of_isIso e.hom).symm.trans hX.1, fun i ↦ hX.2 (i ≫ e.inv)⟩

/-- Semistable objects at a fixed weight are closed under extensions. -/
theorem IsSemistable.of_shortExact {T : ShortComplex C} (hT : T.ShortExact)
    (h₁ : θ.IsSemistable T.X₁) (h₃ : θ.IsSemistable T.X₃) : θ.IsSemistable T.X₂ := by
  refine ⟨by rw [θ.eval_shortExact T hT, h₁.1, h₃.1, add_zero], ?_⟩
  intro U i _
  let p := Abelian.factorThruImage (i ≫ T.g)
  let j := Abelian.image.ι (i ≫ T.g)
  have hfac : p ≫ j = i ≫ T.g := Abelian.image.fac _
  have hz : (kernel.ι p ≫ i) ≫ T.g = 0 := calc
    (kernel.ι p ≫ i) ≫ T.g = kernel.ι p ≫ (i ≫ T.g) := Category.assoc _ _ _
    _ = kernel.ι p ≫ (p ≫ j) := congrArg (kernel.ι p ≫ ·) hfac.symm
    _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp]
  let l := KernelFork.IsLimit.lift' hT.fIsKernel (kernel.ι p ≫ i) hz
  have : Mono l.val := mono_of_mono_fac l.property
  have hl := h₁.2 l.val
  have hr := h₃.2 j
  let E := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  have hE : E.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p)
    (by dsimp [E]; infer_instance) (by dsimp [E]; infer_instance)
  change θ.eval (kernel p) ≤ 0 at hl
  exact (θ.eval_shortExact E hE).trans_le (add_nonpos hl hr)

/-- Semistable objects at the same weight are closed under binary biproducts. -/
theorem IsSemistable.biprod {X Y : C} [HasBinaryBiproduct X Y] (hX : θ.IsSemistable X)
    (hY : θ.IsSemistable Y) : θ.IsSemistable (X ⊞ Y) :=
  IsSemistable.of_shortExact (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact hX hY

/-- A nonzero map from a semistable object to a stable object at the same
weight is epic. -/
theorem epi_of_isSemistable_of_isStable {X Y : C} (hX : θ.IsSemistable X) (hY : θ.IsStable Y)
    (f : X ⟶ Y) (hf : f ≠ 0) : Epi f := by
  let I := Abelian.image f
  let i := Abelian.image.ι f
  have hI : ¬ IsZero I := by
    intro hz
    have hz' : i = 0 := hz.eq_of_src _ _
    apply hf
    rw [← Abelian.image.fac f]
    exact (congrArg (Abelian.factorThruImage f ≫ ·) hz').trans comp_zero
  have hz := (hX.image hY.isSemistable f).1
  have hi : IsIso i := by
    by_contra hn
    exact (lt_irrefl (0 : ℤ)) (hz ▸ hY.2.2 i hI hn)
  rw [← Abelian.image.fac f]
  exact epi_comp (Abelian.factorThruImage f) i

/-- A nonzero map from a stable object to a semistable object at the same
weight is monic. -/
theorem mono_of_isStable_of_isSemistable {X Y : C} (hX : θ.IsStable X) (hY : θ.IsSemistable Y)
    (f : X ⟶ Y) (hf : f ≠ 0) : Mono f := by
  let p := Abelian.factorThruImage f
  have hp : p ≠ 0 := by
    intro hz
    apply hf
    rw [← Abelian.image.fac f]
    exact (congrArg (· ≫ Abelian.image.ι f) hz).trans zero_comp
  have hk := hX.isSemistable.kernel_of_epi (hX.isSemistable.image hY f) p
  have hnot : ¬ IsIso (kernel.ι p) := fun h ↦ hp (zero_of_epi_comp (kernel.ι p) (kernel.condition p))
  have hzero : IsZero (kernel p) := by
    by_contra hn
    exact (lt_irrefl (0 : ℤ)) (hk.1 ▸ hX.2.2 (kernel.ι p) hn hnot)
  have : Mono p := Abelian.mono_of_kernel_ι_eq_zero _ (hzero.eq_of_src _ _)
  rw [← Abelian.image.fac f]
  exact mono_comp p (Abelian.image.ι f)

end EFiniteCharacterizations.Weight
