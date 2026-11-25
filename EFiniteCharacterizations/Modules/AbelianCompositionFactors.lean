module

public import EFiniteCharacterizations.GrothendieckGroups.GrothendieckGroup
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Skeletal

/-! # Composition factors in a length abelian category -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

namespace EFiniteCharacterizations

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A short exact sequence with prescribed end terms and middle object. -/
structure ExtensionSequence (A X Q : C) where
  i : A ⟶ X
  p : X ⟶ Q
  w : i ≫ p = 0
  shortExact : (ShortComplex.mk i p w).ShortExact

namespace ExtensionSequence

instance {A X Q : C} (s : ExtensionSequence A X Q) : Mono s.i := s.shortExact.mono_f
instance {A X Q : C} (s : ExtensionSequence A X Q) : Epi s.p := s.shortExact.epi_g

noncomputable def quotient {A X : C} (i : A ⟶ X) [Mono i] : ExtensionSequence A X (cokernel i) :=
  ⟨i, _, cokernel.condition i, ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i)
    inferInstance (by dsimp; infer_instance)⟩

noncomputable def idLeft (X : C) : ExtensionSequence X X 0 :=
  ⟨𝟙 _, 0, comp_zero, ShortComplex.ShortExact.mk'
    ((ShortComplex.mk (𝟙 X) (0 : X ⟶ 0) comp_zero).exact_iff_epi rfl |>.2 (by dsimp; infer_instance))
    (by dsimp; infer_instance) (by dsimp; infer_instance)⟩

noncomputable def idRight (X : C) : ExtensionSequence 0 X X :=
  ⟨0, 𝟙 _, zero_comp, ShortComplex.ShortExact.mk'
    ((ShortComplex.mk (0 : (0 : C) ⟶ X) (𝟙 X) zero_comp).exact_iff_mono rfl |>.2 (by dsimp; infer_instance))
    (by dsimp; infer_instance) (by dsimp; infer_instance)⟩

noncomputable def ofIso {A X Q A' X' Q' : C} (s : ExtensionSequence A X Q)
    (a : A ≅ A') (b : X ≅ X') (c : Q ≅ Q') : ExtensionSequence A' X' Q' := by
  let D := ShortComplex.mk (a.inv ≫ s.i ≫ b.hom) (b.inv ≫ s.p ≫ c.hom)
    (by simp [← Category.assoc s.i, s.w])
  let e : ShortComplex.mk s.i s.p s.w ≅ D := ShortComplex.isoMk a b c (by simp [D]) (by simp [D])
  exact ⟨D.f,D.g,D.zero,ShortComplex.shortExact_of_iso e s.shortExact⟩

/-- The quotient of two short exact rows by three short exact columns. -/
noncomputable def quotientRows {A X Q A' X' Q' A'' X'' Q'' : C}
    (r : ExtensionSequence A X Q) (s : ExtensionSequence A' X' Q')
    (a : ExtensionSequence A A' A'') (b : ExtensionSequence X X' X'') (c : ExtensionSequence Q Q' Q'')
    (hi : a.i ≫ s.i = r.i ≫ b.i) (hp : b.i ≫ s.p = r.p ≫ c.i) : ExtensionSequence A'' X'' Q'' := by
  let t : ShortComplex.mk r.i r.p r.w ⟶ ShortComplex.mk s.i s.p s.w := ShortComplex.Hom.mk a.i b.i c.i hi hp
  let N : ShortComplex.SnakeInput C := {
    L₀ := kernel t, L₁ := _, L₂ := _, L₃ := cokernel t
    v₀₁ := kernel.ι t, v₁₂ := t, v₂₃ := cokernel.π t
    w₀₂ := kernel.condition t, w₁₃ := cokernel.condition t
    h₀ := kernelIsKernel t, h₃ := cokernelIsCokernel t
    L₁_exact := r.shortExact.exact, epi_L₁_g := r.shortExact.epi_g
    L₂_exact := s.shortExact.exact, mono_L₂_f := s.shortExact.mono_f }
  have : Mono N.v₁₂.τ₃ := inferInstanceAs (Mono c.i)
  have hz : IsZero N.L₀.X₃ := KernelFork.IsLimit.isZero_of_mono N.h₀τ₃
  have hm : Mono N.L₃.f := (N.L₂'.exact_iff_mono (hz.eq_of_src _ _)).1 N.L₂'_exact
  have : Epi N.L₂.g := inferInstanceAs (Epi s.p)
  let row : ExtensionSequence N.L₃.X₁ N.L₃.X₂ N.L₃.X₃ :=
    ⟨_,_,_,ShortComplex.ShortExact.mk' N.L₃_exact hm (N.epi_L₃_g)⟩
  exact row.ofIso (N.h₃τ₁.coconePointUniqueUpToIso a.shortExact.gIsCokernel)
    (N.h₃τ₂.coconePointUniqueUpToIso b.shortExact.gIsCokernel)
    (N.h₃τ₃.coconePointUniqueUpToIso c.shortExact.gIsCokernel)

end ExtensionSequence

/-- The multiset of simple isomorphism classes in a finite composition series. -/
inductive HasCompositionFactors : C → Multiset (Skeleton C) → Prop where
  | zero {X : C} (h : IsZero X) : HasCompositionFactors X 0
  | cons {S X Q : C} {l : Multiset (Skeleton C)} (s : ExtensionSequence S X Q)
      (hs : Simple S) (hq : HasCompositionFactors Q l) : HasCompositionFactors X (toSkeleton S ::ₘ l)

namespace HasCompositionFactors

variable {X : C} {l : Multiset (Skeleton C)}

theorem of_iso (h : HasCompositionFactors X l) {Y : C} (e : X ≅ Y) : HasCompositionFactors Y l := by
  cases h with
  | zero hz => exact .zero (hz.of_iso e.symm)
  | cons s hs hq => exact .cons (s.ofIso (Iso.refl _) e (Iso.refl _)) hs hq

/-- A composition series restricts to a subobject and projects to its quotient.
The two multisets of factors sum to the original multiset. -/
theorem split (h : HasCompositionFactors X l) {A Q : C} (s : ExtensionSequence A X Q) :
    ∃ a q, HasCompositionFactors A a ∧ HasCompositionFactors Q q ∧ l = a + q := by
  induction h generalizing A Q with
  | zero hz =>
    exact ⟨0,0,.zero (hz.of_mono s.i),.zero (hz.of_epi s.p), (zero_add _).symm⟩
  | @cons S M D l row hS hD ih =>
    by_cases hz : row.i ≫ s.p = 0
    · let i := (KernelFork.IsLimit.lift' s.shortExact.fIsKernel row.i hz).val
      have hi : i ≫ s.i = row.i := (KernelFork.IsLimit.lift' s.shortExact.fIsKernel row.i hz).property
      have : Mono i := mono_of_mono_fac hi
      let t := ExtensionSequence.quotient i
      let d := ExtensionSequence.quotientRows (ExtensionSequence.idLeft S) s t row (ExtensionSequence.idRight Q)
        (by simpa [ExtensionSequence.idLeft,t,ExtensionSequence.quotient] using hi)
        (by simpa [ExtensionSequence.idLeft,ExtensionSequence.idRight] using hz)
      obtain ⟨a,q,ha,hq,hl⟩ := ih d
      exact ⟨_,_,.cons t hS ha,hq,by simp [hl]⟩
    · let i := row.i ≫ s.p
      have : Mono i := mono_of_nonzero_from_simple hz
      let t := ExtensionSequence.quotient i
      let d := ExtensionSequence.quotientRows (ExtensionSequence.idRight S) s (ExtensionSequence.idRight A) row t
        (by simp [ExtensionSequence.idRight])
        (by simp [ExtensionSequence.idRight,t,ExtensionSequence.quotient,i])
      obtain ⟨a,q,ha,hq,hl⟩ := ih d
      exact ⟨_,_,ha,.cons t hS hq,by simp [hl]⟩

theorem eq_zero_of_isZero (h : HasCompositionFactors X l) (hz : IsZero X) : l = 0 := by
  cases h with
  | zero => rfl
  | cons s hs _ => exact (Simple.not_isZero _ (hz.of_mono s.i)).elim

theorem eq_singleton_of_simple (h : HasCompositionFactors X l) [Simple X] : l = {toSkeleton X} := by
  cases h with
  | zero hz => exact (Simple.not_isZero _ hz).elim
  | @cons U _ _ _ s hs hq =>
    have hne : s.i ≠ 0 := by
      intro he
      apply Simple.not_isZero U
      exact (IsZero.iff_id_eq_zero _).2 ((cancel_mono s.i).1 (by simp [he]))
    have hi := isIso_of_mono_of_nonzero hne
    have hz := s.shortExact.isIso_f_iff.mp hi
    rw [hq.eq_zero_of_isZero hz, congr_toSkeleton_of_iso (asIso s.i)]
    rfl

theorem unique (h : HasCompositionFactors X l) {l' : Multiset (Skeleton C)}
    (h' : HasCompositionFactors X l') : l = l' := by
  induction h generalizing l' with
  | zero hz => exact (h'.eq_zero_of_isZero hz).symm
  | cons s hs _ ih =>
    obtain ⟨a,q,ha,hq,hl⟩ := h'.split s
    rw [hl, ha.eq_singleton_of_simple, ← ih hq, Multiset.singleton_add]

end HasCompositionFactors

/-- Counting all simple factors gives the intrinsic additive invariant of
a category in which every object has a finite composition series. -/
noncomputable def simpleMultiplicity (h : ∀ X : C, ∃ l, HasCompositionFactors X l) (x : Skeleton C) :
    GrothendieckGroup C →+ ℤ := by
  classical
  let l (X : C) := (h X).choose
  apply GrothendieckGroup.lift (fun X ↦ ((l X).count x : ℤ))
  intro S hs
  obtain ⟨a,q,ha,hq,he⟩ := (h S.X₂).choose_spec.split (ExtensionSequence.mk S.f S.g S.zero hs)
  change l S.X₂ = a + q at he
  rw [he, ha.unique (h S.X₁).choose_spec, hq.unique (h S.X₃).choose_spec, Multiset.count_add, Nat.cast_add]

@[simp] theorem simpleMultiplicity_of_simple (h : ∀ X : C, ∃ l, HasCompositionFactors X l)
    (x : Skeleton C) (S : C) [Simple S] [Decidable (x = toSkeleton S)] :
    simpleMultiplicity h x (GrothendieckGroup.of S) = if x = toSkeleton S then 1 else 0 := by
  classical
  simp only [simpleMultiplicity, GrothendieckGroup.lift_of, (h S).choose_spec.eq_singleton_of_simple]
  by_cases he : x = toSkeleton S <;> simp [he]

end EFiniteCharacterizations
