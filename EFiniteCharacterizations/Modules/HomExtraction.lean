module

public import EFiniteCharacterizations.Modules.Bricks

/-! # Extracting Hom-orthogonal pairs of equal class -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]

/-- Cancelling a nonzero noninvertible map across a class relation removes
the same image class from each side. The residual terms cannot both vanish. -/
theorem exists_residual_pair_of_noniso {X Y : FGModuleCat.{u} R} (f : Y ⟶ X)
    (hf : f ≠ 0) (hni : ¬ IsIso f) :
    ∃ (Q K : FGModuleCat.{u} R) (q : X ⟶ Q) (j : K ⟶ Y), Epi q ∧ Mono j ∧
      GrothendieckGroup.of Q - GrothendieckGroup.of K = GrothendieckGroup.of X - GrothendieckGroup.of Y ∧
      (¬ IsZero Q ∨ ¬ IsZero K) ∧ FGModuleCat.moduleLength Q < FGModuleCat.moduleLength X ∧
      FGModuleCat.moduleLength K < FGModuleCat.moduleLength Y := by
  let p := factorThruImage f
  let i := image.ι f
  let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  let T := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p)
    (by dsimp [S]; infer_instance) (by dsimp [S,p]; infer_instance)
  have hT : T.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i)
    (by dsimp [T,i]; infer_instance) (by dsimp [T]; infer_instance)
  have hs : GrothendieckGroup.of Y = GrothendieckGroup.of (kernel p) + GrothendieckGroup.of (image f) :=
    GrothendieckGroup.of_shortExact S hS
  have ht : GrothendieckGroup.of X = GrothendieckGroup.of (image f) + GrothendieckGroup.of (cokernel i) :=
    GrothendieckGroup.of_shortExact T hT
  refine ⟨_, _, cokernel.π i, kernel.ι p, inferInstance, inferInstance, by grind, ?_, ?_, ?_⟩
  · by_contra! h
    have : Epi i := Abelian.epi_of_cokernel_π_eq_zero _ (h.1.eq_of_tgt _ _)
    have : Mono p := Abelian.mono_of_kernel_ι_eq_zero _ (h.2.eq_of_src _ _)
    have : IsIso i := isIso_of_mono_of_epi i
    have : IsIso p := isIso_of_mono_of_epi p
    apply hni
    rw [← image.fac f]
    change IsIso (p ≫ i)
    infer_instance
  · apply FGModuleCat.moduleLength_lt_of_epi (cokernel.π i)
    intro hi
    have iz : i = 0 := (cancel_mono (cokernel.π i)).mp (by simp)
    exact hf (by rw [← image.fac f]; change p ≫ i = 0; rw [iz, comp_zero])
  · apply FGModuleCat.moduleLength_lt_of_mono (kernel.ι p)
    intro hj
    have pz : p = 0 := (cancel_epi (kernel.ι p)).mp (by simp)
    exact hf (by rw [← image.fac f]; change p ≫ i = 0; rw [pz, zero_comp])

/-- A failure of the equal-class Hom condition yields a nonzero equal-class
pair for which Hom vanishes in both directions. -/
theorem exists_orthogonal_pair_of_not_equalClassHom
    (h : ¬ EqualClassHom (FGModuleCat.{u} R)) :
    ∃ X Y : FGModuleCat.{u} R, GrothendieckGroup.of X = GrothendieckGroup.of Y ∧
      GrothendieckGroup.of X ≠ 0 ∧ (∀ f : X ⟶ Y, f = 0) ∧ (∀ f : Y ⟶ X, f = 0) := by
  classical
  unfold EqualClassHom at h
  push Not at h
  let P (n : ℕ) := ∃ X Y : FGModuleCat.{u} R, FGModuleCat.moduleLength X = n ∧
    GrothendieckGroup.of X = GrothendieckGroup.of Y ∧ GrothendieckGroup.of X ≠ 0 ∧
    ∀ f : X ⟶ Y, f = 0
  have hex : ∃ n, P n := by
    obtain ⟨X, Y, he, hn, hz⟩ := h
    exact ⟨_, X, Y, rfl, he, hn, hz⟩
  obtain ⟨X, Y, hlen, he, hn, hz⟩ := Nat.find_spec hex
  refine ⟨X, Y, he, hn, hz, fun f ↦ ?_⟩
  by_contra hf
  have hni : ¬ IsIso f := by
    intro hi
    exact hf (by simpa using congrArg (fun g : X ⟶ Y ↦ f ≫ g ≫ f) (hz (inv f)))
  obtain ⟨Q, K, q, j, _, _, hdiff, hnonzero, hlt, _⟩ :=
    exists_residual_pair_of_noniso f hf hni
  have he' : GrothendieckGroup.of Q = GrothendieckGroup.of K := sub_eq_zero.mp (by simpa [he] using hdiff)
  have hn' : GrothendieckGroup.of Q ≠ 0 := hnonzero.elim FGModuleCat.class_ne_zero
    (fun hK ↦ he'.symm ▸ FGModuleCat.class_ne_zero hK)
  apply Nat.find_min hex (hlen ▸ hlt)
  refine ⟨_, _, rfl, he', hn', fun g ↦ ?_⟩
  apply (cancel_epi q).mp
  apply (cancel_mono j).mp
  simpa using hz (q ≫ g ≫ j)

private theorem squaredLengths_lt_of_shortExact {S : ShortComplex (FGModuleCat.{u} R)}
    (hs : S.ShortExact) (h₁ : ¬ IsZero S.X₁) (h₃ : ¬ IsZero S.X₃) :
    FGModuleCat.moduleLength S.X₁ ^ 2 + FGModuleCat.moduleLength S.X₃ ^ 2 <
      FGModuleCat.moduleLength S.X₂ ^ 2 := by
  have ha := mt (FGModuleCat.moduleLength_eq_zero_iff_isZero _).1 h₁
  have hb := mt (FGModuleCat.moduleLength_eq_zero_iff_isZero _).1 h₃
  rw [FGModuleCat.moduleLength_shortExact S hs, add_sq]
  have hp := Nat.mul_pos (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
  nlinarith

/-- A nonzero nonepimorphism splits the target class into two quotient
classes of strictly smaller total squared length. -/
theorem exists_quotient_split_of_not_epi {A B : FGModuleCat.{u} R} (f : A ⟶ B)
    (hf : f ≠ 0) (hne : ¬ Epi f) :
    ∃ (L Q : FGModuleCat.{u} R) (p : A ⟶ L) (q : B ⟶ Q), Epi p ∧ Epi q ∧
      GrothendieckGroup.of B = GrothendieckGroup.of L + GrothendieckGroup.of Q ∧
      FGModuleCat.moduleLength L ^ 2 + FGModuleCat.moduleLength Q ^ 2 < FGModuleCat.moduleLength B ^ 2 := by
  let i := image.ι f
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hs : S.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i)
    (by dsimp [S,i]; infer_instance) (by dsimp [S]; infer_instance)
  refine ⟨_, _, factorThruImage f, cokernel.π i, inferInstance, inferInstance,
    GrothendieckGroup.of_shortExact S hs, squaredLengths_lt_of_shortExact (S := S) hs ?_ ?_⟩
  · intro hz
    change IsZero (image f) at hz
    exact hf (by rw [← image.fac f, hz.eq_of_src (image.ι f) 0, comp_zero])
  · intro hz
    change IsZero (cokernel i) at hz
    have : Epi i := Abelian.epi_of_cokernel_π_eq_zero _ (hz.eq_of_tgt _ _)
    exact hne (by rw [← image.fac f]; change Epi (factorThruImage f ≫ i); infer_instance)

/-- A noninvertible epimorphism splits the source class into two subobject
classes of strictly smaller total squared length. -/
theorem exists_subobject_split_of_epi {A B : FGModuleCat.{u} R} (f : A ⟶ B) [Epi f]
    (hf : f ≠ 0) (hne : ¬ IsIso f) :
    ∃ (L Q : FGModuleCat.{u} R) (i : L ⟶ A) (j : Q ⟶ B), Mono i ∧ Mono j ∧
      GrothendieckGroup.of A = GrothendieckGroup.of L + GrothendieckGroup.of Q ∧
      FGModuleCat.moduleLength L ^ 2 + FGModuleCat.moduleLength Q ^ 2 < FGModuleCat.moduleLength A ^ 2 := by
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hs : S.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel f)
    (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
  refine ⟨_, _, kernel.ι f, 𝟙 B, inferInstance, inferInstance,
    GrothendieckGroup.of_shortExact S hs, squaredLengths_lt_of_shortExact (S := S) hs ?_ ?_⟩
  · intro hz
    change IsZero (kernel f) at hz
    have : Mono f := Abelian.mono_of_kernel_ι_eq_zero _ (hz.eq_of_src _ _)
    exact hne (isIso_of_mono_of_epi f)
  · exact fun hz ↦ hf (hz.eq_of_tgt f 0)

end EFiniteCharacterizations
