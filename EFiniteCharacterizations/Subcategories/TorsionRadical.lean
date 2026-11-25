module

public import EFiniteCharacterizations.Subcategories.CompactTorsionEquivalences
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono

/-! # Approximation of finitely many torsion radicals from inside a torsion class -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
universe u
namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]
  (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
theorem exists_torsionRadical_subclass (he : IsEFinite R)
    (T F : ObjectProperty (FGModuleCat.{u} R)) [T.IsClosedUnderQuotients]
    (hp : IsTorsionPair T F) {n : ℕ} (S : Fin n → ShortComplex (FGModuleCat.{u} R))
    (hs : ∀ i, (S i).ShortExact ∧ T (S i).X₁ ∧ F (S i).X₃) :
    ∃ T₀ F₀ : ObjectProperty (FGModuleCat.{u} R), IsTorsionPair T₀ F₀ ∧
      FunctoriallyFinite T₀ ∧ T₀ ≤ T ∧ ∀ i, T₀ (S i).X₁ ∧ F₀ (S i).X₃ := by
  classical
  let A (i : Fin n) := (S i).X₁
  let M := ⨁ A
  have orth (Y) (hy : F Y) : rightHomOrthogonal M Y := by
    intro f
    apply biproduct.hom_ext'
    intro i
    simpa using hp.1 (biproduct.ι A i ≫ f) (hs i).2.1 hy
  refine ⟨_, _, isTorsionPair_generated M, functoriallyFinite_generatedTorsionClass_of_isEFinite k he M,
    ?_, fun i ↦ ⟨?_, orth _ (hs i).2.2⟩⟩
  · intro X hx
    obtain ⟨L,Q,i,p,w,hL,hQ,seq⟩ := hp.2 X
    have := seq.epi_g
    have hz : IsZero Q := (IsZero.iff_id_eq_zero _).2 ((cancel_epi p).mp (by
      simpa using hx Q (orth Q hQ) p))
    have := seq.isIso_f_iff.2 hz
    exact T.prop_of_epi i hL
  · intro Y hy f
    simpa using congrArg (biproduct.ι A i ≫ ·) (hy (biproduct.π A i ≫ f))

end EFiniteCharacterizations
