module

public import EFiniteCharacterizations.RingEpimorphisms.LocalizationTor
public import EFiniteCharacterizations.RingEpimorphisms.ArtinianResidual
public import EFiniteCharacterizations.RingEpimorphisms.ResidualLocalization
public import EFiniteCharacterizations.Silting.Fans.RankTwoTauTilting

/-!
# Ring epimorphisms with vanishing first Tor and Artin algebra targets

Corollary 7.9 (`cor:artin-target`) of the manuscript, answering questions of
Angeleri Hügel–Marks–Vitória and Angeleri Hügel–Sentieri in rank at most two:

* `isEFinite_of_artin_epi_targets`: if every ring epimorphism `R →+* B` with
  `Tor₁ᴿ(B, B) = 0` has an Artin algebra as target, then `Rᵐᵒᵖ` is E-finite.
* `tauTiltingFinite_of_artin_epi_targets`: when `R` also has rank at most two,
  Theorem B upgrades this conclusion to `τ`-tilting finiteness.
-/

@[expose] public section
universe u
namespace EFiniteCharacterizations

/-- A ring finite as a module over a commutative Artinian base ring. -/
def IsArtinAlgebra (B : Type u) [Ring B] : Prop :=
  ∃ (C : Type u) (_ : CommRing C) (_ : IsArtinianRing C) (_ : Algebra C B), Module.Finite C B

/-- **Corollary 7.9 (general rank):** If every ring epimorphism `R →+* B` with
`Tor₁ᴿ(B, B) = 0` has an Artin algebra target, then `Rᵐᵒᵖ` is E-finite. -/
theorem isEFinite_of_artin_epi_targets (k R : Type u) [Field k] [Ring R] [Algebra k R]
    [Module.Finite k R] (H : ∀ (B : Type u) [Ring B] (f : R →+* B), IsRingEpimorphism f →
      Subsingleton (FirstTorSelf f) → IsArtinAlgebra B) : IsEFinite Rᵐᵒᵖ := by
  apply (isEFinite_iff_opposite k).1
  by_contra hn
  obtain ⟨P,B,_,_,f,hf,_,hinf⟩ := exists_infinite_residual_localization k hn
  obtain ⟨C, _, _, _, _⟩ := H B f.toRingHom hf.epic hf.firstTorSelf_subsingleton
  let := IsArtinianRing.of_finite C B
  exact hinf (finite_quotient_residual_of_artinian k B)

/-- **Corollary 7.9 (rank at most two):** In rank `≤ 2`, if every ring epimorphism `R →+* B`
with `Tor₁ᴿ(B, B) = 0` has an Artin algebra target, then `Rᵐᵒᵖ` is `τ`-tilting finite. -/
theorem tauTiltingFinite_of_artin_epi_targets (k R : Type u) [Field k] [Ring R] [Algebra k R]
    [Module.Finite k R] (H : ∀ (B : Type u) [Ring B] (f : R →+* B), IsRingEpimorphism f →
      Subsingleton (FirstTorSelf f) → IsArtinAlgebra B) (hr : (simpleIsomorphismClasses Rᵐᵒᵖ).ncard ≤ 2) :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    IsTauTiltingFinite (R := Rᵐᵒᵖ) k := by
  letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  exact ((rankTwoEquivalences (R := R) k hr).1).1 (isEFinite_of_artin_epi_targets k R H)

end EFiniteCharacterizations
