module

public import EFiniteCharacterizations.RingEpimorphisms.LocalizationTor
public import EFiniteCharacterizations.RingEpimorphisms.ArtinianResidual
public import EFiniteCharacterizations.RingEpimorphisms.ResidualLocalization
public import EFiniteCharacterizations.Silting.Fans.RankTwoTauTilting

/-! # Artin targets of ring epimorphisms with vanishing first Tor -/

@[expose] public section
universe u
namespace EFiniteCharacterizations

/-- A ring finite as a module over a commutative Artinian base ring. -/
def IsArtinAlgebra (B : Type u) [Ring B] : Prop :=
  ∃ (C : Type u) (_ : CommRing C) (_ : IsArtinianRing C) (_ : Algebra C B), Module.Finite C B

theorem isEFinite_of_artin_epi_targets (k R : Type u) [Field k] [Ring R] [Algebra k R]
    [Module.Finite k R] (H : ∀ (B : Type u) [Ring B] (f : R →+* B), IsRingEpimorphism f →
      Subsingleton (FirstTorSelf f) → IsArtinAlgebra B) : IsEFinite Rᵐᵒᵖ := by
  apply (isEFinite_iff_opposite k).1
  by_contra hn
  obtain ⟨P,B,_,_,f,hf,_,hinf⟩ := exists_infinite_residual_localization k hn
  obtain ⟨C, _, _, _, _⟩ := H B f.toRingHom hf.epic hf.firstTorSelf_subsingleton
  let := IsArtinianRing.of_finite C B
  exact hinf (finite_quotient_residual_of_artinian k B)

theorem tauTiltingFinite_of_artin_epi_targets (k R : Type u) [Field k] [Ring R] [Algebra k R]
    [Module.Finite k R] (H : ∀ (B : Type u) [Ring B] (f : R →+* B), IsRingEpimorphism f →
      Subsingleton (FirstTorSelf f) → IsArtinAlgebra B) (hr : (simpleIsomorphismClasses Rᵐᵒᵖ).ncard ≤ 2) :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    IsTauTiltingFinite (R := Rᵐᵒᵖ) k := by
  letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  exact ((rankTwoEquivalences (R := R) k hr).1).1 (isEFinite_of_artin_epi_targets k R H)

end EFiniteCharacterizations
