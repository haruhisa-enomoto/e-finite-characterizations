module

public import EFiniteCharacterizations.Modules.ProjectiveBaseChange
public import EFiniteCharacterizations.Silting.Reduction.ReductionRank

/-! # Arbitrary universal localizations of an E-finite algebra -/

@[expose] public section

open CategoryTheory

universe u v

namespace EFiniteCharacterizations

variable {R B C : Type u} [Ring R] [Ring B] [Ring C] {ι : Type v}

/-- Inversion of every differential in an indexed family after induction. -/
def InvertsFamily (φ : ι → TwoTerm R) (f : R →+* B) : Prop :=
  ∀ i, IsIso ((φ i).induce f).differential

/-- The ring-theoretic universal property of localization at finite projective maps. -/
structure IsUniversalLocalization (φ : ι → TwoTerm R) (f : R →+* B) : Prop where
  inverts : InvertsFamily φ f
  desc : ∀ (T : Type u) [Ring T] (g : R →+* T), InvertsFamily φ g →
    ∃! q : B →+* T, q.comp f = g

theorem invertsFamily_comp_iff (φ : ι → TwoTerm R) (f : R →+* B) (g : B →+* C) :
    InvertsFamily φ (g.comp f) ↔ InvertsFamily (fun i ↦ (φ i).induce f) g := by
  apply forall_congr'
  intro i
  rw [TwoTerm.isIso_induce_iff_regular,TwoTerm.isIso_induce_iff_regular]
  let := Module.compHom C g
  exact ((φ i).invertedOn_induce_iff f (ModuleCat.of B C)).symm

variable (k : Type u) [Field k]

private theorem exists_finite_localization_rank (n : ℕ) :
    ∀ (R : Type u) [Ring R] [Algebra k R] [Module.Finite k R], IsEFinite R →
      (simpleIsomorphismClasses R).ncard = n → ∀ φ : ι → TwoTerm R,
      ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B) (f : R →ₐ[k] B),
        IsUniversalLocalization φ f.toRingHom := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro R _ _ _ hR hr φ
    let := IsArtinianRing.of_finite k R
    let := IsNoetherianRing.of_finite k R
    by_cases hall : ∀ i, IsIso (φ i).differential
    · refine ⟨R,inferInstance,inferInstance,inferInstance,AlgHom.id k R,⟨?_,?_⟩⟩
      · intro i
        apply (TwoTerm.isIso_induce_iff_regular _ _).2
        exact ((φ i).isIso_iff_invertedOn_all.mp (hall i)) _
      · intro T _ g _
        exact ⟨g,rfl,fun q hq ↦ hq⟩
    · obtain ⟨i,hi⟩ := not_forall.mp hall
      obtain ⟨B,_,_,_,f,hB,hs,hfac⟩ := (φ i).exists_smaller_reduction k hR hi
      let ψ := fun j ↦ (φ j).induce f.toRingHom
      obtain ⟨C,_,_,_,p,hp⟩ := ih _ (hs.trans_eq hr) B hB rfl ψ
      refine ⟨C,inferInstance,inferInstance,inferInstance,p.comp f,⟨?_,?_⟩⟩
      · exact (invertsFamily_comp_iff φ f.toRingHom p.toRingHom).2 hp.inverts
      · intro T _ g hg
        obtain ⟨b,hb,hu⟩ := hfac T g (((φ i).isIso_induce_iff_regular g).1 (hg i))
        have hb' : InvertsFamily ψ b := (invertsFamily_comp_iff φ f.toRingHom b).1 (hb ▸ hg)
        obtain ⟨c,hc,hu'⟩ := hp.desc T b hb'
        refine ⟨c,?_,?_⟩
        · change (c.comp p.toRingHom).comp f.toRingHom = g
          rw [hc,hb]
        · intro q hq
          exact hu' q (hu (q.comp p.toRingHom) hq)

/-- Every family of finite projective maps over an E-finite algebra has a
finite-dimensional universal localization over the ground field. -/
theorem exists_finite_universalLocalization [Algebra k R] [Module.Finite k R]
    (hR : IsEFinite R) (φ : ι → TwoTerm R) :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B) (f : R →ₐ[k] B),
      IsUniversalLocalization φ f.toRingHom :=
  exists_finite_localization_rank k _ R hR rfl φ

/-- Every target satisfying the ring universal property is finite-dimensional
for its compatible ground field action. -/
theorem finite_of_universalLocalization [Algebra k R] [Module.Finite k R] [Algebra k B]
    (hR : IsEFinite R) {φ : ι → TwoTerm R} (g : R →ₐ[k] B)
    (hg : IsUniversalLocalization φ g.toRingHom) : Module.Finite k B := by
  obtain ⟨C,_,_,_,f,hf⟩ := exists_finite_universalLocalization k hR φ
  obtain ⟨p,hp,_⟩ := hf.desc B g.toRingHom hg.inverts
  obtain ⟨q,hq,_⟩ := hg.desc C f.toRingHom hf.inverts
  have hid : p.comp q = RingHom.id B := (hg.desc B g.toRingHom hg.inverts).unique
    (show (p.comp q).comp g.toRingHom = _ from (congrArg p.comp hq).trans hp) rfl
  let a : C →ₐ[k] B :=
    { __ := p
      commutes' := fun t ↦ by
        rw [← f.commutes t]
        exact (DFunLike.congr_fun hp (algebraMap k R t)).trans (g.commutes t) }
  exact Module.Finite.of_surjective a.toLinearMap fun x ↦ ⟨q x,DFunLike.congr_fun hid x⟩

/-- The finite-dimensionality condition for all universal localizations at
sets of maps of finitely generated projective right modules. -/
def RightUniversalLocalizationsFinite (R : Type u) [Ring R] [Algebra k R] : Prop :=
  ∀ (Φ : Set (TwoTerm Rᵐᵒᵖ)) (B : Type u) [Ring B] [Algebra k B] (g : R →ₐ[k] B),
    IsUniversalLocalization (fun i : Φ ↦ i.val) (AlgHom.op g).toRingHom → Module.Finite k B

/-- The forward universal-localization implication in the right-module convention. -/
theorem rightUniversalLocalizationsFinite_of_isEFinite [Algebra k R] [Module.Finite k R]
    (hR : IsEFinite Rᵐᵒᵖ) : RightUniversalLocalizationsFinite k R := by
  intro Φ B _ _ g hg
  have := finite_of_universalLocalization k hR (AlgHom.op g) hg
  exact Module.Finite.equiv (MulOpposite.opLinearEquiv k).symm

end EFiniteCharacterizations
