module

public import EFiniteCharacterizations.RingEpimorphisms.ResiduallyFiniteTargets

/-! # Descent of E-finiteness along exact fully faithful functors -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u
namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  [Module.Finite k A] [Module.Finite k B] [IsNoetherianRing A] [IsArtinianRing A]
  [IsNoetherianRing B] [IsArtinianRing B]

include k in
theorem isEFinite_of_exact_embedding (F : FGModuleCat.{u} B ⥤ FGModuleCat.{u} A)
    [F.Full] [F.Faithful] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (h : IsEFinite A) : IsEFinite B := by
  apply (isEFinite_iff_equalClassHom k).2
  intro X Y he hn
  let φ := GrothendieckGroup.map F (fun _ hs ↦ hs.map_of_exact F)
  have hf Z : φ (GrothendieckGroup.of Z) = GrothendieckGroup.of (F.obj Z) := GrothendieckGroup.lift_of ..
  have hn' : ¬ IsZero (F.obj X) := by
    intro hz
    apply hn
    apply GrothendieckGroup.of_isZero
    apply (IsZero.iff_id_eq_zero _).2
    apply F.map_injective
    simpa using hz.eq_of_src (𝟙 _) 0
  obtain ⟨f,hf'⟩ := equalClassHom_of_isEFinite k h _ _
    ((hf X).symm.trans ((congrArg φ he).trans (hf Y))) (FGModuleCat.class_ne_zero hn')
  exact ⟨F.preimage f, fun hz ↦ hf' (by rw [← F.map_preimage f, hz, F.map_zero])⟩

/-- Restriction of scalars along a surjective algebra map preserves E-finiteness
of the target whenever the source is E-finite. -/
theorem isEFinite_of_surjective (f : A →ₐ[k] B) (hf : Function.Surjective f)
    (h : IsEFinite A) : IsEFinite B := by
  let G := ModuleCat.restrictScalars.{u} f.toRingHom
  have epic : IsRingEpimorphism f.toRingHom := by
    intro D _ a b hab
    ext y
    obtain ⟨x,rfl⟩ := hf y
    exact DFunLike.congr_fun hab x
  letI : G.Full := epic.full_restriction
  let : PreservesFiniteLimits G := ⟨fun J _ _ ↦ ⟨fun {K} ↦ inferInstanceAs (PreservesLimit K (ModuleCat.restrictScalars f.toRingHom))⟩⟩
  let : PreservesFiniteColimits G := ⟨fun J _ _ ↦ ⟨fun {K} ↦ inferInstanceAs (PreservesColimit K (ModuleCat.restrictScalars f.toRingHom))⟩⟩
  let J := forget₂ (FGModuleCat.{u} B) (ModuleCat.{u} B)
  let I := forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)
  let : J.Full := inferInstanceAs (ModuleCat.isFG B).ι.Full
  let : J.Faithful := inferInstanceAs (ModuleCat.isFG B).ι.Faithful
  let : G.Faithful := inferInstanceAs (ModuleCat.restrictScalars f.toRingHom).Faithful
  let F : FGModuleCat.{u} B ⥤ FGModuleCat.{u} A := ObjectProperty.lift _ (J ⋙ G) (by
    intro M
    have := Module.Finite.trans (R := k) B (M.obj : Type u)
    have := Module.Finite.equiv (restrictScalarsGroundEquiv k f M.obj).symm
    exact Module.Finite.of_restrictScalars_finite k A (G.obj M.obj))
  let : F.Full := ⟨fun {X Y} p ↦ by
    let t : G.obj X.obj ⟶ G.obj Y.obj := p.hom
    exact ⟨ObjectProperty.homMk (G.preimage t), ObjectProperty.hom_ext _ (G.map_preimage t)⟩⟩
  let : F.Faithful := ⟨fun eqn ↦ ObjectProperty.hom_ext _ (G.map_injective (congrArg (·.hom) eqn))⟩
  letI : PreservesFiniteLimits (F ⋙ I) := inferInstanceAs (PreservesFiniteLimits (J ⋙ G))
  letI : PreservesFiniteColimits (F ⋙ I) := inferInstanceAs (PreservesFiniteColimits (J ⋙ G))
  letI := preservesFiniteLimits_of_reflects_of_preserves F I
  letI := preservesFiniteColimits_of_reflects_of_preserves F I
  exact isEFinite_of_exact_embedding k F h

end EFiniteCharacterizations
