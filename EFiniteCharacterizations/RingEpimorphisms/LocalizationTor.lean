module

public import EFiniteCharacterizations.RingEpimorphisms.LocalizationExtensions
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-!
# Vanishing of `Tor₁ᴿ(B, B)` for universal localizations

Defines `FirstTorSelf f` (`Tor₁ᴿ(B, B)`) from the canonical free presentation of the
restricted regular module of `B` along `f : R →+* B`, and proves by a syzygy pushout
argument that every universal localization at a family of projective morphisms is a
ring epimorphism with `Tor₁ᴿ(B, B) = 0`
(`IsUniversalLocalization.firstTorSelf_subsingleton`).
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
universe u
namespace EFiniteCharacterizations
open ScalarInduction
variable {R B : Type u} [Ring R] [Ring B]

/-- Extension of scalars applied to a module homomorphism. -/
noncomputable def ScalarInduction.mapLinear (f : R →+* B)
    {X Y : Type u} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] (p : X →ₗ[R] Y) :
    Induced f X →ₗ[B] Induced f Y := lift f ((unit f Y).comp p)

/-- The module Tor₁ᴿ(B,B) calculated from the canonical free presentation of B. -/
noncomputable abbrev FirstTorSelf (f : R →+* B) :=
  let N := (ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of B B)
  let q := Finsupp.linearCombination R (id : N → N)
  LinearMap.ker (mapLinear f (X := ↥q.ker) (Y := N →₀ R) q.ker.subtype)

private theorem inverts_restriction {ι : Type*} {φ : ι → TwoTerm R} {f : R →+* B}
    (h : IsUniversalLocalization φ f) (i : ι) (M : ModuleCat.{u} B) :
    (φ i).InvertedOn ((ModuleCat.restrictScalars f).obj M) :=
  ((φ i).invertedOn_induce_iff f M).1 (((φ i).induce f).isIso_iff_invertedOn_all.mp (h.inverts i) M)

/-- Tensoring a short exact sequence with the localization preserves the
inclusion if its quotient already inverts the defining projective maps. -/
theorem IsUniversalLocalization.injective_induced_inclusion {ι : Type*} {φ : ι → TwoTerm R}
    {f : R →+* B} (h : IsUniversalLocalization φ f) (S : ShortComplex (ModuleCat.{u} R))
    (hs : S.ShortExact) (loc : ∀ i, (φ i).InvertedOn S.X₃) :
    Function.Injective (mapLinear f S.f.hom) := by
  let M := ModuleCat.of B (Induced f S.X₁)
  let T := (ModuleCat.restrictScalars f).obj M
  let a : S.X₁ ⟶ T := ModuleCat.ofHom (X := S.X₁) (Y := T) (show S.X₁ →ₗ[R] T from
    { toFun := unit f S.X₁, map_add' := (unit f S.X₁).map_add, map_smul' := (unit f S.X₁).map_smulₛₗ })
  let := hs.mono_f
  let i := pushout.inr S.f a
  let j := pushout.inl S.f a
  let V := pushout S.f a
  let sq := IsPushout.of_hasPushout S.f a
  let seq := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hex : seq.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i)
    (by dsimp [seq,i]; infer_instance) (by dsimp [seq]; infer_instance)
  have := isIso_cokernel_map_of_isPushout sq
  let e : cokernel i ≅ S.X₃ := (asIso (cokernel.map _ _ _ _ sq.w)).symm ≪≫
    (cokernelIsCokernel S.f).coconePointUniqueUpToIso hs.gIsCokernel
  obtain ⟨m,hm⟩ := h.exists_module V (fun t ↦ (φ t).invertedOn_extension seq hex
    (inverts_restriction h t M) (TwoTerm.invertedOn_of_iso e (loc t)))
  letI := m
  let b : S.X₂ →ₛₗ[f] V :=
    { toAddHom := j.hom.toAddHom
      map_smul' := fun r x ↦ (j.hom.map_smul r x).trans (hm r _).symm }
  let c : M →ₗ[B] V :=
    { toAddHom := i.hom.toAddHom
      map_smul' := by
        have z := Module.ext' (Module.compHom V f) V.isModule hm
        have L := h.epic.map_smul (M := M) (N := V)
        rw [z] at L
        exact L i.hom }
  have eqn : (lift f b).comp (mapLinear f S.f.hom) = c := by
    apply hom_ext f
    intro x
    simp only [mapLinear,LinearMap.comp_apply,lift_unit]
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom sq.w) x
  have hinj : Function.Injective c := (ModuleCat.mono_iff_injective i).1 (by dsimp [i]; infer_instance)
  intro x y hxy
  apply hinj
  rw [← eqn]
  exact congrArg (lift f b) hxy

/-- Every universal localization is a ring epimorphism with vanishing first Tor. -/
theorem IsUniversalLocalization.firstTorSelf_subsingleton {ι : Type*} {φ : ι → TwoTerm R}
    {f : R →+* B} (h : IsUniversalLocalization φ f) : Subsingleton (FirstTorSelf f) := by
  let N := (ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of B B)
  let q := Finsupp.linearCombination R (id : N → N)
  let i : ModuleCat.of R q.ker ⟶ ModuleCat.of R (N →₀ R) := ModuleCat.ofHom q.ker.subtype
  let p : ModuleCat.of R (N →₀ R) ⟶ N := ModuleCat.ofHom (X := N →₀ R) (Y := N) q
  let S := ShortComplex.mk i p (by ext x; exact x.property)
  have hs : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.Exact.moduleCat_of_range_eq_ker _ _ q.ker.range_subtype)
    ((ModuleCat.mono_iff_injective _).2 Subtype.val_injective)
    ((ModuleCat.epi_iff_surjective _).2 (Finsupp.linearCombination_surjective R Function.surjective_id))
  have hi := h.injective_induced_inclusion S hs (fun t ↦ inverts_restriction h t (ModuleCat.of B B))
  exact ⟨fun x y ↦ Subtype.ext (hi (x.property.trans y.property.symm))⟩

end EFiniteCharacterizations
