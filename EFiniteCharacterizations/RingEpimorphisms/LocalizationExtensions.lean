module

public import EFiniteCharacterizations.RingEpimorphisms.LocalizationModules
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Extensions of modules over a universal localization -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
universe u
namespace EFiniteCharacterizations
variable {R : Type u} [Ring R]

theorem TwoTerm.invertedOn_extension (P : TwoTerm R) (S : ShortComplex (ModuleCat.{u} R))
    (hs : S.ShortExact) (ha : P.InvertedOn S.X₁) (hc : P.InvertedOn S.X₃) : P.InvertedOn S.X₂ := by
  let := hs.mono_f
  let := hs.epi_g
  let := P.projective_target
  have kerlift {Y : ModuleCat.{u} R} (z : Y ⟶ S.X₂) (hz : z ≫ S.g = 0) :
      ∃ l : Y ⟶ S.X₁, l ≫ S.f = z :=
    let l := KernelFork.IsLimit.lift' hs.fIsKernel z hz
    ⟨l.val,l.property⟩
  constructor
  · intro a b he
    change P.differential.hom ≫ a = P.differential.hom ≫ b at he
    have hz : (a-b) ≫ S.g = 0 := by
      apply hc.1
      simp [Preadditive.sub_comp,Preadditive.comp_sub,← Category.assoc,he]
    obtain ⟨l,hl⟩ := kerlift _ hz
    have hlz : l = 0 := by
      apply ha.1
      apply (cancel_mono S.f).mp
      change (P.differential.hom ≫ l) ≫ S.f = (P.differential.hom ≫ 0) ≫ S.f
      simp [Category.assoc,hl,Preadditive.comp_sub,he]
    exact sub_eq_zero.mp (hl.symm.trans (by simp [hlz]))
  · intro a
    obtain ⟨c,hc'⟩ := hc.2 (a ≫ S.g)
    obtain ⟨b,hb⟩ := Module.projective_lifting_property S.g.hom c.hom hs.moduleCat_surjective_g
    let b' : P.target.obj ⟶ S.X₂ := ModuleCat.ofHom b
    have hb' : b' ≫ S.g = c := ModuleCat.hom_ext hb
    have hz : (a - P.differential.hom ≫ b') ≫ S.g = 0 := by
      rw [Preadditive.sub_comp,Category.assoc,hb',← hc',sub_self]
    obtain ⟨l,hl⟩ := kerlift _ hz
    obtain ⟨t,ht⟩ := ha.2 l
    change P.differential.hom ≫ t = l at ht
    refine ⟨b' + t ≫ S.f,?_⟩
    change P.differential.hom ≫ (b' + t ≫ S.f) = a
    rw [Preadditive.comp_add,← Category.assoc,ht,hl]
    abel

/-- Extensions between modules inverting all the designated maps split
when the universal localization is a division ring. -/
theorem IsUniversalLocalization.splits_over_divisionRing {B : Type u} [DivisionRing B]
    {ι : Type*} {φ : ι → TwoTerm R} {f : R →+* B} (h : IsUniversalLocalization φ f)
    (S : ShortComplex (ModuleCat.{u} R)) (hs : S.ShortExact)
    (ha : ∀ i, (φ i).InvertedOn S.X₁) (hc : ∀ i, (φ i).InvertedOn S.X₃) :
    ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ := by
  obtain ⟨m₂,h₂⟩ := h.exists_module S.X₂ (fun i ↦ (φ i).invertedOn_extension S hs (ha i) (hc i))
  obtain ⟨m₃,h₃⟩ := h.exists_module S.X₃ hc
  let := m₂
  let := m₃
  let q : S.X₂ →ₗ[B] S.X₃ :=
    { toAddHom := S.g.hom.toAddHom
      map_smul' := by
        have e₂ := Module.ext' (Module.compHom S.X₂ f) S.X₂.isModule h₂
        have e₃ := Module.ext' (Module.compHom S.X₃ f) S.X₃.isModule h₃
        have H := h.epic.map_smul (M := S.X₂) (N := S.X₃)
        rw [e₂,e₃] at H
        exact H S.g.hom }
  obtain ⟨s,hsec⟩ := Module.projective_lifting_property q
    (LinearMap.id : S.X₃ →ₗ[B] S.X₃) hs.moduleCat_surjective_g
  let t : S.X₃ →ₗ[R] S.X₂ :=
    { toAddHom := s.toAddHom
      map_smul' := fun r x ↦ (congrArg s (h₃ r x).symm).trans ((s.map_smul _ x).trans (h₂ r _)) }
  exact ⟨ModuleCat.ofHom t, ModuleCat.hom_ext (LinearMap.ext fun x ↦ LinearMap.congr_fun hsec x)⟩

end EFiniteCharacterizations
