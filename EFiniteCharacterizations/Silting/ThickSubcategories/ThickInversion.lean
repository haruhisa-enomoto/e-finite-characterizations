module

public import EFiniteCharacterizations.Silting.ThickSubcategories.ThickGeneration
public import EFiniteCharacterizations.Presentations.StableInversion
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-! # Inversion of differentials in a generated thick subcategory -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
open CochainComplex.HomComplex

namespace EFiniteCharacterizations.TwoTerm

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]

omit [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem zero_iff_iso_d (K : CochainComplex D ℤ)
    (h : ∀ j : ℤ, j ≠ -1 → j ≠ 0 → IsZero (K.X j)) :
    IsZero ((HomotopyCategory.quotient _ _).obj K) ↔ IsIso (K.d (-1) 0) := by
  rw [HomotopyCategory.isZero_quotient_obj_iff]
  constructor
  · rintro ⟨t⟩
    have h₀ := t.comm (-1)
    have h₁ := t.comm 0
    rw [dNext_eq t.hom adjacent, prevD_eq t.hom (show (ComplexShape.up ℤ).Rel (-2) (-1) from rfl)] at h₀
    rw [dNext_eq t.hom (show (ComplexShape.up ℤ).Rel 0 1 from rfl), prevD_eq t.hom adjacent] at h₁
    have hm := (h (-2) (by decide) (by decide)).eq_of_tgt (t.hom (-1) (-2)) 0
    have hp := (h 1 (by decide) (by decide)).eq_of_tgt (K.d 0 1) 0
    exact ⟨t.hom 0 (-1), by simpa [hm] using h₀.symm, by simpa [hp] using h₁.symm⟩
  · intro hi
    let z : Cochain K K (-1) := Cochain.single (inv (K.d (-1) 0)) (-1)
    refine ⟨(Cochain.equivHomotopy _ _).symm ⟨z, ?_⟩⟩
    rw [Cochain.ofHom_zero, add_zero]
    apply Cochain.ext
    intro j j' hj
    suffices hd : ∀ i : ℤ, (Cochain.ofHom (𝟙 K)).v i i (add_zero i) =
        (δ (-1) 0 z).v i i (add_zero i) by
      obtain rfl : j = j' := by omega
      exact hd _
    intro i
    rw [Cochain.ofHom_v, HomologicalComplex.id_f]
    by_cases hm : i = -1
    · subst i
      change 𝟙 _ = (δ (-1) 0 z).v (-1) (-1) rfl
      rw [δ_v (-1) 0 rfl z (-1) (-1) rfl (-2) 0 rfl rfl]
      simp [z, Cochain.single_v_eq_zero]
    by_cases h₀ : i = 0
    · subst i
      change 𝟙 _ = (δ (-1) 0 z).v 0 0 rfl
      rw [δ_v (-1) 0 rfl z 0 0 rfl (-1) 1 rfl rfl]
      simp [z, Cochain.single_v_eq_zero]
    exact (h i hm h₀).eq_of_src _ _

universe u
variable {R : Type u} [Ring R] [IsNoetherianRing R]

omit [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem kernel_iff (F : FGModuleCat.{u} R ⥤ D) [F.Additive] (P : TwoTerm R) :
    (F.mapHomotopyCategory (ComplexShape.up ℤ)).kernel P.homotopyObject ↔ IsIso (F.map P.differential) := by
  let L := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P.toCochainComplex
  change IsZero ((HomotopyCategory.quotient _ _).obj L) ↔ _
  rw [zero_iff_iso_d L (fun j h₁ h₀ ↦ F.map_isZero (isZero_double_X P.differential adjacent j h₁ h₀))]
  change IsIso (F.map (P.toCochainComplex.d (-1) 0)) ↔ _
  rw [double_d P.differential adjacent (by decide)]
  simp only [F.map_comp, isIso_comp_left_iff, isIso_comp_right_iff]

/-- An additive functor that inverts a differential also inverts every
two-term differential in its ambient thick closure. -/
theorem isIso_map_of_inThick (F : FGModuleCat.{u} R ⥤ D) [F.Additive] {P Q : TwoTerm R}
    (h : InThick P Q) (hi : IsIso (F.map P.differential)) : IsIso (F.map Q.differential) := by
  let G := F.mapHomotopyCategory (ComplexShape.up ℤ)
  let Z : ObjectProperty (HomotopyCategory D (ComplexShape.up ℤ)) := IsZero
  have : Z.IsClosedUnderIsomorphisms := ⟨fun e hz ↦ hz.of_iso e.symm⟩
  have : Z.IsStableUnderShift ℤ := ⟨fun t ↦ ⟨fun _ hz ↦ (shiftFunctor _ t).map_isZero hz⟩⟩
  have : Z.IsTriangulatedClosed₂ := .mk' (fun T ht a b ↦ T.isZero₂_of_isZero₁₃ ht a b)
  have : Z.IsTriangulated := {}
  have : Z.IsStableUnderRetracts := ⟨fun r hY ↦ by
    apply (IsZero.iff_id_eq_zero _).2
    rw [← r.retract, hY.eq_of_tgt r.i 0, zero_comp]⟩
  have hz : (Z.inverseImage G).IsTriangulated := inferInstance
  have hr : (Z.inverseImage G).IsStableUnderRetracts := ⟨fun r hY ↦ Z.prop_of_retract (r.map G) hY⟩
  exact (kernel_iff F Q).1 ((ObjectProperty.triangEnvelope_le_iff (Q := Z.inverseImage G) _).2
    (ObjectProperty.singleton_le_iff.2 ((kernel_iff F P).2 hi)) _ h)

/-- Inversion by Hom into any module is preserved throughout a thick closure. -/
theorem invertedOn_of_inThick {P Q : TwoTerm R} (h : InThick P Q) (N : ModuleCat.{u} R)
    (hi : P.InvertedOn N) : Q.InvertedOn N := by
  let G := preadditiveYonedaObj N
  have : G.Additive := inferInstanceAs (preadditiveYonedaObj N).Additive
  let : G.rightOp.Additive := Functor.rightOp_additive G
  let : (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).Additive := ⟨rfl⟩
  let F := forget₂ (FGModuleCat R) (ModuleCat.{u} R) ⋙ G.rightOp
  have : F.Additive := inferInstanceAs ((forget₂ (FGModuleCat R) (ModuleCat.{u} R)) ⋙ G.rightOp).Additive
  have test (T : TwoTerm R) : IsIso (F.map T.differential) ↔ T.InvertedOn N := by
    change IsIso (G.map T.differential.hom.op).op ↔ _
    rw [isIso_op_iff, ConcreteCategory.isIso_iff_bijective]
    rfl
  exact (test Q).1 (isIso_map_of_inThick F h ((test P).2 hi))

end EFiniteCharacterizations.TwoTerm
