module

public import EFiniteCharacterizations.Silting.ThickSubcategories.TwoTermHomotopy
public import EFiniteCharacterizations.Presentations.ExtensionBounds
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.CategoryTheory.Preadditive.Comma

/-! # Triangles of two-term complexes -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex

namespace EFiniteCharacterizations.TwoTerm

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]

/-- The chain map between two-term complexes induced by a commutative square. -/
noncomputable def doubleMap {X Y : Arrow C} (f : X ⟶ Y) :
    double X.hom adjacent ⟶ double Y.hom adjacent :=
  mkHomFromDouble adjacent (by decide)
    (f.left ≫ (doubleXIso₀ Y.hom adjacent).inv)
    (f.right ≫ (doubleXIso₁ Y.hom adjacent (by decide)).inv)
    (by simp [double_d Y.hom adjacent (by decide)])
    (by intro n _; simp [double_d_eq_zero₀ Y.hom adjacent 0 n (by decide)])

/-- Realization of a differential in degrees −1 and 0, functorial on squares. -/
noncomputable def doubleFunctor : Arrow C ⥤ CochainComplex C ℤ where
  obj X := double X.hom adjacent
  map := doubleMap
  map_id _ := by apply from_double_hom_ext <;> simp [doubleMap]
  map_comp _ _ := by apply from_double_hom_ext <;> simp [doubleMap]

set_option backward.isDefEq.respectTransparency false in
instance : (doubleFunctor (C := C)).Additive where
  map_add := by
    intro X Y f g
    apply from_double_hom_ext <;>
      simp [doubleFunctor, doubleMap, add_f_apply, Preadditive.comp_add, Preadditive.add_comp]

/-- A sequence of arrows split on both sources and targets is degreewise
split as a sequence of two-term cochain complexes. -/
noncomputable def doubleSplitting (S : ShortComplex (Arrow C))
    (h₀ : (S.map Arrow.leftFunc).Splitting) (h₁ : (S.map Arrow.rightFunc).Splitting)
    (n : ℤ) : ((S.map doubleFunctor).map (eval _ _ n)).Splitting := by
  by_cases hn : n = -1
  · subst n
    apply h₀.ofIso
    refine ShortComplex.isoMk (doubleXIso₀ S.X₁.hom adjacent).symm
      (doubleXIso₀ S.X₂.hom adjacent).symm (doubleXIso₀ S.X₃.hom adjacent).symm ?_ ?_
    · change (doubleXIso₀ S.X₁.hom adjacent).inv ≫ (doubleMap S.f).f (-1) =
        S.f.left ≫ (doubleXIso₀ S.X₂.hom adjacent).inv
      simp [doubleMap]
    · change (doubleXIso₀ S.X₂.hom adjacent).inv ≫ (doubleMap S.g).f (-1) =
        S.g.left ≫ (doubleXIso₀ S.X₃.hom adjacent).inv
      simp [doubleMap]
  by_cases hn' : n = 0
  · subst n
    apply h₁.ofIso
    refine ShortComplex.isoMk (doubleXIso₁ S.X₁.hom adjacent (by decide)).symm
      (doubleXIso₁ S.X₂.hom adjacent (by decide)).symm (doubleXIso₁ S.X₃.hom adjacent (by decide)).symm ?_ ?_
    · change (doubleXIso₁ S.X₁.hom adjacent (by decide)).inv ≫ (doubleMap S.f).f 0 =
        S.f.right ≫ (doubleXIso₁ S.X₂.hom adjacent (by decide)).inv
      simp [doubleMap]
    · change (doubleXIso₁ S.X₂.hom adjacent (by decide)).inv ≫ (doubleMap S.g).f 0 =
        S.g.right ≫ (doubleXIso₁ S.X₃.hom adjacent (by decide)).inv
      simp [doubleMap]
  exact ShortComplex.Splitting.ofIsZero _ (isZero_double_X S.X₁.hom adjacent n hn hn')
    (isZero_double_X S.X₂.hom adjacent n hn hn') (isZero_double_X S.X₃.hom adjacent n hn hn')

variable {R : Type*} [Ring R] [IsNoetherianRing R]
variable (P Q : TwoTerm R) (w : Q.source ⟶ P.target)

noncomputable def blockSequence : ShortComplex (Arrow (FGModuleCat R)) :=
  ShortComplex.mk (Arrow.homMk (f := Arrow.mk P.differential)
    (g := Arrow.mk (blockDifferential P.differential Q.differential w))
    biprod.inl biprod.inl (by simp))
    (Arrow.homMk (g := Arrow.mk Q.differential) biprod.snd biprod.snd (by simp))
    (by apply Arrow.hom_ext <;> exact biprod.inl_snd)

/-- The canonical degreewise splitting of the block sequence. -/
noncomputable abbrev blockSplitting := doubleSplitting (blockSequence P Q w)
  (ShortComplex.Splitting.ofHasBinaryBiproduct P.source Q.source)
  (ShortComplex.Splitting.ofHasBinaryBiproduct P.target Q.target)

/-- The triangle of the off-diagonal entry of a block differential. -/
noncomputable abbrev blockTriangle := CochainComplex.trianglehOfDegreewiseSplit
  ((blockSequence P Q w).map doubleFunctor) (blockSplitting P Q w)

theorem blockTriangle_distinguished : blockTriangle P Q w ∈ distTriang _ :=
  CochainComplex.trianglehOfDegreewiseSplit_distinguished _ _

set_option backward.isDefEq.respectTransparency false in
private theorem blockConnecting_f :
    (CochainComplex.homOfDegreewiseSplit _ (blockSplitting P Q w)).f (-1) =
      (doubleXIso₀ Q.differential adjacent).hom ≫ w ≫
        (doubleXIso₁ P.differential adjacent (by decide)).inv := by
  rw [CochainComplex.homOfDegreewiseSplit_f]
  change (blockSplitting P Q w (-1)).s ≫
    (P.blockExtension Q w).toCochainComplex.d (-1) 0 ≫ (blockSplitting P Q w 0).r = _
  simp [blockSplitting, doubleSplitting, blockSequence, blockExtension, double_d _ adjacent (by decide),
    ShortComplex.Splitting.ofIso, ShortComplex.Splitting.ofHasBinaryBiproduct, ShortComplex.isoMk, ShortComplex.homMk, Category.assoc]

/-- Every connecting morphism between two-term complexes comes from an
off-diagonal entry over the original ring. -/
theorem exists_blockTriangle_of_connecting
    (δ : Q.homotopyObject ⟶ P.homotopyObject⟦(1 : ℤ)⟧) :
    ∃ w : Q.source ⟶ P.target, (blockTriangle P Q w).mor₃ = δ := by
  let F := HomotopyCategory.quotient (FGModuleCat R) (ComplexShape.up ℤ)
  let e := (F.commShiftIso (1 : ℤ)).app P.toCochainComplex
  obtain ⟨f, hf⟩ := F.map_surjective (δ ≫ e.inv)
  let w := (doubleXIso₀ Q.differential adjacent).inv ≫ f.f (-1) ≫
    (doubleXIso₁ P.differential adjacent (by decide)).hom
  refine ⟨w, ?_⟩
  have heq : CochainComplex.homOfDegreewiseSplit _ (blockSplitting P Q w) = f := by
    apply from_double_hom_ext
    · rw [blockConnecting_f]
      simp [w]
      rfl
    · exact (isZero_double_X P.differential adjacent 1 (by decide) (by decide)).eq_of_tgt _ _
  change F.map (CochainComplex.homOfDegreewiseSplit _ (blockSplitting P Q w)) ≫ e.hom = δ
  rw [heq]
  exact (congrArg (· ≫ e.hom) hf).trans (by simp)

/-- The middle term of every distinguished extension of two-term projective
complexes is represented by a block differential on their original terms. -/
theorem exists_iso_blockExtension {T : Triangle (HomotopyCategory (FGModuleCat R) (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang _) (i : T.obj₁ ≅ P.homotopyObject) (j : T.obj₃ ≅ Q.homotopyObject) :
    ∃ w : Q.source ⟶ P.target, Nonempty (T.obj₂ ≅ (P.blockExtension Q w).homotopyObject) := by
  obtain ⟨w, hw⟩ := exists_blockTriangle_of_connecting P Q
    (j.inv ≫ T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map i.hom)
  let e := isoTriangleOfIso₁₃ T (blockTriangle P Q w) hT (blockTriangle_distinguished P Q w) i j
    (by rw [hw]; exact (j.hom_inv_id_assoc _).symm)
  exact ⟨w, ⟨Triangle.π₂.mapIso e⟩⟩

end EFiniteCharacterizations.TwoTerm
