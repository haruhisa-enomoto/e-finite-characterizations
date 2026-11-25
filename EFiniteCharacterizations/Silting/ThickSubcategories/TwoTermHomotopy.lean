module

public import EFiniteCharacterizations.Presentations.TwoTerm
public import EFiniteCharacterizations.Silting.ThickSubcategories.PresiltingSummand
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Two-term presentations in the homotopy category -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex.HomComplex
open scoped ZeroObject

universe u
namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R] [IsNoetherianRing R] (P Q : TwoTerm R)

theorem adjacent : (ComplexShape.up ℤ).Rel (-1) 0 := rfl

/-- The cochain complex with differential in degrees −1 and 0. -/
noncomputable abbrev toCochainComplex : CochainComplex (FGModuleCat.{u} R) ℤ :=
  double P.differential adjacent

/-- The object represented by this differential in the homotopy category. -/
noncomputable abbrev homotopyObject :=
  (HomotopyCategory.quotient _ _).obj P.toCochainComplex

private noncomputable abbrev srcIso := doubleXIso₀ P.differential adjacent
private noncomputable abbrev tgtIso := doubleXIso₁ P.differential adjacent (by decide)

private theorem outside_zero {n : ℤ} (hn : n < -1 ∨ 1 < n) (z : Cochain P.toCochainComplex Q.toCochainComplex n) :
    z = 0 := by
  apply Cochain.ext
  intro i j h
  by_cases hi : i = -1 ∨ i = 0
  · apply (isZero_double_X Q.differential adjacent j (by omega) (by omega)).eq_of_tgt
  · apply (isZero_double_X P.differential adjacent i (by tauto) (by tauto)).eq_of_src

private theorem one_ext {x y : Cochain P.toCochainComplex Q.toCochainComplex 1}
    (h : x.v (-1) 0 rfl = y.v (-1) 0 rfl) : x = y := by
  apply Cochain.ext
  intro i j hij
  by_cases hi : i = -1
  · obtain rfl := hi
    obtain rfl : j = 0 := by omega
    exact h
  by_cases hi' : i = 0
  · exact (isZero_double_X Q.differential adjacent j (by omega) (by omega)).eq_of_tgt _ _
  exact (isZero_double_X P.differential adjacent i hi hi').eq_of_src _ _

private noncomputable def degreeOne : (P.source ⟶ Q.target) ≃+ Cocycle P.toCochainComplex Q.toCochainComplex 1 where
  toFun f := Cocycle.mk (Cochain.single (P.srcIso.hom ≫ f ≫ Q.tgtIso.inv) 1) 2 rfl
    (outside_zero P Q (by decide) _)
  invFun z := P.srcIso.inv ≫ z.val.v (-1) 0 rfl ≫ Q.tgtIso.hom
  left_inv f := by simp [Cocycle.mk]
  right_inv z := by
    apply Subtype.ext
    apply one_ext P Q
    simp [Cocycle.mk]
  map_add' f g := by
    apply Subtype.ext
    apply one_ext P Q
    change (Cochain.single (P.srcIso.hom ≫ (f + g) ≫ Q.tgtIso.inv) 1).v (-1) 0 rfl =
      (Cochain.single (P.srcIso.hom ≫ f ≫ Q.tgtIso.inv) 1 +
        Cochain.single (P.srcIso.hom ≫ g ≫ Q.tgtIso.inv) 1).v (-1) 0 rfl
    simp [Preadditive.comp_add, Preadditive.add_comp]

private theorem degreeOne_v (f : P.source ⟶ Q.target) :
    ((degreeOne P Q f).val).v (-1) 0 rfl = P.srcIso.hom ≫ f ≫ Q.tgtIso.inv :=
  Cochain.single_v _ _ _

private noncomputable def classMap :=
  (CohomologyClass.mkAddMonoidHom P.toCochainComplex Q.toCochainComplex 1).comp (degreeOne P Q).toAddMonoidHom

private theorem classMap_kernel : (classMap P Q).ker = (homotopyBoundary P Q).range := by
  ext f
  change CohomologyClass.mk (degreeOne P Q f) = 0 ↔ _
  rw [CohomologyClass.mk_eq_zero_iff,mem_coboundaries_iff (degreeOne P Q f) 0 (by decide)]
  constructor
  · rintro ⟨β,hβ⟩
    let a := P.srcIso.inv ≫ β.v (-1) (-1) rfl ≫ Q.srcIso.hom
    let b := P.tgtIso.inv ≫ β.v 0 0 rfl ≫ Q.tgtIso.hom
    refine ⟨(a,b),?_⟩
    have h := congrArg (fun z : Cochain P.toCochainComplex Q.toCochainComplex 1 ↦
      P.srcIso.inv ≫ z.v (-1) 0 rfl ≫ Q.tgtIso.hom) hβ
    simpa [degreeOne_v,homotopyBoundary,a,b,srcIso,tgtIso,double_d _ adjacent (by decide),
      Preadditive.sub_comp,Preadditive.comp_sub] using h
  · rintro ⟨⟨a,b⟩,rfl⟩
    let left := P.srcIso.hom ≫ a ≫ Q.srcIso.inv
    let right := P.tgtIso.hom ≫ b ≫ Q.tgtIso.inv
    refine ⟨Cochain.single left 0 + Cochain.single right 0,one_ext P Q ?_⟩
    simp [left,right,degreeOne_v,homotopyBoundary,srcIso,tgtIso,double_d _ adjacent (by decide),
      Cochain.single_v_eq_zero, sub_eq_add_neg]

private noncomputable def classHomEquiv (n : ℤ) :
    CohomologyClass P.toCochainComplex Q.toCochainComplex n ≃+ (P.homotopyObject ⟶ Q.homotopyObject⟦n⟧) :=
  CohomologyClass.homAddEquiv.trans (Linear.homCongr ℤ (Iso.refl _)
    (((HomotopyCategory.quotient _ _).commShiftIso n).app Q.toCochainComplex)).toAddEquiv

/-- The boundary quotient of two projective differentials is the actual
degree-one Hom group in the homotopy category. -/
@[no_expose] noncomputable def shiftedHomEquiv : P.ShiftedHom Q ≃+ (P.homotopyObject ⟶ Q.homotopyObject⟦(1 : ℤ)⟧) :=
  (QuotientAddGroup.quotientAddEquivOfEq (classMap_kernel P Q).symm).trans <|
    (QuotientAddGroup.quotientKerEquivOfSurjective (classMap P Q)
      (CohomologyClass.mk_surjective.comp (degreeOne P Q).surjective)).trans (classHomEquiv P Q 1)

theorem subsingleton_hom_shift_outside {n : ℤ} (hn : n < -1 ∨ 1 < n) :
    Subsingleton (P.homotopyObject ⟶ Q.homotopyObject⟦n⟧) := by
  have : Subsingleton (Cocycle P.toCochainComplex Q.toCochainComplex n) :=
    ⟨fun z w ↦ Subtype.ext ((outside_zero P Q hn _).trans (outside_zero P Q hn _).symm)⟩
  have : Subsingleton (CohomologyClass P.toCochainComplex Q.toCochainComplex n) :=
    CohomologyClass.mk_surjective.subsingleton
  exact (classHomEquiv P Q n).surjective.subsingleton

theorem subsingleton_hom_shift_of_one_lt {n : ℤ} (hn : 1 < n) :
    Subsingleton (P.homotopyObject ⟶ Q.homotopyObject⟦n⟧) :=
  subsingleton_hom_shift_outside P Q (Or.inr hn)

open scoped ModuleCat.Algebra in
/-- The map to actual degree-one morphisms is linear over the ground field,
with kernel exactly the null-homotopic boundaries. -/
theorem exists_linear_shiftedHom_quotient (k : Type u) [Field k] [Algebra k R] :
    ∃ φ : (P.source ⟶ Q.target) →ₗ[k] (P.homotopyObject ⟶ Q.homotopyObject⟦(1 : ℤ)⟧),
      Function.Surjective φ ∧ ∀ f, φ f = 0 ↔ f ∈ (homotopyBoundary P Q).range := by
  let F := HomotopyCategory.quotient (FGModuleCat.{u} R) (ComplexShape.up ℤ)
  let m := (classHomEquiv P Q 1).toAddMonoidHom.comp (classMap P Q)
  have hlin (a : k) (f : P.source ⟶ Q.target) : m (a • f) = a • m f := by
    let g : End P.toCochainComplex := a • 𝟙 P.toCochainComplex
    have hz : degreeOne P Q (a • f) = (degreeOne P Q f).precomp g := by
      apply Subtype.ext
      apply one_ext P Q
      simp [degreeOne_v,g,Cocycle.precomp,Linear.comp_smul,Linear.smul_comp]
    let j := ((F.commShiftIso (1 : ℤ)).app Q.toCochainComplex).hom
    change F.map (Cocycle.equivHomShift.symm (degreeOne P Q (a • f))) ≫ j =
      a • (F.map (Cocycle.equivHomShift.symm (degreeOne P Q f)) ≫ j)
    rw [hz,Cocycle.equivHomShift_symm_precomp,F.map_comp]
    simp [g,Functor.map_smul,Linear.smul_comp]
  refine ⟨{ m with map_smul' := hlin },(classHomEquiv P Q 1).surjective.comp
    (CohomologyClass.mk_surjective.comp (degreeOne P Q).surjective),?_⟩
  intro f
  change classHomEquiv P Q 1 (classMap P Q f) = 0 ↔ _
  rw [map_eq_zero_iff _ (classHomEquiv P Q 1).injective,← classMap_kernel]
  rfl

/-- For two-term complexes, surjectivity of the boundary map detects
orthogonality in every positive shift. -/
theorem surjective_boundary_iff_homotopy : Function.Surjective (homotopyBoundary P Q) ↔
    ∀ n : ℤ, 0 < n → Subsingleton (P.homotopyObject ⟶ Q.homotopyObject⟦n⟧) := by
  rw [surjective_boundary_iff_subsingleton_shiftedHom]
  constructor
  · intro h n hn
    rcases eq_or_lt_of_le (show 1 ≤ n by omega) with rfl | h'
    · exact (shiftedHomEquiv P Q).surjective.subsingleton
    · exact subsingleton_hom_shift_of_one_lt P Q h'
  · intro h
    have := h 1 (by decide)
    exact (shiftedHomEquiv P Q).injective.subsingleton

/-- The presentation criterion agrees with presilting in all positive shifts. -/
theorem isPresilting_iff_homotopy : P.IsPresilting ↔
    ∀ n : ℤ, 0 < n → Subsingleton (P.homotopyObject ⟶ P.homotopyObject⟦n⟧) :=
  surjective_boundary_iff_homotopy P P

/-- A two-term complex in the thick closure of a presilting differential
is a summand of a finite sum of copies if the two boundary maps are onto. -/
theorem isInAdd_of_mem_thick (hp : P.IsPresilting)
    (hq : (ObjectProperty.singleton P.homotopyObject).triangEnvelope Q.homotopyObject)
    (hPQ : Function.Surjective (homotopyBoundary P Q))
    (hQP : Function.Surjective (homotopyBoundary Q P)) :
    IsInAdd Q.homotopyObject P.homotopyObject :=
  Presilting.isInAdd_of_mem_thick _ ((isPresilting_iff_homotopy P).1 hp) hq
    ((surjective_boundary_iff_homotopy P Q).1 hPQ) ((surjective_boundary_iff_homotopy Q P).1 hQP)

private theorem negOne_ext {z w : Cochain P.toCochainComplex Q.toCochainComplex (-1)}
    (h : z.v 0 (-1) rfl = w.v 0 (-1) rfl) : z = w := by
  apply Cochain.ext
  intro i j hij
  by_cases hi : i = 0
  · obtain rfl := hi
    obtain rfl : j = -1 := by omega
    exact h
  by_cases hs : i = -1
  · apply (isZero_double_X Q.differential adjacent j (by omega) (by omega)).eq_of_tgt
  exact (isZero_double_X P.differential adjacent i hs hi).eq_of_src _ _

private noncomputable abbrev negOneMap (f : cokernel P.differential ⟶ kernel Q.differential) :=
  P.tgtIso.hom ≫ cokernel.π P.differential ≫ f ≫ kernel.ι Q.differential ≫ Q.srcIso.inv

private noncomputable def negOneCycle (f : cokernel P.differential ⟶ kernel Q.differential) :
    Cocycle P.toCochainComplex Q.toCochainComplex (-1) :=
  Cocycle.mk (Cochain.single (negOneMap P Q f) (-1)) 0 rfl (by
    rw [Cochain.δ_single _ (-1) 0 rfl (-1) 0 rfl rfl]
    simp [negOneMap,toCochainComplex,srcIso,tgtIso,double_d _ adjacent (by decide),
      Category.assoc,cokernel.condition_assoc,kernel.condition_assoc])

private theorem negOneCycle_bijective : Function.Bijective (negOneCycle P Q) := by
  constructor
  · intro f g h
    have hh := congrArg (fun z : Cocycle P.toCochainComplex Q.toCochainComplex (-1) ↦ z.val.v 0 (-1) rfl) h
    change (Cochain.single _ (-1)).v 0 (-1) rfl = (Cochain.single _ (-1)).v 0 (-1) rfl at hh
    simp only [Cochain.single_v,negOneMap] at hh
    simpa only [← Category.assoc,cancel_mono,cancel_epi] using hh
  · intro z
    let v := P.tgtIso.inv ≫ z.val.v 0 (-1) rfl ≫ Q.srcIso.hom
    have dz := z.δ_eq_zero 0
    have hp : P.differential ≫ v = 0 := by
      have hh := Cochain.congr_v dz (-1) (-1) rfl
      rw [δ_v (-1) 0 rfl z.val (-1) (-1) rfl (-2) 0 rfl rfl] at hh
      rw [(isZero_double_X Q.differential adjacent (-2) (by decide) (by decide)).eq_of_tgt
        (z.val.v (-1) (-2) rfl) 0] at hh
      have eq := congrArg (fun w ↦ P.srcIso.inv ≫ w ≫ Q.srcIso.hom) hh
      simpa [v,srcIso,tgtIso,toCochainComplex,double_d _ adjacent (by decide),Category.assoc] using eq
    have hq : v ≫ Q.differential = 0 := by
      have hh := Cochain.congr_v dz 0 0 rfl
      rw [δ_v (-1) 0 rfl z.val 0 0 rfl (-1) 1 rfl rfl] at hh
      rw [(isZero_double_X P.differential adjacent 1 (by decide) (by decide)).eq_of_src
        (z.val.v 1 0 rfl) 0] at hh
      have eq := congrArg (fun w ↦ P.tgtIso.inv ≫ w ≫ Q.tgtIso.hom) hh
      simpa [v,srcIso,tgtIso,toCochainComplex,double_d _ adjacent (by decide),Category.assoc] using eq
    let a := kernel.lift Q.differential v hq
    have ha : P.differential ≫ a = 0 := (cancel_mono (kernel.ι Q.differential)).1 (by simp [a,hp])
    refine ⟨cokernel.desc P.differential a ha,Subtype.ext (negOne_ext P Q ?_)⟩
    change (Cochain.single _ (-1)).v 0 (-1) rfl = _
    simp [negOneMap,a,v,Category.assoc]

open scoped ModuleCat.Algebra in
/-- A map to the negative shift factors uniquely through the cokernel of
the source differential and the kernel of the target differential. -/
@[no_expose] noncomputable def negOneHomEquiv (k : Type u) [Field k] [Algebra k R] :
    (cokernel P.differential ⟶ kernel Q.differential) ≃ₗ[k]
      (P.homotopyObject ⟶ Q.homotopyObject⟦(-1 : ℤ)⟧) := by
  let F := HomotopyCategory.quotient (FGModuleCat.{u} R) (ComplexShape.up ℤ)
  let j := ((F.commShiftIso (-1 : ℤ)).app Q.toCochainComplex).hom
  let c := CohomologyClass.mkAddMonoidHom P.toCochainComplex Q.toCochainComplex (-1)
  have hc : Function.Injective c := by
    apply (injective_iff_map_eq_zero _).2
    intro z hz
    rw [show c z = CohomologyClass.mk z from rfl,CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff z (-2) rfl] at hz
    obtain ⟨b,hb⟩ := hz
    rw [outside_zero P Q (by decide) b] at hb
    exact Subtype.ext (by simpa using hb.symm)
  let m := fun f ↦ classHomEquiv P Q (-1) (c (negOneCycle P Q f))
  apply LinearEquiv.ofBijective (f := { toFun := m, map_add' := ?_, map_smul' := ?_ })
    ((classHomEquiv P Q (-1)).bijective.comp
      ((show Function.Bijective c from ⟨hc,CohomologyClass.mk_surjective⟩).comp (negOneCycle_bijective P Q)))
  · intro f g
    change classHomEquiv P Q (-1) (c _) = classHomEquiv P Q (-1) (c _) + classHomEquiv P Q (-1) (c _)
    rw [← map_add,← map_add]
    apply congrArg (fun z ↦ classHomEquiv P Q (-1) (c z))
    apply Subtype.ext
    apply negOne_ext P Q
    change (Cochain.single _ (-1)).v 0 (-1) rfl = (Cochain.single _ (-1) + Cochain.single _ (-1)).v 0 (-1) rfl
    simp [negOneCycle,Cocycle.mk,negOneMap,Preadditive.add_comp,Preadditive.comp_add]
  · intro a f
    let g : End P.toCochainComplex := a • 𝟙 P.toCochainComplex
    have hz : negOneCycle P Q (a • f) = (negOneCycle P Q f).precomp g := by
      apply Subtype.ext
      apply negOne_ext P Q
      simp [negOneCycle,Cocycle.mk,negOneMap,g,Cocycle.precomp,Linear.smul_comp,Linear.comp_smul]
    change F.map (Cocycle.equivHomShift.symm (negOneCycle P Q (a • f))) ≫ j =
      a • (F.map (Cocycle.equivHomShift.symm (negOneCycle P Q f)) ≫ j)
    rw [hz,Cocycle.equivHomShift_symm_precomp,F.map_comp]
    simp [g,Functor.map_smul,Linear.smul_comp]

end EFiniteCharacterizations.TwoTerm
