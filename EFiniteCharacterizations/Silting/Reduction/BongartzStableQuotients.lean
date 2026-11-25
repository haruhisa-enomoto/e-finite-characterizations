module

public import EFiniteCharacterizations.Silting.Reduction.PerpendicularGenerator
public import EFiniteCharacterizations.Modules.IndecomposableProjectives

/-! # Indecomposable summands in a Bongartz completion mapping to a stable module -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- Relative projectivity with respect to epimorphisms whose kernel is in
the weak torsion class of the differential. -/
def LiftsOverWeakTorsion (P : TwoTerm R) (D : FGModuleCat.{u} R) : Prop :=
  ∀ {K M N : FGModuleCat.{u} R} (i : K ⟶ M) (q : M ⟶ N) [Epi q] (h : i ≫ q = 0),
    (ShortComplex.mk i q h).Exact → Function.Surjective (P.precompose K) →
    ∀ f : D ⟶ N, ∃ a : D ⟶ M, a ≫ q = f

theorem liftsOverWeakTorsion_of_bongartz_retract (P Q : TwoTerm R)
    (hQ : ∀ M : FGModuleCat.{u} R, Function.Surjective (P.precompose M) →
      Function.Surjective (Q.precompose M)) {D : FGModuleCat.{u} R}
    (s : D ⟶ cokernel Q.differential) (r : cokernel Q.differential ⟶ D) (hs : s ≫ r = 𝟙 D) :
    P.LiftsOverWeakTorsion D := by
  intro K M N i q _ hi he hk f
  obtain ⟨a,ha⟩ := Q.exists_cokernel_hom_lift hi he (hQ _ hk) (r ≫ f)
  exact ⟨s ≫ a,by rw [Category.assoc,ha,← Category.assoc,hs,Category.id_comp]⟩

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

/-- A nonzero map from an object in the weak torsion class to a stable
object lifts maps from each relative projective. -/
theorem lift_to_stable_quotient (P : TwoTerm R) (hp : P.IsPresilting) {D E B : FGModuleCat.{u} R}
    (hD : P.LiftsOverWeakTorsion D) (hE : Function.Surjective (P.precompose E))
    (hB : (P.eulerWeight k).IsStable B) (q : E ⟶ B) (hq : q ≠ 0) (f : D ⟶ B) :
    ∃ a : D ⟶ E, a ≫ q = f := by
  obtain ⟨I,i,hi,hI,hW⟩ := P.exists_semistable_quotient_of_no_hom_nakayamaKernel k hp E
    ((P.surjective_precompose_iff_no_hom_nakayamaKernel k E).1 hE)
  have hperp := ((P.isSemistable_eulerWeight_iff_perpendicular k hp B).1 hB.isSemistable).1
  have hvan : i ≫ q = 0 := hI.hom_eq_zero _ fun g ↦ hperp.elim _ _
  let p := cokernel.desc i q hvan
  have hc : cokernel.π i ≫ p = q := cokernel.π_desc _ _ _
  have hne : p ≠ 0 := fun hz ↦ hq (by rw [← hc,hz,comp_zero])
  have := Weight.epi_of_isSemistable_of_isStable hW hB p hne
  have hK := hW.kernel_of_epi hB.isSemistable p
  have hKs := ((P.isSemistable_eulerWeight_iff_perpendicular k hp _).1 hK).2
  obtain ⟨b,hb⟩ := hD (kernel.ι p) p (kernel.condition p) (ShortComplex.exact_kernel p)
    ((P.surjective_precompose_iff_no_hom_nakayamaKernel k _).2 hKs) f
  have hIs := P.surjective_precompose_of_generatedBy
    ((surjective_boundary_iff_surjective_precompose P P).1 hp) hI
  obtain ⟨a,ha⟩ := hD i (cokernel.π i) (cokernel.condition i) (ShortComplex.exact_cokernel i) hIs b
  exact ⟨a,by rw [← hc,← Category.assoc,ha,hb]⟩

/-- At most one isomorphism type of indecomposable relative projective in
the weak torsion class maps nontrivially to a specified stable module. -/
theorem iso_of_common_stable_quotient (P : TwoTerm R) (hp : P.IsPresilting) {D E B : FGModuleCat.{u} R}
    (hD : Indecomposable D) (hE : Indecomposable E)
    (hlD : P.LiftsOverWeakTorsion D) (hlE : P.LiftsOverWeakTorsion E)
    (hsD : Function.Surjective (P.precompose D)) (hsE : Function.Surjective (P.precompose E))
    (hB : (P.eulerWeight k).IsStable B) (p : D ⟶ B) (q : E ⟶ B) (hp' : p ≠ 0) (hq : q ≠ 0) :
    Nonempty (D ≅ E) := by
  obtain ⟨a,ha⟩ := P.lift_to_stable_quotient k hp hlD hsE hB q hq p
  obtain ⟨b,hb⟩ := P.lift_to_stable_quotient k hp hlE hsD hB p hp' q
  have := IsArtinianRing.of_finite k R
  have : IsIso (a ≫ b) := FGModuleCat.isIso_of_quotient_eq_self hD p hp' _ (by rw [Category.assoc,hb,ha])
  have : IsIso (b ≫ a) := FGModuleCat.isIso_of_quotient_eq_self hE q hq _ (by rw [Category.assoc,ha,hb])
  have : Mono a := ⟨fun x y h ↦ (cancel_mono (a ≫ b)).mp (by simp only [← Category.assoc,h])⟩
  have : Epi a := ⟨fun x y h ↦ (cancel_epi (b ≫ a)).mp (by simp only [Category.assoc,h])⟩
  have : IsIso a := isIso_of_mono_of_epi a
  exact ⟨asIso a⟩

end EFiniteCharacterizations.TwoTerm
