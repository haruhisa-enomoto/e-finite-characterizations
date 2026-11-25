module

public import EFiniteCharacterizations.Subcategories.TorsionApproximations
public import EFiniteCharacterizations.Stability.SemistablePowers

/-! # Approximations by semistable modules -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R] [IsNoetherianRing R]

private theorem semistable_biproduct_copies {θ : Weight (FGModuleCat.{u} R)}
    {G : FGModuleCat.{u} R} (hg : θ.IsSemistable G) (n : ℕ) :
    θ.IsSemistable (⨁ fun _ : Fin n ↦ G) := by
  let F := forget₂ (FGModuleCat R) (ModuleCat.{u} R)
  let A := fun _ : Fin n ↦ G
  let _ : PreservesBiproduct A F := preservesBiproduct_of_preservesCoproduct F
  let e : (⨁ A) ≅ FGModuleCat.of R (Fin n → G) :=
    F.preimageIso ((F.mapBiproduct A).trans (ModuleCat.biproductIsoPi (fun _ : Fin n ↦ G.obj)))
  exact (hg.finPower n).of_iso e.symm

include k in
private theorem exists_semistable_rightApproximation {θ : Weight (FGModuleCat.{u} R)}
    {G : FGModuleCat.{u} R} (hg : θ.IsSemistable G)
    (hgen : ∀ Y, θ.IsSemistable Y → IsGeneratedBy G Y) (X : FGModuleCat.{u} R) :
    ∃ (D : FGModuleCat.{u} R) (p : D ⟶ X), θ.IsSemistable D ∧
      ∀ Y, θ.IsSemistable Y → ∀ f : Y ⟶ X, ∃ t, t ≫ p = f := by
  have := finiteModuleHom_isFinite k G X
  let n := Module.finrank k (G ⟶ X)
  let A := fun _ : Fin n ↦ G
  let b := Module.finBasis k (G ⟶ X)
  let e : (⨁ A) ⟶ X := biproduct.desc b
  have hA := semistable_biproduct_copies hg n
  obtain ⟨T, j, hj, hT, hkill⟩ := TwoTerm.exists_generated_subobject_killing_hom k G (kernel e)
  let i := j ≫ kernel.ι e
  obtain ⟨m, q, hq⟩ := hT
  have hT' : θ.IsSemistable T := hA.of_mono_of_eval_zero i (le_antisymm (hA.2 i)
    (((Weight.isSemistable_iff_quotients _).1 (semistable_biproduct_copies hg m)).2 q))
  let π := cokernel.π i
  let p := cokernel.desc i e (by simp [i])
  refine ⟨_, p, hT'.cokernel_of_mono hA i, fun Y hY f ↦ ?_⟩
  obtain ⟨l, r, hr⟩ := hgen Y hY
  let L := fun _ : Fin l ↦ G
  have fac (v : G ⟶ X) : ∃ w : G ⟶ ⨁ A, w ≫ e = v := by
    refine ⟨∑ a, b.repr v a • biproduct.ι A a, ?_⟩
    simp [e, Preadditive.sum_comp, Linear.smul_comp, b.sum_repr]
  choose w hw using fun a : Fin l ↦ fac (biproduct.ι L a ≫ r ≫ f)
  let t := biproduct.desc w
  have ht : t ≫ e = r ≫ f := by
    apply biproduct.hom_ext'
    intro a
    rw [show biproduct.ι L a ≫ t ≫ e = w a ≫ e by simp [t], hw]
  have hk := hgen _ ((semistable_biproduct_copies hg l).kernel_of_epi hY r)
  have hker : kernel.ι r ≫ t ≫ π = 0 := by
    apply hk.hom_eq_zero
    intro g
    let v := g ≫ kernel.ι r ≫ t
    have hv : v ≫ e = 0 := by simp [v, ht]
    let v' := kernel.lift e v hv
    let s := Abelian.monoLift j v' (hkill v')
    have hsi : s ≫ i = v := by rw [show s ≫ i = (s ≫ j) ≫ kernel.ι e from (Category.assoc ..).symm,
      Abelian.monoLift_comp, kernel.lift_ι]
    change g ≫ kernel.ι r ≫ t ≫ π = 0
    simpa only [v, Category.assoc] using
      (show v ≫ π = 0 by rw [← hsi, Category.assoc, cokernel.condition, comp_zero])
  let d := Abelian.epiDesc r (t ≫ π) hker
  refine ⟨d, (cancel_epi r).1 ?_⟩
  rw [← Category.assoc, Abelian.comp_epiDesc, Category.assoc, cokernel.π_desc, ht]

/-- The semistable modules of a presilting weight admit both approximations
over any finite-dimensional algebra. -/
theorem TwoTerm.functoriallyFinite_semistable (P : TwoTerm R) (hP : P.IsPresilting) :
    FunctoriallyFinite (P.eulerWeight k).IsSemistable := by
  have hweak := P.functoriallyFinite_weakTorsionClass k hP
  obtain ⟨G, hg, hgen, _⟩ := P.exists_semistable_projective_generator k hP
  refine ⟨fun X ↦ ?_, exists_semistable_rightApproximation k hg hgen⟩
  obtain ⟨B, a, hB, ha⟩ := hweak.1 X
  obtain ⟨D, p, _, hD, hp⟩ := exists_semistable_quotient_approximation k _ B hB
  refine ⟨D, a ≫ p, hD, fun Y hy f ↦ ?_⟩
  obtain ⟨b, hb⟩ := ha Y ((Weight.isSemistable_iff_quotients Y).1 hy).2 f
  obtain ⟨c, hc⟩ := hp Y hy b
  exact ⟨c, by rw [Category.assoc, hc, hb]⟩

include k in
theorem isEFinite_iff_functoriallyFinite_semistable [IsArtinianRing R] :
    IsEFinite R ↔ ∀ g : ProjectiveClass R, FunctoriallyFinite (projectiveClassWeight k g).IsSemistable := by
  refine ⟨fun h g ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨P,hP,rfl⟩ := h g
    rw [P.projectiveClassWeight_eq_eulerWeight k]
    exact P.functoriallyFinite_semistable k hP
  · apply (isEFinite_iff_stableFiniteAtAllIntegralWeights_allFields k).2
    intro g
    obtain ⟨G, a, hG, ha⟩ := (h g).1 (FGModuleCat.of R R)
    exact finite_stableClasses_of_regular_approximation k hG a fun S hs ↦ ha S hs.isSemistable

end EFiniteCharacterizations
