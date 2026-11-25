module

public import EFiniteCharacterizations.Silting.Reduction.Bongartz
public import EFiniteCharacterizations.Stability.SemistableExact

/-! # Projective objects at a covered weight -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

include k in
/-- A retract of a Bongartz cokernel has a universal semistable quotient.
The quotient is projective among the semistable modules, and its
endomorphisms lift to endomorphisms of the retract. -/
theorem exists_semistable_projective_quotient_of_retract
    (P : TwoTerm R) (hP : P.IsPresilting) (Q : TwoTerm R)
    (hb : Function.Surjective (P.precompose (cokernel Q.differential)))
    (hQ : ∀ M : FGModuleCat.{u} R, Function.Surjective (P.precompose M) →
      Function.Surjective (Q.precompose M))
    {D : FGModuleCat.{u} R} (s : D ⟶ cokernel Q.differential) (r : cokernel Q.differential ⟶ D)
    (hs : s ≫ r = 𝟙 D) :
    ∃ (G : FGModuleCat.{u} R) (p : D ⟶ G), Epi p ∧ (P.eulerWeight k).IsSemistable G ∧
      (∀ {M : FGModuleCat.{u} R}, (P.eulerWeight k).IsSemistable M →
        ∀ f : D ⟶ M, ∃ g : G ⟶ M, p ≫ g = f) ∧
      (∀ {M N : FGModuleCat.{u} R} (q : M ⟶ N) [Epi q],
        (P.eulerWeight k).IsSemistable M → (P.eulerWeight k).IsSemistable N →
        ∀ f : G ⟶ N, ∃ g : G ⟶ M, g ≫ q = f) ∧
      ∀ a : G ⟶ G, ∃ e : D ⟶ D, e ≫ p = p ≫ a := by
  let B := cokernel Q.differential
  let θ := P.eulerWeight k
  have hB := (P.surjective_precompose_iff_no_hom_nakayamaKernel k B).1 hb
  have hD : Subsingleton (D ⟶ P.nakayamaKernel k) := by
    have : Epi r := epi_of_epi_fac hs
    exact ⟨fun f g ↦ (cancel_epi r).1 (hB.elim _ _)⟩
  obtain ⟨I, i, hi, hI, hG⟩ := P.exists_semistable_quotient_of_no_hom_nakayamaKernel k hP D hD
  let G := cokernel i
  let p := cokernel.π i
  have hdesc {M : FGModuleCat.{u} R} (hM : θ.IsSemistable M) (f : D ⟶ M) :
      ∃ g : G ⟶ M, p ≫ g = f := by
    have h := ((P.isSemistable_eulerWeight_iff_perpendicular k hP M).1 hM).1
    have hvan : i ≫ f = 0 := hI.hom_eq_zero (i ≫ f) (fun g ↦ h.elim _ _)
    exact ⟨cokernel.desc i f hvan, cokernel.π_desc _ _ _⟩
  have hlift {K M N : FGModuleCat.{u} R} {j : K ⟶ M} {q : M ⟶ N} [Epi q]
      (hj : j ≫ q = 0) (he : (ShortComplex.mk j q hj).Exact)
      (hK : Function.Surjective (P.precompose K)) (f : D ⟶ N) :
      ∃ g : D ⟶ M, g ≫ q = f := by
    obtain ⟨g, hg⟩ := Q.exists_cokernel_hom_lift hj he (hQ K hK) (r ≫ f)
    exact ⟨s ≫ g, by rw [Category.assoc, hg, ← Category.assoc, hs, Category.id_comp]⟩
  refine ⟨G, p, inferInstance, hG, fun hM f ↦ hdesc hM f, ?_, ?_⟩
  · intro M N q _ hM hN f
    have hK := hM.kernel_of_epi hN q
    have hKQ := ((P.isSemistable_eulerWeight_iff_perpendicular k hP _).1 hK).2
    have hk := (P.surjective_precompose_iff_no_hom_nakayamaKernel k _).2 hKQ
    obtain ⟨g, hg⟩ := hlift (kernel.condition q) (ShortComplex.exact_kernel q) hk (p ≫ f)
    obtain ⟨l, hl⟩ := hdesc hM g
    refine ⟨l, (cancel_epi p).1 ?_⟩
    rw [← Category.assoc, hl, hg]
  · intro a
    have hX := (surjective_boundary_iff_surjective_precompose P P).1 hP
    exact hlift (cokernel.condition i) (ShortComplex.exact_cokernel i)
      (P.surjective_precompose_of_generatedBy hX hI) (p ≫ a)

include k in
/-- The semistable category at the Euler weight of a presilting complex
has a finite projective generator. The generator is obtained by dividing
the Bongartz cokernel by the trace of the original cokernel. -/
theorem exists_semistable_projective_generator (P : TwoTerm R) (hP : P.IsPresilting) :
    ∃ G : FGModuleCat.{u} R,
      (P.eulerWeight k).IsSemistable G ∧
      (∀ M : FGModuleCat.{u} R, (P.eulerWeight k).IsSemistable M → IsGeneratedBy G M) ∧
      ∀ {M N : FGModuleCat.{u} R} (q : M ⟶ N) [Epi q],
        (P.eulerWeight k).IsSemistable M → (P.eulerWeight k).IsSemistable N →
        ∀ f : G ⟶ N, ∃ g : G ⟶ M, g ≫ q = f := by
  obtain ⟨Q, hpQ, hQ, hgen⟩ := P.exists_bongartz_complement k hP
  let B := cokernel Q.differential
  obtain ⟨G, p, _, hG, hdesc, hproj, _⟩ := P.exists_semistable_projective_quotient_of_retract
    k hP Q hpQ hQ (𝟙 B) (𝟙 B) (Category.id_comp _)
  refine ⟨G, hG, ?_, hproj⟩
  intro M hM
  have hMQ := ((P.isSemistable_eulerWeight_iff_perpendicular k hP M).1 hM).2
  have hMB : IsGeneratedBy B M :=
    (hgen M).1 ((P.surjective_precompose_iff_no_hom_nakayamaKernel k M).2 hMQ)
  obtain ⟨U, j, _, hU, hj⟩ := exists_generated_subobject_killing_hom k G M
  have hz : cokernel.π j = 0 := hMB.hom_eq_zero _ (fun f ↦ by
    obtain ⟨g, hg⟩ := hdesc hM f
    rw [← hg, Category.assoc, hj, comp_zero])
  have : Epi j := Abelian.epi_of_cokernel_π_eq_zero _ hz
  exact hU.of_epi j

end EFiniteCharacterizations.TwoTerm
