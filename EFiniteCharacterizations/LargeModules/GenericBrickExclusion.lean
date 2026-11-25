module

public import EFiniteCharacterizations.LargeModules.GrainSocle
public import EFiniteCharacterizations.Silting.ThickSubcategories.ThickInversion
public import EFiniteCharacterizations.Stability.IntegralDivisionWeight
public import EFiniteCharacterizations.LargeModules.GenericBrickReduction
public import EFiniteCharacterizations.Stability.OppositeAlgebra

/-! # Exclusion of generic bricks over E-finite algebras -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] (D : Type u) [DivisionRing D]
  (M : ModuleCat.{u} R) [Module D M] [SMulCommClass R D M] [Module.Finite D M]

include k in
/-- The division-ring span of the image of a map killed by the differential
is generated over R by copies of its cokernel. Semistability forces this
span to vanish. -/
private theorem zero_of_divisionSemistable (P : TwoTerm R) (hp : P.IsPresilting)
    (hs : DivisionSemistable D P.projectiveClass M) (f : P.target →ₗ[R] M)
    (hf : f.comp P.differential.hom.hom = 0) : f = 0 := by
  let U := Submodule.span D (Set.range f)
  let V : Submodule R M :=
    { carrier := U
      zero_mem' := U.zero_mem
      add_mem' := U.add_mem
      smul_mem' := fun r x hx ↦ by
        induction hx using Submodule.span_induction with
        | mem _ h => obtain ⟨y,rfl⟩ := h; exact Submodule.subset_span ⟨r • y, f.map_smul r y⟩
        | zero => simp
        | add x y _ _ hx hy => simpa [smul_add] using U.add_mem hx hy
        | smul d x _ hx =>
          change r • d • x ∈ U
          rw [smul_comm r d x]
          exact U.smul_mem d hx }
  let N := ModuleCat.of R V
  let : Module D N := inferInstanceAs (Module D U)
  let : SMulCommClass R D N := ⟨fun r d x ↦ Subtype.ext (smul_comm r d (x.val : M))⟩
  have : Module.Finite D N := inferInstanceAs (Module.Finite D U)
  have hn := hs.2 N V.subtype Subtype.val_injective (fun _ _ ↦ rfl)
  have hsurj := P.surjective_precomposition_of_finite_quotient_tests k hp N (by
    intro Q q hq
    have hperp : Subsingleton (Q ⟶ P.nakayamaKernel k) := by
      suffices hz : ∀ l : Q ⟶ P.nakayamaKernel k, l = 0 from
        ⟨fun l l' ↦ (hz l).trans (hz l').symm⟩
      intro l
      let F := l.hom.hom.comp q.hom
      have hkill (d : D) (x : P.target) : F ⟨d • f x,U.smul_mem d (Submodule.subset_span ⟨x,rfl⟩)⟩ = 0 := by
        let g : P.target →ₗ[R] N := (d • f).codRestrict V fun y ↦ U.smul_mem d (Submodule.subset_span ⟨y,rfl⟩)
        let t : P.target ⟶ P.nakayamaKernel k := FGModuleCat.ofHom (F.comp g)
        have ht : P.differential ≫ t = 0 := by
          ext y
          change F (g (P.differential.hom.hom y)) = 0
          have hg : g (P.differential.hom.hom y) = 0 := Subtype.ext (by
            change d • f (P.differential.hom.hom y) = 0
            rw [show f (P.differential.hom.hom y) = 0 from LinearMap.congr_fun hf y,smul_zero])
          rw [hg,map_zero]
        have hxy := (P.isPresilting_iff_no_hom_nakayamaKernel k).1 hp
        have he := cokernel.π_desc _ t ht
        rw [hxy.elim (cokernel.desc _ t ht) 0,comp_zero] at he
        exact congrArg (fun z : P.target ⟶ P.nakayamaKernel k ↦ z.hom.hom x) he.symm
      have hzero (x : M) (hx : x ∈ U) : ∀ d : D, F ⟨d • x,U.smul_mem d hx⟩ = 0 := by
        induction hx using Submodule.span_induction with
        | mem x hx => obtain ⟨y,rfl⟩ := hx; exact fun d ↦ hkill d y
        | zero => intro d; exact (congrArg F (Subtype.ext (smul_zero d))).trans F.map_zero
        | add x y hx hy ih jh =>
          intro d
          have he : (⟨d • (x+y), U.smul_mem d (U.add_mem hx hy)⟩ : V) =
              ⟨d • x,U.smul_mem d hx⟩ + ⟨d • y,U.smul_mem d hy⟩ := Subtype.ext (smul_add ..)
          rw [he,map_add,ih,jh,add_zero]
        | smul c x hx ih =>
          intro d
          have he : (⟨d • c • x,U.smul_mem d (U.smul_mem c hx)⟩ : V) =
              ⟨(d*c) • x,U.smul_mem (d*c) hx⟩ := Subtype.ext (mul_smul ..).symm
          rw [he,ih]
      ext x
      obtain ⟨y,rfl⟩ := hq x
      exact (show F y = 0 by simpa using hzero y.val y.property 1)
    exact (P.nonneg_eulerWeight_all_quotients_iff k hp Q).2 hperp (𝟙 Q))
  have := finite_hom_over_division D N P.source
  have := finite_hom_over_division D N P.target
  let L := P.differential.hom.hom.lcomp D N
  have he : Module.finrank D (P.target →ₗ[R] N) = Module.finrank D (P.source →ₗ[R] N) := by
    rw [divisionEuler_twoTerm,sub_nonpos] at hn
    exact le_antisymm (by exact_mod_cast hn) (LinearMap.finrank_le_finrank_of_surjective (f := L) hsurj)
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := L) he).2 hsurj
  let g := f.codRestrict V fun x ↦ Submodule.subset_span ⟨x,rfl⟩
  have hz : g = 0 := hinj (show L g = L 0 from LinearMap.ext fun x ↦ Subtype.ext (LinearMap.congr_fun hf x))
  exact LinearMap.ext fun x ↦ congrArg Subtype.val (LinearMap.congr_fun hz x)

include k in
theorem TwoTerm.invertedOn_of_divisionSemistable (P : TwoTerm R) (hp : P.IsPresilting)
    (hs : DivisionSemistable D P.projectiveClass M) : P.InvertedOn M := by
  rw [P.invertedOn_iff_linear]
  let L := P.differential.hom.hom.lcomp D M
  have hi : Function.Injective L := LinearMap.ker_eq_bot.mp
    (LinearMap.ker_eq_bot'.2 fun f hf ↦ zero_of_divisionSemistable k D M P hp hs f hf)
  have he := hs.1
  rw [divisionEuler_twoTerm,sub_eq_zero] at he
  have := finite_hom_over_division D M P.source
  have := finite_hom_over_division D M P.target
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := L) (by exact_mod_cast he)).1 hi⟩

include k in
/-- A bimodule semistable for the division-ring Euler weight of a presilting
complex inverts the differential of every member of its additive closure in
the homotopy category. In particular it belongs to the large perpendicular
category of the basic representative. -/
theorem TwoTerm.invertedOn_summand_of_divisionSemistable (P U : TwoTerm R) (hp : P.IsPresilting)
    (hU : IsInAdd U.homotopyObject P.homotopyObject)
    (hs : DivisionSemistable D P.projectiveClass M) : U.InvertedOn M :=
  invertedOn_of_inThick (inThick_of_isInAdd P U hU) M (P.invertedOn_of_divisionSemistable k D M hp hs)

private theorem no_genericBrick_of_rank (n : ℕ) :
    ∀ (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A], IsEFinite A →
      (simpleIsomorphismClasses A).ncard = n → ¬ ∃ G : ModuleCat.{u} A, IsGenericBrick k G := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rintro A _ _ _ hA hr ⟨G,hG⟩
    let D := Module.End A G
    let : DivisionRing D := hG.divisionRing k
    have : Module.Finite D G := hG.endofinite
    obtain ⟨g,hg,hs⟩ := hG.exists_divisionSemistable k hA
    obtain ⟨P,hP,hc⟩ := hA g
    subst g
    let := IsNoetherianRing.of_finite k A
    have hi := P.invertedOn_of_divisionSemistable k D G hP hs
    obtain ⟨B,_,_,_,hB,hl,hbrick⟩ := hG.exists_smaller_of_inverted k hA hP hg hi
    exact ih _ (hl.trans_eq hr) B hB rfl hbrick

omit [IsNoetherianRing R] in
/-- An E-finite algebra over any field admits no generic brick. -/
theorem no_genericBrick_of_isEFinite (hR : IsEFinite R) :
    ¬ ∃ G : ModuleCat.{u} R, IsGenericBrick k G :=
  no_genericBrick_of_rank k _ R hR rfl

omit [IsNoetherianRing R] in
theorem no_generic_right_brick_of_isEFinite (hR : IsEFinite R) :
    ¬ ∃ G : ModuleCat.{u} Rᵐᵒᵖ, IsGenericBrick k G := by
  let := IsNoetherianRing.of_finite k R
  let := IsArtinianRing.of_finite k R
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  exact no_genericBrick_of_isEFinite k ((isEFinite_iff_opposite k).1 hR)

omit [IsNoetherianRing R] in
/-- Over an E-finite algebra the endomorphism socle excludes generic grains. -/
theorem no_genericGrain_of_isEFinite (hR : IsEFinite R) :
    ¬ ∃ N : ModuleCat.{u} R, IsGenericGrain k N := by
  rintro ⟨N,hN⟩
  exact no_genericBrick_of_isEFinite k hR ⟨_,hN.genericBrick k⟩

omit [IsNoetherianRing R] in
/-- The generic-grain exclusion in the manuscript's right-module convention. -/
theorem no_generic_right_grain_of_isEFinite (hR : IsEFinite R) :
    ¬ ∃ N : ModuleCat.{u} Rᵐᵒᵖ, IsGenericGrain k N := by
  rintro ⟨N,hN⟩
  exact no_generic_right_brick_of_isEFinite k hR ⟨_,hN.genericBrick k⟩

omit [IsNoetherianRing R] in
/-- Every simple Artinian ring-epimorphic target of an E-finite algebra is
finite-dimensional for the induced ground-field action. -/
theorem finite_simpleArtinian_ring_epimorphisms_of_isEFinite (hR : IsEFinite R)
    (B : Type u) [Ring B] [IsSimpleRing B] [IsArtinianRing B] (f : R →+* B)
    (hf : IsRingEpimorphism f) : letI := hf.targetAlgebra k; Module.Finite k B :=
  (no_generic_right_brick_iff_finite_ring_epimorphisms k).1 (no_generic_right_brick_of_isEFinite k hR) B f hf

end EFiniteCharacterizations
