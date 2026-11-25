module

public import EFiniteCharacterizations.Stability.StableIsotypicQuotients
public import EFiniteCharacterizations.LinearAlgebra.GaloisAveraging

/-! # Splitting semistable quotients after finite Galois extension -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra TensorProduct

universe u
namespace EFiniteCharacterizations.FieldExtension

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R] [Module.Finite k F] [IsGalois k F]
local notation "A" => ExtendedAlgebra k F R

/-- A section after restriction of scalars can be averaged to a section
over the extended algebra, including in characteristic dividing the degree. -/
theorem exists_section_of_restricted_section {X Y : FGModuleCat.{u} A} (p : X ⟶ Y)
    (f : restrictObj k F R Y ⟶ restrictObj k F R X) (hf : f ≫ (restrict k F R).map p = 𝟙 _) :
    ∃ t : Y ⟶ X, t ≫ p = 𝟙 Y := by
  classical
  let := isScalarTower_ground_extension k F R X.obj
  let := isScalarTower_ground_extension k F R Y.obj
  let eX := restrictVectorSpaceEquiv k F R X.obj
  let eY := restrictVectorSpaceEquiv k F R Y.obj
  let f₀ : Y →ₗ[k] X := eX.toLinearMap.comp ((f.hom.hom.restrictScalars k).comp eY.symm.toLinearMap)
  let b := Module.finBasis k F
  let l i := (scalarActionMap k F R X (b.traceDual i)).comp (f.hom.hom.comp (scalarActionMap k F R Y (b i)))
  let v : restrictObj k F R Y →ₗ[R] restrictObj k F R X := ∑ i, l i
  have hv (y : Y) : v y = galoisComponent b f₀ (1 : Gal(F/k)) y :=
    (LinearMap.sum_apply Finset.univ l (show restrictObj k F R Y from y)).trans (by rfl)
  have hc (c : F) (y : Y) : v (show Y from c • y) = c • (show X from v y) := by
    exact (hv _).trans ((galoisComponent_smul b f₀ (1 : Gal(F/k)) c y).trans
      (congrArg (fun z : X ↦ c • z) (hv y).symm))
  let t : Y →ₗ[A] X :=
    { v.toAddHom with
      map_smul' := fun a y ↦ by
        refine TensorProduct.inductionOn a ?_ ?_
        · intro c r
          have he (N : FGModuleCat.{u} A) (x : N) : (c ⊗ₜ[k] r : A) • x =
              c • (show N from r • (show restrictObj k F R N from x)) := by
            change _ = algebraMap F A c • algebraInclusion k F R r • x
            rw [← mul_smul]
            simp [algebraInclusion,Algebra.TensorProduct.tmul_mul_tmul]
          exact (congrArg v (he Y y)).trans ((hc c _).trans
            ((congrArg (fun z : X ↦ c • z) (v.map_smul r y)).trans (he X _).symm))
        · intro a c ha hc'
          exact (congrArg v (add_smul a c y)).trans ((v.map_add _ _).trans
            ((congrArg₂ (· + ·) ha hc').trans (add_smul a c (show X from v y)).symm)) }
  refine ⟨FGModuleCat.ofHom t,?_⟩
  ext y
  have h (x : Y) : p.hom.hom (f₀ x) = x :=
    congrArg (fun a : restrictObj k F R Y ⟶ restrictObj k F R Y ↦ a.hom.hom x) hf
  change p.hom.hom (v y) = y
  rw [hv]
  change p.hom.hom (∑ i, b.traceDual i • f₀ ((b i) • y)) = y
  rw [map_sum]
  calc
    _ = ∑ i, (b.traceDual i * b i) • y := by
      apply Finset.sum_congr rfl
      intro i _
      exact ((p.hom.hom.restrictScalars F).map_smul (b.traceDual i) _).trans
        ((congrArg (fun z : Y ↦ b.traceDual i • z) (h ((b i) • y))).trans (mul_smul ..).symm)
    _ = y := by rw [← Finset.sum_smul,traceDual_mul_sum_one,one_smul]

variable [IsNoetherianRing R] [IsNoetherianRing (ExtendedAlgebra k F R)]

/-- Every semistable quotient of the extension of a stable ground module
splits over the extended algebra. -/
theorem split_semistable_quotient_extend_stable (P : TwoTerm R) {S : FGModuleCat.{u} R}
    (hs : (P.eulerWeight k).IsStable S) {N : FGModuleCat.{u} A}
    (hn : ((extendTwoTerm k F R P).eulerWeight F).IsSemistable N) (p : extendObj k F R S ⟶ N) [Epi p] :
    ∃ t : N ⟶ extendObj k F R S, t ≫ p = 𝟙 N := by
  let e := (restrictExtendBasisEquiv k F R (Module.finBasis k F) S).toFGModuleCatIso
  let d : FGModuleCat.of R (Fin (Module.finrank k F) → S) ⟶ restrictObj k F R N := e.inv ≫ (restrict k F R).map p
  have hd : Epi d := (FGModuleCat.epi_iff_surjective d).2 (((FGModuleCat.epi_iff_surjective p).1 inferInstance).comp
    ((FGModuleCat.isIso_iff_bijective e.inv).1 inferInstance).2)
  obtain ⟨t,ht⟩ := (hs.split_quotient_of_power _ ((isSemistable_restrictObj_iff k F R P N).2 hn) d).2
  exact exists_section_of_restricted_section k F R p (t ≫ e.inv) ((Category.assoc ..).trans ht)

private theorem finite_sum_of_stables_of_split_quotients {D : Type u} [Ring D]
    (L : Type u) [Field L] [Algebra L D] [Module.Finite L D] [IsNoetherianRing D]
    (θ : Weight (FGModuleCat.{u} D)) (X : FGModuleCat.{u} D) (hx : θ.IsSemistable X)
    (split : ∀ (Y : FGModuleCat.{u} D), θ.IsSemistable Y → ∀ (p : X ⟶ Y) [Epi p], ∃ t, t ≫ p = 𝟙 Y) :
    ∃ (n : ℕ) (B : Fin n → FGModuleCat.{u} D), (∀ i, θ.IsStable (B i)) ∧
      Nonempty (X ≅ FGModuleCat.of D ((i : Fin n) → B i)) := by
  classical
  let := IsArtinianRing.of_finite L D
  induction hn : FGModuleCat.moduleLength X using Nat.strong_induction_on generalizing X with
  | h d ih =>
    by_cases hz : IsZero X
    · let B (i : Fin 0) : FGModuleCat.{u} D := i.elim0
      let Z := FGModuleCat.of D ((i : Fin 0) → B i)
      have hZ := (FGModuleCat.isZero_iff_subsingleton Z).2 (inferInstanceAs (Subsingleton ((i : Fin 0) → B i)))
      exact ⟨0,B,fun i ↦ i.elim0,⟨hz.iso hZ⟩⟩
    obtain ⟨S,i,hi,hS⟩ := hx.exists_stable_subobject L hz
    let q := cokernel.π i
    have hQ := hS.isSemistable.cokernel_of_mono hx i
    obtain ⟨s,hs⟩ := split _ hQ q
    let E := ShortComplex.mk i q (cokernel.condition i)
    let sp := ShortComplex.Splitting.ofExactOfSection E (ShortComplex.exact_cokernel i) s hs hi
    have hgt : FGModuleCat.moduleLength (cokernel i) < d := by
      have hE : E.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) hi
        (inferInstanceAs (Epi (cokernel.π i)))
      have he := FGModuleCat.moduleLength_shortExact E hE
      change FGModuleCat.moduleLength X = FGModuleCat.moduleLength S + FGModuleCat.moduleLength (cokernel i) at he
      have hne := mt (FGModuleCat.moduleLength_eq_zero_iff_isZero S).1 hS.1
      omega
    obtain ⟨n,B,hB,⟨e⟩⟩ := ih _ hgt _ hQ (fun Y hy p hp ↦ by
      obtain ⟨a,ha⟩ := split Y hy (q ≫ p)
      exact ⟨a ≫ q,(Category.assoc ..).trans ha⟩) rfl
    let C : Fin (n+1) → FGModuleCat.{u} D := Fin.cons S B
    have hC (i : Fin (n+1)) : θ.IsStable (C i) := Fin.cases hS hB i
    let M := FGModuleCat.of D ((i : Fin n) → B i)
    let F := forget₂ (FGModuleCat.{u} D) (ModuleCat.{u} D)
    let e' : S ⊞ M ≅ FGModuleCat.of D (S × ((i : Fin n) → B i)) :=
      F.preimageIso ((FGModuleCat.forgetBiprodIso S M).trans (ModuleCat.biprodIsoProd S.obj M.obj))
    let c := Fin.consLinearEquiv D (fun i : Fin (n+1) ↦ (C i : Type u))
    exact ⟨n+1,C,hC,⟨sp.isoBinaryBiproduct ≪≫ biprod.mapIso (Iso.refl S) e ≪≫ e' ≪≫ c.toFGModuleCatIso⟩⟩

/-- Over any finite Galois extension a stable ground module becomes a
finite direct sum of stable extension modules at the extended weight. -/
theorem extend_stable_is_sum_of_stables (P : TwoTerm R) {S : FGModuleCat.{u} R}
    (hs : (P.eulerWeight k).IsStable S) :
    ∃ (n : ℕ) (B : Fin n → FGModuleCat.{u} A),
      (∀ i, ((extendTwoTerm k F R P).eulerWeight F).IsStable (B i)) ∧
      Nonempty (extendObj k F R S ≅ FGModuleCat.of A ((i : Fin n) → B i)) :=
  finite_sum_of_stables_of_split_quotients F _ _ (isSemistable_extendObj k F R P S hs.isSemistable)
    (fun _ hn p _ ↦ split_semistable_quotient_extend_stable k F R P hs hn p)

end EFiniteCharacterizations.FieldExtension
