module

public import EFiniteCharacterizations.Subcategories.ExactAbelianApproximations
public import EFiniteCharacterizations.RingEpimorphisms.RingEpimorphism

/-! # Residually finite-dimensional epimorphic targets -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R B : Type u} [Ring R] [Algebra k R] [Ring B] [Algebra k B]

/-- The common annihilator of the finite-dimensional modules is zero. -/
def IsResiduallyFiniteDimensional (B : Type u) [Ring B] [Algebra k B] : Prop :=
  ∀ b : B, (∀ M : ModuleCat.{u} B, Module.Finite k M → ∀ x : M, b • x = 0) → b = 0

theorem IsRingEpimorphism.full_restriction {f : R →+* B} (hf : IsRingEpimorphism f) :
    (ModuleCat.restrictScalars.{u} f).Full where
  map_surjective {M N} p := ⟨ModuleCat.ofHom
    { toAddHom := p.hom.toAddHom
      map_smul' := hf.map_smul (M := M) (N := N) p.hom },rfl⟩

/-- Restriction along an algebra map preserves the underlying ground vector space. -/
def restrictScalarsGroundEquiv (f : R →ₐ[k] B) (M : ModuleCat.{u} B) :
    ((ModuleCat.restrictScalars f.toRingHom).obj M : Type u) ≃ₗ[k] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change f (algebraMap k R c) • (show M from x) = algebraMap k B c • (show M from x)
    rw [f.commutes]

/-- Over an E-finite algebra, a left approximation of the regular module
by restrictions of finite target modules supplies a faithful target module. -/
theorem finite_residuallyFinite_epic_target [Module.Finite k R] [IsNoetherianRing R] [IsArtinianRing R]
    (he : IsEFinite R) (f : R →ₐ[k] B) (hf : IsRingEpimorphism f.toRingHom)
    (det : IsResiduallyFiniteDimensional k B) : Module.Finite k B := by
  let G := ModuleCat.restrictScalars.{u} f.toRingHom

  let := hf.full_restriction
  let : PreservesFiniteLimits G := ⟨fun J _ _ ↦ ⟨fun {K} ↦ inferInstanceAs (PreservesLimit K (ModuleCat.restrictScalars f.toRingHom))⟩⟩
  let : PreservesFiniteColimits G := ⟨fun J _ _ ↦ ⟨fun {K} ↦ inferInstanceAs (PreservesColimit K (ModuleCat.restrictScalars f.toRingHom))⟩⟩
  let W := fun X : FGModuleCat.{u} R ↦ G.essImage X.obj
  let : (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).Additive := ⟨rfl⟩
  have hw : IsExactAbelianClass W := (IsExactAbelianClass.essImage G).inverseImage (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))
  obtain ⟨L,a,hL,ha⟩ := (functoriallyFinite_exactAbelianClass k he hw).1 (FGModuleCat.of R R)
  obtain ⟨M,⟨e⟩⟩ := hL
  let := Module.Finite.trans (R := k) R (L : Type u)
  let e₀ := (e.toLinearEquiv.restrictScalars k).symm.trans (restrictScalarsGroundEquiv k f M)
  let := Module.Finite.equiv e₀
  let act : B →ₐ[k] Module.End k M := Algebra.lsmul k k M
  apply Module.Finite.of_injective act.toLinearMap
  apply (injective_iff_map_eq_zero _).2
  intro b hb
  apply det b
  intro N fin x
  let eqN := restrictScalarsGroundEquiv k f N
  let := Module.Finite.equiv eqN.symm
  let := Module.Finite.of_restrictScalars_finite k R (G.obj N : Type u)
  let X := FGModuleCat.of R (G.obj N : Type u)
  have hx : W X := ⟨N,⟨Iso.refl _⟩⟩
  let u : FGModuleCat.of R R ⟶ X := FGModuleCat.ofHom (LinearMap.toSpanSingleton R _ x)
  obtain ⟨v,hv⟩ := ha X hx u
  let p : G.obj M ⟶ G.obj N := e.hom ≫ v.hom
  let z := e.inv.hom (a.hom.hom 1)
  have hp : p.hom z = x := by
    have h₁ := DFunLike.congr_fun (congrArg (fun t : FGModuleCat.of R R ⟶ X ↦ t.hom.hom) hv) 1
    change v.hom.hom (a.hom.hom 1) = (1 : R) • (show G.obj N from x) at h₁
    exact (by simpa [p,z] using (h₁.trans (one_smul R (show G.obj N from x))))
  have hz : b • (show M from z) = 0 := DFunLike.congr_fun hb z
  exact (congrArg (fun y : N ↦ b • y) hp.symm).trans
    ((hf.map_smul (M := M) (N := N) p.hom b z).symm.trans (by rw [hz]; exact p.hom.map_zero))

end EFiniteCharacterizations
