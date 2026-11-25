module

public import EFiniteCharacterizations.LargeModules.GenericKernelEndofinite
public import EFiniteCharacterizations.Presentations.NakayamaPairing
public import EFiniteCharacterizations.Presentations.RepresentProjectiveClass
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # The numerical torsion pair of a generic copresentation -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped TensorProduct ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations
noncomputable section

variable {k R D : Type u} [Field k] [Ring R] [Algebra k R] [DivisionRing D] [Algebra k D]
variable {I J : Type u} [AddCommGroup I] [Module k I] [Module R I] [IsScalarTower k R I]
  [AddCommGroup J] [Module k J] [Module R J] [IsScalarTower k R J]

private def homCoordinates (X : FGModuleCat.{u} R) :
    (Dᵐᵒᵖ ⊗[k] (X →ₗ[R] I)) ≃+ (X.obj ⟶ ModuleCat.of R (I ⊗[k] D)) := by
  let e := (TensorProduct.congr (MulOpposite.opLinearEquiv k (M := D)).symm
    (LinearEquiv.refl k (X →ₗ[R] I))).trans (TensorProduct.comm k D _)
  exact e.toAddEquiv.trans (tensorHomAddEquiv.trans (ModuleCat.homAddEquiv (M := X.obj) (N := ModuleCat.of R (I ⊗[k] D))).symm)

private theorem homCoordinates_apply (X : FGModuleCat.{u} R) (d : Dᵐᵒᵖ) (s : X →ₗ[R] I) (x : X) :
    ((homCoordinates (k := k) X) (d ⊗ₜ[k] s)).hom x = s x ⊗ₜ[k] d.unop :=
  tensorHomAddEquiv_tmul (k := k) s d.unop x

private def composeGround (X : FGModuleCat.{u} R) (p : I →ₗ[R] J) :
    (X →ₗ[R] I) →ₗ[k] (X →ₗ[R] J) where
  toFun s := p.comp s
  map_add' _ _ := by ext; simp
  map_smul' c s := by ext x; exact (p.restrictScalars k).map_smul c (s x)

variable {n : Type u} [Fintype n]

private def postOnCoordinates (X : FGModuleCat.{u} R) (h : Module.Basis n k (I →ₗ[R] J))
    (g : FreeAlgebra k n →ₐ[k] D) :
    (Dᵐᵒᵖ ⊗[k] (X →ₗ[R] I)) →ₗ[Dᵐᵒᵖ] (Dᵐᵒᵖ ⊗[k] (X →ₗ[R] J)) :=
  ∑ j, AlgebraTensorModule.map (LinearMap.toSpanSingleton Dᵐᵒᵖ Dᵐᵒᵖ (.op (g (FreeAlgebra.ι k j))))
    (composeGround X (h j))

private theorem postOnCoordinates_eq (X : FGModuleCat.{u} R) (h : Module.Basis n k (I →ₗ[R] J))
    (g : FreeAlgebra k n →ₐ[k] D) (z : Dᵐᵒᵖ ⊗[k] (X →ₗ[R] I)) :
    homCoordinates X (postOnCoordinates X h g z) = homCoordinates X z ≫ genericCopresentation h g := by
  induction z with
  | tmul d s =>
    ext x
    simp [postOnCoordinates,composeGround,genericCopresentation,
      ModuleCat.hom_sum,LinearMap.sum_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [homCoordinates_apply (k := k) X d s x, homCoordinates_apply (k := k) X _ ((h j).comp s) x]
    rfl
  | add a b ha hb => simp [ha,hb,Preadditive.add_comp]

/-- The ground-field difference of Hom dimensions determines the numerical
torsion pair, with no dimension hypotheses over the localization left to check. -/
theorem genericCopresentation_numerical_pair_of_rigid [IsNoetherianRing R] [IsArtinianRing R]
    [Module.Finite k R] [Module.Finite R I] [Module.Finite R J]
    (injI : Module.Injective R I) (injJ : Module.Injective R J)
    (h : Module.Basis n k (I →ₗ[R] J)) (g : FreeAlgebra k n →ₐ[k] D)
    (rigid : ∀ f, ∃ a c, f = a ≫ genericCopresentation h g + genericCopresentation h g ≫ c)
    (θ : Weight (FGModuleCat.{u} R))
    (he : ∀ X : FGModuleCat.{u} R, θ.eval X = (Module.finrank k (X →ₗ[R] J) : ℤ) - Module.finrank k (X →ₗ[R] I)) :
    perpendicularToModule (kernel (genericCopresentation h g)) = θ.weakTorsionClass ∧
      cogeneratedByModule (kernel (genericCopresentation h g)) = (fun X ↦ ∀ {U : FGModuleCat.{u} R}
        (i : U ⟶ X) [Mono i], ¬ IsZero U → θ.eval U < 0) := by
  let := injective_tensor_vectorSpace (k := k) (D := D) injI
  let := injective_tensor_vectorSpace (k := k) (D := D) injJ
  let := Module.injective_object_of_injective_module R (I ⊗[k] D)
  let := Module.injective_object_of_injective_module R (J ⊗[k] D)
  let eI := fun X : FGModuleCat R ↦ (homCoordinates (k := k) (D := D) (I := I) X).symm
  let eJ := fun X : FGModuleCat R ↦ (homCoordinates (k := k) (D := D) (I := J) X).symm
  let instI := fun X ↦ (eI X).module Dᵐᵒᵖ
  let instJ := fun X ↦ (eJ X).module Dᵐᵒᵖ
  let lI := fun X ↦ (eI X).linearEquiv Dᵐᵒᵖ
  let lJ := fun X ↦ (eJ X).linearEquiv Dᵐᵒᵖ
  let := Module.Finite.trans (R := k) R I
  let := Module.Finite.trans (R := k) R J
  have finI (X : FGModuleCat R) : Module.Finite Dᵐᵒᵖ (X.obj ⟶ ModuleCat.of R (I ⊗[k] D)) :=
    by
      let := Module.Finite.trans (R := k) R (X : Type u)
      exact Module.Finite.equiv (lI X).symm
  have finJ (X : FGModuleCat R) : Module.Finite Dᵐᵒᵖ (X.obj ⟶ ModuleCat.of R (J ⊗[k] D)) :=
    by
      let := Module.Finite.trans (R := k) R (X : Type u)
      exact Module.Finite.equiv (lJ X).symm
  apply rigidKernel_pair_of_euler_formula _ rigid θ Dᵐᵒᵖ
    (fun X ↦ (lJ X).symm.toLinearMap.comp ((postOnCoordinates X h g).comp (lI X).toLinearMap))
  · intro X f
    exact (postOnCoordinates_eq X h g (eI X f)).trans
      (by rw [show homCoordinates X (eI X f) = f from (eI X).symm_apply_apply f])
  · intro X
    rw [(lJ X).finrank_eq,(lI X).finrank_eq,Module.finrank_baseChange,Module.finrank_baseChange,he]

theorem genericCopresentation_numerical_pair [IsNoetherianRing R] [IsArtinianRing R]
    [Module.Finite k R] [Module.Finite R I] [Module.Finite R J]
    (injI : Module.Injective R I) (injJ : Module.Injective R J)
    (h : Module.Basis n k (I →ₗ[R] J)) (g : FreeAlgebra k n →ₐ[k] D)
    {ι : Type*} {φ : ι → TwoTerm (FreeAlgebra k n)} (loc : IsUniversalLocalization φ g.toRingHom)
    (θ : Weight (FGModuleCat.{u} R))
    (he : ∀ X : FGModuleCat.{u} R, θ.eval X = (Module.finrank k (X →ₗ[R] J) : ℤ) - Module.finrank k (X →ₗ[R] I)) :
    perpendicularToModule (kernel (genericCopresentation h g)) = θ.weakTorsionClass ∧
      cogeneratedByModule (kernel (genericCopresentation h g)) = (fun X ↦ ∀ {U : FGModuleCat.{u} R}
        (i : U ⟶ X) [Mono i], ¬ IsZero U → θ.eval U < 0) :=
  genericCopresentation_numerical_pair_of_rigid injI injJ h g (genericCopresentation_rigid h g loc) θ he

/-- Coefficients solving all simultaneous commutator equations realize
every integral weight by an endofinite kernel. -/
theorem exists_endofinite_kernel_of_commutators [IsNoetherianRing R] [IsArtinianRing R]
    [Module.Finite k R]
    (coefficients : ∀ (V : Type u) [Fintype V], ∃ (K : Type u) (_ : DivisionRing K) (_ : Algebra k K)
      (a : V → K), HasSurjectiveCommutators k a) (γ : ProjectiveClass R) :
    ∃ N : ModuleCat.{u} R, IsEndofinite N ∧ SplitsOnCogeneratedModules k N ∧
      perpendicularToModule N = (projectiveClassWeight k γ).weakTorsionClass ∧
      cogeneratedByModule N = (fun X ↦ ∀ {U : FGModuleCat.{u} R} (i : U ⟶ X) [Mono i],
        ¬ IsZero U → (projectiveClassWeight k γ).eval U < 0) := by
  classical
  obtain ⟨P,rfl⟩ := ProjectiveClass.exists_twoTerm γ
  rw [P.projectiveClassWeight_eq_eulerWeight k]
  let I := NakayamaModule k R (P.source : Type u)
  let J := NakayamaModule k R (P.target : Type u)
  let := P.projective_source
  let := P.projective_target
  let finI : Module.Finite R I := (nakayamaObject k P.source).property
  let finJ : Module.Finite R J := (nakayamaObject k P.target).property
  let := Module.Finite.trans (R := k) R I
  let := Module.Finite.trans (R := k) R J
  let h := Module.Free.chooseBasis k (I →ₗ[R] J)
  obtain ⟨K,_,_,a,ha⟩ := coefficients (Module.Free.ChooseBasisIndex k (I →ₗ[R] J))
  let g := FreeAlgebra.lift k a
  have rigid := genericCopresentation_rigid_of_commutators h g (by simpa [g] using ha)
  let injI : Module.Injective R I := inferInstanceAs (Module.Injective R (NakayamaModule k R _))
  let injJ : Module.Injective R J := inferInstanceAs (Module.Injective R (NakayamaModule k R _))
  let := injective_tensor_vectorSpace (k := k) (D := K) injI
  let := injective_tensor_vectorSpace (k := k) (D := K) injJ
  let := Module.injective_object_of_injective_module R (I ⊗[k] K)
  let := Module.injective_object_of_injective_module R (J ⊗[k] K)
  refine ⟨_,genericCopresentation_kernel_endofinite h g,splitsOnCogeneratedModules_kernel_of_rigid k _ rigid,
    genericCopresentation_numerical_pair_of_rigid injI injJ h g rigid _ ?_⟩
  intro X
  have dim (Q : FGModuleCat.{u} R) [Module.Projective R Q] :
      Module.finrank k (X →ₗ[R] NakayamaModule k R (Q : Type u)) = homFinrank k Q X := by
    let := finiteModuleHom_isFinite k Q X
    rw [homFinrank_eq_finrank,(nakayamaTargetHomEquiv k Q X).finrank_eq,
      ← (nakayamaPairing k Q X).finrank_eq,Subspace.dual_finrank_eq]
  rw [P.eulerWeight_eval k,← dim P.target,← dim P.source]


/-- A division-ring universal localization of each finite free algebra suffices
to realize every integral weight by an endofinite kernel. -/
theorem exists_endofinite_kernel_of_free_localizations [IsNoetherianRing R] [IsArtinianRing R]
    [Module.Finite k R]
    (freeLoc : ∀ (V : Type u) [Fintype V], ∃ (K : Type u) (_ : DivisionRing K) (_ : Algebra k K)
      (g : FreeAlgebra k V →ₐ[k] K) (ι : Type u) (φ : ι → TwoTerm (FreeAlgebra k V)),
        IsUniversalLocalization φ g.toRingHom) (γ : ProjectiveClass R) :
    ∃ N : ModuleCat.{u} R, IsEndofinite N ∧ SplitsOnCogeneratedModules k N ∧
      perpendicularToModule N = (projectiveClassWeight k γ).weakTorsionClass ∧
      cogeneratedByModule N = (fun X ↦ ∀ {U : FGModuleCat.{u} R} (i : U ⟶ X) [Mono i],
        ¬ IsZero U → (projectiveClassWeight k γ).eval U < 0) := by
  apply exists_endofinite_kernel_of_commutators _ γ
  intro V _
  obtain ⟨K,_,_,g,ι,φ,loc⟩ := freeLoc V
  exact ⟨K,inferInstance,inferInstance,_,simultaneous_commutators_of_division_localization g loc⟩


end
end EFiniteCharacterizations
