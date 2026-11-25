module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.Congruence.Hom
public import Mathlib.RingTheory.Artinian.Algebra
public import Mathlib.RingTheory.Length
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.RingTheory.Noetherian.Basic

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

/-! # Characterizations of E-finite algebras

All modules at the endpoints are right modules, realized as left modules over
the opposite algebra. The integral lattice is the split Grothendieck group of
finite projectives. Pairs of projectives represent integral weights. -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra ZeroObject
universe u
namespace EFiniteCharacterizations.Statement

variable (R : Type u) [Ring R]

abbrev Mod := FGModuleCat.{u} R
abbrev Proj := {P : Mod R // Module.Projective R P}

/-- Isomorphism and direct sum relations in the projective lattice. -/
def splitRelations : AddSubgroup (FreeAbelianGroup (Proj R)) :=
  AddSubgroup.closure
    ({x | ∃ P Q : Proj R, Nonempty (P.val ≅ Q.val) ∧ x = FreeAbelianGroup.of P - FreeAbelianGroup.of Q} ∪
     {x | ∃ P Q T : Proj R, Nonempty (T.val.obj ≅ P.val.obj ⊞ Q.val.obj) ∧
       x = FreeAbelianGroup.of T - (FreeAbelianGroup.of P + FreeAbelianGroup.of Q)})

abbrev Lattice := FreeAbelianGroup (Proj R) ⧸ splitRelations R

variable {R}
def projClass (P : Proj R) : Lattice R := QuotientAddGroup.mk (FreeAbelianGroup.of P)

/-- Every map to the shift of the complex is null-homotopic. -/
def Presilting {P Q : Proj R} (d : P.val ⟶ Q.val) : Prop :=
  Function.Surjective (fun t : (P.val ⟶ P.val) × (Q.val ⟶ Q.val) ↦ t.1 ≫ d - d ≫ t.2)

variable (R)
def EFinite : Prop := ∀ g : Lattice R, ∃ (P Q : Proj R) (d : P.val ⟶ Q.val),
  Presilting d ∧ projClass Q - projClass P = g

variable [IsNoetherianRing R]

/-- Short exact sequence relations for finite modules. -/
def exactRelations : AddSubgroup (FreeAbelianGroup (Mod R)) :=
  AddSubgroup.closure {r | ∃ S : ShortComplex (Mod R), S.ShortExact ∧
    r = FreeAbelianGroup.of S.X₂ - (FreeAbelianGroup.of S.X₁ + FreeAbelianGroup.of S.X₃)}

abbrev K₀ := FreeAbelianGroup (Mod R) ⧸ exactRelations R

variable {R}
def cl (M : Mod R) : K₀ R := QuotientAddGroup.mk (FreeAbelianGroup.of M)
def Brick (M : Mod R) : Prop := ¬ IsZero M ∧ ∀ f : M ⟶ M, f ≠ 0 → IsIso f
def brickClasses : Set (Skeleton (Mod R)) := {s | Brick ((fromSkeleton _).obj s)}
def simpleClasses (R : Type u) [Ring R] : Set (Skeleton (Mod R)) :=
  {s | ∃ M : Mod R, toSkeleton M = s ∧ Simple M}
def Semibrick (s : Set (Skeleton (Mod R))) : Prop := s ⊆ brickClasses ∧
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ f : (fromSkeleton _).obj x ⟶ (fromSkeleton _).obj y, f = 0

def FunctoriallyFinite (T : ObjectProperty (Mod R)) : Prop :=
  (∀ X, ∃ (L : Mod R) (i : X ⟶ L), T L ∧ ∀ Y, T Y → ∀ f : X ⟶ Y, ∃ g, i ≫ g = f) ∧
  (∀ X, ∃ (L : Mod R) (p : L ⟶ X), T L ∧ ∀ Y, T Y → ∀ f : Y ⟶ X, ∃ g, g ≫ p = f)

def TorsionPair (T F : ObjectProperty (Mod R)) : Prop :=
  (∀ {X Y} (f : X ⟶ Y), T X → F Y → f = 0) ∧
  ∀ X, ∃ (L Q : Mod R) (i : L ⟶ X) (p : X ⟶ Q) (w : i ≫ p = 0), T L ∧ F Q ∧
    (ShortComplex.mk i p w).ShortExact

def leftPerp (F : ObjectProperty (Mod R)) : ObjectProperty (Mod R) :=
  fun X ↦ ∀ Y, F Y → ∀ f : X ⟶ Y, f = 0
def rightPerp (B : Mod R) : ObjectProperty (Mod R) := fun Y ↦ ∀ f : B ⟶ Y, f = 0

structure Wide (W : ObjectProperty (Mod R)) : Prop where
  zero_mem (X : Mod R) : IsZero X → W X
  iso_mem {X Y} : (X ≅ Y) → W X → W Y
  kernel_mem {X Y} (f : X ⟶ Y) : W X → W Y → W (kernel f)
  cokernel_mem {X Y} (f : X ⟶ Y) : W X → W Y → W (cokernel f)
  extension_mem (S : ShortComplex (Mod R)) : S.ShortExact → W S.X₁ → W S.X₃ → W S.X₂

/-- Finite filtrations with factors isomorphic to a prescribed brick. -/
inductive Filt (B : Mod R) : Mod R → Prop where
  | zero {X} (h : IsZero X) : Filt B X
  | extend (S : ShortComplex (Mod R)) (h : S.ShortExact) (e : S.X₁ ≅ B) (q : Filt B S.X₃) :
      Filt B S.X₂

abbrev FiniteTorsion (R : Type u) [Ring R] [IsNoetherianRing R] :=
  {T : ObjectProperty (Mod R) // (∃ F, T = leftPerp F) ∧ FunctoriallyFinite T}

/-- The defining relations in the exact Grothendieck monoid of T. -/
inductive ExactMonoidRel (T : ObjectProperty (Mod R)) : Multiset {X // T X} → Multiset {X // T X} → Prop
  | zero (X) (h : IsZero X.val) : ExactMonoidRel T {X} 0
  | iso (X Y) (e : X.val ≅ Y.val) : ExactMonoidRel T {X} {Y}
  | exact (S : ShortComplex (Mod R)) (h : S.ShortExact) (a : T S.X₁) (b : T S.X₂) (c : T S.X₃) :
      ExactMonoidRel T {⟨S.X₂,b⟩} ({⟨S.X₁,a⟩} + {⟨S.X₃,c⟩})

def MonoidDimension (R : Type u) [Ring R] [IsNoetherianRing R] : Prop :=
  ∀ (T : ObjectProperty (Mod R)), T.IsClosedUnderQuotients → T.IsClosedUnderExtensions → T 0 →
    ∀ X Y (hx : T X) (hy : T Y), cl X = cl Y →
      (addConGen (ExactMonoidRel T)) {⟨X,hx⟩} {⟨Y,hy⟩}

variable (k : Type u) [Field k] [Algebra k R]

noncomputable def endolength (M : Mod R) : ℕ :=
  Module.finrank k (M.obj : Type u) / Module.finrank k (M.obj ⟶ M.obj)

/-- Evaluation of the integral weight [Q] − [P] on a module. -/
noncomputable def weight (P Q : Proj R) (M : Mod R) : ℤ :=
  (Module.finrank k (Q.val.obj ⟶ M.obj) : ℤ) - Module.finrank k (P.val.obj ⟶ M.obj)

def Stable (P Q : Proj R) (M : Mod R) : Prop :=
  ¬ IsZero M ∧ weight k P Q M = 0 ∧ ∀ {U : Mod R} (i : U ⟶ M) [Mono i],
    ¬ IsZero U → ¬ IsIso i → weight k P Q U < 0

def GenericBrick (M : ModuleCat.{u} R) : Prop :=
  ¬ Module.Finite k M ∧ (∀ f : Module.End R M, f ≠ 0 → Function.Bijective f) ∧
    Module.Finite (Module.End R M) M

def GenericGrain (M : ModuleCat.{u} R) : Prop :=
  ¬ Module.Finite k M ∧ Indecomposable M ∧ IsFiniteLength (Module.End R M) M ∧
    ∀ S : ShortComplex (ModuleCat.{u} R), S.ShortExact → Nonempty (S.X₁ ≅ M) → Module.Finite k S.X₃ →
      (∃ (n : ℕ) (f : S.X₃ →ₗ[R] (Fin n → M)), Function.Injective f) → ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃

/-- Isomorphism classes of modules satisfying a predicate. -/
def classes (T : ObjectProperty (Mod R)) : Set (Skeleton (Mod R)) := {s | ∃ M, toSkeleton M = s ∧ T M}

variable (R)
def BrickFinite : Prop := (brickClasses (R := R)).Finite

local instance : HasFiniteBiproducts (Mod R) := HasFiniteBiproducts.of_hasFiniteCoproducts

def TauTiltingFinite : Prop :=
  let n := (simpleClasses R).ncard
  {s : Skeleton (Mod R) | ∃ M : Mod R,
    (∃ (P Q : Proj R) (d : P.val ⟶ Q.val), Presilting d ∧ Nonempty (cokernel d ≅ M)) ∧
    (∃ X : Fin n → Mod R, (∀ i, Indecomposable (X i)) ∧ Function.Injective (toSkeleton ∘ X) ∧
      Nonempty ((⨁ X) ≅ M)) ∧ toSkeleton M = s}.Finite

def RankTwo : Prop :=
  ∀ (k R : Type u) [Field k] [Ring R] [Algebra k R] [Module.Finite k R],
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    (simpleClasses Rᵐᵒᵖ).ncard ≤ 2 →
      (EFinite Rᵐᵒᵖ ↔ TauTiltingFinite Rᵐᵒᵖ) ∧ (EFinite Rᵐᵒᵖ ↔ BrickFinite Rᵐᵒᵖ)

/-- A differential between two finite projective modules. -/
structure Differential where
  source : Proj R
  target : Proj R
  d : source.val ⟶ target.val

variable {R}
def Differential.inverts (D : Differential R) {B : Type u} [Ring B] (f : R →+* B) : Prop :=
  letI := Module.compHom B f
  Function.Bijective (fun g : D.target.val.obj ⟶ ModuleCat.of R B ↦ D.d.hom ≫ g)

def Localization (S : Set (Differential R)) {B : Type u} [Ring B] (f : R →+* B) : Prop :=
  (∀ D ∈ S, D.inverts f) ∧ ∀ (C : Type u) [Ring C] (g : R →+* C),
    (∀ D ∈ S, D.inverts g) → ∃! q : B →+* C, q.comp f = g

def RingEpic {B : Type u} [Ring B] (f : R →+* B) : Prop :=
  ∀ (C : Type u) [Ring C] (g h : B →+* C), g.comp f = h.comp f → g = h

open CategoryTheory.Pretriangulated

noncomputable abbrev Differential.realize (D : Differential R) :=
  (HomotopyCategory.quotient _ _).obj
    (HomologicalComplex.double D.d (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl))

def zeroDifferential (R : Type u) [Ring R] : Differential R :=
  let Z : Proj R := ⟨FGModuleCat.of R PUnit, inferInstance⟩
  ⟨Z,Z,𝟙 Z.val⟩

def Thick (H : Differential R → Prop) : Prop :=
  H (zeroDifferential R) ∧
  (∀ (A B C : Differential R) (f : A.realize ⟶ B.realize) (g : B.realize ⟶ C.realize)
    (h : C.realize ⟶ A.realize⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang _ →
    (H A → (H B ↔ H C)) ∧ (H C → (H B ↔ H A))) ∧
  ∀ A B : Differential R, Retract A.realize B.realize → H B → H A

variable (R)
def ThickGeneration : Prop :=
  ∀ H : Differential R → Prop, Thick H → ∃ U : Differential R,
    Presilting U.d ∧ ∀ X, H X ↔ (ObjectProperty.singleton U.realize).triangEnvelope X.realize

def BrickLabels : Prop :=
  ∀ B : Mod R, Brick B → ∃ T U : FiniteTorsion R, T ⋖ U ∧
    ∀ X, Filt B X ↔ U.val X ∧ ∀ Y, T.val Y → rightPerp Y X

def PolynomialGrowth : Prop :=
  ∃ a n : ℕ, ∀ m : ℕ,
    let C := classes (fun X : Mod R ↦ Brick X ∧ (Module.length R X).toNat ≤ m)
    C.Finite ∧ C.ncard ≤ a * (m + 1) ^ n

def LocalizationFinite : Prop :=
  ∀ (S : Set (Differential Rᵐᵒᵖ)) (B : Type u) [Ring B] [Algebra k B] (f : R →ₐ[k] B),
    Localization S (AlgHom.op f).toRingHom → Module.Finite k B

def SimpleEpicFinite : Prop :=
  ∀ (B : Type u) [Ring B] [IsSimpleRing B] [IsArtinianRing B] (f : R →+* B),
    RingEpic f → letI := Module.compHom B (f.comp (algebraMap k R)); Module.Finite k B

/-- The seventeen conditions of Theorem A(I), in manuscript order. -/
def ArbitraryField : Prop :=
  ∀ (k R : Type u) [Field k] [Ring R] [Algebra k R] [Module.Finite k R],
    let A := Rᵐᵒᵖ
    letI := IsNoetherianRing.of_finite k A
    let E := EFinite A
    (E ↔ ∀ X Y : Mod A, cl X = cl Y → cl X ≠ 0 → ∃ f : X ⟶ Y, f ≠ 0) ∧
    (E ↔ MonoidDimension A) ∧
    (E ↔ ∀ M : Mod A, FunctoriallyFinite (leftPerp (rightPerp M))) ∧
    (E ↔ ∀ T F : ObjectProperty (Mod A), TorsionPair T F → ∀ X Y,
      T X → F Y → ¬ IsZero X → ¬ IsZero Y → cl X ≠ cl Y) ∧
    (E ↔ ∀ W : ObjectProperty (Mod A), Wide W → FunctoriallyFinite W) ∧
    (E ↔ ∀ B : Mod A, Brick B → FunctoriallyFinite (Filt B)) ∧
    (E ↔ BrickLabels A) ∧
    (E ↔ ∀ s : Set (Skeleton (Mod A)), Semibrick s → s.Finite →
      s.ncard = (simpleClasses A).ncard → s = simpleClasses A) ∧
    (E ↔ ∀ s : Set (Skeleton (Mod A)), Semibrick s → s.Finite) ∧
    (E ↔ ∀ r : ℕ, 0 < r → (classes (fun X : Mod A ↦ endolength k X = r ∧ Brick X)).Finite) ∧
    (E ↔ ∀ (P Q : Proj A) (r : ℕ), 0 < r →
      (classes (fun X : Mod A ↦ endolength k X = r ∧ Stable k P Q X)).Finite) ∧
    (E ↔ PolynomialGrowth A) ∧
    (E ↔ ¬ ∃ M : ModuleCat.{u} A, GenericBrick k M) ∧
    (E ↔ ¬ ∃ M : ModuleCat.{u} A, GenericGrain k M) ∧
    (E ↔ ThickGeneration A) ∧ (E ↔ LocalizationFinite (k := k) R) ∧ (E ↔ SimpleEpicFinite (k := k) R)

/-- Composition vectors are indexed by their classes in the exact Grothendieck group. -/
def InfiniteField : Prop :=
  ∀ (k R : Type u) [Field k] [Infinite k] [Ring R] [Algebra k R] [Module.Finite k R],
    let A := Rᵐᵒᵖ
    letI := IsNoetherianRing.of_finite k A
    (EFinite A ↔ ∀ c : K₀ A, (classes (fun X : Mod A ↦ cl X = c ∧ Brick X)).Finite) ∧
    (EFinite A ↔ ∀ (P Q : Proj A) (c : K₀ A),
      (classes (fun X : Mod A ↦ cl X = c ∧ Stable k P Q X)).Finite)

end EFiniteCharacterizations.Statement

namespace EFiniteCharacterizations.Statement

section
open MvPolynomial TopologicalSpace

variable {k σ X : Type*} [Field k]

/-- The Zariski topology on a parameter set given by its affine coordinates. -/
@[instance_reducible] noncomputable def coordinateZariski (c : X → σ → k) : TopologicalSpace X :=
  TopologicalSpace.induced (fun x ↦ pointToPoint (k := k) (c x)) inferInstance
end

section
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {ι m n : Type*} [Fintype ι] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Matrices of the action of the chosen algebra basis on a based module. -/
noncomputable def actionMatrices (b : Module.Basis ι k R) {M : FGModuleCat.{u} R}
    (v : Module.Basis m k (M.obj : Type u)) (j : ι) : Matrix m m k :=
  LinearMap.toMatrix v v (Algebra.lsmul k k (M.obj : Type u) (b j))
end

section
variable {k R I : Type u} [Field k] [Ring R] [Algebra k R] [DecidableEq I]

/-- The prescribed space at each vertex, with its fixed coordinates. -/
abbrev VertexSpace (k : Type u) (d : I → ℕ) := (i : I) → Fin (d i) → k

variable (d : I → ℕ)

noncomputable def vertexProjection (i : I) : Module.End k (VertexSpace k d) :=
  (LinearMap.single k (fun i ↦ Fin (d i) → k) i).comp (LinearMap.proj i)

variable (e : I → R)

/-- Algebra actions on the fixed vertex spaces taking each vertex idempotent
to the corresponding coordinate projection. -/
def VertexRepresentation := {ρ : R →ₐ[k] Module.End k (VertexSpace k d) //
  ∀ i, ρ (e i) = vertexProjection d i}

namespace VertexRepresentation

variable {d e}

abbrev BaseChange (k : Type u) [Field k] (d : I → ℕ) :=
  ∀ i, (Fin (d i) → k) ≃ₗ[k] (Fin (d i) → k)
/-- Conjugation of the algebra action by an invertible change of basis at each vertex. -/
noncomputable def changeBasis (G : BaseChange k d) (ρ : VertexRepresentation (k := k) d e) :
    VertexRepresentation (k := k) d e := by
  let F := LinearEquiv.piCongrRight G
  refine ⟨(F.conjAlgEquiv k).toAlgHom.comp ρ.val,fun i ↦ ?_⟩
  change F.conjAlgEquiv k (ρ.val (e i)) = _
  rw [ρ.property]
  apply LinearMap.ext
  intro z
  funext j
  change G j (Pi.single (M := fun t ↦ Fin (d t) → k) i (F.symm z i) j) =
    Pi.single (M := fun t ↦ Fin (d t) → k) i (z i) j
  by_cases hj : j = i
  · subst j
    simp [F,LinearEquiv.piCongrRight_symm]
  · simp [Pi.single_eq_of_ne hj]

noncomputable instance : MulAction (BaseChange k d) (VertexRepresentation (k := k) d e) where
  smul := changeBasis
  one_smul ρ := by
    apply Subtype.ext
    apply AlgHom.ext
    intro r
    rfl
  mul_smul G H ρ := by
    apply Subtype.ext
    apply AlgHom.ext
    intro r
    rfl

variable [Fintype I]
/-- The finite module defined by evaluation of an algebra action. -/
noncomputable def moduleObj (ρ : VertexRepresentation (k := k) d e) : FGModuleCat.{u} R := by
  let _ : Module R (VertexSpace k d) := Module.compHom _ ρ.val.toRingHom
  have : IsScalarTower k R (VertexSpace k d) := IsScalarTower.of_algebraMap_smul fun c z ↦
    congrArg (fun f : Module.End k (VertexSpace k d) ↦ f z) (ρ.val.commutes c)
  have : Module.Finite R (VertexSpace k d) := Module.Finite.of_restrictScalars_finite k _ _
  exact FGModuleCat.of R (VertexSpace k d)

/-- Coordinates of the underlying module in the prescribed vertex spaces. -/
noncomputable def coordinates (ρ : VertexRepresentation (k := k) d e) :
    (ρ.moduleObj.obj : Type u) ≃ₗ[k] VertexSpace k d where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c z := congrArg (fun f : Module.End k (VertexSpace k d) ↦ f z) (ρ.val.commutes c)
/-- The total basis is the union of the standard bases at the vertices. -/
noncomputable def vertexBasis (ρ : VertexRepresentation (k := k) d e) :
    Module.Basis (Σ i, Fin (d i)) k (ρ.moduleObj.obj : Type u) :=
  (Pi.basisFun k _).map ((LinearEquiv.piCurry k (fun i (_ : Fin (d i)) ↦ k)).trans ρ.coordinates.symm)

variable {J : Type u} [Fintype J] (b : Module.Basis J k R)

/-- Affine coordinates are the matrix coefficients of the basis elements of the algebra. -/
noncomputable def affineCoordinates (ρ : VertexRepresentation (k := k) d e) :
    J × (Σ i, Fin (d i)) × (Σ i, Fin (d i)) → k := fun (j,a,l) ↦
  actionMatrices b ρ.vertexBasis j a l
/-- The point-set Zariski topology of the fixed-vertex representation variety. -/
@[instance_reducible] noncomputable def zariski :
    TopologicalSpace (VertexRepresentation (k := k) d e) := coordinateZariski (affineCoordinates b)

/-- The vertex summand of a module is the image of the vertex idempotent. -/
abbrev vertexPart (e : I → R) (M : FGModuleCat.{u} R) (i : I) :=
  LinearMap.range (Algebra.lsmul k k (M.obj : Type u) (e i))

end VertexRepresentation
end

namespace VertexRepresentation
section
open scoped DirectSum
variable {k R I J : Type u} [Field k] [Ring R] [Algebra k R]
    [Fintype I] [DecidableEq I] [Fintype J]
    (b : Module.Basis J k R) (d : I → ℕ) (e : I → R)

/-- The character specified by integral exponents on the vertex determinants. -/
noncomputable def vertexCharacter (w : I → ℤ) : BaseChange k d →* kˣ where
  toFun G := ∏ i, (LinearEquiv.det (G i)) ^ w i
  map_one' := by simp
  map_mul' G H := by simp [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

/-- Polynomial functions in the action matrices, restricted to the variety. -/
noncomputable def coordinateAlgebra : Subalgebra k (VertexRepresentation (k := k) d e → k) :=
  (MvPolynomial.aeval (fun j ρ ↦ affineCoordinates b ρ j)).range

/-- The degree-m part consists of regular functions on which the inverse
pullback action has character χ to the power m. -/
def kingSemiInvariants (w : I → ℤ) (m : ℕ) : Submodule k (coordinateAlgebra b d e) where
  carrier := {f | ∀ (G : BaseChange k d) x, f.val (G⁻¹ • x) =
    ((vertexCharacter d w G : kˣ) : k) ^ m * f.val x}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg G x
    change f.val _ + g.val _ = _ * (f.val x + g.val x)
    rw [hf,hg,mul_add]
  smul_mem' := by
    intro a f hf G x
    change a * f.val _ = _ * (a * f.val x)
    rw [hf]
    ring

instance (w : I → ℤ) : SetLike.GradedMonoid (kingSemiInvariants b d e w) where
  one_mem := by intro G x; simp
  mul_mem := by
    intro i j f g hf hg G x
    change f.val _ * g.val _ = _ ^ (i + j) * (f.val x * g.val x)
    rw [hf,hg,pow_add]
    ring

/-- The graded ring whose Proj defines the character quotient. -/
abbrev KingSemiInvariantRing (w : I → ℤ) := ⨁ m : ℕ, ↥(kingSemiInvariants b d e w m)

variable (w : I → ℤ)

abbrev KingPiece (m : ℕ) := ↥(kingSemiInvariants b d e w m)

local notation "A" => KingPiece b d e w

noncomputable instance : CommRing (KingSemiInvariantRing b d e w) :=
  @DirectSum.commRing ℕ _ _ _ _ (SetLike.gcommRing (kingSemiInvariants b d e w))

/-- The homogeneous pieces inside the direct sum ring. -/
noncomputable def kingGrading (m : ℕ) : AddSubgroup (KingSemiInvariantRing b d e w) :=
  AddMonoidHom.range (G := A m) (DirectSum.of A m)

instance : SetLike.GradedMonoid (kingGrading b d e w) where
  one_mem := ⟨_,(DirectSum.one_def _).symm⟩
  mul_mem := by
    rintro i j _ _ ⟨f,rfl⟩ ⟨g,rfl⟩
    exact ⟨_,(DirectSum.of_mul_of f g).symm⟩

noncomputable instance : GradedRing (kingGrading b d e w) := by
  let ins (m : ℕ) := AddMonoidHom.rangeRestrict (G := A m) (DirectSum.of A m)
  let deg := kingGrading b d e w
  let split := DirectSum.toAddMonoid (fun m ↦ (DirectSum.of (fun i ↦ ↥(deg i)) m).comp (ins m))
  refine { (inferInstance : SetLike.GradedMonoid deg) with
    toDecomposition := DirectSum.Decomposition.ofAddHom deg split ?_ ?_ }
  · apply DirectSum.addHom_ext
    intro i x
    change (DirectSum.coeAddMonoidHom deg) (split (DirectSum.of A i x)) = _
    rw [DirectSum.toAddMonoid_of]
    exact DirectSum.coeAddMonoidHom_of deg i (ins i x)
  · apply DirectSum.addHom_ext
    rintro i ⟨_,x,rfl⟩
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, split,
      DirectSum.toAddMonoid_of, AddMonoidHom.id_apply]
    rfl

/-- The projective GIT scheme for the chosen vertex determinant character. -/
noncomputable def kingProj : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Proj (kingGrading b d e w)
end

section
variable {k R I J : Type u} [Field k] [Ring R] [Algebra k R]
    [Fintype I] [DecidableEq I] [Fintype J] (b : Module.Basis J k R)
    {d : I → ℕ} {e : I → R} (C : Set (VertexRepresentation (k := k) d e))

/-- Regular functions on a component transforming by the specified determinant character.
Regularity is restriction of a polynomial in the action matrices. The transformation
law is imposed on the function itself, independently of its polynomial representative. -/
def componentWeightSpace (w : I → ℤ) : Submodule k (C → k) where
  carrier := {f | (∃ p : coordinateAlgebra b d e, ∀ x : C, p.val x.val = f x) ∧
    ∀ (G : BaseChange k d) (x y : C), y.val = G⁻¹ • x.val →
      f y = (vertexCharacter d w G : kˣ) * f x}
  zero_mem' := ⟨⟨0,fun _ ↦ rfl⟩,by simp⟩
  add_mem' := by
    rintro f g ⟨⟨p,hp⟩,hf⟩ ⟨⟨q,hq⟩,hg⟩
    refine ⟨⟨p+q, fun x ↦ congrArg₂ (· + ·) (hp x) (hq x)⟩,?_⟩
    intro G x y he
    exact (congrArg₂ (· + ·) (hf G x y he) (hg G x y he)).trans (mul_add ..).symm
  smul_mem' := by
    rintro a f ⟨⟨p,hp⟩,hf⟩
    refine ⟨⟨a • p,fun x ↦ congrArg (a * ·) (hp x)⟩,?_⟩
    intro G x y he
    change a * f y = _ * (a * f x)
    rw [hf G x y he, mul_left_comm]
end
end VertexRepresentation

/-- A split basic algebra Morita equivalent to the algebra of right modules, together
with its complete vertex idempotents and their dimensions on the simple modules. -/
structure Chart (k R : Type u) [Field k] [Ring R] where
  A : Type u
  [ring : Ring A]
  [algebra : Algebra k A]
  [finite : Module.Finite k A]
  n : ℕ
  vertex : ULift.{u} (Fin n) → A
  complete : CompleteOrthogonalIdempotents vertex
  index : simpleClasses A ≃ ULift.{u} (Fin n)
  dimension : ∀ s i, Module.finrank k
    (VertexRepresentation.vertexPart (k := k) vertex ((fromSkeleton _).obj s.val) i) =
      if index s = i then 1 else 0
  equivalence : Mod Rᵐᵒᵖ ≌ Mod A

attribute [instance] Chart.ring Chart.algebra Chart.finite

namespace Chart
open VertexRepresentation
variable {k R : Type u} [Field k] [Ring R] (C : Chart k R)

noncomputable def basis := (Module.finBasis k C.A).reindex (Equiv.ulift.{u}.symm)

def KingCondition : Prop :=
  ∀ (w : ULift.{u} (Fin C.n) → ℤ) (d : ULift.{u} (Fin C.n) → ℕ),
    let X := kingProj C.basis d C.vertex w
    Set.Subsingleton {x : X | IsClosed ({x} : Set X)}

def BrickOrbits : Prop :=
  ∀ d (x : VertexRepresentation (k := k) d C.vertex), Brick x.moduleObj →
    @IsOpen _ (zariski C.basis) (MulAction.orbit (BaseChange k d) x)

def WideLoci : Prop :=
  letI := IsNoetherianRing.of_finite k C.A
  ∀ d (W : ObjectProperty (Mod C.A)), Wide W →
    @IsOpen (VertexRepresentation (k := k) d C.vertex) (zariski C.basis) {x | W x.moduleObj}

def MultiplicityFree : Prop :=
  ∀ d, ∀ Z ∈ @irreducibleComponents _ (zariski (d := d) (e := C.vertex) C.basis),
    ∀ w, Module.rank k (componentWeightSpace C.basis Z w) ≤ 1
end Chart

/-- Every algebra admits the required basic presentation. Each criterion is tested in all such presentations. -/
def AlgebraicallyClosedField : Prop :=
  ∀ (k R : Type u) [Field k] [IsAlgClosed k] [Ring R] [Algebra k R] [Module.Finite k R],
    Nonempty (Chart k R) ∧
    (EFinite Rᵐᵒᵖ ↔ ∀ C : Chart k R, C.KingCondition) ∧
    (EFinite Rᵐᵒᵖ ↔ ∀ C : Chart k R, C.BrickOrbits) ∧
    (EFinite Rᵐᵒᵖ ↔ ∀ C : Chart k R, C.WideLoci)

/-- Weyman's conjecture over an algebraically closed field of any characteristic. -/
def BrickDiscreteMultiplicityFree : Prop :=
  ∀ (k R : Type u) [Field k] [IsAlgClosed k] [Ring R] [Algebra k R] [Module.Finite k R],
    let A := Rᵐᵒᵖ
    letI := IsNoetherianRing.of_finite k A
    (∀ c : K₀ A, (classes (fun X : Mod A ↦ cl X = c ∧ Brick X)).Finite) ↔
      ∀ C : Chart k R, C.MultiplicityFree

end EFiniteCharacterizations.Statement
