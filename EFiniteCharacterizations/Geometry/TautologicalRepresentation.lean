module

public import EFiniteCharacterizations.Geometry.CoordinateDomain
public import EFiniteCharacterizations.Geometry.HomLoci
public import EFiniteCharacterizations.LinearAlgebra.MatrixSpanSpecialization

/-! # The tautological action on a based family -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u w

namespace EFiniteCharacterizations

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
  {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

/-- The full action of the algebra in a chosen basis of a finite module. -/
noncomputable def basedAction {M : FGModuleCat.{u} R}
    (v : Module.Basis n k (M.obj : Type u)) : R →ₐ[k] Matrix n n k :=
  (LinearMap.toMatrixAlgEquiv v).toAlgHom.comp (Algebra.lsmul k k (M.obj : Type u))

variable {X : Type*} (M : X → FGModuleCat.{u} R)
    (v : ∀ x, Module.Basis n k ((M x).obj : Type u)) (b : Module.Basis ι k R)

/-- Coordinates of the matrices of the algebra basis elements. -/
noncomputable def basedActionCoordinates (x : X) (i : ι × n × n) : k :=
  actionMatrices b (v x) i.1 i.2.1 i.2.2

noncomputable def actionPolynomial (b : Module.Basis ι k R) (r : R) :
    Matrix n n (MvPolynomial (ι × n × n) k) :=
  ∑ j : ι, (MvPolynomial.C (b.repr r j) : MvPolynomial (ι × n × n) k) •
    Matrix.of (fun i l : n ↦ MvPolynomial.X (j,i,l))

theorem actionPolynomial_eval (x : X) (r : R) :
    (actionPolynomial (n := n) b r).map (MvPolynomial.eval (basedActionCoordinates M v b x)) =
      basedAction (v x) r := by
  classical
  let f := (basedAction (v x)).toLinearMap
  have h := congrArg f (b.sum_repr r)
  simp only [map_sum,map_smul] at h
  rw [← show f r = basedAction (v x) r from rfl, ← h]
  ext i j
  simp only [actionPolynomial, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rfl

/-- The action of the algebra by matrices of polynomial functions on the family. -/
noncomputable def tautologicalRepresentation (S : Set X) :
    R →+* Matrix n n (MvPolynomial (ι × n × n) k ⧸ coordinateIdeal (basedActionCoordinates M v b) S) :=
  coordinateRepresentation (basedActionCoordinates M v b) S
    (fun x ↦ (basedAction (v x)).toRingHom) (actionPolynomial (n := n) b)
    (fun x ↦ actionPolynomial_eval M v b x)

@[simp] theorem tautologicalRepresentation_eval (S : Set X) (x : S) (r : R) :
    (coordinateEval (basedActionCoordinates M v b) S x).mapMatrix
      (tautologicalRepresentation M v b S r) = basedAction (v x) r :=
  coordinateRepresentation_eval _ _ _ _ _ _ _

/-- Relations in the generic matrix action hold in every member of the family. -/
theorem basedAction_eq_of_generic_eq (S : Set X)
    [IsDomain (MvPolynomial (ι × n × n) k ⧸ coordinateIdeal (basedActionCoordinates M v b) S)]
    (r s : R) (h :
      (tautologicalRepresentation M v b S r).map (algebraMap _ (FractionRing (MvPolynomial (ι × n × n) k ⧸ coordinateIdeal (basedActionCoordinates M v b) S))) =
      (tautologicalRepresentation M v b S s).map (algebraMap _ (FractionRing (MvPolynomial (ι × n × n) k ⧸ coordinateIdeal (basedActionCoordinates M v b) S))))
    (x : S) : basedAction (v x) r = basedAction (v x) s := by
  simpa only [tautologicalRepresentation_eval] using
    specialization_of_coordinateRelation (basedActionCoordinates M v b) S h x

/-- Full scalar span implies the prime-ring sandwich criterion for the
image of a matrix representation. -/
theorem matrix_image_exists_nonzero_sandwich {K A : Type*} [Field K] [Ring A]
    (ρ : A →+* Matrix n n K) (hspan : Submodule.span K (Set.range ρ) = ⊤)
    (a b : A) (ha : ρ a ≠ 0) (hb : ρ b ≠ 0) :
    ∃ x : A, ρ (a * x * b) ≠ 0 := by
  classical
  by_contra! h
  have hz (M : Matrix n n K) : ρ a * M * ρ b = 0 := by
    have hm : M ∈ Submodule.span K (Set.range ρ) := by rw [hspan]; trivial
    induction hm using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨x,rfl⟩ := hM
      simpa only [map_mul] using h x
    | zero => simp
    | add X Y _ _ hX hY => simp [Matrix.mul_add, Matrix.add_mul, hX, hY]
    | smul c X _ hX => simp [hX]
  obtain ⟨i,j,hij⟩ : ∃ i j, ρ a i j ≠ 0 := by
    by_contra! hzero
    exact ha (Matrix.ext hzero)
  obtain ⟨l,m,hlm⟩ : ∃ l m, ρ b l m ≠ 0 := by
    by_contra! hzero
    exact hb (Matrix.ext hzero)
  have he := congrArg (fun M : Matrix n n K ↦ M i m) (hz (Matrix.single j l (1 : K)))
  change (ρ a * Matrix.single j l (1 : K) * ρ b) i m = 0 at he
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single j] at he
  · exact mul_ne_zero hij hlm (by simpa using he)
  · intro x _ hx
    have hzero := Matrix.single_mul_apply_of_ne (1 : K) j l x m hx (ρ b)
    exact (congrArg (fun z : K ↦ ρ a i x * z) hzero).trans (mul_zero _)
  · simp

/-- If one fibre has full matrix span, the generic image satisfies the
prime-ring sandwich criterion. -/
theorem generic_image_exists_nonzero_sandwich {D K A : Type*}
    [CommRing D] [IsDomain D] [Field K] [Ring A]
    (ρ : A →+* Matrix n n D) (e : D →+* K)
    (he : Submodule.span K (Set.range fun a ↦ (ρ a).map e) = ⊤)
    (a b : A)
    (ha : (ρ a).map (algebraMap D (FractionRing D)) ≠ 0)
    (hb : (ρ b).map (algebraMap D (FractionRing D)) ≠ 0) :
    ∃ x : A, (ρ (a * x * b)).map (algebraMap D (FractionRing D)) ≠ 0 := by
  let g := algebraMap D (FractionRing D)
  exact matrix_image_exists_nonzero_sandwich (g.mapMatrix.comp ρ)
    (matrix_span_eq_top_of_specialization e g (IsFractionRing.injective D _) ρ he) a b ha hb

/-- An infinite family of full-span geometric representations of a finitely
generated ground algebra has an infinite subfamily with a prime generic
image. Every relation in that image holds throughout the subfamily. -/
theorem exists_generic_prime_image {k F A : Type u} {n : Type w} {X : Type*} [Field k] [Field F] [Algebra k F]
    [Ring A] [Algebra k A] [Infinite X] [Fintype n] [DecidableEq n]
    (G : Set A) (hfin : G.Finite) (hG : Algebra.adjoin k G = ⊤)
    (ρ : X → A →ₐ[k] Matrix n n F)
    (hfull : ∀ x, Submodule.span F (Set.range (ρ x)) = ⊤) :
    ∃ (S : Set X) (_ : S.Infinite) (K : Type (max u w)) (_ : Field K)
      (q : A →+* Matrix n n K), Submodule.span K (Set.range q) = ⊤ ∧
      (∀ a b, q a ≠ 0 → q b ≠ 0 → ∃ z, q (a * z * b) ≠ 0) ∧
      ∀ a b, q a = q b → ∀ x ∈ S, ρ x a = ρ x b := by
  classical
  let := hfin.fintype
  let c (x : X) (i : G × n × n) := ρ x i.1 i.2.1 i.2.2
  let := coordinateZariski c
  let := coordinateZariski_noetherian c
  obtain ⟨S,hS,hi⟩ := exists_infinite_irreducibleComponent (X := X)
  have hp := coordinateIdeal_isPrime c S hS.1
  let := hp
  let D := MvPolynomial (G × n × n) F ⧸ coordinateIdeal c S
  let K := FractionRing D
  obtain ⟨P,hP⟩ := exists_action_polynomials G hG ρ
  let ψ := coordinateRepresentation c S (fun x ↦ (ρ x).toRingHom) P (fun x a ↦ hP x a)
  have hev (x : S) (a : A) : (coordinateEval c S x).mapMatrix (ψ a) = ρ x a :=
    coordinateRepresentation_eval _ _ _ _ _ _ _
  let q := (algebraMap D K).mapMatrix.comp ψ
  obtain ⟨x,hx⟩ := hi.nonempty
  let y : S := ⟨x,hx⟩
  have hgeneric : Submodule.span K (Set.range q) = ⊤ := by
    apply matrix_span_eq_top_of_specialization (coordinateEval c S y) (algebraMap D K)
      (IsFractionRing.injective D K) ψ
    change Submodule.span F (Set.range fun a ↦ (coordinateEval c S y).mapMatrix (ψ a)) = ⊤
    simpa only [hev] using hfull x
  refine ⟨S,hi,K,inferInstance,q,hgeneric,?_,?_⟩
  · exact matrix_image_exists_nonzero_sandwich q hgeneric
  · intro a b h z hz
    simpa only [hev] using specialization_of_coordinateRelation c S h (⟨z,hz⟩ : S)

end EFiniteCharacterizations
