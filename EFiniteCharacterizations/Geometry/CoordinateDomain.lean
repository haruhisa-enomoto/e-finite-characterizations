module

public import EFiniteCharacterizations.Geometry.ZariskiLoci
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Coordinate rings of irreducible sets of representations -/

@[expose] public section

open TopologicalSpace

namespace EFiniteCharacterizations

variable {k σ X : Type*} [Field k]

/-- Polynomials that vanish throughout the given set of coordinate points. -/
noncomputable def coordinateIdeal (c : X → σ → k) (S : Set X) : Ideal (MvPolynomial σ k) :=
  ⨅ x : S, RingHom.ker (MvPolynomial.eval (c x))

@[simp] theorem mem_coordinateIdeal (c : X → σ → k) (S : Set X) (p : MvPolynomial σ k) :
    p ∈ coordinateIdeal c S ↔ ∀ x ∈ S, MvPolynomial.eval (c x) p = 0 := by
  simp [coordinateIdeal, RingHom.mem_ker]

/-- Irreducibility makes the ring of polynomial functions a domain. -/
theorem coordinateIdeal_isPrime (c : X → σ → k) (S : Set X)
    (hS : @IsIrreducible X (coordinateZariski c) S) : (coordinateIdeal c S).IsPrime := by
  let := coordinateZariski c
  refine ⟨?_,?_⟩
  · intro h
    obtain ⟨x,hx⟩ := hS.nonempty
    have hu : (1 : MvPolynomial σ k) ∈ coordinateIdeal c S := by rw [h]; trivial
    exact (one_ne_zero : (1 : k) ≠ 0) (by simpa using (mem_coordinateIdeal c S 1).1 hu x hx)
  · intro p q hpq
    by_contra! h
    simp only [mem_coordinateIdeal, not_forall] at h
    obtain ⟨⟨x,hx,hpx⟩,⟨y,hy,hqy⟩⟩ := h
    obtain ⟨z,hz,hpz,hqz⟩ := hS.isPreirreducible
      {x | MvPolynomial.eval (c x) p ≠ 0} {x | MvPolynomial.eval (c x) q ≠ 0}
      (coordinateZariski_isOpen_ne_zero c p) (coordinateZariski_isOpen_ne_zero c q)
      ⟨x,hx,hpx⟩ ⟨y,hy,hqy⟩
    exact mul_ne_zero hpz hqz (by simpa only [map_mul] using (mem_coordinateIdeal c S (p*q)).1 hpq z hz)

/-- Evaluation descends to a point of the coordinate ring. -/
noncomputable def coordinateEval (c : X → σ → k) (S : Set X) (x : S) :
    (MvPolynomial σ k ⧸ coordinateIdeal c S) →+* k :=
  Ideal.Quotient.lift _ (MvPolynomial.eval (c x))
    (fun p hp ↦ (mem_coordinateIdeal c S p).1 hp x x.property)

@[simp] theorem coordinateEval_mk (c : X → σ → k) (S : Set X) (x : S)
    (p : MvPolynomial σ k) :
    coordinateEval c S x (Ideal.Quotient.mk _ p) = MvPolynomial.eval (c x) p := rfl

/-- A polynomial function on the set is determined by all its point values. -/
theorem coordinateEval_ext (c : X → σ → k) (S : Set X)
    {p q : MvPolynomial σ k ⧸ coordinateIdeal c S}
    (h : ∀ x : S, coordinateEval c S x p = coordinateEval c S x q) : p = q := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective p
  obtain ⟨q,rfl⟩ := Ideal.Quotient.mk_surjective q
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (mem_coordinateIdeal c S _).2 fun x hx ↦ by
    rw [map_sub, sub_eq_zero]
    exact h ⟨x,hx⟩

/-- Matrix-valued polynomial functions that specialize to representations
at every point define a representation over the coordinate ring. -/
noncomputable def coordinateRepresentation (c : X → σ → k) (S : Set X)
    {A n : Type*} [Ring A] [Fintype n] [DecidableEq n]
    (ρ : S → A →+* Matrix n n k)
    (P : A → Matrix n n (MvPolynomial σ k))
    (hP : ∀ (x : S) a, (P a).map (MvPolynomial.eval (c x)) = ρ x a) :
    A →+* Matrix n n (MvPolynomial σ k ⧸ coordinateIdeal c S) := by
  let φ (a : A) := (P a).map (Ideal.Quotient.mk (coordinateIdeal c S))
  have hs (x : S) (a : A) : (coordinateEval c S x).mapMatrix (φ a) = ρ x a := hP x a
  have he {U V : Matrix n n (MvPolynomial σ k ⧸ coordinateIdeal c S)}
      (h : ∀ x : S, (coordinateEval c S x).mapMatrix U = (coordinateEval c S x).mapMatrix V) :
      U = V := by
    ext i j
    apply coordinateEval_ext c S
    intro x
    exact congrArg (fun M : Matrix n n k ↦ M i j) (h x)
  exact
    { toFun := φ
      map_zero' := he (fun x ↦ by rw [hs, map_zero, map_zero])
      map_one' := he (fun x ↦ by rw [hs, map_one, map_one])
      map_add' := fun a b ↦ he (fun x ↦ by rw [hs, map_add, map_add, hs, hs])
      map_mul' := fun a b ↦ he (fun x ↦ by rw [hs, map_mul, map_mul, hs, hs]) }

@[simp] theorem coordinateRepresentation_eval (c : X → σ → k) (S : Set X)
    {A n : Type*} [Ring A] [Fintype n] [DecidableEq n]
    (ρ : S → A →+* Matrix n n k)
    (P : A → Matrix n n (MvPolynomial σ k))
    (hP : ∀ (x : S) a, (P a).map (MvPolynomial.eval (c x)) = ρ x a)
    (x : S) (a : A) :
    (coordinateEval c S x).mapMatrix (coordinateRepresentation c S ρ P hP a) = ρ x a :=
  hP x a

/-- A relation in the fraction-field representation holds in every fibre. -/
theorem specialization_of_coordinateRelation (c : X → σ → k) (S : Set X)
    {n : Type*} [Fintype n] [DecidableEq n]
    [IsDomain (MvPolynomial σ k ⧸ coordinateIdeal c S)]
    {U V : Matrix n n (MvPolynomial σ k ⧸ coordinateIdeal c S)}
    (h : U.map (algebraMap _ (FractionRing (MvPolynomial σ k ⧸ coordinateIdeal c S))) =
      V.map (algebraMap _ (FractionRing (MvPolynomial σ k ⧸ coordinateIdeal c S))))
    (x : S) : (coordinateEval c S x).mapMatrix U = (coordinateEval c S x).mapMatrix V := by
  have he : U = V := by
    ext i j
    exact IsFractionRing.injective _ _ (congrArg (fun M ↦ M i j) h)
  rw [he]

/-- Matrix entries of a generating set determine polynomial formulas for
the matrix entries of every element of the algebra. -/
theorem exists_action_polynomials {F A n : Type*} [Field F] [Algebra k F] [Ring A] [Algebra k A]
    [Fintype n] [DecidableEq n] (G : Set A) (hG : Algebra.adjoin k G = ⊤)
    (ρ : X → A →ₐ[k] Matrix n n F) :
    ∃ P : A → Matrix n n (MvPolynomial (G × n × n) F), ∀ x a,
      (P a).map (MvPolynomial.eval (fun j : G × n × n ↦ ρ x j.1 j.2.1 j.2.2)) = ρ x a := by
  classical
  have h (a : A) : ∃ p : Matrix n n (MvPolynomial (G × n × n) F), ∀ x,
      p.map (MvPolynomial.eval (fun j : G × n × n ↦ ρ x j.1 j.2.1 j.2.2)) = ρ x a := by
    have ha : a ∈ Algebra.adjoin k G := by rw [hG]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      refine ⟨Matrix.of fun i j ↦ MvPolynomial.X (⟨a,ha⟩,i,j), fun x ↦ ?_⟩
      ext i j
      exact MvPolynomial.eval_X _
    | algebraMap r =>
      refine ⟨(algebraMap k (Matrix n n F) r).map MvPolynomial.C,fun x ↦ ?_⟩
      rw [AlgHom.commutes]
      ext i j
      exact MvPolynomial.eval_C _
    | add a b _ _ ha hb =>
      obtain ⟨p,hp⟩ := ha
      obtain ⟨q,hq⟩ := hb
      refine ⟨p+q,fun x ↦ ?_⟩
      rw [Matrix.map_add, hp, hq, map_add]; exact map_add _
    | mul a b _ _ ha hb =>
      obtain ⟨p,hp⟩ := ha
      obtain ⟨q,hq⟩ := hb
      refine ⟨p*q,fun x ↦ ?_⟩
      rw [Matrix.map_mul, hp, hq, map_mul]
  choose P hP using h
  exact ⟨P,fun x a ↦ hP a x⟩

/-- One component of an infinite Noetherian space contains infinitely many points. -/
theorem exists_infinite_irreducibleComponent [TopologicalSpace X] [NoetherianSpace X] [Infinite X] :
    ∃ S ∈ irreducibleComponents X, S.Infinite := by
  classical
  by_contra! h
  have hf := NoetherianSpace.finite_irreducibleComponents (α := X)
  have hu : (Set.univ : Set X).Finite := by
    rw [← sUnion_irreducibleComponents]
    exact hf.sUnion h
  exact Set.infinite_univ hu

end EFiniteCharacterizations
