module

public import EFiniteCharacterizations.Geometry.VertexMatrixLocalization
public import EFiniteCharacterizations.Geometry.KingModuli
public import EFiniteCharacterizations.Characterizations.ModuleCriteria

/-! # Multiplicity-freeness on irreducible components -/

@[expose] public section

universe u
namespace EFiniteCharacterizations

namespace VertexRepresentation

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

omit [DecidableEq I] in
private theorem character_multiple (w : I → ℤ) (m : ℕ) (G : BaseChange k d) :
    vertexCharacter d (fun i ↦ w i * (m : ℤ)) G = vertexCharacter d w G ^ m := by
  simp [vertexCharacter, zpow_mul, Finset.prod_pow]

/-- Restriction of a degree-m global form to the component gives a regular
semi-invariant of weight m times the original weight. -/
def restrictKingPiece {w : I → ℤ} {m : ℕ} (f : KingPiece b d e w m) :
    componentWeightSpace b C (fun i ↦ w i * (m : ℤ)) :=
  ⟨fun x ↦ f.val.val x.val, ⟨f.val, fun _ ↦ rfl⟩, fun G x y he ↦ by
    change f.val.val y.val = _ * f.val.val x.val
    rw [he,character_multiple, Units.val_pow_eq_pow_val]
    exact f.property G x.val⟩

omit [Fintype J] in
/-- Two unequal values of a ratio on the same component rule out multiplicity one there. -/
theorem not_rank_le_one_of_separating_forms {w : I → ℤ} {m : ℕ}
    (f q : KingPiece b d e w m) (x y : C)
    (hsep : f.val.val x.val * q.val.val y.val ≠ f.val.val y.val * q.val.val x.val) :
    ¬ Module.rank k (componentWeightSpace b C (fun i ↦ w i * (m : ℤ))) ≤ 1 := by
  intro hr
  obtain ⟨v,hv⟩ := rank_le_one_iff.mp hr
  obtain ⟨a,ha⟩ := hv (restrictKingPiece b C f)
  obtain ⟨t,ht⟩ := hv (restrictKingPiece b C q)
  have eval {l : k} {p : KingPiece b d e w m} (h : l • v = restrictKingPiece b C p) (z : C) :
      l * v.val z = p.val.val z.val :=
    congrFun (congrArg Subtype.val h) z
  apply hsep
  rw [← eval ha x, ← eval ht y, ← eval ha y, ← eval ht x]
  ring

/-- On the entire reduced variety, one closed King point bounds the dimension
of every positive-degree piece. Evaluations at any two relevant points have the
same kernel, so a nonzero form spans the piece. -/
theorem rank_kingPiece_le_one_of_closedPoints (w : I → ℤ) (m : ℕ) (hm : 0 < m)
    (hc : Set.Subsingleton {p : ProjectiveSpectrum (kingGrading b d e w) |
      IsClosed ({p} : Set (ProjectiveSpectrum (kingGrading b d e w)))}) :
    Module.rank k (KingPiece b d e w m) ≤ 1 := by
  classical
  let : AddCommGroup (KingPiece b d e w m) := (kingSemiInvariants b d e w m).addCommGroup
  apply (rank_le_one_iff (K := k) (V := KingPiece b d e w m)).mpr
  by_cases hn : ∃ (q : KingPiece b d e w m) (x : VertexRepresentation (k := k) d e), q.val.val x ≠ 0
  · obtain ⟨q,x,hx⟩ := hn
    refine ⟨q,fun f ↦ ⟨f.val.val x / q.val.val x,?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    funext y
    change f.val.val x / q.val.val x * q.val.val y = f.val.val y
    by_cases hy : ∃ p : KingPiece b d e w m, p.val.val y ≠ 0
    · obtain ⟨p,hy⟩ := hy
      let px := kingPoint b w x ⟨m,hm,q,hx⟩
      let py := kingPoint b w y ⟨m,hm,p,hy⟩
      have he : px = py := hc (isClosed_kingPoint b w x _) (isClosed_kingPoint b w y _)
      let a := (f.val.val x / q.val.val x) • q - f
      have ha : DirectSum.of (KingPiece b d e w) m a ∈ px.asHomogeneousIdeal.toIdeal := by
        change kingEvaluation b w x _ = 0
        rw [kingEvaluation_of]
        change Polynomial.monomial m (f.val.val x / q.val.val x * q.val.val x - f.val.val x) = 0
        simp [hx]
      rw [he] at ha
      change kingEvaluation b w y _ = 0 at ha
      rw [kingEvaluation_of] at ha
      have hz := congrArg (fun p : Polynomial k ↦ p.coeff m) ha
      simp only [Polynomial.coeff_monomial_same, Polynomial.coeff_zero] at hz
      exact sub_eq_zero.mp hz
    · push Not at hy
      simp [hy f,hy q]
  · push Not at hn
    refine ⟨0,fun f ↦ ⟨0,?_⟩⟩
    rw [zero_smul]
    apply Subtype.ext
    apply Subtype.ext
    exact funext fun x ↦ (hn f x).symm

/-- At an E-finite split basic algebra the global semi-invariants of each
determinant character form a vector space of dimension at most one. -/
theorem SplitBasicVertices.rank_kingPiece_le_one_of_isEFinite [Module.Finite k R]
    [IsNoetherianRing R] [IsArtinianRing R] [Infinite k] (P : SplitBasicVertices k R I)
    (h : IsEFinite R) (w : I → ℤ) (m : ℕ) (hm : 0 < m) :
    Module.rank k (KingPiece b d P.vertex w m) ≤ 1 := by
  apply rank_kingPiece_le_one_of_closedPoints b w m hm
  let a := ∑ j, w j • ProjectiveClass.of (P.vertexProjective j)
  have hc := P.atMostOneKingClosedPoint_of_isEFinite (d := d) b a h
  unfold SplitBasicVertices.atMostOneKingClosedPoint SplitBasicVertices.kingModuli at hc
  rw [show P.characterExponents a = w from P.characterExponents_vertex_sum w] at hc
  exact hc

/-- On the full variety every regular function transforming by the character is
a global degree-one form. -/
noncomputable def univWeightSpaceEquiv (w : I → ℤ) :
    KingPiece b d e w 1 ≃ₗ[k] componentWeightSpace b (Set.univ (α := VertexRepresentation (k := k) d e)) w :=
  LinearEquiv.ofBijective
    { toFun := fun f ↦ ⟨fun x ↦ f.val.val x.val, ⟨f.val,fun _ ↦ rfl⟩, fun G x y he ↦ by
        change f.val.val y.val = _
        rw [he]
        simpa using f.property G x.val⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    ⟨fun f q h ↦ Subtype.ext (Subtype.ext (funext fun x ↦
        congrArg (fun v ↦ v.val ⟨x,Set.mem_univ _⟩) h)),
      fun f ↦ by
        obtain ⟨⟨p,hp⟩,hf⟩ := f.property
        refine ⟨⟨p,fun G x ↦ ?_⟩,Subtype.ext (funext hp)⟩
        simpa only [pow_one,← hp] using hf G ⟨x,Set.mem_univ _⟩ ⟨_,Set.mem_univ _⟩ rfl⟩

/-- The componentwise bound holds at every dimension vector for which the
fixed-vertex variety is irreducible. -/
theorem SplitBasicVertices.rank_componentWeightSpace_le_one_of_irreducible [Module.Finite k R]
    [IsNoetherianRing R] [IsArtinianRing R] [Infinite k] (P : SplitBasicVertices k R I)
    (h : IsEFinite R) (w : I → ℤ)
    (hi : @IrreducibleSpace _ (zariski (d := d) (e := P.vertex) b))
    (C : Set (VertexRepresentation (k := k) d P.vertex))
    (hC : C ∈ @irreducibleComponents _ (zariski (d := d) (e := P.vertex) b)) :
    Module.rank k (componentWeightSpace b C w) ≤ 1 := by
  let := zariski (d := d) (e := P.vertex) b
  have hc : C = Set.univ := by simpa [irreducibleComponents_eq_singleton] using hC
  subst C
  rw [← (univWeightSpaceEquiv b w).rank_eq]
  exact P.rank_kingPiece_le_one_of_isEFinite b h w 1 Nat.zero_lt_one

end VertexRepresentation

open VertexRepresentation

/-- Each determinant-character space on each irreducible component of each
fixed-vector representation variety of the basic presentation has dimension at most one. -/
def BasicPresentation.IsMultiplicityFree {k R : Type u} [Field k] [Ring R]
    (P : BasicPresentation k R) : Prop :=
  ∀ d, ∀ C ∈ @irreducibleComponents _ (zariski (d := d) (e := P.vertices.vertex) P.algebraBasis),
    ∀ (w : _ → ℤ), Module.rank k (componentWeightSpace P.algebraBasis C w) ≤ 1

/-- Over an algebraically closed field a multiplicity-free algebra is E-finite. -/
theorem isEFinite_of_multiplicityFree (k R : Type u) [Field k] [IsAlgClosed k] [Ring R]
    [Algebra k R] [Module.Finite k R] :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    (basicPresentation k R).IsMultiplicityFree → IsEFinite Rᵐᵒᵖ := by
  let P := basicPresentation k R
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  let := IsNoetherianRing.of_finite k P.Carrier
  let := IsArtinianRing.of_finite k P.Carrier
  intro h
  apply (isEFinite_iff_of_module_equivalence k k P.equivalence).2
  by_contra hn
  obtain ⟨_,d,C,hC,x,hx,y,hy,_,_,f,q,_,_,hsep⟩ :=
    P.vertices.exists_separating_forms_on_component P.algebraBasis hn
  exact not_rank_le_one_of_separating_forms P.algebraBasis C f q ⟨x,hx⟩ ⟨y,hy⟩ hsep (h d C hC _)

/-- The multiplicity-free hypothesis gives finitely many bricks of each ordinary dimension vector. -/
theorem brick_discrete_of_multiplicityFree (k R : Type u) [Field k] [IsAlgClosed k] [Ring R]
    [Algebra k R] [Module.Finite k R] :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    letI := IsArtinianRing.of_finite k Rᵐᵒᵖ
    (basicPresentation k R).IsMultiplicityFree → ∀ d : simpleIsomorphismClasses Rᵐᵒᵖ → ℕ,
      (brickClassesOfClass (classOfCompositionVector k d)).Finite := by
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  exact fun h ↦ (compositionVectorCriteria k R).1.mp (isEFinite_of_multiplicityFree k R h)

end EFiniteCharacterizations
