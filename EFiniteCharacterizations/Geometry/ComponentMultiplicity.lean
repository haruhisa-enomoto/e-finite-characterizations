module

public import EFiniteCharacterizations.Geometry.ComponentDegeneration
public import EFiniteCharacterizations.Geometry.MultiplicityFree

/-!
# Semi-invariant multiplicities on irreducible components and Weyman's conjecture

Corollary C (`cor:intro-weyman`, Weyman's conjecture) and Section 6 of the manuscript.
Over an algebraically closed field `k` of arbitrary characteristic, an algebra is
*multiplicity-free* if on every irreducible component `Z` of every representation
variety `rep(Λ, d)`, the weight space of `GL(d)`-semi-invariants has dimension at
most one for every character `w`.

* `SplitBasicVertices.rank_componentWeightSpace_le_one_of_isEFinite`: when `Λ` is
  E-finite, degenerating a general point of `Z` to its polystable limit and using
  linear independence of the classes of stable bricks shows that all semi-invariants
  of weight `w` on `Z` are proportional.
* `isEFinite_iff_multiplicityFree`: E-finiteness is equivalent to multiplicity-freeness.
* `brick_discrete_iff_multiplicityFree` (**Corollary C**): combining this with
  Theorem A(II) (`(E-fin) ⇔ (dim-brick)`), Schur-representation-finiteness is
  equivalent to multiplicity-freeness.
-/

@[expose] public section

open CategoryTheory
universe u
namespace EFiniteCharacterizations
namespace VertexRepresentation

variable {k R I J : Type u} [Field k] [IsAlgClosed k] [Ring R] [Algebra k R]
    [Fintype I] [DecidableEq I] [Fintype J] (b : Module.Basis J k R)
    {d : I → ℕ} {e : I → R} {w : I → ℤ}

local notation "X" => VertexRepresentation (k := k) d e
local notation "Z" => zariski (d := d) (e := e) b

variable {C : Set (VertexRepresentation (k := k) d e)}
    (hC : C ∈ @irreducibleComponents _ (zariski (d := d) (e := e) b))

private theorem component_total_weight_zero (x : C) (f : componentWeightSpace b C w)
    (hf : f.val x ≠ 0) : ∑ i, (d i : ℤ) * w i = 0 := by
  let n := ∑ i, (d i : ℤ) * w i
  have ht (t : kˣ) : t ^ n = 1 := by
    have hfix : x.val = (centralBaseChange (d := d) t)⁻¹ • x.val := by
      apply eq_inv_smul_iff.2
      exact centralBaseChange_fixes x.val t
    have h := f.property.2 (centralBaseChange t) x x hfix
    rw [centralBaseChange_character] at h
    apply Units.ext
    apply mul_right_cancel₀ hf
    simpa only [Units.val_one, one_mul] using h.symm
  by_contra hn
  have he : (Polynomial.X : Polynomial k) ^ n.natAbs = 1 := by
    apply polynomial_identity_on_units
    intro t
    simpa only [Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_one,Units.val_pow_eq_pow_val,
      Units.val_one] using congrArg Units.val (pow_natAbs_eq_one.mpr (ht t))
  have h := congrArg (Polynomial.eval (0 : k)) he
  simp [zero_pow (show n.natAbs ≠ 0 from Int.natAbs_ne_zero.mpr hn)] at h

include hC in
private theorem vanishing_on_positive_degeneration (x : C) (f : componentWeightSpace b C w)
    {y : k → X} (hc : IsPolynomialCurve b y) (G : kˣ →* BaseChange k d)
    (hG : ∀ t : kˣ, y t = G t • x.val) (a : ℕ) (ha : 0 < a)
    (hw : ∀ t, vertexCharacter d w (G t) = t ^ a) : f.val x = 0 := by
  obtain ⟨q,hq⟩ := f.property.1
  obtain ⟨p,hp⟩ := hc.pullback b q
  have he : Polynomial.X ^ a * p = Polynomial.C (f.val x) := by
    apply polynomial_identity_on_units
    intro t
    have hy : y t ∈ C := hG t ▸ oneParameter_mem_component b G C hC x.val x.property t
    have h := f.property.2 (G t) ⟨y t,hy⟩ x (by change x.val = _ • y t; rw [hG,inv_smul_smul])
    rw [hw, ← hq ⟨_,hy⟩, ← hp] at h
    simpa using h.symm
  have h := congrArg (Polynomial.eval (0 : k)) he
  simpa [zero_pow ha.ne'] using h.symm

variable [Module.Finite k R] [IsArtinianRing R] [IsNoetherianRing R] (P : SplitBasicVertices k R I)

theorem SplitBasicVertices.semistable_of_component_semiInvariant (g : ProjectiveClass R)
    {C : Set (VertexRepresentation (k := k) d P.vertex)}
    (hC : C ∈ @irreducibleComponents _ (zariski (d := d) (e := P.vertex) b))
    (x : C) (f : componentWeightSpace b C (P.characterExponents g)) (hf : f.val x ≠ 0) :
    (projectiveClassWeight k g).IsSemistable x.val.moduleObj := by
  apply P.semistable_of_block_weights x.val g
  · exact (P.eval_eq_total_character_weight g x.val).trans (component_total_weight_zero b x f hf)
  · intro U Q hQ hs
    let E (i : I) := (Submodule.prodEquivOfIsCompl (U i) (Q i) (hQ i)).symm
    by_contra! hn
    let n := ∑ i, (Module.finrank k (U i) : ℤ) * P.characterExponents g i
    have hp : 0 < n := hn
    apply hf
    apply vanishing_on_positive_degeneration b hC x f (blockCurve_polynomial b E x.val hs)
      (blockBaseChangeHom E) (blockCurve_at_unit E x.val hs) n.toNat (by omega)
    intro t
    change vertexCharacter d _ (blockBaseChange E t) = _
    rw [blockBaseChange_character,← zpow_natCast,Int.toNat_of_nonneg hp.le]

omit [Module.Finite k R] [IsArtinianRing R] [IsNoetherianRing R] in
include hC in
private theorem component_evaluation_of_degeneration {x y : X} (hx : x ∈ C)
    (h : WeightZeroDegeneration b w x y) :
    ∃ hy : y ∈ C, ∀ f : componentWeightSpace b C w, f.val ⟨y,hy⟩ = f.val ⟨x,hx⟩ := by
  obtain ⟨c,G,hc,hG,hw,rfl⟩ := h
  have hu (t : kˣ) : c t ∈ C := hG t ▸ oneParameter_mem_component b G C hC x hx t
  let := Z
  have h₀ := hc.special_mem b C (isClosed_of_mem_irreducibleComponents C hC) hu
  refine ⟨h₀,fun f ↦ ?_⟩
  obtain ⟨q,hq⟩ := f.property.1
  obtain ⟨p,hp⟩ := hc.pullback b q
  have he : p = Polynomial.C (f.val ⟨x,hx⟩) := by
    apply polynomial_identity_on_units
    intro t
    have h := f.property.2 (G t) ⟨c t,hu t⟩ ⟨x,hx⟩ (by change x = _ • c t; rw [hG,inv_smul_smul])
    rw [hw,Units.val_one,one_mul] at h
    simpa only [hp,Polynomial.eval_C] using (hq ⟨_,hu t⟩).trans h.symm
  exact (hq ⟨_,h₀⟩).symm.trans ((hp 0).symm.trans (by rw [he,Polynomial.eval_C]))

/-- The polystable limit stays in the prescribed component and has the same
values for every semi-invariant of the chosen character on that component. -/
theorem SplitBasicVertices.exists_polystable_on_component (g : ProjectiveClass R)
    {C : Set (VertexRepresentation (k := k) d P.vertex)}
    (hC : C ∈ @irreducibleComponents _ (zariski (d := d) (e := P.vertex) b))
    (x : C) (hx : (projectiveClassWeight k g).IsSemistable x.val.moduleObj) :
    ∃ y : C, (projectiveClassWeight k g).IsPolystable y.val.moduleObj ∧
      ∀ f : componentWeightSpace b C (P.characterExponents g), f.val y = f.val x := by
  obtain ⟨y,hy,h⟩ := P.exists_polystable_degeneration b g x.val hx
  suffices ∃ hmem : y ∈ C, ∀ f : componentWeightSpace b C (P.characterExponents g),
      f.val ⟨y,hmem⟩ = f.val x by
    obtain ⟨hmem,he⟩ := this
    exact ⟨⟨y,hmem⟩,hy,he⟩
  clear hy
  induction h with
  | refl => exact ⟨x.property,fun _ ↦ rfl⟩
  | tail _ h ih =>
    obtain ⟨hmem,he⟩ := ih
    obtain ⟨hmem',he'⟩ := component_evaluation_of_degeneration b hC hmem h
    exact ⟨hmem',fun f ↦ (he' f).trans (he f)⟩

/-- All semi-invariants of a fixed weight on an irreducible component of an
E-finite algebra are proportional, including when the ambient variety is reducible. -/
theorem SplitBasicVertices.rank_componentWeightSpace_le_one_of_isEFinite (hR : IsEFinite R)
    {C : Set (VertexRepresentation (k := k) d P.vertex)}
    (hC : C ∈ @irreducibleComponents _ (zariski (d := d) (e := P.vertex) b))
    (w : I → ℤ) : Module.rank k (componentWeightSpace b C w) ≤ 1 := by
  classical
  let g := ∑ j, w j • ProjectiveClass.of (P.vertexProjective j)
  have hg : P.characterExponents g = w := P.characterExponents_vertex_sum w
  rw [← hg]
  let F := componentWeightSpace b C (P.characterExponents g)
  apply (rank_le_one_iff (K := k) (V := F)).mpr
  by_cases hn : ∃ (q : F) (x : C), q.val x ≠ 0
  · obtain ⟨q,x,hq⟩ := hn
    obtain ⟨X',hX,hxe⟩ := P.exists_polystable_on_component b g hC x
      (P.semistable_of_component_semiInvariant b g hC x q hq)
    refine ⟨q,?_⟩
    intro f
    let a := f.val x / q.val x
    let v : F := f - a • q
    have hv : v.val x = 0 := by change f.val x - f.val x / q.val x * q.val x = 0; simp [hq]
    refine ⟨a,Subtype.ext (funext fun y ↦ ?_)⟩
    change a * q.val y = f.val y
    apply Eq.symm
    apply sub_eq_zero.mp
    change v.val y = 0
    by_contra hne
    obtain ⟨Y',hY,hye⟩ := P.exists_polystable_on_component b g hC y
      (P.semistable_of_component_semiInvariant b g hC y v hne)
    obtain ⟨i⟩ := (isEFinite_iff_unique_polystable_class k).1 hR g _ _ hX hY
      ((P.class_of_point X'.val).trans (P.class_of_point Y'.val).symm)
    obtain ⟨G,hG⟩ := MulAction.mem_orbit_iff.1 ((mem_orbit_iff X'.val Y'.val).2
      ((sameOrbit_iff_iso _ _).2 ⟨i⟩))
    have he := v.property.2 G Y' X' (by rw [← hG, inv_smul_smul])
    rw [hxe v,hye v,hv] at he
    exact hne ((mul_eq_zero.mp he.symm).resolve_left (Units.ne_zero _))
  · push Not at hn
    exact ⟨0,fun f ↦ ⟨0,Subtype.ext (funext fun x ↦ by simpa using (hn f x).symm)⟩⟩

end VertexRepresentation

/-- The multiplicity-free criterion in part (3) of the baseline proposition. -/
theorem isEFinite_iff_multiplicityFree (k R : Type u) [Field k] [IsAlgClosed k] [Ring R]
    [Algebra k R] [Module.Finite k R] :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    IsEFinite Rᵐᵒᵖ ↔ (basicPresentation k R).IsMultiplicityFree := by
  let P := basicPresentation k R
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  let := IsNoetherianRing.of_finite k P.Carrier
  let := IsArtinianRing.of_finite k P.Carrier
  exact ⟨fun h d C hC w ↦ P.vertices.rank_componentWeightSpace_le_one_of_isEFinite P.algebraBasis
    ((isEFinite_iff_of_module_equivalence k k P.equivalence).1 h) hC w,
    isEFinite_of_multiplicityFree k R⟩

/-- Weyman's corollary over an algebraically closed field of any characteristic. -/
theorem brick_discrete_iff_multiplicityFree (k R : Type u) [Field k] [IsAlgClosed k] [Ring R]
    [Algebra k R] [Module.Finite k R] :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    letI := IsArtinianRing.of_finite k Rᵐᵒᵖ
    (∀ d : simpleIsomorphismClasses Rᵐᵒᵖ → ℕ,
      (brickClassesOfClass (classOfCompositionVector k d)).Finite) ↔
        (basicPresentation k R).IsMultiplicityFree := by
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  exact (compositionVectorCriteria k R).1.symm.trans (isEFinite_iff_multiplicityFree k R)

end EFiniteCharacterizations
