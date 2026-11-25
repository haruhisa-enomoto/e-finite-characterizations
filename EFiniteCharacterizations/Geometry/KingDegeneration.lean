module

public import EFiniteCharacterizations.Geometry.KingEvaluation

/-! # Evaluation along one-parameter degenerations of vertex representations -/

@[expose] public section

universe u
namespace EFiniteCharacterizations.VertexRepresentation

variable {k R I J : Type u} [Field k] [Ring R] [Algebra k R]
    [Fintype I] [DecidableEq I] [Fintype J]
    (b : Module.Basis J k R) {d : I → ℕ} {e : I → R}

abbrev IsPolynomialCurve (y : k → VertexRepresentation (k := k) d e) : Prop :=
  ∀ j, ∃ p : Polynomial k, ∀ t, p.eval t = affineCoordinates b (y t) j

omit [Fintype J] in
theorem IsPolynomialCurve.pullback {y : k → VertexRepresentation (k := k) d e}
    (hy : IsPolynomialCurve b y) (f : coordinateAlgebra b d e) :
    ∃ p : Polynomial k, ∀ t, p.eval t = f.val (y t) := by
  choose v hv using hy
  obtain ⟨q,hq⟩ := f.property
  refine ⟨MvPolynomial.aeval v q, fun t ↦ ?_⟩
  let E := Pi.evalAlgHom k (fun _ : VertexRepresentation (k := k) d e ↦ k) (y t)
  change Polynomial.aeval t (MvPolynomial.aeval v q) = E f.val
  rw [← hq]
  change Polynomial.aeval t (MvPolynomial.aeval v q) = E (MvPolynomial.aeval (fun j ρ ↦ affineCoordinates b ρ j) q)
  rw [MvPolynomial.comp_aeval_apply,MvPolynomial.comp_aeval_apply]
  congr 2
  exact funext fun j ↦ hv j t

theorem polynomial_identity_on_units [Infinite k] {p q : Polynomial k}
    (h : ∀ t : kˣ, p.eval (t : k) = q.eval (t : k)) : p = q :=
  p.eq_of_infinite_eval_eq q ((Set.finite_singleton (0 : k)).infinite_compl.mono fun t ht ↦
    h (Units.mk0 t ht))

variable [Infinite k] (w : I → ℤ) (x : VertexRepresentation (k := k) d e)
    {y : k → VertexRepresentation (k := k) d e} (hy : IsPolynomialCurve b y)
    (G : kˣ → BaseChange k d) (hG : ∀ t : kˣ, y t = G t • x)

include hy hG in
/-- Along a degeneration with trivial character the homogeneous evaluations
on the special fibre are the same as on the original representation. -/
theorem eval_special_of_character_one (hχ : ∀ t, vertexCharacter d w (G t) = 1)
    (m : ℕ) (f : KingPiece b d e w m) : f.val.val (y 0) = f.val.val x := by
  obtain ⟨p,hp⟩ := hy.pullback b f.val
  have he : p = Polynomial.C (f.val.val x) := by
    apply polynomial_identity_on_units
    intro t
    have h := f.property (G t)⁻¹ x
    simpa [hp,hG,map_inv,hχ] using h
  simpa [he] using (hp 0).symm

include hy hG in
/-- A positive character exponent on a degeneration forces the vanishing
of every positive-degree semi-invariant at its general orbit. -/
theorem eval_zero_of_positive_character (a : ℕ) (ha : 0 < a)
    (hχ : ∀ t, vertexCharacter d w (G t) = t ^ a)
    (m : ℕ) (hm : 0 < m) (f : KingPiece b d e w m) : f.val.val x = 0 := by
  obtain ⟨p,hp⟩ := hy.pullback b f.val
  have he : Polynomial.X ^ (a*m) * p = Polynomial.C (f.val.val x) := by
    apply polynomial_identity_on_units
    intro t
    have h := f.property (G t) (y t)
    rw [hG,inv_smul_smul,hχ] at h
    simpa [hp, hG, pow_mul] using h.symm
  have h := congrArg (Polynomial.eval (0 : k)) he
  simpa [zero_pow (Nat.mul_pos ha hm).ne'] using h.symm

/-- Simultaneous scalar base change at every vertex. -/
def centralBaseChange (t : kˣ) : BaseChange k d := fun _ ↦ LinearEquiv.smulOfUnit t

omit [Fintype I] [Infinite k] in
theorem centralBaseChange_fixes (t : kˣ) : centralBaseChange (d := d) t • x = x := by
  let F := LinearEquiv.piCongrRight (centralBaseChange (d := d) t)
  apply Subtype.ext
  apply AlgHom.ext
  intro r
  apply LinearMap.ext
  intro z
  obtain ⟨v,rfl⟩ := F.surjective z
  change F (x.val r (F.symm (F v))) = x.val r (F v)
  rw [F.symm_apply_apply]
  exact ((x.val r).map_smul (t : k) v).symm

omit [Infinite k] in
theorem centralBaseChange_character (t : kˣ) :
    vertexCharacter d w (centralBaseChange t) = t ^ (∑ i, (d i : ℤ) * w i) := by
  have hd (i : I) : LinearEquiv.det (centralBaseChange (d := d) t i) = t ^ d i := by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    change LinearMap.det ((t : k) • (LinearMap.id : (Fin (d i) → k) →ₗ[k] _)) = _
    simp [LinearMap.det_smul]
  change ∏ i, (LinearEquiv.det (centralBaseChange (d := d) t i)) ^ w i = _
  simp only [hd]
  generalize (Finset.univ : Finset I) = S
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => simp [hi,ih,zpow_add,zpow_mul]

/-- Nonvanishing of a positive-degree form forces total numerical weight zero. -/
theorem total_character_weight_zero (m : ℕ) (hm : 0 < m) (f : KingPiece b d e w m)
    (hf : f.val.val x ≠ 0) : ∑ i, (d i : ℤ) * w i = 0 := by
  let n := ∑ i, (d i : ℤ) * w i
  have hy : IsPolynomialCurve b (fun _ ↦ x) := fun j ↦ ⟨Polynomial.C _,fun t ↦ Polynomial.eval_C⟩
  change n = 0
  rcases lt_trichotomy n 0 with hn | hn | hn
  · let G (t : kˣ) := centralBaseChange (d := d) t⁻¹
    apply False.elim (hf _)
    exact eval_zero_of_positive_character b w x hy G (fun t ↦ (centralBaseChange_fixes x t⁻¹).symm)
      (-n).toNat (by omega) (fun t ↦ by
        change vertexCharacter d w (centralBaseChange t⁻¹) = _
        rw [centralBaseChange_character]
        change t⁻¹ ^ n = _
        rw [inv_zpow, ← zpow_neg, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]) m hm f
  · exact hn
  · apply False.elim (hf _)
    exact eval_zero_of_positive_character b w x hy centralBaseChange (fun t ↦ (centralBaseChange_fixes x t).symm)
      n.toNat (by omega) (fun t ↦ by
        rw [centralBaseChange_character, ← zpow_natCast, Int.toNat_of_nonneg hn.le]) m hm f

namespace SplitBasicVertices

variable [Module.Finite k R] [IsNoetherianRing R] [IsArtinianRing R] (P : SplitBasicVertices k R I)
    (g : ProjectiveClass R) (ρ : VertexRepresentation (k := k) d P.vertex)

omit [Infinite k] in
theorem eval_eq_total_character_weight :
    (projectiveClassWeight k g).eval ρ.moduleObj = ∑ i, (d i : ℤ) * P.characterExponents g i := by
  classical
  let := (finite_simpleIsomorphismClasses (R := R) k).fintype
  rw [Weight.eval, P.class_of_point ρ, classOfCompositionVector, map_sum]
  simp only [map_nsmul, nsmul_eq_mul, Function.comp_apply]
  simpa [characterExponents,Weight.eval] using P.simpleIndex.sum_comp
    (fun i ↦ (d i : ℤ) * P.characterExponents g i)

/-- The numerical equality in King's semistability condition follows from
a single nonzero homogeneous evaluation in positive degree. -/
theorem eval_zero_of_nonvanishing_semiInvariant (m : ℕ) (hm : 0 < m)
    (f : KingPiece b d P.vertex (P.characterExponents g) m) (hf : f.val.val ρ ≠ 0) :
    (projectiveClassWeight k g).eval ρ.moduleObj = 0 :=
  (P.eval_eq_total_character_weight g ρ).trans (total_character_weight_zero b _ ρ m hm f hf)

end SplitBasicVertices

end EFiniteCharacterizations.VertexRepresentation
