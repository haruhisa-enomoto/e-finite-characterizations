module

public import EFiniteCharacterizations.LinearAlgebra.PolynomialMinor
public import EFiniteCharacterizations.Stability.StableDeterminant
public import EFiniteCharacterizations.Subcategories.WideSubcategories
public import EFiniteCharacterizations.Subcategories.WideSimpleSupport
public import EFiniteCharacterizations.Stability.SemistableSimples
public import EFiniteCharacterizations.RingEpimorphisms.LocalizationExtensions

/-!
# Determinantal criterion for numerical semistability

Proposition 2.5(2) (`prop:known-baseline`, after King and Schofield/Derksen–Fei):
over an algebraically closed field, a finite-dimensional module `M` is semistable at
an integral weight `g ∈ K₀(proj R)` if and only if some positive multiple `t g` is
represented by a differential `Q` such that `Hom_R(Q.differential, M)` is an
isomorphism (`semistable_iff_exists_inverting_multiple`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Module
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k]

private theorem polynomial_of_invertible_member {ι T V W : Type*} [Fintype ι]
    [AddCommGroup T] [Module k T] [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] (b : Basis ι k T) (Φ : T →ₗ[k] V →ₗ[k] W)
    {p : T} (hp : Function.Bijective (Φ p)) :
    ∃ D : MvPolynomial ι k, D ≠ 0 ∧ ∀ q, MvPolynomial.eval (b.repr q) D ≠ 0 →
      Function.Bijective (Φ q) := by
  classical
  let e := LinearEquiv.ofBijective (Φ p) hp
  let Ψ : T →ₗ[k] V →ₗ[k] V := (e.symm.toLinearMap.compRight k).comp Φ
  let v := Module.finBasis k V
  let D := polynomialMinor b Ψ v v.coord
  have test (q : T) : MvPolynomial.eval (b.repr q) D ≠ 0 ↔ Function.Bijective (Φ q) := by
    rw [eval_polynomialMinor]
    rw [show (Matrix.of fun i j ↦ v.coord i (Ψ q (v j))) = LinearMap.toMatrix v v (Ψ q) by
      ext i j; simp [LinearMap.toMatrix_apply, Basis.coord_apply]]
    rw [LinearMap.det_toMatrix,← isUnit_iff_ne_zero,← LinearMap.isUnit_iff_isUnit_det,
      Module.End.isUnit_iff]
    exact Equiv.comp_bijective (Φ q) e.symm.toEquiv
  refine ⟨D,fun hz ↦ (test p).2 hp (by rw [hz,map_zero]), fun q ↦ (test q).1⟩

variable {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R] [IsNoetherianRing R]

omit [Module.Finite k R] [IsNoetherianRing R] in
private theorem invertedOn_iff_bijective (P : TwoTerm R) (M : FGModuleCat.{u} R) :
    P.InvertedOn M.obj ↔ Function.Bijective (Linear.leftComp k M P.differential) := by
  let e (A : FGModuleCat.{u} R) : (A ⟶ M) ≃ (A.obj ⟶ M.obj) := InducedCategory.homEquiv
  exact ⟨fun h ↦ (e _).symm.bijective.comp (h.comp (e _).bijective),
    fun h ↦ (e _).bijective.comp (h.comp (e _).symm.bijective)⟩

omit [IsNoetherianRing R] in
private theorem simultaneous_inversion [Infinite k] (P : TwoTerm R) (A B : FGModuleCat.{u} R)
    {p q : P.source ⟶ P.target} (hp : ({P with differential := p}).InvertedOn A.obj)
    (hq : ({P with differential := q}).InvertedOn B.obj) :
    ∃ f : P.source ⟶ P.target, ({P with differential := f}).InvertedOn A.obj ∧
      ({P with differential := f}).InvertedOn B.obj := by
  classical
  have := finiteModuleHom_isFinite k P.source P.target
  let b := Module.finBasis k (P.source ⟶ P.target)
  have det (M : FGModuleCat.{u} R) {f : P.source ⟶ P.target}
      (hf : ({P with differential := f}).InvertedOn M.obj) :
      ∃ D : MvPolynomial _ k, D ≠ 0 ∧ ∀ q, MvPolynomial.eval (b.repr q) D ≠ 0 →
        ({P with differential := q}).InvertedOn M.obj := by
    have := finiteModuleHom_isFinite k P.target M
    obtain ⟨D,hd,h⟩ := polynomial_of_invertible_member k b (Linear.comp (S := k) P.source P.target M)
      ((invertedOn_iff_bijective k {P with differential := f} M).1 hf)
    exact ⟨D,hd,fun q hq ↦ (invertedOn_iff_bijective k {P with differential := q} M).2 (h q hq)⟩
  obtain ⟨D,hd,hA⟩ := det A hp
  obtain ⟨E,he,hB⟩ := det B hq
  obtain ⟨x,hx⟩ : ∃ x, MvPolynomial.eval x (D * E) ≠ 0 := by
    by_contra! h
    exact mul_ne_zero hd he (MvPolynomial.funext (fun x ↦ (h x).trans (map_zero _).symm))
  rw [map_mul] at hx
  let f := b.equivFun.symm x
  have hf : ⇑(b.repr f) = x := b.equivFun.apply_symm_apply _
  exact ⟨f,hA f (hf ▸ left_ne_zero_of_mul hx),hB f (hf ▸ right_ne_zero_of_mul hx)⟩

private noncomputable abbrev blockTerms (P : TwoTerm R) (t : ℕ) := P.blockDifferentialOnCopies (t := t) 0

/-- All sufficiently large multiples of the prescribed terms admit an
inverting differential for a semistable module. -/
theorem exists_inverting_differential_of_semistable [IsAlgClosed k] (P : TwoTerm R)
    (M : FGModuleCat.{u} R) (hs : (P.eulerWeight k).IsSemistable M) :
    ∃ m : ℕ, ∀ t ≥ m, let Q := P.blockDifferentialOnCopies (t := t) 0
      ∃ f : Q.source ⟶ Q.target, ({Q with differential := f}).InvertedOn M.obj := by
  let := IsArtinianRing.of_finite k R
  let θ := P.eulerWeight k
  let W : ObjectProperty (FGModuleCat.{u} R) := θ.IsSemistable
  let Test (N : FGModuleCat.{u} R) := ∃ m : ℕ, ∀ t ≥ m,
    ∃ f : (blockTerms P t).source ⟶ (blockTerms P t).target,
      ({blockTerms P t with differential := f}).InvertedOn N.obj
  change Test M
  refine θ.isWideClass_semistable.extension_induction Test ?_ ?_ hs
  · intro N hz
    refine ⟨0,fun t _ ↦ ⟨0,(invertedOn_iff_bijective k _ N).2 ?_⟩⟩
    exact ⟨fun _ _ _ ↦ hz.eq_of_tgt _ _,fun _ ↦ ⟨0,hz.eq_of_tgt _ _⟩⟩
  · intro S hS hsimple _ ih
    let _ : Fact (IsWideClass W) := ⟨θ.isWideClass_semistable⟩
    have hstable := (θ.isStable_iff_simple ⟨_,hsimple.1⟩).2
      ((IsWideClass.simple_iff_simpleMember (W := W) _).2 hsimple)
    obtain ⟨m,hm⟩ := ih
    let n := (homFinrank k P.target S.X₁)^2
    refine ⟨max (n+1) m,?_⟩
    intro t ht
    obtain ⟨p,hp⟩ := P.exists_inverting_power_of_stable k S.X₁ hstable t
      (lt_of_lt_of_le (Nat.lt_succ_self n) ((le_max_left _ _).trans ht))
    obtain ⟨q,hq⟩ := hm t ((le_max_right _ _).trans ht)
    obtain ⟨f,hf,hf'⟩ := simultaneous_inversion k (blockTerms P t) S.X₁ S.X₃
      (p := (P.blockDifferentialOnCopies p).differential) hp hq
    let F := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
    exact ⟨f,({blockTerms P t with differential := f}).invertedOn_extension
      (S.map F) (hS.map_of_exact F) hf hf'⟩

private theorem semistable_of_invertedOn (P : TwoTerm R) (M : FGModuleCat.{u} R) (h : P.InvertedOn M.obj) :
    (P.eulerWeight k).IsSemistable M := by
  have hb := (invertedOn_iff_bijective k P M).1 h
  constructor
  · rw [P.eulerWeight_eval k,homFinrank_eq_finrank,homFinrank_eq_finrank,sub_eq_zero]
    exact_mod_cast (LinearEquiv.ofBijective _ hb).finrank_eq
  · intro U i hi
    have := finiteModuleHom_isFinite k P.source U
    have hj : Function.Injective (Linear.leftComp k U P.differential) := by
      intro a b hab
      apply (cancel_mono i).1
      apply hb.1
      change P.differential ≫ a ≫ i = P.differential ≫ b ≫ i
      change P.differential ≫ a = P.differential ≫ b at hab
      simpa only [← Category.assoc] using congrArg (· ≫ i) hab
    rw [P.eulerWeight_eval k,homFinrank_eq_finrank,homFinrank_eq_finrank,sub_nonpos]
    exact_mod_cast LinearMap.finrank_le_finrank_of_injective hj

/-- The determinantal criterion for an arbitrary integral weight and an arbitrary
semistable module over an algebraically closed field. -/
theorem semistable_iff_exists_inverting_multiple [IsAlgClosed k] (g : ProjectiveClass R)
    (M : FGModuleCat.{u} R) : (projectiveClassWeight k g).IsSemistable M ↔
      ∃ (t : ℕ) (_ : 0 < t) (Q : TwoTerm R), Q.projectiveClass = t • g ∧ Q.InvertedOn M.obj := by
  constructor
  · intro hs
    obtain ⟨P,rfl⟩ := g.exists_twoTerm
    rw [P.projectiveClassWeight_eq_eulerWeight k] at hs
    obtain ⟨m,hm⟩ := P.exists_inverting_differential_of_semistable k M hs
    obtain ⟨f,hf⟩ := hm (m+1) (Nat.le_succ _)
    exact ⟨m+1,Nat.succ_pos _,{blockTerms P (m+1) with differential := f},(P.projectiveClass_blockDifferentialOnCopies (t := m+1) 0),hf⟩
  · rintro ⟨t,ht,Q,hg,hi⟩
    have hs := semistable_of_invertedOn k Q M hi
    rw [← Q.projectiveClassWeight_eq_eulerWeight k,hg,map_nsmul] at hs
    have ht' : (0 : ℤ) < t := by exact_mod_cast ht
    simp only [Weight.IsSemistable,Weight.eval,AddMonoidHom.nsmul_apply,nsmul_eq_mul,
      mul_eq_zero,ht'.ne',false_or] at hs
    exact ⟨hs.1,fun i _ ↦ nonpos_of_mul_nonpos_right (hs.2 i) ht'⟩

end EFiniteCharacterizations.TwoTerm
