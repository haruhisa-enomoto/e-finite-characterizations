module

public import EFiniteCharacterizations.Stability.StableDeterminant
public import EFiniteCharacterizations.LinearAlgebra.RectangularBlockDescent

/-! # One-sided rank tests for numerical torsion pairs -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra Matrix
universe u v
namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R]

omit [Module.Finite k R] [IsNoetherianRing R] in
private theorem rank_trace {M T : FGModuleCat.{u} R} (i : T ⟶ M) [Mono i] (X : FGModuleCat.{u} R) :
    Module.finrank k (LinearMap.range (Linear.rightComp k X i)) = homFinrank k X T := by
  rw [homFinrank_eq_finrank]
  exact LinearMap.finrank_range_of_inj (fun _ _ h ↦ (cancel_mono i).mp h)

/-- Strict negativity on every nonzero subobject forces strict expansion of
each nonzero space of maps from the target projective. -/
theorem strict_expansion_of_subobject_neg (P : TwoTerm R) (M : FGModuleCat.{u} R)
    (neg : ∀ {T : FGModuleCat.{u} R} (i : T ⟶ M) [Mono i], ¬ IsZero T → (P.eulerWeight k).eval T < 0)
    (U : Submodule k (P.target ⟶ M)) (V : Submodule k (P.source ⟶ M))
    (h : ∀ (p : P.source ⟶ P.target) (f : U), p ≫ f.val ∈ V) (hu : 0 < Module.finrank k U) :
    Module.finrank k U < Module.finrank k V := by
  have := finiteModuleHom_isFinite k P.target M
  have := finiteModuleHom_isFinite k P.source M
  obtain ⟨T,i,hi,hU,hV⟩ := P.exists_trace_of_hom_subspace k M U V h
  have ha := Submodule.finrank_mono hU
  have hb := Submodule.finrank_mono hV
  rw [rank_trace] at ha hb
  have hn : ¬ IsZero T := by
    intro hz
    have ht := (homFinrank_eq_zero_iff k P.target T).2 (fun f ↦ hz.eq_of_tgt f 0)
    omega
  have ht := neg i hn
  rw [P.eulerWeight_eval k] at ht
  omega

omit [Module.Finite k R] [IsNoetherianRing R] in
/-- The annihilators of a subspace pair for the transpose family form a
subspace pair for the original Hom maps. -/
private theorem annihilators_of_transpose_pair (P : TwoTerm R) (M : FGModuleCat.{u} R)
    {a : Type*} {n m : Type v} [Fintype a] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (b : Module.Basis a k (P.source ⟶ P.target))
    (u : Module.Basis n k (P.target ⟶ M)) (v : Module.Basis m k (P.source ⟶ M))
    {r s : ℕ} (hp : HasMatrixSubspacePair
      (fun j ↦ (LinearMap.toMatrix u v (Linear.leftComp k M (b j))).transpose) r s) :
    ∃ (U : Submodule k (P.target ⟶ M)) (V : Submodule k (P.source ⟶ M)),
      Module.finrank k U + s = homFinrank k P.target M ∧
      Module.finrank k V + r = homFinrank k P.source M ∧
      ∀ (p : P.source ⟶ P.target) (f : U), p ≫ f.val ∈ V := by
  classical
  obtain ⟨X,Y,LX,LY,B,hX,hY,hB⟩ := hp
  let ψ := Y.transpose.mulVecLin.comp u.equivFun.toLinearMap
  let φ := X.transpose.mulVecLin.comp v.equivFun.toLinearMap
  have dim {l : Type v} {d : Type} [Fintype l] [Fintype d] {H : Type u} [AddCommGroup H] [Module k H]
      (e : H ≃ₗ[k] (l → k)) (A : Matrix l d k) (L : Matrix d l k) [DecidableEq d]
      (hl : L * A = 1) :
      Module.finrank k (A.transpose.mulVecLin.comp e.toLinearMap).ker + Fintype.card d = Module.finrank k H := by
    let f := A.transpose.mulVecLin.comp e.toLinearMap
    let := Module.Finite.equiv e.symm
    have hs : Function.Surjective f := by
      intro z
      refine ⟨e.symm (L.transpose.mulVec z),?_⟩
      change A.transpose.mulVec (e (e.symm _)) = z
      rw [e.apply_symm_apply,Matrix.mulVec_mulVec,← Matrix.transpose_mul,hl,Matrix.transpose_one,Matrix.one_mulVec]
    have he := f.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hs,finrank_top,Module.finrank_pi] at he
    exact (Nat.add_comm ..).trans he
  refine ⟨ψ.ker,φ.ker,?_,?_,?_⟩
  · simpa only [Fintype.card_fin,homFinrank_eq_finrank] using dim u.equivFun Y LY hY
  · simpa only [Fintype.card_fin,homFinrank_eq_finrank] using dim v.equivFun X LX hX
  intro p f
  rw [← b.sum_repr p,Preadditive.sum_comp]
  apply φ.ker.sum_mem
  intro j _
  rw [Linear.smul_comp]
  apply φ.ker.smul_mem
  change X.transpose.mulVec (v.equivFun (b j ≫ f.val)) = 0
  have hf : Y.transpose.mulVec (u.equivFun f.val) = 0 := f.property
  have he := congrArg Matrix.transpose (hB j)
  simp only [Matrix.transpose_mul,Matrix.transpose_transpose] at he
  have coords : (LinearMap.toMatrix u v (Linear.leftComp k M (b j))).mulVec (u.equivFun f.val) =
      v.equivFun (b j ≫ f.val) := LinearMap.toMatrix_mulVec_repr u v _ _
  rw [← coords,
    Matrix.mulVec_mulVec,he,← Matrix.mulVec_mulVec,hf,Matrix.mulVec_zero]

/-- Strict positivity on all nonzero quotients gives strict expansion of
the transpose Hom matrices on each nonzero source subspace. -/
private theorem transpose_expansion_of_quotient_pos (P : TwoTerm R) (M : FGModuleCat.{u} R)
    (pos : ∀ {Q : FGModuleCat.{u} R} (p : M ⟶ Q) [Epi p], ¬ IsZero Q → 0 < (P.eulerWeight k).eval Q)
    {a : Type*} {n m : Type v} [Fintype a] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (b : Module.Basis a k (P.source ⟶ P.target))
    (u : Module.Basis n k (P.target ⟶ M)) (v : Module.Basis m k (P.source ⟶ M))
    {r s : ℕ} (hp : HasMatrixSubspacePair
      (fun j ↦ (LinearMap.toMatrix u v (Linear.leftComp k M (b j))).transpose) r s)
    (hr : 0 < r) : r < s := by
  have := finiteModuleHom_isFinite k P.target M
  have := finiteModuleHom_isFinite k P.source M
  obtain ⟨U,V,hu,hv,h⟩ := annihilators_of_transpose_pair k P M b u v hp
  obtain ⟨T,i,hi,hU,hV⟩ := P.exists_trace_of_hom_subspace k M U V h
  have ha := Submodule.finrank_mono hU
  have hb := Submodule.finrank_mono hV
  rw [rank_trace] at ha hb
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hs : S.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i)
    (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
  have eq (Z : FGModuleCat.{u} R) [Module.Projective R Z] :
      homFinrank k Z M = homFinrank k Z T + homFinrank k Z (cokernel i) :=
    homFinrank_shortExact_of_projective k Z S hs
  have := P.projective_source
  have := P.projective_target
  have hsrc := eq P.source
  have htgt := eq P.target
  have hn : ¬ IsZero (cokernel i) := by
    intro hz
    have := (homFinrank_eq_zero_iff k P.source _).2 (fun f ↦ hz.eq_of_tgt f 0)
    omega
  have hpos := pos (cokernel.π i) hn
  rw [P.eulerWeight_eval k] at hpos
  omega

/-- For a module positive on its nonzero quotients and a module negative
on its nonzero subobjects, a common ground differential has the two required
Hom ranks. The class is a positive multiple of the original projective class. -/
theorem exists_block_precomposition_tests (P : TwoTerm R) (B M : FGModuleCat.{u} R)
    (pos : ∀ {Q : FGModuleCat.{u} R} (p : B ⟶ Q) [Epi p], ¬ IsZero Q → 0 < (P.eulerWeight k).eval Q)
    (neg : ∀ {U : FGModuleCat.{u} R} (i : U ⟶ M) [Mono i], ¬ IsZero U → (P.eulerWeight k).eval U < 0) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : TwoTerm R), Q.projectiveClass = n • P.projectiveClass ∧
      Function.Surjective (Q.precompose B) ∧ Function.Injective (Q.precompose M) := by
  classical
  have := finiteModuleHom_isFinite k P.source P.target
  have := finiteModuleHom_isFinite k P.source M
  have := finiteModuleHom_isFinite k P.target M
  have := finiteModuleHom_isFinite k P.source B
  have := finiteModuleHom_isFinite k P.target B
  let b := Module.finBasis k (P.source ⟶ P.target)
  let u := Module.finBasis k (P.target ⟶ M)
  let v := Module.finBasis k (P.source ⟶ M)
  let u' := Module.finBasis k (P.target ⟶ B)
  let v' := Module.finBasis k (P.source ⟶ B)
  let D j := LinearMap.toMatrix u v (Linear.leftComp k M (b j))
  let H j := LinearMap.toMatrix u' v' (Linear.leftComp k B (b j))
  obtain ⟨t,ht,x,hi,hs⟩ := exists_simultaneous_block_ranks D H (fun r s h hr ↦ by
    obtain ⟨U,V,hu,hv,hUV⟩ := hom_subspaces_of_matrix_pair k b u v r s h
    simpa only [hu,hv] using strict_expansion_of_subobject_neg k P M neg U V hUV (hu ▸ hr))
    (fun _ _ h hr ↦ transpose_expansion_of_quotient_pos k P B pos b u' v' h hr)
  let Q := P.blockDifferentialOnCopies (fun i j ↦ ∑ l, x (i,l,j) • b l)
  refine ⟨t,ht,Q,P.projectiveClass_blockDifferentialOnCopies _,?_,?_⟩
  · intro f
    obtain ⟨z,hz⟩ := hs (homCoordinates k v' t f)
    exact ⟨(homCoordinates k u' t).symm z,(homCoordinates k v' t).injective
      ((block_coordinates k t b u' v' x z).trans hz)⟩
  · intro f g hfg
    let e := homCoordinates k u t
    apply e.injective
    apply hi
    rw [← block_coordinates k t b u v x (e f),← block_coordinates k t b u v x (e g),
      show (homCoordinates k u t).symm (e f) = f from e.symm_apply_apply f,
      show (homCoordinates k u t).symm (e g) = g from e.symm_apply_apply g]
    exact congrArg (homCoordinates k v t) hfg

end EFiniteCharacterizations.TwoTerm
