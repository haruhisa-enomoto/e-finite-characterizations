module

public import EFiniteCharacterizations.LinearAlgebra.PolynomialMinor
public import EFiniteCharacterizations.LinearAlgebra.TensorBilinear
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Kernel-to-image inclusion at a point of maximum geometric rank

Lemma 2.6 (`lem:rank-lemma`) of the manuscript: if a `k`-linear family
`Φ : T → Hom_k(V, W)` attains its maximum rank over `k̄` at a ground point `p ∈ T`,
then `Φ(q)(ker Φ(p)) ⊆ im Φ(p)` for every `q ∈ T`
(`map_ker_le_range_of_maximal_geometric_rank`).
-/

@[expose] public section
open Module
open scoped TensorProduct

namespace EFiniteCharacterizations

variable {k T V W : Type*} [Field k] [AddCommGroup T] [Module k T]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [Module.Finite k W]

private theorem exists_probes_at_rank (f : V →ₗ[k] W) :
    ∃ (v : Fin (finrank k (LinearMap.range f)) → V) (l : Fin (finrank k (LinearMap.range f)) → Dual k W),
      (Matrix.of fun i j ↦ l i (f (v j))).det ≠ 0 := by
  classical
  let B := Module.finBasis k (LinearMap.range f)
  choose v hv using fun j ↦ (B j).property
  choose l hl using fun i ↦ (B.coord i).exists_extend
  refine ⟨v,l,?_⟩
  have he : (Matrix.of fun i j ↦ l i (f (v j))) = 1 := by
    ext i j
    change l i (f (v j)) = _
    rw [hv j]
    change ((l i).comp (LinearMap.range f).subtype) (B j) = _
    rw [hl i]
    by_cases h : i = j <;> simp [Basis.coord_apply,Matrix.one_apply,Finsupp.single_apply,h,eq_comm]
  simp [he]

private theorem rank_ge_of_polynomialMinor_ne_zero {ι : Type*} [Fintype ι]
    (F : Type*) [Field F] [Algebra k F] [Infinite F]
    (b : Basis ι k T) (Φ : T →ₗ[k] V →ₗ[k] W) {n : ℕ}
    (v : Fin n → V) (l : Fin n → Dual k W) (hn : polynomialMinor b Φ v l ≠ 0) :
    ∃ q : F ⊗[k] T, n ≤ finrank F (LinearMap.range (baseChangeBilinear F Φ q)) := by
  classical
  let D := polynomialMinor b Φ v l
  obtain ⟨x,hx⟩ : ∃ x : ι → F, MvPolynomial.eval₂Hom (algebraMap k F) x D ≠ 0 := by
    by_contra! h
    apply hn
    apply MvPolynomial.map_injective (algebraMap k F) (algebraMap k F).injective
    apply MvPolynomial.funext
    intro x
    simp only [map_zero,MvPolynomial.eval_map]
    exact h x
  let q : F ⊗[k] T := ∑ t, x t ⊗ₜ[k] b t
  let f := baseChangeBilinear F Φ q
  let w (j : Fin n) : LinearMap.range f := ⟨f (1 ⊗ₜ[k] v j),_,rfl⟩
  let L (i : Fin n) := (((Algebra.linearMap k F).comp (l i)).liftBaseChange F).comp (LinearMap.range f).subtype
  have he (i j : Fin n) : L i (w j) = ∑ t, algebraMap k F (l i (Φ (b t) (v j))) * x t := by
    simp only [L,w,f,q,LinearMap.comp_apply,Submodule.subtype_apply,map_sum,
      LinearMap.sum_apply,baseChangeBilinear_tmul,mul_one,LinearMap.liftBaseChange_tmul,
      Algebra.linearMap_apply,smul_eq_mul,mul_comm]
  have hd : (Matrix.of fun i j ↦ L i (w j)).det ≠ 0 := by
    change MvPolynomial.eval₂Hom (algebraMap k F) x (polynomialMinor b Φ v l) ≠ 0 at hx
    simpa only [he, eval₂_polynomialMinor] using hx
  have hi : LinearIndependent F w :=
    LinearIndependent.of_comp (LinearMap.pi L) (Matrix.linearIndependent_cols_of_det_ne_zero hd)
  have : Module.Finite F (F ⊗[k] W) := Module.Finite.of_basis ((Module.finBasis k W).baseChange F)
  exact ⟨q,by simpa using hi.fintype_card_le_finrank⟩

/-- If the rank at a ground point bounds every rank after extension to an infinite
field, each direction carries its kernel into its image. -/
theorem map_ker_le_range_of_maximal_extended_rank [Module.Finite k T]
    (F : Type*) [Field F] [Algebra k F] [Infinite F] (Φ : T →ₗ[k] V →ₗ[k] W) (p : T)
    (hmax : ∀ q : F ⊗[k] T,
      finrank F (LinearMap.range (baseChangeBilinear F Φ q)) ≤ finrank k (LinearMap.range (Φ p))) (h : T) :
    (LinearMap.ker (Φ p)).map (Φ h) ≤ LinearMap.range (Φ p) := by
  rintro _ ⟨u,hu,rfl⟩
  by_contra hout
  let b := Module.finBasis k T
  obtain ⟨v,l,hd⟩ := exists_probes_at_rank (Φ p)
  obtain ⟨_,v',l',hn⟩ := exists_larger_polynomialMinor b Φ (LinearMap.mem_ker.mp hu) hout hd
  obtain ⟨q,hq⟩ := rank_ge_of_polynomialMinor_ne_zero F b Φ v' l' hn
  exact (Nat.not_succ_le_self _) (hq.trans (hmax q))

/-- At a point of maximum rank over the algebraic closure, every member of a
linear family takes the kernel at that point into the image at that point. -/
theorem map_ker_le_range_of_maximal_geometric_rank [Module.Finite k T]
    (Φ : T →ₗ[k] V →ₗ[k] W) (p : T) (hmax : ∀ q : AlgebraicClosure k ⊗[k] T,
      finrank (AlgebraicClosure k) (LinearMap.range (baseChangeBilinear (AlgebraicClosure k) Φ q)) ≤
        finrank k (LinearMap.range (Φ p))) (h : T) :
    (LinearMap.ker (Φ p)).map (Φ h) ≤ LinearMap.range (Φ p) :=
  map_ker_le_range_of_maximal_extended_rank (AlgebraicClosure k) Φ p hmax h

end EFiniteCharacterizations
