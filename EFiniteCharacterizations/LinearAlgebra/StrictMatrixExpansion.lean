module

public import EFiniteCharacterizations.LinearAlgebra.MatrixBlowup
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Strict expansion of a rectangular matrix space under algebraic extension -/

@[expose] public section
open Matrix Module
namespace EFiniteCharacterizations

variable {k E : Type*} [Field k] [Field E] [Algebra k E]
  {a n m : Type*} [Fintype n] [Fintype m]

private theorem subspacePair_of_submodules (D : a → Matrix m n k)
    (U : Submodule k (n → k)) (V : Submodule k (m → k))
    (h : ∀ i z, z ∈ U → (D i).mulVec z ∈ V) :
    HasMatrixSubspacePair D (finrank k U) (finrank k V) := by
  classical
  let u := Pi.basisFun k n
  let v := Pi.basisFun k m
  let bu := Module.finBasis k U
  let bv := Module.finBasis k V
  obtain ⟨l,hl⟩ := U.subtype.exists_leftInverse_of_injective U.ker_subtype
  obtain ⟨l',hl'⟩ := V.subtype.exists_leftInverse_of_injective V.ker_subtype
  let B i := ((D i).mulVecLin.comp U.subtype).codRestrict V (fun f ↦ h i f f.property)
  refine ⟨LinearMap.toMatrix bu u U.subtype,LinearMap.toMatrix bv v V.subtype,
    LinearMap.toMatrix u bu l,LinearMap.toMatrix v bv l',fun i ↦ LinearMap.toMatrix bu bv (B i),?_,?_,?_⟩
  · rw [← LinearMap.toMatrix_comp,hl,LinearMap.toMatrix_id]
  · rw [← LinearMap.toMatrix_comp,hl',LinearMap.toMatrix_id]
  · intro i
    have H : D i = LinearMap.toMatrix u v (D i).mulVecLin := by
      change D i = LinearMap.toMatrix' (Matrix.toLin' (D i))
      exact (LinearMap.toMatrix'_toLin' _).symm
    rw [H,← LinearMap.toMatrix_comp,← LinearMap.toMatrix_comp]
    rfl

private theorem map_dim_add_kernel {X Y : Type*} [AddCommGroup X] [Module k X]
    [FiniteDimensional k X] [AddCommGroup Y] [Module k Y] (f : X →ₗ[k] Y) (U : Submodule k X) :
    finrank k (U.map f) + finrank k (U ⊓ LinearMap.ker f : Submodule k X) = finrank k U := by
  let g := f.domRestrict U
  have eq : (LinearMap.ker g).map U.subtype = U ⊓ LinearMap.ker f := by
    ext x
    exact ⟨fun ⟨z,hz,hx⟩ ↦ hx ▸ ⟨z.property,hz⟩,fun ⟨hx,hf⟩ ↦ ⟨⟨x,hx⟩,hf,rfl⟩⟩
  rw [← LinearMap.range_domRestrict,← eq,← (Submodule.equivMapOfInjective U.subtype U.subtype_injective (LinearMap.ker g)).finrank_eq]
  exact g.finrank_range_add_finrank_ker

omit [Fintype m] in
private theorem coefficient_mulVec (l : E →ₗ[k] k) (D : Matrix m n k) (z : n → E) :
    l.compLeft m ((D.map (algebraMap k E)).mulVec z) = D.mulVec (l.compLeft n z) := by
  funext i
  change l (∑ j, algebraMap k E (D i j) * z j) = ∑ j, D i j * l (z j)
  simp only [← Algebra.smul_def,map_sum,map_smul,smul_eq_mul]

/-- Taking the image and kernel of a coordinate functional reduces a pair
over a finite extension to pairs of strictly smaller source dimension. -/
private theorem strict_expansion_on_restriction [Module.Finite k E] (D : a → Matrix m n k)
    (hD : ∀ r s, HasMatrixSubspacePair D r s → 0 < r → r < s)
    (U : Submodule k (n → E)) (V : Submodule k (m → E))
    (maps : ∀ i z, z ∈ U → ((D i).map (algebraMap k E)).mulVec z ∈ V) :
    0 < finrank k U → finrank k U < finrank k V := by
  classical
  generalize hd : finrank k U = d
  induction d using Nat.strong_induction_on generalizing U V with
  | h d ih =>
    intro hpos
    have hne : U ≠ ⊥ := by rintro rfl; simp at hd; omega
    obtain ⟨z,hz,hz'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨j,hj⟩ := Function.ne_iff.mp hz'
    obtain ⟨l,hl⟩ := Module.Projective.exists_dual_ne_zero k (show z j ≠ 0 from hj)
    let f := l.compLeft n
    let g := l.compLeft m
    have him : 0 < finrank k (U.map f) := Submodule.one_le_finrank_iff.mpr (by
      intro hbot
      have hz0 : f z ∈ (⊥ : Submodule k (n → k)) := hbot ▸ U.mem_map_of_mem hz
      exact hl (congrFun (show f z = 0 from hz0) j))
    have pair := subspacePair_of_submodules D (U.map f) (V.map g) (by
      rintro i _ ⟨z,hz,rfl⟩
      exact ⟨_,maps i z hz,coefficient_mulVec l (D i) z⟩)
    have himlt := hD _ _ pair him
    have h₁ := map_dim_add_kernel f U
    have h₂ := map_dim_add_kernel g V
    have kerle : finrank k (U ⊓ f.ker : Submodule k (n → E)) ≤ finrank k (V ⊓ g.ker : Submodule k (m → E)) := by
      by_cases hzero : finrank k (U ⊓ f.ker : Submodule k (n → E)) = 0
      · omega
      apply Nat.le_of_lt
      apply ih _ (by omega) _ _ _ rfl (Nat.pos_of_ne_zero hzero)
      intro i z hz
      refine ⟨maps i z hz.1,?_⟩
      change l.compLeft m _ = 0
      rw [coefficient_mulVec,show l.compLeft n z = 0 from hz.2,Matrix.mulVec_zero]
    omega

private theorem restricted_range_dimension [Module.Finite k E] {o : Type*} [Fintype o] {d : ℕ} (A : Matrix o (Fin d) E) (L : Matrix (Fin d) o E)
    (hL : L * A = 1) : finrank k (A.mulVecLin.range.restrictScalars k) = finrank k E * d := by
  have inj : Function.Injective A.mulVecLin := by
    intro x y eq
    have eq' := congrArg L.mulVec eq
    change L *ᵥ (A *ᵥ x) = L *ᵥ (A *ᵥ y) at eq'
    simpa only [Matrix.mulVec_mulVec,hL,Matrix.one_mulVec] using eq'
  have hd := LinearMap.finrank_range_of_inj (f := A.mulVecLin) inj
  rw [Module.finrank_pi,Fintype.card_fin] at hd
  exact (Module.finrank_mul_finrank k E A.mulVecLin.range).symm.trans (by rw [hd])

/-- A rectangular family strictly expanding every nonzero subspace keeps
this property over any algebraic extension of its coefficient field. -/
theorem strict_matrix_expansion_of_algebraic [Finite a] [Algebra.IsAlgebraic k E]
    (D : a → Matrix m n k) (hD : ∀ r s, HasMatrixSubspacePair D r s → 0 < r → r < s)
    {r s : ℕ} (h : HasMatrixSubspacePair (fun i ↦ (D i).map (algebraMap k E)) r s) (hr : 0 < r) :
    r < s := by
  classical
  obtain ⟨F,_,X,Y,LX,LY,B,hX,hY,hB⟩ := matrixSubspacePair_finite_model D r s h
  let U := X.mulVecLin.range
  let V := Y.mulVecLin.range
  have hu := restricted_range_dimension (k := k) X LX hX
  have hv := restricted_range_dimension (k := k) Y LY hY
  have hlt := strict_expansion_on_restriction D hD (U.restrictScalars k) (V.restrictScalars k) (by
    rintro i _ ⟨z,rfl⟩
    refine ⟨(B i).mulVec z,?_⟩
    change Y *ᵥ ((B i) *ᵥ z) = (D i).map _ *ᵥ (X *ᵥ z)
    rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hB]) (hu ▸ Nat.mul_pos Module.finrank_pos hr)
  change finrank k (X.mulVecLin.range.restrictScalars k) < finrank k (Y.mulVecLin.range.restrictScalars k) at hlt
  rw [hu,hv] at hlt
  exact Nat.lt_of_mul_lt_mul_left hlt

end EFiniteCharacterizations
