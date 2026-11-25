module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Full matrix span from a specialization -/

@[expose] public section

namespace EFiniteCharacterizations

open Module

private def vec {n : Type*} (L : Type*) [Field L] :
    Matrix n n L ≃ₗ[L] ((n × n) → L) where
  toFun := fun A i ↦ A i.1 i.2
  invFun := fun v ↦ Matrix.of fun i j ↦ v (i,j)
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl

/-- A family of matrices with full span at one field-valued specialization
has full span after an injective change of coefficients to a field. -/
theorem matrix_span_eq_top_of_specialization {D F K I n : Type*}
    [CommRing D] [Field F] [Field K] [Fintype n] [DecidableEq n]
    (e : D →+* F) (g : D →+* K) (hg : Function.Injective g)
    (M : I → Matrix n n D)
    (h : Submodule.span F (Set.range fun i ↦ (M i).map e) = ⊤) :
    Submodule.span K (Set.range fun i ↦ (M i).map g) = ⊤ := by
  classical
  let S := Set.range (fun i ↦ vec F ((M i).map e))
  have hS : Submodule.span F S = ⊤ := by
    rw [show S = (vec F) '' Set.range (fun i ↦ (M i).map e) from by
      ext x
      constructor
      · rintro ⟨i,rfl⟩
        exact ⟨_,⟨i,rfl⟩,rfl⟩
      · rintro ⟨y,⟨i,rfl⟩,rfl⟩
        exact ⟨i,rfl⟩]
    change Submodule.span F ((vec F).toLinearMap '' Set.range (fun i ↦ (M i).map e)) = ⊤
    rw [← Submodule.map_span (vec F).toLinearMap, h, Submodule.map_top, LinearEquiv.range]
  let b := Basis.ofSpan hS.ge
  let d := Pi.basisFun F (n × n)
  let b' := b.reindex (b.indexEquiv d)
  have hr (j : n × n) : b' j ∈ S := by
    apply Basis.ofSpan_subset hS.ge
    exact ⟨(b.indexEquiv d).symm j, (Basis.reindex_apply _ _ _).symm⟩
  choose a ha using hr
  let T : Matrix (n × n) (n × n) D := Matrix.of fun i j ↦ M (a j) i.1 i.2
  have hT : (T.map e).det ≠ 0 := by
    have hu : Function.Surjective (T.map e).mulVecLin := by
      rw [← LinearMap.range_eq_top, Matrix.range_mulVecLin]
      have hc : (T.map e).col = b' := by
        funext j
        exact ha j
      rw [hc,b'.span_eq]
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).1
      (Matrix.mulVec_surjective_iff_isUnit.1 hu))
  have hTg : (T.map g).det ≠ 0 := by
    intro hz
    have hh : g T.det = 0 := (RingHom.map_det g T).trans hz
    have ht : T.det = 0 := hg (hh.trans (map_zero g).symm)
    apply hT
    exact (RingHom.map_det e T).symm.trans (by rw [ht,map_zero])
  have huv : Submodule.span K (Set.range (T.map g).col) = ⊤ := by
    rw [← Matrix.range_mulVecLin, LinearMap.range_eq_top]
    exact Matrix.mulVec_surjective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.mpr hTg))
  apply top_unique
  have hv : (⊤ : Submodule K ((n × n) → K)) ≤
      (Submodule.span K (Set.range fun i ↦ (M i).map g)).map (vec K).toLinearMap := by
    rw [← huv, Submodule.map_span]
    apply Submodule.span_mono
    rintro x ⟨j,hj⟩
    exact ⟨_,⟨a j,rfl⟩,hj⟩
  intro x _
  obtain ⟨y,hy,hyx⟩ := hv (show vec K x ∈ (⊤ : Submodule K ((n × n) → K)) from trivial)
  exact (vec K).injective hyx ▸ hy

end EFiniteCharacterizations
