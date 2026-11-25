module

public import EFiniteCharacterizations.Algebra.MatrixSandwichOperators
public import EFiniteCharacterizations.DivisionRings.CoefficientSeparation
public import EFiniteCharacterizations.RingEpimorphisms.RingEpimorphism

/-! # Epicity of the matrix image over its coefficient field -/

@[expose] public section

universe u
namespace EFiniteCharacterizations

variable {B K : Type u} {n : Type} {ι : Type*} [Ring B] [Field K] [Fintype n]
    [DecidableEq n] [Nonempty n] [Fintype ι] (q : B →+* Matrix n n K)
    (b : Module.Basis ι K (Matrix n n K)) (hb : Set.range b ⊆ Set.range q)

local notation "L" => matrixCoefficientField q b
local notation "H" => matrixImageAlgebra q b

include hb

/-- Agreement on the matrix image forces agreement on the generated coefficient
field, and hence on its entire span. -/
theorem toMatrixImageAlgebra_epi : IsRingEpimorphism (toMatrixImageAlgebra q b) := by
  classical
  intro T _ f g h
  let β := matrixImageBasis q b hb
  let Q := toMatrixImageAlgebra q b
  have him (x : B) : f (Q x) = g (Q x) := RingHom.congr_fun h x
  have hβ (i : ι) : f (β i) = g (β i) := by
    obtain ⟨x,hx⟩ := hb ⟨i,rfl⟩
    have he : Q x = β i := Subtype.ext (hx.trans (matrixImageBasis_apply q b hb i).symm)
    simpa only [he] using him x
  choose v hv using matrixImage_separating_multipliers q b hb
  let a := algebraMap L H
  have expand (x : H) : ∑ i, a (β.repr x i) * β i = x := by
    simpa only [a, ← Algebra.smul_def] using β.sum_repr x
  have hc (x : B) := ringHom_agree_on_separated_coefficients f g β
    (fun i ↦ a (β.repr (Q x) i)) (fun (_ : ι) (p : ι × ι) ↦ β p.1) v hβ (fun _ p ↦ hβ p.1)
    (fun i _ p ↦ (Algebra.commutes (β.repr (Q x) i) (β p.1)).symm) hv (by rw [expand]; exact him x)
  let U := (f.comp a).eqLocusField (g.comp a)
  have hL : L ≤ U.map (matrixCoefficientField q b).subtype := by
    apply Subfield.closure_le.mpr
    rintro _ ⟨⟨x,i⟩,rfl⟩
    exact ⟨β.repr (Q x) i, hc x i, matrixImageBasis_repr q b hb (Q x) i⟩
  have ha (t : L) : f (a t) = g (a t) := by
    obtain ⟨s,hs,he⟩ := hL t.property
    exact (Subtype.ext he : s = t) ▸ hs
  apply RingHom.ext
  intro x
  rw [← expand x, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_mul, map_mul, ha, hβ]

end EFiniteCharacterizations
