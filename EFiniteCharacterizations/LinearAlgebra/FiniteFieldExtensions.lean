module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Finite extensions of a specified degree -/

@[expose] public section

universe u

namespace EFiniteCharacterizations

/-- Every finite field has an extension of each positive degree, with the
corresponding power of the ground field's cardinality. -/
theorem exists_finiteFieldExtension (k : Type u) [Field k] [Finite k] (n : ℕ) (hn : 0 < n) :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra k F), Finite F ∧
      Module.finrank k F = n ∧ Nat.card F = Nat.card k ^ n := by
  classical
  let _ := Fintype.ofFinite k
  let p := ringChar k
  let _ : CharP k p := ringChar.charP k
  obtain ⟨e, hp, he⟩ := FiniteField.card k p
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Algebra (ZMod p) k := ZMod.algebra k p
  have hk : Module.finrank (ZMod p) k = (e : ℕ) := by
    apply Nat.pow_right_injective hp.two_le
    exact (FiniteField.pow_finrank_eq_card p k).trans he
  let F := ULift.{u, 0} (GaloisField p ((e : ℕ) * n))
  have hd : (e : ℕ) * n ≠ 0 := Nat.ne_of_gt (Nat.mul_pos e.pos hn)
  have hF : Module.finrank (ZMod p) F = (e : ℕ) * n :=
    (finrank_ulift (R := ZMod p)).trans (GaloisField.finrank p hd)
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod p) (K := k) (L := F) (by rw [hk, hF]; exact dvd_mul_right _ _)
  let _ : Algebra k F := f.toRingHom.toAlgebra
  let _ : IsScalarTower (ZMod p) k F := IsScalarTower.of_algebraMap_eq (fun c ↦ (f.commutes c).symm)
  have hdim := Module.finrank_mul_finrank (ZMod p) k F
  rw [hk, hF] at hdim
  have hn' : Module.finrank k F = n := Nat.eq_of_mul_eq_mul_left e.pos hdim
  exact ⟨F, inferInstance, inferInstance, inferInstance, hn', by rw [Module.natCard_eq_pow_finrank (K := k), hn']⟩

end EFiniteCharacterizations
