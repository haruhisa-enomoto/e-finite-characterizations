module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # Factoring representations through a ground matrix image -/

@[expose] public section

namespace EFiniteCharacterizations

variable {k B T U : Type*} [CommSemiring k] [Ring B] [Ring T] [Ring U] [Algebra k B]

/-- The ground algebra structure on the ring image of a representation. -/
@[instance_reducible] def imageAlgebra (q : B →+* T) : Algebra k q.range :=
  (q.rangeRestrict.comp (algebraMap k B)).toAlgebra' fun c x ↦ by
    obtain ⟨b,rfl⟩ := q.rangeRestrict_surjective x
    simpa only [RingHom.comp_apply, map_mul] using congrArg q.rangeRestrict (Algebra.commutes c b)

/-- A specialization that satisfies all generic relations factors through
the ground algebra image. -/
theorem exists_image_factor (q : B →+* T) [Algebra k U] (ρ : B →ₐ[k] U)
    (h : ∀ a b, q a = q b → ρ a = ρ b) :
    letI := imageAlgebra (k := k) q
    ∃ p : q.range →ₐ[k] U, ∀ a, p (q.rangeRestrict a) = ρ a := by
  classical
  let := imageAlgebra (k := k) q
  choose s hs using q.rangeRestrict_surjective
  let p (x : q.range) := ρ (s x)
  have hp (a : B) : p (q.rangeRestrict a) = ρ a :=
    h _ _ (congrArg Subtype.val (hs _))
  refine ⟨{ toFun := p
            map_one' := (map_one q.rangeRestrict ▸ hp 1).trans (map_one ρ)
            map_zero' := (map_zero q.rangeRestrict ▸ hp 0).trans (map_zero ρ)
            map_add' := ?_
            map_mul' := ?_
            commutes' := fun c ↦ (hp (algebraMap k B c)).trans (ρ.commutes c) },hp⟩
  · intro x y
    obtain ⟨a,rfl⟩ := q.rangeRestrict_surjective x
    obtain ⟨b,rfl⟩ := q.rangeRestrict_surjective y
    rw [← map_mul, hp, hp, hp, map_mul]
  · intro x y
    obtain ⟨a,rfl⟩ := q.rangeRestrict_surjective x
    obtain ⟨b,rfl⟩ := q.rangeRestrict_surjective y
    rw [← map_add, hp, hp, hp, map_add]

end EFiniteCharacterizations
