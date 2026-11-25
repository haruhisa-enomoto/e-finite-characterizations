module

public import EFiniteCharacterizations.ScalarExtension.FieldEndolength
public import EFiniteCharacterizations.ScalarExtension.FieldWitnessFibres
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Counting ground witnesses from a finite family over an extension -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u v w

namespace EFiniteCharacterizations.FieldExtension

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R] [Module.Finite k F] [IsNoetherianRing R]
  [IsNoetherianRing (ExtendedAlgebra k F R)]

local notation "R₊" => ExtendedAlgebra k F R

/-- A finite family of distinct stable extension classes at a fixed list
of weights gives a family of stable ground classes. The loss in count is
bounded by the size of the list and the restricted dimension bound. -/
theorem exists_ground_witness_finset
    {I : Type v} [Fintype I] {J : Type w} [Fintype J]
    (P : J → TwoTerm R) (tag : I → J) (B : I → FGModuleCat.{u} R₊) (d : ℕ)
    (hB : Function.Injective (toSkeleton ∘ B))
    (hs : ∀ x, ((extendTwoTerm k F R (P (tag x))).eulerWeight F).IsStable (B x))
    (hd : ∀ x, Module.finrank F ((B x).obj : Type u) ≤ d) :
    ∃ s : Finset (Skeleton (FGModuleCat.{u} R)),
      Fintype.card I ≤ (Module.finrank k F * d) * (Fintype.card J * s.card) ∧
      ∀ c ∈ s, ∃ (M : FGModuleCat.{u} R) (j : J), toSkeleton M = c ∧ ((P j).eulerWeight k).IsStable M ∧
        Module.finrank k (M.obj : Type u) ≤ Module.finrank k F * d ∧ endolength k M ≤ d := by
  classical
  choose G i hmono hG hGdim hGendo using fun x ↦
    exists_bounded_stable_subobject_restrictObj k F R (P (tag x)) (B x) (hs x)
  let S := Finset.univ.image (fun x ↦ toSkeleton (G x))
  let f (x : I) := (tag x, toSkeleton (G x))
  refine ⟨S, ?_, ?_⟩
  · have hinto (x : I) (_ : x ∈ Finset.univ) : f x ∈ (Finset.univ : Finset J).product S :=
      Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    have hbound (b : J × Skeleton (FGModuleCat.{u} R)) (_ : b ∈ (Finset.univ : Finset J).product S) :
        (Finset.univ.filter (fun x : I ↦ f x = b)).card ≤ Module.finrank k F * d := by
      let C := Finset.univ.filter (fun x : I ↦ f x = b)
      change C.card ≤ _
      by_cases he : C.Nonempty
      · obtain ⟨x₀, hx₀⟩ := he
        have he₀ := (Finset.mem_filter.mp hx₀).2
        have ht₀ : tag x₀ = b.1 := congrArg Prod.fst he₀
        have hW : ((P b.1).eulerWeight k).IsSemistable (G x₀) := by
          rw [← ht₀]
          exact (hG x₀).isSemistable
        let T := stableExtensionClassesOver k F R (P b.1) (G x₀)
        obtain ⟨hfin, hcard⟩ := finite_and_ncard_stableExtensionClassesOver k F R (P b.1) (G x₀) hW
        have hmap : Set.MapsTo (toSkeleton ∘ B) (C : Set I) hfin.toFinset := by
          intro x hx
          have hx' := (Finset.mem_filter.mp hx).2
          have hxTag : tag x = b.1 := congrArg Prod.fst hx'
          have heq : toSkeleton (G x₀) = toSkeleton (G x) :=
            (congrArg Prod.snd he₀).trans (congrArg Prod.snd hx').symm
          let w := Skeleton.isoOfEq heq
          let z := (fromSkeletonToSkeletonIso (B x)).symm
          let a : restrictObj k F R (B x) ≅
              restrictObj k F R ((fromSkeleton _).obj (toSkeleton (B x))) :=
            (restrict k F R).mapIso z
          let v : G x₀ ⟶ restrictObj k F R ((fromSkeleton _).obj (toSkeleton (B x))) :=
            w.hom ≫ i x ≫ a.hom
          let _ := hmono x
          have hv : v ≠ 0 := by
            intro hz
            apply (hG x₀).1
            apply (IsZero.iff_id_eq_zero _).2
            have hv' : Mono v := mono_comp w.hom (i x ≫ a.hom)
            exact (cancel_mono v).1 (by rw [Category.id_comp, hz, zero_comp])
          apply hfin.mem_toFinset.2
          refine ⟨?_, v, hv⟩
          rw [← hxTag]
          exact (hs x).of_iso z
        calc
          C.card ≤ hfin.toFinset.card := Finset.card_le_card_of_injOn _ hmap hB.injOn
          _ = T.ncard := (Set.ncard_eq_toFinset_card T hfin).symm
          _ ≤ Module.finrank k ((G x₀).obj : Type u) := hcard
          _ ≤ Module.finrank k F * d := (hGdim x₀).trans (Nat.mul_le_mul_left _ (hd x₀))
      · simp [Finset.not_nonempty_iff_eq_empty.mp he]
    have ht : ((Finset.univ : Finset J).product S).card = Fintype.card J * S.card :=
      Finset.card_product _ _
    have h := Finset.card_le_mul_card_image_of_maps_to hinto _ hbound
    rw [Finset.card_univ, ht] at h
    exact h
  · intro c hc
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hc
    exact ⟨G x, tag x, hx, hG x, (hGdim x).trans (Nat.mul_le_mul_left _ (hd x)), (hGendo x).trans (hd x)⟩

end EFiniteCharacterizations.FieldExtension
