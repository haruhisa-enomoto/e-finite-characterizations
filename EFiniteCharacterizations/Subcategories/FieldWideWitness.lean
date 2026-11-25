module

public import EFiniteCharacterizations.Subcategories.BrickFiltrationDuality
public import EFiniteCharacterizations.Stability.FiniteCogeneratorWeights
public import Mathlib.FieldTheory.Finiteness

/-! # One stable brick with neither left nor right filtration approximations -/

@[expose] public section
open CategoryTheory Opposite
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

private theorem dual_ground_dimension (X : FGModuleCat.{u} R) :
    Module.finrank k (((Contragredient.dualityEquivalence k R).functor.obj (op X)).obj : Type u) =
      Module.finrank k (X.obj : Type u) := by
  have : Module.Finite k (X.obj : Type u) := Module.Finite.trans R _
  exact (Contragredient.forwardInnerDualEquiv k R X).finrank_eq.trans Subspace.dual_finrank_eq

private theorem dual_endolength [Finite k] (X : FGModuleCat.{u} R) :
    endolength k ((Contragredient.dualityEquivalence k R).functor.obj (op X)) = endolength k X := by
  let E := Contragredient.dualityEquivalence k R
  let B := E.functor.obj (op X)
  rw [endolength,endolength,dual_ground_dimension]
  congr 1
  rw [homFinrank_eq_finrank,homFinrank_eq_finrank]
  have := finiteModuleHom_isFinite k X X
  have := finiteModuleHom_isFinite k B B
  apply Nat.pow_right_injective (a := Nat.card k) Finite.one_lt_card
  change Nat.card k ^ Module.finrank k (B ⟶ B) = Nat.card k ^ Module.finrank k (X ⟶ X)
  rw [← Module.natCard_eq_pow_finrank,← Module.natCard_eq_pow_finrank]
  let e : (op X ⟶ op X) ≃ (B ⟶ B) := Equiv.ofBijective E.functor.map
    ⟨E.functor.map_injective,E.functor.map_surjective⟩
  exact Nat.card_congr (e.symm.trans (opEquiv (op X) (op X)))

variable [IsNoetherianRing R] [IsArtinianRing R]

private theorem finite_of_either_filtration_approximation {I : Type*}
    (X : I → FGModuleCat.{u} R) (θ : Weight (FGModuleCat.{u} R)) (hs : ∀ i, θ.IsStable (X i))
    (hiso : ∀ i j, i ≠ j → ¬ Nonempty (X i ≅ X j))
    (approx : ∀ i, CovariantlyFinite (FilteredBy (X i)) ∨ ContravariantlyFinite (FilteredBy (X i)))
    (d : ℕ) (size : (∀ i, Module.finrank k ((X i).obj : Type u) = d) ∨
      (Finite k ∧ ∀ i, endolength k (X i) = d)) : Finite I := by
  classical
  let S : Set I := {i | CovariantlyFinite (FilteredBy (X i))}
  have hS : S.Finite := by
    have hi (a b : S) (hne : a ≠ b) := hiso a.val b.val (fun eq ↦ hne (Subtype.ext eq))
    rcases size with hd | ⟨_,hd⟩
    · exact finite_covariantlyFinite_stable_of_dimension k (fun i : S ↦ X i.val) θ
        (fun i ↦ hs i.val) hi (fun i ↦ i.property) (fun i ↦ hd i.val)
    · exact finite_covariantlyFinite_stable_of_endolength k (fun i : S ↦ X i.val) θ
        (fun i ↦ hs i.val) hi (fun i ↦ i.property) (fun i ↦ hd i.val)
  apply hS.finite_of_compl
  let _ : IsNoetherianRing Rᵐᵒᵖ := isNoetherian_of_tower k inferInstance
  let _ : IsArtinianRing Rᵐᵒᵖ := isArtinian_of_tower k inferInstance
  let E := Contragredient.dualityEquivalence k R
  let D := E.symm.leftOp
  let Y (i : ↥(Sᶜ)) := E.functor.obj (op (X i.val))
  let ε (i : ↥(Sᶜ)) : D.functor.obj (op (Y i)) ≅ X i.val := (E.unitIso.app (op (X i.val))).unop
  have hY (i : ↥(Sᶜ)) : (dualWeight D θ).IsStable (Y i) := stable_dual D θ _ ((hs i.val).of_iso (ε i).symm)
  have hne (i j : ↥(Sᶜ)) (hn : i ≠ j) : ¬ Nonempty (Y i ≅ Y j) := by
    rintro ⟨e⟩
    exact hiso i.val j.val (fun eq ↦ hn (Subtype.ext eq)) ⟨(E.functor.preimageIso e).unop.symm⟩
  have hcov (i : ↥(Sᶜ)) : CovariantlyFinite (FilteredBy (Y i)) := by
    apply covariantlyFinite_filteredBy_of_dual D
    have eq : FilteredBy (D.functor.obj (op (Y i))) = FilteredBy (X i.val) := by
      funext M
      exact propext ⟨fun h ↦ h.of_iso (ε i) (Iso.refl M),fun h ↦ h.of_iso (ε i).symm (Iso.refl M)⟩
    rw [eq]
    exact (approx i.val).resolve_left i.property
  rcases size with hd | ⟨_,hd⟩
  · exact finite_covariantlyFinite_stable_of_dimension k Y _ hY hne hcov
      (fun i ↦ (dual_ground_dimension k (X i.val)).trans (hd i.val))
  · exact finite_covariantlyFinite_stable_of_endolength k Y _ hY hne hcov
      (fun i ↦ (dual_endolength k (X i.val)).trans (hd i.val))

/-- Over every field an E-infinite algebra has a stable brick at an integral
projective weight whose filtration category admits neither approximation property. -/
theorem exists_stable_brick_without_filtration_approximations (hn : ¬ IsEFinite R) :
    ∃ (g : ProjectiveClass R) (B : FGModuleCat.{u} R), (projectiveClassWeight k g).IsStable B ∧
      IsBrick B ∧ ¬ CovariantlyFinite (FilteredBy B) ∧ ¬ ContravariantlyFinite (FilteredBy B) := by
  classical
  by_contra! h
  have approx (g : ProjectiveClass R) (B : FGModuleCat.{u} R) (hs : (projectiveClassWeight k g).IsStable B) :
      CovariantlyFinite (FilteredBy B) ∨ ContravariantlyFinite (FilteredBy B) :=
    or_iff_not_imp_left.mpr (h g B hs hs.isBrick)
  rcases finite_or_infinite k with hf | hi
  · obtain ⟨g,r,_,hinf⟩ := exists_infinite_stableClassesOfEndolength_allFields k hn
    let S := stableClassesOfEndolength k (projectiveClassWeight k g) r
    choose X he hd hs using fun i : S ↦ i.property
    apply hinf
    exact finite_of_either_filtration_approximation k X _ hs (fun i j hn ⟨e⟩ ↦ hn (Subtype.ext
      ((he i).symm.trans ((congr_toSkeleton_of_iso e).trans (he j))))) (fun i ↦ approx g _ (hs i)) r (.inr ⟨hf,hd⟩)
  · obtain ⟨d,g,hinf⟩ := exists_infinite_stableClassesOfDimension_at_projectiveWeight_of_not_isEFinite k hn
    let S := stableClassesOfDimension k (projectiveClassWeight k g) d
    choose X he hd hs using fun i : S ↦ i.property
    apply hinf
    exact finite_of_either_filtration_approximation k X _ hs (fun i j hn ⟨e⟩ ↦ hn (Subtype.ext
      ((he i).symm.trans ((congr_toSkeleton_of_iso e).trans (he j))))) (fun i ↦ approx g _ (hs i)) d (.inl hd)

end EFiniteCharacterizations
