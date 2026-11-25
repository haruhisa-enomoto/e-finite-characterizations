module

public import EFiniteCharacterizations.Characterizations.HomCharacterizations
public import EFiniteCharacterizations.Subcategories.OrthogonalApproximations

/-! # Integral weights separating finite families in a torsion pair -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

open FamilyExtraction in
/-- Equal-class Hom strictly separates two finite families of nonzero modules
when every map from the first family to the second vanishes. -/
theorem exists_weight_separating_orthogonal {I J : Type*} [Fintype I] [Fintype J]
    (h : EqualClassHom (FGModuleCat.{u} R)) (X : I → FGModuleCat.{u} R) (Y : J → FGModuleCat.{u} R)
    (hx : ∀ i, ¬ IsZero (X i)) (hy : ∀ j, ¬ IsZero (Y j)) (ho : ∀ i j (f : X i ⟶ Y j), f = 0) :
    ∃ g : ProjectiveClass R, (∀ i, 0 < (projectiveClassWeight k g).eval (X i)) ∧
      ∀ j, (projectiveClassWeight k g).eval (Y j) < 0 := by
  classical
  obtain ⟨n, q, hq⟩ := exists_injective_projective_weight_coordinates (R := R) k
  let rows := Sum.elim (fun i ↦ -GrothendieckGroup.of (X i)) (fun j ↦ GrothendieckGroup.of (Y j))
  rcases Farkas.integral_separation_of_injective_coordinates (fun t ↦ projectiveClassWeight k (q t)) hq
    (fun _ : Empty ↦ 0) rows with ⟨w, _, hw⟩ | ⟨a, _, ha, hp, he⟩
  · refine ⟨∑ t, w t • q t, fun i ↦ ?_, fun j ↦ ?_⟩
    · simpa only [Weight.eval, map_sum, map_zsmul, rows, Sum.elim_inl, map_neg, neg_lt_zero] using hw (.inl i)
    · simpa only [Weight.eval, map_sum, map_zsmul, rows, Sum.elim_inr] using hw (.inr j)
  · exfalso
    let l (i : I) := (a (.inl i)).toNat
    let r (j : J) := (a (.inr j)).toNat
    apply Relation.not_equalClassHom (L := weightedFamily X l) (M := weightedFamily Y r) _ h
    constructor
    · rw [totalClass_weightedFamily, totalClass_weightedFamily]
      simp only [Fintype.sum_sum_type, rows, Sum.elim_inl, Sum.elim_inr, smul_neg, Finset.sum_neg_distrib,
        Finset.univ_eq_empty, Finset.sum_empty] at he
      simp only [← natCast_zsmul, l, r, Int.toNat_of_nonneg (ha _)]
      exact (neg_add_eq_zero.mp he)
    · have hex : ∃ i, 0 < a i := by
        by_contra! hn
        exact hp.not_ge (Finset.sum_nonpos fun i _ ↦ hn i)
      obtain ⟨i | j, hp⟩ := hex
      · exact Or.inl ⟨_, mem_weightedFamily.mpr ⟨i, by dsimp [l]; omega, rfl⟩, hx i⟩
      · exact Or.inr ⟨_, mem_weightedFamily.mpr ⟨j, by dsimp [r]; omega, rfl⟩, hy j⟩
    · rintro A hA B hB f
      obtain ⟨i, _, rfl⟩ := mem_weightedFamily.mp hA
      obtain ⟨j, _, rfl⟩ := mem_weightedFamily.mp hB
      exact ho i j f

def nonzeroQuotientClasses (M : FGModuleCat.{u} R) : Set (GrothendieckGroup (FGModuleCat.{u} R)) :=
  {z | ∃ (Q : FGModuleCat.{u} R) (q : M ⟶ Q), Epi q ∧ ¬ IsZero Q ∧ GrothendieckGroup.of Q = z}

private def subClasses (N : FGModuleCat.{u} R) : Set (GrothendieckGroup (FGModuleCat.{u} R)) :=
  {z | ∃ (U : FGModuleCat.{u} R) (i : U ⟶ N), Mono i ∧ ¬ IsZero U ∧ GrothendieckGroup.of U = z}

/-- All nonzero quotients of the first family and all nonzero subobjects of the
second family can be separated simultaneously. -/
theorem exists_weight_separating_quotients_subobjects {I J : Type*} [Finite I] [Finite J]
    (h : EqualClassHom (FGModuleCat.{u} R)) (M : I → FGModuleCat.{u} R) (N : J → FGModuleCat.{u} R)
    (ho : ∀ i j (f : M i ⟶ N j), f = 0) :
    ∃ g : ProjectiveClass R, (∀ i, (projectiveClassWeight k g).strictTorsionClass (M i)) ∧
      ∀ j, ∀ {U : FGModuleCat.{u} R} (a : U ⟶ N j) [Mono a], ¬ IsZero U → (projectiveClassWeight k g).eval U < 0 := by
  classical
  let L := ⋃ i, nonzeroQuotientClasses (M i)
  let H := ⋃ j, subClasses (N j)
  have hL : L.Finite := Set.finite_iUnion fun i ↦
    (finite_classes_of_groundFinrank_le (R := R) k (Module.finrank k ((M i).obj : Type u))).subset (by
      rintro _ ⟨Q,q,hq,_,rfl⟩
      exact ⟨Q, groundFinrank_le_of_epi k q, rfl⟩)
  have hH : H.Finite := Set.finite_iUnion fun j ↦
    (finite_classes_of_groundFinrank_le (R := R) k (Module.finrank k ((N j).obj : Type u))).subset (by
      rintro _ ⟨U,i,hi,_,rfl⟩
      have : Module.Finite k ((N j).obj : Type u) := Module.Finite.trans R _
      exact ⟨U, LinearMap.finrank_le_finrank_of_injective (f := i.hom.hom.restrictScalars k)
        ((FGModuleCat.mono_iff_injective i).1 hi), rfl⟩)
  let := hL.fintype
  let := hH.fintype
  choose a Q p hp hQ he using fun i : L ↦ Set.mem_iUnion.mp i.property
  choose b U t ht hU hf using fun j : H ↦ Set.mem_iUnion.mp j.property
  obtain ⟨g, hg, hg'⟩ := exists_weight_separating_orthogonal k h Q U hQ hU (by
    intro i j f
    apply (cancel_epi (p i)).1
    apply (cancel_mono (t j)).1
    simpa only [Category.assoc, zero_comp, comp_zero] using ho (a i) (b j) (p i ≫ f ≫ t j))
  refine ⟨g, fun i V v hv hn ↦ ?_, fun j W w hw hn ↦ ?_⟩
  · let x : L := ⟨_, Set.mem_iUnion.mpr ⟨i,V,v,hv,hn,rfl⟩⟩
    unfold Weight.eval
    exact (show GrothendieckGroup.of (Q x) = GrothendieckGroup.of V from he x) ▸ hg x
  · let x : H := ⟨_, Set.mem_iUnion.mpr ⟨j,W,w,hw,hn,rfl⟩⟩
    unfold Weight.eval
    exact (show GrothendieckGroup.of (U x) = GrothendieckGroup.of W from hf x) ▸ hg' x

end EFiniteCharacterizations
