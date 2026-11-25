module

public import EFiniteCharacterizations.Geometry.HomLoci
public import EFiniteCharacterizations.RingEpimorphisms.LocalizationModules

/-! # Finite subcovers by inversion loci on families of representations -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R]

/-- For a family of modules of one ground dimension, any cover by loci
inverting projective differentials already has a finite subcover. No topology
on the indexing set or rationality assumption on the points is needed. -/
theorem exists_finite_inversion_cover {X J : Type*} (M : X → FGModuleCat.{u} R)
    {d : ℕ} (hd : ∀ x, Module.finrank k ((M x).obj : Type u) = d) (P : J → TwoTerm R)
    (hc : ∀ x, ∃ j, (P j).InvertedOn (M x).obj) :
    ∃ t : Finset J, ∀ x, ∃ j ∈ t, (P j).InvertedOn (M x).obj := by
  classical
  let _ (x : X) : Module.Finite k ((M x).obj : Type u) := Module.Finite.trans R _
  let b := Module.finBasis k R
  let v x := (Module.finBasis k ((M x).obj : Type u)).reindex (finCongr (hd x))
  let c (x : X) (i : Fin (Module.finrank k R) × Fin d × Fin d) := actionMatrices b (v x) i.1 i.2.1 i.2.2
  let A (i : Fin (Module.finrank k R)) : Matrix (Fin d) (Fin d) (MvPolynomial (Fin (Module.finrank k R) × Fin d × Fin d) k) := Matrix.of fun (s t : Fin d) ↦ MvPolynomial.X (i,s,t)
  have hA x j : (A j).map (MvPolynomial.eval (c x)) = actionMatrices b (v x) j := by
    ext s t
    simp [A,c,Matrix.map_apply]
  let := coordinateZariski c
  let := coordinateZariski_noetherian c
  let U j := {x | (P j).InvertedOn (M x).obj}
  have ho j : IsOpen (U j) := by
    simp only [U, TwoTerm.invertedOn_iff_perpendicular k]
    exact (isOpen_hom_perpendiculars c M v b A hA _).1.inter
      (isOpen_hom_perpendiculars c M v b A hA _).2
  obtain ⟨t,ht⟩ := (NoetherianSpace.isCompact (Set.univ : Set X)).elim_finite_subcover U ho
    (fun x _ ↦ Set.mem_iUnion.mpr (hc x))
  refine ⟨t,fun x ↦ ?_⟩
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
  obtain ⟨hj,hu⟩ := Set.mem_iUnion.mp hj
  exact ⟨j,hj,hu⟩

/-- For an infinite stable family of fixed class, a pointwise choice of
inverting differential preserving stability yields one infinite stable chart. -/
theorem exists_infinite_fixed_class_chart_of_pointwise_inversion {J : Type*}
    (θ : Weight (FGModuleCat.{u} R)) (c : GrothendieckGroup (FGModuleCat.{u} R))
    (hi : (stableClassesOfClass θ c).Infinite) (P : J → TwoTerm R)
    (hs : ∀ j M, θ.IsStable M → ((P j).eulerWeight k).IsStable M)
    (hc : ∀ M, GrothendieckGroup.of M = c → θ.IsStable M → ∃ j, (P j).InvertedOn M.obj) :
    ∃ j, (((P j).stableInvertingClasses k) ∩ stableClassesOfClass θ c).Infinite := by
  classical
  let S := stableClassesOfClass θ c
  choose M hm he hstable using fun x : S ↦ x.property
  have hd (x : S) : Module.finrank k ((M x).obj : Type u) = (dimensionWeight (R := R) k c).toNat := by
    rw [← he x]
    change _ = ((dimensionWeight (R := R) k).eval (M x)).toNat
    simp
  obtain ⟨t,ht⟩ := exists_finite_inversion_cover k M hd P (fun x ↦ hc _ (he x) (hstable x))
  by_contra! hall
  apply hi
  apply (t.finite_toSet.biUnion (fun j _ ↦ hall j)).subset
  intro x hx
  let y : S := ⟨x,hx⟩
  obtain ⟨j,hj,hu⟩ := ht y
  exact Set.mem_iUnion₂.mpr ⟨j,hj,⟨M y,hm y,hs j _ (hstable y),hu⟩,hx⟩

/-- Dropping the fixed class condition gives an infinite stable chart. -/
theorem exists_infinite_stable_chart_of_pointwise_inversion {J : Type*}
    (θ : Weight (FGModuleCat.{u} R)) (c : GrothendieckGroup (FGModuleCat.{u} R))
    (hi : (stableClassesOfClass θ c).Infinite) (P : J → TwoTerm R)
    (hs : ∀ j M, θ.IsStable M → ((P j).eulerWeight k).IsStable M)
    (hc : ∀ M, GrothendieckGroup.of M = c → θ.IsStable M → ∃ j, (P j).InvertedOn M.obj) :
    ∃ j, ((P j).stableInvertingClasses k).Infinite := by
  obtain ⟨j,hj⟩ := exists_infinite_fixed_class_chart_of_pointwise_inversion k θ c hi P hs hc
  exact ⟨j,hj.mono Set.inter_subset_left⟩

end EFiniteCharacterizations
