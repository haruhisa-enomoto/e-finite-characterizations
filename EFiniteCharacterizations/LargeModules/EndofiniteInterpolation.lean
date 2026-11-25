module

public import EFiniteCharacterizations.LargeModules.EndofiniteCompactness

/-! # Interpolation by endomorphisms of an endofinite module -/

@[expose] public section

namespace EFiniteCharacterizations

variable {R : Type*} [Ring R] {N : ModuleCat R}

private def congruenceTest {ι : Type*} (x y : ι → N) (U : ι → Submodule (Module.End R N) N)
    (s : Finset ι) : AffineSubspace (Module.End R N) (N → N) where
  carrier := {v | ∃ e : Module.End R N, (∀ z, v z = e z) ∧ ∀ j ∈ s, e (x j) - y j ∈ U j}
  smul_vsub_vadd_mem' a := by
    rintro v w t ⟨p,hp,hp'⟩ ⟨q,hq,hq'⟩ ⟨r,hr,hr'⟩
    refine ⟨a.comp (p-q) + r,fun z ↦ ?_,fun j hj ↦ ?_⟩
    · change a (v z - w z) + t z = a (p z - q z) + r z
      rw [hp,hq,hr]
    · change a (p (x j) - q (x j)) + r (x j) - y j ∈ U j
      have hd := (U j).sub_mem (hp' j hj) (hq' j hj)
      rw [sub_sub_sub_cancel_right] at hd
      rw [add_sub_assoc]
      exact (U j).add_mem ((U j).smul_mem a hd) (hr' j hj)

/-- Finite systems of evaluation congruences modulo fully invariant additive
subgroups suffice to test whether all of them can be solved by one endomorphism. -/
theorem IsEndofinite.exists_endomorphism_of_finite_congruences (hN : IsEndofinite N)
    {ι : Type*} (x y : ι → N) (U : ι → Submodule (Module.End R N) N)
    (hf : ∀ s : Finset ι, ∃ e : Module.End R N, ∀ j ∈ s, e (x j) - y j ∈ U j) :
    ∃ e : Module.End R N, ∀ j, e (x j) - y j ∈ U j := by
  classical
  let : IsArtinian (Module.End R N) N := (isFiniteLength_iff_isNoetherian_isArtinian.mp hN).2
  let T := congruenceTest x y U
  have hfin (t : Finset (AffineSubspace (Module.End R N) (N → N)))
      (ht : (t : Set _) ⊆ Set.range T) : ∃ v, ∀ A ∈ t, v ∈ A := by
    choose s hs using fun A : t ↦ ht A.property
    obtain ⟨e,he⟩ := hf (Finset.univ.biUnion s)
    refine ⟨e,fun A hA ↦ ?_⟩
    rw [← show T (s ⟨A,hA⟩) = A from hs ⟨A,hA⟩]
    exact ⟨e,fun _ ↦ rfl,fun j hj ↦ he j (Finset.mem_biUnion.mpr ⟨⟨A,hA⟩,by simp,hj⟩)⟩
  obtain ⟨v,hv⟩ := exists_finite_agreement_of_artinian (Set.range T) hfin
  have approx (s : Finset ι) (d : Finset N) :
      ∃ e : Module.End R N, (∀ z ∈ d, v z = e z) ∧ ∀ j ∈ s, e (x j) - y j ∈ U j := by
    obtain ⟨w,⟨e,hw,he⟩,h⟩ := hv (T s) ⟨s,rfl⟩ d
    exact ⟨e,fun z hz ↦ (h z hz).symm.trans (hw z),he⟩
  let e : Module.End R N :=
    { toFun := v
      map_add' a b := by
        obtain ⟨f,h,_⟩ := approx ∅ {a,b,a+b}
        rw [h (a+b) (by simp),h a (by simp),h b (by simp), f.map_add]
      map_smul' r a := by
        obtain ⟨f,h,_⟩ := approx ∅ {a,r • a}
        rw [h (r • a) (by simp),h a (by simp), f.map_smul]
        rfl }
  refine ⟨e,fun j ↦ ?_⟩
  obtain ⟨f,h,hj⟩ := approx {j} {x j}
  change v (x j) - y j ∈ U j
  rw [h _ (by simp)]
  exact hj _ (by simp)

end EFiniteCharacterizations
