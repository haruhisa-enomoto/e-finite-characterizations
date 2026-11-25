module

public import EFiniteCharacterizations.ScalarExtension.GaloisStableHom
public import EFiniteCharacterizations.ScalarExtension.FieldWitnessCounting

/-! # At most one stable extension class for each Galois automorphism -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra TensorProduct

universe u
namespace EFiniteCharacterizations.FieldExtension

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R] [Module.Finite k F]
local notation "A" => ExtendedAlgebra k F R

/-- Two bijections to the same module with the same scalar twist give an
isomorphism over the extended algebra. -/
theorem iso_of_common_galoisHom {X Y Z : FGModuleCat.{u} A} {σ : Gal(F/k)}
    {f : restrictObj k F R X ⟶ restrictObj k F R Z} {g : restrictObj k F R Y ⟶ restrictObj k F R Z}
    (hf : IsGaloisHom k F R σ f) (hg : IsGaloisHom k F R σ g)
    (bf : Function.Bijective f.hom.hom) (bg : Function.Bijective g.hom.hom) : Nonempty (X ≅ Y) := by
  let e := (LinearEquiv.ofBijective f.hom.hom bf).trans (LinearEquiv.ofBijective g.hom.hom bg).symm
  have he (x : X) : g.hom.hom (e x) = f.hom.hom x := (LinearEquiv.ofBijective g.hom.hom bg).apply_symm_apply _
  have hc (c : F) (x : X) : e (scalarActionMap k F R X c x) = scalarActionMap k F R Y c (e x) := by
    apply bg.1
    exact (he _).trans ((hf c x).trans ((congrArg (scalarActionMap k F R Z (σ c)) (he x).symm).trans
      (hg c (e x)).symm))
  let l : X →ₗ[A] Y :=
    { e.toAddEquiv.toAddMonoidHom with
      map_smul' := fun a x ↦ by
        refine TensorProduct.inductionOn a ?_ ?_
        · intro c r
          have hx (M : FGModuleCat.{u} A) (y : M) : (c ⊗ₜ[k] r : A) • y =
              scalarActionMap k F R M c (r • (show restrictObj k F R M from y)) := by
            change _ = algebraMap F A c • algebraInclusion k F R r • y
            rw [← mul_smul]
            simp [algebraInclusion,Algebra.TensorProduct.tmul_mul_tmul]
          exact (congrArg e (hx X x)).trans ((hc c _).trans
            ((congrArg (scalarActionMap k F R Y c) (e.map_smul r x)).trans (hx Y (e x)).symm))
        · intro a d ha hd
          change e ((a+d) • x) = (a+d) • (show Y from e x)
          exact (congrArg e (add_smul a d x)).trans ((e.map_add _ _).trans
            ((congrArg₂ (· + ·) ha hd).trans (add_smul a d (show Y from e x)).symm)) }
  exact ⟨(LinearEquiv.ofBijective l e.bijective).toFGModuleCatIso⟩

variable [IsNoetherianRing R] [IsNoetherianRing (ExtendedAlgebra k F R)]

omit [IsNoetherianRing R] in
private theorem exists_nonzero_map_of_positive_powers {S : FGModuleCat.{u} R} (hn : ¬ IsZero S)
    {X Y : FGModuleCat.{u} R} {n m : ℕ} (hn' : 0 < n) (hm : 0 < m)
    (e : X ≅ FGModuleCat.of R (Fin n → S)) (e' : Y ≅ FGModuleCat.of R (Fin m → S)) :
    ∃ f : X ⟶ Y, f ≠ 0 := by
  let j : Fin n := ⟨0,hn'⟩
  let l : (Fin n → S) →ₗ[R] (Fin m → S) :=
    (LinearMap.pi fun _ ↦ LinearMap.proj j)
  let f : FGModuleCat.of R (Fin n → S) ⟶ FGModuleCat.of R (Fin m → S) := FGModuleCat.ofHom l
  refine ⟨e.hom ≫ f ≫ e'.inv,fun hz ↦ ?_⟩
  have he : f = 0 := by simpa using congrArg (fun a ↦ e.inv ≫ a ≫ e'.hom) hz
  apply hn
  apply (FGModuleCat.isZero_iff_subsingleton S).2
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  exact congrArg (fun a ↦ a.hom.hom (fun _ ↦ x) (⟨0,hm⟩ : Fin m)) he

/-- Pairwise distinct stable extension modules which descend to the same
ground stable witness have cardinality at most the extension degree. Each
module may use a different projective weight. -/
theorem card_le_degree_of_common_stable_witness [IsGalois k F] {I : Type*} [Fintype I]
    (P : I → TwoTerm R) (B : I → FGModuleCat.{u} A) (S : FGModuleCat.{u} R)
    (hs : ∀ i, ((P i).eulerWeight k).IsStable S)
    (hb : ∀ i, ((extendTwoTerm k F R (P i)).eulerWeight F).IsStable (B i))
    (hm : ∀ i, ∃ f : S ⟶ restrictObj k F R (B i), f ≠ 0)
    (hinj : Function.Injective (toSkeleton ∘ B)) : Fintype.card I ≤ Module.finrank k F := by
  classical
  by_cases hI : Nonempty I
  · let j := hI.some
    choose f hf using hm
    choose m hm _ e using fun i ↦ restrict_stable_is_power k F (P i) (hs i) (hb i) (f i) (hf i)
    let e' i := (e i).some
    have H (i : I) := exists_nonzero_map_of_positive_powers R (hs i).1 (hm i) (hm j) (e' i) (e' j)
    choose l hl using H
    choose σ v hv hσ using fun i ↦ exists_galoisHom k F R (l i) (hl i)
    have bij (i : I) : Function.Bijective (v i).hom.hom :=
      bijective_of_galoisHom k F R (hv i) (hσ i) (hb i) (hb j)
        (((hs j).isSemistable.finPower _).of_iso (e' i).symm)
        (((hs i).isSemistable.finPower _).of_iso (e' j).symm)
    have inj : Function.Injective σ := by
      intro i i' eq
      apply hinj
      obtain ⟨a⟩ := iso_of_common_galoisHom k F R (hσ i) (eq ▸ hσ i') (bij i) (bij i')
      exact congr_toSkeleton_of_iso a
    exact (Fintype.card_le_of_injective σ inj).trans_eq (by rw [← Nat.card_eq_fintype_card,IsGalois.card_aut_eq_finrank])
  · have : IsEmpty I := not_nonempty_iff.mp hI
    simp

/-- Restricting a finite family of distinct stable extension modules costs
at most the extension degree in cardinality, independently of the weights. -/
theorem exists_ground_witness_finset_galois [IsGalois k F] {I : Type*} [Fintype I]
    (P : I → TwoTerm R) (B : I → FGModuleCat.{u} A) (d : ℕ)
    (hB : Function.Injective (toSkeleton ∘ B))
    (hs : ∀ i, ((extendTwoTerm k F R (P i)).eulerWeight F).IsStable (B i))
    (hd : ∀ i, Module.finrank F ((B i).obj : Type u) ≤ d) :
    ∃ s : Finset (Skeleton (FGModuleCat.{u} R)), Fintype.card I ≤ Module.finrank k F * s.card ∧
      ∀ c ∈ s, ∃ (M : FGModuleCat.{u} R) (i : I), toSkeleton M = c ∧ ((P i).eulerWeight k).IsStable M ∧
        Module.finrank k (M.obj : Type u) ≤ Module.finrank k F * d ∧ endolength k M ≤ d := by
  classical
  choose G f hf hG hg hlen using fun i ↦ exists_bounded_stable_subobject_restrictObj k F R (P i) (B i) (hs i)
  let s := Finset.univ.image (toSkeleton ∘ G)
  refine ⟨s,?_,?_⟩
  · have hinto : Set.MapsTo (toSkeleton ∘ G) (Finset.univ : Finset I) s :=
      fun i _ ↦ Finset.mem_image_of_mem _ (Finset.mem_univ i)
    have bound (c : Skeleton (FGModuleCat.{u} R)) (_ : c ∈ s) :
        (Finset.univ.filter (fun i ↦ (toSkeleton ∘ G) i = c)).card ≤ Module.finrank k F := by
      let T := Finset.univ.filter (fun i ↦ (toSkeleton ∘ G) i = c)
      let M := (fromSkeleton _).obj c
      have e (i : T) : M ≅ G i.val := (fromSkeleton _).mapIso (eqToIso (Finset.mem_filter.mp i.property).2.symm) ≪≫
        fromSkeletonToSkeletonIso (G i.val)
      have inc (i : T) : ∃ h : M ⟶ restrictObj k F R (B i.val), h ≠ 0 := by
        refine ⟨(e i).hom ≫ f i.val,fun hz ↦ (hG i.val).1 ?_⟩
        have he : f i.val = 0 := by simpa using congrArg ((e i).inv ≫ ·) hz
        apply (IsZero.iff_id_eq_zero _).2
        let _ := hf i.val
        exact (cancel_mono (f i.val)).1 (by simp [he])
      have h := card_le_degree_of_common_stable_witness k F R (fun i : T ↦ P i.val) (fun i ↦ B i.val) M
        (fun i ↦ (hG i.val).of_iso (e i).symm) (fun i ↦ hs i.val) inc
        (fun a b eq ↦ Subtype.ext (hB eq))
      simpa only [Fintype.card_coe] using h
    simpa using Finset.card_le_mul_card_image_of_maps_to hinto _ bound
  · intro c hc
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hc
    exact ⟨G i,i,hi,hG i,(hg i).trans (Nat.mul_le_mul_left _ (hd i)),(hlen i).trans (hd i)⟩

end EFiniteCharacterizations.FieldExtension
