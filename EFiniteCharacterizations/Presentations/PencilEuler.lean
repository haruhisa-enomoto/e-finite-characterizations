module

public import EFiniteCharacterizations.Presentations.PencilHomDimensions

/-! # The Euler characteristic of the three-term complex of morphisms -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
universe u
namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [IsNoetherianRing R]
variable (P Q : TwoTerm R)

private noncomputable abbrev co (n : ℤ) := Cochain P.toCochainComplex Q.toCochainComplex n
private noncomputable abbrev bd (n m : ℤ) := δ_hom k P.toCochainComplex Q.toCochainComplex n m

private theorem dimension_step (l n m : ℤ) (hl : l + 1 = n) (hm : n + 1 = m)
    [Module.Finite k (co P Q n)] :
    Module.finrank k (P.inBoundedProjectives ⟶ Q.inBoundedProjectives⟦n⟧) +
      Module.finrank k (bd k P Q l n).range + Module.finrank k (bd k P Q n m).range =
      Module.finrank k (co P Q n) := by
  let D := bd k P Q n m
  let B := bd k P Q l n
  let F := HomotopyCategory.quotient (FGModuleCat.{u} R) (ComplexShape.up ℤ)
  let j := ((F.commShiftIso n).app Q.toCochainComplex).hom
  let z (x : D.ker) := Cocycle.mk x.val m hm x.property
  let t (x : D.ker) := F.map (Cocycle.equivHomShift.symm (z x)) ≫ j
  let φ : D.ker →ₗ[k] (P.homotopyObject ⟶ Q.homotopyObject⟦n⟧) :=
    { toFun := t
      map_add' := fun a b ↦ by
        have h : z (a+b) = z a + z b := Subtype.ext rfl
        simp [t,h,Preadditive.add_comp]
      map_smul' := fun a b ↦ by
        let g := a • 𝟙 P.toCochainComplex
        have h : z (a • b) = (z b).precomp g := by
          apply Subtype.ext
          ext i j hij
          simp [z,g,Cocycle.precomp,Cocycle.mk,Linear.smul_comp]
        simp [t,h,Cocycle.equivHomShift_symm_precomp,g,Functor.map_smul,Linear.smul_comp] }
  have hs : Function.Surjective φ := by
    intro f
    obtain ⟨v,hv⟩ := F.map_surjective (f ≫ inv j)
    let c := Cocycle.equivHomShift v
    refine ⟨⟨c.val,c.δ_eq_zero m⟩,?_⟩
    change F.map (Cocycle.equivHomShift.symm c) ≫ j = f
    simp [c,hv]
  have hk : ∀ x : D.ker, x ∈ φ.ker ↔ x.val ∈ B.range := by
    intro x
    change F.map (Cocycle.equivHomShift.symm (z x)) ≫ j = 0 ↔ _
    rw [← zero_comp (f := j),cancel_mono,← CohomologyClass.toHom_mk, CohomologyClass.toHom_mk_eq_zero_iff,mem_coboundaries_iff (z x) l hl]
    exact Iff.rfl
  let embed := D.ker.subtype.comp φ.ker.subtype
  have hi : Function.Injective embed := Subtype.val_injective.comp Subtype.val_injective
  have hr : embed.range = B.range := by
    ext x
    constructor
    · rintro ⟨v,rfl⟩
      exact (hk v.val).1 v.property
    · rintro hx
      obtain ⟨w,hw⟩ := hx
      have hd : B w ∈ D.ker := δ_δ _ _ _ w
      subst x
      exact ⟨⟨⟨_,hd⟩,(hk _).2 ⟨w,rfl⟩⟩,rfl⟩
  have he := (LinearEquiv.ofInjective embed hi).finrank_eq
  rw [hr] at he
  have h₁ := φ.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs,finrank_top] at h₁
  rw [(boundedShiftHomEquiv k P Q n).finrank_eq]
  have h₂ := D.finrank_range_add_finrank_ker
  rw [← h₂,← h₁,he]
  ac_rfl

private noncomputable def ev (n i j : ℤ) (h : i+n=j) :
    co P Q n →ₗ[k] (P.toCochainComplex.X i ⟶ Q.toCochainComplex.X j) where
  toFun x := x.v i j h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable abbrev sIso := doubleXIso₀ P.differential adjacent
private noncomputable abbrev tIso := doubleXIso₁ P.differential adjacent (by decide)

private noncomputable def extremeEquiv (n i j : ℤ) (h : i+n=j)
    (onlyTerm : ∀ a b : ℤ, a+n=b → a ≠ i →
      IsZero (P.toCochainComplex.X a) ∨ IsZero (Q.toCochainComplex.X b)) :
    co P Q n ≃ₗ[k] (P.toCochainComplex.X i ⟶ Q.toCochainComplex.X j) := by
  apply LinearEquiv.ofBijective (ev k P Q n i j h)
  constructor
  · intro x y he
    apply Cochain.ext
    intro a b hab
    by_cases ha : a=i
    · obtain rfl := ha
      obtain rfl : b=j := by omega
      exact he
    rcases onlyTerm a b hab ha with hz | hz
    · exact hz.eq_of_src _ _
    · exact hz.eq_of_tgt _ _
  · exact fun f ↦ ⟨Cochain.single f n,Cochain.single_v f _ h⟩

private noncomputable def bottomEquiv : co P Q (-1) ≃ₗ[k] (P.target ⟶ Q.source) :=
  (extremeEquiv k P Q (-1) 0 (-1) rfl (fun a b h hn ↦ by
    by_cases ha : a = -1
    · exact Or.inr (isZero_double_X _ adjacent b (by omega) (by omega))
    · exact Or.inl (isZero_double_X _ adjacent a ha hn))).trans
    (Linear.homCongr k (tIso P) (sIso Q))

private noncomputable def topEquiv : co P Q 1 ≃ₗ[k] (P.source ⟶ Q.target) :=
  (extremeEquiv k P Q 1 (-1) 0 rfl (fun a b h hn ↦ by
    by_cases ha : a = 0
    · exact Or.inr (isZero_double_X _ adjacent b (by omega) (by omega))
    · exact Or.inl (isZero_double_X _ adjacent a hn ha))).trans
    (Linear.homCongr k (sIso P) (tIso Q))

private noncomputable def middleEquiv :
    co P Q 0 ≃ₗ[k] ((P.source ⟶ Q.source) × (P.target ⟶ Q.target)) := by
  let f := (ev k P Q 0 (-1) (-1) rfl).prod (ev k P Q 0 0 0 rfl)
  have hi : Function.Injective f := by
    intro x y he
    apply Cochain.ext
    intro i j hij
    have hj : j=i := by omega
    subst j
    by_cases h : i = -1
    · obtain rfl := h; exact congrArg Prod.fst he
    by_cases h' : i = 0
    · obtain rfl := h'; exact congrArg Prod.snd he
    exact (isZero_double_X _ adjacent i h h').eq_of_src _ _
  have hs : Function.Surjective f := by
    rintro ⟨a,b⟩
    refine ⟨Cochain.single a 0 + Cochain.single b 0,Prod.ext ?_ ?_⟩
    · change (Cochain.single a 0 + Cochain.single b 0).v (-1) (-1) rfl = a
      simp [Cochain.single_v_eq_zero]
    · change (Cochain.single a 0 + Cochain.single b 0).v 0 0 rfl = b
      simp [Cochain.single_v_eq_zero]
  exact (LinearEquiv.ofBijective f ⟨hi,hs⟩).trans
    ((Linear.homCongr k (sIso P) (sIso Q)).prodCongr (Linear.homCongr k (tIso P) (tIso Q)))

include k in
/-- Euler characteristic of the Hom complex on two projective differentials. -/
theorem bounded_hom_euler [Module.Finite k R] :
    let h (n : ℤ) := (Module.finrank k (P.inBoundedProjectives ⟶ Q.inBoundedProjectives⟦n⟧) : ℤ)
    h 0 - h (-1) - h 1 =
      (Module.finrank k (P.source ⟶ Q.source) : ℤ) + Module.finrank k (P.target ⟶ Q.target) -
      Module.finrank k (P.target ⟶ Q.source) - Module.finrank k (P.source ⟶ Q.target) := by
  have (X Y : FGModuleCat.{u} R) : Module.Finite k (X ⟶ Y) := finiteModuleHom_isFinite k X Y
  have := Module.Finite.equiv (bottomEquiv k P Q).symm
  have := Module.Finite.equiv (middleEquiv k P Q).symm
  have := Module.Finite.equiv (topEquiv k P Q).symm
  have extreme (n : ℤ) (hn : n < -1 ∨ 1 < n) : Subsingleton (co P Q n) := by
    constructor
    intro x y
    apply Cochain.ext
    intro i j hij
    by_cases hi : i = -1 ∨ i = 0
    · exact (isZero_double_X _ adjacent j (by omega) (by omega)).eq_of_tgt _ _
    · exact (isZero_double_X _ adjacent i (by tauto) (by tauto)).eq_of_src _ _
  have := extreme (-2) (by decide)
  have := extreme 2 (by decide)
  have low := dimension_step k P Q (-2) (-1) 0 rfl rfl
  have mid := dimension_step k P Q (-1) 0 1 rfl rfl
  have high := dimension_step k P Q 0 1 2 rfl rfl
  have hz : bd k P Q (-2) (-1) = 0 := Subsingleton.elim _ _
  have hz' : bd k P Q 1 2 = 0 := Subsingleton.elim _ _
  rw [hz,LinearMap.range_zero,finrank_bot,(bottomEquiv k P Q).finrank_eq] at low
  rw [hz',LinearMap.range_zero,finrank_bot,(topEquiv k P Q).finrank_eq] at high
  rw [(middleEquiv k P Q).finrank_eq,Module.finrank_prod] at mid
  dsimp only
  omega

/-- On the fixed terms of a two-term presilting complex, any change of
differential weakly increases both Hom dimensions in every integer shift. -/
theorem pencil_hom_finrank_le [Module.Finite k R]
    {A B : FGModuleCat.{u} R} [Module.Projective R A] [Module.Projective R B]
    (u σ : A ⟶ B) (hu : (ofDifferential u).IsPresilting) (V : TwoTerm R) (n : ℤ) :
    let U := (ofDifferential u).inBoundedProjectives
    let S := (ofDifferential σ).inBoundedProjectives
    let W := V.inBoundedProjectives
    Module.finrank k (U ⟶ W⟦n⟧) ≤ Module.finrank k (S ⟶ W⟦n⟧) ∧
      Module.finrank k (W ⟶ U⟦n⟧) ≤ Module.finrank k (W ⟶ S⟦n⟧) := by
  by_cases hn : n = 0
  · subst n
    have low := pencil_hom_finrank_le_of_shift_ne_zero k u σ hu V (-1) (by decide)
    have high := pencil_hom_finrank_le_of_shift_ne_zero k u σ hu V 1 (by decide)
    have left := (bounded_hom_euler k (ofDifferential u) V).trans (bounded_hom_euler k (ofDifferential σ) V).symm
    have right := (bounded_hom_euler k V (ofDifferential u)).trans (bounded_hom_euler k V (ofDifferential σ)).symm
    dsimp only at *
    omega
  · exact pencil_hom_finrank_le_of_shift_ne_zero k u σ hu V n hn

end EFiniteCharacterizations.TwoTerm
