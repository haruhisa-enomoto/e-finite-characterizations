module

public import EFiniteCharacterizations.Silting.ThickSubcategories.PencilJet
public import EFiniteCharacterizations.Silting.ThickSubcategories.ThickReduction
public import EFiniteCharacterizations.Presentations.StableAdd

/-! # Presilting representatives in two-term thick subcategories -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
open CochainComplex.HomComplex
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R] [IsNoetherianRing R]

set_option backward.isDefEq.respectTransparency false in
theorem isZero_contractible (S : FiniteProjective R) : IsZero (contractible S).homotopyObject := by
  let K := (contractible S).toCochainComplex
  let h := (doubleXIso₁ (𝟙 S.val) adjacent (by decide)).hom ≫ (doubleXIso₀ (𝟙 S.val) adjacent).inv
  let z : Cochain K K (-1) := Cochain.single h (-1)
  apply (HomotopyCategory.isZero_quotient_obj_iff _).2
  refine ⟨(Cochain.equivHomotopy _ _).symm ⟨z, ?_⟩⟩
  rw [Cochain.ofHom_zero, add_zero]
  apply Cochain.ext
  intro i j hij
  have hj : j = i := by omega
  subst j
  by_cases hm : i = -1
  · subst i
    change 𝟙 _ = (δ (-1) 0 z).v (-1) (-1) rfl
    rw [δ_v (-1) 0 rfl z (-1) (-1) rfl (-2) 0 rfl rfl]
    simp [z, h, K, Cochain.single_v_eq_zero, contractible, double_d _ adjacent (by decide)]
  by_cases h₀ : i = 0
  · subst i
    change 𝟙 _ = (δ (-1) 0 z).v 0 0 rfl
    rw [δ_v (-1) 0 rfl z 0 0 rfl (-1) 1 rfl rfl]
    simp [z, h, K, Cochain.single_v_eq_zero, contractible, double_d _ adjacent (by decide)]
  exact (isZero_double_X (𝟙 S.val) adjacent i hm h₀).eq_of_src _ _

omit [IsNoetherianRing R] in
theorem projective_jet_terms (P : FGModuleCat.{u} R) (hp : Module.Projective R P) (n : ℕ) :
    Module.Projective R (PencilJet.terms (C := FGModuleCat.{u} R) P n) := by
  induction n with
  | zero => exact hp
  | succ n ih => exact FGModuleCat.projective_biprod (PencilJet.terms P n) P

/-- The jet with n+1 copies of P as its successive factors. -/
noncomputable def jet (P : TwoTerm R) (v : P.source ⟶ P.target) (n : ℕ) : TwoTerm R :=
  ⟨_, _, projective_jet_terms P.source P.projective_source n,
    projective_jet_terms P.target P.projective_target n, PencilJet.differential P.differential v n⟩

theorem mem_jet {H : TwoTerm R → Prop} (hT : TwoOutOfThree H) (P : TwoTerm R) (hP : H P)
    (v : P.source ⟶ P.target) (n : ℕ) : H (jet P v n) := by
  induction n with
  | zero => exact hP
  | succ n ih =>
    let w := v ≫ PencilJet.head P.target n
    exact ((hT (jet P v n) ((jet P v n).blockExtension P w) P _ _ _ (blockTriangle_distinguished (jet P v n) P w)).1 ih).2 hP

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
/-- On fixed terms, a rigid differential lies in every two-term thick
subcategory containing the special fiber. -/
theorem mem_rigid_on_terms {H : TwoTerm R → Prop} (hT : TwoOutOfThree H)
    (hR : ∀ (A B : TwoTerm R), Retract A.homotopyObject B.homotopyObject → H B → H A)
    (P : TwoTerm R) (hP : H P) (u : P.source ⟶ P.target)
    (hu : Function.Surjective (boundaryLinear k u u)) :
    H (⟨P.source, P.target, P.projective_source, P.projective_target, u⟩ : TwoTerm R) := by
  have (A B : FGModuleCat.{u} R) : Module.Finite k (A ⟶ B) := finiteModuleHom_isFinite k A B
  obtain ⟨n, ⟨r⟩⟩ := PencilJet.exists_retract k u P.differential hu
  exact hR _ (jet P (u-P.differential) n)
    (r.map (doubleFunctor ⋙ HomotopyCategory.quotient _ _)) (mem_jet hT P hP _ n)

include k in
/-- A presilting complex in the class of a member of a two-term thick
subcategory belongs to that subcategory, over every field. -/
theorem mem_presilting_of_class_eq {H : TwoTerm R → Prop} (hT : TwoOutOfThree H)
    (hR : ∀ (A B : TwoTerm R), Retract A.homotopyObject B.homotopyObject → H B → H A)
    (P Y : TwoTerm R) (hp : P.IsPresilting) (hy : H Y) (h : P.projectiveClass = Y.projectiveClass) :
    H P := by
  obtain ⟨S, T, ⟨e₁⟩, ⟨e₀⟩⟩ := exists_stable_term_isos P Y h
  let P' := P.directSum (contractible S)
  let Y' := Y.directSum (contractible T)
  let i₁ : P'.source ≅ Y'.source := e₁
  let i₀ : P'.target ≅ Y'.target := e₀
  let u := i₁.inv ≫ P'.differential ≫ i₀.hom
  let U : TwoTerm R := ⟨Y'.source, Y'.target, Y'.projective_source, Y'.projective_target, u⟩
  have hu : i₁.hom ≫ U.differential = P'.differential ≫ i₀.hom := i₁.hom_inv_id_assoc _
  have hr := (isPresilting_iff_of_term_isos k P' U i₁ i₀ hu).1
    ((isPresilting_directSum_contractible_iff k P S).2 hp)
  have hc : H (contractible T) :=
    hR _ Y ⟨0, 0, (isZero_contractible T).eq_of_src _ _⟩ hy
  have hy' : H Y' := ((hT Y Y' (contractible T) _ _ _ (blockTriangle_distinguished Y _ 0)).1 hy).2 hc
  have hU : H U := mem_rigid_on_terms k hT hR Y' hy' u hr
  let e : P'.asArrow ≅ U.asArrow := Arrow.isoMk' P'.differential U.differential i₁ i₀ hu
  let r : Retract P.asArrow P'.asArrow :=
    ⟨inlDirectSum _ _, fstDirectSum _ _, inlDirectSum_fstDirectSum _ _⟩
  exact hR P U ((r.trans e.retract).map (doubleFunctor ⋙ HomotopyCategory.quotient _ _)) hU

include k in
/-- In an E-finite algebra, every two-sided orthogonal member Y of H has a
presilting representative of its class inside the same H and the same orthogonal. -/
theorem exists_presilting_in_orthogonal_of_isEFinite (hf : IsEFinite R) {H : TwoTerm R → Prop}
    (hT : TwoOutOfThree H)
    (hR : ∀ (A B : TwoTerm R), Retract A.homotopyObject B.homotopyObject → H B → H A)
    (U Y : TwoTerm R) (hy : H Y) (hUY : Function.Surjective (homotopyBoundary U Y))
    (hYU : Function.Surjective (homotopyBoundary Y U)) :
    ∃ V : TwoTerm R, H V ∧ V.IsPresilting ∧ V.projectiveClass = Y.projectiveClass ∧
      Function.Surjective (homotopyBoundary U V) ∧ Function.Surjective (homotopyBoundary V U) := by
  obtain ⟨V, hv, hclass⟩ := hf Y.projectiveClass
  obtain ⟨h₁, h₂⟩ := shiftedHomFinrank_le_of_isPresilting_of_class_eq k V Y hv hclass U
  rw [(shiftedHomFinrank_eq_zero_iff k Y U).2 hYU] at h₁
  rw [(shiftedHomFinrank_eq_zero_iff k U Y).2 hUY] at h₂
  exact ⟨V, mem_presilting_of_class_eq k hT hR V Y hv hy hclass, hv, hclass,
    (shiftedHomFinrank_eq_zero_iff k U V).1 (by omega),
    (shiftedHomFinrank_eq_zero_iff k V U).1 (by omega)⟩

end EFiniteCharacterizations.TwoTerm
