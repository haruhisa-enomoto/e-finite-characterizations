module

public import EFiniteCharacterizations.Presentations.SplitBoundary
public import EFiniteCharacterizations.Presentations.StableProjectiveTerms

/-! # Comparison at a presilting complex of the same integral class -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]

/-- Termwise isomorphisms that make the differential square commute preserve
both shifted Hom dimensions. -/
theorem shiftedHomFinrank_eq_of_term_isos (P Q V : TwoTerm R)
    (e₁ : P.source ≅ Q.source) (e₀ : P.target ≅ Q.target)
    (h : e₁.hom ≫ Q.differential = P.differential ≫ e₀.hom) :
    P.shiftedHomFinrank k V = Q.shiftedHomFinrank k V ∧
      V.shiftedHomFinrank k P = V.shiftedHomFinrank k Q := by
  have (M N : FGModuleCat.{u} R) : Module.Finite k (M ⟶ N) := finiteModuleHom_isFinite k M N
  unfold shiftedHomFinrank
  constructor
  · have hr := boundaryLinear_rank_eq_of_source_iso k P.differential Q.differential V.differential e₁ e₀ h
    have ht := (Linear.homCongr k e₁ (Iso.refl V.target)).finrank_eq
    have hp := Submodule.finrank_quotient_add_finrank (boundaryLinear k P.differential V.differential).range
    have hq := Submodule.finrank_quotient_add_finrank (boundaryLinear k Q.differential V.differential).range
    omega
  · have hr := boundaryLinear_rank_eq_of_target_iso k P.differential Q.differential V.differential e₁ e₀ h
    have ht := (Linear.homCongr k (Iso.refl V.source) e₀).finrank_eq
    have hp := Submodule.finrank_quotient_add_finrank (boundaryLinear k V.differential P.differential).range
    have hq := Submodule.finrank_quotient_add_finrank (boundaryLinear k V.differential Q.differential).range
    omega

include k in
theorem isPresilting_iff_of_term_isos (P Q : TwoTerm R) (e₁ : P.source ≅ Q.source)
    (e₀ : P.target ≅ Q.target) (h : e₁.hom ≫ Q.differential = P.differential ≫ e₀.hom) :
    P.IsPresilting ↔ Q.IsPresilting := by
  have h₁ (V : TwoTerm R) := shiftedHomFinrank_eq_of_term_isos k P Q V e₁ e₀ h
  simp only [IsPresilting, ← shiftedHomFinrank_eq_zero_iff k]
  rw [(h₁ P).2, (h₁ Q).1]

/-- A presilting complex minimizes both shifted Hom dimensions among complexes
of its projective class. Adding contractible complexes gives common terms,
so this comparison requires no minimal representatives. -/
theorem shiftedHomFinrank_le_of_isPresilting_of_class_eq (P Q : TwoTerm R)
    (hP : P.IsPresilting) (hclass : P.projectiveClass = Q.projectiveClass) (V : TwoTerm R) :
    P.shiftedHomFinrank k V ≤ Q.shiftedHomFinrank k V ∧
      V.shiftedHomFinrank k P ≤ V.shiftedHomFinrank k Q := by
  obtain ⟨S, T, ⟨e₁⟩, ⟨e₀⟩⟩ := exists_stable_term_isos P Q hclass
  let P' := P.directSum (contractible S)
  let Q' := Q.directSum (contractible T)
  let i₁ : P'.source ≅ Q'.source := e₁
  let i₀ : P'.target ≅ Q'.target := e₀
  let _ := Q'.projective_source
  let _ := Q'.projective_target
  let d : Q'.source ⟶ Q'.target := i₁.inv ≫ P'.differential ≫ i₀.hom
  let P'' := ofDifferential d
  have hd : i₁.hom ≫ P''.differential = P'.differential ≫ i₀.hom := by
    change i₁.hom ≫ (i₁.inv ≫ P'.differential ≫ i₀.hom) = P'.differential ≫ i₀.hom
    rw [Iso.hom_inv_id_assoc]
  have h₁ (W : TwoTerm R) := shiftedHomFinrank_eq_of_term_isos k P' P'' W i₁ i₀ hd
  have hp' : P'.IsPresilting := (isPresilting_directSum_contractible_iff k P S).2 hP
  have hd' : (ofDifferential d).IsPresilting := (isPresilting_iff_of_term_isos k P' P'' i₁ i₀ hd).1 hp'
  have hineq : P''.shiftedHomFinrank k V ≤ Q'.shiftedHomFinrank k V ∧
      V.shiftedHomFinrank k P'' ≤ V.shiftedHomFinrank k Q' :=
    shiftedHomFinrank_le_of_rigid k (σ := Q'.differential) hd' V
  rw [← (h₁ V).1, ← (h₁ V).2] at hineq
  simpa only [P', Q', shiftedHomFinrank_directSum_contractible_source,
    shiftedHomFinrank_directSum_contractible_target] using hineq

/-- The presilting representative of the sum class satisfies the four
inequalities needed to subdivide a sector. -/
theorem shiftedHomFinrank_mediant_bounds (E L Z : TwoTerm R) (hE : E.IsPresilting)
    (hL : L.IsPresilting) (hZ : Z.IsPresilting) (hEL : E.shiftedHomFinrank k L = 0)
    (hLE : 0 < L.shiftedHomFinrank k E) (hclass : Z.projectiveClass = E.projectiveClass + L.projectiveClass) :
    E.shiftedHomFinrank k Z = 0 ∧ Z.shiftedHomFinrank k L = 0 ∧
      Z.shiftedHomFinrank k E < L.shiftedHomFinrank k E ∧
      L.shiftedHomFinrank k Z < L.shiftedHomFinrank k E := by
  obtain ⟨X, hX, hEX, hXL, hXE, hLX⟩ :=
    exists_extension_with_shiftedHomFinrank_bounds k E L hE hL hEL hLE
  have hZX := hclass.trans hX.symm
  have hE' := shiftedHomFinrank_le_of_isPresilting_of_class_eq k Z X hZ hZX E
  have hL' := shiftedHomFinrank_le_of_isPresilting_of_class_eq k Z X hZ hZX L
  exact ⟨Nat.eq_zero_of_le_zero (hE'.2.trans hEX.le), Nat.eq_zero_of_le_zero (hL'.1.trans hXL.le),
    hE'.1.trans_lt hXE, hL'.2.trans_lt hLX⟩

end EFiniteCharacterizations.TwoTerm
