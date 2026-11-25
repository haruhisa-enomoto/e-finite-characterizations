module

public import EFiniteCharacterizations.Silting.ThickSubcategories.TwoTermTriangles

/-! # Reduction to the two-sided orthogonal of a presilting complex -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R]

/-- Membership agrees for every class containing U and satisfying two-out-of-three
on upper triangular block extensions. -/
def SameMembership (U X Y : TwoTerm R) : Prop :=
  ∀ H : TwoTerm R → Prop, H U →
    (∀ (P Q : TwoTerm R) (w : Q.source ⟶ P.target),
      let E := P.blockExtension Q w
      (H P → (H E ↔ H Q)) ∧ (H Q → (H E ↔ H P))) → (H X ↔ H Y)

/-- Successive extensions of X by copies of U on the quotient side. -/
inductive RightExtensions (U X : TwoTerm R) : TwoTerm R → Prop
  | start : RightExtensions U X X
  | next {B} : RightExtensions U X B → (w : U.source ⟶ B.target) →
      RightExtensions U X (B.blockExtension U w)

theorem RightExtensions.sameMembership {U X B : TwoTerm R} (h : RightExtensions U X B) :
    SameMembership U X B := by
  intro H hU hH
  induction h with
  | start => rfl
  | next _ w ih => exact ih.trans ((hH _ U w).2 hU).symm

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

theorem exists_right_orthogonal (U : TwoTerm R) (hu : U.IsPresilting)
    (n : ℕ) (X : TwoTerm R) (hd : U.shiftedHomFinrank k X = n) :
    ∃ Y : TwoTerm R, U.shiftedHomFinrank k Y = 0 ∧ RightExtensions U X Y := by
  induction n using Nat.strong_induction_on generalizing X with
  | h n ih =>
    by_cases hn : n = 0
    · exact ⟨X, hd.trans hn, .start⟩
    have (A B : FGModuleCat.{u} R) : Module.Finite k (A ⟶ B) := finiteModuleHom_isFinite k A B
    obtain ⟨z, hz⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
      (show 0 < U.shiftedHomFinrank k X by omega)
    obtain ⟨w, rfl⟩ := (boundaryLinear k U.differential X.differential).range.mkQ_surjective z
    let E := X.blockExtension U w
    have hlt : U.shiftedHomFinrank k E < n := hd ▸ finrank_lt_of_surjective_of_kills_nonzero
      (blockCokernelInclusion k X.differential U.differential w U.differential)
      (blockCokernelInclusion_surjective _ _ _ _ _ hu) hz
      (blockCokernelInclusion_extensionClass _ _ _ _)
    obtain ⟨Y, hy, he⟩ := ih _ hlt E rfl
    have compose {A B D : TwoTerm R} (p : RightExtensions U A B) (q : RightExtensions U B D) :
        RightExtensions U A D := by
      induction q with
      | start => exact p
      | next _ w ih => exact ih.next w
    exact ⟨Y, hy, compose (RightExtensions.start.next w) he⟩

private theorem exists_left_orthogonal (U : TwoTerm R) (hu : U.IsPresilting)
    (n : ℕ) (X : TwoTerm R) (hd : X.shiftedHomFinrank k U = n) (hx : U.shiftedHomFinrank k X = 0) :
    ∃ Y : TwoTerm R, U.shiftedHomFinrank k Y = 0 ∧ Y.shiftedHomFinrank k U = 0 ∧ SameMembership U X Y := by
  induction n using Nat.strong_induction_on generalizing X with
  | h n ih =>
    by_cases hn : n = 0
    · exact ⟨X, hx, hd.trans hn, fun _ _ _ ↦ Iff.rfl⟩
    have (A B : FGModuleCat.{u} R) : Module.Finite k (A ⟶ B) := finiteModuleHom_isFinite k A B
    obtain ⟨z, hz⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
      (show 0 < X.shiftedHomFinrank k U by omega)
    obtain ⟨w, rfl⟩ := (boundaryLinear k X.differential U.differential).range.mkQ_surjective z
    let E := U.blockExtension X w
    have hlt : E.shiftedHomFinrank k U < n := hd ▸ finrank_lt_of_surjective_of_kills_nonzero
      (blockCokernelProjection k U.differential X.differential w U.differential)
      (blockCokernelProjection_surjective _ _ _ _ _ hu) hz
      (blockCokernelProjection_extensionClass _ _ _ _)
    have hle : U.shiftedHomFinrank k E ≤ U.shiftedHomFinrank k U :=
      LinearMap.finrank_le_finrank_of_surjective (blockCokernelInclusion_surjective k
        U.differential X.differential w U.differential ((shiftedHomFinrank_eq_zero_iff k U X).1 hx))
    have hzU := (shiftedHomFinrank_eq_zero_iff k U U).2 hu
    obtain ⟨Y, hy, hy', he⟩ := ih _ hlt E rfl (by omega)
    exact ⟨Y, hy, hy', fun H hU hH ↦ ((hH U X w).1 hU).symm.trans (he H hU hH)⟩

include k in
/-- Every two-term complex has the same membership as a two-sided orthogonal
complex in every two-term thick subcategory containing U. Repeated block
extensions kill one shifted Hom dimension at a time. -/
theorem exists_orthogonal_sameMembership (U X : TwoTerm R) (hu : U.IsPresilting) :
    ∃ Y : TwoTerm R, Function.Surjective (homotopyBoundary U Y) ∧
      Function.Surjective (homotopyBoundary Y U) ∧ SameMembership U X Y := by
  obtain ⟨Z, hz, hxz⟩ := exists_right_orthogonal k U hu _ X rfl
  obtain ⟨Y, hy, hy', hzy⟩ := exists_left_orthogonal k U hu _ Z rfl hz
  exact ⟨Y, (shiftedHomFinrank_eq_zero_iff k U Y).1 hy,
    (shiftedHomFinrank_eq_zero_iff k Y U).1 hy', fun H hU hH ↦ (hxz.sameMembership H hU hH).trans (hzy H hU hH)⟩

variable [IsNoetherianRing R]

/-- Two-out-of-three for triangles all of whose terms are two-term complexes. -/
def TwoOutOfThree (H : TwoTerm R → Prop) : Prop :=
  ∀ (A B C : TwoTerm R) (f : A.homotopyObject ⟶ B.homotopyObject)
    (g : B.homotopyObject ⟶ C.homotopyObject) (h : C.homotopyObject ⟶ A.homotopyObject⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang _ → (H A → (H B ↔ H C)) ∧ (H C → (H B ↔ H A))

theorem SameMembership.iff_of_twoOutOfThree {U X Y : TwoTerm R} (h : SameMembership U X Y)
    {H : TwoTerm R → Prop} (hT : TwoOutOfThree H) (hU : H U) : H X ↔ H Y :=
  h H hU fun P Q w ↦ hT P (P.blockExtension Q w) Q _ _ _ (blockTriangle_distinguished P Q w)

/-- The two-term intersection of the ambient thick closure. -/
def InThick (U X : TwoTerm R) : Prop :=
  (ObjectProperty.singleton U.homotopyObject).triangEnvelope X.homotopyObject

theorem inThick_self (U : TwoTerm R) : InThick U U :=
  (ObjectProperty.singleton U.homotopyObject).le_triangEnvelope _ (.mk ())

theorem twoOutOfThree_inThick (U : TwoTerm R) : TwoOutOfThree (InThick U) := by
  intro A B C f g h ht
  let D := (ObjectProperty.singleton U.homotopyObject).triangEnvelope
  let T := Triangle.mk f g h
  exact ⟨fun hA ↦ ⟨fun hB ↦ D.ext_of_isTriangulatedClosed₃ T ht hA hB,
      fun hC ↦ D.ext_of_isTriangulatedClosed₂ T ht hA hC⟩,
    fun hC ↦ ⟨fun hB ↦ D.ext_of_isTriangulatedClosed₁ T ht hB hC,
      fun hA ↦ D.ext_of_isTriangulatedClosed₂ T ht hA hC⟩⟩

include k in
/-- For a presilting U, agreement with its ambient thick closure can be
tested just on the two-term complexes orthogonal to U in both directions. -/
theorem iff_inThick_of_orthogonal (U : TwoTerm R) (hu : U.IsPresilting)
    {H : TwoTerm R → Prop} (hT : TwoOutOfThree H) (hU : H U)
    (hZ : ∀ Y : TwoTerm R, Function.Surjective (homotopyBoundary U Y) →
      Function.Surjective (homotopyBoundary Y U) → (H Y ↔ InThick U Y)) (X : TwoTerm R) :
    H X ↔ InThick U X := by
  obtain ⟨Y, hUY, hYU, h⟩ := exists_orthogonal_sameMembership k U X hu
  exact (h.iff_of_twoOutOfThree hT hU).trans ((hZ Y hUY hYU).trans
    (h.iff_of_twoOutOfThree (twoOutOfThree_inThick U) (inThick_self U)).symm)

theorem inThick_of_isInAdd (U X : TwoTerm R) (hx : IsInAdd X.homotopyObject U.homotopyObject) :
    InThick U X :=
  Presilting.mem_thick_of_isInAdd _ _ hx

include k in
/-- Step 1 of thick generation. For a summand-closed additive class H with
two-out-of-three, it suffices to establish that its two-sided orthogonal
objects belong to the additive closure of U. -/
theorem inThick_iff_of_orthogonal_inAdd (U : TwoTerm R) (hu : U.IsPresilting)
    {H : TwoTerm R → Prop} (hT : TwoOutOfThree H) (hU : H U)
    (hadd : ∀ Y : TwoTerm R, IsInAdd Y.homotopyObject U.homotopyObject → H Y)
    (hcore : ∀ Y : TwoTerm R, H Y → Function.Surjective (homotopyBoundary U Y) →
      Function.Surjective (homotopyBoundary Y U) → IsInAdd Y.homotopyObject U.homotopyObject)
    (X : TwoTerm R) : H X ↔ InThick U X :=
  iff_inThick_of_orthogonal k U hu hT hU (fun Y hUY hYU ↦
    ⟨fun hy ↦ inThick_of_isInAdd U Y (hcore Y hy hUY hYU),
      fun hy ↦ hadd Y (isInAdd_of_mem_thick U Y hu hy hUY hYU)⟩) X

end EFiniteCharacterizations.TwoTerm
