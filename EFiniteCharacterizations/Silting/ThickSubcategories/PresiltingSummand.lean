module

public import EFiniteCharacterizations.LinearAlgebra.AddClosure
public import Mathlib.CategoryTheory.Triangulated.Generators

/-! # Orthogonal objects in the thick closure of a presilting object -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty
open scoped ZeroObject

namespace EFiniteCharacterizations

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Presilting

/-- Objects obtained by extensions of shifts of a fixed object, with
the allowed shifts restricted to a specified set of integers. -/
inductive ShiftFactors (P : C) (degrees : Set ℤ) : ObjectProperty C
  | zero {X : C} : IsZero X → ShiftFactors P degrees X
  | generator (n : ℤ) : n ∈ degrees → ShiftFactors P degrees (P⟦n⟧)
  | iso {X Y : C} : (X ≅ Y) → ShiftFactors P degrees X → ShiftFactors P degrees Y
  | extension (T : Triangle C) : T ∈ distTriang C → ShiftFactors P degrees T.obj₁ →
      ShiftFactors P degrees T.obj₃ → ShiftFactors P degrees T.obj₂

variable (P : C) (d : Set ℤ)

instance : (ShiftFactors P d).ContainsZero := ⟨0,isZero_zero _,.zero (isZero_zero _)⟩
instance : (ShiftFactors P d).IsClosedUnderIsomorphisms := ⟨fun e h ↦ .iso e h⟩
instance : (ShiftFactors P d).IsTriangulatedClosed₂ :=
  .mk' (fun T hT a b ↦ .extension T hT a b)

private theorem shift_factors {e : Set ℤ} (s : ℤ) (hs : ∀ i ∈ d, i + s ∈ e)
    {X : C} (h : ShiftFactors P d X) : ShiftFactors P e (X⟦s⟧) := by
  induction h with
  | zero hz => exact .zero ((shiftFunctor C s).map_isZero hz)
  | generator i hi => exact .iso ((shiftFunctorAdd C i s).app P) (.generator _ (hs _ hi))
  | iso eq _ ih => exact .iso ((shiftFunctor C s).mapIso eq) ih
  | extension T hT _ _ h₁ h₃ => exact .extension _ (Triangle.shift_distinguished T hT s) h₁ h₃

local notation "allDegrees" => (Set.univ : Set ℤ)

instance : (ShiftFactors P allDegrees).IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨fun _ h ↦ shift_factors P allDegrees (e := allDegrees) s (fun _ _ ↦ trivial) h⟩

/-- Retract closure preserves extension closure in a triangulated category. -/
theorem extension_closed_retractClosure (A : ObjectProperty C) [A.IsClosedUnderIsomorphisms]
    [A.IsTriangulatedClosed₂] : A.retractClosure.IsTriangulatedClosed₂ := by
  apply IsTriangulatedClosed₂.mk'
  intro T ht ha hb
  apply monotone_retractClosure (extensionProduct_le_of_isTriangulatedClosed₂ (le_refl A) (le_refl A))
  exact extensionProduct_retractClosure_retractClosure_le A A _
    ⟨_,_,_,_,_,ht,ha,hb⟩

private theorem factors_of_thick {X : C} (hx : (singleton P).triangEnvelope X) :
    (ShiftFactors P allDegrees).retractClosure X := by
  let A := ShiftFactors P allDegrees
  let := extension_closed_retractClosure A
  let : A.retractClosure.IsTriangulated := {}
  apply (triangEnvelope_le_iff (singleton P) (Q := A.retractClosure)).2 (singleton_le_iff.2 ?_) X hx
  apply le_retractClosure A
  exact .iso ((shiftFunctorZero C ℤ).app P) (.generator 0 trivial)

private theorem no_maps_from {Y : C} (hgen : ∀ i ∈ d, ∀ f : P⟦i⟧ ⟶ Y, f = 0)
    {X : C} (hx : ShiftFactors P d X) (f : X ⟶ Y) : f = 0 := by
  induction hx with
  | zero h => exact h.eq_of_src f 0
  | generator i hi => exact hgen i hi f
  | iso e _ ih => exact zero_of_epi_comp e.hom (ih _)
  | extension T hT _ _ ha hb =>
    obtain ⟨g,hg⟩ := Triangle.yoneda_exact₂ T hT f (ha _)
    simpa [hb g] using hg

private theorem no_maps_to {X : C} (hgen : ∀ i ∈ d, ∀ f : X ⟶ P⟦i⟧, f = 0)
    {Y : C} (hy : ShiftFactors P d Y) (f : X ⟶ Y) : f = 0 := by
  induction hy with
  | zero h => exact h.eq_of_tgt f 0
  | generator i hi => exact hgen i hi f
  | iso e _ ih => exact zero_of_comp_mono e.inv (ih _)
  | extension T hT _ _ ha hb =>
    obtain ⟨g,hg⟩ := Triangle.coyoneda_exact₂ T hT f (hb _)
    simpa [ha g] using hg

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [Preadditive C] in
theorem between_shifts {X Y : C} {a b : ℤ}
    (h : Subsingleton (X ⟶ Y⟦b-a⟧)) : Subsingleton (X⟦a⟧ ⟶ Y⟦b⟧) := by
  let e : Y⟦b⟧ ≅ (Y⟦b-a⟧)⟦a⟧ := (shiftFunctorAdd' C (b-a) a b (by omega)).app Y
  have : Subsingleton (X⟦a⟧ ⟶ (Y⟦b-a⟧)⟦a⟧) := (shiftFunctor C a).map_surjective.subsingleton
  exact (Iso.homCongr (Iso.refl (X⟦a⟧)) e).injective.subsingleton

private theorem no_backward_extension (hp : ∀ n : ℤ, 0 < n → Subsingleton (P ⟶ P⟦n⟧))
    {a b : Set ℤ} (h : ∀ i ∈ a, ∀ j ∈ b, i ≤ j) {X Y : C}
    (hx : ShiftFactors P a X) (hy : ShiftFactors P b Y) (f : X ⟶ Y⟦(1 : ℤ)⟧) : f = 0 := by
  have sy := shift_factors P b 1 (e := {n | n-1 ∈ b}) (fun j hj ↦ by simpa using hj) hy
  apply no_maps_from P a _ hx f
  intro i hi g
  apply no_maps_to P _ _ sy g
  intro j hj q
  have hle := h i hi (j-1) hj
  exact (between_shifts (a := i) (b := j) (hp _ (by omega))).elim q 0

local infixr:68 " ⋆ " => extensionProduct

private theorem split_swap {A B : ObjectProperty C}
    (h : ∀ X Y, B X → A Y → ∀ f : X ⟶ Y⟦(1 : ℤ)⟧, f = 0) : A ⋆ B ≤ B ⋆ A := by
  rintro X ⟨Y,Z,f,g,t,ht,hy,hz⟩
  obtain ⟨e,_,_⟩ := exists_iso_binaryBiproduct_of_distTriang _ ht (h _ _ hz hy t)
  apply (B ⋆ A).prop_of_iso ((biprod.braiding Z Y) ≪≫ e.symm)
  exact ⟨Z,Y,_,_,_,binaryBiproductTriangle_distinguished Z Y,hz,hy⟩

variable [IsTriangulated C]

private theorem ordered_extension_closed (A B : ObjectProperty C)
    (ha : A ⋆ A ≤ A) (hb : B ⋆ B ≤ B) (hs : B ⋆ A ≤ A ⋆ B) :
    (A ⋆ B) ⋆ (A ⋆ B) ≤ A ⋆ B := by
  calc
    (A ⋆ B) ⋆ (A ⋆ B) = A ⋆ ((B ⋆ A) ⋆ B) := by simp only [extensionProduct_assoc]
    _ ≤ A ⋆ ((A ⋆ B) ⋆ B) := monotone_extensionProduct_right A (monotone_extensionProduct_left B hs)
    _ = (A ⋆ A) ⋆ (B ⋆ B) := by simp only [extensionProduct_assoc]
    _ ≤ A ⋆ B := (monotone_extensionProduct_left _ ha).trans (monotone_extensionProduct_right _ hb)

private theorem cut_factors (hp : ∀ n : ℤ, 0 < n → Subsingleton (P ⟶ P⟦n⟧))
    (a b : Set ℤ) (horder : ∀ i ∈ a, ∀ j ∈ b, i ≤ j) (hcover : d ⊆ a ∪ b) :
    ShiftFactors P d ≤ ShiftFactors P a ⋆ ShiftFactors P b := by
  let A := ShiftFactors P a
  let B := ShiftFactors P b
  have hswap : B ⋆ A ≤ A ⋆ B := split_swap fun _ _ hx hy ↦ no_backward_extension P hp horder hx hy
  have hc := ordered_extension_closed A B
    (extensionProduct_le_of_isTriangulatedClosed₂ (le_refl A) (le_refl A))
    (extensionProduct_le_of_isTriangulatedClosed₂ (le_refl B) (le_refl B)) hswap
  intro X hx
  induction hx with
  | zero hz => exact le_extensionProduct_left B _ (show A _ from .zero hz)
  | generator i hi =>
    rcases hcover hi with ha | hb
    · exact le_extensionProduct_left B _ (show A _ from .generator i ha)
    · exact le_extensionProduct_right A _ (show B _ from .generator i hb)
  | iso e _ ih => exact (A ⋆ B).prop_of_iso e ih
  | extension T hT _ _ ha hb => exact hc _ ⟨_,_,_,_,_,hT,ha,hb⟩

omit [IsTriangulated C] in
private theorem inAdd_of_zero_factors (hp : ∀ n : ℤ, 0 < n → Subsingleton (P ⟶ P⟦n⟧))
    {X : C} (hx : ShiftFactors P {0} X) : IsInAdd X P := by
  induction hx with
  | zero hz => exact ⟨[],by simpa using hz.eq_of_src 0 (𝟙 _)⟩
  | generator i hi =>
    obtain rfl := Set.mem_singleton_iff.1 hi
    let e := (shiftFunctorZero C ℤ).app P
    exact IsInAdd.of_retraction e.hom e.inv e.hom_inv_id
  | iso e _ ih => exact (IsInAdd.of_retraction e.inv e.hom e.inv_hom_id).trans ih
  | extension T hT ha hb ih₁ ih₃ =>
    have hz := no_backward_extension P hp (fun _ hi _ hj ↦ le_of_eq
      ((Set.mem_singleton_iff.1 hi).trans (Set.mem_singleton_iff.1 hj).symm)) hb ha T.mor₃
    obtain ⟨e,_,_⟩ := exists_iso_binaryBiproduct_of_distTriang T hT hz
    apply (IsInAdd.of_retraction e.hom e.inv e.hom_inv_id).trans
    exact IsInAdd.of_total ih₁ ih₃ biprod.fst biprod.inl biprod.snd biprod.inr biprod.total

/-- An object of the thick subcategory generated by a presilting object
belongs to its additive closure if the positive shifted Hom groups vanish
in both directions. This holds in any triangulated category. -/
theorem isInAdd_of_mem_thick {L : C} (hp : ∀ n : ℤ, 0 < n → Subsingleton (P ⟶ P⟦n⟧))
    (hl : (singleton P).triangEnvelope L)
    (hPL : ∀ n : ℤ, 0 < n → Subsingleton (P ⟶ L⟦n⟧))
    (hLP : ∀ n : ℤ, 0 < n → Subsingleton (L ⟶ P⟦n⟧)) : IsInAdd L P := by
  obtain ⟨D,hD,⟨s,r,hs⟩⟩ := factors_of_thick P hl
  let neg := {i : ℤ | i < 0}
  let nonneg := {i : ℤ | 0 ≤ i}
  let pos := {i : ℤ | 0 < i}
  obtain ⟨A,B,f,q,t,ht,hA,hB⟩ := cut_factors P allDegrees hp neg nonneg
    (fun _ hi _ hj ↦ hi.le.trans hj) (fun i _ ↦ lt_or_ge i 0) D hD
  obtain ⟨Z,Y,p,g,t',ht',hZ,hY⟩ := cut_factors P nonneg hp {0} pos
    (fun _ hi _ hj ↦ (Set.mem_singleton_iff.1 hi) ▸ hj.le)
    (fun i hi ↦ (eq_or_lt_of_le hi).imp Eq.symm id) B hB
  have hf : f ≫ r = 0 := by
    apply no_maps_from P neg _ hA
    intro i hi h
    let e := (shiftFunctorZero C ℤ).app L
    have h₀ := between_shifts (a := i) (b := 0) (hPL _ (by change i < 0 at hi; omega))
    exact zero_of_comp_mono e.inv (h₀.elim _ _)
  obtain ⟨u,hu⟩ := Triangle.yoneda_exact₂ _ ht r hf
  have hg : (s ≫ q) ≫ g = 0 := no_maps_to P pos (fun i hi h ↦ (hLP i hi).elim h 0) hY _
  obtain ⟨v,hv⟩ := Triangle.coyoneda_exact₂ _ ht' (s ≫ q) hg
  apply (IsInAdd.of_retraction v (p ≫ u) ?_).trans (inAdd_of_zero_factors P hp hZ)
  change r = q ≫ u at hu
  change s ≫ q = v ≫ p at hv
  rw [← Category.assoc,← hv,Category.assoc,← hu,hs]

theorem mem_thick_of_isInAdd (U X : C) (hx : IsInAdd X U) :
    (singleton U).triangEnvelope X := by
  let D := (ObjectProperty.singleton U).triangEnvelope
  have hU : D U := (singleton U).le_triangEnvelope _ (.mk ())
  obtain ⟨l, hl⟩ := hx
  have factor (t : List ((X ⟶ U) × (U ⟶ X))) :
      ∃ (V : C) (a : X ⟶ V)
        (b : V ⟶ X), D V ∧ a ≫ b = (t.map (fun p ↦ p.1 ≫ p.2)).sum := by
    induction t with
    | nil => exact ⟨_, 0, 0, hU, by simp⟩
    | cons p t ih =>
      obtain ⟨V, a, b, hV, hab⟩ := ih
      exact ⟨_, biprod.lift p.1 a, biprod.desc p.2 b,
        D.ext_of_isTriangulatedClosed₂ _ (binaryBiproductTriangle_distinguished _ _) hU hV,
        by simp [biprod.lift_desc, hab]⟩
  obtain ⟨V, a, b, hv, hab⟩ := factor l
  exact D.prop_of_retract (Retract.mk a b (hab.trans hl)) hv

end Presilting
end EFiniteCharacterizations
