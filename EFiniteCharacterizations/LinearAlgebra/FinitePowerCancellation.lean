module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Cancellation of finite powers in categories with finite Hom sets -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace EFiniteCharacterizations

noncomputable section

variable {C : Type*} [Category C] [HasFiniteProducts C]

/-- Maps to T coequalizing the indicated pairs of parallel arrows. -/
private abbrev Equalizing {D X : C} (s : Finset ((D ⟶ X) × (D ⟶ X))) (T : C) :=
  {f : X ⟶ T // ∀ p ∈ s, p.1 ≫ f = p.2 ≫ f}

private def equalizingPower {D X : C} (s : Finset ((D ⟶ X) × (D ⟶ X))) (T : C) (n : ℕ) :
    Equalizing s (∏ᶜ fun _ : Fin n ↦ T) ≃ (Fin n → Equalizing s T) where
  toFun f i := ⟨f.val ≫ Pi.π _ i, fun p hp ↦ by simp only [← Category.assoc, f.property p hp]⟩
  invFun g := ⟨Pi.lift (fun i ↦ (g i).val), fun p hp ↦ by
    apply Pi.hom_ext
    intro j
    simpa only [Category.assoc, Pi.lift_comp_π] using (g j).property p hp⟩
  left_inv f := Subtype.ext (Pi.hom_ext _ _ (fun i ↦ Pi.lift_comp_π _ i))
  right_inv g := funext fun i ↦ Subtype.ext (Pi.lift_comp_π _ i)

private def equalizingIso {D X T U : C} (s : Finset ((D ⟶ X) × (D ⟶ X))) (e : T ≅ U) :
    Equalizing s T ≃ Equalizing s U where
  toFun f := ⟨f.val ≫ e.hom, fun p hp ↦ by simp only [← Category.assoc, f.property p hp]⟩
  invFun f := ⟨f.val ≫ e.inv, fun p hp ↦ by simp only [← Category.assoc, f.property p hp]⟩
  left_inv _ := Subtype.ext (by simp)
  right_inv _ := Subtype.ext (by simp)

private theorem equalizing_card {D X A B : C} (s : Finset ((D ⟶ X) × (D ⟶ X))) {n : ℕ} (hn : 0 < n)
    (e : (∏ᶜ fun _ : Fin n ↦ A) ≅ ∏ᶜ fun _ : Fin n ↦ B) :
    Nat.card (Equalizing s A) = Nat.card (Equalizing s B) := by
  have h := Nat.card_congr (((equalizingPower s A n).symm.trans (equalizingIso s e)).trans
    (equalizingPower s B n))
  simp only [Nat.card_fun, Nat.card_fin] at h
  exact (pow_left_inj₀ (Nat.zero_le _) (Nat.zero_le _) hn.ne').1 h

private theorem hom_card {X A B : C} {n : ℕ} (hn : 0 < n)
    (e : (∏ᶜ fun _ : Fin n ↦ A) ≅ ∏ᶜ fun _ : Fin n ↦ B) :
    Nat.card (X ⟶ A) = Nat.card (X ⟶ B) := by
  let s : Finset ((X ⟶ X) × (X ⟶ X)) := ∅
  let t (T : C) : Equalizing s T ≃ (X ⟶ T) := Equiv.subtypeUnivEquiv (by simp [s])
  exact (Nat.card_congr (t A)).symm.trans ((equalizing_card s hn e).trans (Nat.card_congr (t B)))

open scoped Classical in
private def badPairs {D X : C} (T : C) [Fintype (X ⟶ T)] (p : (D ⟶ X) × (D ⟶ X)) :
    Finset (X ⟶ T) := Finset.univ.filter fun f ↦ p.1 ≫ f = p.2 ≫ f

open scoped Classical in
private theorem mem_inf_finite {ι α : Type*} [Fintype α] (s : Finset ι) (a : ι → Finset α) (x : α) :
    x ∈ s.inf a ↔ ∀ i ∈ s, x ∈ a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.inf_insert, ih]

open scoped Classical in
omit [HasFiniteProducts C] in
private theorem card_badPairs {D X : C} (T : C) [Fintype (X ⟶ T)] (s : Finset ((D ⟶ X) × (D ⟶ X))) :
    (s.inf (badPairs T)).card = Nat.card (Equalizing s T) := by
  classical
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun f ↦ by simp [mem_inf_finite, badPairs]

/-- If the four Hom sets between A and B are finite, an isomorphism of
their n-fold products for positive n implies an isomorphism A ≅ B. -/
theorem nonempty_iso_of_finite_homs_of_power_iso (A B : C)
    [Finite (A ⟶ A)] [Finite (A ⟶ B)] [Finite (B ⟶ A)] [Finite (B ⟶ B)]
    {n : ℕ} (hn : 0 < n) (e : (∏ᶜ fun _ : Fin n ↦ A) ≅ ∏ᶜ fun _ : Fin n ↦ B) :
    Nonempty (A ≅ B) := by
  classical
  let _ := Fintype.ofFinite (A ⟶ A)
  let _ := Fintype.ofFinite (A ⟶ B)
  let _ := Fintype.ofFinite (B ⟶ A)
  let _ := Fintype.ofFinite (B ⟶ B)
  let s := (Finset.univ : Finset ((B ⟶ A) × (B ⟶ A))).filter fun p ↦ p.1 ≠ p.2
  let good (T : C) [Fintype (A ⟶ T)] := s.inf fun p ↦ (badPairs T p)ᶜ
  have same : (good A).card = (good B).card := by
    apply Int.ofNat_inj.mp
    dsimp only [good]
    rw [Finset.inclusion_exclusion_card_inf_compl, Finset.inclusion_exclusion_card_inf_compl]
    apply Finset.sum_congr rfl
    intro t _
    rw [card_badPairs A t, card_badPairs B t, equalizing_card t hn e]
  have id_good : 𝟙 A ∈ good A := by
    simp [good, mem_inf_finite, badPairs, s]
  obtain ⟨f, hf⟩ := Finset.card_pos.mp (same ▸ Finset.card_pos.mpr ⟨𝟙 A, id_good⟩)
  have inj : Function.Injective (fun g : B ⟶ A ↦ g ≫ f) := by
    intro g h eq
    by_contra ne
    have hm := (mem_inf_finite s _ f).1 hf (g,h) (by simp [s,ne])
    exact (Finset.mem_compl.1 hm) (by simpa [badPairs] using eq)
  have bij := (Fintype.bijective_iff_injective_and_card _).2 ⟨inj,
    by simpa only [← Nat.card_eq_fintype_card] using hom_card (X := B) hn e⟩
  obtain ⟨g,hg⟩ := bij.surjective (𝟙 B)
  change g ≫ f = 𝟙 B at hg
  have surj : Function.Surjective (fun a : A ⟶ A ↦ a ≫ f) :=
    fun t ↦ ⟨t ≫ g, by simp [hg]⟩
  have bij' := (Fintype.bijective_iff_surjective_and_card _).2 ⟨surj,
    by simpa only [← Nat.card_eq_fintype_card] using hom_card (X := A) hn e⟩
  exact ⟨⟨f,g,bij'.injective (by simp [hg]),hg⟩⟩

end
end EFiniteCharacterizations
