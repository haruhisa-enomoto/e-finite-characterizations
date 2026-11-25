module

public import EFiniteCharacterizations.Modules.HomExtraction

/-! # Minimal relations between finite families of modules -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Multiset
open scoped ZeroObject

universe u

namespace EFiniteCharacterizations

namespace FamilyExtraction

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]

abbrev Family (R : Type u) [Ring R] := Multiset (FGModuleCat.{u} R)

noncomputable def totalClass (L : Family R) := (L.map GrothendieckGroup.of).sum

noncomputable def complexity (L : Family R) :=
  (L.map fun X ↦ FGModuleCat.moduleLength X ^ 2).sum

def Orthogonal (L M : Family R) : Prop :=
  ∀ X ∈ L, ∀ Y ∈ M, ∀ f : X ⟶ Y, f = 0

structure Relation (L M : Family R) : Prop where
  classes : totalClass L = totalClass M
  nonzero : (∃ X ∈ L, ¬ IsZero X) ∨ (∃ Y ∈ M, ¬ IsZero Y)
  orthogonal : Orthogonal L M

omit [IsArtinianRing R] in
private theorem exists_sum_object (L : Family R) :
    ∃ A : FGModuleCat.{u} R, GrothendieckGroup.of A = totalClass L ∧
      (∀ Y, (∀ f : A ⟶ Y, f = 0) ↔ ∀ X ∈ L, ∀ f : X ⟶ Y, f = 0) ∧
      (∀ Y, (∀ f : Y ⟶ A, f = 0) ↔ ∀ X ∈ L, ∀ f : Y ⟶ X, f = 0) := by
  induction L using Multiset.induction_on with
  | empty =>
    exact ⟨0, by simp [totalClass, GrothendieckGroup.of_isZero (isZero_zero _)],
      fun _ ↦ ⟨by simp, fun _ f ↦ (isZero_zero _).eq_of_src f 0⟩,
      fun _ ↦ ⟨by simp, fun _ f ↦ (isZero_zero _).eq_of_tgt f 0⟩⟩
  | cons X L ih =>
    obtain ⟨A, he, hout, hin⟩ := ih
    refine ⟨X ⊞ A, ?_, fun Y ↦ ?_, fun Y ↦ ?_⟩
    · have h := GrothendieckGroup.of_shortExact _ (ShortComplex.Splitting.ofHasBinaryBiproduct X A).shortExact
      simp only [totalClass] at he
      simpa [totalClass, he] using (show GrothendieckGroup.of (X ⊞ A) = GrothendieckGroup.of X + GrothendieckGroup.of A from h)
    · simp only [Multiset.mem_cons, forall_eq_or_imp, ← hout]
      constructor
      · intro h
        exact ⟨fun f ↦ by simpa using congrArg (fun g ↦ biprod.inl ≫ g) (h (biprod.desc f 0)),
          fun f ↦ by simpa using congrArg (fun g ↦ biprod.inr ≫ g) (h (biprod.desc 0 f))⟩
      · rintro ⟨hX, hA⟩ f
        apply biprod.hom_ext'
        · simpa using hX (biprod.inl ≫ f)
        · simpa using hA (biprod.inr ≫ f)
    · simp only [Multiset.mem_cons, forall_eq_or_imp, ← hin]
      constructor
      · intro h
        exact ⟨fun f ↦ by simpa using congrArg (fun g ↦ g ≫ biprod.fst) (h (biprod.lift f 0)),
          fun f ↦ by simpa using congrArg (fun g ↦ g ≫ biprod.snd) (h (biprod.lift 0 f))⟩
      · rintro ⟨hX, hA⟩ f
        apply biprod.hom_ext
        · simpa using hX (f ≫ biprod.fst)
        · simpa using hA (f ≫ biprod.snd)

/-- A nontrivial class relation between Hom-orthogonal families gives a
counterexample to equal-class Hom on their direct sums. -/
theorem Relation.not_equalClassHom {L M : Family R} (hr : Relation L M) :
    ¬ EqualClassHom (FGModuleCat.{u} R) := by
  obtain ⟨A, hA, hout, _⟩ := exists_sum_object L
  obtain ⟨B, hB, _, hin⟩ := exists_sum_object M
  have he := hA.trans (hr.classes.trans hB.symm)
  have hn : GrothendieckGroup.of A ≠ 0 := by
    intro hz
    rcases hr.nonzero with ⟨X, hx, hn⟩ | ⟨Y, hy, hn⟩
    · have ha : IsZero A := by by_contra h; exact FGModuleCat.class_ne_zero h hz
      exact hn ((IsZero.iff_id_eq_zero X).2 ((hout X).1 (fun f ↦ ha.eq_of_src f 0) X hx (𝟙 X)))
    · have hb : IsZero B := by by_contra h; exact FGModuleCat.class_ne_zero h (he.symm.trans hz)
      exact hn ((IsZero.iff_id_eq_zero Y).2 ((hin Y).1 (fun f ↦ hb.eq_of_tgt f 0) Y hy (𝟙 Y)))
  intro h
  obtain ⟨f, hf⟩ := h A B he hn
  exact hf ((hout B).2 (fun X hx ↦ (hin X).2 (hr.orthogonal X hx)) f)

/-- An unchanged member or a module strictly shorter than an original member. -/
def Below (L M : Family R) (X : FGModuleCat.{u} R) : Prop :=
  X ∈ L ∨ X ∈ M ∨ ∃ Y, (Y ∈ L ∨ Y ∈ M) ∧ FGModuleCat.moduleLength X < FGModuleCat.moduleLength Y

def Minimal (L M : Family R) : Prop :=
  Relation L M ∧ ∀ A B : Family R, Relation A B → (∀ X, X ∈ A ∨ X ∈ B → Below L M X) →
    complexity L + complexity M ≤ complexity A + complexity B

omit [IsNoetherianRing R] [IsArtinianRing R] in
theorem Relation.exists_minimal_below {L M : Family R} (hr : Relation L M) :
    ∃ A B : Family R, Minimal A B ∧ ∀ X, X ∈ A ∨ X ∈ B → Below L M X := by
  classical
  let P (n : ℕ) := ∃ A B : Family R, Relation A B ∧
    (∀ X, X ∈ A ∨ X ∈ B → Below L M X) ∧ complexity A + complexity B = n
  have h : ∃ n, P n := ⟨_, L, M, hr, fun _ hx ↦ hx.elim Or.inl (Or.inr ∘ Or.inl), rfl⟩
  obtain ⟨A, B, hab, bound, he⟩ := Nat.find_spec h
  refine ⟨A, B, ⟨hab, fun C D hcd hsub ↦ he.trans_le (Nat.find_min' h ⟨C, D, hcd, ?_, rfl⟩)⟩, bound⟩
  intro X hx
  rcases hsub X hx with ha | hb | ⟨Y, hy, hlt⟩
  · exact bound X (Or.inl ha)
  · exact bound X (Or.inr hb)
  · right; right
    rcases bound Y hy with hl | hm | ⟨Z, hz, hyz⟩
    · exact ⟨Y, Or.inl hl, hlt⟩
    · exact ⟨Y, Or.inr hm, hlt⟩
    · exact ⟨Z, hz, hlt.trans hyz⟩

theorem exists_minimal (h : ¬ EqualClassHom (FGModuleCat.{u} R)) :
    ∃ L M : Family R, Minimal L M := by
  classical
  obtain ⟨X, Y, he, hn, hz, _⟩ := exists_orthogonal_pair_of_not_equalClassHom h
  let P (n : ℕ) := ∃ L M : Family R, Relation L M ∧ complexity L + complexity M = n
  have hx : P (complexity {X} + complexity {Y}) := by
    refine ⟨{X}, {Y}, ⟨by simpa [totalClass] using he, Or.inl ⟨X, by simp, fun z ↦ hn (GrothendieckGroup.of_isZero z)⟩, ?_⟩, rfl⟩
    simpa [Orthogonal] using hz
  have hex : ∃ n, P n := ⟨_, hx⟩
  obtain ⟨L, M, hr, hn⟩ := Nat.find_spec hex
  exact ⟨L, M, hr, fun A B hab _ ↦ hn.trans_le (Nat.find_min' hex ⟨A, B, hab, rfl⟩)⟩

/-- Minimality forces Hom to vanish also in the opposite direction. -/
theorem Minimal.reverse {L M : Family R} (hm : Minimal L M) : Orthogonal M L := by
  classical
  intro Y hy X hx f
  by_contra hf
  have hni : ¬ IsIso f := by
    intro _
    have hz := hm.1.orthogonal X hx Y hy (inv f)
    exact hf (by simpa using congrArg (fun g : X ⟶ Y ↦ f ≫ g ≫ f) hz)
  obtain ⟨Q, K, q, j, _, _, hd, hn, hq, hk⟩ := exists_residual_pair_of_noniso f hf hni
  let A := L.erase X
  let B := M.erase Y
  have ha : X ::ₘ A = L := cons_erase hx
  have hb : Y ::ₘ B = M := cons_erase hy
  have hr : Relation (Q ::ₘ A) (K ::ₘ B) := by
    constructor
    · have he := hm.1.classes
      rw [← ha, ← hb] at he
      simp [totalClass] at he ⊢
      grind
    · exact hn.imp (fun h ↦ ⟨Q, mem_cons_self .., h⟩) (fun h ↦ ⟨K, mem_cons_self .., h⟩)
    · intro V hv W hw g
      have ho := hm.1.orthogonal
      rcases mem_cons.mp hv with rfl | hv <;> rcases mem_cons.mp hw with rfl | hw
      · apply (cancel_epi q).mp
        apply (cancel_mono j).mp
        simpa using ho X hx Y hy (q ≫ g ≫ j)
      · apply (cancel_epi q).mp
        simpa using ho X hx W (mem_of_mem_erase hw) (q ≫ g)
      · apply (cancel_mono j).mp
        simpa using ho V (mem_of_mem_erase hv) Y hy (g ≫ j)
      · exact ho V (mem_of_mem_erase hv) W (mem_of_mem_erase hw) g
  have h := hm.2 _ _ hr (by
    intro Z hz
    rcases hz with hl | hm'
    · rcases mem_cons.mp hl with rfl | hz
      · exact Or.inr (Or.inr ⟨X, Or.inl hx, hq⟩)
      · exact Or.inl (mem_of_mem_erase hz)
    · rcases mem_cons.mp hm' with rfl | hz
      · exact Or.inr (Or.inr ⟨Y, Or.inr hy, hk⟩)
      · exact Or.inr (Or.inl (mem_of_mem_erase hz)))
  rw [← ha, ← hb] at h
  simp [complexity] at h
  have h₁ := Nat.pow_lt_pow_left hq (by decide : 2 ≠ 0)
  have h₂ := Nat.pow_lt_pow_left hk (by decide : 2 ≠ 0)
  omega

theorem Minimal.swap {L M : Family R} (hm : Minimal L M) : Minimal M L :=
  ⟨⟨hm.1.classes.symm, hm.1.nonzero.symm, hm.reverse⟩, fun A B hr hb ↦
    (Nat.add_comm _ _).trans_le (hm.2 A B hr (by simpa [Below, or_comm, or_left_comm, or_assoc] using hb))⟩

private theorem nonzero_piece {A U V : FGModuleCat.{u} R} (hn : ¬ IsZero A)
    (hc : GrothendieckGroup.of A = GrothendieckGroup.of U + GrothendieckGroup.of V) :
    ¬ IsZero U ∨ ¬ IsZero V := by
  by_contra! h
  apply FGModuleCat.class_ne_zero hn
  simpa [GrothendieckGroup.of_isZero h.1, GrothendieckGroup.of_isZero h.2] using hc

/-- Every nonzero map between members on the same side of a minimal
relation is invertible. Repeated occurrences are allowed. -/
theorem Minimal.isIso {L M : Family R} (hm : Minimal L M) {X Y : FGModuleCat.{u} R}
    (hx : X ∈ L) (hy : Y ∈ L) (f : X ⟶ Y) (hf : f ≠ 0) : IsIso f := by
  classical
  by_contra hni
  by_cases hep : Epi f
  · obtain ⟨U, V, i, j, _, _, hc, ht⟩ := exists_subobject_split_of_epi f hf hni
    let A := L.erase X
    have ha : X ::ₘ A = L := cons_erase hx
    have hr : Relation M (U ::ₘ V ::ₘ A) := by
      constructor
      · have he := hm.1.classes.symm
        rw [← ha] at he
        simpa [totalClass, hc, add_assoc] using he
      · apply Or.inr
        exact (nonzero_piece (fun hz ↦ hf (hz.eq_of_src f 0)) hc).elim
          (fun h ↦ ⟨U, by simp, h⟩) (fun h ↦ ⟨V, by simp, h⟩)
      · intro B hb W hw g
        rcases mem_cons.mp hw with rfl | hw
        · apply (cancel_mono i).mp
          simpa using hm.reverse B hb X hx (g ≫ i)
        rcases mem_cons.mp hw with rfl | hw
        · apply (cancel_mono j).mp
          simpa using hm.reverse B hb Y hy (g ≫ j)
        exact hm.reverse B hb W (mem_of_mem_erase hw) g
    have hsplit (Z) (hz : Z ∈ U ::ₘ V ::ₘ A) : Below L M Z := by
      rcases mem_cons.mp hz with rfl | hz
      · exact Or.inr (Or.inr ⟨X, Or.inl hx, by
          by_contra! h
          have := Nat.pow_le_pow_left h 2
          omega⟩)
      rcases mem_cons.mp hz with rfl | hz
      · exact Or.inr (Or.inr ⟨X, Or.inl hx, by
          by_contra! h
          have := Nat.pow_le_pow_left h 2
          omega⟩)
      exact Or.inl (mem_of_mem_erase hz)
    have h := hm.2 _ _ hr (fun Z hz ↦ hz.elim (fun h ↦ Or.inr (Or.inl h)) (hsplit Z))
    rw [← ha] at h
    simp [complexity] at h
    omega
  · obtain ⟨U, V, p, q, _, _, hc, ht⟩ := exists_quotient_split_of_not_epi f hf hep
    let A := L.erase Y
    have ha : Y ::ₘ A = L := cons_erase hy
    have hr : Relation (U ::ₘ V ::ₘ A) M := by
      constructor
      · have he := hm.1.classes
        rw [← ha] at he
        simpa [totalClass, hc, add_assoc] using he
      · apply Or.inl
        exact (nonzero_piece (fun hz ↦ hf (hz.eq_of_tgt f 0)) hc).elim
          (fun h ↦ ⟨U, by simp, h⟩) (fun h ↦ ⟨V, by simp, h⟩)
      · intro W hw B hb g
        rcases mem_cons.mp hw with rfl | hw
        · apply (cancel_epi p).mp
          simpa using hm.1.orthogonal X hx B hb (p ≫ g)
        rcases mem_cons.mp hw with rfl | hw
        · apply (cancel_epi q).mp
          simpa using hm.1.orthogonal Y hy B hb (q ≫ g)
        exact hm.1.orthogonal W (mem_of_mem_erase hw) B hb g
    have hsplit (Z) (hz : Z ∈ U ::ₘ V ::ₘ A) : Below L M Z := by
      rcases mem_cons.mp hz with rfl | hz
      · exact Or.inr (Or.inr ⟨Y, Or.inl hy, by
          by_contra! h
          have := Nat.pow_le_pow_left h 2
          omega⟩)
      rcases mem_cons.mp hz with rfl | hz
      · exact Or.inr (Or.inr ⟨Y, Or.inl hy, by
          by_contra! h
          have := Nat.pow_le_pow_left h 2
          omega⟩)
      exact Or.inl (mem_of_mem_erase hz)
    have h := hm.2 _ _ hr (fun Z hz ↦ hz.elim (hsplit Z) (fun h ↦ Or.inr (Or.inl h)))
    rw [← ha] at h
    simp [complexity] at h
    omega

end FamilyExtraction

end EFiniteCharacterizations
