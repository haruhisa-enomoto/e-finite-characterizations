module

public import EFiniteCharacterizations.Modules.Bricks

/-! # Images of minimal length -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace EFiniteCharacterizations

variable {R : Type*} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]

open EFiniteCharacterizations.FGModuleCat

private theorem moduleLength_image_lt_of_not_isIso {B : FGModuleCat R} (g : B ⟶ B)
    (hg : ¬ IsIso g) : moduleLength (image g) < moduleLength B := by
  by_cases h : IsIso (image.ι g)
  · apply moduleLength_lt_of_epi (factorThruImage g)
    intro hp
    exact hg (by rw [← image.fac g]; infer_instance)
  · exact moduleLength_lt_of_mono (image.ι g) h

/-- A nonzero map with minimal image length has a brick as its image. -/
theorem isBrick_image_of_minimal {X Y : FGModuleCat R} (f : X ⟶ Y) (hf : f ≠ 0)
    (hmin : ∀ g : X ⟶ Y, g ≠ 0 → moduleLength (image f) ≤ moduleLength (image g)) :
    IsBrick (image f) := by
  have hf' : ¬ IsZero (image f) := by
    intro h
    apply hf
    rw [← image.fac f, h.eq_of_tgt (factorThruImage f) 0, zero_comp]
  refine ⟨hf', ?_⟩
  intro g hg
  by_contra hgi
  let p := factorThruImage f
  let i := image.ι f
  let h := p ≫ g ≫ i
  have hne : h ≠ 0 := by
    intro hz
    have hz' : p ≫ (g ≫ i) = p ≫ 0 := by simpa [h] using hz
    apply hg
    apply (cancel_mono i).mp
    simpa using (cancel_epi p).mp hz'
  let e : image g ≅ image h :=
    image.isoStrongEpiMono (p ≫ factorThruImage g) (image.ι g ≫ i) (by simp [h])
  have hl := moduleLength_eq_of_iso e
  have hlt := moduleLength_image_lt_of_not_isIso g hgi
  exact (not_lt_of_ge (hmin h hne)) (hl ▸ hlt)

/-- A nonzero Hom space has a map whose image is a brick of minimum length. -/
theorem exists_minimal_image_brick {X Y : FGModuleCat R} (h : ∃ f : X ⟶ Y, f ≠ 0) :
    ∃ f : X ⟶ Y, f ≠ 0 ∧ IsBrick (image f) ∧
      ∀ g : X ⟶ Y, g ≠ 0 → moduleLength (image f) ≤ moduleLength (image g) := by
  classical
  have hlen : ∃ n : ℕ, ∃ f : X ⟶ Y, f ≠ 0 ∧ moduleLength (image f) = n := by
    obtain ⟨f, hf⟩ := h
    exact ⟨_, f, hf, rfl⟩
  obtain ⟨f, hf, heq⟩ := Nat.find_spec hlen
  have hmin (g : X ⟶ Y) (hg : g ≠ 0) : moduleLength (image f) ≤ moduleLength (image g) :=
    heq.trans_le (Nat.find_min' hlen ⟨g, hg, rfl⟩)
  exact ⟨f, hf, isBrick_image_of_minimal f hf hmin, hmin⟩

omit [IsArtinianRing R] in
/-- A map from the source to a proper subobject of a minimal image must vanish. -/
theorem hom_to_proper_subobject_of_minimal_image_size {X Y : FGModuleCat R} (f : X ⟶ Y)
    (size : FGModuleCat R → ℕ)
    (hiso : ∀ {A B : FGModuleCat R}, (A ≅ B) → size A = size B)
    (hstrict : ∀ {A B : FGModuleCat R} (a : A ⟶ B) [Mono a], ¬ IsIso a → size A < size B)
    (hmin : ∀ g : X ⟶ Y, g ≠ 0 → size (image f) ≤ size (image g))
    {L : FGModuleCat R} (i : L ⟶ image f) [Mono i] (hi : ¬ IsIso i) (g : X ⟶ L) :
    g = 0 := by
  by_contra hg
  let m := i ≫ image.ι f
  let h := g ≫ m
  have hne : h ≠ 0 := by
    intro hz
    apply hg
    exact (cancel_mono m).mp (hz.trans (zero_comp).symm)
  let e : image g ≅ image h :=
    image.isoStrongEpiMono (factorThruImage g) (image.ι g ≫ m) (by simp [h])
  have hproper : ¬ IsIso (image.ι g ≫ i) := by
    intro hiso
    have : Epi i := epi_of_epi (image.ι g) i
    exact hi (isIso_of_mono_of_epi i)
  have hlt := hstrict (image.ι g ≫ i) hproper
  rw [hiso e] at hlt
  exact (not_lt_of_ge (hmin h hne)) hlt

theorem hom_to_proper_subobject_of_minimal_image {X Y : FGModuleCat R} (f : X ⟶ Y)
    (hmin : ∀ g : X ⟶ Y, g ≠ 0 → moduleLength (image f) ≤ moduleLength (image g))
    {L : FGModuleCat R} (i : L ⟶ image f) [Mono i] (hi : ¬ IsIso i) (g : X ⟶ L) :
    g = 0 :=
  hom_to_proper_subobject_of_minimal_image_size f moduleLength
    (fun e ↦ moduleLength_eq_of_iso e) (fun a _ h ↦ moduleLength_lt_of_mono a h) hmin i hi g

omit [IsArtinianRing R] in
/-- A map from a proper quotient of a minimal image to the target must vanish. -/
theorem hom_from_proper_quotient_of_minimal_image_size {X Y : FGModuleCat R} (f : X ⟶ Y)
    (size : FGModuleCat R → ℕ)
    (hiso : ∀ {A B : FGModuleCat R}, (A ≅ B) → size A = size B)
    (hstrict : ∀ {A B : FGModuleCat R} (a : A ⟶ B) [Epi a], ¬ IsIso a → size B < size A)
    (hmin : ∀ g : X ⟶ Y, g ≠ 0 → size (image f) ≤ size (image g))
    {Q : FGModuleCat R} (q : image f ⟶ Q) [Epi q] (hq : ¬ IsIso q) (g : Q ⟶ Y) :
    g = 0 := by
  by_contra hg
  let p := factorThruImage f ≫ q
  have : Epi p := epi_comp (factorThruImage f) q
  let h := p ≫ g
  have hne : h ≠ 0 := by
    intro hz
    apply hg
    exact (cancel_epi p).mp (hz.trans (comp_zero).symm)
  have : StrongEpi (p ≫ factorThruImage g) := strongEpi_of_epi _
  let e : image g ≅ image h :=
    image.isoStrongEpiMono (p ≫ factorThruImage g) (image.ι g) (by simp [h])
  have hproper : ¬ IsIso (q ≫ factorThruImage g) := by
    intro hiso
    have : Mono q := mono_of_mono q (factorThruImage g)
    exact hq (isIso_of_mono_of_epi q)
  have hlt := hstrict (q ≫ factorThruImage g) hproper
  rw [hiso e] at hlt
  exact (not_lt_of_ge (hmin h hne)) hlt

theorem hom_from_proper_quotient_of_minimal_image {X Y : FGModuleCat R} (f : X ⟶ Y)
    (hmin : ∀ g : X ⟶ Y, g ≠ 0 → moduleLength (image f) ≤ moduleLength (image g))
    {Q : FGModuleCat R} (q : image f ⟶ Q) [Epi q] (hq : ¬ IsIso q) (g : Q ⟶ Y) :
    g = 0 :=
  hom_from_proper_quotient_of_minimal_image_size f moduleLength
    (fun e ↦ moduleLength_eq_of_iso e) (fun a _ h ↦ moduleLength_lt_of_epi a h) hmin q hq g

end EFiniteCharacterizations
