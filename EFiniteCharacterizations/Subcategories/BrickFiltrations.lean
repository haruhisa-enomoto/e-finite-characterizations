module

public import EFiniteCharacterizations.Subcategories.WideSimpleSupport
public import EFiniteCharacterizations.Characterizations.FixedClassFiniteness
public import EFiniteCharacterizations.Stability.SemistableSimples

/-! # The subcategory filtered by one brick -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]

/-- Objects with a finite filtration whose successive quotients are all
isomorphic to the prescribed module. -/
inductive FilteredBy (B : FGModuleCat.{u} R) : FGModuleCat.{u} R → Prop where
  | zero {X} (h : IsZero X) : FilteredBy B X
  | cons {S X Q} (s : ExtensionSequence S X Q) (e : S ≅ B) (hq : FilteredBy B Q) : FilteredBy B X

omit [IsArtinianRing R] in
theorem FilteredBy.of_iso {A B X Y : FGModuleCat.{u} R} (h : FilteredBy A X)
    (a : A ≅ B) (e : X ≅ Y) : FilteredBy B Y := by
  induction h generalizing Y with
  | zero hz => exact .zero (hz.of_iso e.symm)
  | cons row b _ ih =>
    exact .cons (row.ofIso (Iso.refl _) e (Iso.refl _)) (b ≪≫ a) (ih (Iso.refl _))

omit [IsArtinianRing R] in
theorem FilteredBy.extension {B A X Q : FGModuleCat.{u} R} (hA : FilteredBy B A)
    (s : ExtensionSequence A X Q) (hQ : FilteredBy B Q) : FilteredBy B X := by
  induction hA generalizing X with
  | zero hz =>
    have : IsIso s.p := s.shortExact.isIso_g_iff.2 hz
    exact hQ.of_iso (Iso.refl _) (asIso s.p).symm
  | @cons S A D row e _ ih =>
    let t := ExtensionSequence.quotient (row.i ≫ s.i)
    let q := ExtensionSequence.quotientRows (ExtensionSequence.idLeft S) s row t (ExtensionSequence.idRight Q)
      (by simp [t, ExtensionSequence.quotient, ExtensionSequence.idLeft])
      (by simp [t, ExtensionSequence.quotient, ExtensionSequence.idLeft, ExtensionSequence.idRight, s.w])
    exact .cons t e (ih q)

open IsWideClass in
theorem isWideClass_filteredBy_of_stable {θ : Weight (FGModuleCat.{u} R)} {B : FGModuleCat.{u} R}
    (hb : θ.IsStable B) : IsWideClass (FilteredBy B) := by
  let W : ObjectProperty (FGModuleCat.{u} R) := θ.IsSemistable
  let _ : Fact (IsWideClass W) := ⟨θ.isWideClass_semistable⟩
  let s := ({toSkeleton B} : Set _)
  let V := supportedOn W s
  have hv : IsWideClass V := isWideClass_supportedOn s
  have hsimple := (simple_iff_simpleMember (⟨B,hb.isSemistable⟩ : W.FullSubcategory)).1
    ((θ.isStable_iff_simple _).1 hb)
  have hB : V B := (supportedOn_iff_of_simpleMember s hsimple).2 (by simp [s])
  suffices hf : (FilteredBy B : ObjectProperty _) = V from hf ▸ hv
  funext X
  apply propext
  constructor
  · intro h
    induction h with
    | zero hz => exact hv.zero_mem _ hz
    | cons row e _ ih => exact hv.extension_mem _ row.shortExact (hv.iso_mem e.symm hB) ih
  · rintro ⟨hx,l,hl,hmem⟩
    let P (Y : W.FullSubcategory) (q : Multiset (Skeleton W.FullSubcategory)) :=
      (∀ x ∈ q, W.ι.mapSkeleton.obj x ∈ s) → FilteredBy B Y.obj
    suffices hh : ∀ (Y : W.FullSubcategory) (q), HasCompositionFactors Y q → P Y q from hh ⟨X,hx⟩ l hl hmem
    intro Y q hq
    induction hq with
    | zero hz => exact fun _ ↦ .zero ((IsZero.iff_id_eq_zero _).2 (W.ι.congr_map ((IsZero.iff_id_eq_zero _).1 hz)))
    | @cons S M D q row _ _ ih =>
      intro h
      have he : toSkeleton S.obj = toSkeleton B := by
        simpa [s,Functor.mapSkeleton_obj_toSkeleton] using h (toSkeleton S) (Multiset.mem_cons_self ..)
      obtain ⟨e⟩ := toSkeleton_eq_toSkeleton_iff.1 he
      have hrow := row.shortExact.map_of_exact W.ι
      exact .cons ⟨W.ι.map row.i,W.ι.map row.p,by simpa using W.ι.congr_map row.w,hrow⟩ e
        (ih (fun x hx ↦ h x (Multiset.mem_cons_of_mem hx)))

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
theorem functoriallyFinite_filteredBy_of_isEFinite (he : IsEFinite R) (B : FGModuleCat.{u} R)
    (hb : IsBrick B) : FunctoriallyFinite (FilteredBy B) := by
  obtain ⟨_,hs⟩ := exists_projective_weight_stable_of_isEFinite k he hb
  exact (isEFinite_iff_functoriallyFinite_wideClasses k).1 he _ (isWideClass_filteredBy_of_stable hs)

end EFiniteCharacterizations
