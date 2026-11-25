module

public import EFiniteCharacterizations.Silting.Fans.BrickFacets
public import EFiniteCharacterizations.Subcategories.BrickFiltrationEquivalences
public import EFiniteCharacterizations.Subcategories.CompactTorsionEquivalences
public import Mathlib.Order.Cover

/-!
# Brick labels of covers in the poset of functorially finite torsion classes

Theorem 5.1 (`thm:wide`, condition `(brick-label)` in Theorem A(I)) of the
manuscript: over an arbitrary field, `R` is E-finite if and only if every brick `B`
in `mod R` arises as the brick label `Filt(B) = U ∩ T⊥` of a cover `T ⋖ U` in the
poset `f-tors R` of functorially finite torsion classes (`isEFinite_iff_brickLabels`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
universe u
namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- Torsion classes in a finite module category are the left Hom perpendiculars.
The order on this subtype is inclusion of object properties. -/
abbrev FiniteTorsionPoset (R : Type u) [Ring R] [IsNoetherianRing R] :=
  {T : ObjectProperty (FGModuleCat.{u} R) //
    (∃ F, T = leftHomOrthogonal F) ∧ FunctoriallyFinite T}

/-- The heart interval `U ∩ T⊥` associated to a pair `T, U` of torsion classes. -/
def torsionInterval (T U : ObjectProperty (FGModuleCat.{u} R)) : ObjectProperty (FGModuleCat.{u} R) :=
  fun X ↦ U X ∧ ∀ Y, T Y → rightHomOrthogonal Y X

/-- Condition `(brick-label)`: every brick `B` satisfies `Filt(B) = U ∩ T⊥` for a cover `T ⋖ U`
in `FiniteTorsionPoset R`. -/
def BrickLabels (R : Type u) [Ring R] [IsNoetherianRing R] : Prop :=
  ∀ B : FGModuleCat.{u} R, IsBrick B → ∃ T U : FiniteTorsionPoset R,
    T ⋖ U ∧ FilteredBy B = torsionInterval T.val U.val

private theorem interval_covariantlyFinite (T U : FiniteTorsionPoset R) :
    CovariantlyFinite (torsionInterval T.val U.val) := by
  obtain ⟨F,hF⟩ := T.property.1
  obtain ⟨G,hG⟩ := U.property.1
  intro X
  obtain ⟨A,a,ha,ha'⟩ := U.property.2.1 X
  obtain ⟨L,Q,i,p,w,hL,hQ,hs⟩ := (isTorsionPair_generatedBy T.val).2 A
  have := hs.epi_g
  have hT : T.val L := by
    rw [hF]
    intro Z hz f
    exact hL Z (fun Y hy ↦ (hF ▸ hy : leftHomOrthogonal F Y) Z hz) f
  have hU : U.val Q := hG ▸ leftHomOrthogonal_of_epi p (hG ▸ ha : leftHomOrthogonal G A)
  refine ⟨Q,a ≫ p,⟨hU,hQ⟩,?_⟩
  intro Y hy b
  obtain ⟨c,hc⟩ := ha' Y hy.1 b
  obtain ⟨d,hd⟩ := CokernelCofork.IsColimit.desc' hs.gIsCokernel c (hy.2 L hT (i ≫ c))
  change p ≫ d = c at hd
  exact ⟨d,by rw [Category.assoc,hd,hc]⟩

private theorem FilteredBy.epi_to_factor {B X : FGModuleCat.{u} R} (hx : FilteredBy B X)
    (hn : ¬ IsZero X) : ∃ p : X ⟶ B, Epi p := by
  induction hx with
  | zero hz => exact (hn hz).elim
  | @cons S M Q s e _ ih =>
    by_cases hq : IsZero Q
    · have := s.shortExact.isIso_f_iff.2 hq
      exact ⟨inv s.i ≫ e.hom,inferInstance⟩
    · obtain ⟨p,_⟩ := ih hq
      exact ⟨s.p ≫ p,inferInstance⟩

private theorem kernelRow {X Y : FGModuleCat.{u} R} (p : X ⟶ Y) [Epi p] :
    (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) (by dsimp; infer_instance)
    (by dsimp; infer_instance)

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R] [IsArtinianRing R]

private theorem filteredBy_eq_semistable_of_unique {θ : Weight (FGModuleCat.{u} R)}
    {B : FGModuleCat.{u} R} (hb : θ.IsStable B) (hu : ∀ Y, θ.IsStable Y → Nonempty (B ≅ Y)) :
    (FilteredBy B : ObjectProperty _) = θ.IsSemistable := by
  funext X
  apply propext
  constructor
  · intro hx
    induction hx with
    | zero hz => exact θ.isWideClass_semistable.zero_mem _ hz
    | cons s e _ ih => exact θ.isWideClass_semistable.extension_mem _ s.shortExact ((hb.of_iso e.symm).isSemistable) ih
  · intro hx
    refine θ.isWideClass_semistable.extension_induction (FilteredBy B) (fun _ hz ↦ .zero hz) ?_ hx
    intro S hs hsimple _ ih
    let W : ObjectProperty (FGModuleCat.{u} R) := θ.IsSemistable
    let _ : Fact (IsWideClass W) := ⟨θ.isWideClass_semistable⟩
    have hstable := (θ.isStable_iff_simple ⟨_,hsimple.1⟩).2
      ((IsWideClass.simple_iff_simpleMember (W := W) _).2 hsimple)
    obtain ⟨e⟩ := hu _ hstable
    exact .cons ⟨S.f,S.g,S.zero,hs⟩ e.symm ih

include k in
theorem brickLabels_of_isEFinite (h : IsEFinite R) : BrickLabels R := by
  classical
  intro B hb
  obtain ⟨P,hp,_,hs,hunique⟩ := exists_unique_stable_presilting_facet k h hb
  let θ := P.eulerWeight k
  have hfil := filteredBy_eq_semistable_of_unique hs hunique
  have hweak := (isEFinite_iff_functoriallyFinite_weakTorsion k).1 h P.projectiveClass
  have hstrict := (isEFinite_iff_functoriallyFinite_strictTorsion k).1 h P.projectiveClass
  rw [P.projectiveClassWeight_eq_eulerWeight k] at hweak hstrict
  let T : FiniteTorsionPoset R := ⟨θ.strictTorsionClass,
    ⟨_,strictTorsionClass_eq_leftOrthogonal k θ⟩,hstrict⟩
  have hperp : θ.weakTorsionClass = leftHomOrthogonal (fun Z ↦ Z = P.nakayamaKernel k) := by
    funext X
    apply propext
    rw [show θ.weakTorsionClass X ↔ Subsingleton (X ⟶ P.nakayamaKernel k) from
      P.nonneg_eulerWeight_all_quotients_iff k hp X]
    exact ⟨fun hh _ he ↦ he ▸ fun f ↦ hh.elim f 0, fun hh ↦ ⟨fun a b ↦ (hh _ rfl a).trans (hh _ rfl b).symm⟩⟩
  let U : FiniteTorsionPoset R := ⟨θ.weakTorsionClass,⟨_,hperp⟩,hweak⟩
  have hle : T ≤ U := by
    intro X hx Q q hq
    by_cases hz : IsZero Q
    · exact (θ.eval_isZero hz).ge
    · exact (hx q hz).le
  have hBU : U.val B := ((Weight.isSemistable_iff_quotients _).1 hs.isSemistable).2
  have hBT : ¬ T.val B := fun ht ↦ (ht (𝟙 B) hs.1).ne' hs.2.1
  have hlt : T < U := lt_of_le_not_ge hle (fun rev ↦ hBT (rev _ hBU))
  have hdec (X) (hx : U.val X) : ∃ (Q : FGModuleCat.{u} R) (p : X ⟶ Q),
      Epi p ∧ T.val (kernel p) ∧ FilteredBy B Q := by
    obtain ⟨Q,p,he,hK,hQ⟩ := θ.exists_strict_torsion_decomposition k X
    have hsemi : θ.IsSemistable Q := ⟨le_antisymm (hQ (𝟙 Q)) (hx p),hQ⟩
    exact ⟨Q,p,he,hK,hfil ▸ hsemi⟩
  refine ⟨T,U,⟨hlt,?_⟩,?_⟩
  · intro V hTV hVU
    obtain ⟨F,he⟩ := V.property.1
    have hB : V.val B := by
      by_contra hbad
      apply hTV.not_ge
      intro X hx
      obtain ⟨Q,p,_,hk,hq⟩ := hdec X (hVU.le _ hx)
      by_cases hz : IsZero Q
      · have := (kernelRow p).isIso_f_iff.2 hz
        intro q hq hn
        exact hk (kernel.ι p ≫ q) hn
      obtain ⟨q,_⟩ := hq.epi_to_factor hz
      exact (hbad (he ▸ leftHomOrthogonal_of_epi (p ≫ q) (he ▸ hx : leftHomOrthogonal F X))).elim
    apply hVU.not_ge
    intro X hx
    obtain ⟨Q,p,hp,hk,hq⟩ := hdec X hx
    have hvQ : leftHomOrthogonal F Q := by
      clear hk hp p
      clear * - hq he hB
      induction hq with
      | zero hz => exact fun _ _ f ↦ hz.eq_of_src f 0
      | cons row e _ ih =>
        exact leftHomOrthogonal_of_shortExact row.shortExact
          (leftHomOrthogonal_of_epi e.inv (he ▸ hB)) ih
    rw [he]
    exact leftHomOrthogonal_of_shortExact (kernelRow p)
      (he ▸ hTV.le _ hk) hvQ
  · funext X
    apply propext
    constructor
    · intro hx
      have hw : θ.IsSemistable X := hfil ▸ hx
      exact ⟨((Weight.isSemistable_iff_quotients _).1 hw).2,
        fun _ ht f ↦ Weight.strict_weak_hom_zero ht hw.2 f⟩
    · rintro ⟨hx,ho⟩
      obtain ⟨Q,p,hp,hk,hq⟩ := hdec X hx
      have hz : IsZero (kernel p) := (IsZero.iff_id_eq_zero _).2
        ((cancel_mono (kernel.ι p)).1 (by simp [ho _ hk (kernel.ι p)]))
      have := (kernelRow p).isIso_g_iff.2 hz
      exact hq.of_iso (Iso.refl _) (asIso p).symm

include k in
/-- **Theorem 5.1, `(E-fin) ⇔ (brick-label)`.** -/
theorem isEFinite_iff_brickLabels : IsEFinite R ↔ BrickLabels R := by
  refine ⟨brickLabels_of_isEFinite k,fun h ↦ (isEFinite_iff_covariantlyFinite_filteredBy k).2 ?_⟩
  intro B hb
  obtain ⟨T,U,_,he⟩ := h B hb
  rw [he]
  exact interval_covariantlyFinite T U

end EFiniteCharacterizations
