module

public import EFiniteCharacterizations.GrothendieckGroups.GrothendieckMonoid
public import EFiniteCharacterizations.GrothendieckGroups.WideGrothendieckEquivalence
public import EFiniteCharacterizations.Subcategories.TorsionApproximations
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

/-! # Detecting a missing projective class on a numerical torsion-class monoid -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u
namespace EFiniteCharacterizations

open IsWideClass

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]

omit [IsArtinianRing R] in
/-- Two semistable objects that agree in the weak torsion-class monoid
already agree in the intrinsic Grothendieck group of semistables. -/
theorem semistable_class_eq_of_torsionMonoid_eq (θ : Weight (FGModuleCat.{u} R))
    {X Y : FGModuleCat.{u} R} (hx : θ.IsSemistable X) (hy : θ.IsSemistable Y)
    (e : GrothendieckMonoid.of θ.weakTorsionClass X ((Weight.isSemistable_iff_quotients X).1 hx).2 =
      GrothendieckMonoid.of θ.weakTorsionClass Y ((Weight.isSemistable_iff_quotients Y).1 hy).2) :
    GrothendieckGroup.of (⟨X,hx⟩ : θ.semistableCategory) =
      GrothendieckGroup.of (⟨Y,hy⟩ : θ.semistableCategory) := by
  classical
  let W : ObjectProperty (FGModuleCat.{u} R) := θ.IsSemistable
  let _ : Fact (IsWideClass W) := ⟨θ.isWideClass_semistable⟩
  let f (Z : {Z // θ.weakTorsionClass Z}) : WithTop (GrothendieckGroup W.FullSubcategory) :=
    if h : W Z.val then ↑(GrothendieckGroup.of (⟨Z.val,h⟩ : W.FullSubcategory)) else ⊤
  have hz (Z) (h : IsZero Z.val) : f Z = 0 := by
    have hw := θ.isWideClass_semistable.zero_mem _ h
    have hzero : IsZero (⟨Z.val,hw⟩ : W.FullSubcategory) :=
      (IsZero.iff_id_eq_zero _).2 (W.ι.map_injective ((IsZero.iff_id_eq_zero _).1 h))
    simp [f,show W Z.val from hw,GrothendieckGroup.of_isZero hzero]
  have hi (Z U) (i : Z.val ≅ U.val) : f Z = f U := by
    by_cases ha : W Z.val
    · have hb := θ.isWideClass_semistable.iso_mem i ha
      simp only [f,ha,show W U.val from hb,dite_eq_left]
      exact congrArg _ (GrothendieckGroup.of_eq_of_iso (W.isoMk (X := ⟨_,ha⟩) (Y := ⟨_,hb⟩) i))
    · have hb : ¬ W U.val := fun h ↦ ha (θ.isWideClass_semistable.iso_mem i.symm h)
      simp [f,ha,hb]
  have he (S : ShortComplex (FGModuleCat.{u} R)) (hs : S.ShortExact)
      (a : θ.weakTorsionClass S.X₁) (b : θ.weakTorsionClass S.X₂) (c : θ.weakTorsionClass S.X₃) :
      f ⟨_,b⟩ = f ⟨_,a⟩ + f ⟨_,c⟩ := by
    have hiff (Z) (h : θ.weakTorsionClass Z) : W Z ↔ θ.eval Z = 0 :=
      ⟨fun hw ↦ hw.1, fun hzero ↦ (Weight.isSemistable_iff_quotients _).2 ⟨hzero,h⟩⟩
    have hsum := θ.eval_shortExact S hs
    have h₁ := a (𝟙 _)
    have h₃ := c (𝟙 _)
    by_cases hb : W S.X₂
    · have z := (hiff _ b).1 hb
      have ha := (hiff _ a).2 (by omega)
      have hc := (hiff _ c).2 (by omega)
      let t := liftExtension (W := W) S hs ha hb hc
      simpa only [f,ha,hb,hc,dite_eq_left,← WithTop.coe_add,WithTop.coe_inj] using
        GrothendieckGroup.of_shortExact (ShortComplex.mk t.i t.p t.w) t.shortExact
    · by_cases ha : W S.X₁
      · have hc : ¬ W S.X₃ := fun h ↦ hb (θ.isWideClass_semistable.extension_mem S hs ha h)
        simp [f,hb,hc]
      · simp [f,hb,ha]
  have eqv := congrArg (GrothendieckMonoid.lift θ.weakTorsionClass f hz hi he) e
  have eqf := (GrothendieckMonoid.lift_of θ.weakTorsionClass f hz hi he X
    ((Weight.isSemistable_iff_quotients X).1 hx).2).symm.trans (eqv.trans
      (GrothendieckMonoid.lift_of θ.weakTorsionClass f hz hi he Y ((Weight.isSemistable_iff_quotients Y).1 hy).2))
  simpa [f,show W X from hx,show W Y from hy] using eqf

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

theorem isEFinite_of_injective_weakTorsionMonoid
    (h : ∀ g : ProjectiveClass R, Function.Injective
      (GrothendieckMonoid.dimensionMap (projectiveClassWeight k g).weakTorsionClass)) : IsEFinite R := by
  classical
  by_contra hn
  obtain ⟨g,X,Y,sx,sy,hniso,hxy⟩ := exists_equalClass_stable_pair_allFields k hn
  let θ := projectiveClassWeight (R := R) k g
  let W : ObjectProperty (FGModuleCat.{u} R) := θ.IsSemistable
  let _ : Fact (IsWideClass W) := ⟨θ.isWideClass_semistable⟩
  let A : W.FullSubcategory := ⟨X,sx.isSemistable⟩
  let B : W.FullSubcategory := ⟨Y,sy.isSemistable⟩
  have : Simple A := (θ.isStable_iff_simple A).1 sx
  have : Simple B := (θ.isStable_iff_simple B).1 sy
  have eqv := semistable_class_eq_of_torsionMonoid_eq θ sx.isSemistable sy.isSemistable
    ((h g) ((GrothendieckMonoid.dimensionMap_of θ.weakTorsionClass X _).trans
      (hxy.trans (GrothendieckMonoid.dimensionMap_of θ.weakTorsionClass Y _).symm)))
  have hdiff : toSkeleton A ≠ toSkeleton B := fun he ↦ hniso
    ((toSkeleton_eq_toSkeleton_iff.1 he).map (fun (e : A ≅ B) ↦ W.ι.mapIso e))
  have hh := congrArg (simpleMultiplicity (exists_intrinsic_factors (W := W)) (toSkeleton A)) eqv
  change simpleMultiplicity _ _ (GrothendieckGroup.of A) =
    simpleMultiplicity _ _ (GrothendieckGroup.of B) at hh
  rw [simpleMultiplicity_of_simple, simpleMultiplicity_of_simple] at hh
  simp [hdiff] at hh

end EFiniteCharacterizations
