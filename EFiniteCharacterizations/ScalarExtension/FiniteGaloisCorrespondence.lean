module

public import EFiniteCharacterizations.ScalarExtension.GaloisWitnessFibres

/-! # Stable modules and Galois orbits over finite extensions -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations.FieldExtension

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R] [Module.Finite k F] [IsNoetherianRing R] [IsNoetherianRing (ExtendedAlgebra k F R)]
local notation "A" => ExtendedAlgebra k F R

omit [IsNoetherianRing R] in
private theorem exists_component {M S : FGModuleCat.{u} R} {n : ℕ}
    (f : M ⟶ FGModuleCat.of R (Fin n → S)) (hf : f ≠ 0) : ∃ l : M ⟶ S, l ≠ 0 := by
  by_contra! h
  apply hf
  ext x j
  let p : FGModuleCat.of R (Fin n → S) ⟶ S := FGModuleCat.ofHom (LinearMap.proj j)
  exact congrArg (fun l : M ⟶ S ↦ l.hom.hom x) (h (f ≫ p))

/-- The ground isomorphism class associated to a stable extension module is
characterized by admitting a nonzero map into the restriction. -/
theorem exists_unique_ground_stable_class (P : TwoTerm R) (B : FGModuleCat.{u} A)
    (hb : ((extendTwoTerm k F R P).eulerWeight F).IsStable B) :
    ∃ S : FGModuleCat.{u} R, (P.eulerWeight k).IsStable S ∧
      (∃ f : S ⟶ restrictObj k F R B, f ≠ 0) ∧
      ∀ T : FGModuleCat.{u} R, (P.eulerWeight k).IsStable T → (∃ f : T ⟶ restrictObj k F R B, f ≠ 0) →
        Nonempty (T ≅ S) := by
  obtain ⟨S,i,hi,hs,_⟩ := exists_stable_subobject_restrictObj k F R P B hb
  have hn : i ≠ 0 := fun eq ↦ hs.1 ((IsZero.iff_id_eq_zero _).2 ((cancel_mono i).1 (by simp [eq])))
  obtain ⟨m,_,_,⟨e⟩⟩ := restrict_stable_is_power k F P hs hb i hn
  refine ⟨S,hs,⟨i,hn⟩,?_⟩
  rintro T ht ⟨f,hf⟩
  obtain ⟨l,hl⟩ := exists_component R (f ≫ e.hom) (fun h ↦ hf ((cancel_mono e.hom).1 (h.trans zero_comp.symm)))
  have := Weight.isIso_of_nonzero ht hs l hl
  exact ⟨asIso l⟩

/-- Every stable ground module has a stable extension module lying over it. -/
theorem exists_stable_extension_witness (P : TwoTerm R) (S : FGModuleCat.{u} R)
    (hs : (P.eulerWeight k).IsStable S) :
    ∃ B : FGModuleCat.{u} A, ((extendTwoTerm k F R P).eulerWeight F).IsStable B ∧
      ∃ f : S ⟶ restrictObj k F R B, f ≠ 0 := by
  let X := extendObj k F R S
  have hX := isSemistable_extendObj k F R P S hs.isSemistable
  have hpos := dimensionWeight_pos k S hs.1
  rw [dimensionWeight_eval,Int.natCast_pos] at hpos
  have hn : ¬ IsZero X := by
    intro hz
    have h := (dimensionWeight (R := A) F).eval_isZero hz
    rw [dimensionWeight_eval,finrank_extendObj] at h
    omega
  obtain ⟨B,i,hi,hb⟩ := hX.exists_stable_subobject F hn
  obtain ⟨T,t,ht,hT,_⟩ := exists_stable_subobject_restrictObj k F R P B hb
  let e := (restrictExtendBasisEquiv k F R (Module.finBasis k F) S).toFGModuleCatIso
  let f : T ⟶ FGModuleCat.of R (Fin (Module.finrank k F) → S) := t ≫ (restrict k F R).map i ≫ e.hom
  have hf : Function.Injective f.hom.hom := ((FGModuleCat.isIso_iff_bijective e.hom).1 inferInstance).1.comp
    (((FGModuleCat.mono_iff_injective i).1 hi).comp ((FGModuleCat.mono_iff_injective t).1 ht))
  have : Mono f := (FGModuleCat.mono_iff_injective f).2 hf
  obtain ⟨l,hl⟩ := exists_component R f (fun he ↦ hT.1 ((IsZero.iff_id_eq_zero T).2
    ((cancel_mono f).1 (by simp [he]))))
  have := Weight.isIso_of_nonzero hT hs l hl
  refine ⟨B,hb,inv l ≫ t,fun he ↦ hT.1 ?_⟩
  have ht₀ : t = 0 := by simpa using congrArg (l ≫ ·) he
  exact (IsZero.iff_id_eq_zero _).2 ((cancel_mono t).1 (by simp [ht₀]))

/-- On stable extension modules, equality of the associated ground class
is exactly Galois conjugacy. -/
theorem same_ground_class_iff_galois_conjugate [IsGalois k F] (P : TwoTerm R)
    {X Y : FGModuleCat.{u} A} {S T : FGModuleCat.{u} R}
    (hx : ((extendTwoTerm k F R P).eulerWeight F).IsStable X)
    (hy : ((extendTwoTerm k F R P).eulerWeight F).IsStable Y)
    (hs : (P.eulerWeight k).IsStable S) (ht : (P.eulerWeight k).IsStable T)
    (f : S ⟶ restrictObj k F R X) (hf : f ≠ 0) (g : T ⟶ restrictObj k F R Y) (hg : g ≠ 0) :
    Nonempty (S ≅ T) ↔ ∃ (σ : Gal(F/k)) (v : restrictObj k F R X ⟶ restrictObj k F R Y),
      IsGaloisHom k F R σ v ∧ Function.Bijective v.hom.hom := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨m,hm,_,⟨eX⟩⟩ := restrict_stable_is_power k F P hs hx f hf
    let π : FGModuleCat.of R (Fin m → S) ⟶ S := FGModuleCat.ofHom (LinearMap.proj (⟨0,hm⟩ : Fin m))
    let a : S ⟶ FGModuleCat.of R (Fin m → S) := FGModuleCat.ofHom (LinearMap.pi (fun _ ↦ LinearMap.id))
    have ha : a ≫ π = 𝟙 S := rfl
    have hn : eX.hom ≫ π ≫ e.hom ≫ g ≠ 0 := by
      intro he
      apply hg
      have h := congrArg ((e.inv ≫ a ≫ eX.inv) ≫ ·) he
      simpa only [Category.assoc,Iso.inv_hom_id_assoc,comp_zero,← Category.assoc a π,ha,Category.id_comp] using h
    obtain ⟨σ,v,hv,hσ⟩ := exists_galoisHom k F R _ hn
    exact ⟨σ,v,hσ,bijective_of_galoisHom k F R hv hσ hx hy
      ((isSemistable_restrictObj_iff k F R P X).2 hx.isSemistable)
      ((isSemistable_restrictObj_iff k F R P Y).2 hy.isSemistable)⟩
  · rintro ⟨σ,v,_,hv⟩
    let _ : Mono v := (FGModuleCat.mono_iff_injective v).2 hv.1
    obtain ⟨U,_,_,hu⟩ := exists_unique_ground_stable_class k F R P Y hy
    obtain ⟨e⟩ := hu S hs ⟨f ≫ v,fun he ↦ hf ((cancel_mono v).1 (he.trans zero_comp.symm))⟩
    obtain ⟨e'⟩ := hu T ht ⟨g,hg⟩
    exact ⟨e.trans e'.symm⟩

/-- Over a finite Galois extension, stable extension modules map onto the
ground stable isomorphism classes, with fibres exactly the Galois orbits.
The class of a module is the unique stable ground subobject of its restriction
up to isomorphism. -/
theorem finite_galois_stable_correspondence [IsGalois k F] (P : TwoTerm R) :
    let ExtStable := {B : FGModuleCat.{u} A // ((extendTwoTerm k F R P).eulerWeight F).IsStable B}
    let GroundStable := {c : Skeleton (FGModuleCat.{u} R) // (P.eulerWeight k).IsStable ((fromSkeleton _).obj c)}
    ∃ φ : ExtStable → GroundStable, Function.Surjective φ ∧
      (∀ B, ∃ l : (fromSkeleton _).obj (φ B).val ⟶ restrictObj k F R B.val, l ≠ 0) ∧
      ∀ B C, φ B = φ C ↔ ∃ (σ : Gal(F/k)) (v : restrictObj k F R B.val ⟶ restrictObj k F R C.val),
        IsGaloisHom k F R σ v ∧ Function.Bijective v.hom.hom := by
  classical
  let E := {B : FGModuleCat.{u} A // ((extendTwoTerm k F R P).eulerWeight F).IsStable B}
  let G := {c : Skeleton (FGModuleCat.{u} R) // (P.eulerWeight k).IsStable ((fromSkeleton _).obj c)}
  choose S hs lift unique using fun B : E ↦ exists_unique_ground_stable_class k F R P B.val B.property
  let φ (B : E) : G := ⟨toSkeleton (S B),(hs B).of_iso (fromSkeletonToSkeletonIso (S B)).symm⟩
  refine ⟨φ,?_,?_,?_⟩
  · intro c
    obtain ⟨B,hB,l,hl⟩ := exists_stable_extension_witness k F R P _ c.property
    let i : E := ⟨B,hB⟩
    obtain ⟨e⟩ := unique i _ c.property ⟨l,hl⟩
    exact ⟨i,Subtype.ext ((congr_toSkeleton_of_iso e).symm.trans (toSkeleton_fromSkeleton_obj c.val))⟩
  · intro B
    obtain ⟨f,hf⟩ := lift B
    let e := fromSkeletonToSkeletonIso (S B)
    exact ⟨e.hom ≫ f,fun he ↦ hf ((cancel_epi e.hom).1 (he.trans comp_zero.symm))⟩
  · intro B C
    obtain ⟨f,hf⟩ := lift B
    obtain ⟨g,hg⟩ := lift C
    have h := same_ground_class_iff_galois_conjugate k F R P B.property C.property (hs B) (hs C) f hf g hg
    exact (Subtype.ext_iff.trans toSkeleton_eq_toSkeleton_iff).trans h

end EFiniteCharacterizations.FieldExtension
