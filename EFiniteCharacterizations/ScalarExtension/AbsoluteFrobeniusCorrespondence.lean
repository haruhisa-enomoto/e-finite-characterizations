module

public import EFiniteCharacterizations.ScalarExtension.FiniteFieldOfDefinition
public import EFiniteCharacterizations.ScalarExtension.GeometricConstituents
public import EFiniteCharacterizations.ScalarExtension.StableFieldDescent

/-! # Absolute Frobenius orbits of stable modules over a finite field -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.FieldExtension

variable (k L R : Type u) [Field k] [Finite k] [Field L] [Algebra k L] [IsAlgClosed L]
  [Algebra.IsAlgebraic k L] [Ring R] [Algebra k R] [Module.Finite k R] [IsNoetherianRing R]
  [IsNoetherianRing (ExtendedAlgebra k L R)]

local notation "A" => ExtendedAlgebra k L R

omit [Finite k] [IsAlgClosed L] in
/-- Every geometric stable module occurs in the extension of a stable ground module. -/
theorem exists_ground_of_geometric_stable (P : TwoTerm R) (Y : FGModuleCat.{u} A)
    (hy : ((extendTwoTerm k L R P).eulerWeight L).IsStable Y) :
    ∃ S : FGModuleCat.{u} R, (P.eulerWeight k).IsStable S ∧ ∃ f : extendObj k L R S ⟶ Y, f ≠ 0 := by
  obtain ⟨E,hE,B,⟨e⟩⟩ := exists_finite_field_of_definition k L R Y
  let RK := ExtendedAlgebra k E R
  let _ := IsNoetherianRing.of_finite E RK
  let _ := IsNoetherianRing.of_finite L (ExtendedAlgebra E L RK)
  have hb := isStable_of_extendObj E L RK (extendTwoTerm k E R P)
    ((isStable_tower_iff k E L R P _).1 (hy.of_iso e.symm))
  obtain ⟨S,hs,⟨g,hg⟩,_⟩ := exists_unique_ground_stable_class k E R P B hb
  obtain ⟨p,hepi⟩ := exists_epi_of_hom_restrictObj k E R P hs.isSemistable hb g hg
  let G := (towerEquivalence k E L R).functor
  let q := extendMap E L RK p
  let _ : Epi q := (epi_extendMap_iff E L RK p).2 hepi
  let f := (towerExtendIso k E L R S).hom ≫ G.map q ≫ e.hom
  have _ : Epi f := inferInstanceAs (Epi ((towerExtendIso k E L R S).hom ≫ G.map q ≫ e.hom))
  exact ⟨S,hs,f,fun h ↦ hy.1 ((IsZero.iff_id_eq_zero _).2 ((cancel_epi f).1 (by simp [h])))⟩

/-- The orbit relation on stable modules over the algebraic closure. -/
def geometricStableSetoid (P : TwoTerm R) :
    Setoid {Y : FGModuleCat.{u} A // ((extendTwoTerm k L R P).eulerWeight L).IsStable Y} where
  r X Y := GaloisConjugate k L R X.val Y.val
  iseqv := ⟨fun X ↦ GaloisConjugate.refl X.val,fun h ↦ h.symm,fun h h' ↦ h.trans h'⟩

/-- Absolute Frobenius orbits of geometric stable modules are in bijection with
stable ground isomorphism classes. A ground class corresponds to the orbit of
a given geometric module exactly when that module is a quotient of its extension. -/
theorem absolute_frobenius_correspondence (P : TwoTerm R) :
    ∃ φ : Quotient (geometricStableSetoid k L R P) ≃
        {c : Skeleton (FGModuleCat.{u} R) // (P.eulerWeight k).IsStable ((fromSkeleton _).obj c)},
      ∀ Y S, φ (Quotient.mk _ Y) = S ↔
        ∃ f : extendObj k L R ((fromSkeleton _).obj S.val) ⟶ Y.val, f ≠ 0 := by
  classical
  let E := {Y : FGModuleCat.{u} A // ((extendTwoTerm k L R P).eulerWeight L).IsStable Y}
  let G := {c : Skeleton (FGModuleCat.{u} R) // (P.eulerWeight k).IsStable ((fromSkeleton _).obj c)}
  choose S hs lift using fun Y : E ↦ exists_ground_of_geometric_stable k L R P Y.val Y.property
  let φ (Y : E) : G := ⟨toSkeleton (S Y),(hs Y).of_iso (fromSkeletonToSkeletonIso _).symm⟩
  have key (Y : E) (c : G) : φ Y = c ↔ ∃ f : extendObj k L R ((fromSkeleton _).obj c.val) ⟶ Y.val, f ≠ 0 := by
    constructor
    · rintro rfl
      obtain ⟨f,hf⟩ := lift Y
      let a := (extend k L R).mapIso (fromSkeletonToSkeletonIso (S Y))
      exact ⟨a.hom ≫ f,fun h ↦ hf ((cancel_epi a.hom).1 (h.trans comp_zero.symm))⟩
    · rintro ⟨f,hf⟩
      obtain ⟨g,hg⟩ := lift Y
      obtain ⟨a⟩ := retract_of_geometric_stable_quotient k L R P (hs Y) Y.property g hg
      obtain ⟨b⟩ := retract_of_geometric_stable_quotient k L R P c.property Y.property f hf
      obtain ⟨e⟩ := ground_iso_of_common_constituent k L R P (hs Y) c.property Y.property.1 a b
      exact Subtype.ext ((congr_toSkeleton_of_iso e).trans (toSkeleton_fromSkeleton_obj c.val))
  have onto : Function.Surjective φ := by
    intro c
    obtain ⟨Y,hy,⟨a⟩,_⟩ := geometric_stable_orbit k L R P _ c.property
    exact ⟨⟨Y,hy⟩,(key _ _).2 ⟨a.r,fun h ↦ hy.1 ((IsZero.iff_id_eq_zero _).2 (by rw [← a.retract,h,comp_zero]))⟩⟩
  have fibre (Y Z : E) : GaloisConjugate k L R Y.val Z.val ↔ φ Y = φ Z := by
    constructor
    · intro hc
      obtain ⟨f,hf⟩ := (key Y _).1 rfl
      exact ((key Z _).2 (exists_map_of_conjugate k L R hc f hf)).symm
    · intro eq
      let c := φ Y
      obtain ⟨X,_,_,h⟩ := geometric_stable_orbit k L R P _ c.property
      exact ((h _ Y.property).1 ((key Y c).1 rfl)).symm.trans
        ((h _ Z.property).1 ((key Z c).1 eq.symm))
  let e : Quotient (geometricStableSetoid k L R P) ≃ Quotient (Setoid.ker φ) := Quotient.congrRight fibre
  exact ⟨e.trans (Setoid.quotientKerEquivOfSurjective φ onto),key⟩

end EFiniteCharacterizations.FieldExtension
