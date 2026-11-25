module

public import EFiniteCharacterizations.Presentations.RepresentProjectiveClass
public import EFiniteCharacterizations.Presentations.StableProjectiveTerms
public import EFiniteCharacterizations.LinearAlgebra.Dual.FiniteProjective
public import EFiniteCharacterizations.Modules.FiniteModuleMorphisms

/-! # Duality of finite projectives over a ring and its opposite -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MulOpposite

universe u

namespace EFiniteCharacterizations.FiniteProjective

variable {R : Type u} [Ring R]

/-- The opposite projective Hom(P,R), with right multiplication on its values. -/
abbrev star (P : FiniteProjective R) : FiniteProjective Rᵐᵒᵖ := by
  let _ := P.property
  exact ⟨FGModuleCat.of Rᵐᵒᵖ (Module.Dual R P.val),inferInstance⟩

/-- Transpose a morphism of finite projectives. -/
def transpose {P Q : FiniteProjective R} : (P.val ⟶ Q.val) →+ (Q.star.val ⟶ P.star.val) where
  toFun f := ObjectProperty.homMk (ModuleCat.ofHom (X := Q.star.val.obj) (Y := P.star.val.obj) (f.hom.hom.lcomp Rᵐᵒᵖ R))
  map_zero' := by ext φ x; exact φ.map_zero
  map_add' f g := by ext φ x; exact φ.map_add _ _

@[simp] theorem transpose_id (P : FiniteProjective R) : transpose (P := P) (Q := P) (𝟙 P.val) = 𝟙 P.star.val := rfl

@[simp] theorem transpose_comp {P Q T : FiniteProjective R} (f : P.val ⟶ Q.val) (g : Q.val ⟶ T.val) :
    transpose (P := P) (Q := T) (f ≫ g) = transpose (P := Q) (Q := T) g ≫ transpose (P := P) (Q := Q) f := rfl

/-- The transpose gives all maps in the opposite direction, uniquely. -/
theorem transpose_bijective (P Q : FiniteProjective R) : Function.Bijective (transpose (P := P) (Q := Q)) := by
  classical
  let _ := Q.property
  obtain ⟨n,b,φ,exp⟩ := exists_sum_dual_smul_eq (R := R) (M := Q.val)
  have expand (v : Module.Dual R Q.val) : ∑ j, op (v (b j)) • φ j = v := by
    ext y
    have h := congrArg v (exp y)
    simpa only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,op_smul_eq_mul,smul_eq_mul] using h
  constructor
  · intro f g he
    apply FGModuleCat.hom_ext
    ext x
    have hc (j) : φ j (f.hom.hom x) = φ j (g.hom.hom x) :=
      congrArg (fun h : Q.star.val ⟶ P.star.val ↦ (h.hom.hom (φ j) : Module.Dual R P.val) x) he
    rw [← exp (f.hom.hom x),← exp (g.hom.hom x)]
    simp_rw [hc]
  · intro h
    let f : P.val.obj →ₗ[R] Q.val.obj := ∑ j, (LinearMap.toSpanSingleton R Q.val (b j)).comp (h.hom.hom (φ j))
    refine ⟨FGModuleCat.ofHom f,?_⟩
    apply FGModuleCat.hom_ext
    ext v x
    change v (f x) = (h.hom.hom v : Module.Dual R P.val) x
    have hv := congrArg (fun z : Module.Dual R Q.val ↦ (h.hom.hom z : Module.Dual R P.val) x) (expand v)
    change (h.hom.hom (∑ j, op (v (b j)) • φ j) : Module.Dual R P.val) x = _ at hv
    rw [map_sum] at hv
    simp only [map_smul,LinearMap.sum_apply,LinearMap.smul_apply,op_smul_eq_mul] at hv
    simpa only [f,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.toSpanSingleton_apply,map_sum,map_smul,smul_eq_mul] using hv

/-- Every finite projective over the opposite ring is the dual of a finite
ground projective. Evaluation realizes the isomorphism. -/
theorem exists_star_iso (Q : FiniteProjective Rᵐᵒᵖ) :
    ∃ P : FiniteProjective R, Nonempty (P.star.val ≅ Q.val) := by
  classical
  let _ := Q.property
  obtain ⟨n,b,φ,exp⟩ := exists_sum_dual_smul_eq (R := Rᵐᵒᵖ) (M := Q.val)
  let W := Q.val.obj →ₗ[Rᵐᵒᵖ] R
  let un : Rᵐᵒᵖ →ₗ[Rᵐᵒᵖ] R :=
    { toFun := unop, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let ψ (i : Fin n) : W := un.comp (φ i)
  let coords : W →ₗ[R] (Fin n → R) := { toFun := fun w i ↦ w (b i), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let val : (Fin n → R) →ₗ[R] W := ∑ j, (LinearMap.toSpanSingleton R W (ψ j)).comp (LinearMap.proj j)
  have split : val.comp coords = LinearMap.id := by
    ext w x
    have h := congrArg w (exp x)
    change (val (coords w)) x = w x
    rw [show val (coords w) = ∑ i, w (b i) • ψ i from LinearMap.sum_apply ..,LinearMap.sum_apply]
    rw [map_sum] at h
    simp only [map_smul] at h
    exact h
  let _ : Module.Projective R W := Module.Projective.of_split coords val split
  let _ : Module.Finite R W := Module.Finite.of_surjective val (LinearMap.surjective_of_comp_eq_id coords val split)
  let P : FiniteProjective R := ⟨FGModuleCat.of R W,inferInstance⟩
  let ev : Q.val.obj →ₗ[Rᵐᵒᵖ] (Module.Dual R W) :=
    { toFun := fun q ↦ { toFun := fun w ↦ w q, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
      map_add' := fun _ _ ↦ LinearMap.ext (fun w ↦ w.map_add _ _)
      map_smul' := fun r q ↦ LinearMap.ext (fun w ↦ w.map_smul r q) }
  have bij : Function.Bijective ev := by
    constructor
    · intro x y he
      have hh (j) : φ j x = φ j y := unop_injective (congrArg (fun l : Module.Dual R W ↦ l (ψ j)) he)
      rw [← exp x,← exp y]
      simp_rw [hh]
    · intro w
      refine ⟨∑ j, op (w (ψ j)) • b j,LinearMap.ext fun l ↦ ?_⟩
      have h := congrArg w (LinearMap.congr_fun split l)
      change l (∑ j, op (w (ψ j)) • b j) = w l
      change w (val (coords l)) = w l at h
      rw [show val (coords l) = ∑ i, l (b i) • ψ i from LinearMap.sum_apply ..,map_sum] at h
      simpa only [map_sum,map_smul,op_smul_eq_mul,smul_eq_mul] using h
  exact ⟨P,⟨(LinearEquiv.ofBijective ev bij).toFGModuleCatIso.symm⟩⟩

/-- Two finite projectives are isomorphic exactly when their duals are. -/
theorem star_iso_iff (P Q : FiniteProjective R) : Nonempty (P.star.val ≅ Q.star.val) ↔ Nonempty (P.val ≅ Q.val) := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨f,hf⟩ := (transpose_bijective P Q).2 e.inv
    obtain ⟨g,hg⟩ := (transpose_bijective Q P).2 e.hom
    exact ⟨⟨f,g,(transpose_bijective P P).1 (by rw [transpose_comp,transpose_id,hf,hg,e.hom_inv_id]),
      (transpose_bijective Q Q).1 (by rw [transpose_comp,transpose_id,hf,hg,e.inv_hom_id])⟩⟩
  · rintro ⟨e⟩
    exact ⟨⟨transpose e.inv,transpose e.hom,by rw [← transpose_comp,e.hom_inv_id,transpose_id],
      by rw [← transpose_comp,e.inv_hom_id,transpose_id]⟩⟩

/-- The opposite dual takes a binary biproduct to a biproduct. -/
noncomputable def starBiprodIso (P Q : FiniteProjective R) :
    (ProjectiveClass.biprod P Q).star.val ≅ P.star.val ⊞ Q.star.val := by
  let T := ProjectiveClass.biprod P Q
  let a := ((FGModuleCat.forgetBiprodIso P.val Q.val).trans (ModuleCat.biprodIsoProd P.val.obj Q.val.obj)).toLinearEquiv
  let v : Module.Dual R T.val ≃ₗ[Rᵐᵒᵖ] Module.Dual R (P.val × Q.val) :=
    { toFun := fun f ↦ f.comp a.symm.toLinearMap
      invFun := fun g ↦ g.comp a.toLinearMap
      left_inv := fun f ↦ LinearMap.ext (fun x ↦ congrArg f (a.symm_apply_apply x))
      right_inv := fun g ↦ LinearMap.ext (fun x ↦ congrArg g (a.apply_symm_apply x))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let w : Module.Dual R (P.val × Q.val) ≃ₗ[Rᵐᵒᵖ] (Module.Dual R P.val × Module.Dual R Q.val) :=
    (LinearMap.coprodEquiv Rᵐᵒᵖ).symm
  let H := forget₂ (FGModuleCat.{u} Rᵐᵒᵖ) (ModuleCat.{u} Rᵐᵒᵖ)
  exact H.preimageIso ((v.trans w).toModuleIso.trans
    ((FGModuleCat.forgetBiprodIso P.star.val Q.star.val).trans (ModuleCat.biprodIsoProd _ _)).symm)

end EFiniteCharacterizations.FiniteProjective

namespace EFiniteCharacterizations.ProjectiveClass

variable (R : Type u) [Ring R]

/-- Duality on the split Grothendieck group of finite projectives. -/
noncomputable def starMap : ProjectiveClass R →+ ProjectiveClass Rᵐᵒᵖ :=
  ProjectiveClass.lift (fun P ↦ of P.star)
    (fun P Q e ↦ of_eq_of_iso _ _ ((P.star_iso_iff Q).2 ⟨e⟩).some)
    (fun P Q T e ↦ by
      let H := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
      let f : T.val ≅ (biprod P Q).val := H.preimageIso (e.trans (FGModuleCat.forgetBiprodIso _ _).symm)
      let g := ((T.star_iso_iff _).2 ⟨f⟩).some.trans (P.starBiprodIso Q)
      exact (of_eq_of_iso T.star (biprod P.star Q.star) g).trans (of_biprod _ _))

@[simp] theorem starMap_of (P : FiniteProjective R) : starMap R (of P) = of P.star := lift_of ..

/-- Projective duality identifies the two integral lattices. -/
noncomputable def starEquiv : ProjectiveClass R ≃+ ProjectiveClass Rᵐᵒᵖ := by
  apply AddEquiv.ofBijective (starMap R)
  constructor
  · apply (injective_iff_map_eq_zero _).2
    intro x hx
    obtain ⟨P,Q,rfl⟩ := exists_sub x
    rw [map_sub,starMap_of,starMap_of,sub_eq_zero] at hx
    obtain ⟨U,⟨f⟩⟩ := exists_biprod_iso_of_of_eq hx
    obtain ⟨T,⟨e⟩⟩ := FiniteProjective.exists_star_iso U
    let a := biprod.mapIso (Iso.refl P.star.val) e
    let b := biprod.mapIso (Iso.refl Q.star.val) e
    let g := (P.starBiprodIso T).trans (a.trans (f.trans (b.symm.trans (Q.starBiprodIso T).symm)))
    have he := of_eq_of_iso _ _ (((biprod P T).star_iso_iff (biprod Q T)).1 ⟨g⟩).some
    rw [of_biprod,of_biprod] at he
    exact sub_eq_zero.2 (add_right_cancel he)
  · intro y
    obtain ⟨U,V,rfl⟩ := exists_sub y
    obtain ⟨P,⟨p⟩⟩ := FiniteProjective.exists_star_iso U
    obtain ⟨Q,⟨q⟩⟩ := FiniteProjective.exists_star_iso V
    exact ⟨of P - of Q, by rw [map_sub,starMap_of,starMap_of,of_eq_of_iso _ _ p,of_eq_of_iso _ _ q]⟩

@[simp] theorem starEquiv_of (P : FiniteProjective R) : starEquiv R (of P) = of P.star := starMap_of R P

end EFiniteCharacterizations.ProjectiveClass
