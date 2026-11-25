module

public import EFiniteCharacterizations.Silting.Reduction.PerpendicularReflection
public import EFiniteCharacterizations.Presentations.RegularInversion

/-! # The finite-dimensional algebra of a presilting perpendicular -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R] {P : TwoTerm R}

/-- The reflection of the regular module together with the image of one. -/
structure PointedReflection (P : TwoTerm R) where
  obj : FGModuleCat.{u} R
  point : obj
  inverted : P.InvertedOn obj.obj
  evaluation : ∀ N : ModuleCat.{u} R, P.InvertedOn N →
    Function.Bijective (fun f : obj →ₗ[R] N ↦ f point)

namespace PointedReflection

variable (A : PointedReflection P)

/-- Opposite endomorphisms of the reflected regular module. -/
abbrev Target := (Module.End R A.obj)ᵐᵒᵖ

noncomputable def endAt (x : A.obj) : Module.End R A.obj :=
  ((A.evaluation A.obj.obj A.inverted).2 x).choose

private theorem endAt_point (x : A.obj) : A.endAt x A.point = x :=
  ((A.evaluation A.obj.obj A.inverted).2 x).choose_spec

/-- The original algebra acts on the reflected regular module through a
canonical ring map into the opposite endomorphism algebra. -/
noncomputable def ringMap : R →+* A.Target where
  toFun r := MulOpposite.op (A.endAt (r • A.point))
  map_one' := by
    apply MulOpposite.unop_injective
    apply (A.evaluation A.obj.obj A.inverted).1
    change A.endAt (1 • A.point) A.point = A.point
    rw [one_smul, endAt_point]
  map_zero' := by
    apply MulOpposite.unop_injective
    apply (A.evaluation A.obj.obj A.inverted).1
    change A.endAt (0 • A.point) A.point = 0
    rw [zero_smul, endAt_point]
  map_add' r s := by
    apply MulOpposite.unop_injective
    apply (A.evaluation A.obj.obj A.inverted).1
    change A.endAt ((r+s) • A.point) A.point = A.endAt (r • A.point) A.point + A.endAt (s • A.point) A.point
    rw [endAt_point,endAt_point,endAt_point,add_smul]
  map_mul' r s := by
    apply MulOpposite.unop_injective
    apply (A.evaluation A.obj.obj A.inverted).1
    change A.endAt ((r*s) • A.point) A.point = A.endAt (s • A.point) (A.endAt (r • A.point) A.point)
    rw [endAt_point,endAt_point,map_smul,endAt_point,mul_smul]

/-- Evaluation identifies the restricted regular module with the reflection. -/
noncomputable def regularEquiv :
    letI := Module.compHom A.Target A.ringMap
    A.Target ≃ₗ[R] A.obj := by
  let := Module.compHom A.Target A.ringMap
  let ev : A.Target →ₗ[R] A.obj :=
    { toFun := fun a ↦ a.unop A.point
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r a ↦ by
        change a.unop (A.endAt (r • A.point) A.point) = r • a.unop A.point
        rw [endAt_point,map_smul] }
  exact LinearEquiv.ofBijective ev ((A.evaluation A.obj.obj A.inverted).comp MulOpposite.opEquiv.symm.bijective)

/-- A ring map inverting the differential on its restricted regular module
factors uniquely through the opposite endomorphism algebra. -/
theorem existsUnique_factor {T : Type u} [Ring T] (g : R →+* T)
    (hg : letI := Module.compHom T g; P.InvertedOn (ModuleCat.of R T)) :
    ∃! q : A.Target →+* T, q.comp A.ringMap = g := by
  let := Module.compHom T g
  let N := ModuleCat.of R T
  obtain ⟨l,hl⟩ := (A.evaluation N hg).2 (1 : T)
  change l A.point = 1 at hl
  let right (t : T) : T →ₗ[R] T :=
    { toFun := fun x ↦ x * t
      map_add' := fun x y ↦ add_mul x y t
      map_smul' := fun r x ↦ mul_assoc (g r) x t }
  have comp (a : Module.End R A.obj) : l.comp a = (right (l (a A.point))).comp l := by
    apply (A.evaluation N hg).1
    change l (a A.point) = l A.point * l (a A.point)
    rw [hl,one_mul]
  let q : A.Target →+* T :=
    { toFun := fun a ↦ l (a.unop A.point)
      map_one' := hl
      map_zero' := l.map_zero
      map_add' := fun a b ↦ l.map_add _ _
      map_mul' := fun a b ↦ LinearMap.congr_fun (comp b.unop) (a.unop A.point) }
  have hq : q.comp A.ringMap = g := by
    ext r
    change l (A.endAt (r • A.point) A.point) = g r
    rw [endAt_point,map_smul,hl]
    exact mul_one _
  refine ⟨q,hq,fun q' hq' ↦ ?_⟩
  let := Module.compHom A.Target A.ringMap
  let lin (t : A.Target →+* T) (ht : t.comp A.ringMap = g) : A.Target →ₗ[R] T :=
    { toFun := t
      map_add' := t.map_add
      map_smul' := fun r x ↦ by
        change t (A.ringMap r * x) = g r * t x
        rw [map_mul, show t (A.ringMap r) = g r from DFunLike.congr_fun ht r] }
  have eqL : (lin q' hq').comp A.regularEquiv.symm.toLinearMap =
      (lin q hq).comp A.regularEquiv.symm.toLinearMap := by
    apply (A.evaluation N hg).1
    have hone : A.regularEquiv.symm A.point = 1 := A.regularEquiv.symm_apply_eq.mpr rfl
    change q' (A.regularEquiv.symm A.point) = q (A.regularEquiv.symm A.point)
    rw [hone,map_one,map_one]
  ext x
  simpa [lin]
    using LinearMap.congr_fun eqL (A.regularEquiv x)

theorem invertedOn_regular : letI := Module.compHom A.Target A.ringMap
    P.InvertedOn (ModuleCat.of R A.Target) := by
  let := Module.compHom A.Target A.ringMap
  let e := A.regularEquiv
  have h := (invertedOn_iff_linear P A.obj.obj).1 A.inverted
  apply (invertedOn_iff_linear P _).2
  let d := P.differential.hom.hom
  refine ⟨fun {f g} he ↦ ?_,fun f ↦ ?_⟩
  · have he' : e.toLinearMap.comp f = e.toLinearMap.comp g := h.1 (congrArg (e.toLinearMap.comp ·) he)
    exact LinearMap.ext fun x ↦ e.injective (LinearMap.congr_fun he' x)
  · obtain ⟨z,hz⟩ := h.2 (e.toLinearMap.comp f)
    exact ⟨e.symm.toLinearMap.comp z,LinearMap.ext fun x ↦ by
      change e.symm (z (d x)) = f x
      rw [show z (d x) = e (f x) from LinearMap.congr_fun hz x,e.symm_apply_apply]⟩

/-- Among ring maps, the reflection algebra represents inversion on all
restricted modules. -/
theorem factor_iff_inverted {T : Type u} [Ring T] (g : R →+* T) :
    (∃! q : A.Target →+* T, q.comp A.ringMap = g) ↔
      ∀ (N : Type u) [AddCommGroup N] [Module T N], letI := Module.compHom N g
        P.InvertedOn (ModuleCat.of R N) := by
  constructor
  · rintro ⟨q,rfl,_⟩ N _ _
    let := Module.compHom N q
    exact ((P.invertedOn_restrictions_iff_regular A.ringMap).2 A.invertedOn_regular) N
  · intro h
    exact A.existsUnique_factor g (h T)

/-- The reflection map is epic among rings. -/
theorem epic {T : Type u} [Ring T] (q q' : A.Target →+* T)
    (h : q.comp A.ringMap = q'.comp A.ringMap) : q = q' := by
  let := Module.compHom T q'
  have hi := ((P.invertedOn_restrictions_iff_regular A.ringMap).2 A.invertedOn_regular) T
  exact (A.existsUnique_factor (q'.comp A.ringMap) hi).unique h rfl

/-- The unique linear map from the reflection taking its point to x. -/
noncomputable def liftPoint {N : ModuleCat.{u} R} (hN : P.InvertedOn N) (x : N) : A.obj →ₗ[R] N :=
  ((A.evaluation N hN).2 x).choose

theorem liftPoint_eval {N : ModuleCat.{u} R} (hN : P.InvertedOn N) (x : N) :
    A.liftPoint hN x A.point = x := ((A.evaluation N hN).2 x).choose_spec

/-- The opposite endomorphism algebra acts on every module inverting the
differential. -/
@[instance_reducible] noncomputable def moduleOfInverted {N : ModuleCat.{u} R} (hN : P.InvertedOn N) :
    Module A.Target N := by
  let l := A.liftPoint hN
  have ev (x : N) : l x A.point = x := A.liftPoint_eval hN x
  have comp (a : A.Target) (x : N) : l (l x (a.unop A.point)) = (l x).comp a.unop :=
    (A.evaluation N hN).1 (ev _)
  exact
    { smul := fun a x ↦ l x (a.unop A.point)
      one_smul := ev
      mul_smul := fun a b x ↦ (LinearMap.congr_fun (comp b x) (a.unop A.point)).symm
      smul_add := fun a x y ↦ by
        have h : l (x+y) = l x + l y := (A.evaluation N hN).1 ((ev _).trans (congrArg₂ (· + ·) (ev x) (ev y)).symm)
        exact LinearMap.congr_fun h _
      smul_zero := fun a ↦ LinearMap.congr_fun (show l 0 = 0 from (A.evaluation N hN).1 (ev 0)) _
      add_smul := fun a b x ↦ (l x).map_add _ _
      zero_smul := fun x ↦ (l x).map_zero }

theorem moduleOfInverted_compatible {N : ModuleCat.{u} R} (hN : P.InvertedOn N) (r : R) (x : N) :
    letI := A.moduleOfInverted hN
    A.ringMap r • x = r • x := by
  change A.liftPoint hN x (A.endAt (r • A.point) A.point) = _
  rw [endAt_point,map_smul,liftPoint_eval]

/-- Restriction to the original algebra is full on modules over the reflection algebra. -/
theorem map_smul_of_restricted_linear {M N : Type u} [AddCommGroup M] [Module A.Target M]
    [AddCommGroup N] [Module A.Target N] :
    letI := Module.compHom M A.ringMap
    letI := Module.compHom N A.ringMap
    ∀ (f : M →ₗ[R] N) (a : A.Target) (x : M), f (a • x) = a • f x := by
  let := Module.compHom M A.ringMap
  let := Module.compHom N A.ringMap
  let := Module.compHom A.Target A.ringMap
  intro f a x
  have hN := ((P.invertedOn_restrictions_iff_regular A.ringMap).2 A.invertedOn_regular) N
  let v {Z : Type u} [AddCommGroup Z] [Module A.Target Z] (z : Z) :
      letI := Module.compHom Z A.ringMap
      A.Target →ₗ[R] Z := by
    let := Module.compHom Z A.ringMap
    exact { toFun := fun t ↦ t • z
            map_add' := fun r s ↦ add_smul r s z
            map_smul' := fun r s ↦ mul_smul (A.ringMap r) s z }
  have he : (f.comp (v x)).comp A.regularEquiv.symm.toLinearMap =
      (v (f x)).comp A.regularEquiv.symm.toLinearMap := by
    apply (A.evaluation (ModuleCat.of R N) hN).1
    have hone : A.regularEquiv.symm A.point = 1 := A.regularEquiv.symm_apply_eq.mpr rfl
    change f (A.regularEquiv.symm A.point • x) = A.regularEquiv.symm A.point • f x
    rw [hone,one_smul,one_smul]
  simpa [v] using LinearMap.congr_fun he (A.regularEquiv a)

variable (k : Type u) [Field k] [Algebra k R]

/-- The reflection map preserves ground scalars. -/
noncomputable def algebraMapToTarget : R →ₐ[k] A.Target where
  __ := A.ringMap
  commutes' s := by
    apply MulOpposite.unop_injective
    apply (A.evaluation A.obj.obj A.inverted).1
    change A.endAt (algebraMap k R s • A.point) A.point = _
    rw [endAt_point]
    rfl

theorem finite_target [Module.Finite k R] : Module.Finite k A.Target := by
  have := finiteModuleHom_isFinite k A.obj A.obj
  have := Module.Finite.equiv (finiteModuleHomLinearEquiv k A.obj A.obj)
  exact Module.Finite.equiv (MulOpposite.opLinearEquiv k)

end PointedReflection

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R] [IsArtinianRing R] [IsNoetherianRing R]

/-- Over an E-finite algebra, localization at a presilting differential is
represented by a finite-dimensional algebra. -/
theorem exists_finite_presilting_localization (hR : IsEFinite R) (P : TwoTerm R) (hp : P.IsPresilting) :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B) (f : R →ₐ[k] B),
      (∀ (N : Type u) [AddCommGroup N] [Module B N], letI := Module.compHom N f.toRingHom
        P.InvertedOn (ModuleCat.of R N)) ∧
      ∀ (T : Type u) [Ring T] (g : R →+* T),
        (∃! q : B →+* T, q.comp f.toRingHom = g) ↔
        (letI := Module.compHom T g; P.InvertedOn (ModuleCat.of R T)) := by
  obtain ⟨L,e,hL,he⟩ := exists_finite_pointed_perpendicular k hR P hp
  let A : PointedReflection P := ⟨L,e,hL,he⟩
  exact ⟨A.Target,inferInstance,inferInstance,A.finite_target k,A.algebraMapToTarget k,
    (P.invertedOn_restrictions_iff_regular A.ringMap).2 A.invertedOn_regular,
    fun T _ g ↦ (A.factor_iff_inverted g).trans (P.invertedOn_restrictions_iff_regular g)⟩

end EFiniteCharacterizations.TwoTerm
