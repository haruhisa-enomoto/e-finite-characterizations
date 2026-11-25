module

public import EFiniteCharacterizations.LargeModules.EndofiniteLocal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.RingTheory.LocalRing.Basic

/-! # Relative injectivity of a grain and its endomorphism socle -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
    {N : ModuleCat.{u} R}

private theorem SplitsOnCogeneratedModules.extend_finite (hs : SplitsOnCogeneratedModules k N)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) [Module.Finite k S.X₃]
    {ι : Type*} (p : S.X₃ →ₗ[R] (ι → N)) (hp : Function.Injective p) (f : S.X₁ ⟶ N) :
    ∃ h : S.X₂ ⟶ N, S.f ≫ h = f := by
  let := hS.mono_f
  let i := pushout.inr S.f f
  let sq := IsPushout.of_hasPushout S.f f
  let T := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have ht : T.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i)
    (by dsimp [T,i]; infer_instance) (by dsimp [T]; infer_instance)
  have := isIso_cokernel_map_of_isPushout sq
  let e : cokernel i ≅ S.X₃ := (asIso (cokernel.map _ _ _ _ sq.w)).symm ≪≫
    (cokernelIsCokernel S.f).coconePointUniqueUpToIso hS.gIsCokernel
  let : Module.Finite k ((cokernel i : ModuleCat.{u} R) : Type u) := Module.Finite.equiv (e.toLinearEquiv.symm.restrictScalars k)
  let : IsArtinian R ((cokernel i : ModuleCat.{u} R) : Type u) := isArtinian_of_tower k (S := R) inferInstance
  obtain ⟨n,a,ha⟩ := finite_coordinates_of_product_embedding (X := cokernel i) (N := N)
    (p.comp e.hom.hom) (hp.comp e.toLinearEquiv.injective)
  let v := LinearMap.pi (fun j ↦ (LinearMap.proj (a j)).comp (p.comp e.hom.hom))
  obtain ⟨s,h⟩ := hs T ht ⟨Iso.refl _⟩ inferInstance ⟨n,v,ha⟩
  let split := ShortComplex.Splitting.ofExactOfSection T ht.exact s h ht.mono_f
  refine ⟨pushout.inl _ _ ≫ split.r,?_⟩
  rw [← Category.assoc,pushout.condition,Category.assoc]
  exact (congrArg (f ≫ ·) split.f_r).trans (Category.comp_id _)

variable [Module.Finite k R]

/-- Every map from the kernel of a map to a product of copies of an endofinite
module extends to the whole domain if the finite cogenerated Ext test holds. -/
theorem extends_from_cogenerated_quotient (he : IsEndofinite N) (hs : SplitsOnCogeneratedModules k N)
    (V : ModuleCat.{u} R) {ι : Type u} (p : V →ₗ[R] (ι → N)) (f : p.ker →ₗ[R] N) :
    ∃ h : V →ₗ[R] N, h.comp p.ker.subtype = f := by
  apply he.extend_of_finite_spans
  intro B hB
  let := Module.Finite.of_fg hB
  let : Module.Finite k B := Module.Finite.trans R _
  let q := p.comp B.subtype
  let i := ModuleCat.ofHom q.ker.subtype
  let m := ModuleCat.ofHom q.rangeRestrict
  let S := ShortComplex.mk i m (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subtype.ext x.property)
  let : Module.Finite R q.range := Module.Finite.of_surjective q.rangeRestrict q.surjective_rangeRestrict
  let : Module.Finite k q.range := Module.Finite.trans R _
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 (by
      intro x
      change q.rangeRestrict x = 0 ↔ ∃ y : q.ker, y.val = x
      simpa only [Subtype.exists, exists_prop,exists_eq_right] using
        (show q.rangeRestrict x = 0 ↔ x ∈ q.ker from Subtype.ext_iff)))
    ((ModuleCat.mono_iff_injective i).2 Subtype.val_injective)
    ((ModuleCat.epi_iff_surjective m).2 q.surjective_rangeRestrict)
  let l : q.ker →ₗ[R] p.ker :=
    (B.subtype.comp q.ker.subtype).codRestrict _ (fun x ↦ x.property)
  obtain ⟨h,hh⟩ := hs.extend_finite k S hS q.range.subtype Subtype.val_injective (ModuleCat.ofHom (f.comp l))
  refine ⟨h.hom,fun z hz ↦ ?_⟩
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hh) (⟨⟨z.val,hz⟩,z.property⟩ : q.ker)

section Reject

variable (N)

/-- Evaluate simultaneously all noninvertible endomorphisms. -/
def nonunitEvaluation : N →ₗ[R] ({a : Module.End R N // ¬ IsUnit a} → N) :=
  LinearMap.pi fun a ↦ a.val

/-- The common kernel of the nonunits of the endomorphism ring. When the
endomorphism ring is local, it is its module socle. -/
abbrev nonunitKernel : Submodule R N := (nonunitEvaluation N).ker

private theorem mem_nonunitKernel (x : N) :
    x ∈ nonunitKernel N ↔ ∀ a : Module.End R N, ¬ IsUnit a → a x = 0 := by
  change (fun a : {a : Module.End R N // ¬ IsUnit a} ↦ a.val x) = 0 ↔ _
  exact ⟨fun h a ha ↦ congrFun h ⟨a,ha⟩,fun h ↦ funext fun a ↦ h a.val a.property⟩

theorem mapsTo_nonunitKernel (a : Module.End R N) {x : N} (hx : x ∈ nonunitKernel N) :
    a x ∈ nonunitKernel N := by
  by_cases hu : IsUnit a
  · obtain ⟨u,rfl⟩ := hu
    apply (mem_nonunitKernel N _).2
    intro b hb
    exact (mem_nonunitKernel N x).1 hx (b * u.val) (fun h ↦ hb ((Units.isUnit_mul_units b u).1 h))
  · rw [(mem_nonunitKernel N x).1 hx a hu]
    exact Submodule.zero_mem _

/-- Restriction to the common kernel of nonunits. -/
def nonunitKernelRestriction : Module.End R N →+* Module.End R (nonunitKernel N) where
  toFun a := a.restrict (fun _ ↦ mapsTo_nonunitKernel N a)
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

include k in
theorem nonunitKernelRestriction_surjective (he : IsEndofinite N) (hs : SplitsOnCogeneratedModules k N) :
    Function.Surjective (nonunitKernelRestriction N) := by
  intro a
  obtain ⟨h,hh⟩ := extends_from_cogenerated_quotient k he hs N (nonunitEvaluation N)
    ((nonunitKernel N).subtype.comp a)
  exact ⟨h,LinearMap.ext fun x ↦ Subtype.ext (DFunLike.congr_fun hh x)⟩

include k in
theorem genericBrick_nonunitKernel_of_infinite (he : IsEndofinite N) (hs : SplitsOnCogeneratedModules k N)
    (hinf : ¬ Module.Finite k (nonunitKernel N)) :
    IsGenericBrick k (ModuleCat.of R (nonunitKernel N)) := by
  let S := nonunitKernel N
  let E := Module.End R N
  let res := nonunitKernelRestriction N
  refine ⟨hinf,?_,?_⟩
  · intro a ha
    obtain ⟨g,rfl⟩ := nonunitKernelRestriction_surjective k N he hs a
    by_cases hg : IsUnit g
    · exact (Module.End.isUnit_iff _).1 (res.isUnit_map hg)
    · exact False.elim (ha (LinearMap.ext fun x ↦ Subtype.ext ((mem_nonunitKernel N x.val).1 x.property g hg)))
  · let : Module E S := Module.compHom S res
    let : Module E (Module.End R S) := Module.compHom _ res
    let : IsScalarTower E (Module.End R S) S := ⟨fun _ _ _ ↦ rfl⟩
    let inc : S →ₗ[E] N := { toFun := Subtype.val, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
    let : IsNoetherian E N := (isFiniteLength_iff_isNoetherian_isArtinian.mp he).1
    let := Module.Finite.of_injective inc Subtype.val_injective
    exact Module.Finite.of_restrictScalars_finite E (Module.End R S) S

end Reject

section LocalRing

variable {D : Type u} [Ring D] [IsLocalRing D]

private theorem localRing_dedekindFinite : IsDedekindFiniteMonoid D where
  mul_eq_one_symm {a b} hab := by
    have h : IsUnit (b*a) := (IsLocalRing.isUnit_or_isUnit_one_sub_self (b*a)).resolve_right (fun hu ↦ by
      have hb : (1-b*a)*b = (1-b*a)*0 := by simp [sub_mul,mul_assoc,hab]
      have hz : b = 0 := hu.isRegular.left hb
      simp [hz] at hab)
    apply h.isRegular.left
    simp [mul_assoc,hab,← mul_assoc a b a]

/-- In a simple module over a local ring the annihilator of each nonzero
vector consists of exactly the nonunits. This uses left modules throughout. -/
private theorem simple_smul_zero_iff {L : Type u} [AddCommGroup L] [Module D L]
    [IsSimpleModule D L] (x : L) (hx : x ≠ 0) (a : D) : a • x = 0 ↔ ¬ IsUnit a := by
  constructor
  · rintro h ⟨u,rfl⟩
    exact hx (by simpa only [← mul_smul,Units.inv_mul,one_smul,smul_zero] using congrArg (fun z : L ↦ (↑u⁻¹ : D) • z) h)
  · intro h
    by_contra hn
    obtain ⟨b,hb⟩ := IsSimpleModule.toSpanSingleton_surjective D hn x
    change b • (a • x) = x at hb
    have hz : (1-b*a) • x = 0 := by rw [sub_smul,one_smul,mul_smul,hb,sub_self]
    have hu : IsUnit (b*a) := (IsLocalRing.isUnit_or_isUnit_one_sub_self (b*a)).resolve_right (by
      rintro ⟨u,hu⟩
      rw [← hu] at hz
      exact hx (by simpa only [← mul_smul,Units.inv_mul,one_smul,smul_zero] using congrArg (fun z : L ↦ (↑u⁻¹ : D) • z) hz))
    let := localRing_dedekindFinite (D := D)
    exact h (isUnit_of_mul_isUnit_right hu)

variable [Algebra k D]

private theorem finite_of_finiteLength_of_simple (L : Type u) [AddCommGroup L] [Module D L]
    [Module k L] [IsScalarTower k D L] [IsSimpleModule D L] [Module.Finite k L]
    {X : Type u} [AddCommGroup X] [Module D X] (hX : IsFiniteLength D X) :
    ∀ [Module k X] [IsScalarTower k D X], Module.Finite k X := by
  induction hX with
  | of_subsingleton => intro _ _; infer_instance
  | @of_simple_quotient X _ _ U _ _ ih =>
    intro _ _
    let Q := X ⧸ U
    let := IsSimpleModule.nontrivial D L
    let := IsSimpleModule.nontrivial D Q
    obtain ⟨x,hx⟩ := exists_ne (0 : L)
    obtain ⟨y,hy⟩ := exists_ne (0 : Q)
    let p := LinearMap.toSpanSingleton D L x
    let q := LinearMap.toSpanSingleton D Q y
    have eq : p.ker = q.ker := by
      ext a
      exact (simple_smul_zero_iff x hx a).trans (simple_smul_zero_iff y hy a).symm
    let l := (p.quotKerEquivOfSurjective (IsSimpleModule.toSpanSingleton_surjective D hx)).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ eq ≪≫ₗ q.quotKerEquivOfSurjective (IsSimpleModule.toSpanSingleton_surjective D hy)
    let : Module.Finite k Q := Module.Finite.equiv (l.restrictScalars k)
    let : Module.Finite k U := ih
    exact Module.Finite.of_exact (f := U.subtype.restrictScalars k) (g := U.mkQ.restrictScalars k)
      (LinearMap.exact_subtype_mkQ U) U.mkQ_surjective

end LocalRing

/-- The common kernel of the nonunits is the sum of the simple endomorphism
submodules when the endomorphism ring is local. -/
theorem mem_nonunitKernel_iff_mem_endomorphismSocle (N : ModuleCat.{u} R)
    [IsLocalRing (Module.End R N)] (x : N) :
    x ∈ nonunitKernel N ↔ x ∈ sSup {L : Submodule (Module.End R N) N | IsAtom L} := by
  let D := Module.End R N
  let S : Submodule D N :=
    { carrier := nonunitKernel N
      zero_mem' := Submodule.zero_mem _
      add_mem' := (nonunitKernel N).add_mem
      smul_mem' a _ h := mapsTo_nonunitKernel N a h }
  constructor
  · intro hx
    by_cases hz : x = 0
    · rw [hz]; exact Submodule.zero_mem _
    let p := LinearMap.toSpanSingleton D N x
    let L := p.range
    let v : L := ⟨x,1,one_smul D x⟩
    have hv : v ≠ 0 := fun h ↦ hz (congrArg Subtype.val h)
    let : Nontrivial L := nontrivial_of_ne _ _ hv
    have hL : IsSimpleModule D L := isSimpleModule_iff_toSpanSingleton_surjective.mpr
      ⟨inferInstance,fun y hy z ↦ by
        obtain ⟨a,ha⟩ := y.property
        obtain ⟨b,hb⟩ := z.property
        have hu : IsUnit a := by
          by_contra hn
          exact hy (Subtype.ext (ha.symm.trans ((mem_nonunitKernel N x).1 hx a hn)))
        obtain ⟨u,rfl⟩ := hu
        refine ⟨b * ↑u⁻¹,Subtype.ext ?_⟩
        change (b * ↑u⁻¹) • y.val = z.val
        change (u.val : D) • x = y.val at ha
        rw [← ha,← mul_smul,mul_assoc,Units.inv_mul,mul_one]
        exact hb⟩
    exact (le_sSup (s := {L : Submodule D N | IsAtom L}) (isSimpleModule_iff_isAtom.mp hL)) v.property
  · apply (show sSup {L : Submodule D N | IsAtom L} ≤ S from ?_)
    apply sSup_le
    intro L h y hy
    let : IsSimpleModule D L := isSimpleModule_iff_isAtom.mpr h
    apply (mem_nonunitKernel N y).2
    intro a ha
    by_cases hz : (⟨y,hy⟩ : L) = 0
    · have eq : y = 0 := congrArg Subtype.val hz
      simp [eq]
    · exact congrArg Subtype.val ((simple_smul_zero_iff (⟨y,hy⟩ : L) hz a).2 ha)

omit [Module.Finite k R] in
/-- Over a local endomorphism ring the common kernel of the nonunits of an
infinite-dimensional endofinite module is still infinite-dimensional. -/
theorem nonunitKernel_infinite_of_local (N : ModuleCat.{u} R) [IsLocalRing (Module.End R N)]
    (he : IsEndofinite N) (hinf : ¬ Module.Finite k N) : ¬ Module.Finite k (nonunitKernel N) := by
  intro hfin
  let D := Module.End R N
  let : Nontrivial N := not_subsingleton_iff_nontrivial.mp (fun h ↦ hinf inferInstance)
  let : IsArtinian D N := (isFiniteLength_iff_isNoetherian_isArtinian.mp he).2
  obtain ⟨L,hL⟩ := IsAtomic.exists_atom (Submodule D N)
  let : IsSimpleModule D L := isSimpleModule_iff_isAtom.mpr hL
  let inc : L →ₗ[k] (nonunitKernel N) := (L.subtype.restrictScalars k).codRestrict ((nonunitKernel N).restrictScalars k) (fun x ↦ by
    apply (mem_nonunitKernel N x.val).2
    intro a ha
    by_cases hz : x = 0
    · simp [hz]
    · exact congrArg Subtype.val ((simple_smul_zero_iff x hz a).2 ha))
  let : Module.Finite k L := Module.Finite.of_injective inc (fun _ _ h ↦ Subtype.ext (congrArg (fun z : nonunitKernel N ↦ z.val) h))
  exact hinf (finite_of_finiteLength_of_simple k L he)

/-- The endomorphism socle of a generic grain with local endomorphism ring
is an infinite-dimensional brick of finite endolength. -/
theorem IsGenericGrain.genericBrick_of_local {N : ModuleCat.{u} R} (h : IsGenericGrain k N)
    [IsLocalRing (Module.End R N)] : IsGenericBrick k (ModuleCat.of R (nonunitKernel N)) :=
  genericBrick_nonunitKernel_of_infinite k N h.endofinite h.splits
    (nonunitKernel_infinite_of_local k N h.endofinite h.infinite)

/-- Schlegel's socle construction for a generic grain over any field. -/
theorem IsGenericGrain.genericBrick {N : ModuleCat.{u} R} (h : IsGenericGrain k N) :
    IsGenericBrick k (ModuleCat.of R (nonunitKernel N)) := by
  let := h.endofinite.isLocalRing_end h.indecomposable
  exact h.genericBrick_of_local k

end EFiniteCharacterizations
