module

public import EFiniteCharacterizations.RingEpimorphisms.LocalizationModules
public import EFiniteCharacterizations.LinearAlgebra.Dual.FiniteProjective
public import Mathlib.RingTheory.FreeRing
public import Mathlib.Algebra.RingQuot

/-! # Existence of universal localization at finite projective differentials -/

@[expose] public section

open CategoryTheory

universe u

namespace EFiniteCharacterizations

namespace LocalizationConstruction

variable {R I : Type u} [Ring R] (φ : I → TwoTerm R)

private abbrev Letter := R ⊕ (Σ i : I, Module.Dual R (φ i).source × (φ i).target)
private abbrev Word := FreeRing (Letter φ)

variable {T : Type u} [Ring T] (g : R →+* T)

private def coefficient {X : Type u} [AddCommGroup X] [Module R X] (l : Module.Dual R X) :
    letI := Module.compHom T g; X →ₗ[R] T := by
  let := Module.compHom T g
  exact { toFun := fun x ↦ g (l x), map_add' := fun _ _ ↦ by simp,
          map_smul' := fun r x ↦ by change g (l (r • x)) = g r * g (l x); simp }

private noncomputable def inverseForm (h : InvertsFamily φ g) (i : I) (l : Module.Dual R (φ i).source) :
    letI := Module.compHom T g; (φ i).target →ₗ[R] T := by
  let := Module.compHom T g
  have hi := ((φ i).isIso_induce_iff_regular g).1 (h i)
  exact (((φ i).invertedOn_iff_linear _).1 hi |>.2 (coefficient g l)).choose

private theorem inverseForm_apply (h : InvertsFamily φ g) (i : I) (l : Module.Dual R (φ i).source)
    (x : (φ i).source) : inverseForm φ g h i l ((φ i).differential.hom.hom x) = g (l x) := by
  let := Module.compHom T g
  have hi := ((φ i).isIso_induce_iff_regular g).1 (h i)
  exact LinearMap.congr_fun ((((φ i).invertedOn_iff_linear _).1 hi |>.2 (coefficient g l)).choose_spec) x

private noncomputable def evaluate (h : InvertsFamily φ g) : Word φ →+* T :=
  FreeRing.lift (Sum.elim g (fun ⟨i,l,y⟩ ↦ inverseForm φ g h i l y))

private def Rel (a b : Word φ) : Prop :=
  ∀ (S : Type u) [Ring S] (p : R →+* S) (h : InvertsFamily φ p),
    evaluate φ p h a = evaluate φ p h b

private abbrev Target := RingQuot (Rel φ)

private noncomputable def generator (x : Letter φ) : Target φ := RingQuot.mkRingHom _ (FreeRing.of x)

private noncomputable def base : R →+* Target φ where
  toFun r := generator φ (.inl r)
  map_one' := by
    rw [← (RingQuot.mkRingHom (Rel φ)).map_one]
    apply RingQuot.mkRingHom_rel
    intro S _ p h
    simp [evaluate]
  map_zero' := by
    rw [← (RingQuot.mkRingHom (Rel φ)).map_zero]
    apply RingQuot.mkRingHom_rel
    intro S _ p h
    simp [evaluate]
  map_add' r s := by
    unfold generator
    rw [← map_add]
    apply RingQuot.mkRingHom_rel
    intro S _ p h
    simp [evaluate]
  map_mul' r s := by
    unfold generator
    rw [← map_mul]
    apply RingQuot.mkRingHom_rel
    intro S _ p h
    simp [evaluate]

private noncomputable def descend (h : InvertsFamily φ g) : Target φ →+* T :=
  RingQuot.lift ⟨evaluate φ g h,fun _ _ hab ↦ hab T g h⟩

private theorem descend_generator (h : InvertsFamily φ g) (x : Letter φ) :
    descend φ g h (generator φ x) = Sum.elim g (fun ⟨i,l,y⟩ ↦ inverseForm φ g h i l y) x := by
  unfold descend generator
  rw [RingQuot.lift_mkRingHom_apply]
  exact FreeRing.lift_of _ _

private theorem separate {x y : Target φ}
    (h : ∀ (S : Type u) [Ring S] (p : R →+* S) (hp : InvertsFamily φ p),
      descend φ p hp x = descend φ p hp y) : x = y := by
  obtain ⟨x,rfl⟩ := RingQuot.mkRingHom_surjective (Rel φ) x
  obtain ⟨y,rfl⟩ := RingQuot.mkRingHom_surjective (Rel φ) y
  apply RingQuot.mkRingHom_rel
  intro S _ p hp
  simpa only [descend,RingQuot.lift_mkRingHom_apply] using h S p hp

private noncomputable def universalForm (i : I) (l : Module.Dual R (φ i).source) :
    letI := Module.compHom (Target φ) (base φ); (φ i).target →ₗ[R] Target φ := by
  let := Module.compHom (Target φ) (base φ)
  refine { toFun := fun y ↦ generator φ (.inr ⟨i,l,y⟩), map_add' := ?_, map_smul' := ?_ }
  · intro x y
    apply separate
    intro S _ p hp
    simp only [map_add,descend_generator,Sum.elim_inr]
  · intro r x
    change _ = generator φ (.inl r) * generator φ (.inr ⟨i,l,x⟩)
    apply separate
    intro S _ p hp
    simp only [descend_generator,map_mul,Sum.elim_inl,Sum.elim_inr]
    let := Module.compHom S p
    exact (inverseForm φ p hp i l).map_smul r x

private theorem universalForm_apply (i : I) (l : Module.Dual R (φ i).source) (x : (φ i).source) :
    universalForm φ i l ((φ i).differential.hom.hom x) = base φ (l x) := by
  apply separate
  intro S _ p hp
  change descend φ p hp (generator φ _) = descend φ p hp (generator φ _)
  simpa only [descend_generator,Sum.elim_inl,Sum.elim_inr] using inverseForm_apply φ p hp i l x

private noncomputable def post (q : Target φ →+* T) (hq : q.comp (base φ) = g) :
    letI := Module.compHom (Target φ) (base φ)
    letI := Module.compHom T g
    Target φ →ₗ[R] T := by
  let := Module.compHom (Target φ) (base φ)
  let := Module.compHom T g
  exact { toFun := q, map_add' := q.map_add,
          map_smul' := fun r x ↦ (q.map_mul _ _).trans (congrArg (· * q x) (DFunLike.congr_fun hq r)) }

private theorem descend_base (h : InvertsFamily φ g) : (descend φ g h).comp (base φ) = g :=
  RingHom.ext fun r ↦ descend_generator φ g h (.inl r)

private theorem inverts : InvertsFamily φ (base φ) := by
  intro i
  let P := φ i
  have := P.projective_source
  have : Module.Finite R P.source := P.source.property
  obtain ⟨n,b,l,hb⟩ := exists_sum_dual_smul_eq (R := R) (M := P.source)
  let := Module.compHom (Target φ) (base φ)
  apply (P.isIso_induce_iff_regular _).2
  apply (P.invertedOn_iff_linear _).2
  constructor
  · intro a a' he
    apply LinearMap.ext
    intro x
    apply separate
    intro S _ p hp
    let := Module.compHom S p
    let e := post φ p (descend φ p hp) (descend_base φ p hp)
    have hi := (P.invertedOn_iff_linear _).1 ((P.isIso_induce_iff_regular p).1 (hp i))
    have ht : e.comp a = e.comp a' := hi.1 (congrArg (e.comp ·) he)
    exact LinearMap.congr_fun ht x
  · intro a
    let L : P.target →ₗ[R] Target φ :=
      { toFun y := ∑ j, universalForm φ i (l j) y * a (b j)
        map_add' y z := by simp [add_mul,Finset.sum_add_distrib]
        map_smul' r y := by
          change (∑ j, universalForm φ i (l j) (r • y) * a (b j)) = base φ r * _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [map_smul]
          exact mul_assoc .. }
    refine ⟨L,LinearMap.ext fun x ↦ ?_⟩
    change ∑ j, universalForm φ i (l j) ((φ i).differential.hom.hom x) * a (b j) = a x
    simp only [universalForm_apply]
    change ∑ j, l j x • a (b j) = a x
    simpa only [map_sum,map_smul] using congrArg a (hb x)

private theorem universal : IsUniversalLocalization φ (base φ) := by
  refine ⟨inverts φ,fun T _ g hg ↦ ⟨descend φ g hg,descend_base φ g hg,?_⟩⟩
  intro q hq
  apply RingQuot.ringQuot_ext
  apply FreeRing.hom_ext
  intro x
  change q (generator φ x) = descend φ g hg (generator φ x)
  rw [descend_generator]
  rcases x with r | ⟨i,l,y⟩
  · exact DFunLike.congr_fun hq r
  · let := Module.compHom T g
    let := Module.compHom (Target φ) (base φ)
    let e := post φ g q hq
    have hi := ((φ i).invertedOn_iff_linear _).1 (((φ i).isIso_induce_iff_regular g).1 (hg i))
    have he : e.comp (universalForm φ i l) = inverseForm φ g hg i l := by
      apply hi.1
      apply LinearMap.ext
      intro x
      change q (universalForm φ i l ((φ i).differential.hom.hom x)) = inverseForm φ g hg i l ((φ i).differential.hom.hom x)
      rw [universalForm_apply,inverseForm_apply]
      exact DFunLike.congr_fun hq _
    exact LinearMap.congr_fun he y

private theorem singleton_finitely_generated (k : Type u) [Field k] [Algebra k R]
    [Module.Finite k R] (P : TwoTerm R) :
    let ψ := fun _ : PUnit.{u+1} ↦ P
    letI := (universal ψ).epic.targetAlgebra k
    ∃ S : Set (Target ψ), S.Finite ∧ Algebra.adjoin k S = ⊤ := by
  classical
  let ψ := fun _ : PUnit.{u+1} ↦ P
  let := (universal ψ).epic.targetAlgebra k
  let f : R →ₐ[k] Target ψ := { __ := base ψ, commutes' := fun _ ↦ rfl }
  have := P.projective_source
  have := P.projective_target
  have : Module.Finite R P.source := P.source.property
  have : Module.Finite R P.target := P.target.property
  obtain ⟨n,b,l,hb⟩ := exists_sum_dual_smul_eq (R := R) (M := P.source)
  obtain ⟨m,c,q,hc⟩ := exists_sum_dual_smul_eq (R := R) (M := P.target)
  let r := Module.finBasis k R
  let S := Set.range (fun j ↦ f (r j)) ∪ Set.range
    (fun ij : Fin n × Fin m ↦ universalForm ψ PUnit.unit (l ij.1) (c ij.2))
  let A := Algebra.adjoin k S
  have hbase (x : R) : f x ∈ A := by
    rw [← r.sum_repr x, map_sum]
    exact A.sum_mem fun j _ ↦ by
      rw [map_smul]
      exact A.smul_mem (Algebra.subset_adjoin (Or.inl ⟨j,rfl⟩)) _
  let g : R →+* A := f.toRingHom.codRestrict A.toSubring hbase
  let := Module.compHom A g
  let := Module.compHom (Target ψ) (base ψ)
  let e : A →ₗ[R] Target ψ :=
    { A.subtype.toAddMonoidHom with
      map_smul' := fun _ _ ↦ rfl }
  have hform (j : Fin n) (y : P.target) : universalForm ψ PUnit.unit (l j) y ∈ A := by
    have hh := congrArg (universalForm ψ PUnit.unit (l j)) (hc y)
    rw [← hh, map_sum]
    apply A.sum_mem
    intro i _
    rw [map_smul]
    exact A.mul_mem (hbase (q i y)) (Algebra.subset_adjoin (Or.inr ⟨(j,i),rfl⟩))
  have hi : InvertsFamily ψ g := by
    intro i
    apply (P.isIso_induce_iff_regular g).2
    apply (P.invertedOn_iff_linear _).2
    constructor
    · intro a a' he
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have ht := (P.invertedOn_iff_linear _).1
        ((P.isIso_induce_iff_regular (base ψ)).1 (inverts ψ i))
      have hc' : (e.comp a).comp P.differential.hom.hom =
          (e.comp a').comp P.differential.hom.hom := congrArg (e.comp ·) he
      exact LinearMap.congr_fun (ht.1 hc') x
    · intro a
      let v (j : Fin n) (y : P.target) : A :=
        ⟨universalForm ψ PUnit.unit (l j) y,hform j y⟩
      have hsum (y : P.target) :
          (∑ j, v j y * a (b j)).val =
            ∑ j, universalForm ψ PUnit.unit (l j) y * (a (b j)).val :=
        map_sum A.subtype _ _
      let L : P.target →ₗ[R] A :=
        { toFun := fun y ↦ ∑ j, v j y * a (b j)
          map_add' := fun y z ↦ by
            apply Subtype.ext
            change (∑ j, v j (y + z) * a (b j)).val =
              (∑ j, v j y * a (b j)).val + (∑ j, v j z * a (b j)).val
            simp only [hsum, map_add, add_mul, Finset.sum_add_distrib]
          map_smul' := fun t y ↦ by
            apply Subtype.ext
            change (∑ j, v j (t • y) * a (b j)).val =
              base ψ t * (∑ j, v j y * a (b j)).val
            rw [hsum, hsum]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [map_smul]
            exact mul_assoc .. }
      refine ⟨L,LinearMap.ext fun x ↦ ?_⟩
      apply Subtype.ext
      change (∑ j, v j (P.differential.hom.hom x) * a (b j)).val = (a x).val
      rw [hsum]
      have hs' : (∑ j, (l j x) • a (b j)) = a x := by
        simpa only [map_sum,map_smul] using congrArg a (hb x)
      calc
        _ = ∑ j, base ψ (l j x) * (a (b j)).val := Finset.sum_congr rfl fun j _ ↦
          congrArg (fun t ↦ t * (a (b j)).val) (universalForm_apply ψ PUnit.unit (l j) x)
        _ = _ := (map_sum A.subtype _ _).symm.trans (congrArg Subtype.val hs')
  obtain ⟨s,hs,_⟩ := (universal ψ).desc A g hi
  have he : A.subtype.comp s = RingHom.id _ := (universal ψ).epic _ _ _ (by
    rw [RingHom.comp_assoc, hs]
    rfl)
  refine ⟨S,(Set.finite_range _).union (Set.finite_range _),top_unique fun x _ ↦ ?_⟩
  have hx : (s x).val = x := DFunLike.congr_fun he x
  exact hx ▸ (s x).property

end LocalizationConstruction

/-- A small family of finite projective differentials admits a universal
localization in rings of the same universe as the source. -/
theorem exists_universalLocalization {R I : Type u} [Ring R] (φ : I → TwoTerm R) :
    ∃ (B : Type u) (_ : Ring B) (g : R →+* B), IsUniversalLocalization φ g :=
  ⟨_,inferInstance,_,LocalizationConstruction.universal φ⟩

/-- The universal localization carries the induced central ground-field action. -/
theorem exists_algebra_universalLocalization {R I : Type u} [Ring R] (k : Type u)
    [Field k] [Algebra k R] (φ : I → TwoTerm R) :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (g : R →ₐ[k] B), IsUniversalLocalization φ g.toRingHom := by
  obtain ⟨B,_,g,hg⟩ := exists_universalLocalization φ
  let := hg.epic.targetAlgebra k
  exact ⟨B,inferInstance,inferInstance,{ __ := g, commutes' := fun _ ↦ rfl },hg⟩

/-- A singleton universal localization at finite projective terms is a
finitely generated algebra over the ground field. -/
theorem exists_finitely_generated_singleton_localization {R : Type u} [Ring R] (k : Type u)
    [Field k] [Algebra k R] [Module.Finite k R] (P : TwoTerm R) :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (g : R →ₐ[k] B),
      IsUniversalLocalization (fun _ : Unit ↦ P) g.toRingHom ∧
      ∃ S : Set B, S.Finite ∧ Algebra.adjoin k S = ⊤ := by
  let ψ := fun _ : PUnit.{u+1} ↦ P
  let h := LocalizationConstruction.universal ψ
  let := h.epic.targetAlgebra k
  let g : R →ₐ[k] LocalizationConstruction.Target ψ :=
    { __ := LocalizationConstruction.base ψ, commutes' := fun _ ↦ rfl }
  refine ⟨_,inferInstance,inferInstance,g,?_, LocalizationConstruction.singleton_finitely_generated k P⟩
  exact ⟨fun _ ↦ h.inverts PUnit.unit,fun T _ f hf ↦ h.desc T f (fun _ ↦ hf ())⟩

end EFiniteCharacterizations
