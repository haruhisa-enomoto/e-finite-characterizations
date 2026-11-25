module

public import EFiniteCharacterizations.Presentations.RigidPencilComparison
public import EFiniteCharacterizations.LinearAlgebra.FiniteFieldExtensions
public import Mathlib.Algebra.Polynomial.Roots

/-! # A pair of rigid differentials on the same terms -/

@[expose] public section

open CategoryTheory

namespace EFiniteCharacterizations

universe v w

variable (k : Type v) [Field k] {C : Type*} [Category C] [Preadditive C] [Linear k C]

/-- Parameters off the zero locus of a nonzero polynomial give an isomorphism
between the two rigid members of a pencil. -/
theorem exists_iso_square_of_rigid_pair_polynomial {X Y : C} (p q : X ⟶ Y)
    [Module.Finite k (X ⟶ X)] [Module.Finite k (Y ⟶ Y)] [Module.Finite k (X ⟶ Y)]
    (hp : Function.Surjective (boundaryLinear k p p))
    (hq : Function.Surjective (boundaryLinear k q q)) :
    ∃ d : Polynomial k, d ≠ 0 ∧
      ∀ {F : Type w} [Field F] [Algebra k F] (e : Polynomial k →ₐ[k] F), e d ≠ 0 →
        let G : C ⥤ ScalarCategory k F C := ScalarCategory.of
        ∃ (a : G.obj X ≅ G.obj X) (b : G.obj Y ≅ G.obj Y), a.hom ≫ G.map q = G.map p ≫ b.hom := by
  obtain ⟨d₁, hd₁, h₁⟩ := exists_affine_iso_polynomial k p q hp
  obtain ⟨d₂, hd₂, h₂⟩ := exists_affine_iso_polynomial k q p hq
  let r : Polynomial k →ₐ[k] Polynomial k := Polynomial.aeval (1 - (Polynomial.X : Polynomial k))
  have hrX : r Polynomial.X = 1 - Polynomial.X := Polynomial.aeval_X _
  have hr : Function.Involutive r := by
    have h : r.comp r = AlgHom.id k (Polynomial k) := by
      apply Polynomial.algHom_ext
      change r (r Polynomial.X) = Polynomial.X
      rw [hrX, map_sub, map_one, hrX, sub_sub_cancel]
    intro f
    exact congrFun (congrArg DFunLike.coe h) f
  have hne₁ : d₁ ≠ 0 := by
    rintro rfl
    rw [Polynomial.eval_zero] at hd₁
    exact zero_ne_one hd₁
  have hne₂ : d₂ ≠ 0 := by
    rintro rfl
    rw [Polynomial.eval_zero] at hd₂
    exact zero_ne_one hd₂
  refine ⟨d₁ * r d₂, mul_ne_zero hne₁ (fun hz ↦ hne₂ (hr.injective (hz.trans (map_zero r).symm))), ?_⟩
  intro F _ _ e he
  let G : C ⥤ ScalarCategory k F C := ScalarCategory.of
  rw [map_mul] at he
  obtain ⟨a, b, ha⟩ := h₁ e (left_ne_zero_of_mul he)
  obtain ⟨c, d, hc⟩ := h₂ (e.comp r) (right_ne_zero_of_mul he)
  let w := G.map p + (e Polynomial.X) • G.map (q - p)
  have hw : G.map q + (e.comp r) Polynomial.X • G.map (p - q) = w := by
    change G.map q + e (r Polynomial.X) • G.map (p - q) =
      G.map p + e Polynomial.X • G.map (q - p)
    rw [hrX, map_sub, map_one, Functor.map_sub, Functor.map_sub, sub_smul, one_smul, smul_sub, smul_sub]
    abel
  change a.hom ≫ G.map p = w ≫ b.hom at ha
  change c.hom ≫ G.map q = (G.map q + (e.comp r) Polynomial.X • G.map (p - q)) ≫ d.hom at hc
  rw [hw] at hc
  have hback : a.inv ≫ w = G.map p ≫ b.inv := by
    apply (cancel_mono b.hom).1
    simp only [Category.assoc, ← ha, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨a.symm.trans c, b.symm.trans d, ?_⟩
  change (a.inv ≫ c.hom) ≫ G.map q = G.map p ≫ (b.inv ≫ d.hom)
  rw [Category.assoc, hc, ← Category.assoc a.inv, hback, Category.assoc]

/-- Two rigid differentials on the same terms become isomorphic over the
rational function field. -/
theorem exists_iso_square_of_rigid_pair {X Y : C} (p q : X ⟶ Y)
    [Module.Finite k (X ⟶ X)] [Module.Finite k (Y ⟶ Y)] [Module.Finite k (X ⟶ Y)]
    (hp : Function.Surjective (boundaryLinear k p p))
    (hq : Function.Surjective (boundaryLinear k q q)) :
    let G : C ⥤ ScalarCategory k (RatFunc k) C := ScalarCategory.of
    ∃ (a : G.obj X ≅ G.obj X) (b : G.obj Y ≅ G.obj Y), a.hom ≫ G.map q = G.map p ≫ b.hom := by
  let e : Polynomial k →ₐ[k] RatFunc k := IsScalarTower.toAlgHom k (Polynomial k) _
  have he : Function.Injective e := IsFractionRing.injective (Polynomial k) (RatFunc k)
  obtain ⟨d, hd, hiso⟩ := exists_iso_square_of_rigid_pair_polynomial k p q hp hq
  exact hiso e (fun hz ↦ hd (he (hz.trans (map_zero e).symm)))

/-- Over a finite field, any two rigid differentials on fixed terms become
isomorphic over a finite extension. -/
theorem exists_finite_field_iso_square_of_rigid_pair [Finite k] {X Y : C} (p q : X ⟶ Y)
    [Module.Finite k (X ⟶ X)] [Module.Finite k (Y ⟶ Y)] [Module.Finite k (X ⟶ Y)]
    (hp : Function.Surjective (boundaryLinear k p p))
    (hq : Function.Surjective (boundaryLinear k q q)) :
    ∃ (F : Type v) (_ : Field F) (_ : Algebra k F), Finite F ∧
      let G : C ⥤ ScalarCategory k F C := ScalarCategory.of
      ∃ (a : G.obj X ≅ G.obj X) (b : G.obj Y ≅ G.obj Y), a.hom ≫ G.map q = G.map p ≫ b.hom := by
  obtain ⟨d, hd, hiso⟩ := exists_iso_square_of_rigid_pair_polynomial k p q hp hq
  obtain ⟨F, _, _, hF, _, hcard⟩ := exists_finiteFieldExtension k (d.natDegree + 1) (Nat.succ_pos _)
  let _ := Fintype.ofFinite F
  have hcard' : d.natDegree < Fintype.card F := by
    have hk : 2 ≤ Nat.card k := Finite.one_lt_card
    rw [← Nat.card_eq_fintype_card, hcard]
    exact (Nat.lt_succ_self _).trans ((d.natDegree + 1).lt_two_pow_self.trans_le (Nat.pow_le_pow_left hk _))
  let f := algebraMap k F
  obtain ⟨x, hx⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card (d.map f)
    ((Polynomial.map_eq_zero_iff f.injective).not.2 hd)
    (by simpa only [Polynomial.natDegree_map_eq_of_injective f.injective, Cardinal.mk_fintype, Nat.cast_lt] using hcard')
  refine ⟨F, inferInstance, inferInstance, hF, hiso (Polynomial.aeval x) ?_⟩
  rwa [Polynomial.aeval_def, ← Polynomial.eval_map]

end EFiniteCharacterizations
