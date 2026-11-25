module

public import EFiniteCharacterizations.DivisionRings.HahnTriangular
public import EFiniteCharacterizations.DivisionRings.FreeGroupCoefficients
public import Mathlib.Data.Finset.SMulAntidiagonal
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer

/-! # Division-ring coefficients from well-ordered series on a group -/

@[expose] public section

noncomputable section
namespace EFiniteCharacterizations.OrderedGroupSeries

open scoped Pointwise
variable {G k : Type*} [Group G] [LinearOrder G] [MulLeftMono G] [MulRightMono G] [Field k]

private instance orderedSMul : IsOrderedCancelSMul G G where
  smul_le_smul_left _ _ h a := mul_le_mul_right h a
  smul_le_smul_right _ _ h a := mul_le_mul_left h a
  le_of_smul_le_smul_left _ _ _ := le_of_mul_le_mul_left'
  le_of_smul_le_smul_right _ _ _ := le_of_mul_le_mul_right'

private theorem finite_fiber (x y : HahnSeries G k) (z : G) :
    (fun w ↦ x.coeff (z*w⁻¹) * y.coeff w).HasFiniteSupport := by
  apply ((Set.SMulAntidiagonal.finite_of_isPWO x.isPWO_support y.isPWO_support z).image Prod.snd).subset
  intro w hw
  obtain ⟨hx,hy⟩ := mul_ne_zero_iff.mp hw
  exact ⟨(z*w⁻¹,w),⟨hx,hy,by simp [smul_eq_mul]⟩,rfl⟩

private def conv (x y : HahnSeries G k) : HahnSeries G k where
  coeff z := ∑ᶠ w, x.coeff (z*w⁻¹) * y.coeff w
  isPWO_support' := by
    apply (x.isPWO_support.smul y.isPWO_support).mono
    intro z hz
    by_contra h
    apply hz (finsum_eq_zero_of_forall_eq_zero (fun w ↦ ?_))
    by_contra! hn
    obtain ⟨hx,hy⟩ := mul_ne_zero_iff.mp hn
    exact h ⟨z*w⁻¹,hx,w,hy,by simp [smul_eq_mul]⟩

private def rightConv (y : HahnSeries G k) : Module.End k (HahnSeries G k) where
  toFun x := conv x y
  map_add' x u := HahnSeries.ext (funext fun z ↦ by
    change (∑ᶠ w, (x.coeff _ + u.coeff _) * y.coeff w) = _
    simp only [add_mul]
    exact finsum_add_distrib (finite_fiber x y z) (finite_fiber u y z))
  map_smul' r x := HahnSeries.ext (funext fun z ↦ by
    change (∑ᶠ w, (r * x.coeff _) * y.coeff w) = r * _
    simp only [mul_assoc]
    exact (mul_finsum _ r).symm)

private theorem conv_single_right (x : HahnSeries G k) (w z : G) (b : k) :
    (conv x (HahnSeries.single w b)).coeff z = x.coeff (z*w⁻¹)*b := by
  simp only [conv]
  rw [finsum_eq_single _ w (by intro p h; simp [HahnSeries.coeff_single_of_ne h])]
  simp

private theorem conv_single_left (y : HahnSeries G k) (g z : G) (a : k) :
    (conv (HahnSeries.single g a) y).coeff z = a*y.coeff (g⁻¹*z) := by
  simp only [conv]
  rw [finsum_eq_single _ (g⁻¹*z) (by
    intro p hp
    have h : z*p⁻¹ ≠ g := fun h ↦ hp (by rw [← h]; simp [mul_assoc])
    simp [HahnSeries.coeff_single_of_ne h])]
  simp

variable (G k) in
/-- Operators commuting with every right convolution. Evaluation on the
identity monomial realizes each operator as left convolution by one series. -/
private abbrev coefficientAlgebra : Subalgebra k (Module.End k (HahnSeries G k)) := Subalgebra.centralizer k (Set.range (rightConv (G := G) (k := k)))

private abbrev δ (g : G) : HahnSeries G k := HahnSeries.single g 1

private theorem eval (A : coefficientAlgebra G k) (y : HahnSeries G k) :
    A.val y = conv (A.val (δ 1)) y := by
  have h := (Subalgebra.mem_centralizer_iff k).mp A.property _ ⟨y,rfl⟩
  have h₁ : rightConv y (δ 1) = y := HahnSeries.ext (funext fun z ↦ by
    change (conv (HahnSeries.single 1 1) y).coeff z = _
    rw [conv_single_left]; simp)
  exact (congrArg A.val h₁).symm.trans (LinearMap.congr_fun h (δ 1)).symm

private theorem centralizing_bijective (A : coefficientAlgebra G k) (hne : A ≠ 0) :
    Function.Bijective A.val := by
  let x := A.val (δ 1)
  have hx : x ≠ 0 := by
    intro h
    apply hne
    exact Subtype.ext (LinearMap.ext fun y ↦ (eval A y).trans (by
      change rightConv y x = 0
      rw [h,map_zero]))
  let pos := HahnSeries.support_nonempty_iff.2 hx
  let g := x.isWF_support.min pos
  have hlead : x.coeff g ≠ 0 := x.isWF_support.min_mem pos
  have below {u : G} (h : u < g) : x.coeff u = 0 := not_ne_iff.mp (fun hn ↦ h.not_ge (x.isWF_support.min_le _ hn))
  have causal (u v : HahnSeries G k) (p : G) (h : ∀ w ≤ p, u.coeff w = v.coeff w)
      (b : G) (hb : b ≤ g*p) : (A.val u).coeff b = (A.val v).coeff b := by
    rw [eval A u,eval A v]
    change (∑ᶠ w, x.coeff (b*w⁻¹)*u.coeff w) = ∑ᶠ w, x.coeff (b*w⁻¹)*v.coeff w
    apply finsum_congr
    intro w
    by_cases hw : w ≤ p
    · rw [h w hw]
    · have hlt : b*w⁻¹ < g := (mul_inv_lt_iff_lt_mul).2 (hb.trans_lt (mul_lt_mul_right (lt_of_not_ge hw) g))
      rw [below hlt,zero_mul,zero_mul]
  have term (p : G) (a : k) (z : G) :
      (A.val (HahnSeries.single p a)).coeff z = x.coeff (z*p⁻¹)*a := by
    rw [eval]; exact conv_single_right ..
  have diag (p : G) (a : k) : (A.val (HahnSeries.single p a)).coeff (g*p) = x.coeff g * a := by
    simp [term]
  constructor
  · apply (injective_iff_map_eq_zero _).2
    intro y hy
    by_contra hn
    let p := y.isWF_support.min (HahnSeries.support_nonempty_iff.2 hn)
    have hp : y.coeff p ≠ 0 := y.isWF_support.min_mem _
    have agree (b : G) (hb : b ≤ p) : y.coeff b = (HahnSeries.single p (y.coeff p)).coeff b := by
      rcases hb.eq_or_lt with rfl | h
      · simp
      · rw [HahnSeries.coeff_single_of_ne h.ne]
        exact not_ne_iff.mp fun h' ↦ h.not_ge (y.isWF_support.min_le _ h')
    have e := causal _ _ p agree _ le_rfl
    rw [hy,diag] at e
    exact mul_ne_zero hlead hp e.symm
  · apply HahnTriangular.surjective A.val.toAddMonoidHom (OrderIso.mulLeft g) causal
    intro p d
    refine ⟨d / x.coeff g,?_,fun b hb ↦ ?_⟩
    · change (A.val _).coeff (g*p) = d
      rw [diag,mul_div_cancel₀ _ hlead]
    · change (A.val (HahnSeries.single p _)).coeff b = 0
      rw [term p _ b,below ((mul_inv_lt_iff_lt_mul).2 hb),zero_mul]

private theorem unit_or_zero (A : coefficientAlgebra G k) : IsUnit A ∨ A = 0 := by
  by_cases h : A = 0
  · exact Or.inr h
  left
  obtain ⟨u,hu⟩ := (Module.End.isUnit_iff _).2 (centralizing_bijective A h)
  have hm : (↑u⁻¹ : Module.End k (HahnSeries G k)) ∈ coefficientAlgebra G k := by
    apply (Subalgebra.mem_centralizer_iff k).2
    intro f hf
    apply Commute.units_inv_right
    rw [hu]
    exact (Subalgebra.mem_centralizer_iff k).1 A.property f hf
  refine isUnit_iff_exists.mpr ⟨⟨_,hm⟩,Subtype.ext ?_,Subtype.ext ?_⟩
  · change A.val * ↑u⁻¹ = 1
    rw [← hu,u.mul_inv]
  · change ↑u⁻¹ * A.val = 1
    rw [← hu,u.inv_mul]

private def shift (g : G) : Module.End k (HahnSeries G k) where
  toFun x := conv (δ g) x
  map_add' x y := HahnSeries.ext (funext fun z ↦ by
    simp [δ,conv_single_left,HahnSeries.coeff_add])
  map_smul' r x := HahnSeries.ext (funext fun z ↦ by
    simp [δ,conv_single_left])

private theorem shift_coeff (g : G) (x : HahnSeries G k) (z : G) :
    (shift g x).coeff z = x.coeff (g⁻¹*z) := by
  change (conv (HahnSeries.single g 1) x).coeff z = _
  simp [conv_single_left]

private def monomial (g : G) : coefficientAlgebra G k :=
  ⟨shift g,(Subalgebra.mem_centralizer_iff k).2 (by
    rintro _ ⟨y,rfl⟩
    apply LinearMap.ext
    intro x
    apply HahnSeries.ext
    funext z
    change (conv (shift g x) y).coeff z = (shift g (conv x y)).coeff z
    rw [shift_coeff]
    exact finsum_congr fun w ↦ by rw [shift_coeff,mul_assoc])⟩

private def coeff (g : G) : coefficientAlgebra G k →ₗ[k] k :=
  (HahnSeries.coeff.linearMap (R := k) g).comp
    ((LinearMap.applyₗ (R := k) (δ (1 : G))).comp (coefficientAlgebra G k).val.toLinearMap)

private theorem coeff_separates (A : coefficientAlgebra G k) (h : ∀ g, coeff g A = 0) : A = 0 := by
  have hz : A.val (δ 1) = 0 := HahnSeries.ext (funext h)
  exact Subtype.ext (LinearMap.ext fun y ↦ (eval A y).trans (by
    change rightConv y (A.val (δ 1)) = 0
    rw [hz,map_zero]))

private theorem coeff_mul_monomial (A : coefficientAlgebra G k) (g z : G) :
    coeff z (A * monomial g) = coeff (z*g⁻¹) A := by
  change (A.val (shift g (δ 1))).coeff z = _
  have eq : shift g (δ (k := k) 1) = δ g := by
    apply HahnSeries.ext
    funext w
    simp only [shift_coeff,δ,HahnSeries.coeff_single]
    rw [inv_mul_eq_one]
    simp [eq_comm]
  rw [eq,eval]
  change (conv _ (HahnSeries.single g 1)).coeff z = (A.val (δ 1)).coeff (z*g⁻¹)
  simpa [δ] using conv_single_right (A.val (δ 1)) g z (1 : k)

universe u in
/-- Well-ordered series on a biordered free group provide the division-ring
coefficients needed for the generic copresentation. The algebra is realized
by operators commuting with right convolution, so composition supplies its ring
law and inverses are obtained by solving triangular equations. -/
theorem exists_injective_boundary_of_biorder (k ι : Type u) [Field k] [Fintype ι]
    [LinearOrder (FreeGroup ι)] [MulLeftMono (FreeGroup ι)] [MulRightMono (FreeGroup ι)] :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra k D) (a : ι → D),
      Function.Injective (freeTensorBoundary k a) := by
  let : Ring (coefficientAlgebra (FreeGroup ι) k) := Subalgebra.toRing (A := Module.End k (HahnSeries (FreeGroup ι) k)) (coefficientAlgebra (FreeGroup ι) k)
  let : DivisionRing (coefficientAlgebra (FreeGroup ι) k) :=
    DivisionRing.ofIsUnitOrEqZero (unit_or_zero (G := FreeGroup ι) (k := k))
  refine ⟨coefficientAlgebra (FreeGroup ι) k,inferInstance,inferInstance,fun i ↦ monomial (FreeGroup.of i),?_⟩
  apply FreeGroupCoefficients.injective_boundary (fun g ↦ coeff g)
    (fun z u v ↦ finite_fiber (u.val (δ 1)) (v.val (δ 1)) z) _ coeff_separates
  · intro i z v
    exact shift_coeff (FreeGroup.of i) _ _
  · intro i z v
    exact coeff_mul_monomial v _ _

end EFiniteCharacterizations.OrderedGroupSeries
