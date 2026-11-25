module

public import EFiniteCharacterizations.Geometry.BlockDegeneration
public import EFiniteCharacterizations.Geometry.KingDeterminants

/-! # Block degenerations inside an irreducible component -/

@[expose] public section

open TopologicalSpace
universe u
namespace EFiniteCharacterizations.VertexRepresentation

variable {k R I J : Type u} [Field k] [Ring R] [Algebra k R]
    [Fintype I] [DecidableEq I] [Fintype J] (b : Module.Basis J k R)
    {d : I → ℕ} {e : I → R}

local notation "X" => VertexRepresentation (k := k) d e
local notation "A" => coordinateAlgebra b d e
local notation "Z" => zariski (d := d) (e := e) b

omit [Fintype J] in
private theorem regular_eval_eq (p : MvPolynomial (J × (Σ i, Fin (d i)) × (Σ i, Fin (d i))) k)
    (x : X) : MvPolynomial.aeval (fun j y ↦ affineCoordinates b y j) p x =
      MvPolynomial.eval (affineCoordinates b x) p := by
  let E := Pi.evalAlgHom k (fun _ : X ↦ k) x
  change E (MvPolynomial.aeval _ p) = _
  rw [MvPolynomial.comp_aeval_apply]
  rfl

omit [Fintype J] in
/-- Closed subsets of the vertex variety are simultaneous zero sets of regular functions. -/
private theorem closed_iff_regular (C : Set X) :
    @IsClosed X Z C ↔ ∃ s : Set A, ∀ x, x ∈ C ↔ ∀ f ∈ s, f.val x = 0 := by
  classical
  let := Z
  constructor
  · intro h
    obtain ⟨T,hT,hpre⟩ := isClosed_induced_iff.mp h
    obtain ⟨p,rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus T).mp hT
    let F (q : MvPolynomial (J × (Σ i, Fin (d i)) × (Σ i, Fin (d i))) k) : A :=
      ⟨_,q,rfl⟩
    refine ⟨F '' p,fun x ↦ ?_⟩
    rw [← hpre]
    change (p ⊆ MvPolynomial.vanishingIdeal k {affineCoordinates b x}) ↔ _
    simp only [Set.forall_mem_image,Set.subset_def]
    exact forall_congr' fun q ↦ imp_congr_right fun _ ↦ by
      change q ∈ MvPolynomial.vanishingIdeal k {affineCoordinates b x} ↔ _
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      exact Iff.of_eq (congrArg (· = 0) (regular_eval_eq b q x).symm)
  · rintro ⟨s,hs⟩
    have hc : C = ⋂ f : s, {x | f.val.val x = 0} := Set.ext fun x ↦ by simp [hs]
    rw [hc]
    apply isClosed_iInter
    rintro ⟨⟨_,q,rfl⟩,_⟩
    change IsClosed {x : X | MvPolynomial.aeval (fun j y ↦ affineCoordinates b y j) q x = 0}
    simp_rw [regular_eval_eq]
    simpa only [Set.compl_ofPred,not_not] using (coordinateZariski_isOpen_ne_zero
      (affineCoordinates (e := e) b) q).isClosed_compl

private theorem regular_changeBasis (G : BaseChange k d) (f : A) :
    ∃ q : A, ∀ x, q.val x = f.val (G • x) := by
  classical
  let B := totalVertexBasis (k := k) d
  let F := LinearEquiv.piCongrRight G
  let M := LinearMap.toMatrix B B F.toLinearMap
  let N := LinearMap.toMatrix B B F.symm.toLinearMap
  let c (j : J) := fun a l ↦ actionEntry b d e (b j) a l
  let v (idx : J × (Σ i, Fin (d i)) × (Σ i, Fin (d i))) : A :=
    ∑ i, ∑ h, (M idx.2.1 i * N h idx.2.2) • c idx.1 i h
  have hv (idx) (x : X) : (v idx).val x = affineCoordinates b (G • x) idx := by
    obtain ⟨j,a,l⟩ := idx
    have he : (G • x).val (b j) = F.toLinearMap.comp ((x.val (b j)).comp F.symm.toLinearMap) := rfl
    have hm := congrArg (LinearMap.toMatrix B B) he
    rw [LinearMap.toMatrix_comp B B B, LinearMap.toMatrix_comp B B B] at hm
    have hcoord : affineCoordinates b (G • x) (j,a,l) =
        LinearMap.toMatrix B B ((G • x).val (b j)) a l := by
      simp only [affineCoordinates,actionMatrices,LinearMap.toMatrix_apply,vertexBasis,B,totalVertexBasis,
        Module.Basis.map_apply,Module.Basis.map_repr,LinearEquiv.trans_apply,LinearEquiv.symm_trans_apply,
        LinearEquiv.symm_symm,Algebra.lsmul_apply,coordinates_smul,LinearEquiv.apply_symm_apply]
    rw [hcoord,hm]
    simp [v,c,M,N,actionEntry,B,Matrix.mul_apply,Finset.mul_sum,mul_comm,mul_left_comm]
  obtain ⟨q,hq⟩ := f.property
  refine ⟨MvPolynomial.aeval v q,fun x ↦ ?_⟩
  let E := (Pi.evalAlgHom k (fun _ : X ↦ k) x).comp (coordinateAlgebra b d e).val
  change E (MvPolynomial.aeval v q) = _
  rw [MvPolynomial.comp_aeval_apply,← hq]
  change _ = MvPolynomial.aeval (fun j (y : X) ↦ affineCoordinates b y j) q (G • x)
  rw [regular_eval_eq]
  change MvPolynomial.aeval (fun i ↦ (v i).val x) q = _
  simp_rw [hv]
  rfl

omit [Fintype J] in
/-- The special point of a polynomial curve lies in a closed set containing its punctured curve. -/
theorem IsPolynomialCurve.special_mem [Infinite k] (C : Set X) (hC : @IsClosed _ Z C)
    {y : k → X} (hy : IsPolynomialCurve b y) (h : ∀ t : kˣ, y t ∈ C) : y 0 ∈ C := by
  obtain ⟨s,hs⟩ := (closed_iff_regular b C).1 hC
  apply (hs _).2
  intro f hf
  obtain ⟨p,hp⟩ := hy.pullback b f
  have he : p = 0 := p.eq_of_infinite_eval_eq 0 ((Set.finite_singleton (0 : k)).infinite_compl.mono
    fun t ht ↦ by
      change p.eval t = (0 : Polynomial k).eval t
      simpa only [Polynomial.eval_zero] using
      (hp t).trans ((hs _).1 (h (Units.mk0 t ht)) f hf))
  simpa [he] using (hp 0).symm

private theorem continuous_changeBasis (G : BaseChange k d) :
    @Continuous X X Z Z (G • ·) := by
  let := Z
  apply continuous_iff_isClosed.mpr
  intro C hC
  obtain ⟨s,hs⟩ := (closed_iff_regular b C).1 hC
  choose q hq using regular_changeBasis b G
  refine (closed_iff_regular b _).2 ⟨q '' s,fun x ↦ ?_⟩
  change G • x ∈ C ↔ _
  rw [hs]
  simp only [Set.forall_mem_image,hq]

private noncomputable def baseChangeHomeomorph (G : BaseChange k d) :
    @Homeomorph X X Z Z := by
  let := Z
  exact { MulAction.toPerm G with
    continuous_toFun := continuous_changeBasis b G
    continuous_invFun := continuous_changeBasis b G⁻¹ }

private noncomputable def componentPermutation :
    BaseChange k d →* Equiv.Perm (@irreducibleComponents X Z) := by
  let := Z
  let pre (G : BaseChange k d) (C : irreducibleComponents X) : irreducibleComponents X :=
    ⟨(G⁻¹ • ·) ⁻¹' C.val, preimage_mem_irreducibleComponents C.property
      (baseChangeHomeomorph b G⁻¹).isOpenEmbedding (by
        obtain ⟨x,hx⟩ := C.property.1.nonempty
        exact ⟨x,hx,G • x,inv_smul_smul G x⟩)⟩
  let perm (G : BaseChange k d) : Equiv.Perm (irreducibleComponents X) :=
    { toFun := pre G
      invFun := pre G⁻¹
      left_inv := fun C ↦ Subtype.ext (Set.ext fun x ↦ by
        change (G⁻¹ • (G⁻¹⁻¹ • x) ∈ C.val) ↔ _
        simp)
      right_inv := fun C ↦ Subtype.ext (Set.ext fun x ↦ by
        change (G⁻¹⁻¹ • (G⁻¹ • x) ∈ C.val) ↔ _
        simp) }
  exact { toFun := perm
          map_one' := Equiv.ext fun C ↦ Subtype.ext (Set.ext fun x ↦ by change (1 : BaseChange k d)⁻¹ • x ∈ C.val ↔ _; simp)
          map_mul' G H := Equiv.ext fun C ↦ Subtype.ext (Set.ext fun x ↦ by
            change (G * H)⁻¹ • x ∈ C.val ↔ H⁻¹ • (G⁻¹ • x) ∈ C.val
            simp [mul_smul]) }

/-- A multiplicative one-parameter subgroup fixes each component. It acts on a
finite set of components, while every nonzero scalar has an n-th root. -/
theorem oneParameter_mem_component [IsAlgClosed k] (G : kˣ →* BaseChange k d)
    (C : Set X) (hC : C ∈ @irreducibleComponents X Z) (x : X) (hx : x ∈ C) (t : kˣ) :
    G t • x ∈ C := by
  classical
  let := Z
  let : NoetherianSpace X := coordinateZariski_noetherian (affineCoordinates b)
  let := (NoetherianSpace.finite_irreducibleComponents (α := X)).fintype
  let H := (componentPermutation (e := e) b).comp G
  let n := Fintype.card (Equiv.Perm (irreducibleComponents X))
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (t : k) (n := n) Fintype.card_pos
  have hne : z ≠ 0 := by
    rintro rfl
    exact t.ne_zero (by rw [← hz,zero_pow (show n ≠ 0 from Fintype.card_ne_zero)])
  let u := Units.mk0 z hne
  have hu : u ^ n = t := Units.ext hz
  have he : H t = 1 := by rw [← hu,map_pow]; exact pow_card_eq_one
  have heC := congrArg (fun g : Equiv.Perm (irreducibleComponents X) ↦ (g ⟨C,hC⟩).val) he
  change ((G t)⁻¹ • ·) ⁻¹' C = C at heC
  rw [← heC]
  change (G t)⁻¹ • (G t • x) ∈ C
  simpa using hx

end EFiniteCharacterizations.VertexRepresentation
