module

public import EFiniteCharacterizations.Geometry.KingDegeneration

/-! # Scaling the extension block of an upper triangular representation -/

@[expose] public section

universe u
namespace EFiniteCharacterizations

variable {k R U V : Type u} [Field k] [Ring R] [Algebra k R]
    [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    (α : R →ₐ[k] Module.End k (U × V))

/-- The lower-left block vanishes exactly when the first summand is invariant. -/
def PreservesFirstSummand : Prop := ∀ r (u : U), (α r (u,0)).2 = 0

private theorem block_snd (h : PreservesFirstSummand α) (r : R) (u : U) (v : V) :
    (α r (u,v)).2 = (α r (0,v)).2 := by
  have he : (u,v) = (u,0) + (0,v) := by simp
  rw [he,map_add,Prod.snd_add,h,zero_add]

private theorem block_fst (r : R) (u : U) (v : V) :
    (α r (u,v)).1 = (α r (u,0)).1 + (α r (0,v)).1 := by
  have he : (u,v) = (u,0) + (0,v) := by simp
  rw [he,map_add,Prod.fst_add]

/-- Multiply the upper-right block by t, leaving the diagonal blocks fixed. -/
def scaleExtensionBlock (t : k) (h : PreservesFirstSummand α) : R →ₐ[k] Module.End k (U × V) where
  toFun r :=
    ((LinearMap.fst k U V ∘ₗ α r ∘ₗ LinearMap.inl k U V ∘ₗ LinearMap.fst k U V) +
      t • (LinearMap.fst k U V ∘ₗ α r ∘ₗ LinearMap.inr k U V ∘ₗ LinearMap.snd k U V)).prod
      (LinearMap.snd k U V ∘ₗ α r ∘ₗ LinearMap.inr k U V ∘ₗ LinearMap.snd k U V)
  map_zero' := by ext x <;> simp
  map_one' := by ext x <;> simp
  map_add' r s := by ext x <;> simp [smul_add,add_add_add_comm]
  map_mul' r s := by
    apply LinearMap.ext
    rintro ⟨u,v⟩
    change ((α (r*s) (u,0)).1 + t • (α (r*s) (0,v)).1, (α (r*s) (0,v)).2) = _
    rw [map_mul]
    have he : α s (u,0) = ((α s (u,0)).1,0) := Prod.ext rfl (h s u)
    change ((α r (α s (u,0))).1 + t • (α r (α s (0,v))).1, (α r (α s (0,v))).2) =
      ((α r ((α s (u,0)).1 + t • (α s (0,v)).1,0)).1 +
        t • (α r (0,(α s (0,v)).2)).1, (α r (0,(α s (0,v)).2)).2)
    rw [he,block_fst α r (α s (0,v)).1 (α s (0,v)).2,
      block_snd α h r (α s (0,v)).1 (α s (0,v)).2]
    have hh (a b : U) : (a+t • b,(0 : V)) = (a,0) + t • (b,0) := by simp
    rw [hh,map_add,map_smul]
    simp [smul_add,add_assoc]
  commutes' c := by ext x <;> simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem scaleExtensionBlock_apply (t : k) (h : PreservesFirstSummand α) (r : R) (z : U × V) :
    scaleExtensionBlock α t h r z =
      ((α r (z.1,0)).1 + t • (α r (0,z.2)).1,(α r (0,z.2)).2) := rfl

/-- The base change scaling the invariant first summand and fixing its complement. -/
def firstSummandScaling (t : kˣ) : (U × V) ≃ₗ[k] (U × V) :=
  (LinearEquiv.smulOfUnit t).prodCongr (LinearEquiv.refl k V)

theorem scaleExtensionBlock_at_unit (t : kˣ) (h : PreservesFirstSummand α) (r : R) :
    scaleExtensionBlock α (t : k) h r = (firstSummandScaling t).conjAlgEquiv k (α r) := by
  apply LinearMap.ext
  intro z
  obtain ⟨⟨u,v⟩,rfl⟩ := (firstSummandScaling (U := U) (V := V) t).surjective z
  change scaleExtensionBlock α (t : k) h r _ = firstSummandScaling t (α r ((firstSummandScaling t).symm _))
  rw [LinearEquiv.symm_apply_apply]
  change ((α r ((t : k) • u,0)).1 + (t : k) • (α r (0,v)).1,(α r (0,v)).2) =
    ((t : k) • (α r (u,v)).1,(α r (u,v)).2)
  have he : ((t : k) • u,(0 : V)) = (t : k) • (u,0) := by simp
  rw [he,map_smul,block_fst α r u v,block_snd α h r u v,smul_add]
  rfl

theorem det_firstSummandScaling [Module.Finite k U] [Module.Finite k V] (t : kˣ) :
    LinearEquiv.det (firstSummandScaling (U := U) (V := V) t) = t ^ Module.finrank k U := by
  apply Units.ext
  rw [LinearEquiv.coe_det, firstSummandScaling, LinearEquiv.coe_prodCongr, LinearMap.det_prodMap]
  change LinearMap.det ((t : k) • (LinearMap.id : U →ₗ[k] U)) * LinearMap.det (LinearMap.id : V →ₗ[k] V) = _
  simp [LinearMap.det_smul]

/-- The dependence on the parameter is affine linear in the endomorphism space. -/
theorem scaleExtensionBlock_affine (h : PreservesFirstSummand α) (r : R) (t : k) :
    scaleExtensionBlock α t h r = scaleExtensionBlock α 0 h r +
      t • (α r - scaleExtensionBlock α 0 h r) := by
  apply LinearMap.ext
  rintro ⟨u,v⟩
  apply Prod.ext
  · change (α r (u,0)).1 + t • (α r (0,v)).1 =
      ((α r (u,0)).1 + (0 : k) • (α r (0,v)).1) +
        t • ((α r (u,v)).1 - ((α r (u,0)).1 + (0 : k) • (α r (0,v)).1))
    simp [block_fst α r u v]
  · change (α r (0,v)).2 = (α r (0,v)).2 + t • ((α r (u,v)).2 - (α r (0,v)).2)
    simp [block_snd α h r u v]

namespace VertexRepresentation

variable {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] (b : Module.Basis J k R)
    {d : I → ℕ} {e : I → R}

omit [Fintype J] in
theorem isPolynomialCurve_of_affine_actions (y : k → VertexRepresentation (k := k) d e)
    (A B : R → Module.End k (VertexSpace k d))
    (h : ∀ t r, (y t).val r = A r + t • B r) : IsPolynomialCurve b y := by
  classical
  let v := (Pi.basisFun k (Σ i, Fin (d i))).map (LinearEquiv.piCurry k (fun i (_ : Fin (d i)) ↦ k))
  rintro ⟨j,a,l⟩
  refine ⟨Polynomial.C (LinearMap.toMatrix v v (A (b j)) a l) +
    Polynomial.X * Polynomial.C (LinearMap.toMatrix v v (B (b j)) a l), fun t ↦ ?_⟩
  have he := congrArg (fun F ↦ LinearMap.toMatrix v v F a l) (h t (b j))
  simp only [map_add,map_smul,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at he
  simpa only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,
    affineCoordinates,actionMatrices,LinearMap.toMatrix_apply,vertexBasis,Module.Basis.map_apply,
    Module.Basis.map_repr,LinearEquiv.trans_apply,LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm,Algebra.lsmul_apply,coordinates_smul,LinearEquiv.apply_symm_apply,v]
    using he.symm

variable {P Q : I → Type u} [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    [∀ i, AddCommGroup (Q i)] [∀ i, Module k (Q i)]
    (E : ∀ i, (Fin (d i) → k) ≃ₗ[k] (P i × Q i))

/-- A vertexwise choice of complements separates the total space into two summands. -/
def vertexSplitting : VertexSpace k d ≃ₗ[k] ((∀ i, P i) × (∀ i, Q i)) where
  toFun z := (fun i ↦ (E i (z i)).1, fun i ↦ (E i (z i)).2)
  invFun z := fun i ↦ (E i).symm (z.1 i,z.2 i)
  left_inv z := by ext i j; simp
  right_inv z := by ext i <;> simp
  map_add' z y := by ext i <;> simp
  map_smul' c z := by ext i <;> simp

variable (ρ : VertexRepresentation (k := k) d e)

abbrev splitAction := ((vertexSplitting E).conjAlgEquiv k).toAlgHom.comp ρ.val

/-- Rescale the extension on the fixed vertex spaces. -/
def blockCurve (h : PreservesFirstSummand (splitAction E ρ)) (t : k) :
    VertexRepresentation (k := k) d e := by
  let F := vertexSplitting E
  let α := splitAction E ρ
  refine ⟨(F.symm.conjAlgEquiv k).toAlgHom.comp (scaleExtensionBlock α t h),fun i ↦ ?_⟩
  apply LinearMap.ext
  intro z
  apply F.injective
  change F (F.symm (scaleExtensionBlock α t h (e i) (F z))) = _
  rw [F.apply_symm_apply,scaleExtensionBlock_apply]
  have hv (a : (∀ i, P i) × (∀ i, Q i)) (j : I) :
      E j ((ρ.val (e i) (F.symm a)) j) = if j = i then (a.1 j,a.2 j) else 0 := by
    rw [ρ.property]
    by_cases hj : j = i
    · subst j
      simp [vertexProjection,F,vertexSplitting]
    · simp [vertexProjection,hj,F,vertexSplitting]
  apply Prod.ext <;> funext j
  · change (E j ((ρ.val (e i) (F.symm ((F z).1,0))) j)).1 +
      t • (E j ((ρ.val (e i) (F.symm (0,(F z).2))) j)).1 = (E j ((vertexProjection d i z) j)).1
    rw [hv,hv]
    by_cases hj : j = i
    · subst j; simp [vertexProjection,F,vertexSplitting]
    · simp [hj,vertexProjection]
  · change (E j ((ρ.val (e i) (F.symm (0,(F z).2))) j)).2 = (E j ((vertexProjection d i z) j)).2
    rw [hv]
    by_cases hj : j = i
    · subst j; simp [vertexProjection,F,vertexSplitting]
    · simp [hj,vertexProjection]

omit [Fintype J] in
theorem blockCurve_polynomial (h : PreservesFirstSummand (splitAction E ρ)) :
    IsPolynomialCurve b (blockCurve E ρ h) := by
  let α := splitAction E ρ
  let F := (vertexSplitting E).symm.conjAlgEquiv k
  apply isPolynomialCurve_of_affine_actions b _
    (fun r ↦ F (scaleExtensionBlock α 0 h r)) (fun r ↦ F (α r - scaleExtensionBlock α 0 h r))
  intro t r
  change F (scaleExtensionBlock α t h r) = _
  rw [scaleExtensionBlock_affine,map_add,map_smul]

def blockBaseChange (t : kˣ) : BaseChange k d :=
  fun i ↦ ((E i).trans (firstSummandScaling t)).trans (E i).symm

/-- Scaling the first term of a vertex splitting is a one-parameter subgroup. -/
def blockBaseChangeHom : kˣ →* BaseChange k d where
  toFun := blockBaseChange E
  map_one' := by
    funext i
    apply LinearEquiv.ext
    intro x
    apply (E i).injective
    change E i ((E i).symm _) = E i x
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext (one_smul k _) rfl
  map_mul' t s := by
    funext i
    apply LinearEquiv.ext
    intro x
    apply (E i).injective
    simp only [blockBaseChange,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,
      Pi.mul_apply,LinearEquiv.mul_apply]
    exact Prod.ext (mul_smul (t : k) (s : k) _) rfl

theorem blockCurve_at_unit (h : PreservesFirstSummand (splitAction E ρ)) (t : kˣ) :
    blockCurve E ρ h (t : k) = blockBaseChange E t • ρ := by
  let F := vertexSplitting E
  let T := firstSummandScaling (U := ∀ i, P i) (V := ∀ i, Q i) t
  let G := LinearEquiv.piCongrRight (blockBaseChange E t)
  have hg (z : VertexSpace k d) : G z = F.symm (T (F z)) := rfl
  apply Subtype.ext
  apply AlgHom.ext
  intro r
  apply LinearMap.ext
  intro z
  obtain ⟨v,rfl⟩ := G.surjective z
  change F.symm (scaleExtensionBlock (splitAction E ρ) (t : k) h r (F (G v))) =
    G (ρ.val r (G.symm (G v)))
  rw [G.symm_apply_apply,hg,hg,F.apply_symm_apply,scaleExtensionBlock_at_unit]
  change F.symm (T (F (ρ.val r (F.symm (T.symm (T (F v))))))) = _
  rw [T.symm_apply_apply,F.symm_apply_apply]

variable [∀ i, Module.Finite k (P i)] [∀ i, Module.Finite k (Q i)] (w : I → ℤ)

theorem blockBaseChange_character (t : kˣ) :
    vertexCharacter d w (blockBaseChange E t) = t ^ (∑ i, (Module.finrank k (P i) : ℤ) * w i) := by
  change ∏ i, LinearEquiv.det (blockBaseChange E t i) ^ w i = _
  have hd (i : I) : LinearEquiv.det (blockBaseChange E t i) = t ^ Module.finrank k (P i) :=
    by simpa only [blockBaseChange,LinearEquiv.symm_symm] using
      (LinearEquiv.det_conj (firstSummandScaling (U := P i) (V := Q i) t) (E i).symm).trans
        (det_firstSummandScaling (U := P i) (V := Q i) t)
  simp only [hd]
  generalize (Finset.univ : Finset I) = S
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => simp [hi,ih,zpow_add,zpow_mul]

/-- A positive-degree semi-invariant can be nonzero only if each invariant
first summand in a vertex splitting has nonpositive weight. -/
theorem block_weight_nonpos_of_nonvanishing [Infinite k]
    (h : PreservesFirstSummand (splitAction E ρ)) (m : ℕ) (hm : 0 < m)
    (f : KingPiece b d e w m) (hf : f.val.val ρ ≠ 0) :
    ∑ i, (Module.finrank k (P i) : ℤ) * w i ≤ 0 := by
  by_contra! hn
  let n := ∑ i, (Module.finrank k (P i) : ℤ) * w i
  have hpos : 0 < n := hn
  exact hf (eval_zero_of_positive_character b w ρ (blockCurve_polynomial b E ρ h)
    (blockBaseChange E) (blockCurve_at_unit E ρ h) n.toNat (by omega)
    (fun t ↦ by rw [blockBaseChange_character,← zpow_natCast,Int.toNat_of_nonneg hpos.le]) m hm f)

end VertexRepresentation

end EFiniteCharacterizations
