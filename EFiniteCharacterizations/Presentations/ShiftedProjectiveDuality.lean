module

public import EFiniteCharacterizations.Presentations.ProjectiveDuality
public import EFiniteCharacterizations.Presentations.StableAdd

/-! # Shifted projective duality for two-term complexes -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R]

private abbrev src (P : TwoTerm R) : FiniteProjective R := ⟨P.source,P.projective_source⟩
private abbrev tgt (P : TwoTerm R) : FiniteProjective R := ⟨P.target,P.projective_target⟩
private abbrev tr (P Q : FiniteProjective R) := FiniteProjective.transpose (P := P) (Q := Q)

/-- Dualize the projective terms and reverse degrees to obtain another two-term complex. -/
def shiftedDual (P : TwoTerm R) : TwoTerm Rᵐᵒᵖ :=
  let A : FiniteProjective R := ⟨P.source,P.projective_source⟩
  let B : FiniteProjective R := ⟨P.target,P.projective_target⟩
  ⟨B.star.val,A.star.val,B.star.property,A.star.property,FiniteProjective.transpose (P := A) (Q := B) P.differential⟩

theorem class_shiftedDual (P : TwoTerm R) :
    P.shiftedDual.projectiveClass = -ProjectiveClass.starEquiv R P.projectiveClass := by
  simp only [projectiveClass,map_sub,ProjectiveClass.starEquiv_of,neg_sub]
  rfl

private theorem presilting_iff_factorization (P : TwoTerm R) :
    P.IsPresilting ↔ ∀ f : P.source ⟶ P.target, ∃ a b, f = a ≫ P.differential + P.differential ≫ b := by
  constructor
  · intro h f
    obtain ⟨⟨a,b⟩,hf⟩ := h f
    exact ⟨a,-b,by simpa [homotopyBoundary,sub_eq_add_neg] using hf.symm⟩
  · intro h f
    obtain ⟨a,b,hf⟩ := h f
    exact ⟨(a,-b),by simpa [homotopyBoundary] using hf.symm⟩

/-- Shifted projective duality preserves and reflects the two-term presilting condition. -/
theorem isPresilting_shiftedDual_iff (P : TwoTerm R) : P.shiftedDual.IsPresilting ↔ P.IsPresilting := by
  rw [presilting_iff_factorization,presilting_iff_factorization]
  constructor
  · intro h f
    obtain ⟨a,b,he⟩ := h (tr (src P) (tgt P) f)
    obtain ⟨a',rfl⟩ := (FiniteProjective.transpose_bijective (tgt P) (tgt P)).2 a
    obtain ⟨b',rfl⟩ := (FiniteProjective.transpose_bijective (src P) (src P)).2 b
    refine ⟨b',a',(FiniteProjective.transpose_bijective (src P) (tgt P)).1 ?_⟩
    rw [map_add]
    exact he.trans (add_comm _ _)
  · intro h g
    obtain ⟨f,rfl⟩ := (FiniteProjective.transpose_bijective (src P) (tgt P)).2 g
    obtain ⟨a,b,he⟩ := h f
    exact ⟨tr (tgt P) (tgt P) b,tr (src P) (src P) a,by rw [he,map_add]; exact add_comm _ _⟩

private def transposeSquare (P Q : TwoTerm R) : (P.asArrow ⟶ Q.asArrow) →+ (Q.shiftedDual.asArrow ⟶ P.shiftedDual.asArrow) where
  toFun f := Arrow.homMk (tr (tgt P) (tgt Q) f.right) (tr (src P) (src Q) f.left) (by
    have h := congrArg (tr (src P) (tgt Q)) f.w
    exact h.symm)
  map_zero' := by apply Arrow.hom_ext <;> exact map_zero _
  map_add' f g := by apply Arrow.hom_ext <;> exact map_add _ _ _

private theorem transposeSquare_bijective (P Q : TwoTerm R) : Function.Bijective (transposeSquare P Q) := by
  constructor
  · intro f g h
    exact Arrow.hom_ext _ _ ((FiniteProjective.transpose_bijective (src P) (src Q)).1 (congrArg Arrow.Hom.right h))
      ((FiniteProjective.transpose_bijective (tgt P) (tgt Q)).1 (congrArg Arrow.Hom.left h))
  · intro g
    obtain ⟨l,hl⟩ := (FiniteProjective.transpose_bijective (src P) (src Q)).2 g.right
    obtain ⟨r,hr⟩ := (FiniteProjective.transpose_bijective (tgt P) (tgt Q)).2 g.left
    have hh : l ≫ Q.differential = P.differential ≫ r := by
      apply (FiniteProjective.transpose_bijective (src P) (tgt Q)).1
      change tr (src Q) (tgt Q) Q.differential ≫ tr (src P) (src Q) l = tr (tgt P) (tgt Q) r ≫ tr (src P) (tgt P) P.differential
      rw [show tr (src P) (src Q) l = _ from hl,show tr (tgt P) (tgt Q) r = _ from hr]
      exact g.w.symm
    exact ⟨Arrow.homMk l r hh,Arrow.hom_ext _ _ hr hl⟩

private theorem transposeSquare_comp {P Q T : TwoTerm R} (f : P.asArrow ⟶ Q.asArrow) (g : Q.asArrow ⟶ T.asArrow) :
    transposeSquare P T (f ≫ g) = transposeSquare Q T g ≫ transposeSquare P Q f := rfl

/-- The additive closure used to generate the real cones is invariant under shifted duality. -/
theorem inAdd_shiftedDual_iff (P Q : TwoTerm R) :
    IsInAdd P.shiftedDual.asArrow Q.shiftedDual.asArrow ↔ IsInAdd P.asArrow Q.asArrow := by
  classical
  let e (A B : TwoTerm R) := AddEquiv.ofBijective (transposeSquare A B) (transposeSquare_bijective A B)
  constructor
  · rintro ⟨l,hl⟩
    refine ⟨l.map (fun p ↦ ((e P Q).symm p.2,(e Q P).symm p.1)),(e P P).injective ?_⟩
    rw [map_list_sum,List.map_map,List.map_map]
    have hh (p : (P.shiftedDual.asArrow ⟶ Q.shiftedDual.asArrow) × (Q.shiftedDual.asArrow ⟶ P.shiftedDual.asArrow)) :
        e P P ((e P Q).symm p.2 ≫ (e Q P).symm p.1) = p.1 ≫ p.2 := by
      change e Q P ((e Q P).symm p.1) ≫ e P Q ((e P Q).symm p.2) = _
      simp
    exact (congrArg List.sum (List.map_congr_left fun p _ ↦ hh p)).trans hl
  · rintro ⟨l,hl⟩
    refine ⟨l.map (fun p ↦ (transposeSquare Q P p.2,transposeSquare P Q p.1)),?_⟩
    rw [List.map_map]
    have h := congrArg (transposeSquare P P) hl
    rw [map_list_sum,List.map_map] at h
    exact (congrArg List.sum (List.map_congr_left fun p _ ↦ (transposeSquare_comp (P := P) (Q := Q) (T := P) p.1 p.2).symm)).trans h

/-- Every opposite two-term differential is isomorphic to a shifted dual. -/
theorem exists_shiftedDual_iso (Q : TwoTerm Rᵐᵒᵖ) : ∃ P : TwoTerm R, Nonempty (P.shiftedDual.asArrow ≅ Q.asArrow) := by
  obtain ⟨A,⟨a⟩⟩ := FiniteProjective.exists_star_iso (tgt Q)
  obtain ⟨B,⟨b⟩⟩ := FiniteProjective.exists_star_iso (src Q)
  obtain ⟨f,hf⟩ := (FiniteProjective.transpose_bijective A B).2 (b.hom ≫ Q.differential ≫ a.inv)
  let P : TwoTerm R := ⟨A.val,B.val,A.property,B.property,f⟩
  refine ⟨P,⟨Arrow.isoMk b a ?_⟩⟩
  change b.hom ≫ Q.differential = FiniteProjective.transpose (P := A) (Q := B) f ≫ a.hom
  simp [hf]

end EFiniteCharacterizations.TwoTerm
