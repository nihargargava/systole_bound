module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceBoundaryGraphWicksCertificate
public import BuserSarnak.FiniteListFirstReturn
public import BuserSarnak.OrientableWicksResidualCertificate

@[expose] public section

/-!
# Exact tree-splice first return of the actual peripheral transition

The original side pairing is split into its actual selected-tree and
non-tree parts. Cancelling the tree pairing from the original vertex
permutation gives the genuine tree-spliced permutation. The literal
filtered peripheral transition is its positive first return to the retained
non-tree sides, under the original-side decoder.

No transitivity or vertex-orbit identification is assumed here. To conclude
one orbit, the actual local vertex cycles must still be identified and
merged along the selected spanning tree.
-/

open Set UpperHalfPlane
open scoped UpperHalfPlane Classical

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- Original cyclic sides retained after deleting exactly the selected physical tree. -/
def intrinsicBoundaryRetainedSidePred (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) : Prop :=
  B.intrinsicBoundaryPhysicalEdge i ∉ range B.intrinsicBoundaryTreePhysicalEdge

theorem intrinsicBoundaryRetainedSidePred_pair (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryRetainedSidePred (B.intrinsicCyclicPairing i) ↔
      B.intrinsicBoundaryRetainedSidePred i := by
  unfold intrinsicBoundaryRetainedSidePred
  rw [B.intrinsicBoundaryPhysicalEdge_pair]

/-- Reverse exactly the two original orientations of each actually selected tree side. -/
def intrinsicBoundaryTreePairingPerm (B : DirichletBoundarySegments X o) :
    Equiv.Perm (Fin B.intrinsicBoundaryRadialCuts.card) := by
  classical
  let f := fun i => if B.intrinsicBoundaryRetainedSidePred i then i else B.intrinsicCyclicPairing i
  have hff : Function.Involutive f := by
    intro i
    by_cases hi : B.intrinsicBoundaryRetainedSidePred i
    · simp only [f, if_pos hi]
    · have hp : ¬ B.intrinsicBoundaryRetainedSidePred (B.intrinsicCyclicPairing i) :=
        fun hp => hi ((B.intrinsicBoundaryRetainedSidePred_pair i).mp hp)
      simp only [f, if_neg hi, if_neg hp]
      exact B.intrinsicCyclicPairing_involutive i
  exact ⟨f, f, hff, hff⟩

/-- Reverse exactly the retained non-tree sides and fix every deleted tree orientation. -/
def intrinsicBoundaryNonTreePairingPerm (B : DirichletBoundarySegments X o) :
    Equiv.Perm (Fin B.intrinsicBoundaryRadialCuts.card) := by
  classical
  let f := fun i => if B.intrinsicBoundaryRetainedSidePred i then B.intrinsicCyclicPairing i else i
  have hff : Function.Involutive f := by
    intro i
    by_cases hi : B.intrinsicBoundaryRetainedSidePred i
    · have hp := (B.intrinsicBoundaryRetainedSidePred_pair i).mpr hi
      simp only [f, if_pos hi, if_pos hp]
      exact B.intrinsicCyclicPairing_involutive i
    · simp only [f, if_neg hi]
  exact ⟨f, f, hff, hff⟩

theorem intrinsicBoundaryTreePairingPerm_apply (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryTreePairingPerm i =
      if B.intrinsicBoundaryRetainedSidePred i then i else B.intrinsicCyclicPairing i := rfl

theorem intrinsicBoundaryNonTreePairingPerm_apply (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryNonTreePairingPerm i =
      if B.intrinsicBoundaryRetainedSidePred i then B.intrinsicCyclicPairing i else i := rfl

/-- Tree cancellation leaves precisely the actual non-tree pairing. -/
theorem intrinsicBoundarySidePairingPerm_mul_treePairing
    (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundarySidePairingPerm * B.intrinsicBoundaryTreePairingPerm =
      B.intrinsicBoundaryNonTreePairingPerm := by
  classical
  apply Equiv.ext
  intro i
  change B.intrinsicCyclicPairing (B.intrinsicBoundaryTreePairingPerm i) = _
  rw [intrinsicBoundaryTreePairingPerm_apply, intrinsicBoundaryNonTreePairingPerm_apply]
  by_cases hi : B.intrinsicBoundaryRetainedSidePred i
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi, B.intrinsicCyclicPairing_involutive]

/-- The original local vertex transition with all actual tree attachments spliced. -/
def intrinsicBoundaryTreeSplicedVertexPerm (B : DirichletBoundarySegments X o) :
    Equiv.Perm (Fin B.intrinsicBoundaryRadialCuts.card) :=
  B.intrinsicBoundaryOriginalVertexPerm * B.intrinsicBoundaryTreePairingPerm

/-- This is the exact tree-splice factorization, not a support-only equality. -/
theorem intrinsicBoundaryTreeSplicedVertexPerm_eq (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundaryTreeSplicedVertexPerm =
      B.intrinsicBoundaryOriginalSideOrder.formPerm * B.intrinsicBoundaryNonTreePairingPerm := by
  rw [intrinsicBoundaryTreeSplicedVertexPerm, intrinsicBoundaryOriginalVertexPerm,
    mul_assoc, intrinsicBoundarySidePairingPerm_mul_treePairing]

private theorem signedOriginalSide_letter (B : DirichletBoundarySegments X o)
    (letter : B.IntrinsicBoundaryNonTreeEdge × Bool) :
    B.intrinsicBoundaryPeripheralSideLetter (B.intrinsicBoundaryPeripheralSignedOriginalSide letter) =
      some letter :=
  (B.intrinsicBoundaryPeripheralSideLetter_some_iff _ letter).mpr rfl

theorem Internal.SurfaceBoundaryGraphTreeOrbitHelpers.signedOriginalSide_retained (B : DirichletBoundarySegments X o)
    (letter : B.IntrinsicBoundaryNonTreeEdge × Bool) :
    B.intrinsicBoundaryRetainedSidePred (B.intrinsicBoundaryPeripheralSignedOriginalSide letter) := by
  intro ht
  have hn := (B.intrinsicBoundaryPeripheralSideLetter_eq_none_iff _).mpr ht
  rw [signedOriginalSide_letter] at hn
  cases hn

theorem Internal.SurfaceBoundaryGraphTreeOrbitHelpers.signedOriginalSide_injective (B : DirichletBoundarySegments X o) :
    Function.Injective B.intrinsicBoundaryPeripheralSignedOriginalSide := by
  intro a b h
  apply Option.some.inj
  rw [← signedOriginalSide_letter B a, ← signedOriginalSide_letter B b, h]

/-- The exact original-side decoder identifies signed letters with retained original sides. -/
def intrinsicBoundaryRetainedSideEquiv (B : DirichletBoundarySegments X o) :
    (B.IntrinsicBoundaryNonTreeEdge × Bool) ≃
      {i : Fin B.intrinsicBoundaryRadialCuts.card // B.intrinsicBoundaryRetainedSidePred i} :=
  Equiv.ofBijective
    (fun letter => ⟨B.intrinsicBoundaryPeripheralSignedOriginalSide letter,
      Internal.SurfaceBoundaryGraphTreeOrbitHelpers.signedOriginalSide_retained B letter⟩)
    ⟨fun _ _ h => Internal.SurfaceBoundaryGraphTreeOrbitHelpers.signedOriginalSide_injective B (congrArg Subtype.val h), by
      classical
      intro i
      let letter : B.IntrinsicBoundaryNonTreeEdge × Bool :=
        (⟨B.intrinsicBoundaryPhysicalEdge i.val, i.property⟩,
          if i.val < B.intrinsicCyclicPairing i.val then true else false)
      have hs : B.intrinsicBoundaryPeripheralSideLetter i.val = some letter := by
        rw [intrinsicBoundaryPeripheralSideLetter, dif_neg i.property]
      refine ⟨letter, Subtype.ext ?_⟩
      exact ((B.intrinsicBoundaryPeripheralSideLetter_some_iff _ letter).mp hs).symm⟩

@[simp]
theorem intrinsicBoundaryRetainedSideEquiv_val (B : DirichletBoundarySegments X o)
    (letter : B.IntrinsicBoundaryNonTreeEdge × Bool) :
    (B.intrinsicBoundaryRetainedSideEquiv letter).val =
      B.intrinsicBoundaryPeripheralSignedOriginalSide letter := rfl

private theorem signedOriginalSide_partner (B : DirichletBoundarySegments X o)
    (letter : B.IntrinsicBoundaryNonTreeEdge × Bool) :
    B.intrinsicBoundaryPeripheralSignedOriginalSide
        (signedLetterPartnerPerm B.IntrinsicBoundaryNonTreeEdge letter) =
      B.intrinsicCyclicPairing (B.intrinsicBoundaryPeripheralSignedOriginalSide letter) := by
  rcases letter with ⟨e, sign⟩
  cases sign
  · exact (B.intrinsicCyclicPairing_involutive e.val.val).symm
  · rfl

private theorem formPerm_map_originalSide (B : DirichletBoundarySegments X o)
    (letter : B.IntrinsicBoundaryNonTreeEdge × Bool) :
    (B.intrinsicBoundaryPeripheralLetters.map B.intrinsicBoundaryPeripheralSignedOriginalSide).formPerm
        (B.intrinsicBoundaryPeripheralSignedOriginalSide letter) =
      B.intrinsicBoundaryPeripheralSignedOriginalSide
        (B.intrinsicBoundaryPeripheralLetters.formPerm letter) := by
  classical
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem (B.intrinsicBoundaryPeripheralLetters_mem letter)
  rw [← hget]
  rw [List.formPerm_apply_getElem _ B.intrinsicBoundaryPeripheralLetters_nodup k hk]
  have hmap := List.formPerm_apply_getElem
    (B.intrinsicBoundaryPeripheralLetters.map B.intrinsicBoundaryPeripheralSignedOriginalSide)
    (List.Nodup.map (Internal.SurfaceBoundaryGraphTreeOrbitHelpers.signedOriginalSide_injective B) B.intrinsicBoundaryPeripheralLetters_nodup)
    k (by simpa only [List.length_map] using hk)
  simpa only [List.getElem_map, List.length_map] using hmap

/-- The signed transition is first return of the original reversed boundary after physical pairing. -/
theorem intrinsicBoundaryPeripheralTransition_boundaryFirstReturn
    (B : DirichletBoundarySegments X o) (letter : B.IntrinsicBoundaryNonTreeEdge × Bool) :
    B.intrinsicBoundaryPeripheralSignedOriginalSide
        ((B.intrinsicBoundaryPeripheralLetters.formPerm *
          signedLetterPartnerPerm B.IntrinsicBoundaryNonTreeEdge) letter) =
      (finitePermutationFirstReturn B.intrinsicBoundaryOriginalSideOrder.formPerm
        B.intrinsicBoundaryRetainedSidePred
        (B.intrinsicBoundaryRetainedSideEquiv
          (signedLetterPartnerPerm B.IntrinsicBoundaryNonTreeEdge letter))).val := by
  classical
  have hm := (formPerm_map_originalSide B
    (signedLetterPartnerPerm B.IntrinsicBoundaryNonTreeEdge letter)).symm
  rw [B.intrinsicBoundaryPeripheralLetters_originalSide_list] at hm
  have hfilter :
      (List.ofFn (fun i : Fin B.intrinsicBoundaryRadialCuts.card => i)).reverse.filter
          (fun i => decide (B.intrinsicBoundaryPhysicalEdge i ∉
            range B.intrinsicBoundaryTreePhysicalEdge)) =
        B.intrinsicBoundaryOriginalSideOrder.filter
          (fun i => decide (B.intrinsicBoundaryRetainedSidePred i)) := by
    apply List.filter_congr
    intro i hi
    by_cases ht : B.intrinsicBoundaryPhysicalEdge i ∈
        range B.intrinsicBoundaryTreePhysicalEdge
    · simp [intrinsicBoundaryRetainedSidePred, ht]
    · simp [intrinsicBoundaryRetainedSidePred, ht]
  rw [hfilter] at hm
  rw [Equiv.Perm.mul_apply]
  rw [hm]
  have hfirst := list_formPerm_filter_eq_firstReturn B.intrinsicBoundaryOriginalSideOrder
    (List.nodup_reverse.mpr (List.nodup_ofFn.mpr Function.injective_id))
    B.intrinsicBoundaryRetainedSidePred
    (B.intrinsicBoundaryRetainedSideEquiv
      (signedLetterPartnerPerm B.IntrinsicBoundaryNonTreeEdge letter))
  simpa only [intrinsicBoundaryRetainedSideEquiv_val] using hfirst

private theorem firstReturn_mul_eq_of_fix_complement
    {A : Type*} [Finite A] (f p : Equiv.Perm A) (P : A → Prop) [DecidablePred P]
    (hp : ∀ x, P x → P (p x)) (hfix : ∀ x, ¬ P x → p x = x)
    (x : {x : A // P x}) :
    (finitePermutationFirstReturn (f * p) P x).val =
      (finitePermutationFirstReturn f P ⟨p x.val, hp x.val x.property⟩).val := by
  let y : {x : A // P x} := ⟨p x.val, hp x.val x.property⟩
  let n := finitePermutationFirstReturnTime f P y
  have hn : 0 < n := finitePermutationFirstReturnTime_pos f P y
  have hbefore : ∀ k : ℕ, 0 < k → k < n → ¬ P (f^[k] y.val) := by
    intro k hk hkn
    exact finitePermutationFirstReturnTime_min f P y hk hkn
  have hiter : ∀ k : ℕ, 0 < k → k ≤ n → (f * p)^[k] x.val = f^[k] y.val := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
      intro _ hkn
      by_cases hk0 : k = 0
      · subst k
        rfl
      · have hk : 0 < k := Nat.pos_of_ne_zero hk0
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hk (by omega)]
        change f (p (f^[k] y.val)) = f (f^[k] y.val)
        rw [hfix _ (hbefore k hk (by omega))]
  have hgap : PositiveOrbitGap (f * p) P x.val (finitePermutationFirstReturn f P y).val := by
    refine ⟨n, hn, ?_, ?_⟩
    · exact hiter n hn (le_refl n)
    · intro k hk hkn
      rw [hiter k hk hkn.le]
      exact hbefore k hk hkn
  exact PositiveOrbitGap.firstReturn_val_eq
    (finitePermutation_exists_positive_return (f * p) P) x hgap
    (finitePermutationFirstReturn f P y).property

/-- The actual spliced vertex permutation has the same first return as boundary
advancement after crossing the retained original side. -/
theorem intrinsicBoundaryTreeSplicedVertexPerm_firstReturn
    (B : DirichletBoundarySegments X o)
    (x : {i : Fin B.intrinsicBoundaryRadialCuts.card // B.intrinsicBoundaryRetainedSidePred i}) :
    (finitePermutationFirstReturn B.intrinsicBoundaryTreeSplicedVertexPerm
      B.intrinsicBoundaryRetainedSidePred x).val =
      (finitePermutationFirstReturn B.intrinsicBoundaryOriginalSideOrder.formPerm
        B.intrinsicBoundaryRetainedSidePred
        ⟨B.intrinsicCyclicPairing x.val,
          (B.intrinsicBoundaryRetainedSidePred_pair x.val).mpr x.property⟩).val := by
  classical
  rw [intrinsicBoundaryTreeSplicedVertexPerm_eq]
  have hp : ∀ i, B.intrinsicBoundaryRetainedSidePred i →
      B.intrinsicBoundaryRetainedSidePred (B.intrinsicBoundaryNonTreePairingPerm i) := by
    intro i hi
    rw [intrinsicBoundaryNonTreePairingPerm_apply, if_pos hi]
    exact (B.intrinsicBoundaryRetainedSidePred_pair i).mpr hi
  have hfix : ∀ i, ¬ B.intrinsicBoundaryRetainedSidePred i →
      B.intrinsicBoundaryNonTreePairingPerm i = i := by
    intro i hi
    rw [intrinsicBoundaryNonTreePairingPerm_apply, if_neg hi]
  have h := firstReturn_mul_eq_of_fix_complement
    B.intrinsicBoundaryOriginalSideOrder.formPerm B.intrinsicBoundaryNonTreePairingPerm
    B.intrinsicBoundaryRetainedSidePred hp hfix x
  have hpair : (⟨B.intrinsicBoundaryNonTreePairingPerm x.val, hp x.val x.property⟩ :
      {i : Fin B.intrinsicBoundaryRadialCuts.card // B.intrinsicBoundaryRetainedSidePred i}) =
      ⟨B.intrinsicCyclicPairing x.val,
        (B.intrinsicBoundaryRetainedSidePred_pair x.val).mpr x.property⟩ := by
    apply Subtype.ext
    change B.intrinsicBoundaryNonTreePairingPerm x.val = B.intrinsicCyclicPairing x.val
    simp [intrinsicBoundaryNonTreePairingPerm, x.property]
  rw [hpair] at h
  exact h

/-- The literal filtered-word transition is conjugate to first return of the
actual tree-spliced vertex permutation. No transitivity premise is used. -/
theorem intrinsicBoundaryPeripheralTransition_treeFirstReturn
    (B : DirichletBoundarySegments X o) (letter : B.IntrinsicBoundaryNonTreeEdge × Bool) :
    B.intrinsicBoundaryRetainedSideEquiv
        ((B.intrinsicBoundaryPeripheralLetters.formPerm *
          signedLetterPartnerPerm B.IntrinsicBoundaryNonTreeEdge) letter) =
      finitePermutationFirstReturn B.intrinsicBoundaryTreeSplicedVertexPerm
        B.intrinsicBoundaryRetainedSidePred (B.intrinsicBoundaryRetainedSideEquiv letter) := by
  classical
  apply Subtype.ext
  rw [intrinsicBoundaryRetainedSideEquiv_val,
    intrinsicBoundaryPeripheralTransition_boundaryFirstReturn,
    intrinsicBoundaryTreeSplicedVertexPerm_firstReturn]
  have hstart : B.intrinsicBoundaryRetainedSideEquiv
      (signedLetterPartnerPerm B.IntrinsicBoundaryNonTreeEdge letter) =
      ⟨B.intrinsicCyclicPairing (B.intrinsicBoundaryRetainedSideEquiv letter).val,
        (B.intrinsicBoundaryRetainedSidePred_pair
          (B.intrinsicBoundaryRetainedSideEquiv letter).val).mpr
          (B.intrinsicBoundaryRetainedSideEquiv letter).property⟩ := by
    apply Subtype.ext
    simpa only [intrinsicBoundaryRetainedSideEquiv_val] using
      signedOriginalSide_partner B letter
  rw [hstart]

#print axioms intrinsicBoundaryTreeSplicedVertexPerm_eq
#print axioms intrinsicBoundaryPeripheralTransition_boundaryFirstReturn
#print axioms intrinsicBoundaryTreeSplicedVertexPerm_firstReturn
#print axioms intrinsicBoundaryPeripheralTransition_treeFirstReturn

end

end SystolicGrowth.DirichletBoundarySegments
