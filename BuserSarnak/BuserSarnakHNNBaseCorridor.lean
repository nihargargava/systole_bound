module

public import BuserSarnak.BuserSarnakBaseReducedWord
public import BuserSarnak.BuserSarnakFiniteStatePingPong
public import BuserSarnak.BuserSarnakConeBoundarySeparation
public import BuserSarnak.BuserSarnakHNNBoundaryPingPong

@[expose] public section

/-!
# The two base-word corridors at the octagon HNN boundary

The associated source and target elements have reduced free-product words

* `e₂ A⁻¹ e₃` and
* `e₁ A⁻¹ e₄`.

Their inverses give the opposite orientations.  This file records those four
words at the level of the canonical dependent alphabet, proves their weights,
and packages the exact three-state boundary cycles.  These are the concrete
corridors needed to classify a reduced base word whose translate meets one of
the two associated boundary intervals.
-/

open scoped MatrixGroups Pointwise

namespace SystolicGrowth

noncomputable section

local instance : DecidableEq OctagonBaseFactor := Classical.decEq _
local instance (i : OctagonBaseFactor) :
    DecidableEq (OctagonBaseFactorGroup i) := Classical.decEq _

abbrev OctagonBaseCorridorLetter :=
  Σ i, OctagonBaseFactorGroup i

/-- An integral power of the handle factor, as a candidate reduced-word
letter.  The reducedness predicate below excludes the zero power. -/
def octagonHandleCorridorLetter (n : ℤ) : OctagonBaseCorridorLetter :=
  ⟨.handle,
    ⟨octagonBaseA ^ n, Subgroup.zpow_mem_zpowers octagonBaseA n⟩⟩

/-- A cone-factor generator, as a reduced-word letter. -/
def octagonConeCorridorLetter (i : OctagonBaseFactor) :
    OctagonBaseCorridorLetter :=
  ⟨i, octagonBaseFactorGenerator i⟩

/-- The source corridor in the negative-exponent orientation. -/
def octagonSourceForwardCycle : List OctagonBaseCorridorLetter :=
  [octagonConeCorridorLetter .cone2,
    octagonHandleCorridorLetter (-1),
    octagonConeCorridorLetter .cone3]

/-- The source corridor in the positive-exponent orientation. -/
def octagonSourceBackwardCycle : List OctagonBaseCorridorLetter :=
  [octagonConeCorridorLetter .cone3,
    octagonHandleCorridorLetter 1,
    octagonConeCorridorLetter .cone2]

/-- The target corridor in the negative-exponent orientation. -/
def octagonTargetForwardCycle : List OctagonBaseCorridorLetter :=
  [octagonConeCorridorLetter .cone1,
    octagonHandleCorridorLetter (-1),
    octagonConeCorridorLetter .cone4]

/-- The target corridor in the positive-exponent orientation. -/
def octagonTargetBackwardCycle : List OctagonBaseCorridorLetter :=
  [octagonConeCorridorLetter .cone4,
    octagonHandleCorridorLetter 1,
    octagonConeCorridorLetter .cone1]

@[simp] lemma octagonSourceForwardCycle_ne_nil :
    octagonSourceForwardCycle ≠ [] := by
  simp [octagonSourceForwardCycle]

@[simp] lemma octagonSourceBackwardCycle_ne_nil :
    octagonSourceBackwardCycle ≠ [] := by
  simp [octagonSourceBackwardCycle]

@[simp] lemma octagonTargetForwardCycle_ne_nil :
    octagonTargetForwardCycle ≠ [] := by
  simp [octagonTargetForwardCycle]

@[simp] lemma octagonTargetBackwardCycle_ne_nil :
    octagonTargetBackwardCycle ≠ [] := by
  simp [octagonTargetBackwardCycle]

@[simp] lemma octagonBaseReducedLetterValue_handleCorridorLetter (n : ℤ) :
    octagonBaseReducedLetterValue (octagonHandleCorridorLetter n) =
      octagonBaseA ^ n := rfl

@[simp] lemma octagonBaseReducedLetterValue_coneCorridorLetter
    (i : OctagonBaseFactor) :
    octagonBaseReducedLetterValue (octagonConeCorridorLetter i) =
      octagonBaseFactorElement i := rfl

@[simp] lemma octagonBaseReducedLetterWeight_handleCorridorLetter (n : ℤ) :
    octagonBaseReducedLetterWeight (octagonHandleCorridorLetter n) = n := by
  change Multiplicative.toAdd
      (octagonBaseExponent (octagonBaseA ^ n)) = n
  rw [map_zpow]
  simp [octagonBaseA, octagonBaseExponentImage]

@[simp] lemma octagonBaseReducedLetterWeight_coneCorridorLetter
    (i : OctagonBaseFactor) (hi : i ≠ .handle) :
    octagonBaseReducedLetterWeight (octagonConeCorridorLetter i) = 0 := by
  cases i with
  | handle => exact (hi rfl).elim
  | cone1 =>
      change Multiplicative.toAdd
        (octagonBaseExponent octagonBaseE1) = 0
      simp [octagonBaseE1, octagonBaseExponentImage]
  | cone2 =>
      change Multiplicative.toAdd
        (octagonBaseExponent octagonBaseE2) = 0
      simp [octagonBaseE2, octagonBaseExponentImage]
  | cone3 =>
      change Multiplicative.toAdd
        (octagonBaseExponent octagonBaseE3) = 0
      simp [octagonBaseE3, octagonBaseExponentImage]
  | cone4 =>
      change Multiplicative.toAdd
        (octagonBaseExponent octagonBaseE4) = 0
      simp [octagonBaseE4, octagonBaseExponentImage]

private lemma octagonBaseE1_inv : octagonBaseE1⁻¹ = octagonBaseE1 := by
  have h : octagonBaseE1 * octagonBaseE1 = 1 := by
    simpa [octagonBaseE1, pow_two] using octagonBase_e1_sq
  exact (eq_inv_of_mul_eq_one_left h).symm

private lemma octagonBaseE2_inv : octagonBaseE2⁻¹ = octagonBaseE2 := by
  have h : octagonBaseE2 * octagonBaseE2 = 1 := by
    simpa [octagonBaseE2, pow_two] using octagonBase_e2_sq
  exact (eq_inv_of_mul_eq_one_left h).symm

private lemma octagonBaseE3_inv : octagonBaseE3⁻¹ = octagonBaseE3 := by
  have h : octagonBaseE3 * octagonBaseE3 = 1 := by
    simpa [octagonBaseE3, pow_two] using octagonBase_e3_sq
  exact (eq_inv_of_mul_eq_one_left h).symm

private lemma octagonBaseE4_inv : octagonBaseE4⁻¹ = octagonBaseE4 := by
  have h : octagonBaseE4 * octagonBaseE4 = 1 := by
    simpa [octagonBaseE4, pow_two] using octagonBase_e4_sq
  exact (eq_inv_of_mul_eq_one_left h).symm

@[simp] lemma octagonSourceForwardCycle_weight :
    FiniteStatePingPong.weight octagonBaseReducedLetterWeight
      octagonSourceForwardCycle = -1 := by
  simp [FiniteStatePingPong.weight, octagonSourceForwardCycle]

@[simp] lemma octagonSourceBackwardCycle_weight :
    FiniteStatePingPong.weight octagonBaseReducedLetterWeight
      octagonSourceBackwardCycle = 1 := by
  simp [FiniteStatePingPong.weight, octagonSourceBackwardCycle]

@[simp] lemma octagonTargetForwardCycle_weight :
    FiniteStatePingPong.weight octagonBaseReducedLetterWeight
      octagonTargetForwardCycle = -1 := by
  simp [FiniteStatePingPong.weight, octagonTargetForwardCycle]

@[simp] lemma octagonTargetBackwardCycle_weight :
    FiniteStatePingPong.weight octagonBaseReducedLetterWeight
      octagonTargetBackwardCycle = 1 := by
  simp [FiniteStatePingPong.weight, octagonTargetBackwardCycle]

@[simp] lemma octagonSourceForwardCycle_value :
    (octagonSourceForwardCycle.map octagonBaseReducedLetterValue).prod =
      octagonBaseSourceElement := by
  change octagonBaseE2 * (octagonBaseA⁻¹ * octagonBaseE3) =
    octagonBaseSourceElement
  simp only [octagonBaseSourceElement]
  group

@[simp] lemma octagonSourceBackwardCycle_value :
    (octagonSourceBackwardCycle.map octagonBaseReducedLetterValue).prod =
      octagonBaseSourceElement⁻¹ := by
  change octagonBaseE3 * (octagonBaseA * octagonBaseE2) =
    octagonBaseSourceElement⁻¹
  simp only [octagonBaseSourceElement, mul_inv_rev, inv_inv,
    octagonBaseE2_inv, octagonBaseE3_inv]

@[simp] lemma octagonTargetForwardCycle_value :
    (octagonTargetForwardCycle.map octagonBaseReducedLetterValue).prod =
      octagonBaseTargetElement := by
  change octagonBaseE1 * (octagonBaseA⁻¹ * octagonBaseE4) =
    octagonBaseTargetElement
  simp only [octagonBaseTargetElement, octagonBaseE1_inv,
    octagonBaseE4_inv]
  group

@[simp] lemma octagonTargetBackwardCycle_value :
    (octagonTargetBackwardCycle.map octagonBaseReducedLetterValue).prod =
      octagonBaseTargetElement⁻¹ := by
  change octagonBaseE4 * (octagonBaseA * octagonBaseE1) =
    octagonBaseTargetElement⁻¹
  simp only [octagonBaseTargetElement, mul_inv_rev, inv_inv,
    octagonBaseE1_inv, octagonBaseE4_inv]

/-! ## Exact boundary cycles -/

/-- The interval adjacent to the source interval across the `e₂` side. -/
def octagonHNNSourceCone2CorridorSet : Set OctagonProjectiveBoundary :=
  octagonBaseToPGL23 octagonBaseE2 • octagonHNNSourceBoundarySet

/-- The interval adjacent to the source interval across the `e₃` side. -/
def octagonHNNSourceCone3CorridorSet : Set OctagonProjectiveBoundary :=
  octagonBaseToPGL23 octagonBaseE3 • octagonHNNSourceBoundarySet

/-- The interval adjacent to the target interval across the `e₁` side. -/
def octagonHNNTargetCone1CorridorSet : Set OctagonProjectiveBoundary :=
  octagonBaseToPGL23 octagonBaseE1 • octagonHNNTargetBoundarySet

/-- The interval adjacent to the target interval across the `e₄` side. -/
def octagonHNNTargetCone4CorridorSet : Set OctagonProjectiveBoundary :=
  octagonBaseToPGL23 octagonBaseE4 • octagonHNNTargetBoundarySet

private lemma octagonBaseToPGL23_E1_sq :
    octagonBaseToPGL23 octagonBaseE1 ^ 2 = 1 := by
  rw [← map_pow, show octagonBaseE1 ^ 2 = 1 by
    exact octagonBase_e1_sq, map_one]

private lemma octagonBaseToPGL23_E2_sq :
    octagonBaseToPGL23 octagonBaseE2 ^ 2 = 1 := by
  rw [← map_pow, show octagonBaseE2 ^ 2 = 1 by
    exact octagonBase_e2_sq, map_one]

private lemma octagonBaseToPGL23_E3_sq :
    octagonBaseToPGL23 octagonBaseE3 ^ 2 = 1 := by
  rw [← map_pow, show octagonBaseE3 ^ 2 = 1 by
    exact octagonBase_e3_sq, map_one]

private lemma octagonBaseToPGL23_E4_sq :
    octagonBaseToPGL23 octagonBaseE4 ^ 2 = 1 := by
  rw [← map_pow, show octagonBaseE4 ^ 2 = 1 by
    exact octagonBase_e4_sq, map_one]

/-- The `e₂` involution exchanges the source interval and its first corridor
interval. -/
lemma octagon_E2_smul_sourceCone2CorridorSet :
    octagonBaseToPGL23 octagonBaseE2 •
        octagonHNNSourceCone2CorridorSet =
      octagonHNNSourceBoundarySet := by
  rw [octagonHNNSourceCone2CorridorSet, ← mul_smul,
    ← pow_two, octagonBaseToPGL23_E2_sq, one_smul]

/-- The `e₃` involution exchanges the source interval and its second corridor
interval. -/
lemma octagon_E3_smul_sourceCone3CorridorSet :
    octagonBaseToPGL23 octagonBaseE3 •
        octagonHNNSourceCone3CorridorSet =
      octagonHNNSourceBoundarySet := by
  rw [octagonHNNSourceCone3CorridorSet, ← mul_smul,
    ← pow_two, octagonBaseToPGL23_E3_sq, one_smul]

/-- The handle generator carries the `e₂` source-corridor interval to the
`e₃` source-corridor interval. -/
lemma octagon_A_smul_sourceCone2CorridorSet :
    octagonBaseToPGL23 octagonBaseA •
        octagonHNNSourceCone2CorridorSet =
      octagonHNNSourceCone3CorridorSet := by
  have hstab : octagonBaseToPGL23 octagonBaseSourceElement •
      octagonHNNSourceBoundarySet = octagonHNNSourceBoundarySet := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [octagonBaseToPGL23_sourceElement]
    exact octagonHNNSourceQuaternionUnit_mem_stabilizer
  rw [octagonHNNSourceCone2CorridorSet,
    octagonHNNSourceCone3CorridorSet]
  rw [← mul_smul]
  calc
    (octagonBaseToPGL23 octagonBaseA *
          octagonBaseToPGL23 octagonBaseE2) •
        octagonHNNSourceBoundarySet =
        (octagonBaseToPGL23 octagonBaseA *
          octagonBaseToPGL23 octagonBaseE2) •
          (octagonBaseToPGL23 octagonBaseSourceElement •
            octagonHNNSourceBoundarySet) := by rw [hstab]
    _ = ((octagonBaseToPGL23 octagonBaseA *
          octagonBaseToPGL23 octagonBaseE2) *
            octagonBaseToPGL23 octagonBaseSourceElement) •
          octagonHNNSourceBoundarySet := by simp only [mul_smul]
    _ = octagonBaseToPGL23 octagonBaseE3 •
          octagonHNNSourceBoundarySet := by
      congr 1
      simp only [octagonBaseSourceElement, map_mul, map_inv]
      calc
        _ = octagonBaseToPGL23 octagonBaseA *
              (octagonBaseToPGL23 octagonBaseE2 *
                octagonBaseToPGL23 octagonBaseE2) *
              (octagonBaseToPGL23 octagonBaseA)⁻¹ *
              octagonBaseToPGL23 octagonBaseE3 := by group
        _ = octagonBaseToPGL23 octagonBaseE3 := by
          rw [show octagonBaseToPGL23 octagonBaseE2 *
              octagonBaseToPGL23 octagonBaseE2 = 1 by
                simpa [pow_two] using octagonBaseToPGL23_E2_sq]
          simp

/-- The inverse handle step traverses the source corridor in the opposite
direction. -/
lemma octagon_A_inv_smul_sourceCone3CorridorSet :
    (octagonBaseToPGL23 octagonBaseA)⁻¹ •
        octagonHNNSourceCone3CorridorSet =
      octagonHNNSourceCone2CorridorSet := by
  rw [← octagon_A_smul_sourceCone2CorridorSet]
  simp

/-- The `e₁` involution exchanges the target interval and its first corridor
interval. -/
lemma octagon_E1_smul_targetCone1CorridorSet :
    octagonBaseToPGL23 octagonBaseE1 •
        octagonHNNTargetCone1CorridorSet =
      octagonHNNTargetBoundarySet := by
  rw [octagonHNNTargetCone1CorridorSet, ← mul_smul,
    ← pow_two, octagonBaseToPGL23_E1_sq, one_smul]

/-- The `e₄` involution exchanges the target interval and its second corridor
interval. -/
lemma octagon_E4_smul_targetCone4CorridorSet :
    octagonBaseToPGL23 octagonBaseE4 •
        octagonHNNTargetCone4CorridorSet =
      octagonHNNTargetBoundarySet := by
  rw [octagonHNNTargetCone4CorridorSet, ← mul_smul,
    ← pow_two, octagonBaseToPGL23_E4_sq, one_smul]

/-- The handle generator carries the `e₁` target-corridor interval to the
`e₄` target-corridor interval. -/
lemma octagon_A_smul_targetCone1CorridorSet :
    octagonBaseToPGL23 octagonBaseA •
        octagonHNNTargetCone1CorridorSet =
      octagonHNNTargetCone4CorridorSet := by
  have hstab : octagonBaseToPGL23 octagonBaseTargetElement •
      octagonHNNTargetBoundarySet = octagonHNNTargetBoundarySet := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [octagonBaseToPGL23_targetElement]
    exact octagonHNNTargetQuaternionUnit_mem_stabilizer
  rw [octagonHNNTargetCone1CorridorSet,
    octagonHNNTargetCone4CorridorSet]
  rw [← mul_smul]
  calc
    (octagonBaseToPGL23 octagonBaseA *
          octagonBaseToPGL23 octagonBaseE1) •
        octagonHNNTargetBoundarySet =
        (octagonBaseToPGL23 octagonBaseA *
          octagonBaseToPGL23 octagonBaseE1) •
          (octagonBaseToPGL23 octagonBaseTargetElement •
            octagonHNNTargetBoundarySet) := by rw [hstab]
    _ = ((octagonBaseToPGL23 octagonBaseA *
          octagonBaseToPGL23 octagonBaseE1) *
            octagonBaseToPGL23 octagonBaseTargetElement) •
          octagonHNNTargetBoundarySet := by simp only [mul_smul]
    _ = octagonBaseToPGL23 octagonBaseE4 •
          octagonHNNTargetBoundarySet := by
      congr 1
      simp only [octagonBaseTargetElement, map_mul, map_inv]
      have hE4inv : (octagonBaseToPGL23 octagonBaseE4)⁻¹ =
          octagonBaseToPGL23 octagonBaseE4 := by
        exact (eq_inv_of_mul_eq_one_left (by
          simpa [pow_two] using octagonBaseToPGL23_E4_sq)).symm
      rw [hE4inv]
      group

/-- The inverse handle step traverses the target corridor in the opposite
direction. -/
lemma octagon_A_inv_smul_targetCone4CorridorSet :
    (octagonBaseToPGL23 octagonBaseA)⁻¹ •
        octagonHNNTargetCone4CorridorSet =
      octagonHNNTargetCone1CorridorSet := by
  rw [← octagon_A_smul_targetCone1CorridorSet]
  simp

private lemma octagonCorridorLetterPGL_prod
    (w : List OctagonBaseCorridorLetter) :
    (w.map octagonBaseReducedLetterPGL).prod =
      octagonBaseToPGL23
        (w.map octagonBaseReducedLetterValue).prod := by
  induction w with
  | nil => simp
  | cons l w ih =>
      simp [octagonBaseReducedLetterPGL, ih]

private lemma octagonBaseSourceElement_mem_source :
    octagonBaseSourceElement ∈ octagonBaseSource := by
  change octagonBaseSourceElement ∈
    Subgroup.zpowers octagonBaseSourceElement
  exact Subgroup.mem_zpowers _

private lemma octagonBaseTargetElement_mem_target :
    octagonBaseTargetElement ∈ octagonBaseTarget := by
  change octagonBaseTargetElement ∈
    Subgroup.zpowers octagonBaseTargetElement
  exact Subgroup.mem_zpowers _

/-- One complete forward source corridor preserves the source interval. -/
lemma octagonSourceForwardCycle_smul_sourceBoundary :
    FiniteStatePingPong.eval octagonBaseReducedLetterPGL
        octagonSourceForwardCycle • octagonHNNSourceBoundarySet =
      octagonHNNSourceBoundarySet := by
  rw [show FiniteStatePingPong.eval octagonBaseReducedLetterPGL
      octagonSourceForwardCycle =
        octagonBaseToPGL23 octagonBaseSourceElement by
    rw [FiniteStatePingPong.eval, octagonCorridorLetterPGL_prod,
      octagonSourceForwardCycle_value]]
  apply MulAction.mem_stabilizer_iff.mp
  exact octagonBaseToPGL23_mem_sourceBoundary_stabilizer
    octagonBaseSourceElement octagonBaseSourceElement_mem_source

/-- One complete backward source corridor preserves the source interval. -/
lemma octagonSourceBackwardCycle_smul_sourceBoundary :
    FiniteStatePingPong.eval octagonBaseReducedLetterPGL
        octagonSourceBackwardCycle • octagonHNNSourceBoundarySet =
      octagonHNNSourceBoundarySet := by
  rw [show FiniteStatePingPong.eval octagonBaseReducedLetterPGL
      octagonSourceBackwardCycle =
        octagonBaseToPGL23 octagonBaseSourceElement⁻¹ by
    rw [FiniteStatePingPong.eval, octagonCorridorLetterPGL_prod,
      octagonSourceBackwardCycle_value, map_inv]]
  apply MulAction.mem_stabilizer_iff.mp
  exact octagonBaseToPGL23_mem_sourceBoundary_stabilizer
    octagonBaseSourceElement⁻¹
      (Subgroup.inv_mem _ octagonBaseSourceElement_mem_source)

/-- One complete forward target corridor preserves the target interval. -/
lemma octagonTargetForwardCycle_smul_targetBoundary :
    FiniteStatePingPong.eval octagonBaseReducedLetterPGL
        octagonTargetForwardCycle • octagonHNNTargetBoundarySet =
      octagonHNNTargetBoundarySet := by
  rw [show FiniteStatePingPong.eval octagonBaseReducedLetterPGL
      octagonTargetForwardCycle =
        octagonBaseToPGL23 octagonBaseTargetElement by
    rw [FiniteStatePingPong.eval, octagonCorridorLetterPGL_prod,
      octagonTargetForwardCycle_value]]
  apply MulAction.mem_stabilizer_iff.mp
  exact octagonBaseToPGL23_mem_targetBoundary_stabilizer
    octagonBaseTargetElement octagonBaseTargetElement_mem_target

/-- One complete backward target corridor preserves the target interval. -/
lemma octagonTargetBackwardCycle_smul_targetBoundary :
    FiniteStatePingPong.eval octagonBaseReducedLetterPGL
        octagonTargetBackwardCycle • octagonHNNTargetBoundarySet =
      octagonHNNTargetBoundarySet := by
  rw [show FiniteStatePingPong.eval octagonBaseReducedLetterPGL
      octagonTargetBackwardCycle =
        octagonBaseToPGL23 octagonBaseTargetElement⁻¹ by
    rw [FiniteStatePingPong.eval, octagonCorridorLetterPGL_prod,
      octagonTargetBackwardCycle_value, map_inv]]
  apply MulAction.mem_stabilizer_iff.mp
  exact octagonBaseToPGL23_mem_targetBoundary_stabilizer
    octagonBaseTargetElement⁻¹
      (Subgroup.inv_mem _ octagonBaseTargetElement_mem_target)

/-! ## The exact remaining cylinder classification

The definitions below make the final geometric obligation precise.  An
overlap is expressed on the canonical free-product alphabet, so the generic
two-orientation peeling theorem applies without any conversion between word
models.
-/

/-- A reduced-letter word has a point taking `U` into `V`. -/
def octagonBoundaryCorridorOverlap
    (U V : Set OctagonProjectiveBoundary)
    (w : List OctagonBaseCorridorLetter) : Prop :=
  ∃ p ∈ U,
    FiniteStatePingPong.eval octagonBaseReducedLetterPGL w • p ∈ V

/-- The two invariants carried by a canonical free-product word. -/
def OctagonBaseCorridorReduced
    (w : List OctagonBaseCorridorLetter) : Prop :=
  (∀ l ∈ w, l.2 ≠ 1) ∧
    w.IsChain fun l l' => l.1 ≠ l'.1

/-- Words made of zero or more forward source-corridor turns. -/
def OctagonSourceForwardCorridor
    (w : List OctagonBaseCorridorLetter) : Prop :=
  ∃ n : ℕ, w = FiniteStatePingPong.cycleRepeat
    octagonSourceForwardCycle n

/-- Words made of zero or more backward source-corridor turns. -/
def OctagonSourceBackwardCorridor
    (w : List OctagonBaseCorridorLetter) : Prop :=
  ∃ n : ℕ, w = FiniteStatePingPong.cycleRepeat
    octagonSourceBackwardCycle n

/-- Words made of zero or more forward target-corridor turns. -/
def OctagonTargetForwardCorridor
    (w : List OctagonBaseCorridorLetter) : Prop :=
  ∃ n : ℕ, w = FiniteStatePingPong.cycleRepeat
    octagonTargetForwardCycle n

/-- Words made of zero or more backward target-corridor turns. -/
def OctagonTargetBackwardCorridor
    (w : List OctagonBaseCorridorLetter) : Prop :=
  ∃ n : ℕ, w = FiniteStatePingPong.cycleRepeat
    octagonTargetBackwardCycle n

private lemma sourceForwardCorridor_peel
    (w : List OctagonBaseCorridorLetter)
    (hw : OctagonSourceForwardCorridor w) :
    w = [] ∨ ∃ v, OctagonSourceForwardCorridor v ∧
      w = v ++ octagonSourceForwardCycle := by
  obtain ⟨n, rfl⟩ := hw
  cases n with
  | zero => simp
  | succ n =>
      right
      refine ⟨FiniteStatePingPong.cycleRepeat
        octagonSourceForwardCycle n, ⟨n, rfl⟩, ?_⟩
      exact FiniteStatePingPong.cycleRepeat_succ _ _

private lemma sourceBackwardCorridor_peel
    (w : List OctagonBaseCorridorLetter)
    (hw : OctagonSourceBackwardCorridor w) :
    w = [] ∨ ∃ v, OctagonSourceBackwardCorridor v ∧
      w = v ++ octagonSourceBackwardCycle := by
  obtain ⟨n, rfl⟩ := hw
  cases n with
  | zero => simp
  | succ n =>
      right
      refine ⟨FiniteStatePingPong.cycleRepeat
        octagonSourceBackwardCycle n, ⟨n, rfl⟩, ?_⟩
      exact FiniteStatePingPong.cycleRepeat_succ _ _

private lemma targetForwardCorridor_peel
    (w : List OctagonBaseCorridorLetter)
    (hw : OctagonTargetForwardCorridor w) :
    w = [] ∨ ∃ v, OctagonTargetForwardCorridor v ∧
      w = v ++ octagonTargetForwardCycle := by
  obtain ⟨n, rfl⟩ := hw
  cases n with
  | zero => simp
  | succ n =>
      right
      refine ⟨FiniteStatePingPong.cycleRepeat
        octagonTargetForwardCycle n, ⟨n, rfl⟩, ?_⟩
      exact FiniteStatePingPong.cycleRepeat_succ _ _

private lemma targetBackwardCorridor_peel
    (w : List OctagonBaseCorridorLetter)
    (hw : OctagonTargetBackwardCorridor w) :
    w = [] ∨ ∃ v, OctagonTargetBackwardCorridor v ∧
      w = v ++ octagonTargetBackwardCycle := by
  obtain ⟨n, rfl⟩ := hw
  cases n with
  | zero => simp
  | succ n =>
      right
      refine ⟨FiniteStatePingPong.cycleRepeat
        octagonTargetBackwardCycle n, ⟨n, rfl⟩, ?_⟩
      exact FiniteStatePingPong.cycleRepeat_succ _ _

/-- The precise geometric/cylinder statement left by the corridor method.
The first two fields say that the two corridor components never meet.  The
last two say that a self-intersection can only follow one orientation of the
corresponding three-edge cycle. -/
structure OctagonHNNBaseCorridorClassification : Prop where
  source_target : ∀ w : List OctagonBaseCorridorLetter,
    OctagonBaseCorridorReduced w →
    ¬octagonBoundaryCorridorOverlap octagonHNNSourceBoundarySet
      octagonHNNTargetBoundarySet w
  target_source : ∀ w : List OctagonBaseCorridorLetter,
    OctagonBaseCorridorReduced w →
    ¬octagonBoundaryCorridorOverlap octagonHNNTargetBoundarySet
      octagonHNNSourceBoundarySet w
  source_self : ∀ w : List OctagonBaseCorridorLetter,
    OctagonBaseCorridorReduced w →
    octagonBoundaryCorridorOverlap octagonHNNSourceBoundarySet
      octagonHNNSourceBoundarySet w →
      w = [] ∨ OctagonSourceForwardCorridor w ∨
        OctagonSourceBackwardCorridor w
  target_self : ∀ w : List OctagonBaseCorridorLetter,
    OctagonBaseCorridorReduced w →
    octagonBoundaryCorridorOverlap octagonHNNTargetBoundarySet
      octagonHNNTargetBoundarySet w →
      w = [] ∨ OctagonTargetForwardCorridor w ∨
        OctagonTargetBackwardCorridor w

lemma OctagonHNNBaseCorridorClassification.source_eq_nil_of_weight_zero
    (C : OctagonHNNBaseCorridorClassification)
    {w : List OctagonBaseCorridorLetter}
    (hreduced : OctagonBaseCorridorReduced w)
    (hoverlap : octagonBoundaryCorridorOverlap
      octagonHNNSourceBoundarySet octagonHNNSourceBoundarySet w)
    (hweight : FiniteStatePingPong.weight
      octagonBaseReducedLetterWeight w = 0) :
    w = [] := by
  apply FiniteStatePingPong.eq_nil_of_two_suffix_corridors_and_weight_zero
    (fun v => OctagonBaseCorridorReduced v ∧
      octagonBoundaryCorridorOverlap
        octagonHNNSourceBoundarySet octagonHNNSourceBoundarySet v)
    OctagonSourceForwardCorridor OctagonSourceBackwardCorridor
    octagonSourceForwardCycle octagonSourceBackwardCycle
    octagonSourceForwardCycle_ne_nil octagonSourceBackwardCycle_ne_nil
    (fun v hv => C.source_self v hv.1 hv.2)
    sourceForwardCorridor_peel sourceBackwardCorridor_peel
    octagonBaseReducedLetterWeight
  · simp
  · simp
  · exact ⟨hreduced, hoverlap⟩
  · exact hweight

lemma OctagonHNNBaseCorridorClassification.target_eq_nil_of_weight_zero
    (C : OctagonHNNBaseCorridorClassification)
    {w : List OctagonBaseCorridorLetter}
    (hreduced : OctagonBaseCorridorReduced w)
    (hoverlap : octagonBoundaryCorridorOverlap
      octagonHNNTargetBoundarySet octagonHNNTargetBoundarySet w)
    (hweight : FiniteStatePingPong.weight
      octagonBaseReducedLetterWeight w = 0) :
    w = [] := by
  apply FiniteStatePingPong.eq_nil_of_two_suffix_corridors_and_weight_zero
    (fun v => OctagonBaseCorridorReduced v ∧
      octagonBoundaryCorridorOverlap
        octagonHNNTargetBoundarySet octagonHNNTargetBoundarySet v)
    OctagonTargetForwardCorridor OctagonTargetBackwardCorridor
    octagonTargetForwardCycle octagonTargetBackwardCycle
    octagonTargetForwardCycle_ne_nil octagonTargetBackwardCycle_ne_nil
    (fun v hv => C.target_self v hv.1 hv.2)
    targetForwardCorridor_peel targetBackwardCorridor_peel
    octagonBaseReducedLetterWeight
  · simp
  · simp
  · exact ⟨hreduced, hoverlap⟩
  · exact hweight

private lemma octagonBaseReducedWord_weight_zero
    (g : OctagonBaseGroup) (hg : g ∈ octagonBaseExponentKernel) :
    FiniteStatePingPong.weight octagonBaseReducedLetterWeight
      (octagonBaseReducedWord g).toList = 0 := by
  rw [FiniteStatePingPong.weight, octagonBaseReducedWord_weight]
  change octagonBaseExponent g = 1 at hg
  rw [hg]
  rfl

private lemma octagonBaseReducedWord_eval
    (g : OctagonBaseGroup) :
    FiniteStatePingPong.eval octagonBaseReducedLetterPGL
      (octagonBaseReducedWord g).toList = octagonBaseToPGL23 g := by
  exact octagonBaseReducedWord_pgl g

private lemma octagonBaseReducedWord_isCorridorReduced
    (g : OctagonBaseGroup) :
    OctagonBaseCorridorReduced (octagonBaseReducedWord g).toList := by
  exact ⟨(octagonBaseReducedWord g).ne_one,
    (octagonBaseReducedWord g).chain_ne⟩

/-- The cylinder classification implies both signed cross-domain estimates. -/
theorem octagonHNN_base_cross_of_corridorClassification
    (C : OctagonHNNBaseCorridorClassification) :
    ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet (-u))ᶜ := by
  intro u g _ p hp
  rw [Set.mem_compl_iff]
  intro hbad
  rcases Int.units_eq_one_or u with rfl | rfl
  · apply C.target_source (octagonBaseReducedWord g).toList
      (octagonBaseReducedWord_isCorridorReduced g)
    refine ⟨p, ?_, ?_⟩
    · exact hp
    · simpa [octagonBoundaryCorridorOverlap,
        octagonBaseReducedWord_eval]
      using hbad
  · apply C.source_target (octagonBaseReducedWord g).toList
      (octagonBaseReducedWord_isCorridorReduced g)
    refine ⟨p, ?_, ?_⟩
    · exact hp
    · simpa [octagonBoundaryCorridorOverlap,
        octagonBaseReducedWord_eval]
      using hbad

/-- The cylinder classification and the nonzero corridor weights imply both
signed nonidentity self-domain estimates. -/
theorem octagonHNN_base_self_of_corridorClassification
    (C : OctagonHNNBaseCorridorClassification) :
    ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel → g ≠ 1 →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet u)ᶜ := by
  intro u g hg hg1 p hp
  rw [Set.mem_compl_iff]
  intro hbad
  have hweight := octagonBaseReducedWord_weight_zero g hg
  have hnil : (octagonBaseReducedWord g).toList = [] := by
    rcases Int.units_eq_one_or u with rfl | rfl
    · apply C.target_eq_nil_of_weight_zero
      · exact octagonBaseReducedWord_isCorridorReduced g
      · exact ⟨p, hp, by
          simpa [octagonBoundaryCorridorOverlap,
            octagonBaseReducedWord_eval] using hbad⟩
      · exact hweight
    · apply C.source_eq_nil_of_weight_zero
      · exact octagonBaseReducedWord_isCorridorReduced g
      · exact ⟨p, hp, by
          simpa [octagonBoundaryCorridorOverlap,
            octagonBaseReducedWord_eval] using hbad⟩
      · exact hweight
  apply hg1
  rw [← octagonBaseReducedWord_value g]
  simp [hnil]

/-- Once the concrete cylinder classification is established, HNN
faithfulness is unconditional with respect to the former `hcross`/`hself`
interfaces. -/
theorem octagonHNNToPGL23_injective_of_corridorClassification
    (C : OctagonHNNBaseCorridorClassification) :
    Function.Injective octagonHNNToPGL23 :=
  octagonHNNToPGL23_injective_of_cross_self
    (octagonHNN_base_cross_of_corridorClassification C)
    (octagonHNN_base_self_of_corridorClassification C)

/-- The same classification gives the faithful projective octagon action. -/
theorem projectiveOctagonToPGL23_injective_of_corridorClassification
    (C : OctagonHNNBaseCorridorClassification) :
    Function.Injective projectiveOctagonToPGL23 :=
  projectiveOctagonToPGL23_injective_iff_hnn.mpr
    (octagonHNNToPGL23_injective_of_corridorClassification C)

/-- The classification also propagates through the central extension to the
original integral quaternion representation. -/
theorem liftedOctagonToQuaternion_injective_of_corridorClassification
    (C : OctagonHNNBaseCorridorClassification) :
    Function.Injective liftedOctagonToQuaternion := by
  apply liftedOctagonToQuaternion_injective_iff_projective.mpr
  apply projectiveOctagonToProjectivizedQuaternion_injective_iff_pgl.mpr
  exact projectiveOctagonToPGL23_injective_of_corridorClassification C

end

end SystolicGrowth
