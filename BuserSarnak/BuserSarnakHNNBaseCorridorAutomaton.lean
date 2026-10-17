module

public import BuserSarnak.BuserSarnakHNNBaseCorridorGeometry

@[expose] public section

/-!
# The scaled bridge automaton for the octagon HNN base

Conjugating the four cone involutions by powers of the handle produces two
bi-infinite corridor lines on the projective boundary.  This file defines
their bridge states and cone domains, proves their geometric incidence, and
uses the resulting deterministic escape/path automaton to classify every
reduced base word meeting a source or target bridge.
-/

open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise

namespace SystolicGrowth

noncomputable section

private lemma octagonCorridorScale_ne_zero : octagonCorridorScale ≠ 0 :=
  ne_of_gt octagonCorridorScale_pos

/-- One of the four alternating bridge types in the source and target
corridor lines. -/
inductive OctagonCorridorBridgeKind where
  | sourceCenter
  | sourceGap
  | targetCenter
  | targetGap
  deriving DecidableEq

/-- A bridge type together with its integral handle level. -/
structure OctagonCorridorBridge where
  level : ℤ
  kind : OctagonCorridorBridgeKind
  deriving DecidableEq

/-- The exact projective interval represented by a corridor bridge. -/
def octagonCorridorBridgeSet (b : OctagonCorridorBridge) :
    Set OctagonProjectiveBoundary :=
  match b.kind with
  | .sourceCenter =>
      (octagonBaseToPGL23 octagonBaseA) ^ b.level •
        octagonHNNSourceBoundarySet
  | .sourceGap =>
      (octagonBaseToPGL23 octagonBaseA) ^ b.level •
        octagonHNNSourceCone3CorridorSet
  | .targetCenter =>
      (octagonBaseToPGL23 octagonBaseA) ^ b.level •
        octagonHNNTargetBoundarySet
  | .targetGap =>
      (octagonBaseToPGL23 octagonBaseA) ^ b.level •
        octagonHNNTargetCone4CorridorSet

/-- The rational open shell enclosing a bridge. -/
def octagonCorridorBridgeShell (b : OctagonCorridorBridge) :
    Set OctagonProjectiveBoundary :=
  let r := octagonCorridorScale ^ b.level
  match b.kind with
  | .sourceCenter => projectiveIntervalSet (r * (1 / 2)) (r * 2)
  | .sourceGap => projectiveIntervalSet (r * 1) (r * 16)
  | .targetCenter => projectiveIntervalSet (r * (-2)) (r * (-(1 / 2)))
  | .targetGap => projectiveIntervalSet (r * (-16)) (r * (-1))

/-- Every exact bridge lies in its rational scale shell. -/
lemma octagonCorridorBridgeSet_subset_shell (b : OctagonCorridorBridge) :
    octagonCorridorBridgeSet b ⊆ octagonCorridorBridgeShell b := by
  rcases b with ⟨n, k⟩
  cases k with
  | sourceCenter =>
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Set.mem_smul_set.mp hp
      have hq' := octagonSourceBoundary_subset_shell hq
      have hmem :
          (octagonBaseToPGL23 octagonBaseA) ^ n • q ∈
            (octagonBaseToPGL23 octagonBaseA) ^ n •
              projectiveIntervalSet (1 / 2) 2 :=
        Set.smul_mem_smul_set hq'
      rw [octagon_A_zpow_smul_projectiveIntervalSet] at hmem
      simpa [octagonCorridorBridgeShell] using hmem
  | sourceGap =>
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Set.mem_smul_set.mp hp
      have hq' := octagonSourceCone3Corridor_subset_shell hq
      have hmem :
          (octagonBaseToPGL23 octagonBaseA) ^ n • q ∈
            (octagonBaseToPGL23 octagonBaseA) ^ n •
              projectiveIntervalSet 1 16 :=
        Set.smul_mem_smul_set hq'
      rw [octagon_A_zpow_smul_projectiveIntervalSet] at hmem
      simpa [octagonCorridorBridgeShell] using hmem
  | targetCenter =>
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Set.mem_smul_set.mp hp
      have hq' := octagonTargetBoundary_subset_shell hq
      have hmem :
          (octagonBaseToPGL23 octagonBaseA) ^ n • q ∈
            (octagonBaseToPGL23 octagonBaseA) ^ n •
              projectiveIntervalSet (-2) (-1 / 2) :=
        Set.smul_mem_smul_set hq'
      rw [octagon_A_zpow_smul_projectiveIntervalSet] at hmem
      change _ ∈ projectiveIntervalSet
        (octagonCorridorScale ^ n * (-2))
        (octagonCorridorScale ^ n * (-(1 / 2)))
      convert hmem using 1
      all_goals ring_nf
  | targetGap =>
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Set.mem_smul_set.mp hp
      have hq' := octagonTargetCone4Corridor_subset_shell hq
      have hmem :
          (octagonBaseToPGL23 octagonBaseA) ^ n • q ∈
            (octagonBaseToPGL23 octagonBaseA) ^ n •
              projectiveIntervalSet (-16) (-1) :=
        Set.smul_mem_smul_set hq'
      rw [octagon_A_zpow_smul_projectiveIntervalSet] at hmem
      simpa [octagonCorridorBridgeShell] using hmem

private lemma octagonScaledIntervals_disjoint_of_shift
    {n m d : ℤ} {l u l' u' : ℝ}
    (_hl : 0 < l) (hlu : l < u) (hl' : 0 < l') (hlu' : l' < u')
    (_hd : 0 ≤ d) (hnm : n + d ≤ m)
    (hsep : u ≤ octagonCorridorScale ^ d * l') :
    Disjoint
      (projectiveIntervalSet
        (octagonCorridorScale ^ n * l) (octagonCorridorScale ^ n * u))
      (projectiveIntervalSet
        (octagonCorridorScale ^ m * l') (octagonCorridorScale ^ m * u')) := by
  have hr1 : (1 : ℝ) ≤ octagonCorridorScale :=
    (show (1 : ℝ) < octagonCorridorScale by
      linarith [octagonCorridorScale_gt]).le
  have hrn : 0 < octagonCorridorScale ^ n :=
    zpow_pos octagonCorridorScale_pos n
  have hrm : 0 < octagonCorridorScale ^ m :=
    zpow_pos octagonCorridorScale_pos m
  have hpow : octagonCorridorScale ^ (n + d) ≤
      octagonCorridorScale ^ m :=
    zpow_le_zpow_right₀ hr1 hnm
  have hscale : octagonCorridorScale ^ n * u ≤
      octagonCorridorScale ^ m * l' := by
    calc
      octagonCorridorScale ^ n * u ≤
          octagonCorridorScale ^ n *
            (octagonCorridorScale ^ d * l') :=
        mul_le_mul_of_nonneg_left hsep hrn.le
      _ = octagonCorridorScale ^ (n + d) * l' := by
        rw [zpow_add₀ octagonCorridorScale_ne_zero]
        ring
      _ ≤ octagonCorridorScale ^ m * l' :=
        mul_le_mul_of_nonneg_right hpow hl'.le
  apply projectiveIntervalSet_disjoint_of_le
  · exact mul_lt_mul_of_pos_left hlu hrn
  · exact hscale
  · exact mul_lt_mul_of_pos_left hlu' hrm

private lemma octagonNegativeScaledIntervals_disjoint_of_shift
    {n m d : ℤ} {l u l' u' : ℝ}
    (_hl : 0 < l) (hlu : l < u) (hl' : 0 < l') (hlu' : l' < u')
    (_hd : 0 ≤ d) (hnm : n + d ≤ m)
    (hsep : u ≤ octagonCorridorScale ^ d * l') :
    Disjoint
      (projectiveIntervalSet
        (octagonCorridorScale ^ m * (-u'))
        (octagonCorridorScale ^ m * (-l')))
      (projectiveIntervalSet
        (octagonCorridorScale ^ n * (-u))
        (octagonCorridorScale ^ n * (-l))) := by
  have hr1 : (1 : ℝ) ≤ octagonCorridorScale :=
    (show (1 : ℝ) < octagonCorridorScale by
      linarith [octagonCorridorScale_gt]).le
  have hrn : 0 < octagonCorridorScale ^ n :=
    zpow_pos octagonCorridorScale_pos n
  have hrm : 0 < octagonCorridorScale ^ m :=
    zpow_pos octagonCorridorScale_pos m
  have hpow : octagonCorridorScale ^ (n + d) ≤
      octagonCorridorScale ^ m :=
    zpow_le_zpow_right₀ hr1 hnm
  have hscale : octagonCorridorScale ^ n * u ≤
      octagonCorridorScale ^ m * l' := by
    calc
      octagonCorridorScale ^ n * u ≤
          octagonCorridorScale ^ n *
            (octagonCorridorScale ^ d * l') :=
        mul_le_mul_of_nonneg_left hsep hrn.le
      _ = octagonCorridorScale ^ (n + d) * l' := by
        rw [zpow_add₀ octagonCorridorScale_ne_zero]
        ring
      _ ≤ octagonCorridorScale ^ m * l' :=
        mul_le_mul_of_nonneg_right hpow hl'.le
  apply projectiveIntervalSet_disjoint_of_le
  · nlinarith
  · nlinarith
  · nlinarith

private lemma octagonSourceCenter_disjoint_sourceGap :
    Disjoint octagonHNNSourceBoundarySet
      octagonHNNSourceCone3CorridorSet := by
  rw [Set.disjoint_left]
  intro p hpS hpG
  obtain ⟨q, hq, rfl⟩ := Set.mem_smul_set.mp hpG
  have hout := octagon_B_maps_sourceBoundary_outside_both false true hq
  apply hout
  left
  simpa only [show octagonBaseToPGL23 octagonBaseE3 =
      BuserSarnakQuaternionUnit.toPGL23
        (octagonUnit (.B false true)) by
    change octagonBaseToPGL23 (octagonBaseFactorElement .cone3) = _
    exact octagonBaseToPGL23_factorElement .cone3] using hpS

private lemma octagonTargetCenter_disjoint_targetGap :
    Disjoint octagonHNNTargetBoundarySet
      octagonHNNTargetCone4CorridorSet := by
  rw [Set.disjoint_left]
  intro p hpT hpG
  obtain ⟨q, hq, rfl⟩ := Set.mem_smul_set.mp hpG
  have hout := octagon_B_maps_targetBoundary_outside_both true true hq
  apply hout
  right
  simpa only [show octagonBaseToPGL23 octagonBaseE4 =
      BuserSarnakQuaternionUnit.toPGL23
        (octagonUnit (.B true true)) by
    change octagonBaseToPGL23 (octagonBaseFactorElement .cone4) = _
    exact octagonBaseToPGL23_factorElement .cone4] using hpT

private lemma octagonSourceCenterShell_disjoint_self
    {n m : ℤ} (hnm : n ≠ m) :
    Disjoint
      (octagonCorridorBridgeShell ⟨n, .sourceCenter⟩)
      (octagonCorridorBridgeShell ⟨m, .sourceCenter⟩) := by
  rcases lt_trichotomy n m with h | h | h
  · dsimp only [octagonCorridorBridgeShell]
    apply octagonScaledIntervals_disjoint_of_shift
      (n := n) (m := m) (d := 1)
      (l := 1 / 2) (u := 2) (l' := 1 / 2) (u' := 2)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · omega
    · norm_num
      linarith [octagonCorridorScale_gt]
  · exact (hnm h).elim
  · symm
    dsimp only [octagonCorridorBridgeShell]
    apply octagonScaledIntervals_disjoint_of_shift
      (n := m) (m := n) (d := 1)
      (l := 1 / 2) (u := 2) (l' := 1 / 2) (u' := 2)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · omega
    · norm_num
      linarith [octagonCorridorScale_gt]

private lemma octagonSourceGapShell_disjoint_self
    {n m : ℤ} (hnm : n ≠ m) :
    Disjoint
      (octagonCorridorBridgeShell ⟨n, .sourceGap⟩)
      (octagonCorridorBridgeShell ⟨m, .sourceGap⟩) := by
  rcases lt_trichotomy n m with h | h | h
  · dsimp only [octagonCorridorBridgeShell]
    apply octagonScaledIntervals_disjoint_of_shift
      (n := n) (m := m) (d := 1)
      (l := 1) (u := 16) (l' := 1) (u' := 16)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · omega
    · norm_num
      linarith [octagonCorridorScale_gt]
  · exact (hnm h).elim
  · symm
    dsimp only [octagonCorridorBridgeShell]
    apply octagonScaledIntervals_disjoint_of_shift
      (n := m) (m := n) (d := 1)
      (l := 1) (u := 16) (l' := 1) (u' := 16)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · omega
    · norm_num
      linarith [octagonCorridorScale_gt]

private lemma octagonSourceCenterShell_disjoint_gap
    {n m : ℤ} (hnm : n ≠ m) :
    Disjoint
      (octagonCorridorBridgeShell ⟨n, .sourceCenter⟩)
      (octagonCorridorBridgeShell ⟨m, .sourceGap⟩) := by
  rcases lt_trichotomy n m with h | h | h
  · dsimp only [octagonCorridorBridgeShell]
    apply octagonScaledIntervals_disjoint_of_shift
      (n := n) (m := m) (d := 1)
      (l := 1 / 2) (u := 2) (l' := 1) (u' := 16)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · omega
    · norm_num
      linarith [octagonCorridorScale_gt]
  · exact (hnm h).elim
  · symm
    dsimp only [octagonCorridorBridgeShell]
    apply octagonScaledIntervals_disjoint_of_shift
      (n := m) (m := n) (d := 1)
      (l := 1) (u := 16) (l' := 1 / 2) (u' := 2)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · omega
    · norm_num
      linarith [octagonCorridorScale_gt]

private lemma octagonTargetCenterShell_disjoint_self
    {n m : ℤ} (hnm : n ≠ m) :
    Disjoint
      (octagonCorridorBridgeShell ⟨n, .targetCenter⟩)
      (octagonCorridorBridgeShell ⟨m, .targetCenter⟩) := by
  rcases lt_trichotomy n m with h | h | h
  · symm
    dsimp only [octagonCorridorBridgeShell]
    apply octagonNegativeScaledIntervals_disjoint_of_shift
      (n := n) (m := m) (d := 1)
      (l := 1 / 2) (u := 2) (l' := 1 / 2) (u' := 2)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · omega
    · norm_num
      linarith [octagonCorridorScale_gt]
  · exact (hnm h).elim
  · dsimp only [octagonCorridorBridgeShell]
    apply octagonNegativeScaledIntervals_disjoint_of_shift
      (n := m) (m := n) (d := 1)
      (l := 1 / 2) (u := 2) (l' := 1 / 2) (u' := 2)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · omega
    · norm_num
      linarith [octagonCorridorScale_gt]

private lemma octagonTargetGapShell_disjoint_self
    {n m : ℤ} (hnm : n ≠ m) :
    Disjoint
      (octagonCorridorBridgeShell ⟨n, .targetGap⟩)
      (octagonCorridorBridgeShell ⟨m, .targetGap⟩) := by
  rcases lt_trichotomy n m with h | h | h
  · symm
    dsimp only [octagonCorridorBridgeShell]
    apply octagonNegativeScaledIntervals_disjoint_of_shift
      (n := n) (m := m) (d := 1)
      (l := 1) (u := 16) (l' := 1) (u' := 16)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · omega
    · norm_num
      linarith [octagonCorridorScale_gt]
  · exact (hnm h).elim
  · dsimp only [octagonCorridorBridgeShell]
    apply octagonNegativeScaledIntervals_disjoint_of_shift
      (n := m) (m := n) (d := 1)
      (l := 1) (u := 16) (l' := 1) (u' := 16)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · omega
    · norm_num
      linarith [octagonCorridorScale_gt]

private lemma octagonTargetCenterShell_disjoint_gap
    {n m : ℤ} (hnm : n ≠ m) :
    Disjoint
      (octagonCorridorBridgeShell ⟨n, .targetCenter⟩)
      (octagonCorridorBridgeShell ⟨m, .targetGap⟩) := by
  rcases lt_trichotomy n m with h | h | h
  · symm
    dsimp only [octagonCorridorBridgeShell]
    apply octagonNegativeScaledIntervals_disjoint_of_shift
      (n := n) (m := m) (d := 1)
      (l := 1 / 2) (u := 2) (l' := 1) (u' := 16)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · omega
    · norm_num
      linarith [octagonCorridorScale_gt]
  · exact (hnm h).elim
  · dsimp only [octagonCorridorBridgeShell]
    apply octagonNegativeScaledIntervals_disjoint_of_shift
      (n := m) (m := n) (d := 1)
      (l := 1) (u := 16) (l' := 1 / 2) (u' := 2)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · omega
    · norm_num
      linarith [octagonCorridorScale_gt]

private lemma octagonSourceShell_disjoint_targetShell
    (n m : ℤ) (s t : Bool) :
    Disjoint
      (octagonCorridorBridgeShell
        ⟨n, if s then .sourceCenter else .sourceGap⟩)
      (octagonCorridorBridgeShell
        ⟨m, if t then .targetCenter else .targetGap⟩) := by
  have hrn : 0 < octagonCorridorScale ^ n :=
    zpow_pos octagonCorridorScale_pos n
  have hrm : 0 < octagonCorridorScale ^ m :=
    zpow_pos octagonCorridorScale_pos m
  cases s <;> cases t <;>
    simp only [Bool.false_eq_true, ↓reduceIte, octagonCorridorBridgeShell]
  all_goals symm
  all_goals apply projectiveIntervalSet_disjoint_of_le
  all_goals nlinarith

/-- Distinct corridor bridges are disjoint. -/
theorem octagonCorridorBridgeSet_pairwise_disjoint :
    Pairwise fun b c =>
      Disjoint (octagonCorridorBridgeSet b) (octagonCorridorBridgeSet c) := by
  rintro ⟨n, k⟩ ⟨m, l⟩ hne
  have hmono (h : Disjoint
      (octagonCorridorBridgeShell ⟨n, k⟩)
      (octagonCorridorBridgeShell ⟨m, l⟩)) :
      Disjoint (octagonCorridorBridgeSet ⟨n, k⟩)
        (octagonCorridorBridgeSet ⟨m, l⟩) :=
    h.mono (octagonCorridorBridgeSet_subset_shell _)
      (octagonCorridorBridgeSet_subset_shell _)
  cases k <;> cases l
  · apply hmono
    apply octagonSourceCenterShell_disjoint_self
    intro h
    apply hne
    cases h
    rfl

  · by_cases hnm : n = m
    · subst m
      change Disjoint
        ((octagonBaseToPGL23 octagonBaseA) ^ n •
          octagonHNNSourceBoundarySet)
        ((octagonBaseToPGL23 octagonBaseA) ^ n •
          octagonHNNSourceCone3CorridorSet)
      exact Set.disjoint_smul_set.mpr octagonSourceCenter_disjoint_sourceGap
    · exact hmono (octagonSourceCenterShell_disjoint_gap hnm)
  · exact hmono (octagonSourceShell_disjoint_targetShell n m true true)
  · exact hmono (octagonSourceShell_disjoint_targetShell n m true false)
  · by_cases hnm : n = m
    · subst m
      change Disjoint
        ((octagonBaseToPGL23 octagonBaseA) ^ n •
          octagonHNNSourceCone3CorridorSet)
        ((octagonBaseToPGL23 octagonBaseA) ^ n •
          octagonHNNSourceBoundarySet)
      exact Set.disjoint_smul_set.mpr
        octagonSourceCenter_disjoint_sourceGap.symm
    · exact hmono
        (octagonSourceCenterShell_disjoint_gap
          (n := m) (m := n) (Ne.symm hnm)).symm
  · apply hmono
    apply octagonSourceGapShell_disjoint_self
    intro h
    apply hne
    cases h
    rfl
  · exact hmono (octagonSourceShell_disjoint_targetShell n m false true)
  · exact hmono (octagonSourceShell_disjoint_targetShell n m false false)
  · exact hmono (octagonSourceShell_disjoint_targetShell m n true true).symm
  · exact hmono (octagonSourceShell_disjoint_targetShell m n false true).symm
  · apply hmono
    apply octagonTargetCenterShell_disjoint_self
    intro h
    apply hne
    cases h
    rfl
  · by_cases hnm : n = m
    · subst m
      change Disjoint
        ((octagonBaseToPGL23 octagonBaseA) ^ n •
          octagonHNNTargetBoundarySet)
        ((octagonBaseToPGL23 octagonBaseA) ^ n •
          octagonHNNTargetCone4CorridorSet)
      exact Set.disjoint_smul_set.mpr octagonTargetCenter_disjoint_targetGap
    · exact hmono (octagonTargetCenterShell_disjoint_gap hnm)
  · exact hmono (octagonSourceShell_disjoint_targetShell m n true false).symm
  · exact hmono (octagonSourceShell_disjoint_targetShell m n false false).symm
  · by_cases hnm : n = m
    · subst m
      change Disjoint
        ((octagonBaseToPGL23 octagonBaseA) ^ n •
          octagonHNNTargetCone4CorridorSet)
        ((octagonBaseToPGL23 octagonBaseA) ^ n •
          octagonHNNTargetBoundarySet)
      exact Set.disjoint_smul_set.mpr
        octagonTargetCenter_disjoint_targetGap.symm
    · exact hmono
        (octagonTargetCenterShell_disjoint_gap
          (n := m) (m := n) (Ne.symm hnm)).symm
  · apply hmono
    apply octagonTargetGapShell_disjoint_self
    intro h
    apply hne
    cases h
    rfl

/-- The four order-two cone factors, excluding the handle factor. -/
inductive OctagonCorridorCone where
  | cone1
  | cone2
  | cone3
  | cone4
  deriving DecidableEq

/-- The base free-product factor belonging to a corridor cone. -/
def OctagonCorridorCone.baseFactor :
    OctagonCorridorCone → OctagonBaseFactor
  | .cone1 => .cone1
  | .cone2 => .cone2
  | .cone3 => .cone3
  | .cone4 => .cone4

/-- A cone involution conjugated to an integral handle level. -/
structure OctagonCorridorReflection where
  level : ℤ
  cone : OctagonCorridorCone
  deriving DecidableEq

/-- The projective transformation represented by a conjugated cone
involution. -/
def octagonCorridorReflectionPGL (r : OctagonCorridorReflection) :
    PGL(2, ℝ) :=
  (octagonBaseToPGL23 octagonBaseA) ^ r.level *
    octagonBaseToPGL23 (octagonBaseFactorElement r.cone.baseFactor) *
      (octagonBaseToPGL23 octagonBaseA) ^ (-r.level)

/-- The conjugated ordinary ping-pong domain of a corridor reflection. -/
def octagonCorridorReflectionDomain (r : OctagonCorridorReflection) :
    Set OctagonProjectiveBoundary :=
  (octagonBaseToPGL23 octagonBaseA) ^ r.level •
    octagonBasePingPongSet r.cone.baseFactor

lemma octagonCorridorReflectionDomain_eq_interval
    (r : OctagonCorridorReflection) :
    octagonCorridorReflectionDomain r =
      match r.cone with
      | .cone1 => projectiveIntervalSet
          (octagonCorridorScale ^ r.level * (-1))
          (octagonCorridorScale ^ r.level * (-(1 / 4)))
      | .cone2 => projectiveIntervalSet
          (octagonCorridorScale ^ r.level * (1 / 4))
          (octagonCorridorScale ^ r.level * 1)
      | .cone3 => projectiveIntervalSet
          (octagonCorridorScale ^ r.level * 1)
          (octagonCorridorScale ^ r.level * 4)
      | .cone4 => projectiveIntervalSet
          (octagonCorridorScale ^ r.level * (-4))
          (octagonCorridorScale ^ r.level * (-1)) := by
  rcases r with ⟨n, c⟩
  cases c <;>
    simp only [octagonCorridorReflectionDomain,
      OctagonCorridorCone.baseFactor, octagonBasePingPongSet,
      octagonCone1ProjectiveLineSet, octagonCone2ProjectiveLineSet,
      octagonCone3ProjectiveLineSet, octagonCone4ProjectiveLineSet] <;>
    rw [octagon_A_zpow_smul_projectiveIntervalSet]
  · (congr 1; ring)

/-- The first bridge incident to a conjugated cone reflection. -/
def octagonCorridorReflectionLeftBridge
    (r : OctagonCorridorReflection) : OctagonCorridorBridge :=
  match r.cone with
  | .cone1 => ⟨r.level - 1, .targetGap⟩
  | .cone2 => ⟨r.level - 1, .sourceGap⟩
  | .cone3 => ⟨r.level, .sourceCenter⟩
  | .cone4 => ⟨r.level, .targetCenter⟩

/-- The second bridge incident to a conjugated cone reflection. -/
def octagonCorridorReflectionRightBridge
    (r : OctagonCorridorReflection) : OctagonCorridorBridge :=
  match r.cone with
  | .cone1 => ⟨r.level, .targetCenter⟩
  | .cone2 => ⟨r.level, .sourceCenter⟩
  | .cone3 => ⟨r.level, .sourceGap⟩
  | .cone4 => ⟨r.level, .targetGap⟩

/-- A reflection is incident to either endpoint bridge of its edge in the
corridor graph. -/
def OctagonCorridorIncident
    (r : OctagonCorridorReflection) (b : OctagonCorridorBridge) : Prop :=
  b = octagonCorridorReflectionLeftBridge r ∨
    b = octagonCorridorReflectionRightBridge r

/-- A conjugated cone reflection carries its left incident bridge exactly to
its right incident bridge. -/
lemma octagonCorridorReflectionPGL_smul_leftBridge
    (r : OctagonCorridorReflection) :
    octagonCorridorReflectionPGL r •
        octagonCorridorBridgeSet
          (octagonCorridorReflectionLeftBridge r) =
      octagonCorridorBridgeSet
        (octagonCorridorReflectionRightBridge r) := by
  rcases r with ⟨n, c⟩
  cases c <;>
    simp only [octagonCorridorReflectionPGL,
      OctagonCorridorCone.baseFactor,
      octagonBaseFactorElement,
      octagonCorridorReflectionLeftBridge,
      octagonCorridorReflectionRightBridge,
      octagonCorridorBridgeSet, mul_smul]
  · have hpow :
        (octagonBaseToPGL23 octagonBaseA) ^ (-n) *
            (octagonBaseToPGL23 octagonBaseA) ^ (n - 1) =
          (octagonBaseToPGL23 octagonBaseA) ^ (-1 : ℤ) := by
      rw [← zpow_add]
      congr 1
      omega
    simp only [← mul_smul]
    rw [hpow, mul_smul, mul_smul, zpow_neg, zpow_one,
      octagon_A_inv_smul_targetCone4CorridorSet,
      octagon_E1_smul_targetCone1CorridorSet]
  · have hpow :
        (octagonBaseToPGL23 octagonBaseA) ^ (-n) *
            (octagonBaseToPGL23 octagonBaseA) ^ (n - 1) =
          (octagonBaseToPGL23 octagonBaseA) ^ (-1 : ℤ) := by
      rw [← zpow_add]
      congr 1
      omega
    simp only [← mul_smul]
    rw [hpow, mul_smul, mul_smul, zpow_neg, zpow_one,
      octagon_A_inv_smul_sourceCone3CorridorSet,
      octagon_E2_smul_sourceCone2CorridorSet]
  · simp only [← mul_smul]
    rw [zpow_neg, inv_mul_cancel, mul_one, mul_smul]
    rfl
  · simp only [← mul_smul]
    rw [zpow_neg, inv_mul_cancel, mul_one, mul_smul]
    rfl

/-- Every conjugated corridor reflection is still an involution. -/
lemma octagonCorridorReflectionPGL_sq
    (r : OctagonCorridorReflection) :
    octagonCorridorReflectionPGL r *
        octagonCorridorReflectionPGL r = 1 := by
  rcases r with ⟨n, c⟩
  cases c <;>
    simp only [octagonCorridorReflectionPGL,
      OctagonCorridorCone.baseFactor, octagonBaseFactorElement,
      zpow_neg]
  · have he : octagonBaseToPGL23 octagonBaseE1 *
        octagonBaseToPGL23 octagonBaseE1 = 1 := by
      simpa only [pow_two] using (show
        octagonBaseToPGL23 octagonBaseE1 ^ 2 = 1 by
          rw [← map_pow, show octagonBaseE1 ^ 2 = 1 by
            exact octagonBase_e1_sq, map_one])
    calc
      _ = (octagonBaseToPGL23 octagonBaseA) ^ n *
          (octagonBaseToPGL23 octagonBaseE1 *
            octagonBaseToPGL23 octagonBaseE1) *
          ((octagonBaseToPGL23 octagonBaseA) ^ n)⁻¹ := by group
      _ = 1 := by rw [he]; simp
  · have he : octagonBaseToPGL23 octagonBaseE2 *
        octagonBaseToPGL23 octagonBaseE2 = 1 := by
      simpa only [pow_two] using (show
        octagonBaseToPGL23 octagonBaseE2 ^ 2 = 1 by
          rw [← map_pow, show octagonBaseE2 ^ 2 = 1 by
            exact octagonBase_e2_sq, map_one])
    calc
      _ = (octagonBaseToPGL23 octagonBaseA) ^ n *
          (octagonBaseToPGL23 octagonBaseE2 *
            octagonBaseToPGL23 octagonBaseE2) *
          ((octagonBaseToPGL23 octagonBaseA) ^ n)⁻¹ := by group
      _ = 1 := by rw [he]; simp
  · have he : octagonBaseToPGL23 octagonBaseE3 *
        octagonBaseToPGL23 octagonBaseE3 = 1 := by
      simpa only [pow_two] using (show
        octagonBaseToPGL23 octagonBaseE3 ^ 2 = 1 by
          rw [← map_pow, show octagonBaseE3 ^ 2 = 1 by
            exact octagonBase_e3_sq, map_one])
    calc
      _ = (octagonBaseToPGL23 octagonBaseA) ^ n *
          (octagonBaseToPGL23 octagonBaseE3 *
            octagonBaseToPGL23 octagonBaseE3) *
          ((octagonBaseToPGL23 octagonBaseA) ^ n)⁻¹ := by group
      _ = 1 := by rw [he]; simp
  · have he : octagonBaseToPGL23 octagonBaseE4 *
        octagonBaseToPGL23 octagonBaseE4 = 1 := by
      simpa only [pow_two] using (show
        octagonBaseToPGL23 octagonBaseE4 ^ 2 = 1 by
          rw [← map_pow, show octagonBaseE4 ^ 2 = 1 by
            exact octagonBase_e4_sq, map_one])
    calc
      _ = (octagonBaseToPGL23 octagonBaseA) ^ n *
          (octagonBaseToPGL23 octagonBaseE4 *
            octagonBaseToPGL23 octagonBaseE4) *
          ((octagonBaseToPGL23 octagonBaseA) ^ n)⁻¹ := by group
      _ = 1 := by rw [he]; simp

/-- A conjugated cone reflection carries its right incident bridge exactly
back to its left incident bridge. -/
lemma octagonCorridorReflectionPGL_smul_rightBridge
    (r : OctagonCorridorReflection) :
    octagonCorridorReflectionPGL r •
        octagonCorridorBridgeSet
          (octagonCorridorReflectionRightBridge r) =
      octagonCorridorBridgeSet
        (octagonCorridorReflectionLeftBridge r) := by
  have h := congrArg
    (fun U : Set OctagonProjectiveBoundary =>
      octagonCorridorReflectionPGL r • U)
    (octagonCorridorReflectionPGL_smul_leftBridge r)
  rw [← mul_smul, octagonCorridorReflectionPGL_sq, one_smul] at h
  exact h.symm

private lemma octagonPositiveScaledIntervals_disjoint_of_ne
    {n m : ℤ} {l u l' u' : ℝ}
    (hl : 0 < l) (hlu : l < u) (hl' : 0 < l') (hlu' : l' < u')
    (hnm : n ≠ m)
    (hforward : u ≤ octagonCorridorScale * l')
    (hbackward : u' ≤ octagonCorridorScale * l) :
    Disjoint
      (projectiveIntervalSet
        (octagonCorridorScale ^ n * l) (octagonCorridorScale ^ n * u))
      (projectiveIntervalSet
        (octagonCorridorScale ^ m * l') (octagonCorridorScale ^ m * u')) := by
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · apply octagonScaledIntervals_disjoint_of_shift
      (n := n) (m := m) (d := 1) hl hlu hl' hlu'
    · omega
    · omega
    · simpa using hforward
  · symm
    apply octagonScaledIntervals_disjoint_of_shift
      (n := m) (m := n) (d := 1) hl' hlu' hl hlu
    · omega
    · omega
    · simpa using hbackward

private lemma octagonNegativeScaledIntervals_disjoint_of_ne
    {n m : ℤ} {l u l' u' : ℝ}
    (hl : 0 < l) (hlu : l < u) (hl' : 0 < l') (hlu' : l' < u')
    (hnm : n ≠ m)
    (hforward : u ≤ octagonCorridorScale * l')
    (hbackward : u' ≤ octagonCorridorScale * l) :
    Disjoint
      (projectiveIntervalSet
        (octagonCorridorScale ^ n * (-u))
        (octagonCorridorScale ^ n * (-l)))
      (projectiveIntervalSet
        (octagonCorridorScale ^ m * (-u'))
        (octagonCorridorScale ^ m * (-l'))) := by
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · symm
    apply octagonNegativeScaledIntervals_disjoint_of_shift
      (n := n) (m := m) (d := 1) hl hlu hl' hlu'
    · omega
    · omega
    · simpa using hforward
  · apply octagonNegativeScaledIntervals_disjoint_of_shift
      (n := m) (m := n) (d := 1) hl' hlu' hl hlu
    · omega
    · omega
    · simpa using hbackward

private lemma octagonPositiveScaledIntervals_disjoint_negative
    {n m : ℤ} {l u l' u' : ℝ}
    (hl : 0 < l) (hlu : l < u) (hl' : 0 < l') (hlu' : l' < u') :
    Disjoint
      (projectiveIntervalSet
        (octagonCorridorScale ^ n * l) (octagonCorridorScale ^ n * u))
      (projectiveIntervalSet
        (octagonCorridorScale ^ m * (-u'))
        (octagonCorridorScale ^ m * (-l'))) := by
  have hrn : 0 < octagonCorridorScale ^ n :=
    zpow_pos octagonCorridorScale_pos n
  have hrm : 0 < octagonCorridorScale ^ m :=
    zpow_pos octagonCorridorScale_pos m
  symm
  apply projectiveIntervalSet_disjoint_of_le
  · nlinarith
  · nlinarith
  · exact mul_lt_mul_of_pos_left hlu hrn

private lemma octagonSmallPositiveDomain_disjoint_gap
    {n m : ℤ} (hnm : m ≠ n - 1) :
    Disjoint
      (projectiveIntervalSet
        (octagonCorridorScale ^ n * (1 / 4))
        (octagonCorridorScale ^ n * 1))
      (projectiveIntervalSet
        (octagonCorridorScale ^ m * 1)
        (octagonCorridorScale ^ m * 16)) := by
  by_cases hle : n ≤ m
  · apply octagonScaledIntervals_disjoint_of_shift
      (n := n) (m := m) (d := 0)
      (l := 1 / 4) (u := 1) (l' := 1) (u' := 16)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · omega
    · omega
    · norm_num
  · symm
    apply octagonScaledIntervals_disjoint_of_shift
      (n := m) (m := n) (d := 2)
      (l := 1) (u := 16) (l' := 1 / 4) (u' := 1)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · omega
    · omega
    · rw [zpow_ofNat]
      norm_num [pow_two]
      nlinarith [octagonCorridorScale_gt,
        sq_nonneg (octagonCorridorScale - 33)]

private lemma octagonSmallNegativeDomain_disjoint_gap
    {n m : ℤ} (hnm : m ≠ n - 1) :
    Disjoint
      (projectiveIntervalSet
        (octagonCorridorScale ^ n * (-1))
        (octagonCorridorScale ^ n * (-(1 / 4))))
      (projectiveIntervalSet
        (octagonCorridorScale ^ m * (-16))
        (octagonCorridorScale ^ m * (-1))) := by
  by_cases hle : n ≤ m
  · symm
    apply octagonNegativeScaledIntervals_disjoint_of_shift
      (n := n) (m := m) (d := 0)
      (l := 1 / 4) (u := 1) (l' := 1) (u' := 16)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · omega
    · omega
    · norm_num
  · apply octagonNegativeScaledIntervals_disjoint_of_shift
      (n := m) (m := n) (d := 2)
      (l := 1) (u := 16) (l' := 1 / 4) (u' := 1)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · omega
    · omega
    · rw [zpow_ofNat]
      norm_num [pow_two]
      nlinarith [octagonCorridorScale_gt,
        sq_nonneg (octagonCorridorScale - 33)]

/-- The ordinary ping-pong domain of a conjugated cone reflection is
disjoint from every bridge not incident to that reflection. -/
theorem octagonCorridorReflectionDomain_disjoint_nonincident
    (r : OctagonCorridorReflection) (b : OctagonCorridorBridge)
    (h : ¬ OctagonCorridorIncident r b) :
    Disjoint (octagonCorridorReflectionDomain r)
      (octagonCorridorBridgeSet b) := by
  rcases r with ⟨n, c⟩
  rcases b with ⟨m, k⟩
  rw [octagonCorridorReflectionDomain_eq_interval]
  have hb := octagonCorridorBridgeSet_subset_shell
    (⟨m, k⟩ : OctagonCorridorBridge)
  cases c <;> cases k
  · have hd := octagonPositiveScaledIntervals_disjoint_negative
      (n := m) (m := n)
      (l := 1 / 2) (u := 2) (l' := 1 / 4) (u' := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact hd.symm.mono Set.Subset.rfl (by
      simpa [octagonCorridorBridgeShell] using hb)
  · have hd := octagonPositiveScaledIntervals_disjoint_negative
      (n := m) (m := n)
      (l := 1) (u := 16) (l' := 1 / 4) (u' := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact hd.symm.mono Set.Subset.rfl (by
      simpa [octagonCorridorBridgeShell] using hb)
  · have hmn : n ≠ m := by
      intro hnm
      subst m
      apply h
      right
      rfl
    have hd := octagonNegativeScaledIntervals_disjoint_of_ne
      (n := n) (m := m)
      (l := 1 / 4) (u := 1) (l' := 1 / 2) (u' := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hmn
      (by norm_num; linarith [octagonCorridorScale_gt])
      (by norm_num; linarith [octagonCorridorScale_gt])
    exact hd.mono Set.Subset.rfl (by
      simpa [octagonCorridorBridgeShell] using hb)

  · have hmn : m ≠ n - 1 := by
      intro hmn
      subst m
      apply h
      left
      rfl
    exact (octagonSmallNegativeDomain_disjoint_gap hmn).mono
      Set.Subset.rfl (by
        simpa [octagonCorridorBridgeShell] using hb)
  · have hmn : n ≠ m := by
      intro hnm
      subst m
      apply h
      right
      rfl
    have hd := octagonPositiveScaledIntervals_disjoint_of_ne
      (n := n) (m := m)
      (l := 1 / 4) (u := 1) (l' := 1 / 2) (u' := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hmn
      (by norm_num; linarith [octagonCorridorScale_gt])
      (by norm_num; linarith [octagonCorridorScale_gt])
    exact hd.mono Set.Subset.rfl (by
      simpa [octagonCorridorBridgeShell] using hb)
  · have hmn : m ≠ n - 1 := by
      intro hmn
      subst m
      apply h
      left
      rfl
    exact (octagonSmallPositiveDomain_disjoint_gap hmn).mono
      Set.Subset.rfl (by
        simpa [octagonCorridorBridgeShell] using hb)
  · have hd := octagonPositiveScaledIntervals_disjoint_negative
      (n := n) (m := m)
      (l := 1 / 4) (u := 1) (l' := 1 / 2) (u' := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact hd.mono Set.Subset.rfl (by
      simpa [octagonCorridorBridgeShell] using hb)
  · have hd := octagonPositiveScaledIntervals_disjoint_negative
      (n := n) (m := m)
      (l := 1 / 4) (u := 1) (l' := 1) (u' := 16)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact hd.mono Set.Subset.rfl (by
      simpa [octagonCorridorBridgeShell] using hb)
  · have hmn : n ≠ m := by
      intro hnm
      subst m
      apply h
      left
      rfl
    have hd := octagonPositiveScaledIntervals_disjoint_of_ne
      (n := n) (m := m)
      (l := 1) (u := 4) (l' := 1 / 2) (u' := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hmn
      (by norm_num; linarith [octagonCorridorScale_gt])
      (by norm_num; linarith [octagonCorridorScale_gt])
    exact hd.mono Set.Subset.rfl (by
      simpa [octagonCorridorBridgeShell] using hb)
  · have hmn : n ≠ m := by
      intro hnm
      subst m
      apply h
      right
      rfl
    have hd := octagonPositiveScaledIntervals_disjoint_of_ne
      (n := n) (m := m)
      (l := 1) (u := 4) (l' := 1) (u' := 16)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hmn
      (by norm_num; linarith [octagonCorridorScale_gt])
      (by norm_num; linarith [octagonCorridorScale_gt])
    exact hd.mono Set.Subset.rfl (by
      simpa [octagonCorridorBridgeShell] using hb)
  · have hd := octagonPositiveScaledIntervals_disjoint_negative
      (n := n) (m := m)
      (l := 1) (u := 4) (l' := 1 / 2) (u' := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact hd.mono Set.Subset.rfl (by
      simpa [octagonCorridorBridgeShell] using hb)
  · have hd := octagonPositiveScaledIntervals_disjoint_negative
      (n := n) (m := m)
      (l := 1) (u := 4) (l' := 1) (u' := 16)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact hd.mono Set.Subset.rfl (by
      simpa [octagonCorridorBridgeShell] using hb)
  · have hd := octagonPositiveScaledIntervals_disjoint_negative
      (n := m) (m := n)
      (l := 1 / 2) (u := 2) (l' := 1) (u' := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact hd.symm.mono Set.Subset.rfl (by
      simpa [octagonCorridorBridgeShell] using hb)
  · have hd := octagonPositiveScaledIntervals_disjoint_negative
      (n := m) (m := n)
      (l := 1) (u := 16) (l' := 1) (u' := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact hd.symm.mono Set.Subset.rfl (by
      simpa [octagonCorridorBridgeShell] using hb)
  · have hmn : n ≠ m := by
      intro hnm
      subst m
      apply h
      left
      rfl
    have hd := octagonNegativeScaledIntervals_disjoint_of_ne
      (n := n) (m := m)
      (l := 1) (u := 4) (l' := 1 / 2) (u' := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hmn
      (by norm_num; linarith [octagonCorridorScale_gt])
      (by norm_num; linarith [octagonCorridorScale_gt])
    exact hd.mono Set.Subset.rfl (by
      simpa [octagonCorridorBridgeShell] using hb)
  · have hmn : n ≠ m := by
      intro hnm
      subst m
      apply h
      right
      rfl
    have hd := octagonNegativeScaledIntervals_disjoint_of_ne
      (n := n) (m := m)
      (l := 1) (u := 4) (l' := 1) (u' := 16)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hmn
      (by norm_num; linarith [octagonCorridorScale_gt])
      (by norm_num; linarith [octagonCorridorScale_gt])
    exact hd.mono Set.Subset.rfl (by
      simpa [octagonCorridorBridgeShell] using hb)

private lemma octagonPositiveSmallLargeDomains_disjoint (n m : ℤ) :
    Disjoint
      (projectiveIntervalSet
        (octagonCorridorScale ^ n * (1 / 4))
        (octagonCorridorScale ^ n * 1))
      (projectiveIntervalSet
        (octagonCorridorScale ^ m * 1)
        (octagonCorridorScale ^ m * 4)) := by
  by_cases hnm : n = m
  · subst m
    have hr : 0 < octagonCorridorScale ^ n :=
      zpow_pos octagonCorridorScale_pos n
    apply projectiveIntervalSet_disjoint_of_le <;> nlinarith
  · apply octagonPositiveScaledIntervals_disjoint_of_ne
      (n := n) (m := m)
      (l := 1 / 4) (u := 1) (l' := 1) (u' := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hnm
    · norm_num
      linarith [octagonCorridorScale_gt]
    · norm_num
      linarith [octagonCorridorScale_gt]

private lemma octagonNegativeSmallLargeDomains_disjoint (n m : ℤ) :
    Disjoint
      (projectiveIntervalSet
        (octagonCorridorScale ^ n * (-1))
        (octagonCorridorScale ^ n * (-(1 / 4))))
      (projectiveIntervalSet
        (octagonCorridorScale ^ m * (-4))
        (octagonCorridorScale ^ m * (-1))) := by
  by_cases hnm : n = m
  · subst m
    have hr : 0 < octagonCorridorScale ^ n :=
      zpow_pos octagonCorridorScale_pos n
    symm
    apply projectiveIntervalSet_disjoint_of_le <;> nlinarith
  · apply octagonNegativeScaledIntervals_disjoint_of_ne
      (n := n) (m := m)
      (l := 1 / 4) (u := 1) (l' := 1) (u' := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hnm
    · norm_num
      linarith [octagonCorridorScale_gt]
    · norm_num
      linarith [octagonCorridorScale_gt]

/-- Distinct conjugated cone reflections have disjoint ordinary
ping-pong domains. -/
theorem octagonCorridorReflectionDomain_pairwise_disjoint :
    Pairwise fun r s =>
      Disjoint (octagonCorridorReflectionDomain r)
        (octagonCorridorReflectionDomain s) := by
  rintro ⟨n, c⟩ ⟨m, d⟩ hne
  rw [octagonCorridorReflectionDomain_eq_interval,
    octagonCorridorReflectionDomain_eq_interval]
  cases c <;> cases d
  · have hnm : n ≠ m := by
      intro hnm
      apply hne
      cases hnm
      rfl
    apply octagonNegativeScaledIntervals_disjoint_of_ne
      (n := n) (m := m)
      (l := 1 / 4) (u := 1) (l' := 1 / 4) (u' := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hnm
    all_goals norm_num; linarith [octagonCorridorScale_gt]
  · exact (octagonPositiveScaledIntervals_disjoint_negative
      (n := m) (m := n)
      (l := 1 / 4) (u := 1) (l' := 1 / 4) (u' := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).symm
  · exact (octagonPositiveScaledIntervals_disjoint_negative
      (n := m) (m := n)
      (l := 1) (u := 4) (l' := 1 / 4) (u' := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).symm
  · exact octagonNegativeSmallLargeDomains_disjoint n m
  · exact octagonPositiveScaledIntervals_disjoint_negative
      (n := n) (m := m)
      (l := 1 / 4) (u := 1) (l' := 1 / 4) (u' := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · have hnm : n ≠ m := by
      intro hnm
      apply hne
      cases hnm
      rfl
    apply octagonPositiveScaledIntervals_disjoint_of_ne
      (n := n) (m := m)
      (l := 1 / 4) (u := 1) (l' := 1 / 4) (u' := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hnm
    all_goals norm_num; linarith [octagonCorridorScale_gt]
  · exact octagonPositiveSmallLargeDomains_disjoint n m
  · exact octagonPositiveScaledIntervals_disjoint_negative
      (n := n) (m := m)
      (l := 1 / 4) (u := 1) (l' := 1) (u' := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact octagonPositiveScaledIntervals_disjoint_negative
      (n := n) (m := m)
      (l := 1) (u := 4) (l' := 1 / 4) (u' := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact (octagonPositiveSmallLargeDomains_disjoint m n).symm
  · have hnm : n ≠ m := by
      intro hnm
      apply hne
      cases hnm
      rfl
    apply octagonPositiveScaledIntervals_disjoint_of_ne
      (n := n) (m := m)
      (l := 1) (u := 4) (l' := 1) (u' := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hnm
    all_goals norm_num; linarith [octagonCorridorScale_gt]
  · exact octagonPositiveScaledIntervals_disjoint_negative
      (n := n) (m := m)
      (l := 1) (u := 4) (l' := 1) (u' := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact (octagonNegativeSmallLargeDomains_disjoint m n).symm
  · exact (octagonPositiveScaledIntervals_disjoint_negative
      (n := m) (m := n)
      (l := 1 / 4) (u := 1) (l' := 1) (u' := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).symm
  · exact (octagonPositiveScaledIntervals_disjoint_negative
      (n := m) (m := n)
      (l := 1) (u := 4) (l' := 1) (u' := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).symm
  · have hnm : n ≠ m := by
      intro hnm
      apply hne
      cases hnm
      rfl
    apply octagonNegativeScaledIntervals_disjoint_of_ne
      (n := n) (m := m)
      (l := 1) (u := 4) (l' := 1) (u' := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hnm
    all_goals norm_num; linarith [octagonCorridorScale_gt]

/-- A conjugated cone reflection sends the complement of its conjugated
ordinary ping-pong domain into that domain. -/
theorem octagonCorridorReflectionPGL_maps_compl_domain
    (r : OctagonCorridorReflection) :
    Set.MapsTo
      (fun p : OctagonProjectiveBoundary =>
        octagonCorridorReflectionPGL r • p)
      (octagonCorridorReflectionDomain r)ᶜ
      (octagonCorridorReflectionDomain r) := by
  rcases r with ⟨n, c⟩
  have hbase : Set.MapsTo
      (fun p : OctagonProjectiveBoundary =>
        octagonBaseToPGL23
          (octagonBaseFactorElement c.baseFactor) • p)
      (octagonBasePingPongSet c.baseFactor)ᶜ
      (octagonBasePingPongSet c.baseFactor) := by
    cases c with
    | cone1 =>
        simpa [OctagonCorridorCone.baseFactor,
          octagonBBaseFactor] using
          (octagonB_maps_compl_basePingPongSet true false)
    | cone2 =>
        simpa [OctagonCorridorCone.baseFactor,
          octagonBBaseFactor] using
          (octagonB_maps_compl_basePingPongSet false false)
    | cone3 =>
        simpa [OctagonCorridorCone.baseFactor,
          octagonBBaseFactor] using
          (octagonB_maps_compl_basePingPongSet false true)
    | cone4 =>
        simpa [OctagonCorridorCone.baseFactor,
          octagonBBaseFactor] using
          (octagonB_maps_compl_basePingPongSet true true)
  intro p hp
  let q : OctagonProjectiveBoundary :=
    (octagonBaseToPGL23 octagonBaseA) ^ (-n) • p
  have hpq : (octagonBaseToPGL23 octagonBaseA) ^ n • q = p := by
    simp only [q, ← mul_smul, ← zpow_add]
    norm_num
  have hq : q ∈ (octagonBasePingPongSet c.baseFactor)ᶜ := by
    rw [Set.mem_compl_iff]
    intro hqin
    apply hp
    rw [← hpq]
    exact Set.smul_mem_smul_set hqin
  have himage := Set.smul_mem_smul_set (a :=
    (octagonBaseToPGL23 octagonBaseA) ^ n) (hbase hq)
  rw [octagonCorridorReflectionDomain]
  convert himage using 1
  rw [← hpq]
  simp only [octagonCorridorReflectionPGL, q,
    ← mul_smul, ← zpow_add]
  norm_num
  rw [mul_assoc]

end

end SystolicGrowth
