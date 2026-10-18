module

public import BuserSarnak.BuserSarnakHNNBaseCorridorNormalization

@[expose] public section

/-!
# Classifying accepted octagon corridor words

The direct syllable automaton separates the source and target corridor
components and then peels the two possible oriented cycles from every
self-overlap word.
-/

open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise

namespace SystolicGrowth

noncomputable section

/-- Whether a bridge belongs to the source corridor component. -/
def octagonCorridorBridgeIsSource (b : OctagonCorridorBridge) : Bool :=
  match b.kind with
  | .sourceCenter | .sourceGap => true
  | .targetCenter | .targetGap => false

private lemma octagonCorridorBridgeShift_isSource
    (k : ℤ) (b : OctagonCorridorBridge) :
    octagonCorridorBridgeIsSource (octagonCorridorBridgeShift k b) =
      octagonCorridorBridgeIsSource b := by
  rcases b with ⟨n, kind⟩
  cases kind <;> rfl

private lemma octagonCorridorReflectionStep_isSource
    {r : OctagonCorridorReflection} {b c : OctagonCorridorBridge}
    (hstep : octagonCorridorReflectionStep r b = some c) :
    octagonCorridorBridgeIsSource c =
      octagonCorridorBridgeIsSource b := by
  rcases r with ⟨n, cone⟩
  rcases b with ⟨m, kind⟩
  cases cone <;> cases kind <;>
    simp [octagonCorridorReflectionStep,
      octagonCorridorReflectionLeftBridge,
      octagonCorridorReflectionRightBridge,
      OctagonCorridorBridge.mk.injEq] at hstep <;>
    try contradiction
  all_goals rcases hstep with ⟨_, rfl⟩
  all_goals rfl

private lemma octagonBaseCorridorLetterStep_isSource
    {l : OctagonBaseCorridorLetter} {b c : OctagonCorridorBridge}
    (hstep : octagonBaseCorridorLetterStep l b = some c) :
    octagonCorridorBridgeIsSource c =
      octagonCorridorBridgeIsSource b := by
  rcases l with ⟨i, x⟩
  cases i with
  | handle =>
      simp only [octagonBaseCorridorLetterStep] at hstep
      cases hstep
      exact octagonCorridorBridgeShift_isSource _ _
  | cone1 =>
      exact octagonCorridorReflectionStep_isSource hstep
  | cone2 =>
      exact octagonCorridorReflectionStep_isSource hstep
  | cone3 =>
      exact octagonCorridorReflectionStep_isSource hstep
  | cone4 =>
      exact octagonCorridorReflectionStep_isSource hstep

/-- Every successful direct syllable path remains in one corridor
component. -/
lemma octagonBaseCorridorPath_isSource
    {w : List OctagonBaseCorridorLetter} {b c : OctagonCorridorBridge}
    (hpath : octagonBaseCorridorPath w b = some c) :
    octagonCorridorBridgeIsSource c =
      octagonCorridorBridgeIsSource b := by
  induction w generalizing c with
  | nil =>
      simp only [octagonBaseCorridorPath] at hpath
      cases hpath
      rfl
  | cons l w ih =>
      simp only [octagonBaseCorridorPath] at hpath
      cases htail : octagonBaseCorridorPath w b with
      | none => simp [htail] at hpath
      | some d =>
          simp only [htail, Option.bind_some] at hpath
          exact (octagonBaseCorridorLetterStep_isSource hpath).trans
            (ih htail)

private lemma octagonSourceCenterBridgeSet :
    octagonCorridorBridgeSet ⟨0, .sourceCenter⟩ =
      octagonHNNSourceBoundarySet := by
  change (octagonBaseToPGL23 octagonBaseA) ^ (0 : ℤ) •
      octagonHNNSourceBoundarySet = octagonHNNSourceBoundarySet
  rw [zpow_zero, one_smul]

private lemma octagonTargetCenterBridgeSet :
    octagonCorridorBridgeSet ⟨0, .targetCenter⟩ =
      octagonHNNTargetBoundarySet := by
  change (octagonBaseToPGL23 octagonBaseA) ^ (0 : ℤ) •
      octagonHNNTargetBoundarySet = octagonHNNTargetBoundarySet
  rw [zpow_zero, one_smul]

/-- No reduced base word carries a source-boundary point into the target
boundary. -/
theorem octagonHNNBaseCorridor_source_target
    (w : List OctagonBaseCorridorLetter)
    (hreduced : OctagonBaseCorridorReduced w) :
    ¬ octagonBoundaryCorridorOverlap octagonHNNSourceBoundarySet
      octagonHNNTargetBoundarySet w := by
  intro hoverlap
  have hpath : octagonBaseCorridorPath w ⟨0, .sourceCenter⟩ =
      some ⟨0, .targetCenter⟩ := by
    apply octagonBaseCorridorPath_eq_of_overlap w hreduced
    simpa [octagonBoundaryCorridorOverlap,
      octagonSourceCenterBridgeSet, octagonTargetCenterBridgeSet] using
      hoverlap
  have hside := octagonBaseCorridorPath_isSource hpath
  contradiction

/-- No reduced base word carries a target-boundary point into the source
boundary. -/
theorem octagonHNNBaseCorridor_target_source
    (w : List OctagonBaseCorridorLetter)
    (hreduced : OctagonBaseCorridorReduced w) :
    ¬ octagonBoundaryCorridorOverlap octagonHNNTargetBoundarySet
      octagonHNNSourceBoundarySet w := by
  intro hoverlap
  have hpath : octagonBaseCorridorPath w ⟨0, .targetCenter⟩ =
      some ⟨0, .sourceCenter⟩ := by
    apply octagonBaseCorridorPath_eq_of_overlap w hreduced
    simpa [octagonBoundaryCorridorOverlap,
      octagonSourceCenterBridgeSet, octagonTargetCenterBridgeSet] using
      hoverlap
  have hside := octagonBaseCorridorPath_isSource hpath
  contradiction

private lemma octagonBaseCorridorPath_append
    (u v : List OctagonBaseCorridorLetter) (b : OctagonCorridorBridge) :
    octagonBaseCorridorPath (u ++ v) b =
      (octagonBaseCorridorPath v b).bind
        (octagonBaseCorridorPath u) := by
  induction u with
  | nil =>
      simp only [List.nil_append]
      cases octagonBaseCorridorPath v b <;> rfl
  | cons l u ih =>
      simp only [List.cons_append, octagonBaseCorridorPath]
      rw [ih]
      cases octagonBaseCorridorPath v b <;> rfl

private lemma OctagonBaseCorridorReduced.reverse
    {w : List OctagonBaseCorridorLetter}
    (h : OctagonBaseCorridorReduced w) :
    OctagonBaseCorridorReduced w.reverse := by
  constructor
  · intro l hl
    apply h.1 l
    simpa using hl
  · rw [List.isChain_reverse]
    apply h.2.imp
    intro l l' hne heq
    exact hne heq.symm

@[simp] private lemma octagonHandleStep_bridge
    (x : OctagonBaseFactorGroup .handle) (n : ℤ)
    (kind : OctagonCorridorBridgeKind) :
    octagonBaseCorridorLetterStep ⟨.handle, x⟩ ⟨n, kind⟩ =
      some ⟨octagonBaseReducedLetterWeight
        (⟨.handle, x⟩ : OctagonBaseCorridorLetter) + n, kind⟩ := rfl

@[simp] private lemma octagonHandleCorridorLetterStep
    (k n : ℤ) (kind : OctagonCorridorBridgeKind) :
    octagonBaseCorridorLetterStep (octagonHandleCorridorLetter k)
        ⟨n, kind⟩ = some ⟨k + n, kind⟩ := by
  change some (⟨octagonBaseReducedLetterWeight
      (octagonHandleCorridorLetter k) + n, kind⟩ : OctagonCorridorBridge) =
    some (⟨k + n, kind⟩ : OctagonCorridorBridge)
  rw [octagonBaseReducedLetterWeight_handleCorridorLetter]

@[simp] private lemma octagonCone2Step_sourceCenter
    (x : OctagonBaseFactorGroup .cone2) (n : ℤ) :
    octagonBaseCorridorLetterStep ⟨.cone2, x⟩
        ⟨n, .sourceCenter⟩ =
      if n = 0 then some ⟨-1, .sourceGap⟩ else none := by
  simp [octagonBaseCorridorLetterStep,
    octagonCorridorReflectionStep,
    octagonCorridorReflectionLeftBridge,
    octagonCorridorReflectionRightBridge,
    OctagonCorridorBridge.mk.injEq]

@[simp] private lemma octagonCone3Step_sourceCenter
    (x : OctagonBaseFactorGroup .cone3) (n : ℤ) :
    octagonBaseCorridorLetterStep ⟨.cone3, x⟩
        ⟨n, .sourceCenter⟩ =
      if n = 0 then some ⟨0, .sourceGap⟩ else none := by
  simp [octagonBaseCorridorLetterStep,
    octagonCorridorReflectionStep,
    octagonCorridorReflectionLeftBridge,
    octagonCorridorReflectionRightBridge,
    OctagonCorridorBridge.mk.injEq]

@[simp] private lemma octagonCone2Step_sourceGap
    (x : OctagonBaseFactorGroup .cone2) (n : ℤ) :
    octagonBaseCorridorLetterStep ⟨.cone2, x⟩
        ⟨n, .sourceGap⟩ =
      if n = -1 then some ⟨0, .sourceCenter⟩ else none := by
  simp [octagonBaseCorridorLetterStep,
    octagonCorridorReflectionStep,
    octagonCorridorReflectionLeftBridge,
    octagonCorridorReflectionRightBridge,
    OctagonCorridorBridge.mk.injEq]

@[simp] private lemma octagonCone3Step_sourceGap
    (x : OctagonBaseFactorGroup .cone3) (n : ℤ) :
    octagonBaseCorridorLetterStep ⟨.cone3, x⟩
        ⟨n, .sourceGap⟩ =
      if n = 0 then some ⟨0, .sourceCenter⟩ else none := by
  simp [octagonBaseCorridorLetterStep,
    octagonCorridorReflectionStep,
    octagonCorridorReflectionLeftBridge,
    octagonCorridorReflectionRightBridge,
    OctagonCorridorBridge.mk.injEq]

@[simp] private lemma octagonCone1Step_source
    (x : OctagonBaseFactorGroup .cone1) (n : ℤ)
    (gap : Bool) :
    octagonBaseCorridorLetterStep ⟨.cone1, x⟩
        ⟨n, if gap then .sourceGap else .sourceCenter⟩ = none := by
  cases gap <;> simp [octagonBaseCorridorLetterStep,
    octagonCorridorReflectionStep,
    octagonCorridorReflectionLeftBridge,
    octagonCorridorReflectionRightBridge]

@[simp] private lemma octagonCone4Step_source
    (x : OctagonBaseFactorGroup .cone4) (n : ℤ)
    (gap : Bool) :
    octagonBaseCorridorLetterStep ⟨.cone4, x⟩
        ⟨n, if gap then .sourceGap else .sourceCenter⟩ = none := by
  cases gap <;> simp [octagonBaseCorridorLetterStep,
    octagonCorridorReflectionStep,
    octagonCorridorReflectionLeftBridge,
    octagonCorridorReflectionRightBridge]

@[simp] private lemma octagonCone1Step_sourceCenter
    (x : OctagonBaseFactorGroup .cone1) (n : ℤ) :
    octagonBaseCorridorLetterStep ⟨.cone1, x⟩
      ⟨n, .sourceCenter⟩ = none := by
  simpa using octagonCone1Step_source x n false

@[simp] private lemma octagonCone1Step_sourceGap
    (x : OctagonBaseFactorGroup .cone1) (n : ℤ) :
    octagonBaseCorridorLetterStep ⟨.cone1, x⟩
      ⟨n, .sourceGap⟩ = none := by
  simpa using octagonCone1Step_source x n true

@[simp] private lemma octagonCone4Step_sourceCenter
    (x : OctagonBaseFactorGroup .cone4) (n : ℤ) :
    octagonBaseCorridorLetterStep ⟨.cone4, x⟩
      ⟨n, .sourceCenter⟩ = none := by
  simpa using octagonCone4Step_source x n false

@[simp] private lemma octagonCone4Step_sourceGap
    (x : OctagonBaseFactorGroup .cone4) (n : ℤ) :
    octagonBaseCorridorLetterStep ⟨.cone4, x⟩
      ⟨n, .sourceGap⟩ = none := by
  simpa using octagonCone4Step_source x n true

@[simp] private lemma octagonSourceForwardCycle_path :
    octagonBaseCorridorPath octagonSourceForwardCycle
        ⟨0, .sourceCenter⟩ = some ⟨0, .sourceCenter⟩ := by
  simp [octagonSourceForwardCycle, octagonBaseCorridorPath,
    octagonConeCorridorLetter]

@[simp] private lemma octagonSourceBackwardCycle_path :
    octagonBaseCorridorPath octagonSourceBackwardCycle
        ⟨0, .sourceCenter⟩ = some ⟨0, .sourceCenter⟩ := by
  simp [octagonSourceBackwardCycle, octagonBaseCorridorPath,
    octagonConeCorridorLetter]

private lemma OctagonBaseCorridorReduced.left_of_append
    {u v : List OctagonBaseCorridorLetter}
    (h : OctagonBaseCorridorReduced (u ++ v)) :
    OctagonBaseCorridorReduced u := by
  constructor
  · intro l hl
    exact h.1 l (List.mem_append_left v hl)
  · exact (List.isChain_append.mp h.2).1

private lemma octagonSourceCorridor_suffix
    (w : List OctagonBaseCorridorLetter)
    (hreduced : OctagonBaseCorridorReduced w)
    (hpath : octagonBaseCorridorPath w ⟨0, .sourceCenter⟩ =
      some ⟨0, .sourceCenter⟩) :
    w = [] ∨ ∃ v,
      OctagonBaseCorridorReduced v ∧
      octagonBaseCorridorPath v ⟨0, .sourceCenter⟩ =
        some ⟨0, .sourceCenter⟩ ∧
      (w = v ++ octagonSourceForwardCycle ∨
        w = v ++ octagonSourceBackwardCycle) := by
  have hrevReduced := hreduced.reverse
  generalize hrev : w.reverse = rev at hrevReduced
  cases rev with
  | nil =>
      left
      simpa using congrArg List.reverse hrev
  | cons l₁ rest =>
      have hw₁ : w = rest.reverse ++ [l₁] := by
        calc
          w = w.reverse.reverse := by simp
          _ = (l₁ :: rest).reverse := by rw [hrev]
          _ = rest.reverse ++ [l₁] := List.reverse_cons
      have hl₁ne : l₁.2 ≠ 1 :=
        hrevReduced.1 l₁ (by simp)
      rcases l₁ with ⟨i₁, x₁⟩
      cases i₁ with
      | handle =>
          have hk₁ := octagonBaseReducedHandleLetter_weight_ne_zero x₁ hl₁ne
          cases rest with
          | nil =>
              rw [hw₁, octagonBaseCorridorPath_append] at hpath
              simp [octagonBaseCorridorPath, hk₁] at hpath
          | cons l₂ rest₂ =>
              have hfac₁₂ : OctagonBaseFactor.handle ≠ l₂.1 :=
                (List.isChain_cons_cons.mp hrevReduced.2).1
              have hw₂ : w = rest₂.reverse ++ [l₂, ⟨.handle, x₁⟩] := by
                simpa [List.append_assoc] using hw₁
              rcases l₂ with ⟨i₂, x₂⟩
              cases i₂ with
              | handle => exact (hfac₁₂ rfl).elim
              | cone1 =>
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath] at hpath
              | cone2 =>
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath, hk₁] at hpath
              | cone3 =>
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath, hk₁] at hpath
              | cone4 =>
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath] at hpath
      | cone1 =>
          rw [hw₁, octagonBaseCorridorPath_append] at hpath
          simp [octagonBaseCorridorPath] at hpath
      | cone4 =>
          rw [hw₁, octagonBaseCorridorPath_append] at hpath
          simp [octagonBaseCorridorPath] at hpath
      | cone3 =>
          cases rest with
          | nil =>
              rw [hw₁, octagonBaseCorridorPath_append] at hpath
              simp [octagonBaseCorridorPath] at hpath
          | cons l₂ rest₂ =>
              have hfac₁₂ : OctagonBaseFactor.cone3 ≠ l₂.1 :=
                (List.isChain_cons_cons.mp hrevReduced.2).1
              rcases l₂ with ⟨i₂, x₂⟩
              have hl₂ne : x₂ ≠ 1 :=
                hrevReduced.1 ⟨i₂, x₂⟩ (by simp)
              cases i₂ with
              | cone1 =>
                  have hw₂ : w = rest₂.reverse ++
                      [⟨.cone1, x₂⟩, ⟨.cone3, x₁⟩] := by
                    simpa [List.append_assoc] using hw₁
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath] at hpath
              | cone2 =>
                  have hw₂ : w = rest₂.reverse ++
                      [⟨.cone2, x₂⟩, ⟨.cone3, x₁⟩] := by
                    simpa [List.append_assoc] using hw₁
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath] at hpath
              | cone3 => exact (hfac₁₂ rfl).elim
              | cone4 =>
                  have hw₂ : w = rest₂.reverse ++
                      [⟨.cone4, x₂⟩, ⟨.cone3, x₁⟩] := by
                    simpa [List.append_assoc] using hw₁
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath] at hpath
              | handle =>
                  have hk₂ :=
                    octagonBaseReducedHandleLetter_weight_ne_zero x₂ hl₂ne
                  cases rest₂ with
                  | nil =>
                      have hw₂ : w =
                          [⟨.handle, x₂⟩, ⟨.cone3, x₁⟩] := by
                        simpa using hw₁
                      rw [hw₂] at hpath
                      simp [octagonBaseCorridorPath] at hpath
                  | cons l₃ rest₃ =>
                      have hfac₂₃ : OctagonBaseFactor.handle ≠ l₃.1 :=
                        (List.isChain_cons_cons.mp hrevReduced.2.tail).1
                      rcases l₃ with ⟨i₃, x₃⟩
                      have hl₃ne : x₃ ≠ 1 :=
                        hrevReduced.1 ⟨i₃, x₃⟩ (by simp)
                      cases i₃ with
                      | handle => exact (hfac₂₃ rfl).elim
                      | cone1 =>
                          have hw₃ : w = rest₃.reverse ++
                              [⟨.cone1, x₃⟩, ⟨.handle, x₂⟩,
                                ⟨.cone3, x₁⟩] := by
                            simpa [List.append_assoc] using hw₁
                          rw [hw₃, octagonBaseCorridorPath_append] at hpath
                          simp [octagonBaseCorridorPath] at hpath
                      | cone3 =>
                          have hw₃ : w = rest₃.reverse ++
                              [⟨.cone3, x₃⟩, ⟨.handle, x₂⟩,
                                ⟨.cone3, x₁⟩] := by
                            simpa [List.append_assoc] using hw₁
                          rw [hw₃, octagonBaseCorridorPath_append] at hpath
                          simp [octagonBaseCorridorPath, hk₂] at hpath
                      | cone4 =>
                          have hw₃ : w = rest₃.reverse ++
                              [⟨.cone4, x₃⟩, ⟨.handle, x₂⟩,
                                ⟨.cone3, x₁⟩] := by
                            simpa [List.append_assoc] using hw₁
                          rw [hw₃, octagonBaseCorridorPath_append] at hpath
                          simp [octagonBaseCorridorPath] at hpath
                      | cone2 =>
                          have hw₃ : w = rest₃.reverse ++
                              [⟨.cone2, x₃⟩, ⟨.handle, x₂⟩,
                                ⟨.cone3, x₁⟩] := by
                            simpa [List.append_assoc] using hw₁
                          have hk : octagonBaseReducedLetterWeight
                              (⟨.handle, x₂⟩ : OctagonBaseCorridorLetter) = -1 := by
                            by_contra hk
                            rw [hw₃, octagonBaseCorridorPath_append] at hpath
                            simp [octagonBaseCorridorPath, hk] at hpath
                          have hl₁ := octagonBaseConeSyllable_eq_corridorLetter
                            (i := .cone3) (by intro h; cases h) x₁ hl₁ne
                          have hl₂ := octagonBaseHandleSyllable_eq_corridorLetter x₂
                          rw [hk] at hl₂
                          have hl₃ := octagonBaseConeSyllable_eq_corridorLetter
                            (i := .cone2) (by intro h; cases h) x₃ hl₃ne
                          rw [hl₁, hl₂, hl₃] at hw₃
                          right
                          refine ⟨rest₃.reverse, ?_, ?_, Or.inl ?_⟩
                          · rw [hw₃] at hreduced
                            exact hreduced.left_of_append
                          · rw [hw₃, octagonBaseCorridorPath_append] at hpath
                            change (octagonBaseCorridorPath
                              octagonSourceForwardCycle
                              ⟨0, .sourceCenter⟩).bind
                                (octagonBaseCorridorPath rest₃.reverse) =
                              some ⟨0, .sourceCenter⟩ at hpath
                            rw [octagonSourceForwardCycle_path] at hpath
                            exact hpath
                          · simpa [octagonSourceForwardCycle] using hw₃
      | cone2 =>
          cases rest with
          | nil =>
              rw [hw₁, octagonBaseCorridorPath_append] at hpath
              simp [octagonBaseCorridorPath] at hpath
          | cons l₂ rest₂ =>
              have hfac₁₂ : OctagonBaseFactor.cone2 ≠ l₂.1 :=
                (List.isChain_cons_cons.mp hrevReduced.2).1
              rcases l₂ with ⟨i₂, x₂⟩
              have hl₂ne : x₂ ≠ 1 :=
                hrevReduced.1 ⟨i₂, x₂⟩ (by simp)
              cases i₂ with
              | cone1 =>
                  have hw₂ : w = rest₂.reverse ++
                      [⟨.cone1, x₂⟩, ⟨.cone2, x₁⟩] := by
                    simpa [List.append_assoc] using hw₁
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath] at hpath
              | cone2 => exact (hfac₁₂ rfl).elim
              | cone3 =>
                  have hw₂ : w = rest₂.reverse ++
                      [⟨.cone3, x₂⟩, ⟨.cone2, x₁⟩] := by
                    simpa [List.append_assoc] using hw₁
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath] at hpath
              | cone4 =>
                  have hw₂ : w = rest₂.reverse ++
                      [⟨.cone4, x₂⟩, ⟨.cone2, x₁⟩] := by
                    simpa [List.append_assoc] using hw₁
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath] at hpath
              | handle =>
                  have hk₂ :=
                    octagonBaseReducedHandleLetter_weight_ne_zero x₂ hl₂ne
                  cases rest₂ with
                  | nil =>
                      have hw₂ : w =
                          [⟨.handle, x₂⟩, ⟨.cone2, x₁⟩] := by
                        simpa using hw₁
                      rw [hw₂] at hpath
                      simp [octagonBaseCorridorPath] at hpath
                  | cons l₃ rest₃ =>
                      have hfac₂₃ : OctagonBaseFactor.handle ≠ l₃.1 :=
                        (List.isChain_cons_cons.mp hrevReduced.2.tail).1
                      rcases l₃ with ⟨i₃, x₃⟩
                      have hl₃ne : x₃ ≠ 1 :=
                        hrevReduced.1 ⟨i₃, x₃⟩ (by simp)
                      cases i₃ with
                      | handle => exact (hfac₂₃ rfl).elim
                      | cone1 =>
                          have hw₃ : w = rest₃.reverse ++
                              [⟨.cone1, x₃⟩, ⟨.handle, x₂⟩,
                                ⟨.cone2, x₁⟩] := by
                            simpa [List.append_assoc] using hw₁
                          rw [hw₃, octagonBaseCorridorPath_append] at hpath
                          simp [octagonBaseCorridorPath] at hpath
                      | cone2 =>
                          have hw₃ : w = rest₃.reverse ++
                              [⟨.cone2, x₃⟩, ⟨.handle, x₂⟩,
                                ⟨.cone2, x₁⟩] := by
                            simpa [List.append_assoc] using hw₁
                          rw [hw₃, octagonBaseCorridorPath_append] at hpath
                          simp [octagonBaseCorridorPath, hk₂] at hpath
                      | cone4 =>
                          have hw₃ : w = rest₃.reverse ++
                              [⟨.cone4, x₃⟩, ⟨.handle, x₂⟩,
                                ⟨.cone2, x₁⟩] := by
                            simpa [List.append_assoc] using hw₁
                          rw [hw₃, octagonBaseCorridorPath_append] at hpath
                          simp [octagonBaseCorridorPath] at hpath
                      | cone3 =>
                          have hw₃ : w = rest₃.reverse ++
                              [⟨.cone3, x₃⟩, ⟨.handle, x₂⟩,
                                ⟨.cone2, x₁⟩] := by
                            simpa [List.append_assoc] using hw₁
                          have hk : octagonBaseReducedLetterWeight
                              (⟨.handle, x₂⟩ : OctagonBaseCorridorLetter) = 1 := by
                            by_contra hk
                            have hk' : octagonBaseReducedLetterWeight
                                (⟨.handle, x₂⟩ : OctagonBaseCorridorLetter) +
                                  (-1) ≠ 0 := by omega
                            rw [hw₃, octagonBaseCorridorPath_append] at hpath
                            simp [octagonBaseCorridorPath, hk'] at hpath
                          have hl₁ := octagonBaseConeSyllable_eq_corridorLetter
                            (i := .cone2) (by intro h; cases h) x₁ hl₁ne
                          have hl₂ := octagonBaseHandleSyllable_eq_corridorLetter x₂
                          rw [hk] at hl₂
                          have hl₃ := octagonBaseConeSyllable_eq_corridorLetter
                            (i := .cone3) (by intro h; cases h) x₃ hl₃ne
                          rw [hl₁, hl₂, hl₃] at hw₃
                          right
                          refine ⟨rest₃.reverse, ?_, ?_, Or.inr ?_⟩
                          · rw [hw₃] at hreduced
                            exact hreduced.left_of_append
                          · rw [hw₃, octagonBaseCorridorPath_append] at hpath
                            change (octagonBaseCorridorPath
                              octagonSourceBackwardCycle
                              ⟨0, .sourceCenter⟩).bind
                                (octagonBaseCorridorPath rest₃.reverse) =
                              some ⟨0, .sourceCenter⟩ at hpath
                            rw [octagonSourceBackwardCycle_path] at hpath
                            exact hpath
                          · simpa [octagonSourceBackwardCycle] using hw₃

private lemma octagonSourceBackward_append_forward_not_reduced
    (n : ℕ) (hn : n ≠ 0) :
    ¬ OctagonBaseCorridorReduced
      (FiniteStatePingPong.cycleRepeat octagonSourceBackwardCycle n ++
        octagonSourceForwardCycle) := by
  intro h
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
      have hboundary := (List.isChain_append.mp h.2).2.2
      have hbad := hboundary
        (octagonConeCorridorLetter .cone2)
        (by simp [FiniteStatePingPong.cycleRepeat_succ,
          octagonSourceBackwardCycle])
        (octagonConeCorridorLetter .cone2)
        (by simp [octagonSourceForwardCycle])
      exact hbad rfl

private lemma octagonSourceForward_append_backward_not_reduced
    (n : ℕ) (hn : n ≠ 0) :
    ¬ OctagonBaseCorridorReduced
      (FiniteStatePingPong.cycleRepeat octagonSourceForwardCycle n ++
        octagonSourceBackwardCycle) := by
  intro h
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
      have hboundary := (List.isChain_append.mp h.2).2.2
      have hbad := hboundary
        (octagonConeCorridorLetter .cone3)
        (by simp [FiniteStatePingPong.cycleRepeat_succ,
          octagonSourceForwardCycle])
        (octagonConeCorridorLetter .cone3)
        (by simp [octagonSourceBackwardCycle])
      exact hbad rfl

/-- Every reduced direct source loop consists entirely of forward cycles or
entirely of backward cycles. -/
theorem octagonSourceCorridorPath_classification
    (w : List OctagonBaseCorridorLetter)
    (hreduced : OctagonBaseCorridorReduced w)
    (hpath : octagonBaseCorridorPath w ⟨0, .sourceCenter⟩ =
      some ⟨0, .sourceCenter⟩) :
    w = [] ∨ OctagonSourceForwardCorridor w ∨
      OctagonSourceBackwardCorridor w := by
  rcases octagonSourceCorridor_suffix w hreduced hpath with
    hnil | ⟨v, hvred, hvpath, hforward | hbackward⟩
  · exact Or.inl hnil
  · rcases octagonSourceCorridorPath_classification v hvred hvpath with
      hvnil | hvforward | hvbackward
    · subst v
      right
      left
      refine ⟨1, ?_⟩
      simpa [FiniteStatePingPong.cycleRepeat_succ] using hforward
    · obtain ⟨n, hn⟩ := hvforward
      right
      left
      refine ⟨n + 1, ?_⟩
      rw [hforward, hn]
      exact (FiniteStatePingPong.cycleRepeat_succ
        octagonSourceForwardCycle n).symm
    · obtain ⟨n, hn⟩ := hvbackward
      by_cases hn0 : n = 0
      · subst n
        simp at hn
        subst v
        right
        left
        refine ⟨1, ?_⟩
        simpa [FiniteStatePingPong.cycleRepeat_succ] using hforward
      · exfalso
        apply octagonSourceBackward_append_forward_not_reduced n hn0
        rw [← hn, ← hforward]
        exact hreduced
  · rcases octagonSourceCorridorPath_classification v hvred hvpath with
      hvnil | hvforward | hvbackward
    · subst v
      right
      right
      refine ⟨1, ?_⟩
      simpa [FiniteStatePingPong.cycleRepeat_succ] using hbackward
    · obtain ⟨n, hn⟩ := hvforward
      by_cases hn0 : n = 0
      · subst n
        simp at hn
        subst v
        right
        right
        refine ⟨1, ?_⟩
        simpa [FiniteStatePingPong.cycleRepeat_succ] using hbackward
      · exfalso
        apply octagonSourceForward_append_backward_not_reduced n hn0
        rw [← hn, ← hbackward]
        exact hreduced
    · obtain ⟨n, hn⟩ := hvbackward
      right
      right
      refine ⟨n + 1, ?_⟩
      rw [hbackward, hn]
      exact (FiniteStatePingPong.cycleRepeat_succ
        octagonSourceBackwardCycle n).symm
termination_by w.length
decreasing_by
  · rw [hforward]
    simp [octagonSourceForwardCycle]
  · rw [hbackward]
    simp [octagonSourceBackwardCycle]
 
@[simp] private lemma octagonCone1Step_targetCenter
    (x : OctagonBaseFactorGroup .cone1) (n : ℤ) :
    octagonBaseCorridorLetterStep ⟨.cone1, x⟩
        ⟨n, .targetCenter⟩ =
      if n = 0 then some ⟨-1, .targetGap⟩ else none := by
  simp [octagonBaseCorridorLetterStep,
    octagonCorridorReflectionStep,
    octagonCorridorReflectionLeftBridge,
    octagonCorridorReflectionRightBridge,
    OctagonCorridorBridge.mk.injEq]

@[simp] private lemma octagonCone4Step_targetCenter
    (x : OctagonBaseFactorGroup .cone4) (n : ℤ) :
    octagonBaseCorridorLetterStep ⟨.cone4, x⟩
        ⟨n, .targetCenter⟩ =
      if n = 0 then some ⟨0, .targetGap⟩ else none := by
  simp [octagonBaseCorridorLetterStep,
    octagonCorridorReflectionStep,
    octagonCorridorReflectionLeftBridge,
    octagonCorridorReflectionRightBridge,
    OctagonCorridorBridge.mk.injEq]

@[simp] private lemma octagonCone1Step_targetGap
    (x : OctagonBaseFactorGroup .cone1) (n : ℤ) :
    octagonBaseCorridorLetterStep ⟨.cone1, x⟩
        ⟨n, .targetGap⟩ =
      if n = -1 then some ⟨0, .targetCenter⟩ else none := by
  simp [octagonBaseCorridorLetterStep,
    octagonCorridorReflectionStep,
    octagonCorridorReflectionLeftBridge,
    octagonCorridorReflectionRightBridge,
    OctagonCorridorBridge.mk.injEq]

@[simp] private lemma octagonCone4Step_targetGap
    (x : OctagonBaseFactorGroup .cone4) (n : ℤ) :
    octagonBaseCorridorLetterStep ⟨.cone4, x⟩
        ⟨n, .targetGap⟩ =
      if n = 0 then some ⟨0, .targetCenter⟩ else none := by
  simp [octagonBaseCorridorLetterStep,
    octagonCorridorReflectionStep,
    octagonCorridorReflectionLeftBridge,
    octagonCorridorReflectionRightBridge,
    OctagonCorridorBridge.mk.injEq]

@[simp] private lemma octagonCone2Step_target
    (x : OctagonBaseFactorGroup .cone2) (n : ℤ)
    (gap : Bool) :
    octagonBaseCorridorLetterStep ⟨.cone2, x⟩
        ⟨n, if gap then .targetGap else .targetCenter⟩ = none := by
  cases gap <;> simp [octagonBaseCorridorLetterStep,
    octagonCorridorReflectionStep,
    octagonCorridorReflectionLeftBridge,
    octagonCorridorReflectionRightBridge]

@[simp] private lemma octagonCone3Step_target
    (x : OctagonBaseFactorGroup .cone3) (n : ℤ)
    (gap : Bool) :
    octagonBaseCorridorLetterStep ⟨.cone3, x⟩
        ⟨n, if gap then .targetGap else .targetCenter⟩ = none := by
  cases gap <;> simp [octagonBaseCorridorLetterStep,
    octagonCorridorReflectionStep,
    octagonCorridorReflectionLeftBridge,
    octagonCorridorReflectionRightBridge]

@[simp] private lemma octagonCone2Step_targetCenter
    (x : OctagonBaseFactorGroup .cone2) (n : ℤ) :
    octagonBaseCorridorLetterStep ⟨.cone2, x⟩
      ⟨n, .targetCenter⟩ = none := by
  simpa using octagonCone2Step_target x n false

@[simp] private lemma octagonCone2Step_targetGap
    (x : OctagonBaseFactorGroup .cone2) (n : ℤ) :
    octagonBaseCorridorLetterStep ⟨.cone2, x⟩
      ⟨n, .targetGap⟩ = none := by
  simpa using octagonCone2Step_target x n true

@[simp] private lemma octagonCone3Step_targetCenter
    (x : OctagonBaseFactorGroup .cone3) (n : ℤ) :
    octagonBaseCorridorLetterStep ⟨.cone3, x⟩
      ⟨n, .targetCenter⟩ = none := by
  simpa using octagonCone3Step_target x n false

@[simp] private lemma octagonCone3Step_targetGap
    (x : OctagonBaseFactorGroup .cone3) (n : ℤ) :
    octagonBaseCorridorLetterStep ⟨.cone3, x⟩
      ⟨n, .targetGap⟩ = none := by
  simpa using octagonCone3Step_target x n true

@[simp] private lemma octagonTargetForwardCycle_path :
    octagonBaseCorridorPath octagonTargetForwardCycle
        ⟨0, .targetCenter⟩ = some ⟨0, .targetCenter⟩ := by
  simp [octagonTargetForwardCycle, octagonBaseCorridorPath,
    octagonConeCorridorLetter]

@[simp] private lemma octagonTargetBackwardCycle_path :
    octagonBaseCorridorPath octagonTargetBackwardCycle
        ⟨0, .targetCenter⟩ = some ⟨0, .targetCenter⟩ := by
  simp [octagonTargetBackwardCycle, octagonBaseCorridorPath,
    octagonConeCorridorLetter]

private lemma octagonTargetCorridor_suffix
    (w : List OctagonBaseCorridorLetter)
    (hreduced : OctagonBaseCorridorReduced w)
    (hpath : octagonBaseCorridorPath w ⟨0, .targetCenter⟩ =
      some ⟨0, .targetCenter⟩) :
    w = [] ∨ ∃ v,
      OctagonBaseCorridorReduced v ∧
      octagonBaseCorridorPath v ⟨0, .targetCenter⟩ =
        some ⟨0, .targetCenter⟩ ∧
      (w = v ++ octagonTargetForwardCycle ∨
        w = v ++ octagonTargetBackwardCycle) := by
  have hrevReduced := hreduced.reverse
  generalize hrev : w.reverse = rev at hrevReduced
  cases rev with
  | nil =>
      left
      simpa using congrArg List.reverse hrev
  | cons l₁ rest =>
      have hw₁ : w = rest.reverse ++ [l₁] := by
        calc
          w = w.reverse.reverse := by simp
          _ = (l₁ :: rest).reverse := by rw [hrev]
          _ = rest.reverse ++ [l₁] := List.reverse_cons
      have hl₁ne : l₁.2 ≠ 1 :=
        hrevReduced.1 l₁ (by simp)
      rcases l₁ with ⟨i₁, x₁⟩
      cases i₁ with
      | handle =>
          have hk₁ := octagonBaseReducedHandleLetter_weight_ne_zero x₁ hl₁ne
          cases rest with
          | nil =>
              rw [hw₁, octagonBaseCorridorPath_append] at hpath
              simp [octagonBaseCorridorPath, hk₁] at hpath
          | cons l₂ rest₂ =>
              have hfac₁₂ : OctagonBaseFactor.handle ≠ l₂.1 :=
                (List.isChain_cons_cons.mp hrevReduced.2).1
              have hw₂ : w = rest₂.reverse ++ [l₂, ⟨.handle, x₁⟩] := by
                simpa [List.append_assoc] using hw₁
              rcases l₂ with ⟨i₂, x₂⟩
              cases i₂ with
              | handle => exact (hfac₁₂ rfl).elim
              | cone2 =>
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath] at hpath
              | cone1 =>
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath, hk₁] at hpath
              | cone4 =>
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath, hk₁] at hpath
              | cone3 =>
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath] at hpath
      | cone2 =>
          rw [hw₁, octagonBaseCorridorPath_append] at hpath
          simp [octagonBaseCorridorPath] at hpath
      | cone3 =>
          rw [hw₁, octagonBaseCorridorPath_append] at hpath
          simp [octagonBaseCorridorPath] at hpath
      | cone4 =>
          cases rest with
          | nil =>
              rw [hw₁, octagonBaseCorridorPath_append] at hpath
              simp [octagonBaseCorridorPath] at hpath
          | cons l₂ rest₂ =>
              have hfac₁₂ : OctagonBaseFactor.cone4 ≠ l₂.1 :=
                (List.isChain_cons_cons.mp hrevReduced.2).1
              rcases l₂ with ⟨i₂, x₂⟩
              have hl₂ne : x₂ ≠ 1 :=
                hrevReduced.1 ⟨i₂, x₂⟩ (by simp)
              cases i₂ with
              | cone2 =>
                  have hw₂ : w = rest₂.reverse ++
                      [⟨.cone2, x₂⟩, ⟨.cone4, x₁⟩] := by
                    simpa [List.append_assoc] using hw₁
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath] at hpath
              | cone1 =>
                  have hw₂ : w = rest₂.reverse ++
                      [⟨.cone1, x₂⟩, ⟨.cone4, x₁⟩] := by
                    simpa [List.append_assoc] using hw₁
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath] at hpath
              | cone4 => exact (hfac₁₂ rfl).elim
              | cone3 =>
                  have hw₂ : w = rest₂.reverse ++
                      [⟨.cone3, x₂⟩, ⟨.cone4, x₁⟩] := by
                    simpa [List.append_assoc] using hw₁
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath] at hpath
              | handle =>
                  have hk₂ :=
                    octagonBaseReducedHandleLetter_weight_ne_zero x₂ hl₂ne
                  cases rest₂ with
                  | nil =>
                      have hw₂ : w =
                          [⟨.handle, x₂⟩, ⟨.cone4, x₁⟩] := by
                        simpa using hw₁
                      rw [hw₂] at hpath
                      simp [octagonBaseCorridorPath] at hpath
                  | cons l₃ rest₃ =>
                      have hfac₂₃ : OctagonBaseFactor.handle ≠ l₃.1 :=
                        (List.isChain_cons_cons.mp hrevReduced.2.tail).1
                      rcases l₃ with ⟨i₃, x₃⟩
                      have hl₃ne : x₃ ≠ 1 :=
                        hrevReduced.1 ⟨i₃, x₃⟩ (by simp)
                      cases i₃ with
                      | handle => exact (hfac₂₃ rfl).elim
                      | cone2 =>
                          have hw₃ : w = rest₃.reverse ++
                              [⟨.cone2, x₃⟩, ⟨.handle, x₂⟩,
                                ⟨.cone4, x₁⟩] := by
                            simpa [List.append_assoc] using hw₁
                          rw [hw₃, octagonBaseCorridorPath_append] at hpath
                          simp [octagonBaseCorridorPath] at hpath
                      | cone4 =>
                          have hw₃ : w = rest₃.reverse ++
                              [⟨.cone4, x₃⟩, ⟨.handle, x₂⟩,
                                ⟨.cone4, x₁⟩] := by
                            simpa [List.append_assoc] using hw₁
                          rw [hw₃, octagonBaseCorridorPath_append] at hpath
                          simp [octagonBaseCorridorPath, hk₂] at hpath
                      | cone3 =>
                          have hw₃ : w = rest₃.reverse ++
                              [⟨.cone3, x₃⟩, ⟨.handle, x₂⟩,
                                ⟨.cone4, x₁⟩] := by
                            simpa [List.append_assoc] using hw₁
                          rw [hw₃, octagonBaseCorridorPath_append] at hpath
                          simp [octagonBaseCorridorPath] at hpath
                      | cone1 =>
                          have hw₃ : w = rest₃.reverse ++
                              [⟨.cone1, x₃⟩, ⟨.handle, x₂⟩,
                                ⟨.cone4, x₁⟩] := by
                            simpa [List.append_assoc] using hw₁
                          have hk : octagonBaseReducedLetterWeight
                              (⟨.handle, x₂⟩ : OctagonBaseCorridorLetter) = -1 := by
                            by_contra hk
                            rw [hw₃, octagonBaseCorridorPath_append] at hpath
                            simp [octagonBaseCorridorPath, hk] at hpath
                          have hl₁ := octagonBaseConeSyllable_eq_corridorLetter
                            (i := .cone4) (by intro h; cases h) x₁ hl₁ne
                          have hl₂ := octagonBaseHandleSyllable_eq_corridorLetter x₂
                          rw [hk] at hl₂
                          have hl₃ := octagonBaseConeSyllable_eq_corridorLetter
                            (i := .cone1) (by intro h; cases h) x₃ hl₃ne
                          rw [hl₁, hl₂, hl₃] at hw₃
                          right
                          refine ⟨rest₃.reverse, ?_, ?_, Or.inl ?_⟩
                          · rw [hw₃] at hreduced
                            exact hreduced.left_of_append
                          · rw [hw₃, octagonBaseCorridorPath_append] at hpath
                            change (octagonBaseCorridorPath
                              octagonTargetForwardCycle
                              ⟨0, .targetCenter⟩).bind
                                (octagonBaseCorridorPath rest₃.reverse) =
                              some ⟨0, .targetCenter⟩ at hpath
                            rw [octagonTargetForwardCycle_path] at hpath
                            exact hpath
                          · simpa [octagonTargetForwardCycle] using hw₃
      | cone1 =>
          cases rest with
          | nil =>
              rw [hw₁, octagonBaseCorridorPath_append] at hpath
              simp [octagonBaseCorridorPath] at hpath
          | cons l₂ rest₂ =>
              have hfac₁₂ : OctagonBaseFactor.cone1 ≠ l₂.1 :=
                (List.isChain_cons_cons.mp hrevReduced.2).1
              rcases l₂ with ⟨i₂, x₂⟩
              have hl₂ne : x₂ ≠ 1 :=
                hrevReduced.1 ⟨i₂, x₂⟩ (by simp)
              cases i₂ with
              | cone2 =>
                  have hw₂ : w = rest₂.reverse ++
                      [⟨.cone2, x₂⟩, ⟨.cone1, x₁⟩] := by
                    simpa [List.append_assoc] using hw₁
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath] at hpath
              | cone1 => exact (hfac₁₂ rfl).elim
              | cone4 =>
                  have hw₂ : w = rest₂.reverse ++
                      [⟨.cone4, x₂⟩, ⟨.cone1, x₁⟩] := by
                    simpa [List.append_assoc] using hw₁
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath] at hpath
              | cone3 =>
                  have hw₂ : w = rest₂.reverse ++
                      [⟨.cone3, x₂⟩, ⟨.cone1, x₁⟩] := by
                    simpa [List.append_assoc] using hw₁
                  rw [hw₂, octagonBaseCorridorPath_append] at hpath
                  simp [octagonBaseCorridorPath] at hpath
              | handle =>
                  have hk₂ :=
                    octagonBaseReducedHandleLetter_weight_ne_zero x₂ hl₂ne
                  cases rest₂ with
                  | nil =>
                      have hw₂ : w =
                          [⟨.handle, x₂⟩, ⟨.cone1, x₁⟩] := by
                        simpa using hw₁
                      rw [hw₂] at hpath
                      simp [octagonBaseCorridorPath] at hpath
                  | cons l₃ rest₃ =>
                      have hfac₂₃ : OctagonBaseFactor.handle ≠ l₃.1 :=
                        (List.isChain_cons_cons.mp hrevReduced.2.tail).1
                      rcases l₃ with ⟨i₃, x₃⟩
                      have hl₃ne : x₃ ≠ 1 :=
                        hrevReduced.1 ⟨i₃, x₃⟩ (by simp)
                      cases i₃ with
                      | handle => exact (hfac₂₃ rfl).elim
                      | cone2 =>
                          have hw₃ : w = rest₃.reverse ++
                              [⟨.cone2, x₃⟩, ⟨.handle, x₂⟩,
                                ⟨.cone1, x₁⟩] := by
                            simpa [List.append_assoc] using hw₁
                          rw [hw₃, octagonBaseCorridorPath_append] at hpath
                          simp [octagonBaseCorridorPath] at hpath
                      | cone1 =>
                          have hw₃ : w = rest₃.reverse ++
                              [⟨.cone1, x₃⟩, ⟨.handle, x₂⟩,
                                ⟨.cone1, x₁⟩] := by
                            simpa [List.append_assoc] using hw₁
                          rw [hw₃, octagonBaseCorridorPath_append] at hpath
                          simp [octagonBaseCorridorPath, hk₂] at hpath
                      | cone3 =>
                          have hw₃ : w = rest₃.reverse ++
                              [⟨.cone3, x₃⟩, ⟨.handle, x₂⟩,
                                ⟨.cone1, x₁⟩] := by
                            simpa [List.append_assoc] using hw₁
                          rw [hw₃, octagonBaseCorridorPath_append] at hpath
                          simp [octagonBaseCorridorPath] at hpath
                      | cone4 =>
                          have hw₃ : w = rest₃.reverse ++
                              [⟨.cone4, x₃⟩, ⟨.handle, x₂⟩,
                                ⟨.cone1, x₁⟩] := by
                            simpa [List.append_assoc] using hw₁
                          have hk : octagonBaseReducedLetterWeight
                              (⟨.handle, x₂⟩ : OctagonBaseCorridorLetter) = 1 := by
                            by_contra hk
                            have hk' : octagonBaseReducedLetterWeight
                                (⟨.handle, x₂⟩ : OctagonBaseCorridorLetter) +
                                  (-1) ≠ 0 := by omega
                            rw [hw₃, octagonBaseCorridorPath_append] at hpath
                            simp [octagonBaseCorridorPath, hk'] at hpath
                          have hl₁ := octagonBaseConeSyllable_eq_corridorLetter
                            (i := .cone1) (by intro h; cases h) x₁ hl₁ne
                          have hl₂ := octagonBaseHandleSyllable_eq_corridorLetter x₂
                          rw [hk] at hl₂
                          have hl₃ := octagonBaseConeSyllable_eq_corridorLetter
                            (i := .cone4) (by intro h; cases h) x₃ hl₃ne
                          rw [hl₁, hl₂, hl₃] at hw₃
                          right
                          refine ⟨rest₃.reverse, ?_, ?_, Or.inr ?_⟩
                          · rw [hw₃] at hreduced
                            exact hreduced.left_of_append
                          · rw [hw₃, octagonBaseCorridorPath_append] at hpath
                            change (octagonBaseCorridorPath
                              octagonTargetBackwardCycle
                              ⟨0, .targetCenter⟩).bind
                                (octagonBaseCorridorPath rest₃.reverse) =
                              some ⟨0, .targetCenter⟩ at hpath
                            rw [octagonTargetBackwardCycle_path] at hpath
                            exact hpath
                          · simpa [octagonTargetBackwardCycle] using hw₃

private lemma octagonTargetBackward_append_forward_not_reduced
    (n : ℕ) (hn : n ≠ 0) :
    ¬ OctagonBaseCorridorReduced
      (FiniteStatePingPong.cycleRepeat octagonTargetBackwardCycle n ++
        octagonTargetForwardCycle) := by
  intro h
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
      have hboundary := (List.isChain_append.mp h.2).2.2
      have hbad := hboundary
        (octagonConeCorridorLetter .cone1)
        (by simp [FiniteStatePingPong.cycleRepeat_succ,
          octagonTargetBackwardCycle])
        (octagonConeCorridorLetter .cone1)
        (by simp [octagonTargetForwardCycle])
      exact hbad rfl

private lemma octagonTargetForward_append_backward_not_reduced
    (n : ℕ) (hn : n ≠ 0) :
    ¬ OctagonBaseCorridorReduced
      (FiniteStatePingPong.cycleRepeat octagonTargetForwardCycle n ++
        octagonTargetBackwardCycle) := by
  intro h
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
      have hboundary := (List.isChain_append.mp h.2).2.2
      have hbad := hboundary
        (octagonConeCorridorLetter .cone4)
        (by simp [FiniteStatePingPong.cycleRepeat_succ,
          octagonTargetForwardCycle])
        (octagonConeCorridorLetter .cone4)
        (by simp [octagonTargetBackwardCycle])
      exact hbad rfl

/-- Every reduced direct target loop consists entirely of forward cycles or
entirely of backward cycles. -/
theorem octagonTargetCorridorPath_classification
    (w : List OctagonBaseCorridorLetter)
    (hreduced : OctagonBaseCorridorReduced w)
    (hpath : octagonBaseCorridorPath w ⟨0, .targetCenter⟩ =
      some ⟨0, .targetCenter⟩) :
    w = [] ∨ OctagonTargetForwardCorridor w ∨
      OctagonTargetBackwardCorridor w := by
  rcases octagonTargetCorridor_suffix w hreduced hpath with
    hnil | ⟨v, hvred, hvpath, hforward | hbackward⟩
  · exact Or.inl hnil
  · rcases octagonTargetCorridorPath_classification v hvred hvpath with
      hvnil | hvforward | hvbackward
    · subst v
      right
      left
      refine ⟨1, ?_⟩
      simpa [FiniteStatePingPong.cycleRepeat_succ] using hforward
    · obtain ⟨n, hn⟩ := hvforward
      right
      left
      refine ⟨n + 1, ?_⟩
      rw [hforward, hn]
      exact (FiniteStatePingPong.cycleRepeat_succ
        octagonTargetForwardCycle n).symm
    · obtain ⟨n, hn⟩ := hvbackward
      by_cases hn0 : n = 0
      · subst n
        simp at hn
        subst v
        right
        left
        refine ⟨1, ?_⟩
        simpa [FiniteStatePingPong.cycleRepeat_succ] using hforward
      · exfalso
        apply octagonTargetBackward_append_forward_not_reduced n hn0
        rw [← hn, ← hforward]
        exact hreduced
  · rcases octagonTargetCorridorPath_classification v hvred hvpath with
      hvnil | hvforward | hvbackward
    · subst v
      right
      right
      refine ⟨1, ?_⟩
      simpa [FiniteStatePingPong.cycleRepeat_succ] using hbackward
    · obtain ⟨n, hn⟩ := hvforward
      by_cases hn0 : n = 0
      · subst n
        simp at hn
        subst v
        right
        right
        refine ⟨1, ?_⟩
        simpa [FiniteStatePingPong.cycleRepeat_succ] using hbackward
      · exfalso
        apply octagonTargetForward_append_backward_not_reduced n hn0
        rw [← hn, ← hbackward]
        exact hreduced
    · obtain ⟨n, hn⟩ := hvbackward
      right
      right
      refine ⟨n + 1, ?_⟩
      rw [hbackward, hn]
      exact (FiniteStatePingPong.cycleRepeat_succ
        octagonTargetBackwardCycle n).symm
termination_by w.length
decreasing_by
  · rw [hforward]
    simp [octagonTargetForwardCycle]
  · rw [hbackward]
    simp [octagonTargetBackwardCycle]

/-- A reduced word whose action overlaps the source boundary with itself is
one of the two source corridor orientations. -/
theorem octagonHNNBaseCorridor_source_self
    (w : List OctagonBaseCorridorLetter)
    (hreduced : OctagonBaseCorridorReduced w)
    (hoverlap : octagonBoundaryCorridorOverlap
      octagonHNNSourceBoundarySet octagonHNNSourceBoundarySet w) :
    w = [] ∨ OctagonSourceForwardCorridor w ∨
      OctagonSourceBackwardCorridor w := by
  apply octagonSourceCorridorPath_classification w hreduced
  apply octagonBaseCorridorPath_eq_of_overlap w hreduced
  simpa [octagonBoundaryCorridorOverlap,
    octagonSourceCenterBridgeSet] using hoverlap

/-- A reduced word whose action overlaps the target boundary with itself is
one of the two target corridor orientations. -/
theorem octagonHNNBaseCorridor_target_self
    (w : List OctagonBaseCorridorLetter)
    (hreduced : OctagonBaseCorridorReduced w)
    (hoverlap : octagonBoundaryCorridorOverlap
      octagonHNNTargetBoundarySet octagonHNNTargetBoundarySet w) :
    w = [] ∨ OctagonTargetForwardCorridor w ∨
      OctagonTargetBackwardCorridor w := by
  apply octagonTargetCorridorPath_classification w hreduced
  apply octagonBaseCorridorPath_eq_of_overlap w hreduced
  simpa [octagonBoundaryCorridorOverlap,
    octagonTargetCenterBridgeSet] using hoverlap

/-- The concrete octagon bridge geometry supplies all four cases required by
the HNN base-corridor interface. -/
theorem octagonHNNBaseCorridorClassification :
    OctagonHNNBaseCorridorClassification where
  source_target := octagonHNNBaseCorridor_source_target
  target_source := octagonHNNBaseCorridor_target_source
  source_self := octagonHNNBaseCorridor_source_self
  target_self := octagonHNNBaseCorridor_target_self

/-- The octagon HNN representation is faithful, with no geometric
separation assumptions remaining. -/
theorem octagonHNNToPGL23_injective :
    Function.Injective octagonHNNToPGL23 :=
  octagonHNNToPGL23_injective_of_corridorClassification
    octagonHNNBaseCorridorClassification

/-- The induced projective octagon representation is faithful. -/
theorem projectiveOctagonToPGL23_injective :
    Function.Injective projectiveOctagonToPGL23 :=
  projectiveOctagonToPGL23_injective_of_corridorClassification
    octagonHNNBaseCorridorClassification

/-- The lifted integral quaternion representation is faithful. -/
theorem liftedOctagonToQuaternion_injective :
    Function.Injective liftedOctagonToQuaternion :=
  liftedOctagonToQuaternion_injective_of_corridorClassification
    octagonHNNBaseCorridorClassification


end

end SystolicGrowth
