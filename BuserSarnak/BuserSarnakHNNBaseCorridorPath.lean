module

public import BuserSarnak.BuserSarnakHNNBaseCorridorAutomaton

@[expose] public section

/-!
# Reduced paths in the octagon corridor automaton

This file turns the geometric bridge/reflection data into a deterministic
right-to-left path computation.  A reduced reflection word either follows
the corridor exactly or sends its initial bridge into the ping-pong domain
of its leftmost reflection.
-/

open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise

namespace SystolicGrowth

noncomputable section

/-- The partial bridge transition across one corridor reflection. -/
def octagonCorridorReflectionStep
    (r : OctagonCorridorReflection) (b : OctagonCorridorBridge) :
    Option OctagonCorridorBridge :=
  if b = octagonCorridorReflectionLeftBridge r then
    some (octagonCorridorReflectionRightBridge r)
  else if b = octagonCorridorReflectionRightBridge r then
    some (octagonCorridorReflectionLeftBridge r)
  else none

/-- Run a reflection word in the right-to-left order of its group action. -/
def octagonCorridorReflectionPath :
    List OctagonCorridorReflection → OctagonCorridorBridge →
      Option OctagonCorridorBridge
  | [], b => some b
  | r :: rs, b => (octagonCorridorReflectionPath rs b).bind
      (octagonCorridorReflectionStep r)

/-- Evaluate a word of conjugated cone reflections in `PGL(2,ℝ)`. -/
abbrev octagonCorridorReflectionEval
    (rs : List OctagonCorridorReflection) : PGL(2, ℝ) :=
  FiniteStatePingPong.eval octagonCorridorReflectionPGL rs

private lemma octagonCorridorReflectionLeftBridge_ne_rightBridge
    (r : OctagonCorridorReflection) :
    octagonCorridorReflectionLeftBridge r ≠
      octagonCorridorReflectionRightBridge r := by
  rcases r with ⟨n, c⟩
  cases c <;>
    simp [octagonCorridorReflectionLeftBridge,
      octagonCorridorReflectionRightBridge]

lemma octagonCorridorReflectionStep_eq_none_iff
    (r : OctagonCorridorReflection) (b : OctagonCorridorBridge) :
    octagonCorridorReflectionStep r b = none ↔
      ¬ OctagonCorridorIncident r b := by
  simp only [octagonCorridorReflectionStep, OctagonCorridorIncident]
  by_cases hl : b = octagonCorridorReflectionLeftBridge r
  · simp [hl]
  · by_cases hr : b = octagonCorridorReflectionRightBridge r
    · simp [hr,
        (octagonCorridorReflectionLeftBridge_ne_rightBridge r).symm]
    · simp [hl, hr]

lemma octagonCorridorReflectionStep_smul
    {r : OctagonCorridorReflection} {b c : OctagonCorridorBridge}
    (hstep : octagonCorridorReflectionStep r b = some c) :
    octagonCorridorReflectionPGL r • octagonCorridorBridgeSet b =
      octagonCorridorBridgeSet c := by
  simp only [octagonCorridorReflectionStep] at hstep
  by_cases hl : b = octagonCorridorReflectionLeftBridge r
  · rw [if_pos hl] at hstep
    cases hstep
    rw [hl]
    exact octagonCorridorReflectionPGL_smul_leftBridge r
  · rw [if_neg hl] at hstep
    by_cases hr : b = octagonCorridorReflectionRightBridge r
    · rw [if_pos hr] at hstep
      cases hstep
      rw [hr]
      exact octagonCorridorReflectionPGL_smul_rightBridge r
    · rw [if_neg hr] at hstep
      contradiction

lemma octagonCorridorReflectionStep_symm
    {r : OctagonCorridorReflection} {b c : OctagonCorridorBridge}
    (hstep : octagonCorridorReflectionStep r b = some c) :
    octagonCorridorReflectionStep r c = some b := by
  simp only [octagonCorridorReflectionStep] at hstep ⊢
  by_cases hl : b = octagonCorridorReflectionLeftBridge r
  · rw [if_pos hl] at hstep
    cases hstep
    rw [if_neg
      (octagonCorridorReflectionLeftBridge_ne_rightBridge r).symm,
      if_pos rfl, hl]
  · rw [if_neg hl] at hstep
    by_cases hr : b = octagonCorridorReflectionRightBridge r
    · rw [if_pos hr] at hstep
      cases hstep
      rw [if_pos rfl, hr]
    · rw [if_neg hr] at hstep
      contradiction

/-- Adjacent reflections in a reduced reflection word are distinct. -/
def OctagonCorridorReflectionReduced
    (rs : List OctagonCorridorReflection) : Prop :=
  rs.IsChain fun r s => r ≠ s

/-- A reduced reflection word either follows an exact bridge path, or is
trapped in the domain of its leftmost reflection. -/
theorem octagonCorridorReflectionPath_or_mapsTo_domain
    (rs : List OctagonCorridorReflection)
    (hreduced : OctagonCorridorReflectionReduced rs)
    (b : OctagonCorridorBridge) :
    (∃ c, octagonCorridorReflectionPath rs b = some c ∧
      octagonCorridorReflectionEval rs • octagonCorridorBridgeSet b =
        octagonCorridorBridgeSet c) ∨
    (octagonCorridorReflectionPath rs b = none ∧
      ∃ r tail, rs = r :: tail ∧
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary =>
            octagonCorridorReflectionEval rs • p)
          (octagonCorridorBridgeSet b)
          (octagonCorridorReflectionDomain r)) := by
  induction rs with
  | nil =>
      left
      exact ⟨b, rfl, by simp [octagonCorridorReflectionEval]⟩
  | cons r rs ih =>
      have htail : OctagonCorridorReflectionReduced rs :=
        hreduced.tail
      rcases ih htail with hexact | htrapped
      · obtain ⟨c, hpath, heval⟩ := hexact
        by_cases hnone : octagonCorridorReflectionStep r c = none
        · right
          constructor
          · simp [octagonCorridorReflectionPath, hpath, hnone]
          · refine ⟨r, rs, rfl, ?_⟩
            intro p hp
            have htailImage :
                octagonCorridorReflectionEval rs • p ∈
                  octagonCorridorBridgeSet c := by
              rw [← heval]
              exact Set.smul_mem_smul_set hp
            have hnonincident : ¬ OctagonCorridorIncident r c :=
              (octagonCorridorReflectionStep_eq_none_iff r c).mp hnone
            have hdisjoint :=
              octagonCorridorReflectionDomain_disjoint_nonincident
                r c hnonincident
            have hcompl : octagonCorridorReflectionEval rs • p ∈
                (octagonCorridorReflectionDomain r)ᶜ := by
              rw [Set.mem_compl_iff]
              intro hdomain
              exact Set.disjoint_left.mp hdisjoint hdomain htailImage
            simpa [octagonCorridorReflectionEval, mul_smul] using
              (octagonCorridorReflectionPGL_maps_compl_domain r hcompl)
        · obtain ⟨d, hstep⟩ : ∃ d,
              octagonCorridorReflectionStep r c = some d := by
            cases hs : octagonCorridorReflectionStep r c with
            | none => exact (hnone hs).elim
            | some d => exact ⟨d, rfl⟩
          left
          refine ⟨d, ?_, ?_⟩
          · simp [octagonCorridorReflectionPath, hpath, hstep]
          · simp only [octagonCorridorReflectionEval,
              FiniteStatePingPong.eval_cons, mul_smul]
            rw [heval,
              octagonCorridorReflectionStep_smul hstep]
      · obtain ⟨hpath, q, tail, hrs, hmaps⟩ := htrapped
        cases hrs
        right
        constructor
        · change (octagonCorridorReflectionPath (q :: tail) b).bind
              (octagonCorridorReflectionStep r) = none
          rw [hpath]
          rfl
        · refine ⟨r, q :: tail, rfl, ?_⟩
          have hrq : r ≠ q := by
            exact (List.isChain_cons_cons.mp hreduced).1
          have hdisjoint :=
            octagonCorridorReflectionDomain_pairwise_disjoint hrq
          intro p hp
          have hqdomain := hmaps hp
          have hcompl :
              octagonCorridorReflectionEval (q :: tail) • p ∈
                (octagonCorridorReflectionDomain r)ᶜ := by
            rw [Set.mem_compl_iff]
            intro hrdomain
            exact Set.disjoint_left.mp hdisjoint hrdomain hqdomain
          simpa [octagonCorridorReflectionEval, mul_smul] using
            (octagonCorridorReflectionPGL_maps_compl_domain r hcompl)

/-- A bridge-to-bridge overlap of a reduced reflection word forces the
deterministic corridor path to end at the observed bridge. -/
theorem octagonCorridorReflectionPath_eq_of_overlap
    (rs : List OctagonCorridorReflection)
    (hreduced : OctagonCorridorReflectionReduced rs)
    (b c : OctagonCorridorBridge)
    (hoverlap : ∃ p ∈ octagonCorridorBridgeSet b,
      octagonCorridorReflectionEval rs • p ∈
        octagonCorridorBridgeSet c) :
    octagonCorridorReflectionPath rs b = some c := by
  induction rs generalizing c with
  | nil =>
      obtain ⟨p, hpb, hpc⟩ := hoverlap
      simp only [octagonCorridorReflectionEval,
        FiniteStatePingPong.eval_nil, one_smul] at hpc
      have hbc : b = c := by
        by_contra hne
        exact Set.disjoint_left.mp
          (octagonCorridorBridgeSet_pairwise_disjoint hne) hpb hpc
      subst c
      rfl
  | cons r rs ih =>
      have htail : OctagonCorridorReflectionReduced rs :=
        hreduced.tail
      by_cases hincident : OctagonCorridorIncident r c
      · have hnotnone : octagonCorridorReflectionStep r c ≠ none := by
          intro hnone
          exact ((octagonCorridorReflectionStep_eq_none_iff r c).mp hnone)
            hincident
        obtain ⟨d, hstep⟩ : ∃ d,
            octagonCorridorReflectionStep r c = some d := by
          cases hs : octagonCorridorReflectionStep r c with
          | none => exact (hnotnone hs).elim
          | some d => exact ⟨d, rfl⟩
        obtain ⟨p, hpb, hpc⟩ := hoverlap
        have hpc' := Set.smul_mem_smul_set
          (a := octagonCorridorReflectionPGL r) hpc
        have hsmul := octagonCorridorReflectionStep_smul hstep
        have htailImage : octagonCorridorReflectionEval rs • p ∈
            octagonCorridorBridgeSet d := by
          simp only [octagonCorridorReflectionEval,
            FiniteStatePingPong.eval_cons, mul_smul] at hpc'
          rw [← mul_smul, octagonCorridorReflectionPGL_sq,
            one_smul, hsmul] at hpc'
          exact hpc'
        have htailPath := ih htail d ⟨p, hpb, htailImage⟩
        have hback := octagonCorridorReflectionStep_symm hstep
        simp [octagonCorridorReflectionPath, htailPath, hback]
      · rcases octagonCorridorReflectionPath_or_mapsTo_domain
          (r :: rs) hreduced b with hexact | htrapped
        · obtain ⟨d, hpath, heval⟩ := hexact
          obtain ⟨p, hpb, hpc⟩ := hoverlap
          have hpd : octagonCorridorReflectionEval (r :: rs) • p ∈
              octagonCorridorBridgeSet d := by
            rw [← heval]
            exact Set.smul_mem_smul_set hpb
          have hdc : d = c := by
            by_contra hne
            exact Set.disjoint_left.mp
              (octagonCorridorBridgeSet_pairwise_disjoint hne) hpd hpc
          simpa [hdc] using hpath
        · obtain ⟨_, q, tail, hrs, hmaps⟩ := htrapped
          cases hrs
          obtain ⟨p, hpb, hpc⟩ := hoverlap
          have hpdomain := hmaps hpb
          exact (Set.disjoint_left.mp
            (octagonCorridorReflectionDomain_disjoint_nonincident
              r c hincident) hpdomain hpc).elim

end

end SystolicGrowth
