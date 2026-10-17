module

public import BuserSarnak.BuserSarnakHNNBaseCorridorPath

@[expose] public section

/-!
# Normalizing octagon base words into corridor reflections

A free-product word is rewritten as a product of handle-conjugated cone
reflections followed by one terminal handle power.  This is the bridge from
canonical base words to the geometric corridor path engine.
-/

open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise

namespace SystolicGrowth

noncomputable section

local instance : DecidableEq OctagonBaseFactor := Classical.decEq _
local instance (i : OctagonBaseFactor) :
    DecidableEq (OctagonBaseFactorGroup i) := Classical.decEq _

/-- Translate a conjugated reflection by a handle power. -/
def octagonCorridorReflectionShift (k : ℤ)
    (r : OctagonCorridorReflection) : OctagonCorridorReflection :=
  ⟨k + r.level, r.cone⟩

@[simp] lemma octagonCorridorReflectionShift_level
    (k : ℤ) (r : OctagonCorridorReflection) :
    (octagonCorridorReflectionShift k r).level = k + r.level := rfl

@[simp] lemma octagonCorridorReflectionShift_cone
    (k : ℤ) (r : OctagonCorridorReflection) :
    (octagonCorridorReflectionShift k r).cone = r.cone := rfl

lemma octagonCorridorReflectionPGL_shift
    (k : ℤ) (r : OctagonCorridorReflection) :
    octagonCorridorReflectionPGL (octagonCorridorReflectionShift k r) =
      (octagonBaseToPGL23 octagonBaseA) ^ k *
        octagonCorridorReflectionPGL r *
          (octagonBaseToPGL23 octagonBaseA) ^ (-k) := by
  rcases r with ⟨n, c⟩
  simp only [octagonCorridorReflectionShift,
    octagonCorridorReflectionPGL]
  rw [zpow_add]
  have hneg : -(k + n) = -n + -k := by omega
  rw [hneg, zpow_add]
  group

lemma octagonCorridorReflectionEval_map_shift
    (k : ℤ) (rs : List OctagonCorridorReflection) :
    octagonCorridorReflectionEval
        (rs.map (octagonCorridorReflectionShift k)) =
      (octagonBaseToPGL23 octagonBaseA) ^ k *
        octagonCorridorReflectionEval rs *
          (octagonBaseToPGL23 octagonBaseA) ^ (-k) := by
  induction rs with
  | nil =>
      simp [octagonCorridorReflectionEval]
  | cons r rs ih =>
      simp only [List.map_cons, octagonCorridorReflectionEval,
        FiniteStatePingPong.eval_cons]
      rw [octagonCorridorReflectionPGL_shift]
      have ih' :
          FiniteStatePingPong.eval octagonCorridorReflectionPGL
              (rs.map (octagonCorridorReflectionShift k)) =
            (octagonBaseToPGL23 octagonBaseA) ^ k *
              FiniteStatePingPong.eval octagonCorridorReflectionPGL rs *
                (octagonBaseToPGL23 octagonBaseA) ^ (-k) := ih
      rw [ih']
      group

private lemma octagonBaseReducedHandleLetter_value
    (x : OctagonBaseFactorGroup .handle) :
    octagonBaseReducedLetterValue
        (⟨.handle, x⟩ : OctagonBaseCorridorLetter) =
      octagonBaseA ^ octagonBaseReducedLetterWeight
        (⟨.handle, x⟩ : OctagonBaseCorridorLetter) := by
  rcases x with ⟨x, ⟨n, hn⟩⟩
  subst x
  change octagonBaseA ^ n = octagonBaseA ^
    Multiplicative.toAdd (octagonBaseExponent (octagonBaseA ^ n))
  rw [map_zpow]
  simp [octagonBaseA, octagonBaseExponentImage]

private lemma octagonBaseReducedConeLetter_value
    {i : OctagonBaseFactor} (hi : i ≠ .handle)
    (x : OctagonBaseFactorGroup i) (hx : x ≠ 1) :
    octagonBaseReducedLetterValue
        (⟨i, x⟩ : OctagonBaseCorridorLetter) =
      octagonBaseFactorElement i := by
  rcases x with ⟨x, ⟨n, hn⟩⟩
  subst x
  change octagonBaseFactorElement i ^ n = octagonBaseFactorElement i
  have hpow : octagonBaseFactorElement i ^ n ≠ 1 := by
    intro hpow
    apply hx
    apply Subtype.ext
    exact hpow
  cases i with
  | handle => exact (hi rfl).elim
  | cone1 =>
      exact zpow_eq_self_of_orderOf_eq_two
        (by simpa using orderOf_octagonBaseFactorElement .cone1) n hpow
  | cone2 =>
      exact zpow_eq_self_of_orderOf_eq_two
        (by simpa using orderOf_octagonBaseFactorElement .cone2) n hpow
  | cone3 =>
      exact zpow_eq_self_of_orderOf_eq_two
        (by simpa using orderOf_octagonBaseFactorElement .cone3) n hpow
  | cone4 =>
      exact zpow_eq_self_of_orderOf_eq_two
        (by simpa using orderOf_octagonBaseFactorElement .cone4) n hpow

private lemma octagonBaseReducedConeLetter_weight
    {i : OctagonBaseFactor} (hi : i ≠ .handle)
    (x : OctagonBaseFactorGroup i) :
    octagonBaseReducedLetterWeight
        (⟨i, x⟩ : OctagonBaseCorridorLetter) = 0 := by
  rcases x with ⟨x, ⟨n, hn⟩⟩
  subst x
  change Multiplicative.toAdd
      (octagonBaseExponent (octagonBaseFactorElement i ^ n)) = 0
  rw [map_zpow]
  cases i with
  | handle => exact (hi rfl).elim
  | cone1 => simp [octagonBaseFactorElement, octagonBaseE1,
      octagonBaseExponentImage]
  | cone2 => simp [octagonBaseFactorElement, octagonBaseE2,
      octagonBaseExponentImage]
  | cone3 => simp [octagonBaseFactorElement, octagonBaseE3,
      octagonBaseExponentImage]
  | cone4 => simp [octagonBaseFactorElement, octagonBaseE4,
      octagonBaseExponentImage]

/-- A reflection word together with its terminal handle exponent. -/
structure OctagonCorridorNormalForm where
  reflections : List OctagonCorridorReflection
  exponent : ℤ

/-- Normalize a dependent free-product word from right to left.  A leading
handle shifts every reflection already produced from the tail. -/
def octagonCorridorNormalize :
    List OctagonBaseCorridorLetter → OctagonCorridorNormalForm
  | [] => ⟨[], 0⟩
  | ⟨.handle, x⟩ :: w =>
      let N := octagonCorridorNormalize w
      let k := octagonBaseReducedLetterWeight
        (⟨.handle, x⟩ : OctagonBaseCorridorLetter)
      ⟨N.reflections.map (octagonCorridorReflectionShift k),
        k + N.exponent⟩
  | ⟨.cone1, _⟩ :: w =>
      let N := octagonCorridorNormalize w
      ⟨⟨0, .cone1⟩ :: N.reflections, N.exponent⟩
  | ⟨.cone2, _⟩ :: w =>
      let N := octagonCorridorNormalize w
      ⟨⟨0, .cone2⟩ :: N.reflections, N.exponent⟩
  | ⟨.cone3, _⟩ :: w =>
      let N := octagonCorridorNormalize w
      ⟨⟨0, .cone3⟩ :: N.reflections, N.exponent⟩
  | ⟨.cone4, _⟩ :: w =>
      let N := octagonCorridorNormalize w
      ⟨⟨0, .cone4⟩ :: N.reflections, N.exponent⟩

/-- The terminal handle exponent of the normal form is the additive weight
of the original free-product word. -/
lemma octagonCorridorNormalize_exponent
    (w : List OctagonBaseCorridorLetter) :
    (octagonCorridorNormalize w).exponent =
      FiniteStatePingPong.weight octagonBaseReducedLetterWeight w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
      rcases l with ⟨i, x⟩
      cases i with
      | handle =>
          simp only [octagonCorridorNormalize,
            FiniteStatePingPong.weight, List.map_cons, List.sum_cons]
          simpa [FiniteStatePingPong.weight] using
            congrArg (fun z =>
              octagonBaseReducedLetterWeight
                (⟨.handle, x⟩ : OctagonBaseCorridorLetter) + z) ih
      | cone1 =>
          simp only [octagonCorridorNormalize,
            FiniteStatePingPong.weight, List.map_cons, List.sum_cons]
          rw [octagonBaseReducedConeLetter_weight (by
            intro h; cases h)]
          simpa [FiniteStatePingPong.weight] using ih
      | cone2 =>
          simp only [octagonCorridorNormalize,
            FiniteStatePingPong.weight, List.map_cons, List.sum_cons]
          rw [octagonBaseReducedConeLetter_weight (by
            intro h; cases h)]
          simpa [FiniteStatePingPong.weight] using ih
      | cone3 =>
          simp only [octagonCorridorNormalize,
            FiniteStatePingPong.weight, List.map_cons, List.sum_cons]
          rw [octagonBaseReducedConeLetter_weight (by
            intro h; cases h)]
          simpa [FiniteStatePingPong.weight] using ih
      | cone4 =>
          simp only [octagonCorridorNormalize,
            FiniteStatePingPong.weight, List.map_cons, List.sum_cons]
          rw [octagonBaseReducedConeLetter_weight (by
            intro h; cases h)]
          simpa [FiniteStatePingPong.weight] using ih

/-- Projective evaluation is preserved by corridor normalization. -/
theorem octagonCorridorNormalize_eval
    (w : List OctagonBaseCorridorLetter)
    (hne : ∀ l ∈ w, l.2 ≠ 1) :
    FiniteStatePingPong.eval octagonBaseReducedLetterPGL w =
      octagonCorridorReflectionEval
          (octagonCorridorNormalize w).reflections *
        (octagonBaseToPGL23 octagonBaseA) ^
          (octagonCorridorNormalize w).exponent := by
  induction w with
  | nil =>
      simp [octagonCorridorNormalize, octagonCorridorReflectionEval]
  | cons l w ih =>
      have hl : l.2 ≠ 1 := hne l (by simp)
      have hw : ∀ q ∈ w, q.2 ≠ 1 := by
        intro q hq
        exact hne q (by simp [hq])
      rcases l with ⟨i, x⟩
      cases i with
      | handle =>
          simp only [FiniteStatePingPong.eval_cons,
            octagonBaseReducedLetterPGL,
            octagonCorridorNormalize]
          rw [octagonBaseReducedHandleLetter_value, map_zpow, ih hw,
            octagonCorridorReflectionEval_map_shift, zpow_add]
          group
      | cone1 =>
          simp only [FiniteStatePingPong.eval_cons,
            octagonBaseReducedLetterPGL,
            octagonCorridorNormalize,
            octagonCorridorReflectionEval,
            FiniteStatePingPong.eval_cons]
          rw [octagonBaseReducedConeLetter_value (by
            intro h; cases h) x hl, ih hw]
          simp [octagonCorridorReflectionPGL,
            OctagonCorridorCone.baseFactor]
          simp only [octagonCorridorReflectionEval]
          group
      | cone2 =>
          simp only [FiniteStatePingPong.eval_cons,
            octagonBaseReducedLetterPGL,
            octagonCorridorNormalize,
            octagonCorridorReflectionEval,
            FiniteStatePingPong.eval_cons]
          rw [octagonBaseReducedConeLetter_value (by
            intro h; cases h) x hl, ih hw]
          simp [octagonCorridorReflectionPGL,
            OctagonCorridorCone.baseFactor]
          simp only [octagonCorridorReflectionEval]
          group
      | cone3 =>
          simp only [FiniteStatePingPong.eval_cons,
            octagonBaseReducedLetterPGL,
            octagonCorridorNormalize,
            octagonCorridorReflectionEval,
            FiniteStatePingPong.eval_cons]
          rw [octagonBaseReducedConeLetter_value (by
            intro h; cases h) x hl, ih hw]
          simp [octagonCorridorReflectionPGL,
            OctagonCorridorCone.baseFactor]
          simp only [octagonCorridorReflectionEval]
          group
      | cone4 =>
          simp only [FiniteStatePingPong.eval_cons,
            octagonBaseReducedLetterPGL,
            octagonCorridorNormalize,
            octagonCorridorReflectionEval,
            FiniteStatePingPong.eval_cons]
          rw [octagonBaseReducedConeLetter_value (by
            intro h; cases h) x hl, ih hw]
          simp [octagonCorridorReflectionPGL,
            OctagonCorridorCone.baseFactor]
          simp only [octagonCorridorReflectionEval]
          group

lemma octagonBaseReducedHandleLetter_weight_ne_zero
    (x : OctagonBaseFactorGroup .handle) (hx : x ≠ 1) :
    octagonBaseReducedLetterWeight
        (⟨.handle, x⟩ : OctagonBaseCorridorLetter) ≠ 0 := by
  intro hweight
  apply hx
  apply Subtype.ext
  have hvalue := octagonBaseReducedHandleLetter_value x
  rw [hweight] at hvalue
  simpa [octagonBaseReducedLetterValue,
    octagonBaseFactorInclusion] using hvalue

private lemma octagonCorridorReflectionShift_injective (k : ℤ) :
    Function.Injective (octagonCorridorReflectionShift k) := by
  rintro ⟨n, c⟩ ⟨m, d⟩ h
  simp only [octagonCorridorReflectionShift,
    OctagonCorridorReflection.mk.injEq] at h
  obtain ⟨hnm, hcd⟩ := h
  subst d
  congr
  omega

private lemma octagonCorridorReflectionReduced_map_shift
    (k : ℤ) {rs : List OctagonCorridorReflection}
    (h : OctagonCorridorReflectionReduced rs) :
    OctagonCorridorReflectionReduced
      (rs.map (octagonCorridorReflectionShift k)) := by
  rw [OctagonCorridorReflectionReduced, List.isChain_map]
  apply h.imp
  intro r s hrs heq
  exact hrs (octagonCorridorReflectionShift_injective k heq)

private lemma octagonCorridorNormalize_head_ne
    (c : OctagonCorridorCone) (w : List OctagonBaseCorridorLetter)
    (hne : ∀ l ∈ w, l.2 ≠ 1)
    (hhead : ∀ l ∈ w.head?, c.baseFactor ≠ l.1)
    (hchain : w.IsChain fun l l' => l.1 ≠ l'.1) :
    ∀ r ∈ (octagonCorridorNormalize w).reflections.head?,
      (⟨0, c⟩ : OctagonCorridorReflection) ≠ r := by
  intro r hr
  cases w with
  | nil => simp [octagonCorridorNormalize] at hr
  | cons l w =>
      rcases l with ⟨i, x⟩
      have hx : x ≠ 1 := hne ⟨i, x⟩ (by simp)
      have hci : c.baseFactor ≠ i := hhead ⟨i, x⟩ (by simp)
      cases i with
      | handle =>
          cases w with
          | nil => simp [octagonCorridorNormalize] at hr
          | cons l' w' =>
              rcases l' with ⟨j, y⟩
              have hhj : OctagonBaseFactor.handle ≠ j :=
                (List.isChain_cons_cons.mp hchain).1
              cases j with
              | handle => exact (hhj rfl).elim
              | cone1 =>
                  have hr' : r = octagonCorridorReflectionShift
                      (octagonBaseReducedLetterWeight
                        (⟨.handle, x⟩ : OctagonBaseCorridorLetter))
                      ⟨0, .cone1⟩ := by
                    simpa [octagonCorridorNormalize] using hr.symm
                  subst r
                  intro heq
                  have hlevel := congrArg OctagonCorridorReflection.level heq
                  simp only [octagonCorridorReflectionShift_level] at hlevel
                  exact octagonBaseReducedHandleLetter_weight_ne_zero x hx
                    (by omega)
              | cone2 =>
                  have hr' : r = octagonCorridorReflectionShift
                      (octagonBaseReducedLetterWeight
                        (⟨.handle, x⟩ : OctagonBaseCorridorLetter))
                      ⟨0, .cone2⟩ := by
                    simpa [octagonCorridorNormalize] using hr.symm
                  subst r
                  intro heq
                  have hlevel := congrArg OctagonCorridorReflection.level heq
                  simp only [octagonCorridorReflectionShift_level] at hlevel
                  exact octagonBaseReducedHandleLetter_weight_ne_zero x hx
                    (by omega)
              | cone3 =>
                  have hr' : r = octagonCorridorReflectionShift
                      (octagonBaseReducedLetterWeight
                        (⟨.handle, x⟩ : OctagonBaseCorridorLetter))
                      ⟨0, .cone3⟩ := by
                    simpa [octagonCorridorNormalize] using hr.symm
                  subst r
                  intro heq
                  have hlevel := congrArg OctagonCorridorReflection.level heq
                  simp only [octagonCorridorReflectionShift_level] at hlevel
                  exact octagonBaseReducedHandleLetter_weight_ne_zero x hx
                    (by omega)
              | cone4 =>
                  have hr' : r = octagonCorridorReflectionShift
                      (octagonBaseReducedLetterWeight
                        (⟨.handle, x⟩ : OctagonBaseCorridorLetter))
                      ⟨0, .cone4⟩ := by
                    simpa [octagonCorridorNormalize] using hr.symm
                  subst r
                  intro heq
                  have hlevel := congrArg OctagonCorridorReflection.level heq
                  simp only [octagonCorridorReflectionShift_level] at hlevel
                  exact octagonBaseReducedHandleLetter_weight_ne_zero x hx
                    (by omega)
      | cone1 =>
          simp only [octagonCorridorNormalize, List.head?_cons,
            Option.mem_some_iff] at hr
          subst r
          intro heq
          apply hci
          have hc := congrArg OctagonCorridorReflection.cone heq
          cases c <;> simp_all [OctagonCorridorCone.baseFactor]
      | cone2 =>
          simp only [octagonCorridorNormalize, List.head?_cons,
            Option.mem_some_iff] at hr
          subst r
          intro heq
          apply hci
          have hc := congrArg OctagonCorridorReflection.cone heq
          cases c <;> simp_all [OctagonCorridorCone.baseFactor]
      | cone3 =>
          simp only [octagonCorridorNormalize, List.head?_cons,
            Option.mem_some_iff] at hr
          subst r
          intro heq
          apply hci
          have hc := congrArg OctagonCorridorReflection.cone heq
          cases c <;> simp_all [OctagonCorridorCone.baseFactor]
      | cone4 =>
          simp only [octagonCorridorNormalize, List.head?_cons,
            Option.mem_some_iff] at hr
          subst r
          intro heq
          apply hci
          have hc := congrArg OctagonCorridorReflection.cone heq
          cases c <;> simp_all [OctagonCorridorCone.baseFactor]

/-- Normalization carries canonical free-product reducedness to adjacent
distinctness of the conjugated reflection word. -/
theorem octagonCorridorNormalize_reflections_reduced
    (w : List OctagonBaseCorridorLetter)
    (hreduced : OctagonBaseCorridorReduced w) :
    OctagonCorridorReflectionReduced
      (octagonCorridorNormalize w).reflections := by
  induction w with
  | nil =>
      simp [octagonCorridorNormalize,
        OctagonCorridorReflectionReduced]
  | cons l w ih =>
      have hl : l.2 ≠ 1 := hreduced.1 l (by simp)
      have hwne : ∀ q ∈ w, q.2 ≠ 1 := by
        intro q hq
        exact hreduced.1 q (by simp [hq])
      have hwchain : w.IsChain fun q q' => q.1 ≠ q'.1 :=
        hreduced.2.tail
      have htail : OctagonBaseCorridorReduced w :=
        ⟨hwne, hwchain⟩
      have hhead := (List.isChain_cons.mp hreduced.2).1
      rcases l with ⟨i, x⟩
      cases i with
      | handle =>
          simp only [octagonCorridorNormalize]
          exact octagonCorridorReflectionReduced_map_shift _ (ih htail)
      | cone1 =>
          simp only [octagonCorridorNormalize,
            OctagonCorridorReflectionReduced, List.isChain_cons]
          constructor
          · apply octagonCorridorNormalize_head_ne .cone1 w hwne
              (by simpa [OctagonCorridorCone.baseFactor] using hhead)
              hwchain
          · exact ih htail
      | cone2 =>
          simp only [octagonCorridorNormalize,
            OctagonCorridorReflectionReduced, List.isChain_cons]
          constructor
          · apply octagonCorridorNormalize_head_ne .cone2 w hwne
              (by simpa [OctagonCorridorCone.baseFactor] using hhead)
              hwchain
          · exact ih htail
      | cone3 =>
          simp only [octagonCorridorNormalize,
            OctagonCorridorReflectionReduced, List.isChain_cons]
          constructor
          · apply octagonCorridorNormalize_head_ne .cone3 w hwne
              (by simpa [OctagonCorridorCone.baseFactor] using hhead)
              hwchain
          · exact ih htail
      | cone4 =>
          simp only [octagonCorridorNormalize,
            OctagonCorridorReflectionReduced, List.isChain_cons]
          constructor
          · apply octagonCorridorNormalize_head_ne .cone4 w hwne
              (by simpa [OctagonCorridorCone.baseFactor] using hhead)
              hwchain
          · exact ih htail

/-- Translate a bridge by a handle power. -/
def octagonCorridorBridgeShift (k : ℤ)
    (b : OctagonCorridorBridge) : OctagonCorridorBridge :=
  ⟨k + b.level, b.kind⟩

lemma octagon_A_zpow_smul_corridorBridgeSet
    (k : ℤ) (b : OctagonCorridorBridge) :
    (octagonBaseToPGL23 octagonBaseA) ^ k •
        octagonCorridorBridgeSet b =
      octagonCorridorBridgeSet (octagonCorridorBridgeShift k b) := by
  rcases b with ⟨n, kind⟩
  cases kind <;>
    simp only [octagonCorridorBridgeSet, octagonCorridorBridgeShift,
      ← mul_smul, ← zpow_add]

/-- An overlap of a normalized base word forces the corresponding exact
path between the handle-shifted initial bridge and the observed bridge. -/
theorem octagonCorridorNormalize_path_eq_of_overlap
    (w : List OctagonBaseCorridorLetter)
    (hreduced : OctagonBaseCorridorReduced w)
    (b c : OctagonCorridorBridge)
    (hoverlap : ∃ p ∈ octagonCorridorBridgeSet b,
      FiniteStatePingPong.eval octagonBaseReducedLetterPGL w • p ∈
        octagonCorridorBridgeSet c) :
    octagonCorridorReflectionPath
        (octagonCorridorNormalize w).reflections
        (octagonCorridorBridgeShift
          (octagonCorridorNormalize w).exponent b) = some c := by
  apply octagonCorridorReflectionPath_eq_of_overlap
    (octagonCorridorNormalize w).reflections
    (octagonCorridorNormalize_reflections_reduced w hreduced)
  obtain ⟨p, hpb, hpc⟩ := hoverlap
  let q : OctagonProjectiveBoundary :=
    (octagonBaseToPGL23 octagonBaseA) ^
      (octagonCorridorNormalize w).exponent • p
  refine ⟨q, ?_, ?_⟩
  · have hq := Set.smul_mem_smul_set
      (a := (octagonBaseToPGL23 octagonBaseA) ^
        (octagonCorridorNormalize w).exponent) hpb
    rw [octagon_A_zpow_smul_corridorBridgeSet] at hq
    exact hq
  · rw [octagonCorridorNormalize_eval w hreduced.1] at hpc
    simpa [q, mul_smul] using hpc

/-- The exact partial action of one original free-product syllable on a
corridor bridge. -/
def octagonBaseCorridorLetterStep
    (l : OctagonBaseCorridorLetter) (b : OctagonCorridorBridge) :
    Option OctagonCorridorBridge :=
  match l.1 with
  | .handle => some (octagonCorridorBridgeShift
      (octagonBaseReducedLetterWeight l) b)
  | .cone1 => octagonCorridorReflectionStep ⟨0, .cone1⟩ b
  | .cone2 => octagonCorridorReflectionStep ⟨0, .cone2⟩ b
  | .cone3 => octagonCorridorReflectionStep ⟨0, .cone3⟩ b
  | .cone4 => octagonCorridorReflectionStep ⟨0, .cone4⟩ b

/-- Run original base syllables in their right-to-left action order. -/
def octagonBaseCorridorPath :
    List OctagonBaseCorridorLetter → OctagonCorridorBridge →
      Option OctagonCorridorBridge
  | [], b => some b
  | l :: w, b => (octagonBaseCorridorPath w b).bind
      (octagonBaseCorridorLetterStep l)

private lemma octagonCorridorBridgeShift_add
    (k e : ℤ) (b : OctagonCorridorBridge) :
    octagonCorridorBridgeShift k (octagonCorridorBridgeShift e b) =
      octagonCorridorBridgeShift (k + e) b := by
  rcases b with ⟨n, kind⟩
  simp [octagonCorridorBridgeShift]
  omega

private lemma octagonCorridorBridgeShift_injective (k : ℤ) :
    Function.Injective (octagonCorridorBridgeShift k) := by
  rintro ⟨n, kind⟩ ⟨m, kind'⟩ h
  simp only [octagonCorridorBridgeShift,
    OctagonCorridorBridge.mk.injEq] at h
  obtain ⟨hnm, hkind⟩ := h
  subst kind'
  congr
  omega

private lemma octagonCorridorBridgeShift_leftBridge
    (k : ℤ) (r : OctagonCorridorReflection) :
    octagonCorridorBridgeShift k
        (octagonCorridorReflectionLeftBridge r) =
      octagonCorridorReflectionLeftBridge
        (octagonCorridorReflectionShift k r) := by
  rcases r with ⟨n, c⟩
  cases c <;> simp [octagonCorridorBridgeShift,
    octagonCorridorReflectionShift,
    octagonCorridorReflectionLeftBridge] <;> omega

private lemma octagonCorridorBridgeShift_rightBridge
    (k : ℤ) (r : OctagonCorridorReflection) :
    octagonCorridorBridgeShift k
        (octagonCorridorReflectionRightBridge r) =
      octagonCorridorReflectionRightBridge
        (octagonCorridorReflectionShift k r) := by
  rcases r with ⟨n, c⟩
  cases c <;> simp [octagonCorridorBridgeShift,
    octagonCorridorReflectionShift,
    octagonCorridorReflectionRightBridge]

private lemma octagonCorridorReflectionStep_shift
    (k : ℤ) (r : OctagonCorridorReflection)
    (b : OctagonCorridorBridge) :
    octagonCorridorReflectionStep
        (octagonCorridorReflectionShift k r)
        (octagonCorridorBridgeShift k b) =
      (octagonCorridorReflectionStep r b).map
        (octagonCorridorBridgeShift k) := by
  simp only [octagonCorridorReflectionStep]
  by_cases hl : b = octagonCorridorReflectionLeftBridge r
  · have hl' : octagonCorridorBridgeShift k b =
        octagonCorridorReflectionLeftBridge
          (octagonCorridorReflectionShift k r) := by
      rw [hl, octagonCorridorBridgeShift_leftBridge]
    rw [if_pos hl, if_pos hl', Option.map_some,
      octagonCorridorBridgeShift_rightBridge]
  · have hl' : octagonCorridorBridgeShift k b ≠
        octagonCorridorReflectionLeftBridge
          (octagonCorridorReflectionShift k r) := by
      rw [← octagonCorridorBridgeShift_leftBridge]
      intro heq
      exact hl (octagonCorridorBridgeShift_injective k heq)
    rw [if_neg hl, if_neg hl']
    by_cases hr : b = octagonCorridorReflectionRightBridge r
    · have hr' : octagonCorridorBridgeShift k b =
          octagonCorridorReflectionRightBridge
            (octagonCorridorReflectionShift k r) := by
        rw [hr, octagonCorridorBridgeShift_rightBridge]
      rw [if_pos hr, if_pos hr', Option.map_some,
        octagonCorridorBridgeShift_leftBridge]
    · have hr' : octagonCorridorBridgeShift k b ≠
          octagonCorridorReflectionRightBridge
            (octagonCorridorReflectionShift k r) := by
        rw [← octagonCorridorBridgeShift_rightBridge]
        intro heq
        exact hr (octagonCorridorBridgeShift_injective k heq)
      rw [if_neg hr, if_neg hr']
      rfl

private lemma octagonCorridorReflectionPath_shift
    (k : ℤ) (rs : List OctagonCorridorReflection)
    (b : OctagonCorridorBridge) :
    octagonCorridorReflectionPath
        (rs.map (octagonCorridorReflectionShift k))
        (octagonCorridorBridgeShift k b) =
      (octagonCorridorReflectionPath rs b).map
        (octagonCorridorBridgeShift k) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [List.map_cons, octagonCorridorReflectionPath]
      rw [ih]
      cases hpath : octagonCorridorReflectionPath rs b with
      | none => rfl
      | some c =>
          simp only [Option.map_some, Option.bind_some]
          exact octagonCorridorReflectionStep_shift k r c

/-- The direct syllable path agrees exactly with the normalized reflection
path started at the terminal-handle-shifted bridge. -/
theorem octagonBaseCorridorPath_eq_normalized
    (w : List OctagonBaseCorridorLetter) (b : OctagonCorridorBridge) :
    octagonBaseCorridorPath w b =
      octagonCorridorReflectionPath
        (octagonCorridorNormalize w).reflections
        (octagonCorridorBridgeShift
          (octagonCorridorNormalize w).exponent b) := by
  induction w with
  | nil =>
      rcases b with ⟨n, kind⟩
      simp [octagonBaseCorridorPath, octagonCorridorNormalize,
        octagonCorridorBridgeShift, octagonCorridorReflectionPath]
  | cons l w ih =>
      rcases l with ⟨i, x⟩
      cases i with
      | handle =>
          simp only [octagonBaseCorridorPath,
            octagonBaseCorridorLetterStep,
            octagonCorridorNormalize]
          rw [← octagonCorridorBridgeShift_add,
            octagonCorridorReflectionPath_shift]
          rw [← ih]
          cases octagonBaseCorridorPath w b <;> rfl
      | cone1 =>
          simp only [octagonBaseCorridorPath,
            octagonBaseCorridorLetterStep,
            octagonCorridorNormalize, octagonCorridorReflectionPath]
          rw [← ih]
          rfl
      | cone2 =>
          simp only [octagonBaseCorridorPath,
            octagonBaseCorridorLetterStep,
            octagonCorridorNormalize, octagonCorridorReflectionPath]
          rw [← ih]
          rfl
      | cone3 =>
          simp only [octagonBaseCorridorPath,
            octagonBaseCorridorLetterStep,
            octagonCorridorNormalize, octagonCorridorReflectionPath]
          rw [← ih]
          rfl
      | cone4 =>
          simp only [octagonBaseCorridorPath,
            octagonBaseCorridorLetterStep,
            octagonCorridorNormalize, octagonCorridorReflectionPath]
          rw [← ih]
          rfl

/-- Consequently every actual overlap determines the endpoint of the direct
syllable path. -/
theorem octagonBaseCorridorPath_eq_of_overlap
    (w : List OctagonBaseCorridorLetter)
    (hreduced : OctagonBaseCorridorReduced w)
    (b c : OctagonCorridorBridge)
    (hoverlap : ∃ p ∈ octagonCorridorBridgeSet b,
      FiniteStatePingPong.eval octagonBaseReducedLetterPGL w • p ∈
        octagonCorridorBridgeSet c) :
    octagonBaseCorridorPath w b = some c := by
  rw [octagonBaseCorridorPath_eq_normalized]
  exact octagonCorridorNormalize_path_eq_of_overlap
    w hreduced b c hoverlap

/-- A handle-factor syllable is the canonical handle letter at its recorded
integer weight. -/
lemma octagonBaseHandleSyllable_eq_corridorLetter
    (x : OctagonBaseFactorGroup .handle) :
    (⟨.handle, x⟩ : OctagonBaseCorridorLetter) =
      octagonHandleCorridorLetter
        (octagonBaseReducedLetterWeight
          (⟨.handle, x⟩ : OctagonBaseCorridorLetter)) := by
  unfold octagonHandleCorridorLetter
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  apply Subtype.ext
  exact octagonBaseReducedHandleLetter_value x

/-- A nonidentity cone-factor syllable is its unique order-two generator. -/
lemma octagonBaseConeSyllable_eq_corridorLetter
    {i : OctagonBaseFactor} (hi : i ≠ .handle)
    (x : OctagonBaseFactorGroup i) (hx : x ≠ 1) :
    (⟨i, x⟩ : OctagonBaseCorridorLetter) =
      octagonConeCorridorLetter i := by
  unfold octagonConeCorridorLetter
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  apply Subtype.ext
  exact octagonBaseReducedConeLetter_value hi x hx
end

end SystolicGrowth
