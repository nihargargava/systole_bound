module

public import Mathlib.GroupTheory.GroupAction.Basic

@[expose] public section

/-!
# Finite-state ping-pong

This file packages the elementary induction used by corridor-style
ping-pong arguments.  A word is read from right to left, matching the order
in which the product of its letters acts.  Local transitions between a
family of disjoint regions then certify that a word with a nontrivial state
transition cannot evaluate to the identity.
-/

open Set

namespace FiniteStatePingPong

variable {Alphabet State G X : Type*} [Monoid G] [MulAction G X]

/-- Run a deterministic state machine in the right-to-left order in which a
group product acts on a point. -/
def run (step : Alphabet → State → State) : List Alphabet → State → State
  | [], s => s
  | a :: w, s => step a (run step w s)

/-- Evaluate a word after interpreting each letter in a monoid. -/
def eval (letter : Alphabet → G) (w : List Alphabet) : G :=
  (w.map letter).prod

@[simp] lemma run_nil (step : Alphabet → State → State) (s : State) :
    run step [] s = s := rfl

@[simp] lemma run_cons (step : Alphabet → State → State)
    (a : Alphabet) (w : List Alphabet) (s : State) :
    run step (a :: w) s = step a (run step w s) := rfl

@[simp] lemma eval_nil (letter : Alphabet → G) :
    eval letter [] = 1 := by
  simp [eval]

@[simp] lemma eval_cons (letter : Alphabet → G)
    (a : Alphabet) (w : List Alphabet) :
    eval letter (a :: w) = letter a * eval letter w := by
  simp [eval]

/-- Local transition estimates propagate through a whole word.  Only the
letters occurring in the word need estimates. -/
theorem mapsTo_eval_of_mem
    (letter : Alphabet → G) (step : Alphabet → State → State)
    (region : State → Set X) (w : List Alphabet)
    (hstep : ∀ a ∈ w, ∀ s,
      MapsTo (fun x => letter a • x) (region s) (region (step a s)))
    (s : State) :
    MapsTo (fun x => eval letter w • x)
      (region s) (region (run step w s)) := by
  induction w generalizing s with
  | nil =>
      intro x hx
      simpa using hx
  | cons a w ih =>
      intro x hx
      have hw : eval letter w • x ∈ region (run step w s) := by
        apply ih
        · intro b hb t
          exact hstep b (by simp [hb]) t
        · exact hx
      have ha := hstep a (by simp) (run step w s) hw
      simpa [mul_smul] using ha

/-- Universal local transition estimates propagate through every word. -/
theorem mapsTo_eval
    (letter : Alphabet → G) (step : Alphabet → State → State)
    (region : State → Set X)
    (hstep : ∀ a s,
      MapsTo (fun x => letter a • x) (region s) (region (step a s)))
    (w : List Alphabet) (s : State) :
    MapsTo (fun x => eval letter w • x)
      (region s) (region (run step w s)) := by
  apply mapsTo_eval_of_mem letter step region w
  intro a _ t
  exact hstep a t

/-- If state regions are pairwise disjoint, observing the image in a given
region determines the final state. -/
theorem run_eq_of_image_mem
    (letter : Alphabet → G) (step : Alphabet → State → State)
    (region : State → Set X)
    (hstep : ∀ a s,
      MapsTo (fun x => letter a • x) (region s) (region (step a s)))
    (hdisjoint : Pairwise fun s t => Disjoint (region s) (region t))
    {w : List Alphabet} {s t : State} {x : X}
    (hx : x ∈ region s) (himage : eval letter w • x ∈ region t) :
    run step w s = t := by
  have hrun := mapsTo_eval letter step region hstep w s hx
  by_contra hne
  exact Set.disjoint_left.mp (hdisjoint hne) hrun himage

/-- A word that changes a nonempty state region cannot evaluate to the
identity. -/
theorem eval_ne_one_of_run_ne
    (letter : Alphabet → G) (step : Alphabet → State → State)
    (region : State → Set X)
    (hstep : ∀ a s,
      MapsTo (fun x => letter a • x) (region s) (region (step a s)))
    (hdisjoint : Pairwise fun s t => Disjoint (region s) (region t))
    {w : List Alphabet} {s : State} (hs : (region s).Nonempty)
    (hrun : run step w s ≠ s) :
    eval letter w ≠ 1 := by
  intro heval
  obtain ⟨x, hx⟩ := hs
  have himage := mapsTo_eval letter step region hstep w s hx
  have hsame : eval letter w • x ∈ region s := by
    simpa [heval] using hx
  exact Set.disjoint_left.mp (hdisjoint hrun) himage hsame

/-- Consequently, an identity word must return every inhabited state to
itself. -/
theorem run_eq_of_eval_eq_one
    (letter : Alphabet → G) (step : Alphabet → State → State)
    (region : State → Set X)
    (hstep : ∀ a s,
      MapsTo (fun x => letter a • x) (region s) (region (step a s)))
    (hdisjoint : Pairwise fun s t => Disjoint (region s) (region t))
    {w : List Alphabet} {s : State} (hs : (region s).Nonempty)
    (heval : eval letter w = 1) :
    run step w s = s := by
  by_contra hrun
  exact eval_ne_one_of_run_ne letter step region hstep hdisjoint hs hrun heval

section Corridor

variable {A : Type*}

/-- Additive weight of a word.  In the octagon application this records the
handle exponent. -/
def weight (letterWeight : A → ℤ) (w : List A) : ℤ :=
  (w.map letterWeight).sum

@[simp] lemma weight_nil (letterWeight : A → ℤ) :
    weight letterWeight [] = 0 := by
  simp [weight]

@[simp] lemma weight_append (letterWeight : A → ℤ)
    (u v : List A) :
    weight letterWeight (u ++ v) =
      weight letterWeight u + weight letterWeight v := by
  simp [weight]

/-- Repeat a corridor block by appending it on the right. -/
def cycleRepeat (cycle : List A) : ℕ → List A
  | 0 => []
  | n + 1 => cycleRepeat cycle n ++ cycle

@[simp] lemma cycleRepeat_zero (cycle : List A) : cycleRepeat cycle 0 = [] := rfl

@[simp] lemma cycleRepeat_succ (cycle : List A) (n : ℕ) :
    cycleRepeat cycle (n + 1) = cycleRepeat cycle n ++ cycle := rfl

@[simp] lemma weight_cycleRepeat (letterWeight : A → ℤ)
    (cycle : List A) (n : ℕ) :
    weight letterWeight (cycleRepeat cycle n) = n * weight letterWeight cycle := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.cast_succ, add_mul]

/-- If every nonempty accepted word has a fixed accepted suffix that can be
peeled off, then the accepted language consists of powers of that suffix.
This is the abstract word-peeling step behind a corridor argument. -/
theorem eq_pow_of_suffix_peel
    (Accept : List A → Prop) (cycle : List A) (hcycle : cycle ≠ [])
    (hpeel : ∀ w, Accept w →
      w = [] ∨ ∃ v, Accept v ∧ w = v ++ cycle)
    {w : List A} (hw : Accept w) :
    ∃ n : ℕ, w = cycleRepeat cycle n := by
  rcases hpeel w hw with hnil | ⟨v, hv, hweq⟩
  · exact ⟨0, by simp [hnil]⟩
  · obtain ⟨n, hn⟩ :=
      eq_pow_of_suffix_peel Accept cycle hcycle hpeel hv
    exact ⟨n + 1, by rw [hweq, hn, cycleRepeat_succ]⟩
termination_by w.length
decreasing_by
  rw [hweq]
  rw [List.length_append]
  apply Nat.lt_add_of_pos_right
  exact Nat.pos_of_ne_zero (by simpa using hcycle)

/-- A corridor cycle with nonzero weight cannot occur in a weight-zero word.
Combined with `eq_pow_of_suffix_peel`, this rules out every nonempty accepted
transversal word. -/
theorem eq_nil_of_suffix_peel_and_weight_zero
    (Accept : List A → Prop) (cycle : List A) (hcycle : cycle ≠ [])
    (hpeel : ∀ w, Accept w →
      w = [] ∨ ∃ v, Accept v ∧ w = v ++ cycle)
    (letterWeight : A → ℤ) (hcycleWeight : weight letterWeight cycle ≠ 0)
    {w : List A} (hw : Accept w) (hwWeight : weight letterWeight w = 0) :
    w = [] := by
  obtain ⟨n, rfl⟩ := eq_pow_of_suffix_peel Accept cycle hcycle hpeel hw
  have hn : n = 0 := by
    by_contra hn0
    have hnInt : (n : ℤ) ≠ 0 := by exact_mod_cast hn0
    have : (n : ℤ) * weight letterWeight cycle ≠ 0 :=
      mul_ne_zero hnInt hcycleWeight
    exact this (by simpa using hwWeight)
  simp [hn]

/-- A two-orientation corridor language.  After the first peel chooses a
forward or backward cycle, the corresponding one-cycle peeling argument and
its nonzero weight rule out a nonempty weight-zero word. -/
theorem eq_nil_of_two_suffix_corridors_and_weight_zero
    (Accept Forward Backward : List A → Prop)
    (forwardCycle backwardCycle : List A)
    (hforwardCycle : forwardCycle ≠ [])
    (hbackwardCycle : backwardCycle ≠ [])
    (hsplit : ∀ w, Accept w →
      w = [] ∨ Forward w ∨ Backward w)
    (hforwardPeel : ∀ w, Forward w →
      w = [] ∨ ∃ v, Forward v ∧ w = v ++ forwardCycle)
    (hbackwardPeel : ∀ w, Backward w →
      w = [] ∨ ∃ v, Backward v ∧ w = v ++ backwardCycle)
    (letterWeight : A → ℤ)
    (hforwardWeight : weight letterWeight forwardCycle ≠ 0)
    (hbackwardWeight : weight letterWeight backwardCycle ≠ 0)
    {w : List A} (hw : Accept w) (hwWeight : weight letterWeight w = 0) :
    w = [] := by
  rcases hsplit w hw with hnil | hforward | hbackward
  · exact hnil
  · exact eq_nil_of_suffix_peel_and_weight_zero
      Forward forwardCycle hforwardCycle hforwardPeel
      letterWeight hforwardWeight hforward hwWeight
  · exact eq_nil_of_suffix_peel_and_weight_zero
      Backward backwardCycle hbackwardCycle hbackwardPeel
      letterWeight hbackwardWeight hbackward hwWeight

end Corridor

end FiniteStatePingPong
