module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.MetricChainDistance
public import Mathlib.Tactic

@[expose] public section

/-!
# Coherent dyadic grids obtained from exact midpoints

Repeated exact midpoint subdivision constructs the finite grids needed
for extending an actual intrinsic-metric segment. Their coherence is
independent of midpoint uniqueness. Exact adjacent distances and the
endpoint distance force all pairwise grid distances; the geometric
consumer supplies the already constructed actual glued midpoints.
-/

namespace SystolicGrowth

variable {M : Type*}

/-- Repeated midpoint subdivision, with natural indices so that refinement
coherence can be stated without transporting finite-index types. -/
def midpointDyadicGrid (m : M → M → M) (x y : M) : ℕ → ℕ → M
  | 0, k => if k = 0 then x else y
  | n + 1, k => if k % 2 = 0 then midpointDyadicGrid m x y n (k / 2)
    else m (midpointDyadicGrid m x y n (k / 2))
      (midpointDyadicGrid m x y n (k / 2 + 1))

@[simp] theorem midpointDyadicGrid_even (m : M → M → M) (x y : M) (n k : ℕ) :
    midpointDyadicGrid m x y (n + 1) (2 * k) = midpointDyadicGrid m x y n k := by
  have hdiv : 2 * k / 2 = k := by omega
  have hmod : 2 * k % 2 = 0 := by omega
  simp only [midpointDyadicGrid, hmod, if_pos, hdiv]

@[simp] theorem midpointDyadicGrid_odd (m : M → M → M) (x y : M) (n k : ℕ) :
    midpointDyadicGrid m x y (n + 1) (2 * k + 1) =
      m (midpointDyadicGrid m x y n k) (midpointDyadicGrid m x y n (k + 1)) := by
  have hdiv : (2 * k + 1) / 2 = k := by omega
  have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
  simp only [midpointDyadicGrid, if_neg hmod, hdiv]

@[simp] theorem midpointDyadicGrid_zero (m : M → M → M) (x y : M) (n : ℕ) :
    midpointDyadicGrid m x y n 0 = x := by
  induction n with
  | zero => simp [midpointDyadicGrid]
  | succ n ih => simpa using (midpointDyadicGrid_even m x y n 0).trans ih

@[simp] theorem midpointDyadicGrid_endpoint (m : M → M → M) (x y : M) (n : ℕ) :
    midpointDyadicGrid m x y n (2 ^ n) = y := by
  induction n with
  | zero => simp [midpointDyadicGrid]
  | succ n ih =>
    rw [pow_succ, Nat.mul_comm, midpointDyadicGrid_even, ih]

/-- Coherence at every integral refinement factor, without any assumption
that the chosen midpoint is unique. -/
theorem midpointDyadicGrid_rescale (m : M → M → M) (x y : M) (n q k : ℕ) :
    midpointDyadicGrid m x y (n + q) (k * 2 ^ q) = midpointDyadicGrid m x y n k := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ]
    have hidx : k * (2 ^ q * 2) = 2 * (k * 2 ^ q) := by ring
    rw [hidx, Nat.add_succ, midpointDyadicGrid_even, ih]

/-- The same coherence stated for two ordered subdivision levels. -/
theorem midpointDyadicGrid_refine (m : M → M → M) (x y : M) {n N : ℕ}
    (h : n ≤ N) (k : ℕ) :
    midpointDyadicGrid m x y N (k * 2 ^ (N - n)) = midpointDyadicGrid m x y n k := by
  simpa only [Nat.add_sub_of_le h] using midpointDyadicGrid_rescale m x y n (N - n) k

variable [PseudoMetricSpace M]

/-- Every adjacent dyadic pair has the exact half-distance obtained from
the actual chosen midpoint, independently of choices at other pairs. -/
theorem midpointDyadicGrid_adjacent (m : M → M → M)
    (hm : ∀ a b : M, dist a (m a b) = dist a b / 2 ∧ dist (m a b) b = dist a b / 2)
    (x y : M) (n k : ℕ) (hk : k < 2 ^ n) :
    dist (midpointDyadicGrid m x y n k) (midpointDyadicGrid m x y n (k + 1)) =
      dist x y / (2 : ℝ) ^ n := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by simpa using hk
    subst k
    simp [midpointDyadicGrid]
  | succ n ih =>
    let j := k / 2
    have hsize : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
    rw [hsize] at hk
    have hj : j < 2 ^ n := by dsimp [j]; omega
    by_cases hmod : k % 2 = 0
    · have hidx : k = 2 * j := by dsimp [j]; omega
      rw [hidx, midpointDyadicGrid_even, midpointDyadicGrid_odd,
        (hm _ _).1, ih j hj, div_div, pow_succ]
    · have hidx : k = 2 * j + 1 := by dsimp [j]; omega
      have hnext : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
      rw [hidx, hnext, midpointDyadicGrid_odd, midpointDyadicGrid_even,
        (hm _ _).2, ih j hj, div_div, pow_succ]

/-- Endpoint saturation forces every ordered dyadic distance, using the
actual finite-chain triangle inequality rather than midpoint uniqueness. -/
theorem midpointDyadicGrid_dist_ordered (m : M → M → M)
    (hm : ∀ a b : M, dist a (m a b) = dist a b / 2 ∧ dist (m a b) b = dist a b / 2)
    (x y : M) (n : ℕ) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 2 ^ n) :
    dist (midpointDyadicGrid m x y n i) (midpointDyadicGrid m x y n j) =
      ((j - i : ℕ) : ℝ) * (dist x y / (2 : ℝ) ^ n) := by
  have hend : dist (midpointDyadicGrid m x y n 0)
      (midpointDyadicGrid m x y n (2 ^ n)) = (2 ^ n : ℕ) * (dist x y / (2 : ℝ) ^ n) := by
    simp only [midpointDyadicGrid_zero, midpointDyadicGrid_endpoint,
      Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  exact metric_chain_dist_eq (midpointDyadicGrid m x y n)
    (fun k hk => (midpointDyadicGrid_adjacent m hm x y n k hk).le) hend hij hj

/-- Exact scaled distance between arbitrary indices of one dyadic grid.
This is the coordinate contract consumed by the dense interval extension. -/
theorem midpointDyadicGrid_dist (m : M → M → M)
    (hm : ∀ a b : M, dist a (m a b) = dist a b / 2 ∧ dist (m a b) b = dist a b / 2)
    (x y : M) (n : ℕ) {i j : ℕ} (hi : i ≤ 2 ^ n) (hj : j ≤ 2 ^ n) :
    dist (midpointDyadicGrid m x y n i) (midpointDyadicGrid m x y n j) =
      dist x y * |(i : ℝ) / (2 : ℝ) ^ n - (j : ℝ) / (2 : ℝ) ^ n| := by
  have hordered {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 2 ^ n) :
      dist (midpointDyadicGrid m x y n i) (midpointDyadicGrid m x y n j) =
        dist x y * |(i : ℝ) / (2 : ℝ) ^ n - (j : ℝ) / (2 : ℝ) ^ n| := by
    rw [midpointDyadicGrid_dist_ordered m hm x y n hij hj, Nat.cast_sub hij]
    have hcast : (i : ℝ) ≤ j := by exact_mod_cast hij
    rw [abs_of_nonpos (sub_nonpos.mpr (div_le_div_of_nonneg_right hcast (by positivity)))]
    ring
  rcases le_total i j with hij | hji
  · exact hordered hij hj
  · rw [dist_comm, abs_sub_comm]
    exact hordered hji hi

#print axioms midpointDyadicGrid_rescale
#print axioms midpointDyadicGrid_refine
#print axioms midpointDyadicGrid_adjacent
#print axioms midpointDyadicGrid_dist_ordered
#print axioms midpointDyadicGrid_dist

end SystolicGrowth
