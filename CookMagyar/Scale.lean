module

public import CookMagyar.CircleMethod

@[expose] public section

namespace SystolicGrowth

/-! # Choosing the cubic circle-method scale

For a fixed number `n` of variables and target `T`, we choose the least `N`
for which

`4 T ≤ (4 n - 1) N³`.

For large `T`, minimality forces `T/N³` into the compact interval
`[n-1/3, n-1/5]`.  This is the integer-only version of the ceiling/cube-root
choice used in the scale selection.
-/

/-- The compact normalized-target window
`n - 1/3 ≤ T/N³ ≤ n - 1/5`, written without division. -/
def CookMagyarWindow (n N T : ℕ) : Prop :=
  (3 * n - 1) * N ^ 3 ≤ 3 * T ∧
  5 * T ≤ (5 * n - 1) * N ^ 3

theorem Internal.ScaleHelpers.exists_cubic_scale (n T : ℕ) (hn : 0 < n) :
    ∃ N : ℕ, 4 * T ≤ (4 * n - 1) * N ^ 3 := by
  let N := 4 * T + 1
  have hN : 1 ≤ N := by simp [N]
  have hTN : 4 * T ≤ N := by simp [N]
  have hpow : N ≤ N ^ 3 := Nat.le_pow (by norm_num)
  have hcoef : 1 ≤ 4 * n - 1 := by omega
  refine ⟨N, hTN.trans (hpow.trans ?_)⟩
  nlinarith

/-- The least scale satisfying `4T ≤ (4n-1)N³`. -/
noncomputable def cubicScale (n T : ℕ) (hn : 0 < n) : ℕ :=
  Nat.find (Internal.ScaleHelpers.exists_cubic_scale n T hn)

theorem cubicScale_spec (n T : ℕ) (hn : 0 < n) :
    4 * T ≤ (4 * n - 1) * (cubicScale n T hn) ^ 3 :=
  Nat.find_spec (Internal.ScaleHelpers.exists_cubic_scale n T hn)

theorem cubicScale_min {n T : ℕ} (hn : 0 < n) {M : ℕ}
    (hM : M < cubicScale n T hn) :
    (4 * n - 1) * M ^ 3 < 4 * T := by
  have hnot := Nat.find_min (Internal.ScaleHelpers.exists_cubic_scale n T hn) hM
  omega

theorem cubicScale_pos {n T : ℕ} (hn : 0 < n) (hT : 0 < T) :
    0 < cubicScale n T hn := by
  have hs := cubicScale_spec n T hn
  by_contra h
  have hz : cubicScale n T hn = 0 := by omega
  simp [hz] at hs
  omega

/-- A target threshold forcing the least scale to be at least `K`. -/
def cubicScaleTargetThresholdFor (n K : ℕ) : ℕ :=
  (4 * n - 1) * K ^ 3 + 1

theorem le_cubicScale_of_targetThresholdFor {n T K : ℕ} (hn : 0 < n)
    (hT : cubicScaleTargetThresholdFor n K ≤ T) :
    K ≤ cubicScale n T hn := by
  by_contra hnot
  have hscale : cubicScale n T hn < K := by omega
  have hs := cubicScale_spec n T hn
  have hpow : (cubicScale n T hn) ^ 3 ≤ K ^ 3 :=
    Nat.pow_le_pow_left (by omega) 3
  have hupper :
      (4 * n - 1) * (cubicScale n T hn) ^ 3 ≤
        (4 * n - 1) * K ^ 3 :=
    Nat.mul_le_mul_left _ hpow
  have hlower : (4 * n - 1) * K ^ 3 + 1 ≤ T := hT
  omega

/-- A deliberately coarse threshold after which the least scale is at least
`36n`.  No sharp constant is needed downstream. -/
def cubicScaleTargetThreshold (n : ℕ) : ℕ :=
  cubicScaleTargetThresholdFor n (36 * n)

theorem thirtySix_mul_le_cubicScale {n T : ℕ} (hn : 0 < n)
    (hT : cubicScaleTargetThreshold n ≤ T) :
    36 * n ≤ cubicScale n T hn := by
  exact le_cubicScale_of_targetThresholdFor hn hT

private theorem lower_window_coefficient {n N : ℕ} (hn : 0 < n)
    (hN : 36 * n ≤ N) :
    4 * (3 * n - 1) * N ^ 3 ≤
      3 * (4 * n - 1) * (N - 1) ^ 3 := by
  have hNpos : 0 < N := by omega
  let M := N - 1
  have hNM : M + 1 = N := Nat.sub_add_cancel (by omega)
  have hM : 36 * n - 1 ≤ M := by omega
  have hcoefM : 36 * n - 12 ≤ M := by omega
  have hmul : (36 * n - 12) * M ≤ M ^ 2 := by
    calc
      (36 * n - 12) * M ≤ M * M := Nat.mul_le_mul_right M hcoefM
      _ = M ^ 2 := by ring
  have hsmall : 12 * n - 4 ≤ 10 * M ^ 2 := by
    have hMpos : 1 ≤ M := by omega
    have hlin : 12 * n - 4 ≤ M := by omega
    have hMpow : M ≤ M ^ 2 := Nat.le_pow (by norm_num)
    have hten : M ^ 2 ≤ 10 * M ^ 2 := by nlinarith
    exact hlin.trans (hMpow.trans hten)
  have hbig : (36 * n - 1) * M ^ 2 ≤ M ^ 3 := by
    calc
      (36 * n - 1) * M ^ 2 ≤ M * M ^ 2 :=
        Nat.mul_le_mul_right (M ^ 2) hM
      _ = M ^ 3 := by ring
  have hextra :
      4 * (3 * n - 1) * (3 * M ^ 2 + 3 * M + 1) ≤ M ^ 3 := by
    have hc₁ : 4 * (3 * n - 1) = 12 * n - 4 := by omega
    have hc₂ : (12 * n - 4) * 3 = 36 * n - 12 := by omega
    have hc₃ : 36 * n - 1 = (36 * n - 12) + 11 := by omega
    have haux :
        4 * (3 * n - 1) * (3 * M ^ 2 + 3 * M + 1) ≤
          (36 * n - 1) * M ^ 2 := by
      calc
        4 * (3 * n - 1) * (3 * M ^ 2 + 3 * M + 1) =
            (36 * n - 12) * M ^ 2 +
              ((36 * n - 12) * M + (12 * n - 4)) := by
          rw [hc₁]
          rw [mul_add, mul_add]
          simp only [mul_one]
          rw [← mul_assoc (12 * n - 4) 3 (M ^ 2), hc₂]
          rw [← mul_assoc (12 * n - 4) 3 M, hc₂]
          ring
        _ ≤ (36 * n - 12) * M ^ 2 + (M ^ 2 + 10 * M ^ 2) :=
          Nat.add_le_add_left (Nat.add_le_add hmul hsmall) _
        _ = ((36 * n - 12) + 11) * M ^ 2 := by ring
        _ = (36 * n - 1) * M ^ 2 := by rw [← hc₃]
    exact haux.trans hbig
  have hcoeff : 4 * (3 * n - 1) + 1 = 3 * (4 * n - 1) := by omega
  rw [← hNM]
  simp only [Nat.add_sub_cancel]
  calc
    4 * (3 * n - 1) * (M + 1) ^ 3 =
        4 * (3 * n - 1) * M ^ 3 +
          4 * (3 * n - 1) * (3 * M ^ 2 + 3 * M + 1) := by ring
    _ ≤ 4 * (3 * n - 1) * M ^ 3 + M ^ 3 :=
      Nat.add_le_add_left hextra _
    _ = (4 * (3 * n - 1) + 1) * M ^ 3 := by ring
    _ = 3 * (4 * n - 1) * M ^ 3 := by rw [hcoeff]

/-- Minimality of `cubicScale` puts a sufficiently large target in the
compact normalized window used by the uniform circle-method estimates. -/
theorem cubicScale_mem_window {n T : ℕ} (hn : 0 < n)
    (hT : cubicScaleTargetThreshold n ≤ T) :
    CookMagyarWindow n (cubicScale n T hn) T := by
  let N := cubicScale n T hn
  have hNlarge : 36 * n ≤ N := by
    simpa [N] using thirtySix_mul_le_cubicScale hn hT
  have hNpos : 0 < N := by omega
  have hmin : (4 * n - 1) * (N - 1) ^ 3 < 4 * T := by
    apply cubicScale_min hn
    dsimp [N]
    omega
  have hcoef := lower_window_coefficient hn hNlarge
  have hlower : (3 * n - 1) * N ^ 3 ≤ 3 * T := by
    apply Nat.le_of_mul_le_mul_left (c := 4) ?_ (by norm_num)
    calc
      4 * ((3 * n - 1) * N ^ 3) = 4 * (3 * n - 1) * N ^ 3 := by ring
      _ ≤ 3 * (4 * n - 1) * (N - 1) ^ 3 := hcoef
      _ ≤ 3 * (4 * T) := by
        simpa [mul_assoc] using Nat.mul_le_mul_left 3 hmin.le
      _ = 4 * (3 * T) := by ring
  have hspec : 4 * T ≤ (4 * n - 1) * N ^ 3 := by
    simpa [N] using cubicScale_spec n T hn
  have hupper : 5 * T ≤ (5 * n - 1) * N ^ 3 := by
    apply Nat.le_of_mul_le_mul_left (c := 4) ?_ (by norm_num)
    calc
      4 * (5 * T) = 5 * (4 * T) := by ring
      _ ≤ 5 * ((4 * n - 1) * N ^ 3) := Nat.mul_le_mul_left 5 hspec
      _ ≤ 4 * ((5 * n - 1) * N ^ 3) := by
        have hc : 5 * (4 * n - 1) ≤ 4 * (5 * n - 1) := by omega
        calc
          5 * ((4 * n - 1) * N ^ 3) =
              (5 * (4 * n - 1)) * N ^ 3 := by ring
          _ ≤ (4 * (5 * n - 1)) * N ^ 3 := Nat.mul_le_mul_right _ hc
          _ = 4 * ((5 * n - 1) * N ^ 3) := by ring
  exact ⟨hlower, hupper⟩

end SystolicGrowth
