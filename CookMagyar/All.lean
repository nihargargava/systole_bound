module

public import Core.SystolicCore
public import CookMagyar.ArcGeometry
public import CookMagyar.EulerProduct
public import CookMagyar.LocalFactorTail
public import CookMagyar.LocalLargePrimeCounts
public import CookMagyar.LocalLargePrimeLift
public import CookMagyar.LocalNonsingular
public import CookMagyar.LocalSmallPrimeCounts
public import CookMagyar.MajorArcArithmetic
public import CookMagyar.MinorArcReduction
public import CookMagyar.APCharacterBridge
public import CookMagyar.RealBridge
public import CookMagyar.RealDensityConvolution
public import CookMagyar.Uniformity
public import CookMagyar.Vaughan
public import CookMagyar.HuaSieve
public import CookMagyar.HuaStepEight
public import CookMagyar.HuaAsymptotic
public import CookMagyar.CubicHighMoment
public import CookMagyar.MinorArcHighMoment
public import CookMagyar.UnweightedResidueAbel
public import CookMagyar.UnweightedCompleteModel
public import CookMagyar.UnweightedHomogeneousModel
public import CookMagyar.AuxiliaryPowerCutoff
public import CookMagyar.OrdinaryWeylLinear
public import CookMagyar.OrdinaryWeylSpacing
public import CookMagyar.OrdinaryWeylPairs
public import CookMagyar.GeneralCubicWeyl
public import CookMagyar.PrimeMinorArcVaughan
public import CookMagyar.OrdinaryWeylMinorArc

@[expose] public section

open Filter Set
open scoped BigOperators Topology

namespace SystolicGrowth

/-! ## The target-uniform Cook--Magyar specialization

This file isolates the analytic number theory used in the systolic-growth
argument.  The analytic estimates enter through
`CookMagyarCircle.SeparatedCubicEstimates`: a positive main term, a major-arc
approximation, a minor-arc bound, and Hua's target-free eighth-moment
estimate.  Prime-power removal is then proved from Hua plus Mathlib's
Chebyshev bounds, uniformly in the moving target.
`CookMagyar.Uniformity` chooses one common target-independent threshold and
`CookMagyar.Assembly` proves that these estimates yield a bounded odd-prime
solution.  Everything from that solution to the genus decomposition is
elementary arithmetic and is proved here.

The normalization by `24` is integral at every odd integer.  The
Cook--Magyar target `T` is `24 * q`, so the genus bookkeeping can use `q`
directly.

The remaining analytic development has three successive estimates: the
von-Mangoldt major-arc asymptotic uniform in `T/N^3`, uniform positivity of
the real density and singular series for `24 ∣ T`, and the cubic
minor-arc/Hua estimates.  Removal of prime powers and the prime `2` is
already derived from the Hua estimate.  In the singular-series step the
required tail estimate is
`|μ_p(T)-1| ≤ C p^(-1-δ)`; the absolute value is essential.  The local-factor
rank condition also requires at least `33` variables.
-/

/-- The cubic value normalized by its universal factor `24` on odd inputs. -/
def normalizedPrimeCubic (p : ℕ) : ℕ := primeCubic p / 24

/-- The genus `ν (p^3-p)+1`, with the integer normalization `h=24ν`. -/
def arithmeticGenus (h p : ℕ) : ℕ :=
  h * normalizedPrimeCubic p + 1

private lemma primeCubic_factor (p : ℕ) (hp : 1 ≤ p) :
    primeCubic p = (p - 1) * p * (p + 1) := by
  cases p with
  | zero => omega
  | succ q =>
    simp only [primeCubic, Nat.add_sub_cancel]
    ring_nf
    omega

private lemma three_dvd_three_consecutive (p : ℕ) :
    3 ∣ (p - 1) * p * (p + 1) := by
  have hrange : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hrange with h0 | h1 | h2
  · have hp : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hp (p - 1)) (p + 1)
  · have hp : 3 ∣ p - 1 := by
      simpa [h1] using (Nat.dvd_sub_mod (n := 3) p)
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hp p) (p + 1)
  · have hp : 3 ∣ p + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    exact dvd_mul_of_dvd_right hp ((p - 1) * p)

private lemma eight_dvd_three_consecutive_of_odd (p : ℕ) (hp : Odd p) :
    8 ∣ (p - 1) * p * (p + 1) := by
  obtain ⟨k, rfl⟩ := hp
  rcases Nat.even_or_odd k with hk | hk
  · obtain ⟨j, rfl⟩ := hk
    refine ⟨j * ((4 * j + 1) * (2 * j + 1)), ?_⟩
    simp only [Nat.add_sub_cancel]
    ring
  · obtain ⟨j, rfl⟩ := hk
    refine ⟨(2 * j + 1) * ((2 * (2 * j + 1) + 1) * (j + 1)), ?_⟩
    simp only [Nat.add_sub_cancel]
    ring

/-- The elementary congruence behind the normalization: `24 ∣ p³-p` for
every odd natural number `p`. -/
theorem twenty_four_dvd_primeCubic_of_odd {p : ℕ} (hp : Odd p) :
    24 ∣ primeCubic p := by
  have hp_one : 1 ≤ p := by
    obtain ⟨k, rfl⟩ := hp
    omega
  rw [primeCubic_factor p hp_one]
  change 3 * 8 ∣ _
  exact (by decide : Nat.Coprime 3 8).mul_dvd_of_dvd_of_dvd
    (three_dvd_three_consecutive p)
    (eight_dvd_three_consecutive_of_odd p hp)

/-- On odd inputs, division by `24` in `normalizedPrimeCubic` is exact. -/
theorem twenty_four_mul_normalizedPrimeCubic_of_odd {p : ℕ} (hp : Odd p) :
    24 * normalizedPrimeCubic p = primeCubic p := by
  exact Nat.mul_div_cancel' (twenty_four_dvd_primeCubic_of_odd hp)

theorem twenty_four_mul_normalizedPrimeCubic_of_odd_prime
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    24 * normalizedPrimeCubic p = primeCubic p :=
  twenty_four_mul_normalizedPrimeCubic_of_odd (hp.odd_of_ne_two hp2)

/-- Convert the raw Cook--Magyar equation at target `24q` to the normalized
equation used in the genus calculation. -/
theorem sum_normalizedPrimeCubic_eq_of_sum_primeCubic_eq
    {n q : ℕ} (primes : Fin n → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hodd : ∀ i, primes i ≠ 2)
    (hsum : (∑ i, primeCubic (primes i)) = 24 * q) :
    (∑ i, normalizedPrimeCubic (primes i)) = q := by
  apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 24)
  calc
    24 * (∑ i, normalizedPrimeCubic (primes i)) =
        ∑ i, 24 * normalizedPrimeCubic (primes i) := by rw [Finset.mul_sum]
    _ = ∑ i, primeCubic (primes i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact twenty_four_mul_normalizedPrimeCubic_of_odd_prime
        (hprime i) (hodd i)
    _ = 24 * q := hsum

/-- Convert the root-free raw comparability estimate into its normalized
form. -/
theorem normalized_comparable_of_primeCubic_comparable
    {n q p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcompare : 24 * q ≤ 4 * n * primeCubic p) :
    q ≤ 4 * n * normalizedPrimeCubic p := by
  apply Nat.le_of_mul_le_mul_left (c := 24) ?_ (by norm_num)
  calc
    24 * q ≤ 4 * n * primeCubic p := hcompare
    _ = 24 * (4 * n * normalizedPrimeCubic p) := by
      rw [← twenty_four_mul_normalizedPrimeCubic_of_odd_prime hp hp2]
      ring

/-- An odd-prime solution of the cubic equation at scale `N`. -/
structure OddPrimeSolution (n N T : ℕ) where
  primes : Fin n → ℕ
  prime : ∀ i, (primes i).Prime
  ne_two : ∀ i, primes i ≠ 2
  upper : ∀ i, primes i ≤ N
  equation : (∑ i, primeCubic (primes i)) = T

/-- Convert the prime-only Fourier-counting output into the bounded solution
record used by the arithmetic reduction. -/
theorem oddPrimeSolution_nonempty_of_cubicRepresentation
    {n N T : ℕ}
    (h : CookMagyarCircle.IsOddPrimeCubicRepresentation n N T) :
    Nonempty (OddPrimeSolution n N T) := by
  rcases h with ⟨x, heq, hx⟩
  exact ⟨{
    primes := fun i ↦ x i
    prime := fun i ↦ (hx i).1
    ne_two := fun i ↦ (hx i).2
    upper := fun i ↦ Nat.le_of_lt_succ (x i).isLt
    equation := heq }⟩

/-- No coordinate of a solution in the chosen target window can be much
smaller than the ambient scale.  The contradiction argument avoids cube roots. -/
theorem OddPrimeSolution.lower_cube
    {n N T : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N)
    (s : OddPrimeSolution n N T) (hw : CookMagyarWindow n N T)
    (i : Fin n) : N ^ 3 < 2 * (s.primes i) ^ 3 := by
  by_contra hnot
  have hsmall : 2 * (s.primes i) ^ 3 ≤ N ^ 3 := by omega
  have hpoint : ∀ j : Fin n, primeCubic (s.primes j) ≤ (s.primes j) ^ 3 := by
    intro j
    exact Nat.sub_le _ _
  have herase :
      (∑ j ∈ (Finset.univ.erase i), (s.primes j) ^ 3) ≤
        (n - 1) * N ^ 3 := by
    calc
      (∑ j ∈ (Finset.univ.erase i), (s.primes j) ^ 3) ≤
          (Finset.univ.erase i).card • (N ^ 3) :=
        Finset.sum_le_card_nsmul _ _ _ (by
          intro j _
          exact Nat.pow_le_pow_left (s.upper j) 3)
      _ = (n - 1) * N ^ 3 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
        exact Nat.nsmul_eq_mul _ _
  have hcube :
      (∑ j, (s.primes j) ^ 3) ≤
        (n - 1) * N ^ 3 + (s.primes i) ^ 3 := by
    rw [← Finset.sum_erase_add Finset.univ (fun j ↦ (s.primes j) ^ 3)
      (Finset.mem_univ i)]
    exact Nat.add_le_add_right herase _
  have hT : T ≤ ∑ j, (s.primes j) ^ 3 := by
    calc
      T = ∑ j, primeCubic (s.primes j) := s.equation.symm
      _ ≤ ∑ j, (s.primes j) ^ 3 := Finset.sum_le_sum fun j _ ↦ hpoint j
  have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have h3nsub : 3 * n - 1 + 1 = 3 * n := by omega
  have hNcube : 0 < N ^ 3 := pow_pos (by omega) 3
  have hlower := hw.1
  nlinarith

/-- The compact target window implies the root-free comparability estimate
used in the genus calculation. -/
theorem OddPrimeSolution.target_le_four_mul_primeCubic
    {n N T : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N)
    (s : OddPrimeSolution n N T) (hw : CookMagyarWindow n N T)
    (i : Fin n) : T ≤ 4 * n * primeCubic (s.primes i) := by
  have hlower := s.lower_cube hn hN hw i
  have hp_two : 2 ≤ s.primes i := (s.prime i).two_le
  have hpcube : s.primes i ≤ (s.primes i) ^ 3 := Nat.le_pow (by norm_num)
  have hsquare : 2 ≤ (s.primes i) ^ 2 :=
    hp_two.trans (Nat.le_pow (by norm_num))
  have htwop : 2 * s.primes i ≤ (s.primes i) ^ 3 := by
    calc
      2 * s.primes i ≤ (s.primes i) ^ 2 * s.primes i :=
        Nat.mul_le_mul_right _ hsquare
      _ = (s.primes i) ^ 3 := by ring
  have hsub : (s.primes i) ^ 3 - s.primes i + s.primes i =
      (s.primes i) ^ 3 := Nat.sub_add_cancel hpcube
  have hvalue : (s.primes i) ^ 3 ≤ 2 * primeCubic (s.primes i) := by
    dsimp [primeCubic]
    omega
  have hupper := hw.2
  have hcoef : 5 * n - 1 ≤ 5 * n := Nat.sub_le _ _
  have hTn : T ≤ n * N ^ 3 := by
    apply Nat.le_of_mul_le_mul_left (c := 5) ?_ (by norm_num)
    calc
      5 * T ≤ (5 * n - 1) * N ^ 3 := hupper
      _ ≤ (5 * n) * N ^ 3 := Nat.mul_le_mul_right _ hcoef
      _ = 5 * (n * N ^ 3) := by ring
  calc
    T ≤ n * N ^ 3 := hTn
    _ ≤ n * (2 * (s.primes i) ^ 3) :=
      Nat.mul_le_mul_left n (by omega)
    _ ≤ n * (2 * (2 * primeCubic (s.primes i))) :=
      Nat.mul_le_mul_left n (Nat.mul_le_mul_left 2 hvalue)
    _ = 4 * n * primeCubic (s.primes i) := by ring

/-- The exact target-uniform prime-representation consequence needed from
Cook--Magyar, together with the local-density and prime-power-removal
arguments proved in this development.

For fixed `n`, `threshold n` is chosen before the varying target `q`.  The
returned scale places `T = 24q` in a fixed compact normalized-target window,
and the returned primes lie below that scale.  The lower comparability of the
primes is then proved by `OddPrimeSolution.lower_cube`, rather than included
as another analytic assumption.
-/
structure TargetUniformCookMagyarInput where
  minSummands : ℕ
  /-- This simultaneously covers prime-power removal (`n ≥ 9`) and the
  local-factor tail estimate, whose rank hypothesis requires `n > 32`. -/
  minSummands_ge_thirtyThree : 33 ≤ minSummands
  threshold : ℕ → ℕ
  representation : ∀ (n q : ℕ), minSummands ≤ n → threshold n ≤ q →
    ∃ N : ℕ, CookMagyarWindow n N (24 * q) ∧
      Nonempty (OddPrimeSolution n N (24 * q))

/-- Source-level output of the specialized circle method.  The scale
threshold is chosen before both `N` and the moving target `T`.  The result is
stated as positivity/existence in the prime-only count developed in
`CookMagyar.PrimePowerRemoval`, rather than directly as the downstream
`OddPrimeSolution` record.

The eventual proof of this structure consists of the uniform major-arc main
term, minor-arc error, singular-density lower bounds, and prime-power removal.
-/
structure CookMagyarCircleMethodInput where
  minSummands : ℕ
  minSummands_ge_thirtyThree : 33 ≤ minSummands
  scaleThreshold : ℕ → ℕ
  representation : ∀ (n N T : ℕ), minSummands ≤ n →
    scaleThreshold n ≤ N → 24 ∣ T → CookMagyarWindow n N T →
      CookMagyarCircle.IsOddPrimeCubicRepresentation n N T

/-- Uniform quantitative arc estimates imply the source-level prime
representation theorem. -/
noncomputable def CookMagyarCircle.UniformCubicCircleBounds.toCircleMethodInput
    (a : CookMagyarCircle.UniformCubicCircleBounds) :
    CookMagyarCircleMethodInput where
  minSummands := a.minSummands
  minSummands_ge_thirtyThree := a.minSummands_ge_thirtyThree
  scaleThreshold := a.scaleThreshold
  representation := by
    intro n N T hn hN hdvd hwindow
    exact (a.bounds n N T hn hN hdvd hwindow).exists_oddPrimeCubicRepresentation

/-- Choosing a common threshold and making the error margins explicit from the
analytic Cook--Magyar estimates. -/
noncomputable def cookMagyarAnalyticBounds
    (estimates : CookMagyarCircle.SeparatedCubicEstimates) :
    CookMagyarCircle.UniformCubicCircleBounds :=
  estimates.toUniformCubicCircleBounds

/-- The source-level uniform prime-representation theorem, assembled from
the quantitative analytic bounds. -/
noncomputable def cookMagyarCircleMethod
    (estimates : CookMagyarCircle.SeparatedCubicEstimates) :
    CookMagyarCircleMethodInput :=
  (cookMagyarAnalyticBounds estimates).toCircleMethodInput

/-- The source-level uniform circle theorem implies the exact target-uniform
representation API.  The scale and compact-window claims are proved by
`cubicScale_mem_window`; they are not analytic assumptions. -/
noncomputable def targetUniformCookMagyar
    (cm : CookMagyarCircleMethodInput) : TargetUniformCookMagyarInput := by
  refine
    { minSummands := cm.minSummands
      minSummands_ge_thirtyThree := cm.minSummands_ge_thirtyThree
      threshold := fun n ↦ max (cubicScaleTargetThreshold n)
        (cubicScaleTargetThresholdFor n (cm.scaleThreshold n))
      representation := ?_ }
  intro n q hn hq
  have hnpos : 0 < n := by
    have h33 : 33 ≤ cm.minSummands := cm.minSummands_ge_thirtyThree
    omega
  have hwindowTarget : cubicScaleTargetThreshold n ≤ 24 * q := by
    have hle : cubicScaleTargetThreshold n ≤ q :=
      (le_max_left _ _).trans hq
    omega
  have hsourceTarget :
      cubicScaleTargetThresholdFor n (cm.scaleThreshold n) ≤ 24 * q := by
    have hle : cubicScaleTargetThresholdFor n (cm.scaleThreshold n) ≤ q :=
      (le_max_right _ _).trans hq
    omega
  let N := cubicScale n (24 * q) hnpos
  have hwindow : CookMagyarWindow n N (24 * q) := by
    simpa [N] using cubicScale_mem_window hnpos hwindowTarget
  have hNsource : cm.scaleThreshold n ≤ N := by
    simpa [N] using
      le_cubicScale_of_targetThresholdFor hnpos hsourceTarget
  have hdvd : 24 ∣ 24 * q := ⟨q, rfl⟩
  have hrep := cm.representation n N (24 * q) hn hNsource hdvd hwindow
  exact ⟨N, hwindow, oddPrimeSolution_nonempty_of_cubicRepresentation hrep⟩

/-- The packaged arithmetic decomposition consumed by the geometric
reduction. -/
structure UniformCookMagyarInput (h : ℕ) where
  maxSummands : ℕ
  componentFraction : ℝ
  componentFraction_pos : 0 < componentFraction
  logLoss : ℝ
  decomposition : ∀ᶠ g : ℕ in atTop,
    ∃ n : ℕ, 0 < n ∧ n ≤ maxSummands ∧
      ∃ primes : Fin n → ℕ,
        (∀ i, (primes i).Prime) ∧
        (∀ i, primes i ≠ 2) ∧
        (∑ i, arithmeticGenus h (primes i)) = g ∧
        (∀ i, (1 / 3 : ℝ) * Real.log g - logLoss ≤ Real.log (primes i)) ∧
        (∀ i, componentFraction * (g : ℝ) ≤
          (arithmeticGenus h (primes i) : ℝ))

/-! ### Elementary estimates -/

/-- An arithmetic genus is at most `(h+1)p³`.  This deliberately crude
bound is enough to turn component-genus comparability into prime
comparability on the logarithmic scale. -/
theorem arithmeticGenus_le_mul_cube (h : ℕ) {p : ℕ} (hp : p.Prime) :
    arithmeticGenus h p ≤ (h + 1) * p ^ 3 := by
  have hp_one : 1 ≤ p ^ 3 := one_le_pow₀ hp.one_le
  have hcubic : normalizedPrimeCubic p ≤ p ^ 3 := by
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  dsimp [arithmeticGenus]
  calc
    h * normalizedPrimeCubic p + 1 ≤ h * p ^ 3 + p ^ 3 :=
      Nat.add_le_add (Nat.mul_le_mul_left h hcubic) hp_one
    _ = (h + 1) * p ^ 3 := by ring

/-- If one arithmetic component occupies a fixed fraction of the total
genus, its indexing prime has logarithm `(1/3) log g + O(1)`. -/
theorem log_prime_lower_of_genus_fraction
    (h : ℕ) {a : ℝ} (ha : 0 < a) {g p : ℕ} (hg : 0 < g)
    (hp : p.Prime)
    (hlarge : a * (g : ℝ) ≤ (arithmeticGenus h p : ℝ)) :
    (1 / 3 : ℝ) * Real.log g -
        Real.log (((h : ℝ) + 1) / a) / 3 ≤ Real.log p := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hfactor_pos : 0 < ((h : ℝ) + 1) / a :=
    div_pos (by positivity) ha
  have hgenus_upper :
      (arithmeticGenus h p : ℝ) ≤ ((h : ℝ) + 1) * (p : ℝ) ^ 3 := by
    exact_mod_cast arithmeticGenus_le_mul_cube h hp
  have hbound : (g : ℝ) ≤ (((h : ℝ) + 1) / a) * (p : ℝ) ^ 3 := by
    have hg_div : (g : ℝ) ≤ (arithmeticGenus h p : ℝ) / a :=
      (le_div_iff₀ ha).2 (by simpa [mul_comm] using hlarge)
    calc
      (g : ℝ) ≤ (arithmeticGenus h p : ℝ) / a := hg_div
      _ ≤ (((h : ℝ) + 1) * (p : ℝ) ^ 3) / a :=
        div_le_div_of_nonneg_right hgenus_upper ha.le
      _ = (((h : ℝ) + 1) / a) * (p : ℝ) ^ 3 := by ring
  have hlog := Real.log_le_log (by exact_mod_cast hg) hbound
  rw [Real.log_mul hfactor_pos.ne' (pow_ne_zero 3 hp_pos.ne'), Real.log_pow] at hlog
  norm_num at hlog ⊢
  linarith

/-! ### From prime representations to genus decompositions -/

noncomputable def uniformCookMagyar
    (cm : TargetUniformCookMagyarInput) (h : ℕ) (hh : 0 < h) :
    UniformCookMagyarInput h := by
  classical
  let n₀ := cm.minSummands
  let N := n₀ + h
  let thresholdSum := ∑ j ∈ Finset.range N, cm.threshold j
  let a : ℝ := 1 / (5 * (N : ℝ))
  have hn₀ : 33 ≤ n₀ := by
    simpa [n₀] using cm.minSummands_ge_thirtyThree
  have hN : 0 < N := by omega
  have ha : 0 < a := by
    dsimp [a]
    positivity
  refine
    { maxSummands := N
      componentFraction := a
      componentFraction_pos := ha
      logLoss := Real.log (((h : ℝ) + 1) / a) / 3
      decomposition := ?_ }
  filter_upwards [eventually_ge_atTop (n₀ + h * thresholdSum)] with g hg
  let q := (g - n₀) / h
  let n := n₀ + (g - n₀) % h
  have hn₀g : n₀ ≤ g := by omega
  have hr_lt : (g - n₀) % h < h := Nat.mod_lt _ hh
  have hn_pos : 0 < n := by omega
  have hn_le : n ≤ N := by omega
  have hn₀_le : cm.minSummands ≤ n := by simp [n, n₀]
  have hg_eq : g = n + h * q := by
    have hdivision := Nat.mod_add_div (g - n₀) h
    dsimp [n, q]
    omega
  have hq_ge : thresholdSum ≤ q := by
    apply (Nat.le_div_iff_mul_le hh).2
    exact Nat.le_sub_of_add_le (by simpa [mul_comm, add_comm] using hg)
  have hn_lt : n < N := by omega
  have hn_mem : n ∈ Finset.range N := Finset.mem_range.mpr hn_lt
  have hthreshold_le : cm.threshold n ≤ thresholdSum := by
    dsimp [thresholdSum]
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hn_mem
  obtain ⟨scale, hwindow, ⟨solution⟩⟩ :=
    cm.representation n q hn₀_le (hthreshold_le.trans hq_ge)
  let primes : Fin n → ℕ := solution.primes
  have hprime : ∀ i, (primes i).Prime := fun i ↦ solution.prime i
  have hodd : ∀ i, primes i ≠ 2 := fun i ↦ solution.ne_two i
  have hscale_one : 1 ≤ scale := by
    let i : Fin n := ⟨0, hn_pos⟩
    exact (solution.prime i).one_le.trans (solution.upper i)
  have hsum_raw : (∑ i, primeCubic (primes i)) = 24 * q := by
    simpa [primes] using solution.equation
  have hcomparable_raw : ∀ i,
      24 * q ≤ 4 * n * primeCubic (primes i) := fun i ↦ by
    simpa [primes] using
      solution.target_le_four_mul_primeCubic
        (by omega) hscale_one hwindow i
  have hsum : (∑ i, normalizedPrimeCubic (primes i)) = q :=
    sum_normalizedPrimeCubic_eq_of_sum_primeCubic_eq
      primes hprime hodd hsum_raw
  have hcomparable : ∀ i,
      q ≤ 4 * n * normalizedPrimeCubic (primes i) := fun i ↦
    normalized_comparable_of_primeCubic_comparable
      (hprime i) (hodd i) (hcomparable_raw i)
  have hlarge : ∀ i, a * (g : ℝ) ≤
      (arithmeticGenus h (primes i) : ℝ) := by
    intro i
    let v := normalizedPrimeCubic (primes i)
    let G := arithmeticGenus h (primes i)
    have hq_mul : h * q ≤ h * (4 * n * v) :=
      Nat.mul_le_mul_left h (hcomparable i)
    have hn_factor : 4 * n ≤ 4 * N := Nat.mul_le_mul_left 4 hn_le
    have hv_factor : h * v ≤ G := by
      dsimp [G, v, arithmeticGenus]
      omega
    have hmain : 4 * n * (h * v) ≤ 4 * N * G :=
      Nat.mul_le_mul hn_factor hv_factor
    have hG_one : 1 ≤ G := by simp [G, arithmeticGenus]
    have hn_tail : n ≤ N * G := by
      exact hn_le.trans <| by
        calc
          N = N * 1 := by simp
          _ ≤ N * G := Nat.mul_le_mul_left N hG_one
    have htotal : g ≤ 5 * N * G := by
      calc
        g = h * q + n := by omega
        _ ≤ h * (4 * n * v) + n := Nat.add_le_add_right hq_mul n
        _ = 4 * n * (h * v) + n := by ring
        _ ≤ 4 * N * G + N * G := Nat.add_le_add hmain hn_tail
        _ = 5 * N * G := by ring
    have htotal_real : (g : ℝ) ≤ 5 * (N : ℝ) * (G : ℝ) := by
      exact_mod_cast htotal
    have hden_pos : 0 < 5 * (N : ℝ) := by positivity
    change a * (g : ℝ) ≤ (G : ℝ)
    calc
      a * (g : ℝ) = (g : ℝ) / (5 * (N : ℝ)) := by
        dsimp [a]
        ring
      _ ≤ (G : ℝ) := (div_le_iff₀ hden_pos).2 <| by
        simpa [mul_comm, mul_left_comm, mul_assoc] using htotal_real
  refine ⟨n, hn_pos, hn_le, primes, hprime, hodd, ?_, ?_, ?_⟩
  · calc
      (∑ i, arithmeticGenus h (primes i)) =
          (∑ i, h * normalizedPrimeCubic (primes i)) + (∑ _i : Fin n, 1) := by
            exact Finset.sum_add_distrib
      _ = h * (∑ i, normalizedPrimeCubic (primes i)) + n := by
            rw [Finset.mul_sum]
            simp
      _ = h * q + n := by rw [hsum]
      _ = g := by omega
  · intro i
    exact log_prime_lower_of_genus_fraction h ha (by omega) (hprime i) (hlarge i)
  · exact hlarge

end SystolicGrowth
