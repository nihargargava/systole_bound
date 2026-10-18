module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.DirichletLocalGrowth
public import CookMagyar.DirichletLocalZeros
public import Mathlib.Analysis.Meromorphic.FactorizedRational
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Schwarz

@[expose] public section

/-!
# Removing the actual local zeros of a Dirichlet L-function

On the inner disk at height `τ`, the actual divisor of a nonprincipal
Dirichlet `L`-function is finite and nonnegative. The uniform center lower
bound rules out local identically-zero germs throughout the connected disk.
The pinned meromorphic factorization theorem then removes every actual
zero. Analytic continuity promotes its codiscrete equality to an exact
pointwise factorization, including at the zeros themselves.
-/

open scoped BigOperators Topology
open Filter Function Metric Set

namespace SystolicGrowth.CookMagyarCircle

variable {q : ℕ} [NeZero q]

/-- Removing all actual zeros in the disk of radius `5/4` leaves an
analytic nowhere-zero remainder, with exact pointwise factorization. -/
theorem exists_dirichlet_LFunction_local_factorization
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ) :
    (MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
      (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ))).support.Finite ∧
    0 ≤ MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
      (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) ∧
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) ∧
      (∀ s ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ), g s ≠ 0) ∧
      ∀ s ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ),
        DirichletCharacter.LFunction χ s =
          (∏ᶠ u : ℂ, (s - u) ^ (MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
            (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u)) * g s := by
  let c : ℂ := 2 + (τ : ℂ) * Complex.I
  let U : Set ℂ := ball c (5 / 4 : ℝ)
  let f : ℂ → ℂ := DirichletCharacter.LFunction χ
  have hf (s : ℂ) : AnalyticAt ℂ f s :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have hfU : AnalyticOnNhd ℂ f U := fun s _ => hf s
  have hfinite : (MeromorphicOn.divisor f U).support.Finite :=
    MeromorphicOn.divisor_ball_support_finite (fun s _ => (hf s).meromorphicAt)
  have hnonneg : 0 ≤ MeromorphicOn.divisor f U :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfU
  have hcU : c ∈ U := mem_ball_self (by norm_num)
  have hfc : f c ≠ 0 := by
    intro hzero
    have hlower := dirichlet_LFunction_center_norm_lower χ τ
    change (1 / 4 : ℝ) ≤ ‖f c‖ at hlower
    rw [hzero, norm_zero] at hlower
    norm_num at hlower
  have hcorder : meromorphicOrderAt f c ≠ ⊤ := by
    have heq : meromorphicOrderAt f c = 0 :=
      (hf c).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfc
    rw [heq]
    exact WithTop.zero_ne_top
  have horder : ∀ u : U, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    exact hfU.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_ball hcU u.property hcorder
  obtain ⟨g, hg, hgz, hcodiscrete⟩ :=
    hfU.meromorphicOn.extract_zeros_poles horder hfinite
  refine ⟨hfinite, hnonneg, g, hg, ?_, ?_⟩
  · intro s hs
    exact hgz ⟨s, hs⟩
  · intro s hs
    let φ : ℂ → ℂ := ∏ᶠ u, (· - u) ^ MeromorphicOn.divisor f U u
    have hφ : AnalyticAt ℂ φ s := Function.FactorizedRational.analyticAt (hnonneg s)
    have hprod : AnalyticAt ℂ (φ * g) s := hφ.mul (hg s hs)
    have heqNE : f =ᶠ[𝓝[≠] s] φ * g :=
      (hf s).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
        hprod.meromorphicAt hs isOpen_ball.preperfect hcodiscrete
    have heq : f s = (φ * g) s :=
      ((hf s).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
        hprod.continuousAt).mp heqNE |>.eq_of_nhds
    change f s = (∏ᶠ u : ℂ, (s - u) ^ MeromorphicOn.divisor f U u) * g s
    rw [heq]
    simpa only [φ, Pi.mul_apply] using
      congrArg (fun z : ℂ => z * g s)
        (congrFun (Function.FactorizedRational.finprod_eq_fun hfinite) s)

private theorem logDeriv_factorizedRational
    (D : ℂ → ℤ) (hD : D.HasFiniteSupport) (hD0 : ∀ u, 0 ≤ D u) (s : ℂ)
    (hs : (∏ᶠ u, (· - u) ^ D u) s ≠ 0) :
    logDeriv (∏ᶠ u, (· - u) ^ D u) s = ∑ᶠ u, (D u : ℂ) / (s - u) := by
  classical
  have hfun : (∏ᶠ u, (· - u) ^ D u) =
      fun z => ∏ u ∈ hD.toFinset, (z - u) ^ D u := by
    rw [Function.FactorizedRational.finprod_eq_fun hD]
    funext z
    apply finprod_eq_prod_of_mulSupport_subset
    intro u hu
    have hDu : D u ≠ 0 := by
      intro hzero
      exact hu (by simp [hzero])
    exact (Set.Finite.mem_toFinset hD).mpr hDu
  rw [hfun] at hs ⊢
  rw [logDeriv_fun_prod (s := hD.toFinset) (f := fun u z : ℂ => (z - u) ^ D u)
    (x := s) (fun u hu => (Finset.prod_ne_zero_iff.mp hs) u hu)
    (fun u _ => ((analyticAt_id.sub analyticAt_const).fun_zpow_nonneg
      (hD0 u)).differentiableAt)]
  calc
    _ = ∑ u ∈ hD.toFinset, (D u : ℂ) / (s - u) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [logDeriv_fun_zpow (by fun_prop)]
      simp [logDeriv_apply, div_eq_mul_inv]
    _ = ∑ᶠ u, (D u : ℂ) / (s - u) := by
      symm
      apply finsum_eq_sum_of_support_subset
      intro u hu
      have hDu : D u ≠ 0 := by
        intro hzero
        exact hu (by simp [hzero])
      exact (Set.Finite.mem_toFinset hD).mpr hDu

/-- The same actual local factorization gives its exact logarithmic
derivative at every point where the actual `L`-function is nonzero. -/
theorem exists_dirichlet_LFunction_local_factorization_logDeriv
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) ∧
      (∀ s ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ), g s ≠ 0) ∧
      (∀ s ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ),
        DirichletCharacter.LFunction χ s =
          (∏ᶠ u : ℂ, (s - u) ^ (MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
            (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u)) * g s) ∧
      ∀ s ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ),
        DirichletCharacter.LFunction χ s ≠ 0 →
          logDeriv (DirichletCharacter.LFunction χ) s =
            (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
              (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) / (s - u)) +
              logDeriv g s := by
  obtain ⟨hfinite, hnonneg, g, hg, hgz, hfg⟩ :=
    exists_dirichlet_LFunction_local_factorization χ hχ τ
  refine ⟨g, hg, hgz, hfg, ?_⟩
  intro s hs hsne
  let U : Set ℂ := ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)
  let f : ℂ → ℂ := DirichletCharacter.LFunction χ
  let D : ℂ → ℤ := MeromorphicOn.divisor f U
  let φ : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u
  have hfactor (z : ℂ) (hz : z ∈ U) : f z = φ z * g z := by
    have heval : φ z = ∏ᶠ u : ℂ, (z - u) ^ D u :=
      congrFun (Function.FactorizedRational.finprod_eq_fun (d := D) hfinite) z
    rw [heval]
    exact hfg z hz
  have hφne : φ s ≠ 0 := by
    intro hzero
    change f s ≠ 0 at hsne
    exact hsne (by rw [hfactor s hs, hzero, zero_mul])
  have hφ : AnalyticAt ℂ φ s := Function.FactorizedRational.analyticAt (hnonneg s)
  have heq : f =ᶠ[𝓝 s] fun z => φ z * g z := by
    filter_upwards [isOpen_ball.mem_nhds hs] with z hz
    exact hfactor z hz
  change logDeriv f s = (∑ᶠ u : ℂ, (D u : ℂ) / (s - u)) + logDeriv g s
  calc
    _ = logDeriv (fun z => φ z * g z) s := by
      simp only [logDeriv_apply]
      rw [heq.deriv_eq, heq.eq_of_nhds]
    _ = logDeriv φ s + logDeriv g s :=
      logDeriv_mul s hφne (hgz s hs) hφ.differentiableAt (hg s hs).differentiableAt
    _ = _ := by
      rw [logDeriv_factorizedRational D hfinite (fun u => hnonneg u) s hφne]

/-- On `Re(s)>1`, actual Dirichlet nonvanishing discharges the pointwise
nonzero condition in the exact local logarithmic-derivative decomposition. -/
theorem exists_dirichlet_LFunction_local_logDeriv_of_one_lt_re
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) ∧
      (∀ s ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ), g s ≠ 0) ∧
      (∀ s ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ),
        DirichletCharacter.LFunction χ s =
          (∏ᶠ u : ℂ, (s - u) ^ (MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
            (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u)) * g s) ∧
      ∀ s ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ), 1 < s.re →
        logDeriv (DirichletCharacter.LFunction χ) s =
          (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
            (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) / (s - u)) +
            logDeriv g s := by
  obtain ⟨g, hg, hgz, hfg, hlogDeriv⟩ :=
    exists_dirichlet_LFunction_local_factorization_logDeriv χ hχ τ
  refine ⟨g, hg, hgz, hfg, ?_⟩
  intro s hs hre
  apply hlogDeriv s hs
  rw [χ.LFunction_eq_LSeries hre]
  exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hre

private theorem norm_factorizedRational_center_le_rpow_aux
    (D : ℂ → ℤ) (hD : D.HasFiniteSupport)
    (hDnonneg : ∀ u, 0 ≤ D u) (c : ℂ)
    (hbound : ∀ u, D u ≠ 0 → ‖c - u‖ ≤ 5 / 4) :
    ‖(∏ᶠ u : ℂ, (c - u) ^ D u)‖ ≤
      (5 / 4 : ℝ) ^ (∑ u ∈ hD.toFinset, (D u).toNat) := by
  have heval : (∏ᶠ u : ℂ, (c - u) ^ D u) =
      ∏ u ∈ hD.toFinset, (c - u) ^ D u := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro u hu
    have hDu : D u ≠ 0 := by
      intro hzero
      exact hu (by simp [hzero])
    exact (Set.Finite.mem_toFinset hD).mpr hDu
  rw [heval, norm_prod]
  simp only [norm_zpow]
  calc
    ∏ u ∈ hD.toFinset, ‖c - u‖ ^ D u ≤
        ∏ u ∈ hD.toFinset, (5 / 4 : ℝ) ^ (D u).toNat := by
      apply Finset.prod_le_prod₀ (fun u hu => by positivity)
      intro u hu
      rw [← Int.toNat_of_nonneg (hDnonneg u)]
      exact zpow_le_zpow_left₀ (by positivity) (norm_nonneg _)
        (hbound u (by
          intro hzero
          have hu' : u ∈ Function.support D :=
            (Set.Finite.mem_toFinset hD).mp hu
          exact hu' (by simp [hzero])))
    _ = (5 / 4 : ℝ) ^ (∑ u ∈ hD.toFinset, (D u).toNat) := by
      rw [Finset.prod_pow_eq_pow_sum]

private theorem norm_factorizedRational_center_le_rpow
    (D : ℂ → ℤ) (hD : D.HasFiniteSupport)
    (hDnonneg : ∀ u, 0 ≤ D u) (c : ℂ)
    (hbound : ∀ u, D u ≠ 0 → ‖c - u‖ ≤ 5 / 4) (J : ℝ)
    (hmass : (∑ u ∈ hD.toFinset, (D u : ℝ)) ≤ J) :
    ‖(∏ᶠ u : ℂ, (c - u) ^ D u)‖ ≤ (5 / 4 : ℝ) ^ J := by
  have hmassNat : (∑ u ∈ hD.toFinset, (D u).toNat : ℝ) ≤ J := by
    calc
      _ = ∑ u ∈ hD.toFinset, (D u : ℝ) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact_mod_cast Int.toNat_of_nonneg (hDnonneg u)
      _ ≤ J := hmass
  calc
    _ ≤ (5 / 4 : ℝ) ^ (∑ u ∈ hD.toFinset, (D u).toNat) :=
      norm_factorizedRational_center_le_rpow_aux D hD hDnonneg c hbound
    _ = (5 / 4 : ℝ) ^ (∑ u ∈ hD.toFinset, (D u).toNat : ℝ) := by
      rw [← Nat.cast_sum, Real.rpow_natCast]
    _ ≤ (5 / 4 : ℝ) ^ J :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hmassNat

private theorem quotient_center_lower_of_factorization
    {L g : ℂ → ℂ} (D : ℂ → ℤ) (c : ℂ) (J : ℝ)
    (hfactor : L c = (∏ᶠ u : ℂ, (c - u) ^ D u) * g c)
    (hL : (1 / 4 : ℝ) ≤ ‖L c‖)
    (hφpos : 0 < ‖∏ᶠ u : ℂ, (c - u) ^ D u‖)
    (hφbound : ‖∏ᶠ u : ℂ, (c - u) ^ D u‖ ≤ (5 / 4 : ℝ) ^ J) :
    (1 / 4 : ℝ) * (5 / 4 : ℝ) ^ (-J) ≤ ‖g c‖ := by
  have hnorm : ‖L c‖ =
      ‖∏ᶠ u : ℂ, (c - u) ^ D u‖ * ‖g c‖ := by
    rw [hfactor, norm_mul]
  have hquot : ‖L c‖ / ‖∏ᶠ u : ℂ, (c - u) ^ D u‖ = ‖g c‖ := by
    rw [hnorm]
    field_simp
  have hlow : (1 / 4 : ℝ) / ((5 / 4 : ℝ) ^ J) ≤ ‖g c‖ := by
    calc
      (1 / 4 : ℝ) / ((5 / 4 : ℝ) ^ J) ≤
          (1 / 4 : ℝ) / ‖∏ᶠ u : ℂ, (c - u) ^ D u‖ :=
        div_le_div_of_nonneg_left (by norm_num) hφpos hφbound
      _ ≤ ‖L c‖ / ‖∏ᶠ u : ℂ, (c - u) ^ D u‖ :=
        div_le_div_of_nonneg_right hL hφpos.le
      _ = ‖g c‖ := hquot
  rw [Real.rpow_neg (by norm_num : 0 ≤ (5 / 4 : ℝ)) J, div_eq_mul_inv]
  simpa only [div_eq_mul_inv] using hlow

/-- The nonvanishing remainder in the actual radius-`5/4` factorization has
a quantitative center lower bound. It follows from the actual L-function
center lower bound and Jensen's multiplicity bound; no lower-bound hypothesis
on the remainder is assumed. -/
theorem exists_dirichlet_LFunction_local_factorization_center_lower
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) ∧
      (∀ s ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ), g s ≠ 0) ∧
      (∀ s ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ),
        DirichletCharacter.LFunction χ s =
          (∏ᶠ u : ℂ, (s - u) ^ (MeromorphicOn.divisor
            (DirichletCharacter.LFunction χ)
            (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u)) * g s) ∧
      (1 / 4 : ℝ) * (5 / 4 : ℝ) ^
        (-(Real.log (28 * (q : ℝ) * (|τ| + 2)) /
          Real.log (6 / 5 : ℝ))) ≤ ‖g (2 + (τ : ℂ) * Complex.I)‖ := by
  obtain ⟨hfinite, hnonneg, g, hg, hgz, hfg⟩ :=
    exists_dirichlet_LFunction_local_factorization χ hχ τ
  let c : ℂ := 2 + (τ : ℂ) * Complex.I
  let U : Set ℂ := ball c (5 / 4 : ℝ)
  let f : ℂ → ℂ := DirichletCharacter.LFunction χ
  let D : ℂ → ℤ := MeromorphicOn.divisor f U
  let Dc : ℂ → ℤ := MeromorphicOn.divisor f (closedBall c (5 / 4 : ℝ))
  let Z : Finset ℂ := dirichletLocalZeros χ τ
  let J : ℝ := Real.log (28 * (q : ℝ) * (|τ| + 2)) /
    Real.log (6 / 5 : ℝ)
  have hfU : AnalyticOnNhd ℂ f U := by
    intro z hz
    exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hfC : AnalyticOnNhd ℂ f (closedBall c (5 / 4 : ℝ)) := by
    intro z hz
    exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hDfinite : D.HasFiniteSupport := hfinite
  have hDnonneg : ∀ u, 0 ≤ D u := fun u =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfU u
  have hsumDc : (∑ u ∈ Z, (Dc u : ℝ)) ≤ J := by
    have hsumD : (∑ u ∈ Z, Dc u : ℤ) ≤ J := by
      have hfiniteSum : (∑ᶠ u : ℂ, Dc u) = ∑ u ∈ Z, Dc u := by
        apply finsum_eq_sum_of_support_subset
        intro u hu
        have hu' : u ∈ Function.support Dc := hu
        change u ∈ Z
        simpa only [Z, dirichletLocalZeros, Set.Finite.mem_toFinset] using hu'
      rw [← hfiniteSum]
      simpa only [Dc, c, f, J] using
        (dirichlet_LFunction_local_sum_divisor_le χ hχ τ)
    exact_mod_cast hsumD
  have hmass : (∑ u ∈ hfinite.toFinset, (D u : ℝ)) ≤ J := by
    calc
      _ = ∑ u ∈ hfinite.toFinset, (Dc u : ℝ) := by
        apply Finset.sum_congr rfl
        intro u hu
        have huSupport : u ∈ Function.support D :=
          (Set.Finite.mem_toFinset hfinite).mp hu
        have huD : D u ≠ 0 := Function.mem_support.mp huSupport
        have huU : u ∈ U := by
          by_contra huNot
          have hz : D u = 0 := by simp [D, huNot]
          exact huD hz
        have huC : u ∈ closedBall c (5 / 4 : ℝ) :=
          Metric.mem_closedBall.mpr (Metric.mem_ball.mp huU).le
        have hsame : D u = Dc u := by
          change MeromorphicOn.divisor f U u =
            MeromorphicOn.divisor f (closedBall c (5 / 4 : ℝ)) u
          rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfU huU,
            MeromorphicOn.AnalyticOnNhd.divisor_apply hfC huC]
        rw [hsame]
      _ ≤ ∑ u ∈ Z, (Dc u : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro u hu
          have huSupport : u ∈ Function.support D :=
            (Set.Finite.mem_toFinset hfinite).mp hu
          have huD : D u ≠ 0 := Function.mem_support.mp huSupport
          have huU : u ∈ U := by
            by_contra huNot
            have hz : D u = 0 := by simp [D, huNot]
            exact huD hz
          have huC : u ∈ closedBall c (5 / 4 : ℝ) :=
            Metric.mem_closedBall.mpr (Metric.mem_ball.mp huU).le
          have hsame : D u = Dc u := by
            change MeromorphicOn.divisor f U u =
              MeromorphicOn.divisor f (closedBall c (5 / 4 : ℝ)) u
            rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfU huU,
              MeromorphicOn.AnalyticOnNhd.divisor_apply hfC huC]
          have hDc : Dc u ≠ 0 := hsame ▸ huD
          change u ∈ dirichletLocalZeros χ τ
          have huSuppC : u ∈ Function.support Dc := Function.mem_support.mpr hDc
          simpa only [Z, dirichletLocalZeros, Set.Finite.mem_toFinset] using huSuppC
        · intro u huZ huNotS
          have huZ' : u ∈ dirichletLocalZeros χ τ := by simpa [Z] using huZ
          have hmem : u ∈ closedBall c (5 / 4 : ℝ) :=
            (mem_dirichletLocalZeros_iff χ hχ τ u).mp huZ' |>.1
          exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfC u
      _ ≤ J := hsumDc
  have hbound (u : ℂ) (huD : D u ≠ 0) : ‖c - u‖ ≤ 5 / 4 := by
    have huU : u ∈ U := by
      by_contra huNot
      have hz : D u = 0 := by simp [D, huNot]
      exact huD hz
    calc
      ‖c - u‖ = dist c u := by rw [← dist_eq_norm]
      _ = dist u c := dist_comm _ _
      _ ≤ 5 / 4 := (Metric.mem_ball.mp huU).le
  have hphiBound := norm_factorizedRational_center_le_rpow
    D hDfinite hDnonneg c hbound J hmass
  have hc : c ∈ U := mem_ball_self (by norm_num)
  have hfc := dirichlet_LFunction_center_norm_lower χ τ
  change (1 / 4 : ℝ) ≤ ‖DirichletCharacter.LFunction χ c‖ at hfc
  have hfact := hfg c hc
  have hphine : (∏ᶠ u : ℂ, (c - u) ^ D u) ≠ 0 := by
    intro hzero
    change DirichletCharacter.LFunction χ c = _ at hfact
    rw [hzero, zero_mul] at hfact
    rw [hfact] at hfc
    norm_num at hfc
  have hphipos : 0 < ‖∏ᶠ u : ℂ, (c - u) ^ D u‖ := norm_pos_iff.mpr hphine
  have hlower := quotient_center_lower_of_factorization D c J hfact hfc hphipos hphiBound
  refine ⟨g, hg, hgz, hfg, ?_⟩
  simpa [c, D, U, f, J] using hlower

private theorem factor_norm_lower_on_outer_sphere
    (D : ℂ → ℤ) (hD : D.HasFiniteSupport)
    (hDnonneg : ∀ u, 0 ≤ D u) (c s : ℂ) (J : ℝ)
    (hroot : ∀ u, D u ≠ 0 → dist u c < 5 / 4)
    (hs : dist s c = 3 / 2)
    (hmass : (∑ u ∈ hD.toFinset, (D u : ℝ)) ≤ J) :
    (1 / 4 : ℝ) ^ J ≤ ‖(∏ᶠ u : ℂ, (s - u) ^ D u)‖ := by
  have heval : (∏ᶠ u : ℂ, (s - u) ^ D u) =
      ∏ u ∈ hD.toFinset, (s - u) ^ D u := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro u hu
    have hDu : D u ≠ 0 := by
      intro hzero
      exact hu (by simp [hzero])
    exact (Set.Finite.mem_toFinset hD).mpr hDu
  have hmassNat : (∑ u ∈ hD.toFinset, (D u).toNat : ℝ) ≤ J := by
    calc
      _ = ∑ u ∈ hD.toFinset, (D u : ℝ) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact_mod_cast Int.toNat_of_nonneg (hDnonneg u)
      _ ≤ J := hmass
  have hbase (x : ℝ) : (1 / 4 : ℝ) ^ x = (4 : ℝ) ^ (-x) := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num)]
    rw [← Real.rpow_neg (by norm_num : 0 ≤ (4 : ℝ)) x]
  have hpow : (4 : ℝ) ^ (∑ u ∈ hD.toFinset, (D u).toNat : ℝ) ≤ (4 : ℝ) ^ J :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hmassNat
  have hpow' : (4 : ℝ) ^ (-J) ≤
      (4 : ℝ) ^ (-(∑ u ∈ hD.toFinset, (D u).toNat : ℝ)) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [heval, norm_prod]
  simp only [norm_zpow]
  calc
    _ ≥ ∏ u ∈ hD.toFinset, (1 / 4 : ℝ) ^ D u := by
      apply Finset.prod_le_prod₀ (fun u hu => by positivity)
      intro u hu
      have huSupport : u ∈ Function.support D :=
        (Set.Finite.mem_toFinset hD).mp hu
      have hDu : D u ≠ 0 := Function.mem_support.mp huSupport
      have hdist : (1 / 4 : ℝ) ≤ ‖s - u‖ := by
        have hu' := hroot u hDu
        have htri := dist_triangle s u c
        rw [hs] at htri
        have hdist' : (1 / 4 : ℝ) ≤ dist s u := by linarith
        simpa only [dist_eq_norm] using hdist'
      exact zpow_le_zpow_left₀ (hDnonneg u) (by positivity) hdist
    _ = ∏ u ∈ hD.toFinset, (1 / 4 : ℝ) ^ (D u).toNat := by
      apply Finset.prod_congr rfl
      intro u hu
      nth_rewrite 1 [← Int.toNat_of_nonneg (hDnonneg u)]
      norm_cast
    _ = (1 / 4 : ℝ) ^ (∑ u ∈ hD.toFinset, (D u).toNat) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ = (1 / 4 : ℝ) ^ (∑ u ∈ hD.toFinset, (D u).toNat : ℝ) := by
      rw [← Nat.cast_sum, Real.rpow_natCast]
    _ = (4 : ℝ) ^ (-(∑ u ∈ hD.toFinset, (D u).toNat : ℝ)) := hbase _
    _ ≥ (4 : ℝ) ^ (-J) := hpow'
    _ = (1 / 4 : ℝ) ^ J := (hbase J).symm

private theorem extend_local_factorization_remainder
    {f g : ℂ → ℂ} {D : ℂ → ℤ} {c : ℂ}
    (hD : D.HasFiniteSupport) (hDnonneg : ∀ u, 0 ≤ D u)
    (hroot : ∀ u, D u ≠ 0 → dist u c < 5 / 4)
    (hf : ∀ z, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ ball c (5 / 4 : ℝ), AnalyticAt ℂ g z)
    (hfactor : ∀ z ∈ ball c (5 / 4 : ℝ),
      f z = (∏ᶠ u : ℂ, (z - u) ^ D u) * g z) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G Set.univ ∧
      (∀ z ∈ ball c (5 / 4 : ℝ), G z = g z) ∧
      (∀ z ∉ ball c (5 / 4 : ℝ),
        G z = f z / (∏ᶠ u : ℂ, (z - u) ^ D u)) := by
  let φ : ℂ → ℂ := ∏ᶠ u : ℂ, (· - u) ^ D u
  let G : ℂ → ℂ := fun z => if φ z = 0 then g z else f z / φ z
  have hφ (z : ℂ) : AnalyticAt ℂ φ z := Function.FactorizedRational.analyticAt (hDnonneg z)
  have hinside (z : ℂ) (hz : z ∈ ball c (5 / 4 : ℝ)) : G z = g z := by
    by_cases hzero : φ z = 0
    · simp [G, hzero]
    · have hfac := hfactor z hz
      have hφeval : φ z = ∏ᶠ u : ℂ, (z - u) ^ D u :=
        congrFun (Function.FactorizedRational.finprod_eq_fun hD) z
      rw [← hφeval] at hfac
      change f z = φ z * g z at hfac
      have hdivide : f z / φ z = g z := by
        rw [hfac]
        field_simp
      simp [G, hzero, hdivide]
  have houtsidePhi (z : ℂ) (hz : z ∉ ball c (5 / 4 : ℝ)) : φ z ≠ 0 := by
    have hDz : D z = 0 := by
      by_contra hne
      have hrootz := hroot z hne
      exact hz (Metric.mem_ball.mpr hrootz)
    exact Function.FactorizedRational.ne_zero hDz
  refine ⟨G, ?_, ?_, ?_⟩
  · intro z _
    by_cases hz : z ∈ ball c (5 / 4 : ℝ)
    · have heq : G =ᶠ[𝓝 z] g := by
        filter_upwards [isOpen_ball.mem_nhds hz] with w hw
        exact hinside w hw
      exact (hg z hz).congr heq.symm
    · have hφz := houtsidePhi z hz
      have hφne : ∀ᶠ w in 𝓝 z, φ w ≠ 0 := (hφ z).continuousAt.eventually_ne hφz
      have heq : G =ᶠ[𝓝 z] fun w => f w / φ w := by
        filter_upwards [hφne] with w hw
        simp [G, hw]
      exact ((hf z).div (hφ z) hφz).congr heq.symm
  · exact fun z hz => hinside z hz
  · intro z hz
    have hφz := houtsidePhi z hz
    simp [G, hφz]
    congr 1
    exact congrFun (Function.FactorizedRational.finprod_eq_fun hD) z

private theorem local_factorization_remainder_supnorm
    {f g : ℂ → ℂ} {D : ℂ → ℤ} {c : ℂ} {M J : ℝ}
    (hD : D.HasFiniteSupport) (hDnonneg : ∀ u, 0 ≤ D u)
    (hroot : ∀ u, D u ≠ 0 → dist u c < 5 / 4)
    (hf : ∀ z, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ ball c (5 / 4 : ℝ), AnalyticAt ℂ g z)
    (hfactor : ∀ z ∈ ball c (5 / 4 : ℝ),
      f z = (∏ᶠ u : ℂ, (z - u) ^ D u) * g z)
    (hgrowth : ∀ z ∈ closedBall c (3 / 2 : ℝ), ‖f z‖ ≤ M)
    (hmass : (∑ u ∈ hD.toFinset, (D u : ℝ)) ≤ J) :
    ∀ z ∈ ball c (5 / 4 : ℝ), ‖g z‖ ≤ M / ((1 / 4 : ℝ) ^ J) := by
  obtain ⟨G, hGanalytic, hGinner, hGouter⟩ :=
    extend_local_factorization_remainder hD hDnonneg hroot hf hg hfactor
  let φ : ℂ → ℂ := ∏ᶠ u : ℂ, (· - u) ^ D u
  have hGDiff : DifferentiableOn ℂ G Set.univ := by
    intro z hz
    exact (hGanalytic z (by trivial)).differentiableAt.differentiableWithinAt
  have hdiffCont : DiffContOnCl ℂ G (ball c (3 / 2 : ℝ)) :=
    hGDiff.diffContOnCl_ball (c := c) (R := 3 / 2) (by intro z hz; trivial)
  have hboundary (z : ℂ) (hz : z ∈ frontier (ball c (3 / 2 : ℝ))) :
      ‖G z‖ ≤ M / ((1 / 4 : ℝ) ^ J) := by
    have hzSphere : z ∈ sphere c (3 / 2 : ℝ) := frontier_ball_subset_sphere hz
    have hs : dist z c = 3 / 2 := Metric.mem_sphere.mp hzSphere
    have hout : z ∉ ball c (5 / 4 : ℝ) := by
      intro hzInner
      have : dist z c < 5 / 4 := Metric.mem_ball.mp hzInner
      linarith
    have hrootnorm := factor_norm_lower_on_outer_sphere D hD hDnonneg c z J hroot hs hmass
    have hφnormpos : 0 < ‖φ z‖ := norm_pos_iff.mpr (by
      have hDz : D z = 0 := by
        by_contra hn
        exact hout (Metric.mem_ball.mpr (hroot z hn))
      exact Function.FactorizedRational.ne_zero hDz)
    have hφnorm : (1 / 4 : ℝ) ^ J ≤ ‖φ z‖ := by
      simpa only [φ, Function.FactorizedRational.finprod_eq_fun hD] using hrootnorm
    have hGquot : G z = f z / φ z := by
      rw [hGouter z hout]
      congr 1
      exact (congrFun (Function.FactorizedRational.finprod_eq_fun hD) z).symm
    have hquot : ‖f z / φ z‖ ≤ M / ((1 / 4 : ℝ) ^ J) := by
      rw [norm_div]
      have hMnonneg : 0 ≤ M := le_trans (norm_nonneg (f c))
        (hgrowth c (Metric.mem_closedBall.mpr (by simp; norm_num)))
      exact div_le_div₀ hMnonneg
        (hgrowth z (Metric.mem_closedBall.mpr (by simp [hs])))
        (Real.rpow_pos_of_pos (by norm_num) J) hφnorm
    rw [hGquot]
    exact hquot
  intro z hz
  have hzOuter : z ∈ ball c (3 / 2 : ℝ) := by
    apply Metric.mem_ball.mpr
    have hz' := Metric.mem_ball.mp hz
    linarith
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le
    isBounded_ball hdiffCont hboundary (subset_closure hzOuter)
  rw [← hGinner z hz]
  exact hmax

/-- Uniformly bound the actual nonvanishing remainder of the Dirichlet
L-function local factorization. The proof analytically extends the quotient
outside the zero disk and applies maximum modulus on the radius-`3/2` disk. -/
theorem dirichlet_LFunction_local_remainder_norm_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ)
    (g : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)))
    (hfactor : ∀ s ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ),
      DirichletCharacter.LFunction χ s =
        (∏ᶠ u : ℂ, (s - u) ^ (MeromorphicOn.divisor
          (DirichletCharacter.LFunction χ)
          (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u)) * g s) :
    ∀ s ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ),
      ‖g s‖ ≤ (7 * (q : ℝ) * (|τ| + 2)) /
        ((1 / 4 : ℝ) ^ (Real.log (28 * (q : ℝ) * (|τ| + 2)) /
          Real.log (6 / 5 : ℝ))) := by
  let c : ℂ := 2 + (τ : ℂ) * Complex.I
  let U : Set ℂ := ball c (5 / 4 : ℝ)
  let f : ℂ → ℂ := DirichletCharacter.LFunction χ
  let D : ℂ → ℤ := MeromorphicOn.divisor f U
  let Dc : ℂ → ℤ := MeromorphicOn.divisor f (closedBall c (5 / 4 : ℝ))
  let Z : Finset ℂ := dirichletLocalZeros χ τ
  let J : ℝ := Real.log (28 * (q : ℝ) * (|τ| + 2)) /
    Real.log (6 / 5 : ℝ)
  have hfU : AnalyticOnNhd ℂ f U := by
    intro z hz
    exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hfC : AnalyticOnNhd ℂ f (closedBall c (5 / 4 : ℝ)) := by
    intro z hz
    exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hfinite : (MeromorphicOn.divisor f U).support.Finite :=
    MeromorphicOn.divisor_ball_support_finite (fun z _ =>
      (DirichletCharacter.differentiable_LFunction hχ).analyticAt z |>.meromorphicAt)
  have hDfinite : D.HasFiniteSupport := hfinite
  have hDnonneg : ∀ u, 0 ≤ D u := fun u =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfU u
  have hsumDc : (∑ u ∈ Z, (Dc u : ℝ)) ≤ J := by
    have hsumD : (∑ u ∈ Z, Dc u : ℤ) ≤ J := by
      have hfiniteSum : (∑ᶠ u : ℂ, Dc u) = ∑ u ∈ Z, Dc u := by
        apply finsum_eq_sum_of_support_subset
        intro u hu
        have hu' : u ∈ Function.support Dc := hu
        change u ∈ Z
        simpa only [Z, dirichletLocalZeros, Set.Finite.mem_toFinset] using hu'
      rw [← hfiniteSum]
      simpa only [Dc, c, f, J] using
        (dirichlet_LFunction_local_sum_divisor_le χ hχ τ)
    exact_mod_cast hsumD
  have hmass : (∑ u ∈ hfinite.toFinset, (D u : ℝ)) ≤ J := by
    calc
      _ = ∑ u ∈ hfinite.toFinset, (Dc u : ℝ) := by
        apply Finset.sum_congr rfl
        intro u hu
        have huSupport : u ∈ Function.support D :=
          (Set.Finite.mem_toFinset hfinite).mp hu
        have huD : D u ≠ 0 := Function.mem_support.mp huSupport
        have huU : u ∈ U := by
          by_contra huNot
          have hz : D u = 0 := by simp [D, huNot]
          exact huD hz
        have huC : u ∈ closedBall c (5 / 4 : ℝ) :=
          Metric.mem_closedBall.mpr (Metric.mem_ball.mp huU).le
        have hsame : D u = Dc u := by
          change MeromorphicOn.divisor f U u =
            MeromorphicOn.divisor f (closedBall c (5 / 4 : ℝ)) u
          rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfU huU,
            MeromorphicOn.AnalyticOnNhd.divisor_apply hfC huC]
        rw [hsame]
      _ ≤ ∑ u ∈ Z, (Dc u : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro u hu
          have huSupport : u ∈ Function.support D :=
            (Set.Finite.mem_toFinset hfinite).mp hu
          have huD : D u ≠ 0 := Function.mem_support.mp huSupport
          have huU : u ∈ U := by
            by_contra huNot
            have hz : D u = 0 := by simp [D, huNot]
            exact huD hz
          have huC : u ∈ closedBall c (5 / 4 : ℝ) :=
            Metric.mem_closedBall.mpr (Metric.mem_ball.mp huU).le
          have hsame : D u = Dc u := by
            change MeromorphicOn.divisor f U u =
              MeromorphicOn.divisor f (closedBall c (5 / 4 : ℝ)) u
            rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfU huU,
              MeromorphicOn.AnalyticOnNhd.divisor_apply hfC huC]
          have hDc : Dc u ≠ 0 := hsame ▸ huD
          change u ∈ dirichletLocalZeros χ τ
          have huSuppC : u ∈ Function.support Dc := Function.mem_support.mpr hDc
          simpa only [Z, dirichletLocalZeros, Set.Finite.mem_toFinset] using huSuppC
        · intro u huZ huNotS
          have huZ' : u ∈ dirichletLocalZeros χ τ := by simpa [Z] using huZ
          have hmem : u ∈ closedBall c (5 / 4 : ℝ) :=
            (mem_dirichletLocalZeros_iff χ hχ τ u).mp huZ' |>.1
          exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfC u
      _ ≤ J := hsumDc
  have hroot (u : ℂ) (huD : D u ≠ 0) : dist u c < 5 / 4 := by
    have huU : u ∈ U := by
      by_contra huNot
      have hz : D u = 0 := by simp [D, huNot]
      exact huD hz
    exact Metric.mem_ball.mp huU
  have hfanalytic (z : ℂ) : AnalyticAt ℂ f z :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hg' (z : ℂ) (hz : z ∈ U) : AnalyticAt ℂ g z := hg z hz
  have hfactor' (z : ℂ) (hz : z ∈ U) :
      f z = (∏ᶠ u : ℂ, (z - u) ^ D u) * g z := by
    simpa only [f, D, U, c] using hfactor z hz
  have hgrowth (z : ℂ) (hz : z ∈ closedBall c (3 / 2 : ℝ)) :
      ‖f z‖ ≤ 7 * (q : ℝ) * (|τ| + 2) := by
    simpa only [f, c] using dirichlet_LFunction_norm_le_shifted_disk χ hχ τ hz
  have hresult := local_factorization_remainder_supnorm hDfinite hDnonneg
    hroot hfanalytic hg' hfactor' hgrowth hmass
  simpa [c, U, J, f] using hresult

/-- Quantitative logarithmic-derivative bound for a zero-free analytic
function on a disk. The only size inputs are a uniform upper bound and a
positive lower bound at the disk center; no lower bound away from the center
and no derivative estimate is assumed. The proof takes a primitive of `g'/g`,
normalizes it to vanish at the center, controls its real part from the norm
ratio, applies Borel--Carathéodory, then Schwarz on a small disk around each
target point. -/
theorem norm_logDeriv_le_of_analyticOnNhd_nonzero_centerBound
    {g : ℂ → ℂ} {c : ℂ} {R r M m : ℝ}
    (hR : 0 < R) (_hr : 0 ≤ r) (hrR : r < R)
    (hg : AnalyticOnNhd ℂ g (ball c R))
    (hgne : ∀ z ∈ ball c R, g z ≠ 0)
    (hM : ∀ z ∈ ball c R, ‖g z‖ ≤ M)
    (hm : 0 < m) (hcenter : m ≤ ‖g c‖) :
    ∀ z ∈ closedBall c r,
      ‖logDeriv g z‖ ≤
        4 * (Real.log (M / m) + 1) * (r + (R - r) / 3) /
          (((R - r) / 3) * (R - (r + (R - r) / 3))) := by
  let U : Set ℂ := ball c R
  let δ : ℝ := (R - r) / 3
  let Rmid : ℝ := r + δ
  let L : ℝ := Real.log (M / m) + 1
  let f : ℂ → ℂ := fun z => deriv g z / g z
  let F : ℂ → ℂ := Classical.choose
    ((hg.deriv.div hg hgne).differentiableOn.isExactOn_ball.with_val_at c 0)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hRmid : Rmid < R := by
    dsimp [Rmid, δ]
    nlinarith
  have hcenterMem : c ∈ U := by
    dsimp [U]
    exact mem_ball_self hR
  have hMpos : 0 < M := lt_of_lt_of_le hm (hcenter.trans (hM c hcenterMem))
  have hratio : 1 ≤ M / m := by
    rw [le_div_iff₀ hm]
    nlinarith [hcenter.trans (hM c hcenterMem)]
  have hLnonneg : 0 ≤ L := by
    dsimp [L]
    exact add_nonneg (Real.log_nonneg hratio) (by norm_num)
  have hLpos : 0 < L := by
    have hlognonneg := Real.log_nonneg hratio
    dsimp [L]
    linarith
  have hFcenter : F c = 0 := by
    dsimp [F]
    exact Classical.choose_spec
      ((hg.deriv.div hg hgne).differentiableOn.isExactOn_ball.with_val_at c 0) |>.1
  have hFder (z : ℂ) (hz : z ∈ U) :
      HasDerivAt F (deriv g z / g z) z := by
    dsimp [F]
    exact (Classical.choose_spec
      ((hg.deriv.div hg hgne).differentiableOn.isExactOn_ball.with_val_at c 0)).2 z hz
  have hFdiff : DifferentiableOn ℂ F U := by
    intro z hz
    exact (hFder z hz).differentiableAt.differentiableWithinAt
  have hGdiff : DifferentiableOn ℂ (fun z => g z * Complex.exp (-F z)) U := by
    intro z hz
    have hgAt : DifferentiableAt ℂ g z := (hg z hz).differentiableAt
    have hFAt : DifferentiableAt ℂ F z := (hFder z hz).differentiableAt
    have hExpDiff : DifferentiableAt ℂ (fun w => Complex.exp (-F w)) z := by
      exact (Complex.hasDerivAt_exp (-F z)).differentiableAt.comp z hFAt.neg
    exact (hgAt.mul hExpDiff).differentiableWithinAt
  have hGder (z : ℂ) (hz : z ∈ U) :
      HasDerivAt (fun w => g w * Complex.exp (-F w)) 0 z := by
    have hgAt : HasDerivAt g (deriv g z) z := (hg z hz).differentiableAt.hasDerivAt
    have hFAt := hFder z hz
    have hexp : HasDerivAt (fun w => Complex.exp (-F w))
        (Complex.exp (-F z) * -(deriv g z / g z)) z := by
      exact (Complex.hasDerivAt_exp (-F z)).comp z hFAt.neg
    have hmul' : HasDerivAt (fun w => g w * Complex.exp (-F w))
        (deriv g z * Complex.exp (-F z) +
          g z * (Complex.exp (-F z) * -(deriv g z / g z))) z := by
      exact hgAt.fun_mul hexp
    have hcoeff : deriv g z * Complex.exp (-F z) +
        g z * (Complex.exp (-F z) * -(deriv g z / g z)) = 0 := by
      field_simp [hgne z hz]
      ring
    simpa only [hcoeff] using hmul'
  have hGconst (z : ℂ) (hz : z ∈ U) :
      g z * Complex.exp (-F z) = g c := by
    have hconst := isOpen_ball.is_const_of_deriv_eq_zero isPreconnected_ball
      hGdiff (by
        intro w hw
        exact (hGder w hw).deriv) hz hcenterMem
    simpa [hFcenter] using hconst
  have hfactor (z : ℂ) (hz : z ∈ U) :
      g z = g c * Complex.exp (F z) := by
    have hconst := hGconst z hz
    have hexp : Complex.exp (-F z) * Complex.exp (F z) = 1 := by
      rw [← Complex.exp_add]
      simp
    calc
      g z = (g z * Complex.exp (-F z)) * Complex.exp (F z) := by rw [mul_assoc, hexp, mul_one]
      _ = g c * Complex.exp (F z) := by rw [hconst]
  have hReBound (z : ℂ) (hz : z ∈ U) : (F z).re ≤ L := by
    have hnormRatio : ‖g z‖ / ‖g c‖ = Real.exp (F z).re := by
      rw [hfactor z hz, norm_mul, Complex.norm_exp]
      have hcne : ‖g c‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le hm hcenter)
      field_simp
    have hzpos : 0 < ‖g z‖ := norm_pos_iff.mpr (hgne z hz)
    have hcpos : 0 < ‖g c‖ := lt_of_lt_of_le hm hcenter
    have hratio' : ‖g z‖ / ‖g c‖ ≤ M / m := by
      calc
        ‖g z‖ / ‖g c‖ ≤ M / ‖g c‖ :=
          div_le_div_of_nonneg_right (hM z hz) (norm_nonneg _)
        _ ≤ M / m := div_le_div_of_nonneg_left hMpos.le hm hcenter
    have hlog := Real.log_le_log (div_pos hzpos hcpos) hratio'
    have hlogEq : Real.log (‖g z‖ / ‖g c‖) = (F z).re := by
      rw [hnormRatio, Real.log_exp]
    rw [hlogEq] at hlog
    dsimp [L]
    linarith
  have hshiftDiff : DifferentiableOn ℂ (fun w => F (c + w)) (ball 0 R) := by
    intro w hw
    have hw' : c + w ∈ U := by
      change dist (c + w) c < R
      simpa [dist_eq_norm] using hw
    have hmap : DifferentiableWithinAt ℂ (fun x : ℂ => c + x) (ball 0 R) w := by
      fun_prop
    exact (hFdiff (c + w) hw').comp w
      (by
        change DifferentiableWithinAt ℂ (fun x => c + x) (ball 0 R) w
        fun_prop)
      (by
        change MapsTo (fun x => c + x) (ball 0 R) U
        intro x hx
        change dist (c + x) c < R
        simpa [dist_eq_norm] using hx)
  have hshiftMaps : MapsTo (fun w => F (c + w)) (ball 0 R) {w : ℂ | w.re ≤ L} := by
    intro w hw
    have hw' : c + w ∈ U := by
      change dist (c + w) c < R
      simpa [dist_eq_norm] using hw
    exact hReBound (c + w) hw'
  intro z hz
  have hzmem : z ∈ U := by
    change dist z c ≤ r at hz
    change dist z c < R
    exact lt_of_le_of_lt hz hrR
  have hcenterNorm : ‖z - c‖ ≤ r := by
    change dist z c ≤ r at hz
    simpa only [dist_eq_norm] using hz
  have hFbound (w : ℂ) (hw : w ∈ ball z δ) :
      ‖F w‖ ≤ 2 * L * Rmid / (R - Rmid) := by
    have hwU : w ∈ U := by
      change dist w c < R
      have hwz : dist w z < δ := Metric.mem_ball.mp hw
      have hzc : dist z c ≤ r := by simpa [dist_eq_norm, norm_sub_rev] using hcenterNorm
      exact lt_of_le_of_lt (dist_triangle w z c) (by linarith)
    have hwShift : c + (w - c) = w := by ring
    have hwShiftBall : w - c ∈ ball (0 : ℂ) R := by
      change dist (w - c) 0 < R
      have hwNorm : ‖w - c‖ < R := by
        change dist w c < R at hwU
        simpa only [dist_eq_norm] using hwU
      simpa [dist_eq_norm] using hwNorm
    have hFshiftzero : F (c + 0) = 0 := by simpa using hFcenter
    have hbc := Complex.borelCaratheodory_zero hLpos hshiftDiff hshiftMaps hR
      hwShiftBall hFshiftzero
    have hnormShift : ‖w - c‖ ≤ Rmid := by
      have hwz : dist w z < δ := Metric.mem_ball.mp hw
      have hzc : dist z c ≤ r := by simpa [dist_eq_norm, norm_sub_rev] using hcenterNorm
      dsimp [Rmid]
      have hle : dist w c ≤ δ + r := by
        calc
          dist w c ≤ dist w z + dist z c := dist_triangle w z c
          _ ≤ δ + r := add_le_add hwz.le hzc
      simpa [dist_eq_norm, add_comm] using hle
    have hratioNorm : ‖w - c‖ / (R - ‖w - c‖) ≤ Rmid / (R - Rmid) := by
      have hwUdist : dist w c < R := by simpa [U] using hwU
      apply (div_le_div_iff₀ (by simpa [dist_eq_norm] using hwUdist) (by linarith [hRmid])).2
      nlinarith [hnormShift]
    have hbc' : ‖F w‖ ≤ 2 * L * (‖w - c‖ / (R - ‖w - c‖)) := by
      rw [hwShift] at hbc
      simpa [mul_div_assoc] using hbc
    calc
      ‖F w‖ ≤ 2 * L * (‖w - c‖ / (R - ‖w - c‖)) := hbc'
      _ ≤ 2 * L * (Rmid / (R - Rmid)) :=
        mul_le_mul_of_nonneg_left hratioNorm (by positivity)
      _ = 2 * L * Rmid / (R - Rmid) := by ring
  have hFmaps (w : ℂ) (hw : w ∈ ball z δ) :
      F w ∈ closedBall (F z) (4 * L * Rmid / (R - Rmid)) := by
    rw [mem_closedBall, dist_eq_norm]
    have hzBound : ‖F z‖ ≤ 2 * L * Rmid / (R - Rmid) := by
      have hz' : z ∈ ball z δ := mem_ball_self hδ
      exact hFbound z hz'
    calc
      ‖F w - F z‖ ≤ ‖F w‖ + ‖F z‖ := norm_sub_le _ _
      _ ≤ 4 * L * Rmid / (R - Rmid) := by
        calc
          _ ≤ 2 * L * Rmid / (R - Rmid) + 2 * L * Rmid / (R - Rmid) :=
            add_le_add (hFbound w hw) hzBound
          _ = _ := by ring
  have hFderBound : ‖deriv F z‖ ≤
      (4 * L * Rmid / (R - Rmid)) / δ := by
    have hsubset : ball z δ ⊆ U := by
      intro w hw
      change dist w c < R
      have hwz : dist w z < δ := Metric.mem_ball.mp hw
      have hzc : dist z c ≤ r := by simpa [dist_eq_norm, norm_sub_rev] using hcenterNorm
      have hd : δ + r < R := by dsimp [δ]; nlinarith
      have htri := dist_triangle w z c
      exact lt_of_le_of_lt htri (by linarith)
    exact Complex.norm_deriv_le_div_of_mapsTo_ball
      (hFdiff.mono hsubset)
      hFmaps hδ
  have hlogDeriv : logDeriv g z = deriv F z := by
    rw [logDeriv_apply, (hFder z hzmem).deriv]
  rw [hlogDeriv]
  simpa [Rmid, δ, L, div_div, mul_comm] using hFderBound

/-- The explicit finite zero contribution in the local logarithmic-derivative
factorization is quantitatively bounded on a horizontal line separated from
all zeros. The bound is quadratic in the Jensen logarithm: one logarithm
counts zeros with multiplicity, and the second is the reciprocal separation.
This is the finite-divisor part of the MA03 horizontal-edge estimate; the
nonvanishing factor's logarithmic derivative is a separate obligation. -/
theorem norm_dirichlet_LFunction_local_zero_logDeriv_sum_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ H σ : ℝ)
    (_hσ : σ ∈ Set.Icc (9 / 10 : ℝ) (11 / 10))
    (hsep : ∀ z : ℂ, DirichletCharacter.LFunction χ z = 0 →
      1 / (24 * (Real.log (28 * (q : ℝ) * (|τ| + 2)) /
        Real.log (6 / 5 : ℝ) + 1)) ≤
          ‖((σ : ℂ) + (H : ℂ) * Complex.I) - z‖) :
    ‖∑ᶠ u : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
          (closedBall (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) /
            (((σ : ℂ) + (H : ℂ) * Complex.I) - u)‖ ≤
      24 * (Real.log (28 * (q : ℝ) * (|τ| + 2)) /
        Real.log (6 / 5 : ℝ)) *
          (Real.log (28 * (q : ℝ) * (|τ| + 2)) /
            Real.log (6 / 5 : ℝ) + 1) := by
  let c : ℂ := 2 + (τ : ℂ) * Complex.I
  let U : Set ℂ := closedBall c (5 / 4 : ℝ)
  let D : ℂ → ℤ := MeromorphicOn.divisor (DirichletCharacter.LFunction χ) U
  let Z : Finset ℂ := dirichletLocalZeros χ τ
  let s : ℂ := (σ : ℂ) + (H : ℂ) * Complex.I
  let J : ℝ := Real.log (28 * (q : ℝ) * (|τ| + 2)) /
    Real.log (6 / 5 : ℝ)
  let δ : ℝ := 1 / (24 * (J + 1))
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hτ : 0 ≤ |τ| := abs_nonneg τ
  have hJ : 0 ≤ J := by
    dsimp [J]
    apply div_nonneg
    · apply Real.log_nonneg
      have harg : (1 : ℝ) ≤ 28 * (q : ℝ) * (|τ| + 2) := by
        have hnonneg : 0 ≤ (q : ℝ) - 1 := by linarith
        have hfactor : 0 ≤ |τ| + 2 := by positivity
        nlinarith [mul_nonneg hnonneg hfactor]
      exact harg
    · exact (Real.log_pos (by norm_num : (1 : ℝ) < 6 / 5)).le
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hDnonneg : ∀ u, 0 ≤ D u := by
    intro u
    have hf := dirichlet_LFunction_analyticOnNhd_disk χ hχ τ (5 / 4)
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf u
  have hsumD : (∑ u ∈ Z, D u : ℤ) ≤ J := by
    have hfinite : (∑ᶠ u : ℂ, D u) = ∑ u ∈ Z, D u := by
      apply finsum_eq_sum_of_support_subset
      intro u hu
      change u ∈ Z
      have hu' : u ∈ Function.support D := hu
      simpa only [Z, dirichletLocalZeros, Set.Finite.mem_toFinset] using hu'
    rw [← hfinite]
    exact dirichlet_LFunction_local_sum_divisor_le χ hχ τ
  have hsumDreal : (∑ u ∈ Z, (D u : ℝ)) ≤ J := by
    have hcast : ((∑ u ∈ Z, D u : ℤ) : ℝ) = ∑ u ∈ Z, (D u : ℝ) := by
      simp only [Int.cast_sum]
    rw [← hcast]
    exact_mod_cast hsumD
  have hsumEq : (∑ᶠ u : ℂ, (D u : ℂ) / (s - u)) =
      ∑ u ∈ Z, (D u : ℂ) / (s - u) := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    have hDu : D u ≠ 0 := by
      intro hzero
      apply hu
      simp [hzero]
    change u ∈ Z
    have hu' : u ∈ Function.support D := Function.mem_support.mpr hDu
    simpa only [Z, dirichletLocalZeros, Set.Finite.mem_toFinset] using hu'
  have hterm (u : ℂ) (hu : u ∈ Z) :
      ‖(D u : ℂ) / (s - u)‖ ≤ (D u : ℝ) / δ := by
    have hzero : DirichletCharacter.LFunction χ u = 0 := by
      have := (mem_dirichletLocalZeros_iff χ hχ τ u).mp hu
      exact this.2
    have hden : δ ≤ ‖s - u‖ := by
      have := hsep u hzero
      simpa only [δ, J, s, norm_sub_rev] using this
    have hDreal : ‖(D u : ℂ)‖ = (D u : ℝ) := by
      rw [Complex.norm_intCast]
      exact abs_of_nonneg (by exact_mod_cast hDnonneg u)
    rw [norm_div, hDreal]
    have hinv : (‖s - u‖)⁻¹ ≤ δ⁻¹ :=
      by simpa only [one_div] using one_div_le_one_div_of_le hδ hden
    calc
      (D u : ℝ) / ‖s - u‖ = (D u : ℝ) * (‖s - u‖)⁻¹ := by ring
      _ ≤ (D u : ℝ) * δ⁻¹ := mul_le_mul_of_nonneg_left hinv
        (by exact_mod_cast hDnonneg u)
      _ = (D u : ℝ) / δ := by ring
  have hsumNorm :
      ‖∑ u ∈ Z, (D u : ℂ) / (s - u)‖ ≤
        ∑ u ∈ Z, ‖(D u : ℂ) / (s - u)‖ := norm_sum_le _ _
  have hsumTerm :
      (∑ u ∈ Z, ‖(D u : ℂ) / (s - u)‖) ≤
        ∑ u ∈ Z, (D u : ℝ) / δ :=
    Finset.sum_le_sum fun u hu => hterm u hu
  have hsumDiv : (∑ u ∈ Z, (D u : ℝ) / δ) =
      (∑ u ∈ Z, (D u : ℝ)) / δ := by rw [Finset.sum_div]
  have hbound : (∑ u ∈ Z, (D u : ℝ)) / δ ≤ J / δ :=
    div_le_div_of_nonneg_right hsumDreal hδ.le
  have hfinal : J / δ ≤ 24 * J * (J + 1) := by
    dsimp [δ]
    field_simp
    rfl
  calc
    ‖∑ᶠ u : ℂ, (D u : ℂ) / (s - u)‖ =
        ‖∑ u ∈ Z, (D u : ℂ) / (s - u)‖ := by rw [hsumEq]
    _ ≤ ∑ u ∈ Z, ‖(D u : ℂ) / (s - u)‖ := hsumNorm
    _ ≤ ∑ u ∈ Z, (D u : ℝ) / δ := hsumTerm
    _ = (∑ u ∈ Z, (D u : ℝ)) / δ := hsumDiv
    _ ≤ J / δ := hbound
    _ ≤ 24 * J * (J + 1) := hfinal
  

#print axioms exists_dirichlet_LFunction_local_factorization
#print axioms exists_dirichlet_LFunction_local_factorization_logDeriv
#print axioms exists_dirichlet_LFunction_local_logDeriv_of_one_lt_re
#print axioms norm_dirichlet_LFunction_local_zero_logDeriv_sum_le
#print axioms norm_logDeriv_le_of_analyticOnNhd_nonzero_centerBound
#print axioms exists_dirichlet_LFunction_local_factorization_center_lower
#print axioms dirichlet_LFunction_local_remainder_norm_le

end SystolicGrowth.CookMagyarCircle
