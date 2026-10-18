module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ComplexLocalWeakSobolev
public import Geometry.ComplexSobolevOneDerivativeRepresentative
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

/-!
# Local elliptic regularity from the actual compact-test equation

Local real weak first derivatives are converted to genuine cutoff Sobolev
distributions. The compact-test Laplace equation identifies their localized
Laplacians; nested cutoffs then give `H³` and a real classical `C¹`
representative. No higher Sobolev membership is an input.
-/

open Set Filter MeasureTheory TemperedDistribution
open scoped ContDiff Topology ENNReal LineDeriv SchwartzMap Laplacian

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- **Math.** The Schwartz Laplacian does not enlarge topological support. -/
theorem complexSchwartz_laplacian_tsupport_subset (ψ : 𝓢(ℂ, ℂ)) :
    tsupport (Δ ψ : 𝓢(ℂ, ℂ)) ⊆ tsupport (ψ : ℂ → ℂ) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro z hz
  by_contra hn
  apply hz
  rw [SchwartzMap.laplacian_eq_sum (stdOrthonormalBasis ℝ ℂ)]
  simp only [sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply image_eq_zero_of_notMem_tsupport
  exact fun hi => hn ((SchwartzMap.tsupport_lineDerivOp_subset _ _).trans
    (SchwartzMap.tsupport_lineDerivOp_subset _ _) hi)

/-- **Math.** A continuous coefficient preserves compact-local `L²`. -/
theorem localL2_mul_continuousOn {V : Set ℂ} {F b : ℂ → ℝ}
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K))
    (hb : ContinuousOn b V) (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) :
    MemLp (fun z => b z * F z) 2 (volume.restrict K) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hb.mono hKV)
  have hbtop : MemLp b ∞ (volume.restrict K) :=
    memLp_top_of_bound ((hb.mono hKV).aestronglyMeasurable hK.measurableSet) C
      ((ae_restrict_mem hK.measurableSet).mono fun z hz => hC z hz)
  exact hbtop.fun_mul (hF K hK hKV)

/-- **Math.** The real compact-test Laplace identity is the literal
complex-valued Schwartz identity after complexification. -/
theorem complexLocalWeakLaplacian_test
    {V : Set ℂ} (u R : ℂ → ℝ)
    (hu : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp u 2 (volume.restrict K))
    (hR : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp R 2 (volume.restrict K))
    (heq : ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, u z * Δ η z) = ∫ z : ℂ, R z * η z)
    (ψ : 𝓢(ℂ, ℂ)) (hψc : HasCompactSupport (ψ : ℂ → ℂ))
    (hψV : tsupport (ψ : ℂ → ℂ) ⊆ V) :
    (∫ z : ℂ, (Δ ψ) z * (u z : ℂ)) = ∫ z : ℂ, ψ z * (R z : ℂ) := by
  have huC (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) :
      MemLp (fun z => (u z : ℂ)) 2 (volume.restrict K) := (hu K hK hKV).ofReal
  have hRC (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) :
      MemLp (fun z => (R z : ℂ)) 2 (volume.restrict K) := (hR K hK hKV).ofReal
  have hΔc : HasCompactSupport ((Δ ψ : 𝓢(ℂ, ℂ)) : ℂ → ℂ) :=
    hψc.of_isClosed_subset (isClosed_tsupport _) (complexSchwartz_laplacian_tsupport_subset ψ)
  have hleft := localL2_compact_mul_integrable huC (Δ ψ : 𝓢(ℂ, ℂ))
    (Δ ψ : 𝓢(ℂ, ℂ)).continuous hΔc
    ((complexSchwartz_laplacian_tsupport_subset ψ).trans hψV)
  have hright := localL2_compact_mul_integrable hRC ψ ψ.continuous hψc hψV
  have hL (L : ℂ →L[ℝ] ℝ) :
      L (∫ z : ℂ, (Δ ψ) z * (u z : ℂ)) =
        L (∫ z : ℂ, ψ z * (R z : ℂ)) := by
    have hη : ContDiff ℝ ∞ (fun z => L (ψ z)) := L.contDiff.comp ψ.smooth'
    have hηc : HasCompactSupport (fun z => L (ψ z)) := hψc.comp_left (map_zero L)
    have hηV : tsupport (fun z => L (ψ z)) ⊆ V :=
      (tsupport_comp_subset (map_zero L) ψ).trans hψV
    have hηΔ (z : ℂ) : Δ (fun z => L (ψ z)) z = L ((Δ ψ) z) := by
      rw [SchwartzMap.laplacian_apply]
      exact (ψ.smooth 2).contDiffAt.laplacian_CLM_comp_left
    calc
      L (∫ z : ℂ, (Δ ψ) z * (u z : ℂ)) =
          ∫ z : ℂ, u z * Δ (fun z => L (ψ z)) z := by
        rw [← L.integral_comp_comm hleft]
        apply integral_congr_ae
        filter_upwards with z
        rw [hηΔ]
        change L (((Δ ψ : 𝓢(ℂ, ℂ)) z) * (u z : ℂ)) =
          u z * L ((Δ ψ : 𝓢(ℂ, ℂ)) z)
        rw [mul_comm ((Δ ψ : 𝓢(ℂ, ℂ)) z) (u z : ℂ)]
        simpa only [Complex.real_smul, smul_eq_mul] using
          L.map_smul (u z) ((Δ ψ) z)
      _ = ∫ z : ℂ, R z * L (ψ z) := heq _ hη hηc hηV
      _ = L (∫ z : ℂ, ψ z * (R z : ℂ)) := by
        rw [← L.integral_comp_comm hright]
        apply integral_congr_ae
        filter_upwards with z
        simpa only [Complex.real_smul, smul_eq_mul, mul_comm] using
          (L.map_smul (R z) (ψ z)).symm
  exact Complex.ext (hL Complex.reCLM) (hL Complex.imCLM)

/-- **Math.** A locally smooth coefficient times a compactly supported
complex cutoff is globally smooth. -/
theorem complex_contDiffOn_mul_supported {V : Set ℂ} (hV : IsOpen V)
    {b ζ : ℂ → ℂ} (hb : ContDiffOn ℝ ∞ b V) (hζ : ContDiff ℝ ∞ ζ)
    (hζV : tsupport ζ ⊆ V) : ContDiff ℝ ∞ (fun z => b z * ζ z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ V
  · exact (hb.contDiffAt (hV.mem_nhds hz)).mul hζ.contDiffAt
  · have hzero : ζ =ᶠ[𝓝 z] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun hz' => hz (hζV hz'))
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hzero] with w hw
    simp only [hw, Pi.zero_apply, mul_zero]

/-- **Math.** The actual weak equation identifies the cutoff Laplacian of
any localization which equals the original function near that cutoff.
The right side is the actual localized forcing distribution. -/
theorem complexLocalWeakLaplacian_cutoff
    {V : Set ℂ} (u F a : ℂ → ℝ)
    (hu : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp u 2 (volume.restrict K))
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K))
    (ha : ContinuousOn a V)
    (heq : ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, u z * Δ η z) =
        ∫ z : ℂ, a z ^ 2 * (F z * η z))
    (χu χF : ℂ → ℂ) (w q : 𝓢'(ℂ, ℂ))
    (hw : ∀ φ : 𝓢(ℂ, ℂ), w φ = ∫ z : ℂ, φ z * (χu z * (u z : ℂ)))
    (hq : ∀ φ : 𝓢(ℂ, ℂ), q φ = ∫ z : ℂ, φ z * (χF z * (F z : ℂ)))
    (ζ κ : 𝓢(ℂ, ℂ)) (hζc : HasCompactSupport (ζ : ℂ → ℂ))
    (hζV : tsupport (ζ : ℂ → ℂ) ⊆ V)
    (hχu : ∀ z ∈ tsupport (ζ : ℂ → ℂ), χu z = 1)
    (hχF : ∀ z ∈ tsupport (ζ : ℂ → ℂ), χF z = 1)
    (hκ : ∀ z, κ z = ζ z * (a z ^ 2 : ℝ)) :
    TemperedDistribution.smulLeftCLM ℂ ζ (Δ w) =
      TemperedDistribution.smulLeftCLM ℂ κ q := by
  ext φ
  let ψ := SchwartzMap.smulLeftCLM ℂ ζ φ
  have hψ (z : ℂ) : ψ z = ζ z * φ z := by
    simp [ψ, SchwartzMap.smulLeftCLM_apply_apply ζ.hasTemperateGrowth, smul_eq_mul]
  have hψsub : tsupport (ψ : ℂ → ℂ) ⊆ tsupport (ζ : ℂ → ℂ) := by
    have hf : (ψ : ℂ → ℂ) = fun z => ζ z * φ z := funext hψ
    rw [hf]
    exact tsupport_mul_subset_left
  have hψc : HasCompactSupport (ψ : ℂ → ℂ) :=
    hζc.of_isClosed_subset (isClosed_tsupport _) hψsub
  have hR := localL2_mul_continuousOn hF (ha.pow 2)
  have heq' (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
      (hηV : tsupport η ⊆ V) :
      (∫ z : ℂ, u z * Δ η z) = ∫ z : ℂ, (a z ^ 2 * F z) * η z := by
    simpa only [mul_assoc] using heq η hη hηc hηV
  have hid := complexLocalWeakLaplacian_test u (fun z => a z ^ 2 * F z)
    hu hR heq' ψ hψc (hψsub.trans hζV)
  rw [TemperedDistribution.smulLeftCLM_apply_apply,
    TemperedDistribution.laplacian_apply_apply, hw,
    TemperedDistribution.smulLeftCLM_apply_apply, hq]
  change (∫ z : ℂ, (Δ ψ) z * (χu z * (u z : ℂ))) = _
  calc
    (∫ z : ℂ, (Δ ψ) z * (χu z * (u z : ℂ))) =
        ∫ z : ℂ, (Δ ψ) z * (u z : ℂ) := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ tsupport (ζ : ℂ → ℂ)
      · rw [hχu z hz, one_mul]
      · have hzΔ : (Δ ψ) z = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hz (hψsub (complexSchwartz_laplacian_tsupport_subset ψ h)))
        simp [hzΔ]
    _ = ∫ z : ℂ, ψ z * ((a z ^ 2 * F z : ℝ) : ℂ) := hid
    _ = ∫ z : ℂ, (SchwartzMap.smulLeftCLM ℂ κ φ) z * (χF z * (F z : ℂ)) := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [hψ, SchwartzMap.smulLeftCLM_apply_apply κ.hasTemperateGrowth,
        smul_eq_mul, hκ, Complex.ofReal_mul]
      by_cases hz : z ∈ tsupport (ζ : ℂ → ℂ)
      · rw [hχF z hz]
        ring
      · rw [image_eq_zero_of_notMem_tsupport hz]
        simp

/-- **Math.** A smaller cutoff removes an outer localization which is
identically one on its support, with the exact integral action retained. -/
theorem complexDistribution_cutoff_local_action
    (u : ℂ → ℝ) (χ : ℂ → ℂ) (w : 𝓢'(ℂ, ℂ))
    (hw : ∀ φ : 𝓢(ℂ, ℂ), w φ = ∫ z : ℂ, φ z * (χ z * (u z : ℂ)))
    (ζ : 𝓢(ℂ, ℂ)) (hχ : ∀ z ∈ tsupport (ζ : ℂ → ℂ), χ z = 1)
    (φ : 𝓢(ℂ, ℂ)) :
    (TemperedDistribution.smulLeftCLM ℂ ζ w) φ =
      ∫ z : ℂ, φ z * (ζ z * (u z : ℂ)) := by
  rw [TemperedDistribution.smulLeftCLM_apply_apply, hw]
  apply integral_congr_ae
  filter_upwards with z
  simp only [SchwartzMap.smulLeftCLM_apply_apply ζ.hasTemperateGrowth, smul_eq_mul]
  by_cases hz : z ∈ tsupport (ζ : ℂ → ℂ)
  · rw [hχ z hz]
    ring
  · rw [image_eq_zero_of_notMem_tsupport hz]
    simp

/-- **Math.** Two genuine nested elliptic gains give an actual `H³`
cutoff of the local solution. Both the solution and the forcing enter only
through local `L²` values and their compact-test weak first derivatives. -/
theorem complexLocalWeakElliptic_nested_cutoffs
    {V : Set ℂ} (hV : IsOpen V) (u F a : ℂ → ℝ)
    (Du DF : Fin 2 → ℂ → ℝ)
    (hu : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp u 2 (volume.restrict K))
    (hDu : ∀ (j : Fin 2) (K : Set ℂ), IsCompact K → K ⊆ V →
      MemLp (Du j) 2 (volume.restrict K))
    (huw : ∀ (j : Fin 2) (η : ℂ → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, Du j z * η z) =
        -(∫ z : ℂ, u z * fderiv ℝ η z (if j = 0 then 1 else Complex.I)))
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K))
    (hDF : ∀ (j : Fin 2) (K : Set ℂ), IsCompact K → K ⊆ V →
      MemLp (DF j) 2 (volume.restrict K))
    (hFw : ∀ (j : Fin 2) (η : ℂ → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, DF j z * η z) =
        -(∫ z : ℂ, F z * fderiv ℝ η z (if j = 0 then 1 else Complex.I)))
    (ha : ContDiffOn ℝ ∞ a V)
    (heq : ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, u z * Δ η z) =
        ∫ z : ℂ, a z ^ 2 * (F z * η z))
    (ζ₀ ζ₁ ζ₂ : 𝓢(ℂ, ℂ))
    (hζ₀c : HasCompactSupport (ζ₀ : ℂ → ℂ)) (hζ₀V : tsupport (ζ₀ : ℂ → ℂ) ⊆ V)
    (hζ₁c : HasCompactSupport (ζ₁ : ℂ → ℂ)) (hζ₁V : tsupport (ζ₁ : ℂ → ℂ) ⊆ V)
    (hζ₂c : HasCompactSupport (ζ₂ : ℂ → ℂ)) (hζ₂V : tsupport (ζ₂ : ℂ → ℂ) ⊆ V)
    (h₀₁ : ∀ z ∈ tsupport (ζ₁ : ℂ → ℂ), ζ₀ z = 1)
    (h₁₂ : ∀ z ∈ tsupport (ζ₂ : ℂ → ℂ), ζ₁ z = 1) :
    ∃ w : Lp ℂ 2 (volume : Measure ℂ),
      w =ᵐ[volume] (fun z => ζ₂ z * (u z : ℂ)) ∧
      MemSobolev 3 2 (w : 𝓢'(ℂ, ℂ)) ∧
      ∀ φ : 𝓢(ℂ, ℂ), (w : 𝓢'(ℂ, ℂ)) φ =
        ∫ z : ℂ, φ z * (ζ₂ z * (u z : ℂ)) := by
  obtain ⟨w₀, _, hw₀, hw₀act, _⟩ :=
    complexLocalWeakSobolev_cutoff u Du hu hDu huw ζ₀ hζ₀c hζ₀V
  obtain ⟨q, _, hq, hqact, _⟩ :=
    complexLocalWeakSobolev_cutoff F DF hF hDF hFw ζ₀ hζ₀c hζ₀V
  have hκ (ζ : 𝓢(ℂ, ℂ)) (hζc : HasCompactSupport (ζ : ℂ → ℂ))
      (hζV : tsupport (ζ : ℂ → ℂ) ⊆ V) :
      ∃ κ : 𝓢(ℂ, ℂ), ∀ z, κ z = ζ z * (a z ^ 2 : ℝ) := by
    have hsm : ContDiff ℝ ∞ (fun z => ((a z ^ 2 : ℝ) : ℂ) * ζ z) :=
      complex_contDiffOn_mul_supported hV
        (Complex.ofRealCLM.contDiff.comp_contDiffOn (ha.pow 2)) ζ.smooth' hζV
    have hc : HasCompactSupport (fun z => ((a z ^ 2 : ℝ) : ℂ) * ζ z) := hζc.mul_left
    exact ⟨hc.toSchwartzMap hsm, fun z => mul_comm _ _⟩
  obtain ⟨κ₁, hκ₁⟩ := hκ ζ₁ hζ₁c hζ₁V
  have hΔ₁ := complexLocalWeakLaplacian_cutoff u F a hu hF ha.continuousOn heq
    ζ₀ ζ₀ w₀ q hw₀act hqact ζ₁ κ₁ hζ₁c hζ₁V h₀₁ h₀₁ hκ₁
  let w₁ := TemperedDistribution.smulLeftCLM ℂ ζ₁ (w₀ : 𝓢'(ℂ, ℂ))
  have hw₁ : MemSobolev 2 2 w₁ := by
    apply complexDistribution_memSobolev_two_cutoff ζ₁ (w₀ : 𝓢'(ℂ, ℂ)) hw₀
    rw [hΔ₁]
    exact (complexDistribution_memSobolev_one_smulLeft κ₁ q hq).mono (by norm_num)
  have hw₁act : ∀ φ : 𝓢(ℂ, ℂ), w₁ φ = ∫ z : ℂ, φ z * (ζ₁ z * (u z : ℂ)) :=
    complexDistribution_cutoff_local_action u ζ₀ w₀ hw₀act ζ₁ h₀₁
  have h₀₂ : ∀ z ∈ tsupport (ζ₂ : ℂ → ℂ), ζ₀ z = 1 := by
    intro z hz
    apply h₀₁ z
    apply subset_tsupport
    change ζ₁ z ≠ 0
    rw [h₁₂ z hz]
    exact one_ne_zero
  obtain ⟨κ₂, hκ₂⟩ := hκ ζ₂ hζ₂c hζ₂V
  have hΔ₂ := complexLocalWeakLaplacian_cutoff u F a hu hF ha.continuousOn heq
    ζ₁ ζ₀ w₁ q hw₁act hqact ζ₂ κ₂ hζ₂c hζ₂V h₁₂ h₀₂ hκ₂
  have hw₂ : MemSobolev 3 2 (TemperedDistribution.smulLeftCLM ℂ ζ₂ w₁) := by
    apply complexDistribution_memSobolev_three_cutoff ζ₂ w₁ hw₁
    rw [hΔ₂]
    exact complexDistribution_memSobolev_one_smulLeft κ₂ q hq
  obtain ⟨w₂, hw₂ae, _, hw₂act, _⟩ :=
    complexLocalWeakSobolev_cutoff u Du hu hDu huw ζ₂ hζ₂c hζ₂V
  have he : (w₂ : 𝓢'(ℂ, ℂ)) = TemperedDistribution.smulLeftCLM ℂ ζ₂ w₁ := by
    ext φ
    rw [hw₂act, complexDistribution_cutoff_local_action u ζ₁ w₁ hw₁act ζ₂ h₁₂]
  exact ⟨w₂, hw₂ae, he.symm ▸ hw₂, hw₂act⟩

/-- **Math.** Every point of an open coordinate domain has three actual
nested compact Schwartz cutoffs, the innermost equal to one on an open
neighborhood. -/
theorem exists_complex_three_nested_cutoffs
    {V : Set ℂ} (hV : IsOpen V) (x : ℂ) (hx : x ∈ V) :
    ∃ (W : Set ℂ) (ζ₀ ζ₁ ζ₂ : 𝓢(ℂ, ℂ)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      HasCompactSupport (ζ₀ : ℂ → ℂ) ∧ tsupport (ζ₀ : ℂ → ℂ) ⊆ V ∧
      HasCompactSupport (ζ₁ : ℂ → ℂ) ∧ tsupport (ζ₁ : ℂ → ℂ) ⊆ V ∧
      HasCompactSupport (ζ₂ : ℂ → ℂ) ∧ tsupport (ζ₂ : ℂ → ℂ) ⊆ V ∧
      (∀ z ∈ tsupport (ζ₁ : ℂ → ℂ), ζ₀ z = 1) ∧
      (∀ z ∈ tsupport (ζ₂ : ℂ → ℂ), ζ₁ z = 1) ∧
      (∀ z ∈ W, ζ₂ z = 1) := by
  obtain ⟨r, hr, hrV⟩ : ∃ r : ℝ, 0 < r ∧ Metric.closedBall x r ⊆ V :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hx)
  let b₀ : ContDiffBump x := ⟨r / 2, r, by positivity, by linarith⟩
  let b₁ : ContDiffBump x := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let b₂ : ContDiffBump x := ⟨r / 8, r / 4, by positivity, by linarith⟩
  have hc (b : ContDiffBump x) : HasCompactSupport (fun z => (b z : ℂ)) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hs (b : ContDiffBump x) : ContDiff ℝ ∞ (fun z => (b z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  let ζ : ContDiffBump x → 𝓢(ℂ, ℂ) := fun b => (hc b).toSchwartzMap (hs b)
  have hz (b : ContDiffBump x) (z : ℂ) : ζ b z = (b z : ℂ) := rfl
  have hsub (b : ContDiffBump x) :
      tsupport (ζ b : ℂ → ℂ) ⊆ Metric.closedBall x b.rOut := by
    change tsupport (fun z => (b z : ℂ)) ⊆ _
    exact (tsupport_comp_subset Complex.ofReal_zero (b : ℂ → ℝ)).trans
      (by rw [b.tsupport_eq])
  refine ⟨Metric.ball x (r / 8), ζ b₀, ζ b₁, ζ b₂, Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity), ?_, hc b₀, ?_, hc b₁, ?_, hc b₂, ?_, ?_, ?_, ?_⟩
  · exact (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by linarith : r / 8 ≤ r))).trans hrV
  · exact (hsub b₀).trans hrV
  · exact ((hsub b₁).trans
      (Metric.closedBall_subset_closedBall (by dsimp [b₁]; linarith))).trans hrV
  · exact ((hsub b₂).trans
      (Metric.closedBall_subset_closedBall (by dsimp [b₂]; linarith))).trans hrV
  · intro z hz'
    rw [hz, b₀.one_of_mem_closedBall (hsub b₁ hz')]
    exact Complex.ofReal_one
  · intro z hz'
    rw [hz, b₁.one_of_mem_closedBall (hsub b₂ hz')]
    exact Complex.ofReal_one
  · intro z hz'
    rw [hz, b₂.one_of_mem_closedBall (Metric.ball_subset_closedBall hz')]
    exact Complex.ofReal_one

/-- **Math.** A real local weak solution with local weak `H¹` forcing
has a real `C¹` representative on a genuine neighborhood of every point.
The higher regularity is derived from the compact-test equation, not
required as a hypothesis. -/
theorem complexLocalWeakElliptic_exists_contDiff_one
    {V : Set ℂ} (hV : IsOpen V) (u F a : ℂ → ℝ)
    (Du DF : Fin 2 → ℂ → ℝ)
    (hu : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp u 2 (volume.restrict K))
    (hDu : ∀ (j : Fin 2) (K : Set ℂ), IsCompact K → K ⊆ V →
      MemLp (Du j) 2 (volume.restrict K))
    (huw : ∀ (j : Fin 2) (η : ℂ → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, Du j z * η z) =
        -(∫ z : ℂ, u z * fderiv ℝ η z (if j = 0 then 1 else Complex.I)))
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K))
    (hDF : ∀ (j : Fin 2) (K : Set ℂ), IsCompact K → K ⊆ V →
      MemLp (DF j) 2 (volume.restrict K))
    (hFw : ∀ (j : Fin 2) (η : ℂ → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, DF j z * η z) =
        -(∫ z : ℂ, F z * fderiv ℝ η z (if j = 0 then 1 else Complex.I)))
    (ha : ContDiffOn ℝ ∞ a V)
    (heq : ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, u z * Δ η z) =
        ∫ z : ℂ, a z ^ 2 * (F z * η z))
    (x : ℂ) (hx : x ∈ V) :
    ∃ (W : Set ℂ) (c : ℂ → ℝ), IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      ContDiffOn ℝ 1 c W ∧ u =ᵐ[volume.restrict W] c := by
  obtain ⟨W, ζ₀, ζ₁, ζ₂, hW, hxW, hWV, hζ₀c, hζ₀V, hζ₁c, hζ₁V,
    hζ₂c, hζ₂V, h₀₁, h₁₂, hζ₂one⟩ := exists_complex_three_nested_cutoffs hV x hx
  obtain ⟨w, hwae, hw, _⟩ := complexLocalWeakElliptic_nested_cutoffs hV u F a Du DF
    hu hDu huw hF hDF hFw ha heq ζ₀ ζ₁ ζ₂ hζ₀c hζ₀V hζ₁c hζ₁V hζ₂c hζ₂V h₀₁ h₁₂
  obtain ⟨f, c, hfc, hfae, hc⟩ := complex_memSobolev_three_ae_contDiff_one w hw
  have hwf : w = f := by
    apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ℂ) (μ := (volume : Measure ℂ)) (p := 2))
    exact hfc
  have hwc : (w : ℂ → ℂ) =ᵐ[volume] (c : ℂ → ℂ) := hwf ▸ hfae
  refine ⟨W, fun z => (c z).re, hW, hxW, hWV,
    (Complex.reCLM.contDiff.comp hc).contDiffOn, ?_⟩
  filter_upwards [hwae.restrict (s := W), hwc.restrict (s := W),
    ae_restrict_mem hW.measurableSet] with z huz hcz hzW
  have he : (u z : ℂ) = c z := by
    simpa only [hζ₂one z hzW, one_mul] using huz.symm.trans hcz
  exact congrArg Complex.re he

#print axioms complexLocalWeakLaplacian_test
#print axioms complexLocalWeakLaplacian_cutoff
#print axioms complexLocalWeakElliptic_nested_cutoffs
#print axioms exists_complex_three_nested_cutoffs
#print axioms complexLocalWeakElliptic_exists_contDiff_one

end

end SystolicGrowth
