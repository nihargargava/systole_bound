module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ComplexLocalWeakElliptic
public import Geometry.ComplexSobolevIntegerMultiplier
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

/-!
# Arbitrary-order local elliptic gain from the actual weak equation

Smooth compact cutoffs are constructed around arbitrary compact subsets
of the open coordinate domain. The actual compact-test equation then
identifies each localized Laplacian, including all product commutators.
Iteration gives genuine higher Sobolev representatives for every cutoff.
-/

open Set Filter MeasureTheory TemperedDistribution Manifold
open scoped ContDiff Topology ENNReal LineDeriv SchwartzMap Laplacian

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- **Math.** Every compact subset of an open complex-coordinate domain
has a genuine real-valued smooth compact cutoff which is one there. -/
theorem exists_real_smooth_compact_cutoff
    {V K : Set ℂ} (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V) :
    ∃ η : ℂ → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ V ∧ (∀ z ∈ K, η z = 1) := by
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  obtain ⟨η, hη, _, hηs, hηone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (modelWithCornersSelf ℝ ℂ)
      (n := (⊤ : ℕ∞)) Metric.isOpen_thickening hK.isClosed
      (Metric.self_subset_thickening hδ K)
  have hsub : tsupport η ⊆ Metric.cthickening δ K := by
    rw [tsupport, hηs]
    exact Metric.closure_thickening_subset_cthickening δ K
  refine ⟨η, hη.contDiff,
    (hK.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport _) hsub,
    hsub.trans hδV, ?_⟩
  exact fun z hz => (hηone z).mp hz

/-- **Math.** The same cutoff as a literal Schwartz multiplier, suitable
for any further finite number of nested localizations. -/
theorem exists_complex_schwartz_compact_cutoff
    {V K : Set ℂ} (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V) :
    ∃ ζ : 𝓢(ℂ, ℂ), HasCompactSupport (ζ : ℂ → ℂ) ∧
      tsupport (ζ : ℂ → ℂ) ⊆ V ∧ (∀ z ∈ K, ζ z = 1) := by
  obtain ⟨η, hη, hηc, hηV, hηone⟩ := exists_real_smooth_compact_cutoff hV hK hKV
  have hc : HasCompactSupport (fun z => (η z : ℂ)) :=
    hηc.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ (fun z => (η z : ℂ)) := Complex.ofRealCLM.contDiff.comp hη
  refine ⟨hc.toSchwartzMap hs, hc,
    (tsupport_comp_subset Complex.ofReal_zero η).trans hηV, ?_⟩
  intro z hz
  change (η z : ℂ) = 1
  rw [hηone z hz, Complex.ofReal_one]

/-- **Math.** One arbitrary integer-order elliptic gain under genuine
cutoffs. The localized Laplacian is derived from the actual raw PDE;
only the already obtained lower Sobolev orders are hypotheses. -/
theorem complexLocalWeakElliptic_cutoff_gain
    {V : Set ℂ} (hV : IsOpen V) (n : ℕ) (u F a : ℂ → ℝ)
    (hu : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp u 2 (volume.restrict K))
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K))
    (ha : ContDiffOn ℝ ∞ a V)
    (heq : ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, u z * Δ η z) =
        ∫ z : ℂ, a z ^ 2 * (F z * η z))
    (χu χF : ℂ → ℂ) (w q : Lp ℂ 2 (volume : Measure ℂ))
    (hwae : w =ᵐ[volume] (fun z => χu z * (u z : ℂ)))
    (hqae : q =ᵐ[volume] (fun z => χF z * (F z : ℂ)))
    (hw : MemSobolev ((n : ℝ) + 1) 2 (w : 𝓢'(ℂ, ℂ)))
    (hq : MemSobolev (n : ℝ) 2 (q : 𝓢'(ℂ, ℂ)))
    (ζ : 𝓢(ℂ, ℂ)) (hζc : HasCompactSupport (ζ : ℂ → ℂ))
    (hζV : tsupport (ζ : ℂ → ℂ) ⊆ V)
    (hχu : ∀ z ∈ tsupport (ζ : ℂ → ℂ), χu z = 1)
    (hχF : ∀ z ∈ tsupport (ζ : ℂ → ℂ), χF z = 1) :
    ∃ r : Lp ℂ 2 (volume : Measure ℂ),
      r =ᵐ[volume] (fun z => ζ z * (u z : ℂ)) ∧
      MemSobolev ((n : ℝ) + 2) 2 (r : 𝓢'(ℂ, ℂ)) ∧
      ∀ φ : 𝓢(ℂ, ℂ), (r : 𝓢'(ℂ, ℂ)) φ =
        ∫ z : ℂ, φ z * (ζ z * (u z : ℂ)) := by
  have hwact := complexL2_toTemperedDistribution_apply_of_ae w _ hwae
  have hqact := complexL2_toTemperedDistribution_apply_of_ae q _ hqae
  have hκsm : ContDiff ℝ ∞ (fun z => ((a z ^ 2 : ℝ) : ℂ) * ζ z) :=
    complex_contDiffOn_mul_supported hV
      (Complex.ofRealCLM.contDiff.comp_contDiffOn (ha.pow 2)) ζ.smooth' hζV
  have hκc : HasCompactSupport (fun z => ((a z ^ 2 : ℝ) : ℂ) * ζ z) := hζc.mul_left
  let κ : 𝓢(ℂ, ℂ) := hκc.toSchwartzMap hκsm
  have hκ (z : ℂ) : κ z = ζ z * (a z ^ 2 : ℝ) := mul_comm _ _
  have hΔ := complexLocalWeakLaplacian_cutoff u F a hu hF ha.continuousOn heq
    χu χF w q hwact hqact ζ κ hζc hζV hχu hχF hκ
  have hgain : MemSobolev ((n : ℝ) + 2) 2
      (TemperedDistribution.smulLeftCLM ℂ ζ (w : 𝓢'(ℂ, ℂ))) := by
    apply complexDistribution_memSobolev_nat_add_two_cutoff n ζ w hw
    rw [hΔ]
    exact complexDistribution_memSobolev_nat_smulLeft n κ q hq
  have hr := complexLocalCutoffValue_memLp u hu ζ ζ.continuous hζc hζV
  let r := hr.toLp (complexLocalCutoffValue u ζ)
  have hrae : r =ᵐ[volume] (fun z => ζ z * (u z : ℂ)) := hr.coeFn_toLp
  have hract := complexL2_toTemperedDistribution_apply_of_ae r _ hrae
  have hre : (r : 𝓢'(ℂ, ℂ)) = TemperedDistribution.smulLeftCLM ℂ ζ (w : 𝓢'(ℂ, ℂ)) := by
    ext φ
    rw [hract, complexDistribution_cutoff_local_action u χu w hwact ζ hχu]
  exact ⟨r, hrae, hre.symm ▸ hgain, hract⟩

/-- **Math.** Integer elliptic gain holds for every compact cutoff of
the domain: an outer cutoff is constructed, not assumed. -/
theorem complexLocalWeakElliptic_all_cutoffs_gain
    {V : Set ℂ} (hV : IsOpen V) (n : ℕ) (u F a : ℂ → ℝ)
    (hu : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp u 2 (volume.restrict K))
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K))
    (ha : ContDiffOn ℝ ∞ a V)
    (heq : ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, u z * Δ η z) =
        ∫ z : ℂ, a z ^ 2 * (F z * η z))
    (huS : ∀ ζ : 𝓢(ℂ, ℂ), HasCompactSupport (ζ : ℂ → ℂ) →
      tsupport (ζ : ℂ → ℂ) ⊆ V → ∃ w : Lp ℂ 2 (volume : Measure ℂ),
        w =ᵐ[volume] (fun z => ζ z * (u z : ℂ)) ∧
        MemSobolev ((n : ℝ) + 1) 2 (w : 𝓢'(ℂ, ℂ)))
    (hFS : ∀ ζ : 𝓢(ℂ, ℂ), HasCompactSupport (ζ : ℂ → ℂ) →
      tsupport (ζ : ℂ → ℂ) ⊆ V → ∃ q : Lp ℂ 2 (volume : Measure ℂ),
        q =ᵐ[volume] (fun z => ζ z * (F z : ℂ)) ∧
        MemSobolev (n : ℝ) 2 (q : 𝓢'(ℂ, ℂ))) :
    ∀ ζ : 𝓢(ℂ, ℂ), HasCompactSupport (ζ : ℂ → ℂ) →
      tsupport (ζ : ℂ → ℂ) ⊆ V → ∃ r : Lp ℂ 2 (volume : Measure ℂ),
        r =ᵐ[volume] (fun z => ζ z * (u z : ℂ)) ∧
        MemSobolev ((n : ℝ) + 2) 2 (r : 𝓢'(ℂ, ℂ)) := by
  intro ζ hζc hζV
  obtain ⟨χ, hχc, hχV, hχone⟩ := exists_complex_schwartz_compact_cutoff hV hζc hζV
  obtain ⟨w, hwae, hw⟩ := huS χ hχc hχV
  obtain ⟨q, hqae, hq⟩ := hFS χ hχc hχV
  obtain ⟨r, hrae, hr, _⟩ := complexLocalWeakElliptic_cutoff_gain hV n u F a
    hu hF ha heq χ χ w q hwae hqae hw hq ζ hζc hζV hχone hχone
  exact ⟨r, hrae, hr⟩

/-- **Math.** Repeated genuine local elliptic gain: local `H¹` of the
solution and local `Hⁿ` of its forcing give local `Hⁿ⁺²`, with actual
`L²` representatives for every compact cutoff. -/
theorem complexLocalWeakElliptic_all_cutoffs_from_one
    {V : Set ℂ} (hV : IsOpen V) (n : ℕ) (u F a : ℂ → ℝ)
    (hu : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp u 2 (volume.restrict K))
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K))
    (ha : ContDiffOn ℝ ∞ a V)
    (heq : ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, u z * Δ η z) =
        ∫ z : ℂ, a z ^ 2 * (F z * η z))
    (huOne : ∀ ζ : 𝓢(ℂ, ℂ), HasCompactSupport (ζ : ℂ → ℂ) →
      tsupport (ζ : ℂ → ℂ) ⊆ V → ∃ w : Lp ℂ 2 (volume : Measure ℂ),
        w =ᵐ[volume] (fun z => ζ z * (u z : ℂ)) ∧
        MemSobolev 1 2 (w : 𝓢'(ℂ, ℂ)))
    (hFS : ∀ ζ : 𝓢(ℂ, ℂ), HasCompactSupport (ζ : ℂ → ℂ) →
      tsupport (ζ : ℂ → ℂ) ⊆ V → ∃ q : Lp ℂ 2 (volume : Measure ℂ),
        q =ᵐ[volume] (fun z => ζ z * (F z : ℂ)) ∧
        MemSobolev (n : ℝ) 2 (q : 𝓢'(ℂ, ℂ))) :
    ∀ ζ : 𝓢(ℂ, ℂ), HasCompactSupport (ζ : ℂ → ℂ) →
      tsupport (ζ : ℂ → ℂ) ⊆ V → ∃ r : Lp ℂ 2 (volume : Measure ℂ),
        r =ᵐ[volume] (fun z => ζ z * (u z : ℂ)) ∧
        MemSobolev ((n : ℝ) + 2) 2 (r : 𝓢'(ℂ, ℂ)) := by
  revert hFS
  induction n with
  | zero =>
    intro hFS
    exact complexLocalWeakElliptic_all_cutoffs_gain hV 0 u F a hu hF ha heq
      (by simpa only [Nat.cast_zero, zero_add] using huOne) hFS
  | succ n ih =>
    intro hFS
    have hFSn : ∀ ζ : 𝓢(ℂ, ℂ), HasCompactSupport (ζ : ℂ → ℂ) →
        tsupport (ζ : ℂ → ℂ) ⊆ V → ∃ q : Lp ℂ 2 (volume : Measure ℂ),
          q =ᵐ[volume] (fun z => ζ z * (F z : ℂ)) ∧
          MemSobolev (n : ℝ) 2 (q : 𝓢'(ℂ, ℂ)) := by
      intro ζ hζc hζV
      obtain ⟨q, hqae, hq⟩ := hFS ζ hζc hζV
      exact ⟨q, hqae, hq.mono (by exact_mod_cast Nat.le_succ n)⟩
    have hprev := ih hFSn
    apply complexLocalWeakElliptic_all_cutoffs_gain hV (n + 1) u F a hu hF ha heq _ hFS
    intro ζ hζc hζV
    obtain ⟨w, hwae, hw⟩ := hprev ζ hζc hζV
    refine ⟨w, hwae, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hw

/-- **Math.** Raw local `L²` weak derivative data are sufficient for the
starting order; only the actual forcing's cutoff order is supplied. -/
theorem complexLocalWeakElliptic_all_cutoffs
    {V : Set ℂ} (hV : IsOpen V) (n : ℕ) (u F a : ℂ → ℝ)
    (Du : Fin 2 → ℂ → ℝ)
    (hu : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp u 2 (volume.restrict K))
    (hDu : ∀ (j : Fin 2) (K : Set ℂ), IsCompact K → K ⊆ V →
      MemLp (Du j) 2 (volume.restrict K))
    (huw : ∀ (j : Fin 2) (η : ℂ → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, Du j z * η z) =
        -(∫ z : ℂ, u z * fderiv ℝ η z (if j = 0 then 1 else Complex.I)))
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K))
    (ha : ContDiffOn ℝ ∞ a V)
    (heq : ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, u z * Δ η z) =
        ∫ z : ℂ, a z ^ 2 * (F z * η z))
    (hFS : ∀ ζ : 𝓢(ℂ, ℂ), HasCompactSupport (ζ : ℂ → ℂ) →
      tsupport (ζ : ℂ → ℂ) ⊆ V → ∃ q : Lp ℂ 2 (volume : Measure ℂ),
        q =ᵐ[volume] (fun z => ζ z * (F z : ℂ)) ∧
        MemSobolev (n : ℝ) 2 (q : 𝓢'(ℂ, ℂ))) :
    ∀ ζ : 𝓢(ℂ, ℂ), HasCompactSupport (ζ : ℂ → ℂ) →
      tsupport (ζ : ℂ → ℂ) ⊆ V → ∃ r : Lp ℂ 2 (volume : Measure ℂ),
        r =ᵐ[volume] (fun z => ζ z * (u z : ℂ)) ∧
        MemSobolev ((n : ℝ) + 2) 2 (r : 𝓢'(ℂ, ℂ)) := by
  apply complexLocalWeakElliptic_all_cutoffs_from_one hV n u F a hu hF ha heq _ hFS
  intro ζ hζc hζV
  obtain ⟨w, hwae, hw, _, _⟩ :=
    complexLocalWeakSobolev_cutoff u Du hu hDu huw ζ hζc hζV
  exact ⟨w, hwae, hw⟩

/-- **Math.** Local `H²` of the actual forcing produces an actual real
`C²` solution representative near each point, starting only from the raw
local weak `H¹` solution and the actual compact-test PDE. -/
theorem complexLocalWeakElliptic_exists_contDiff_two
    {V : Set ℂ} (hV : IsOpen V) (u F a : ℂ → ℝ)
    (Du : Fin 2 → ℂ → ℝ)
    (hu : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp u 2 (volume.restrict K))
    (hDu : ∀ (j : Fin 2) (K : Set ℂ), IsCompact K → K ⊆ V →
      MemLp (Du j) 2 (volume.restrict K))
    (huw : ∀ (j : Fin 2) (η : ℂ → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, Du j z * η z) =
        -(∫ z : ℂ, u z * fderiv ℝ η z (if j = 0 then 1 else Complex.I)))
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K))
    (ha : ContDiffOn ℝ ∞ a V)
    (heq : ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, u z * Δ η z) =
        ∫ z : ℂ, a z ^ 2 * (F z * η z))
    (hFS : ∀ ζ : 𝓢(ℂ, ℂ), HasCompactSupport (ζ : ℂ → ℂ) →
      tsupport (ζ : ℂ → ℂ) ⊆ V → ∃ q : Lp ℂ 2 (volume : Measure ℂ),
        q =ᵐ[volume] (fun z => ζ z * (F z : ℂ)) ∧
        MemSobolev 2 2 (q : 𝓢'(ℂ, ℂ)))
    (x : ℂ) (hx : x ∈ V) :
    ∃ (W : Set ℂ) (c : ℂ → ℝ), IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      ContDiffOn ℝ 2 c W ∧ u =ᵐ[volume.restrict W] c := by
  obtain ⟨W, _, _, ζ, hW, hxW, hWV, _, _, _, _, hζc, hζV, _, _, hζone⟩ :=
    exists_complex_three_nested_cutoffs hV x hx
  obtain ⟨w, hwae, hw⟩ := complexLocalWeakElliptic_all_cutoffs hV 2 u F a Du
    hu hDu huw hF ha heq (by simpa using hFS) ζ hζc hζV
  have hw₄ : MemSobolev 4 2 (w : 𝓢'(ℂ, ℂ)) := by norm_num at hw ⊢; exact hw
  obtain ⟨f, c, hfc, hfae, hc⟩ := complex_memSobolev_four_ae_contDiff_two w hw₄
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
    simpa only [hζone z hzW, one_mul] using huz.symm.trans hcz
  exact congrArg Complex.re he

#print axioms exists_real_smooth_compact_cutoff
#print axioms complexLocalWeakElliptic_cutoff_gain
#print axioms complexLocalWeakElliptic_all_cutoffs_from_one
#print axioms complexLocalWeakElliptic_all_cutoffs
#print axioms complexLocalWeakElliptic_exists_contDiff_two

end

end SystolicGrowth
