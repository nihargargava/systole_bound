module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.MetricGluingAttainment
public import Geometry.GluingCollarFinChainGeodesic

@[expose] public section

/-!
# Actual geodesic intervals in general metric gluing

Two genuine piece segments through the same attained seam point form an
isometric interval in the original Mathlib metric quotient. Exact endpoint
attainment prevents a shorter mixed internal route. Zero-length legs and
same-copy endpoints are retained, without any curvature premise.
-/

open Set

namespace SystolicGrowth

/-- Genuine piece segments through a specified minimizing seam point give
an actual two-leg isometric interval, with its exact junction and copied
ranges. Both zero-leg cases are included. -/
theorem metricGlue_twoLeg_segment_of_seam
    {A B S : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (hA : ∀ x y : A, ∃ α : Icc (0 : ℝ) (dist x y) → A,
      Isometry α ∧ α ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        α ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (hB : ∀ x y : B, ∃ β : Icc (0 : ℝ) (dist x y) → B,
      Isometry β ∧ β ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        β ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (x : A) (y : B) (q : S)
    (hq : dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ y) =
      dist x (Φ q) + dist (Ψ q) y) :
    let L := Metric.toGlueL hΦ hΨ
    let R := Metric.toGlueR hΦ hΨ
    let d := dist (L x) (R y)
    ∃ τ : Icc (0 : ℝ) d, ∃ σ : Icc (0 : ℝ) d → Metric.GlueSpace hΦ hΨ,
      Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = L x ∧
      σ ⟨d, ⟨dist_nonneg, le_rfl⟩⟩ = R y ∧
      τ.1 = dist x (Φ q) ∧ σ τ = L (Φ q) ∧
      (∀ t, t.1 ≤ τ.1 → σ t ∈ range L) ∧
      (∀ t, τ.1 ≤ t.1 → σ t ∈ range R) := by
  dsimp only
  let L := Metric.toGlueL hΦ hΨ
  let R := Metric.toGlueR hΦ hΨ
  let a := dist x (Φ q)
  let b := dist (Ψ q) y
  obtain ⟨αA, hαA, hαzero, hαone⟩ := hA x (Φ q)
  obtain ⟨βB, hβB, hβzero, hβone⟩ := hB (Ψ q) y
  let α := L ∘ αA
  let β := R ∘ βB
  have ha : 0 ≤ a := dist_nonneg
  have hb : 0 ≤ b := dist_nonneg
  have hα : Isometry α := (Metric.toGlueL_isometry hΦ hΨ).comp hαA
  have hβ : Isometry β := (Metric.toGlueR_isometry hΦ hΨ).comp hβB
  have hjoin : α ⟨a, ⟨ha, le_rfl⟩⟩ = β ⟨0, ⟨le_rfl, hb⟩⟩ := by
    dsimp only [α, β, Function.comp_apply]
    rw [hαone, hβzero]
    exact congrFun (Metric.toGlue_commute hΦ hΨ) q
  have hd : dist (α ⟨0, ⟨le_rfl, ha⟩⟩) (β ⟨b, ⟨hb, le_rfl⟩⟩) = a + b := by
    dsimp only [α, β, Function.comp_apply]
    rw [hαzero, hβone]
    exact hq
  have hresult : ∃ τ : Icc (0 : ℝ) (a + b),
      ∃ σ : Icc (0 : ℝ) (a + b) → Metric.GlueSpace hΦ hΨ,
        Isometry σ ∧
        σ ⟨0, ⟨le_rfl, add_nonneg ha hb⟩⟩ = L x ∧
        σ ⟨a + b, ⟨add_nonneg ha hb, le_rfl⟩⟩ = R y ∧
        τ.1 = a ∧ σ τ = L (Φ q) ∧
        (∀ t, t.1 ≤ τ.1 → σ t ∈ range L) ∧
        (∀ t, τ.1 ≤ t.1 → σ t ∈ range R) := by
    obtain ⟨σ, hσ, hleft, hright⟩ :=
      exists_isometric_two_leg_interval ha hb α β hα hβ hjoin hd
    let τ : Icc (0 : ℝ) (a + b) := ⟨a, ⟨ha, le_add_of_nonneg_right hb⟩⟩
    refine ⟨τ, σ, hσ, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · simpa only [α, Function.comp_apply, hαzero] using hleft ⟨0, ⟨le_rfl, ha⟩⟩
    · simpa only [β, Function.comp_apply, b, hβone] using hright ⟨b, ⟨hb, le_rfl⟩⟩
    · simpa only [α, Function.comp_apply, a, τ, hαone] using hleft ⟨a, ⟨ha, le_rfl⟩⟩
    · intro t ht
      let s : Icc (0 : ℝ) a := ⟨t.1, ⟨t.2.1, ht⟩⟩
      have hs := hleft s
      change σ t = L (αA s) at hs
      exact ⟨_, hs.symm⟩
    · intro t ht
      let s : Icc (0 : ℝ) b := ⟨t.1 - a, ⟨by change a ≤ t.1 at ht; linarith,
        by have := t.2.2; linarith⟩⟩
      have hs := hright s
      have ht' : (⟨a + s.1, ⟨add_nonneg ha s.2.1, add_le_add le_rfl s.2.2⟩⟩ :
          Icc (0 : ℝ) (a + b)) = t := by apply Subtype.ext; dsimp [s]; ring
      rw [ht'] at hs
      exact ⟨_, hs.symm⟩
  change dist (L x) (R y) = a + b at hq
  let P : ℝ → Prop := fun d =>
    ∃ τ : Icc (0 : ℝ) d, ∃ σ : Icc (0 : ℝ) d → Metric.GlueSpace hΦ hΨ,
      Isometry σ ∧ (∀ t, t.1 = 0 → σ t = L x) ∧
      (∀ t, t.1 = d → σ t = R y) ∧ τ.1 = a ∧ σ τ = L (Φ q) ∧
      (∀ t, t.1 ≤ τ.1 → σ t ∈ range L) ∧
      (∀ t, τ.1 ≤ t.1 → σ t ∈ range R)
  have hp : P (a + b) := by
    obtain ⟨τ, σ, hσ, hstart, hfinish, hτ, hseam, hleft, hright⟩ := hresult
    refine ⟨τ, σ, hσ, ?_, ?_, hτ, hseam, hleft, hright⟩
    · intro t ht
      have ht' : t = ⟨0, ⟨le_rfl, add_nonneg ha hb⟩⟩ := Subtype.ext ht
      rw [ht']
      exact hstart
    · intro t ht
      have ht' : t = ⟨a + b, ⟨add_nonneg ha hb, le_rfl⟩⟩ := Subtype.ext ht
      rw [ht']
      exact hfinish
  have hp' : P (dist (L x) (R y)) := by rw [hq]; exact hp
  obtain ⟨τ, σ, hσ, hstart, hfinish, hτ, hseam, hleft, hright⟩ := hp'
  exact ⟨τ, σ, hσ, hstart _ rfl, hfinish _ rfl, hτ, hseam, hleft, hright⟩

/-- Every cross-piece pair has an actual two-leg geodesic through the same
attained seam point. The first piece is proper; the seam is complete. -/
theorem metricGlue_cross_exists_twoLeg_isometric_segment
    {A B S : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    [ProperSpace A] [CompleteSpace S]
    {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (hA : ∀ x y : A, ∃ α : Icc (0 : ℝ) (dist x y) → A,
      Isometry α ∧ α ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        α ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (hB : ∀ x y : B, ∃ β : Icc (0 : ℝ) (dist x y) → B,
      Isometry β ∧ β ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        β ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (x : A) (y : B) :
    let L := Metric.toGlueL hΦ hΨ
    let R := Metric.toGlueR hΦ hΨ
    let d := dist (L x) (R y)
    ∃ q : S, d = dist x (Φ q) + dist (Ψ q) y ∧
      ∃ τ : Icc (0 : ℝ) d, ∃ σ : Icc (0 : ℝ) d → Metric.GlueSpace hΦ hΨ,
        Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = L x ∧
        σ ⟨d, ⟨dist_nonneg, le_rfl⟩⟩ = R y ∧
        τ.1 = dist x (Φ q) ∧ σ τ = L (Φ q) ∧
        (∀ t, t.1 ≤ τ.1 → σ t ∈ range L) ∧
        (∀ t, τ.1 ≤ t.1 → σ t ∈ range R) := by
  dsimp only
  obtain ⟨q, hq⟩ := metricGlue_cross_dist_attained hΦ hΨ x y
  exact ⟨q, hq, metricGlue_twoLeg_segment_of_seam hΦ hΨ hA hB x y q hq⟩

private theorem exists_isometric_interval_copy
    {E M : Type*} [MetricSpace E] [MetricSpace M] (F : E → M) (hF : Isometry F)
    (x y : E)
    (h : ∃ α : Icc (0 : ℝ) (dist x y) → E,
      Isometry α ∧ α ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        α ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y) :
    ∃ σ : Icc (0 : ℝ) (dist (F x) (F y)) → M,
      Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = F x ∧
        σ ⟨dist (F x) (F y), ⟨dist_nonneg, le_rfl⟩⟩ = F y := by
  obtain ⟨α, hα, hzero, hone⟩ := h
  let P : ℝ → Prop := fun d =>
    ∃ σ : Icc (0 : ℝ) d → M, Isometry σ ∧
      (∀ t, t.1 = 0 → σ t = F x) ∧ (∀ t, t.1 = d → σ t = F y)
  have hp : P (dist x y) := by
    refine ⟨F ∘ α, hF.comp hα, ?_, ?_⟩
    · intro t ht
      have ht' : t = ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ := Subtype.ext ht
      rw [ht']
      simpa using congrArg F hzero
    · intro t ht
      have ht' : t = ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ := Subtype.ext ht
      rw [ht']
      simpa using congrArg F hone
  have hp' : P (dist (F x) (F y)) := by rw [hF.dist_eq]; exact hp
  obtain ⟨σ, hσ, hstart, hfinish⟩ := hp'
  exact ⟨σ, hσ, hstart _ rfl, hfinish _ rfl⟩

private theorem exists_isometric_interval_reverse
    {M : Type*} [MetricSpace M] (x y : M)
    (h : ∃ α : Icc (0 : ℝ) (dist x y) → M,
      Isometry α ∧ α ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        α ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y) :
    ∃ σ : Icc (0 : ℝ) (dist y x) → M,
      Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = y ∧
        σ ⟨dist y x, ⟨dist_nonneg, le_rfl⟩⟩ = x := by
  obtain ⟨α, hα, hzero, hone⟩ := h
  let ρ : Icc (0 : ℝ) (dist x y) → Icc (0 : ℝ) (dist x y) := fun t =>
    ⟨dist x y - t.1, ⟨sub_nonneg.mpr t.2.2, sub_le_self _ t.2.1⟩⟩
  have hρ : Isometry ρ := by
    apply Isometry.of_dist_eq
    intro s t
    simp only [Subtype.dist_eq, Real.dist_eq, ρ]
    rw [show dist x y - s.1 - (dist x y - t.1) = -(s.1 - t.1) by ring, abs_neg]
  let P : ℝ → Prop := fun d =>
    ∃ σ : Icc (0 : ℝ) d → M, Isometry σ ∧
      (∀ t, t.1 = 0 → σ t = y) ∧ (∀ t, t.1 = d → σ t = x)
  have hp : P (dist x y) := by
    refine ⟨α ∘ ρ, hα.comp hρ, ?_, ?_⟩
    · intro t ht
      have h0 : ρ t = ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ := by
        apply Subtype.ext
        simp [ρ, ht]
      simpa only [Function.comp_apply, h0] using hone
    · intro t ht
      have h1 : ρ t = ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ := by
        apply Subtype.ext
        simp [ρ, ht]
      simpa only [Function.comp_apply, h1] using hzero
  have hp' : P (dist y x) := by rw [dist_comm y x]; exact hp
  obtain ⟨σ, hσ, hstart, hfinish⟩ := hp'
  exact ⟨σ, hσ, hstart _ rfl, hfinish _ rfl⟩

/-- The actual metric gluing has genuine isometric geodesic intervals when
both original pieces do. This segment-existence property is stable under
iterated gluing; no glued-space segment is supplied as an input. -/
theorem metricGlue_exists_isometric_interval
    {A B S : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    [ProperSpace A] [CompleteSpace S]
    {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (hA : ∀ x y : A, ∃ α : Icc (0 : ℝ) (dist x y) → A,
      Isometry α ∧ α ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        α ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (hB : ∀ x y : B, ∃ β : Icc (0 : ℝ) (dist x y) → B,
      Isometry β ∧ β ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        β ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (x y : Metric.GlueSpace hΦ hΨ) :
    ∃ σ : Icc (0 : ℝ) (dist x y) → Metric.GlueSpace hΦ hΨ,
      Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        σ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y := by
  let L := Metric.toGlueL hΦ hΨ
  let R := Metric.toGlueR hΦ hΨ
  have hcross (u : A) (v : B) :
      ∃ σ : Icc (0 : ℝ) (dist (L u) (R v)) → Metric.GlueSpace hΦ hΨ,
        Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = L u ∧
          σ ⟨dist (L u) (R v), ⟨dist_nonneg, le_rfl⟩⟩ = R v := by
    obtain ⟨_, _, _, σ, hσ, hzero, hone, _⟩ :=
      metricGlue_cross_exists_twoLeg_isometric_segment hΦ hΨ hA hB u v
    exact ⟨σ, hσ, hzero, hone⟩
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      cases x with
      | inl u =>
        cases y with
        | inl v =>
          exact exists_isometric_interval_copy L (Metric.toGlueL_isometry hΦ hΨ) u v (hA u v)
        | inr v => exact hcross u v
      | inr u =>
        cases y with
        | inl v => exact exists_isometric_interval_reverse (L v) (R u) (hcross v u)
        | inr v =>
          exact exists_isometric_interval_copy R (Metric.toGlueR_isometry hΦ hΨ) u v (hB u v)

#print axioms metricGlue_twoLeg_segment_of_seam
#print axioms metricGlue_cross_exists_twoLeg_isometric_segment
#print axioms metricGlue_exists_isometric_interval

end SystolicGrowth
