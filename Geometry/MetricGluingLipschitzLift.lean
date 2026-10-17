module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Topology.MetricSpace.Gluing
public import Mathlib.Data.ENNReal.Operations

@[expose] public section

/-!
# Nonexpanding maps out of the native metric gluing

Two nonexpanding maps agreeing on the seam descend through Mathlib's actual
metric separation quotient. The cross-distance estimate uses its infimum of
all seam routes, without attainment, properness or additional metric data.
-/

open Set

namespace SystolicGrowth

private theorem metricGlue_cross_map_edist_le
    {A B S T : Type*} [MetricSpace A] [MetricSpace B] [Nonempty S] [EMetricSpace T]
    (Φ : S → A) (Ψ : S → B) (f : A → T) (g : B → T)
    (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g)
    (hcomm : f ∘ Φ = g ∘ Ψ) (x : A) (y : B) :
    edist (f x) (g y) ≤ ENNReal.ofReal (⨅ q : S, dist x (Φ q) + dist y (Ψ q)) := by
  rw [ENNReal.ofReal_iInf]
  refine le_iInf fun q => ?_
  calc
    edist (f x) (g y) ≤ edist (f x) (f (Φ q)) + edist (f (Φ q)) (g y) :=
      edist_triangle _ _ _
    _ = edist (f x) (f (Φ q)) + edist (g (Ψ q)) (g y) := by
      rw [show f (Φ q) = g (Ψ q) from congrFun hcomm q]
    _ ≤ edist x (Φ q) + edist (Ψ q) y := add_le_add
      (by simpa only [ENNReal.coe_one, one_mul] using hf x (Φ q))
      (by simpa only [ENNReal.coe_one, one_mul] using hg (Ψ q) y)
    _ = ENNReal.ofReal (dist x (Φ q) + dist y (Ψ q)) := by
      rw [edist_dist, edist_dist, dist_comm (Ψ q) y,
        ENNReal.ofReal_add dist_nonneg dist_nonneg]

/-- The piecewise map is nonexpanding for the genuine gluing pseudometric. -/
theorem metricGlue_sum_lipschitz
    {A B S T : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    [EMetricSpace T] {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (f : A → T) (g : B → T) (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g)
    (hcomm : f ∘ Φ = g ∘ Ψ) :
    letI : PseudoMetricSpace (A ⊕ B) := Metric.gluePremetric hΦ hΨ
    LipschitzWith 1 (Sum.elim f g) := by
  letI : PseudoMetricSpace (A ⊕ B) := Metric.gluePremetric hΦ hΨ
  refine LipschitzWith.of_edist_le ?_
  intro u v
  rw [edist_dist]
  cases u with
  | inl x =>
    cases v with
    | inl y =>
      change edist (f x) (f y) ≤ ENNReal.ofReal (dist x y)
      simpa only [ENNReal.coe_one, one_mul, edist_dist] using hf x y
    | inr y =>
      change edist (f x) (g y) ≤
        ENNReal.ofReal ((⨅ q : S, dist x (Φ q) + dist y (Ψ q)) + 0)
      simpa only [add_zero] using
        metricGlue_cross_map_edist_le Φ Ψ f g hf hg hcomm x y
  | inr x =>
    cases v with
    | inl y =>
      change edist (g x) (f y) ≤
        ENNReal.ofReal ((⨅ q : S, dist y (Φ q) + dist x (Ψ q)) + 0)
      simpa only [add_zero, edist_comm] using
        metricGlue_cross_map_edist_le Φ Ψ f g hf hg hcomm y x
    | inr y =>
      change edist (g x) (g y) ≤ ENNReal.ofReal (dist x y)
      simpa only [ENNReal.coe_one, one_mul, edist_dist] using hg x y

/-- Descend two seam-compatible nonexpanding maps through the native
separation quotient. The following lemmas give its exact values and bound. -/
noncomputable def metricGlueLipschitzLift
    {A B S T : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    [EMetricSpace T] {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (f : A → T) (g : B → T) : Metric.GlueSpace hΦ hΨ → T :=
  @SeparationQuotient.lift' (A ⊕ B) T
    (Metric.gluePremetric hΦ hΨ).toUniformSpace _ _ (Sum.elim f g)

private theorem metricGlueLipschitzLift_mk
    {A B S T : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    [EMetricSpace T] {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (f : A → T) (g : B → T) (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g)
    (hcomm : f ∘ Φ = g ∘ Ψ) (u : A ⊕ B) :
    metricGlueLipschitzLift hΦ hΨ f g (Quotient.mk'' u) = Sum.elim f g u := by
  letI : PseudoMetricSpace (A ⊕ B) := Metric.gluePremetric hΦ hΨ
  have hsum := metricGlue_sum_lipschitz hΦ hΨ f g hf hg hcomm
  exact @SeparationQuotient.lift'_mk (A ⊕ B) T
    (Metric.gluePremetric hΦ hΨ).toUniformSpace _ _
    (Sum.elim f g) hsum.uniformContinuous u

@[simp] theorem metricGlueLipschitzLift_left
    {A B S T : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    [EMetricSpace T] {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (f : A → T) (g : B → T) (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g)
    (hcomm : f ∘ Φ = g ∘ Ψ) (x : A) :
    metricGlueLipschitzLift hΦ hΨ f g (Metric.toGlueL hΦ hΨ x) = f x := by
  exact metricGlueLipschitzLift_mk hΦ hΨ f g hf hg hcomm (.inl x)

@[simp] theorem metricGlueLipschitzLift_right
    {A B S T : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    [EMetricSpace T] {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (f : A → T) (g : B → T) (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g)
    (hcomm : f ∘ Φ = g ∘ Ψ) (x : B) :
    metricGlueLipschitzLift hΦ hΨ f g (Metric.toGlueR hΦ hΨ x) = g x := by
  exact metricGlueLipschitzLift_mk hΦ hΨ f g hf hg hcomm (.inr x)

/-- The descended map is nonexpanding on the actual metric gluing quotient. -/
theorem metricGlueLipschitzLift_lipschitz
    {A B S T : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    [EMetricSpace T] {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (f : A → T) (g : B → T) (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g)
    (hcomm : f ∘ Φ = g ∘ Ψ) :
    LipschitzWith 1 (metricGlueLipschitzLift hΦ hΨ f g) := by
  letI : PseudoMetricSpace (A ⊕ B) := Metric.gluePremetric hΦ hΨ
  have hsum := metricGlue_sum_lipschitz hΦ hΨ f g hf hg hcomm
  refine LipschitzWith.of_edist_le ?_
  intro u v
  induction u using Quotient.inductionOn with
  | h u =>
    induction v using Quotient.inductionOn with
    | h v =>
      rw [metricGlueLipschitzLift_mk hΦ hΨ f g hf hg hcomm,
        metricGlueLipschitzLift_mk hΦ hΨ f g hf hg hcomm]
      change edist (Sum.elim f g u) (Sum.elim f g v) ≤
        (Metric.gluePremetric hΦ hΨ).edist u v
      rw [(Metric.gluePremetric hΦ hΨ).edist_dist]
      simpa only [ENNReal.coe_one, one_mul, edist_dist] using hsum u v

private theorem metricStageMap_leRecOn
    {X : ℕ → Type*} {T : Type*} {i : ∀ n, X n → X (n + 1)}
    (F : ∀ n, X n → T) (hcomm : ∀ n x, F (n + 1) (i n x) = F n x)
    {n m : ℕ} (hnm : n ≤ m) (x : X n) :
    F m (Nat.leRecOn hnm (i _) x) = F n x := by
  induction m, hnm using Nat.le_induction with
  | base => simp only [Nat.leRecOn_self]
  | succ m hnm ih =>
    rw [Nat.leRecOn_succ hnm, hcomm]
    exact ih

/-- Compatible nonexpanding stage maps are nonexpanding for Mathlib's
native inductive-limit pseudometric on the disjoint union of stages. -/
theorem metricInductiveLimit_stageMap_lipschitz
    {X : ℕ → Type*} [∀ n, MetricSpace (X n)] {T : Type*} [EMetricSpace T]
    {i : ∀ n, X n → X (n + 1)} (I : ∀ n, Isometry (i n))
    (F : ∀ n, X n → T) (hF : ∀ n, LipschitzWith 1 (F n))
    (hcomm : ∀ n x, F (n + 1) (i n x) = F n x) :
    letI : PseudoMetricSpace (Σ n, X n) := Metric.inductivePremetric I
    LipschitzWith 1 (fun x : Σ n, X n => F x.1 x.2) := by
  letI : PseudoMetricSpace (Σ n, X n) := Metric.inductivePremetric I
  refine LipschitzWith.of_edist_le ?_
  intro x y
  rw [edist_dist]
  change edist (F x.1 x.2) (F y.1 y.2) ≤ ENNReal.ofReal (Metric.inductiveLimitDist i x y)
  let m := max x.1 y.1
  let a : X m := Nat.leRecOn (C := X) (Nat.le_max_left x.1 y.1) (i _) x.2
  let b : X m := Nat.leRecOn (C := X) (Nat.le_max_right x.1 y.1) (i _) y.2
  have ha : F m a = F x.1 x.2 :=
    metricStageMap_leRecOn F hcomm (Nat.le_max_left x.1 y.1) x.2
  have hb : F m b = F y.1 y.2 :=
    metricStageMap_leRecOn F hcomm (Nat.le_max_right x.1 y.1) y.2
  calc
    edist (F x.1 x.2) (F y.1 y.2) = edist (F m a) (F m b) := by rw [ha, hb]
    _ ≤ edist a b := by simpa only [ENNReal.coe_one, one_mul] using hF m a b
    _ = ENNReal.ofReal (Metric.inductiveLimitDist i x y) := by rw [edist_dist]; rfl

/-- Descend compatible stage maps through the actual metric inductive limit. -/
noncomputable def metricInductiveLimitLipschitzLift
    {X : ℕ → Type*} [∀ n, MetricSpace (X n)] {T : Type*} [EMetricSpace T]
    {i : ∀ n, X n → X (n + 1)} (I : ∀ n, Isometry (i n))
    (F : ∀ n, X n → T) : Metric.InductiveLimit I → T :=
  @SeparationQuotient.lift' (Σ n, X n) T
    (Metric.inductivePremetric I).toUniformSpace _ _ (fun x => F x.1 x.2)

private theorem metricInductiveLimitLipschitzLift_mk
    {X : ℕ → Type*} [∀ n, MetricSpace (X n)] {T : Type*} [EMetricSpace T]
    {i : ∀ n, X n → X (n + 1)} (I : ∀ n, Isometry (i n))
    (F : ∀ n, X n → T) (hF : ∀ n, LipschitzWith 1 (F n))
    (hcomm : ∀ n x, F (n + 1) (i n x) = F n x) (x : Σ n, X n) :
    metricInductiveLimitLipschitzLift I F (Quotient.mk'' x) = F x.1 x.2 := by
  letI : PseudoMetricSpace (Σ n, X n) := Metric.inductivePremetric I
  have hstage := metricInductiveLimit_stageMap_lipschitz I F hF hcomm
  exact @SeparationQuotient.lift'_mk (Σ n, X n) T
    (Metric.inductivePremetric I).toUniformSpace _ _
    (fun x => F x.1 x.2) hstage.uniformContinuous x

/-- Exact evaluation of the descended map on each original finite stage. -/
@[simp] theorem metricInductiveLimitLipschitzLift_eval
    {X : ℕ → Type*} [∀ n, MetricSpace (X n)] {T : Type*} [EMetricSpace T]
    {i : ∀ n, X n → X (n + 1)} (I : ∀ n, Isometry (i n))
    (F : ∀ n, X n → T) (hF : ∀ n, LipschitzWith 1 (F n))
    (hcomm : ∀ n x, F (n + 1) (i n x) = F n x) (n : ℕ) (x : X n) :
    metricInductiveLimitLipschitzLift I F (Metric.toInductiveLimit I n x) = F n x :=
  metricInductiveLimitLipschitzLift_mk I F hF hcomm ⟨n, x⟩

/-- The compatible-stage lift is nonexpanding on the native metric limit. -/
theorem metricInductiveLimitLipschitzLift_lipschitz
    {X : ℕ → Type*} [∀ n, MetricSpace (X n)] {T : Type*} [EMetricSpace T]
    {i : ∀ n, X n → X (n + 1)} (I : ∀ n, Isometry (i n))
    (F : ∀ n, X n → T) (hF : ∀ n, LipschitzWith 1 (F n))
    (hcomm : ∀ n x, F (n + 1) (i n x) = F n x) :
    LipschitzWith 1 (metricInductiveLimitLipschitzLift I F) := by
  letI : PseudoMetricSpace (Σ n, X n) := Metric.inductivePremetric I
  have hstage := metricInductiveLimit_stageMap_lipschitz I F hF hcomm
  refine LipschitzWith.of_edist_le ?_
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      rw [metricInductiveLimitLipschitzLift_mk I F hF hcomm,
        metricInductiveLimitLipschitzLift_mk I F hF hcomm]
      change edist (F x.1 x.2) (F y.1 y.2) ≤ (Metric.inductivePremetric I).edist x y
      rw [(Metric.inductivePremetric I).edist_dist]
      simpa only [ENNReal.coe_one, one_mul, edist_dist] using hstage x y

#print axioms metricGlue_sum_lipschitz
#print axioms metricGlueLipschitzLift_lipschitz
#print axioms metricGlueLipschitzLift_left
#print axioms metricGlueLipschitzLift_right
#print axioms metricInductiveLimit_stageMap_lipschitz
#print axioms metricInductiveLimitLipschitzLift_lipschitz
#print axioms metricInductiveLimitLipschitzLift_eval

end SystolicGrowth
