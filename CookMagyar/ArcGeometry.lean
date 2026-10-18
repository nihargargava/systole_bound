module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.Arcs

@[expose] public section

namespace SystolicGrowth
namespace CookMagyarArcs

/-! # Separation of cubic major arcs

Distinct reduced rational centers of denominators `q₁,q₂` are separated by
at least `1/(q₁q₂)`.  This is the elementary geometric input used when the
major-arc integral is rewritten as a sum of integrals over individual arcs.
-/

/-- Cross multiplication is injective on reduced fractions with positive
denominators. -/
theorem reduced_center_cross_ne
    {a₁ q₁ a₂ q₂ : ℕ}
    (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (hcop₁ : Nat.Coprime a₁ q₁) (hcop₂ : Nat.Coprime a₂ q₂)
    (hne : (a₁, q₁) ≠ (a₂, q₂)) :
    a₁ * q₂ ≠ a₂ * q₁ := by
  intro hcross
  have hq₁dvd : q₁ ∣ q₂ := by
    apply hcop₁.symm.dvd_of_dvd_mul_left
    exact ⟨a₂, by simpa [mul_comm] using hcross⟩
  have hq₂dvd : q₂ ∣ q₁ := by
    apply hcop₂.symm.dvd_of_dvd_mul_left
    exact ⟨a₁, by simpa [mul_comm] using hcross.symm⟩
  have hq : q₁ = q₂ := Nat.dvd_antisymm hq₁dvd hq₂dvd
  subst q₂
  have ha : a₁ = a₂ := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hq₁) hcross
  exact hne (by simp [ha])

/-- A division-free cross-product inequality gives the standard separation
bound between two rational centers. -/
theorem one_div_mul_le_abs_rationalCenter_sub_of_cross_ne
    {a₁ q₁ a₂ q₂ : ℕ}
    (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (hcross : a₁ * q₂ ≠ a₂ * q₁) :
    1 / ((q₁ : ℝ) * q₂) ≤
      |rationalCenter a₁ q₁ - rationalCenter a₂ q₂| := by
  have hq₁pos : (0 : ℝ) < q₁ := by exact_mod_cast Nat.pos_of_ne_zero hq₁
  have hq₂pos : (0 : ℝ) < q₂ := by exact_mod_cast Nat.pos_of_ne_zero hq₂
  have hdenpos : (0 : ℝ) < (q₁ : ℝ) * q₂ := mul_pos hq₁pos hq₂pos
  rcases lt_or_gt_of_ne hcross with hlt | hgt
  · have hdiffNat : 1 ≤ a₂ * q₁ - a₁ * q₂ := by omega
    have hdiffReal : (1 : ℝ) ≤ (a₂ * q₁ - a₁ * q₂ : ℕ) := by
      exact_mod_cast hdiffNat
    have hcenter :
        rationalCenter a₂ q₂ - rationalCenter a₁ q₁ =
          (a₂ * q₁ - a₁ * q₂ : ℕ) / ((q₁ : ℝ) * q₂) := by
      unfold rationalCenter
      rw [Nat.cast_sub (Nat.le_of_lt hlt)]
      push_cast
      field_simp
    have hnonneg :
        0 ≤ rationalCenter a₂ q₂ - rationalCenter a₁ q₁ := by
      rw [hcenter]
      positivity
    rw [abs_sub_comm, abs_of_nonneg hnonneg, hcenter]
    exact (div_le_div_iff_of_pos_right hdenpos).2 hdiffReal
  · have hdiffNat : 1 ≤ a₁ * q₂ - a₂ * q₁ := by omega
    have hdiffReal : (1 : ℝ) ≤ (a₁ * q₂ - a₂ * q₁ : ℕ) := by
      exact_mod_cast hdiffNat
    have hcenter :
        rationalCenter a₁ q₁ - rationalCenter a₂ q₂ =
          (a₁ * q₂ - a₂ * q₁ : ℕ) / ((q₁ : ℝ) * q₂) := by
      unfold rationalCenter
      rw [Nat.cast_sub (Nat.le_of_lt hgt)]
      push_cast
      field_simp
    have hnonneg :
        0 ≤ rationalCenter a₁ q₁ - rationalCenter a₂ q₂ := by
      rw [hcenter]
      positivity
    rw [abs_of_nonneg hnonneg, hcenter]
    exact (div_le_div_iff_of_pos_right hdenpos).2 hdiffReal

/-- Distinct reduced centers enjoy the usual `1/(q₁q₂)` separation. -/
theorem reduced_rationalCenter_separated
    {a₁ q₁ a₂ q₂ : ℕ}
    (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (hcop₁ : Nat.Coprime a₁ q₁) (hcop₂ : Nat.Coprime a₂ q₂)
    (hne : (a₁, q₁) ≠ (a₂, q₂)) :
    1 / ((q₁ : ℝ) * q₂) ≤
      |rationalCenter a₁ q₁ - rationalCenter a₂ q₂| :=
  one_div_mul_le_abs_rationalCenter_sub_of_cross_ne hq₁ hq₂
    (reduced_center_cross_ne hq₁ hq₂ hcop₁ hcop₂ hne)

/-- The same separation estimate in the actual period-one circle metric.
This version correctly handles a center near `0` and another near `1`. -/
theorem reduced_periodicDistance_separated
    {a₁ q₁ a₂ q₂ : ℕ}
    (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (ha₁ : a₁ < q₁) (ha₂ : a₂ < q₂)
    (hcop₁ : Nat.Coprime a₁ q₁) (hcop₂ : Nat.Coprime a₂ q₂)
    (hne : (a₁, q₁) ≠ (a₂, q₂)) :
    1 / ((q₁ : ℝ) * q₂) ≤
      periodicDistance (rationalCenter a₁ q₁)
        (rationalCenter a₂ q₂) := by
  let d : ℝ := rationalCenter a₁ q₁ - rationalCenter a₂ q₂
  let u : UnitAddCircle := (d : UnitAddCircle)
  have hqprod : 0 < q₁ * q₂ := Nat.mul_pos
    (Nat.pos_of_ne_zero hq₁) (Nat.pos_of_ne_zero hq₂)
  have hnsmul : (q₁ * q₂) • u = 0 := by
    change (q₁ * q₂) • (d : UnitAddCircle) = 0
    rw [← AddCircle.coe_nsmul]
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
    refine ⟨(a₁ : ℤ) * q₂ - (a₂ : ℤ) * q₁, ?_⟩
    simp only [zsmul_eq_mul, d, rationalCenter]
    push_cast
    have hq₁r : (q₁ : ℝ) ≠ 0 := by exact_mod_cast hq₁
    have hq₂r : (q₂ : ℝ) ≠ 0 := by exact_mod_cast hq₂
    field_simp [hq₁r, hq₂r]
    ring_nf
    simp [pow_two, mul_assoc, hq₁r, hq₂r]
  have huFinite : IsOfFinAddOrder u :=
    (isOfFinAddOrder_iff_nsmul_eq_zero).2 ⟨q₁ * q₂, hqprod, hnsmul⟩
  have hu0 : u ≠ 0 := by
    intro hu
    have hcoe :
        (rationalCenter a₁ q₁ : UnitAddCircle) =
          (rationalCenter a₂ q₂ : UnitAddCircle) := by
      have :
          (rationalCenter a₁ q₁ : UnitAddCircle) -
            (rationalCenter a₂ q₂ : UnitAddCircle) = 0 := by
        simpa [u, d, AddCircle.coe_sub] using hu
      exact sub_eq_zero.mp this
    have hq₁pos : (0 : ℝ) < q₁ := by exact_mod_cast Nat.pos_of_ne_zero hq₁
    have hq₂pos : (0 : ℝ) < q₂ := by exact_mod_cast Nat.pos_of_ne_zero hq₂
    have hc₁ : rationalCenter a₁ q₁ ∈ Set.Ico (0 : ℝ) (0 + 1) := by
      constructor
      · unfold rationalCenter
        positivity
      · simpa [rationalCenter] using (div_lt_one hq₁pos).2 (by exact_mod_cast ha₁)
    have hc₂ : rationalCenter a₂ q₂ ∈ Set.Ico (0 : ℝ) (0 + 1) := by
      constructor
      · unfold rationalCenter
        positivity
      · simpa [rationalCenter] using (div_lt_one hq₂pos).2 (by exact_mod_cast ha₂)
    have hreal : rationalCenter a₁ q₁ = rationalCenter a₂ q₂ :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico hc₁ hc₂).mp hcoe
    have hsep := reduced_rationalCenter_separated
      hq₁ hq₂ hcop₁ hcop₂ hne
    rw [hreal, sub_self, abs_zero] at hsep
    have : (0 : ℝ) < 1 / ((q₁ : ℝ) * q₂) := by positivity
    linarith
  have horddvd : addOrderOf u ∣ q₁ * q₂ :=
    (addOrderOf_dvd_iff_nsmul_eq_zero).2 hnsmul
  have hordle : addOrderOf u ≤ q₁ * q₂ :=
    Nat.le_of_dvd hqprod horddvd
  have horder := AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder
    huFinite hu0
  have hmul :
      (addOrderOf u : ℝ) * ‖u‖ ≤ ((q₁ * q₂ : ℕ) : ℝ) * ‖u‖ := by
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast hordle
    · exact norm_nonneg u
  have hone : (1 : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) * ‖u‖ := by
    have horder' : (1 : ℝ) ≤ (addOrderOf u : ℝ) * ‖u‖ := by
      simpa [nsmul_eq_mul] using horder
    exact horder'.trans hmul
  have hqprodReal : (0 : ℝ) < ((q₁ * q₂ : ℕ) : ℝ) := by exact_mod_cast hqprod
  have hdiv : 1 / (((q₁ * q₂ : ℕ) : ℝ)) ≤ ‖u‖ :=
    (div_le_iff₀ hqprodReal).2 (by simpa [mul_comm] using hone)
  simpa only [Nat.cast_mul, u, d, periodicDistance, dist_eq_norm,
    ← AddCircle.coe_sub] using hdiv

/-- The individual clipped arc around one rational center. -/
noncomputable def majorArcAt (N Q a q : ℕ) : Set ℝ :=
  {α | α ∈ Set.Icc (0 : ℝ) 1 ∧
    periodicDistance α (rationalCenter a q) < cubicArcRadius N Q}

theorem mem_majorArcAt_iff {N Q a q : ℕ} {α : ℝ} :
    α ∈ majorArcAt N Q a q ↔
      α ∈ Set.Icc (0 : ℝ) 1 ∧
        periodicDistance α (rationalCenter a q) < cubicArcRadius N Q :=
  Iff.rfl

/-- The set of major arcs is the finite union of its individual rational
neighborhoods. -/
theorem majorArcs_eq_iUnion_majorArcAt (N Q : ℕ) :
    majorArcs N Q =
      ⋃ aq ∈ majorArcCenters Q, majorArcAt N Q aq.1 aq.2 := by
  ext α
  constructor
  · rintro ⟨hIcc, a, q, haq, hdist⟩
    simp only [Set.mem_iUnion]
    exact ⟨(a, q), haq, hIcc, hdist⟩
  · intro h
    simp only [Set.mem_iUnion] at h
    obtain ⟨⟨a, q⟩, haq, hIcc, hdist⟩ := h
    exact ⟨hIcc, a, q, haq, hdist⟩

/-- Under the standard major-arc scale separation, twice the arc radius is
bounded by the reciprocal product of any two admissible denominators. -/
theorem two_cubicArcRadius_le_fraction_separation
    {N Q q₁ q₂ : ℕ}
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (hq₁Q : q₁ ≤ Q) (hq₂Q : q₂ ≤ Q)
    (hscale : 2 * Q ^ 3 ≤ N ^ 3) :
    2 * cubicArcRadius N Q ≤ 1 / ((q₁ : ℝ) * q₂) := by
  have hQpos : 0 < Q := lt_of_lt_of_le (Nat.pos_of_ne_zero hq₁0) hq₁Q
  have hNcube : 0 < N ^ 3 := lt_of_lt_of_le (by positivity) hscale
  have hNposNat : 0 < N := Nat.pos_of_ne_zero fun hN0 ↦ by
    subst N
    simp at hNcube
  have hNpos : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
  have hdenpos : (0 : ℝ) < (q₁ : ℝ) * q₂ := by
    positivity
  have hqq : q₁ * q₂ ≤ Q ^ 2 := by
    nlinarith [Nat.mul_le_mul hq₁Q hq₂Q]
  have hcrossNat : 2 * Q * (q₁ * q₂) ≤ N ^ 3 := by
    calc
      2 * Q * (q₁ * q₂) ≤ 2 * Q * Q ^ 2 :=
        Nat.mul_le_mul_left (2 * Q) hqq
      _ = 2 * Q ^ 3 := by ring
      _ ≤ N ^ 3 := hscale
  have hcrossReal :
      (2 : ℝ) * Q * ((q₁ : ℝ) * q₂) ≤ (N : ℝ) ^ 3 := by
    exact_mod_cast hcrossNat
  unfold cubicArcRadius
  rw [show (2 : ℝ) * ((Q : ℝ) / (N : ℝ) ^ 3) =
      ((2 : ℝ) * Q) / (N : ℝ) ^ 3 by ring]
  exact (div_le_div_iff₀ hNpos hdenpos).2 (by simpa using hcrossReal)

/-- Once `2Q³ ≤ N³`, distinct reduced major arcs are pairwise disjoint.
The strict radius in `majorArcAt` means equality at the boundary causes no
exception. -/
theorem majorArcAt_disjoint_of_distinct
    {N Q a₁ q₁ a₂ q₂ : ℕ}
    (hc₁ : (a₁, q₁) ∈ majorArcCenters Q)
    (hc₂ : (a₂, q₂) ∈ majorArcCenters Q)
    (hne : (a₁, q₁) ≠ (a₂, q₂))
    (hscale : 2 * Q ^ 3 ≤ N ^ 3) :
    Disjoint (majorArcAt N Q a₁ q₁) (majorArcAt N Q a₂ q₂) := by
  rw [Set.disjoint_left]
  intro α hα₁ hα₂
  have hsep := reduced_periodicDistance_separated
    hc₁.2.1 hc₂.2.1 hc₁.2.2.1 hc₂.2.2.1
      hc₁.2.2.2 hc₂.2.2.2 hne
  have hradius := two_cubicArcRadius_le_fraction_separation
    hc₁.2.1 hc₂.2.1 hc₁.1 hc₂.1 hscale
  have hclose :
      periodicDistance (rationalCenter a₁ q₁)
          (rationalCenter a₂ q₂) <
        2 * cubicArcRadius N Q := by
    calc
      periodicDistance (rationalCenter a₁ q₁)
          (rationalCenter a₂ q₂) ≤
          periodicDistance (rationalCenter a₁ q₁) α +
            periodicDistance α (rationalCenter a₂ q₂) := by
        unfold periodicDistance
        exact dist_triangle _ _ _
      _ < cubicArcRadius N Q + cubicArcRadius N Q := by
        exact add_lt_add (by
          simpa only [periodicDistance, dist_comm] using hα₁.2) hα₂.2
      _ = 2 * cubicArcRadius N Q := by ring
  exact (not_lt_of_ge (hradius.trans hsep)) hclose

theorem majorArcAt_measurableSet (N Q a q : ℕ) :
    MeasurableSet (majorArcAt N Q a q) := by
  unfold majorArcAt
  have hcont : Continuous (fun α : ℝ =>
      periodicDistance α (rationalCenter a q)) := by
    unfold periodicDistance
    exact (AddCircle.continuous_mk' (1 : ℝ)).dist
      (continuous_const : Continuous (fun _ : ℝ =>
        (rationalCenter a q : UnitAddCircle)))
  apply measurableSet_Icc.inter
  exact (isOpen_lt hcont continuous_const).measurableSet

theorem majorArcAt_subset_Icc (N Q a q : ℕ) :
    majorArcAt N Q a q ⊆ Set.Icc (0 : ℝ) 1 := by
  intro α hα
  exact hα.1

theorem cubicIntegrand_integrableOn_majorArcAt
    (n N T Q a q : ℕ) :
    MeasureTheory.IntegrableOn (cubicIntegrand n N T)
      (majorArcAt N Q a q) :=
  (cubicIntegrand_integrableOn_Icc n N T).mono_set
    (majorArcAt_subset_Icc N Q a q)

/-- Under the separation condition, the major-arc integral is literally the
finite sum of the individual rational-arc integrals. -/
theorem cubicMajorArcIntegral_eq_sum_individual
    (n N T Q : ℕ) (hscale : 2 * Q ^ 3 ≤ N ^ 3) :
    cubicMajorArcIntegral n N T Q =
      ∑ aq ∈ (majorArcCenters_finite Q).toFinset,
        ∫ α in majorArcAt N Q aq.1 aq.2,
          cubicIntegrand n N T α := by
  classical
  let centers : Finset (ℕ × ℕ) := (majorArcCenters_finite Q).toFinset
  have hmajor : majorArcs N Q = ⋃ aq ∈ centers,
      majorArcAt N Q aq.1 aq.2 := by
    rw [majorArcs_eq_iUnion_majorArcAt]
    simp only [centers, Set.Finite.mem_toFinset]
  have hpair : Set.Pairwise (↑centers)
      (fun aq₁ aq₂ : ℕ × ℕ ↦
        Disjoint (majorArcAt N Q aq₁.1 aq₁.2)
          (majorArcAt N Q aq₂.1 aq₂.2)) := by
    rintro ⟨a₁, q₁⟩ h₁ ⟨a₂, q₂⟩ h₂ hne
    apply majorArcAt_disjoint_of_distinct
    · simpa [centers] using h₁
    · simpa [centers] using h₂
    · exact hne
    · exact hscale
  unfold cubicMajorArcIntegral
  rw [hmajor]
  simpa only [centers] using
    MeasureTheory.integral_biUnion_finset centers
      (fun aq _ ↦ majorArcAt_measurableSet N Q aq.1 aq.2)
      hpair
      (fun aq _ ↦ cubicIntegrand_integrableOn_majorArcAt
        n N T Q aq.1 aq.2)

end CookMagyarArcs
end SystolicGrowth
