module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaTypeIICauchy

@[expose] public section

/-!
# Joint moment aggregation for Hua's Type-II estimate

The exact outer-difference aggregate is padded only after taking norms of
the retained inner intervals. Its diagonal contributions remain explicit.
Fourth-power Hölder then reduces the positive five-shift contribution to
the cubic frequency envelope, without an analytic saving hypothesis.
-/

open scoped BigOperators

namespace SystolicGrowth.CookMagyarCircle

/-- The padded joint outer/inner moment after three outer differences. The inner
window retains both original outer vertices; padding only enlarges the shift
and base-point ranges. -/
noncomputable def huaTypeIIJointInnerMoment
    (P l D D' w P₀ a q : ℕ) (P' : ℝ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 D, ∑ k ∈ Finset.Icc 1 D,
    ∑ r ∈ Finset.Icc 1 D, ∑ u ∈ Finset.range (D' + 1),
      ‖∑ v ∈ huaTypeIIInnerWindowOnOuterVertices
          P l D D' w P₀ P' {u, u + r + k + h},
        generalCubicPhase
          (6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * h * k * r) 0 0
          (-(6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * h * k * r) *
            (w : ℝ) ^ 3) v‖

/-- A coarse eighth-moment bound for the actual common-window cubic sums.
The `648` term retains all three diagonal contributions. Only nonnegative
inner norms, not signed support weights, are enlarged to the full box. -/
theorem hua_typeII_interval_eighth_le_jointInnerMoment
    (P l D D' w a q P₀ : ℕ) (P' b c : ℝ)
    (hD : 1 ≤ D) (hDD' : D ≤ D') (hD' : D' ≤ 2 * D) :
    let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
    let A := fun v : ℕ => ((a : ℝ) / q) * (l : ℝ) ^ 3 *
      ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
    let B := fun v : ℕ => b * (l : ℝ) ^ 2 *
      ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
    let C := fun v : ℕ => c * (l : ℝ) * ((v : ℝ) - (w : ℝ))
    let S := fun v => ∑ u ∈ U v,
      generalCubicPhase (A v) (B v) (C v) 0 u
    (∑ v ∈ Finset.Icc 1 P₀, ‖S v‖ ^ 8) ≤
      648 * (P₀ : ℝ) * (D : ℝ) ^ 7 +
        1024 * (D : ℝ) ^ 4 *
          huaTypeIIJointInnerMoment P l D D' w P₀ a q P' := by
  dsimp only
  let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
  let W := fun v h => (Finset.range (D' + 1 - h)).filter
    (fun u => u ∈ U v ∧ u + h ∈ U v)
  let X := fun v h k => (Finset.range ((D' - h) + 1 - k)).filter
    (fun u => u ∈ U v ∧ u + h ∈ U v ∧
      u + k ∈ U v ∧ u + k + h ∈ U v)
  let F := fun h k r u : ℕ =>
    ‖∑ v ∈ huaTypeIIInnerWindowOnOuterVertices
        P l D D' w P₀ P' {u, u + r + k + h},
      generalCubicPhase
        (6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * h * k * r) 0 0
        (-(6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * h * k * r) *
          (w : ℝ) ^ 3) v‖
  let H := fun h k r =>
    ∑ u ∈ Finset.range ((D' - h - k) + 1 - r), F h k r u
  let G := fun h k r => ∑ u ∈ Finset.range (D' + 1), F h k r u
  let R := fun h => ∑ k ∈ Finset.Icc 1 D, ∑ r ∈ Finset.Icc 1 D, G h k r
  have hF (h k r u : ℕ) : 0 ≤ F h k r u := norm_nonneg _
  have hG (h k r : ℕ) : 0 ≤ G h k r := by
    exact Finset.sum_nonneg fun u _ => hF h k r u
  have hR (h : ℕ) : 0 ≤ R h := by
    exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun r _ => hG h k r
  have hJ : 0 ≤ huaTypeIIJointInnerMoment P l D D' w P₀ a q P' := by
    exact Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun u _ => hF h k r u
  have hJsum : (∑ h ∈ Finset.Icc 1 D, R h) =
      huaTypeIIJointInnerMoment P l D D' w P₀ a q P' := rfl
  have hcardU (v : ℕ) : (U v).card ≤ D := by
    have hc : (U v).card ≤ (Finset.Icc (D + 1) D').card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    simp only [Nat.card_Icc] at hc
    omega
  have hcardW (v h : ℕ) : (W v h).card ≤ D := by
    apply (Finset.card_le_card ?_).trans (hcardU v)
    intro u hu
    exact (Finset.mem_filter.mp hu).2.1
  have hcardX (v h k : ℕ) : (X v h k).card ≤ D := by
    apply (Finset.card_le_card ?_).trans (hcardU v)
    intro u hu
    exact (Finset.mem_filter.mp hu).2.1
  have hdiagU : (∑ v ∈ Finset.Icc 1 P₀, ((U v).card : ℝ) ^ 4) ≤
      (P₀ : ℝ) * (D : ℝ) ^ 4 := by
    calc
      _ ≤ ∑ v ∈ Finset.Icc 1 P₀, (D : ℝ) ^ 4 := by
        apply Finset.sum_le_sum
        intro v hv
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hcardU v) 4
      _ = _ := by simp [Nat.card_Icc]
  have hdiagW (h : ℕ) :
      (∑ v ∈ Finset.Icc 1 P₀, ((W v h).card : ℝ) ^ 2) ≤
        (P₀ : ℝ) * (D : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ v ∈ Finset.Icc 1 P₀, (D : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro v hv
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hcardW v h) 2
      _ = _ := by simp [Nat.card_Icc]
  have hdiagX (h k : ℕ) :
      (∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) ≤
        (P₀ : ℝ) * (D : ℝ) := by
    calc
      _ ≤ ∑ v ∈ Finset.Icc 1 P₀, (D : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        exact_mod_cast hcardX v h k
      _ = _ := by simp [Nat.card_Icc]
  have hH (h k r : ℕ) : H h k r ≤ G h k r := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega))
    intro u hu hu'
    exact hF h k r u
  have hshift (h : ℕ) :
      (∑ k ∈ Finset.Icc 1 (D - h),
        ∑ r ∈ Finset.Icc 1 (D - h - k), H h k r) ≤ R h := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 (D - h),
          ∑ r ∈ Finset.Icc 1 D, G h k r := by
        apply Finset.sum_le_sum
        intro k hk
        calc
          _ ≤ ∑ r ∈ Finset.Icc 1 (D - h - k), G h k r :=
            Finset.sum_le_sum fun r _ => hH h k r
          _ ≤ ∑ r ∈ Finset.Icc 1 D, G h k r := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc le_rfl (by omega))
            intro r hr hr'
            exact hG h k r
      _ ≤ R h := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc le_rfl (by omega))
        intro k hk hk'
        exact Finset.sum_nonneg fun r _ => hG h k r
  have hdiagK (h : ℕ) :
      (∑ k ∈ Finset.Icc 1 (D - h),
        ∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) ≤
      (P₀ : ℝ) * (D : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 (D - h), (P₀ : ℝ) * (D : ℝ) :=
        Finset.sum_le_sum fun k _ => hdiagX h k
      _ = ((D - h : ℕ) : ℝ) * ((P₀ : ℝ) * (D : ℝ)) := by
        simp [Nat.card_Icc]
      _ ≤ (D : ℝ) * ((P₀ : ℝ) * (D : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le D h)
          (by positivity)
      _ = _ := by ring
  have hbracket (h : ℕ) :
      (∑ v ∈ Finset.Icc 1 P₀, ((W v h).card : ℝ) ^ 2) +
        4 * (∑ k ∈ Finset.Icc 1 (D - h),
          ((∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) +
            2 * (∑ r ∈ Finset.Icc 1 (D - h - k), H h k r))) ≤
      5 * (P₀ : ℝ) * (D : ℝ) ^ 2 + 8 * R h := by
    rw [Finset.sum_add_distrib]
    simp only [← Finset.mul_sum]
    have hw := hdiagW h
    have hk := hdiagK h
    have hr := hshift h
    linarith
  have houter :
      (∑ h ∈ Finset.Icc 1 D,
        (((D - h + 1 : ℕ) : ℝ)) *
          ((∑ v ∈ Finset.Icc 1 P₀, ((W v h).card : ℝ) ^ 2) +
            4 * (∑ k ∈ Finset.Icc 1 (D - h),
              ((∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) +
                2 * (∑ r ∈ Finset.Icc 1 (D - h - k), H h k r))))) ≤
        5 * (P₀ : ℝ) * (D : ℝ) ^ 4 +
          8 * (D : ℝ) * huaTypeIIJointInnerMoment P l D D' w P₀ a q P' := by
    calc
      _ ≤ ∑ h ∈ Finset.Icc 1 D,
          (D : ℝ) * (5 * (P₀ : ℝ) * (D : ℝ) ^ 2 + 8 * R h) := by
        apply Finset.sum_le_sum
        intro h hh
        calc
          _ ≤ (((D - h + 1 : ℕ) : ℝ)) *
              (5 * (P₀ : ℝ) * (D : ℝ) ^ 2 + 8 * R h) :=
            mul_le_mul_of_nonneg_left (hbracket h) (by positivity)
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right ?_ (by positivity)
            have hh' := Finset.mem_Icc.mp hh
            exact_mod_cast (show D - h + 1 ≤ D by omega)
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        rw [hJsum]
        push_cast
        ring
  have hinterior :
      (∑ v ∈ Finset.Icc 1 P₀, ((U v).card : ℝ) ^ 4) +
        16 * (∑ h ∈ Finset.Icc 1 D,
          (((D - h + 1 : ℕ) : ℝ)) *
            ((∑ v ∈ Finset.Icc 1 P₀, ((W v h).card : ℝ) ^ 2) +
              4 * (∑ k ∈ Finset.Icc 1 (D - h),
                ((∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) +
                  2 * (∑ r ∈ Finset.Icc 1 (D - h - k), H h k r))))) ≤
        81 * (P₀ : ℝ) * (D : ℝ) ^ 4 +
          128 * (D : ℝ) * huaTypeIIJointInnerMoment P l D D' w P₀ a q P' := by
    linarith
  have hpref : (((D + 1 : ℕ) : ℝ) ^ 3) ≤ 8 * (D : ℝ) ^ 3 := by
    calc
      _ ≤ (2 * (D : ℝ)) ^ 3 := by
        apply pow_le_pow_left₀ (by positivity)
        exact_mod_cast (show D + 1 ≤ 2 * D by omega)
      _ = _ := by ring
  have hbase := hua_typeII_interval_eighth_threeOuterShift_innerIntervals
    P l D D' w a q P₀ P' b c hDD' hD'
  calc
    _ ≤ (((D + 1 : ℕ) : ℝ) ^ 3) *
        ((∑ v ∈ Finset.Icc 1 P₀, ((U v).card : ℝ) ^ 4) +
          16 * (∑ h ∈ Finset.Icc 1 D,
            (((D - h + 1 : ℕ) : ℝ)) *
              ((∑ v ∈ Finset.Icc 1 P₀, ((W v h).card : ℝ) ^ 2) +
                4 * (∑ k ∈ Finset.Icc 1 (D - h),
                  ((∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) +
                    2 * (∑ r ∈ Finset.Icc 1 (D - h - k), H h k r)))))) := hbase
    _ ≤ (((D + 1 : ℕ) : ℝ) ^ 3) *
        (81 * (P₀ : ℝ) * (D : ℝ) ^ 4 +
          128 * (D : ℝ) * huaTypeIIJointInnerMoment P l D D' w P₀ a q P') :=
      mul_le_mul_of_nonneg_left hinterior (by positivity)
    _ ≤ (8 * (D : ℝ) ^ 3) *
        (81 * (P₀ : ℝ) * (D : ℝ) ^ 4 +
          128 * (D : ℝ) * huaTypeIIJointInnerMoment P l D D' w P₀ a q P') :=
      mul_le_mul_of_nonneg_right hpref (by positivity)
    _ = _ := by ring

/-- Joint fourth-moment Hölder aggregation of the exact variable inner-window
fourth-power bound. The cubic shift box keeps all three outer and two inner
positive shifts, and no cancellation estimate is assumed. -/
theorem hua_typeII_jointInnerMoment_four_le_frequencyEnvelope
    (P l D D' w P₀ a q : ℕ) (P' : ℝ) :
    huaTypeIIJointInnerMoment P l D D' w P₀ a q P' ^ 4 ≤
      (D : ℝ) ^ 9 * (((D' + 1 : ℕ) : ℝ) ^ 4) *
        (6 * (D : ℝ) ^ 3 * (P₀ : ℝ) ^ 3 +
          16 * (P₀ : ℝ) *
            (∑ x ∈ huaTypeIICubicShiftBox D P₀,
              linearDistanceEnvelope (P₀ : ℝ)
                (((a : ℝ) / q) *
                  (huaTypeIICubicShiftFrequency l x : ℝ)))) := by
  let I := Finset.Icc 1 D
  let O := Finset.range (D' + 1)
  let S := I.product (I.product (I.product O))
  let f : ℕ × (ℕ × (ℕ × ℕ)) → ℝ := fun x =>
    ‖∑ v ∈ huaTypeIIInnerWindowOnOuterVertices
        P l D D' w P₀ P' {x.2.2.2, x.2.2.2 + x.2.2.1 + x.2.1 + x.1},
      generalCubicPhase
        (6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * x.1 * x.2.1 * x.2.2.1) 0 0
        (-(6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * x.1 * x.2.1 * x.2.2.1) *
          (w : ℝ) ^ 3) v‖
  let G : ℕ → ℕ → ℕ → ℝ := fun h k r =>
    ∑ η₁ ∈ Finset.Icc 1 P₀, ∑ η₂ ∈ Finset.Icc 1 P₀,
      linearDistanceEnvelope (P₀ : ℝ)
        (((a : ℝ) / q) *
          (huaTypeIICubicShiftFrequency l (h, k, r, η₁, η₂) : ℝ))
  have hL : huaTypeIIJointInnerMoment P l D D' w P₀ a q P' =
      ∑ x ∈ S, f x := by
    simp [huaTypeIIJointInnerMoment, S, I, O, f, Finset.sum_product]
  have hcard : ((S.card : ℝ) ^ 3) =
      (D : ℝ) ^ 9 * (((D' + 1 : ℕ) : ℝ) ^ 3) := by
    simp [S, I, O, Nat.card_Icc, Finset.card_product]
    ring
  have hpoint (x : ℕ × (ℕ × (ℕ × ℕ))) (_hx : x ∈ S) :
      f x ^ 4 ≤ 6 * (P₀ : ℝ) ^ 3 +
        16 * (P₀ : ℝ) * G x.1 x.2.1 x.2.2.1 := by
    rcases x with ⟨h, k, r, u⟩
    exact hua_typeII_innerWindow_four_le_mixedFrequency_envelope
      P l D D' w P₀ a q h k r P' {u, u + r + k + h}
  have hbox :
      (∑ h ∈ I, ∑ k ∈ I, ∑ r ∈ I, G h k r) =
        ∑ x ∈ huaTypeIICubicShiftBox D P₀,
          linearDistanceEnvelope (P₀ : ℝ)
            (((a : ℝ) / q) *
              (huaTypeIICubicShiftFrequency l x : ℝ)) := by
    simp [G, I, huaTypeIICubicShiftBox, Finset.sum_product]
  have hsum :
      (∑ x ∈ S, f x ^ 4) ≤
        (((D' + 1 : ℕ) : ℝ)) *
          (6 * (D : ℝ) ^ 3 * (P₀ : ℝ) ^ 3 +
            16 * (P₀ : ℝ) *
              (∑ x ∈ huaTypeIICubicShiftBox D P₀,
                linearDistanceEnvelope (P₀ : ℝ)
                  (((a : ℝ) / q) *
                    (huaTypeIICubicShiftFrequency l x : ℝ)))) := by
    calc
      _ ≤ ∑ x ∈ S,
          (6 * (P₀ : ℝ) ^ 3 +
            16 * (P₀ : ℝ) * G x.1 x.2.1 x.2.2.1) := by
              apply Finset.sum_le_sum
              intro x hx
              exact hpoint x hx
      _ = _ := by
        rw [← hbox]
        simp [S, I, O, Finset.sum_product, Finset.sum_add_distrib,
          Finset.sum_const, ← Finset.mul_sum, Nat.card_Icc]
        ring
  calc
    huaTypeIIJointInnerMoment P l D D' w P₀ a q P' ^ 4 =
        (∑ x ∈ S, f x) ^ 4 := by rw [hL]
    _ ≤ (S.card : ℝ) ^ 3 * (∑ x ∈ S, f x ^ 4) := by
      exact pow_sum_le_card_mul_sum_pow (fun x _hx => norm_nonneg _) 3
    _ ≤ (S.card : ℝ) ^ 3 *
        (((D' + 1 : ℕ) : ℝ)) *
          (6 * (D : ℝ) ^ 3 * (P₀ : ℝ) ^ 3 +
            16 * (P₀ : ℝ) *
              (∑ x ∈ huaTypeIICubicShiftBox D P₀,
                linearDistanceEnvelope (P₀ : ℝ)
                  (((a : ℝ) / q) *
                    (huaTypeIICubicShiftFrequency l x : ℝ)))) := by
                      have hnonneg : (0 : ℝ) ≤ (S.card : ℝ) ^ 3 := by positivity
                      simpa only [mul_assoc] using
                        (mul_le_mul_of_nonneg_left hsum hnonneg)
    _ = _ := by rw [hcard]; ring

#print axioms hua_typeII_jointInnerMoment_four_le_frequencyEnvelope

/-- The fourth power of the actual common-window eighth moment, with all
diagonals and the positive five-shift frequency envelope explicit. -/
theorem hua_typeII_interval_eighth_four_le_frequencyEnvelope
    (P l D D' w a q P₀ : ℕ) (P' b c : ℝ)
    (hD : 1 ≤ D) (hDD' : D ≤ D') (hD' : D' ≤ 2 * D) :
    let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
    let A := fun v : ℕ => ((a : ℝ) / q) * (l : ℝ) ^ 3 *
      ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
    let B := fun v : ℕ => b * (l : ℝ) ^ 2 *
      ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
    let C := fun v : ℕ => c * (l : ℝ) * ((v : ℝ) - (w : ℝ))
    let S := fun v => ∑ u ∈ U v,
      generalCubicPhase (A v) (B v) (C v) 0 u
    (∑ v ∈ Finset.Icc 1 P₀, ‖S v‖ ^ 8) ^ 4 ≤
      8 * (648 ^ 4 * (P₀ : ℝ) ^ 4 * (D : ℝ) ^ 28 +
        1024 ^ 4 * (D : ℝ) ^ 25 * (((D' + 1 : ℕ) : ℝ) ^ 4) *
          (6 * (D : ℝ) ^ 3 * (P₀ : ℝ) ^ 3 +
            16 * (P₀ : ℝ) *
              (∑ x ∈ huaTypeIICubicShiftBox D P₀,
                linearDistanceEnvelope (P₀ : ℝ)
                  (((a : ℝ) / q) *
                    (huaTypeIICubicShiftFrequency l x : ℝ))))) := by
  dsimp only
  let J := huaTypeIIJointInnerMoment P l D D' w P₀ a q P'
  have hJ : 0 ≤ J := by
    dsimp [J, huaTypeIIJointInnerMoment]
    exact Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun u _ => norm_nonneg _
  have hbase := hua_typeII_interval_eighth_le_jointInnerMoment
    P l D D' w a q P₀ P' b c hD hDD' hD'
  have hinner := hua_typeII_jointInnerMoment_four_le_frequencyEnvelope
    P l D D' w P₀ a q P'
  calc
    _ ≤ (648 * (P₀ : ℝ) * (D : ℝ) ^ 7 + 1024 * (D : ℝ) ^ 4 * J) ^ 4 :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun v _ => by positivity) hbase 4
    _ ≤ 8 * ((648 * (P₀ : ℝ) * (D : ℝ) ^ 7) ^ 4 +
        (1024 * (D : ℝ) ^ 4 * J) ^ 4) := by
      have h := add_pow_le
        (show 0 ≤ 648 * (P₀ : ℝ) * (D : ℝ) ^ 7 by positivity)
        (show 0 ≤ 1024 * (D : ℝ) ^ 4 * J by positivity) 4
      norm_num at h
      exact h
    _ = 8 * (648 ^ 4 * (P₀ : ℝ) ^ 4 * (D : ℝ) ^ 28 +
        1024 ^ 4 * (D : ℝ) ^ 16 * J ^ 4) := by ring
    _ ≤ 8 * (648 ^ 4 * (P₀ : ℝ) ^ 4 * (D : ℝ) ^ 28 +
        1024 ^ 4 * (D : ℝ) ^ 16 *
          ((D : ℝ) ^ 9 * (((D' + 1 : ℕ) : ℝ) ^ 4) *
            (6 * (D : ℝ) ^ 3 * (P₀ : ℝ) ^ 3 +
              16 * (P₀ : ℝ) *
                (∑ x ∈ huaTypeIICubicShiftBox D P₀,
                  linearDistanceEnvelope (P₀ : ℝ)
                    (((a : ℝ) / q) *
                      (huaTypeIICubicShiftFrequency l x : ℝ)))))) := by
      apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hinner (by positivity))
    _ = _ := by ring

#print axioms hua_typeII_interval_eighth_le_jointInnerMoment
#print axioms hua_typeII_interval_eighth_four_le_frequencyEnvelope

/-- Scalar normalization of the explicit moment polynomial. The three
terms are precisely the outer diagonal, inner diagonal and frequency
envelope losses; the generous constant avoids later fractional roots. -/
theorem hua_typeII_moment_polynomial_le_normalized
    (D D' N : ℕ) (E : ℝ) (hD : 1 ≤ D) (hD' : D' ≤ 2 * D)
    (hN : 0 < N) (hE : 0 ≤ E) :
    8 * (648 ^ 4 * (N : ℝ) ^ 4 * (D : ℝ) ^ 28 +
      1024 ^ 4 * (D : ℝ) ^ 25 * (((D' + 1 : ℕ) : ℝ) ^ 4) *
        (6 * (D : ℝ) ^ 3 * (N : ℝ) ^ 3 + 16 * (N : ℝ) * E)) ≤
      (2 : ℝ) ^ 64 * (D : ℝ) ^ 32 * (N : ℝ) ^ 4 *
        (1 / (D : ℝ) ^ 4 + 1 / (N : ℝ) +
          E / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3)) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpad : (((D' + 1 : ℕ) : ℝ) ^ 4) ≤ 81 * (D : ℝ) ^ 4 := by
    calc
      _ ≤ (3 * (D : ℝ)) ^ 4 := by
        apply pow_le_pow_left₀ (by positivity)
        exact_mod_cast (show D' + 1 ≤ 3 * D by omega)
      _ = _ := by ring
  have hidentity : (D : ℝ) ^ 32 * (N : ℝ) ^ 4 *
      (1 / (D : ℝ) ^ 4 + 1 / (N : ℝ) +
        E / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3)) =
      (D : ℝ) ^ 28 * (N : ℝ) ^ 4 +
        (D : ℝ) ^ 32 * (N : ℝ) ^ 3 + (D : ℝ) ^ 29 * N * E := by
    field_simp [ne_of_gt hDR, ne_of_gt hNR]
  have hcoef1 : (8 : ℝ) * 648 ^ 4 ≤ 2 ^ 64 := by norm_num
  have hcoef2 : (8 : ℝ) * 1024 ^ 4 * 81 * 6 ≤ 2 ^ 64 := by norm_num
  have hcoef3 : (8 : ℝ) * 1024 ^ 4 * 81 * 16 ≤ 2 ^ 64 := by norm_num
  calc
    _ ≤ 8 * (648 ^ 4 * (N : ℝ) ^ 4 * (D : ℝ) ^ 28 +
        1024 ^ 4 * (D : ℝ) ^ 25 * (81 * (D : ℝ) ^ 4) *
          (6 * (D : ℝ) ^ 3 * (N : ℝ) ^ 3 + 16 * (N : ℝ) * E)) := by
      gcongr
    _ = (8 * 648 ^ 4) * ((D : ℝ) ^ 28 * (N : ℝ) ^ 4) +
        (8 * 1024 ^ 4 * 81 * 6) * ((D : ℝ) ^ 32 * (N : ℝ) ^ 3) +
        (8 * 1024 ^ 4 * 81 * 16) * ((D : ℝ) ^ 29 * N * E) := by ring
    _ ≤ (2 : ℝ) ^ 64 * ((D : ℝ) ^ 28 * (N : ℝ) ^ 4) +
        (2 : ℝ) ^ 64 * ((D : ℝ) ^ 32 * (N : ℝ) ^ 3) +
        (2 : ℝ) ^ 64 * ((D : ℝ) ^ 29 * N * E) :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hcoef1 (by positivity))
        (mul_le_mul_of_nonneg_right hcoef2 (by positivity)))
        (mul_le_mul_of_nonneg_right hcoef3 (by positivity))
    _ = (2 : ℝ) ^ 64 * ((D : ℝ) ^ 28 * (N : ℝ) ^ 4 +
        (D : ℝ) ^ 32 * (N : ℝ) ^ 3 + (D : ℝ) ^ 29 * N * E) := by ring
    _ = _ := by rw [← hidentity]; ring

#print axioms hua_typeII_moment_polynomial_le_normalized

end SystolicGrowth.CookMagyarCircle
