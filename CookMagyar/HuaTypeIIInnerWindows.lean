module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaTypeIIDifferencing
public import CookMagyar.HuaTypeIIInnerWeyl
public import CookMagyar.HuaTypeIIExceptionalFrequency
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# Inner intervals after exchanging Hua's outer-shift sums

Keep the outer vertex index when exchanging sums. For any finite set of
outer vertices, the surviving positive inner indices form an actual interval,
not an arbitrary subset with an assumed cancellation bound. The source's
strict lower and weak upper common-window tests are retained exactly.
-/

namespace SystolicGrowth.CookMagyarCircle

open scoped BigOperators

/-- Positive inner indices whose original common windows contain every
specified outer vertex. This is the support after fixing the outer vertices,
not an enlargement of a signed exponential sum. -/
noncomputable def huaTypeIIInnerWindowOnOuterVertices
    (P l D D' w P₀ : ℕ) (P' : ℝ) (R : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 P₀).filter (fun v =>
    ∀ u ∈ R, u ∈ huaTypeIICommonOuterWindow P l D D' v w P')

/-- Membership retains the positive interval bound and every original
outer-vertex membership test. -/
theorem mem_huaTypeIIInnerWindowOnOuterVertices_iff
    (P l D D' w P₀ v : ℕ) (P' : ℝ) (R : Finset ℕ) :
    v ∈ huaTypeIIInnerWindowOnOuterVertices P l D D' w P₀ P' R ↔
      1 ≤ v ∧ v ≤ P₀ ∧
        ∀ u ∈ R, u ∈ huaTypeIICommonOuterWindow P l D D' v w P' := by
  simp only [huaTypeIIInnerWindowOnOuterVertices, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- Intermediate positive inner indices preserve all common-window tests.
No positivity or cancellation assumption on the lower source endpoint is
needed: monotonicity is applied to multiplication by natural outer vertices. -/
theorem hua_typeII_innerWindow_mem_of_between
    (P l D D' w P₀ : ℕ) (P' : ℝ) (R : Finset ℕ)
    {v₁ v₂ v : ℕ}
    (hv₁ : v₁ ∈ huaTypeIIInnerWindowOnOuterVertices P l D D' w P₀ P' R)
    (hv₂ : v₂ ∈ huaTypeIIInnerWindowOnOuterVertices P l D D' w P₀ P' R)
    (hlo : v₁ ≤ v) (hhi : v ≤ v₂) :
    v ∈ huaTypeIIInnerWindowOnOuterVertices P l D D' w P₀ P' R := by
  obtain ⟨h1lo, h1hi, h1⟩ :=
    (mem_huaTypeIIInnerWindowOnOuterVertices_iff P l D D' w P₀ v₁ P' R).1 hv₁
  obtain ⟨h2lo, h2hi, h2⟩ :=
    (mem_huaTypeIIInnerWindowOnOuterVertices_iff P l D D' w P₀ v₂ P' R).1 hv₂
  have hvpos : 0 < v := lt_of_lt_of_le (by omega : 0 < v₁) hlo
  have hv₁R : (0 : ℝ) < v₁ := by exact_mod_cast (by omega : 0 < v₁)
  have hv₂R : (0 : ℝ) < v₂ := by exact_mod_cast (by omega : 0 < v₂)
  have hvR : (0 : ℝ) < v := by exact_mod_cast hvpos
  have hloR : (v₁ : ℝ) ≤ v := by exact_mod_cast hlo
  have hhiR : (v : ℝ) ≤ v₂ := by exact_mod_cast hhi
  apply (mem_huaTypeIIInnerWindowOnOuterVertices_iff P l D D' w P₀ v P' R).2
  refine ⟨h1lo.trans hlo, hhi.trans h2hi, ?_⟩
  intro u hu
  obtain ⟨hDu, huD', h1lower, _, hwlower, hwupper⟩ :=
    (mem_huaTypeIICommonOuterWindow_iff P l D D' v₁ w u P').1 (h1 u hu)
  obtain ⟨_, _, _, h2upper, _, _⟩ :=
    (mem_huaTypeIICommonOuterWindow_iff P l D D' v₂ w u P').1 (h2 u hu)
  have hprodlo : (u : ℝ) * v₁ ≤ (u : ℝ) * v :=
    mul_le_mul_of_nonneg_left hloR (Nat.cast_nonneg u)
  have hprodhi : (u : ℝ) * v ≤ (u : ℝ) * v₂ :=
    mul_le_mul_of_nonneg_left hhiR (Nat.cast_nonneg u)
  have hlower : P' / (v : ℝ) < (u : ℝ) :=
    (div_lt_iff₀ hvR).2 (((div_lt_iff₀ hv₁R).1 h1lower).trans_le hprodlo)
  have hupper : (u : ℝ) ≤ ((P : ℝ) / l) / v :=
    (le_div_iff₀ hvR).2 (hprodhi.trans ((le_div_iff₀ hv₂R).1 h2upper))
  exact (mem_huaTypeIICommonOuterWindow_iff P l D D' v w u P').2
    ⟨hDu, huD', hlower, hupper, hwlower, hwupper⟩

/-- The surviving inner support is exactly one finite positive interval.
An empty support is represented by `Icc 1 0`; nonempty endpoints are its
actual minimum and maximum. -/
theorem exists_huaTypeIIInnerWindowOnOuterVertices_eq_Icc
    (P l D D' w P₀ : ℕ) (P' : ℝ) (R : Finset ℕ) :
    ∃ lo hi : ℕ, 1 ≤ lo ∧ hi ≤ P₀ ∧
      huaTypeIIInnerWindowOnOuterVertices P l D D' w P₀ P' R = Finset.Icc lo hi := by
  classical
  let W := huaTypeIIInnerWindowOnOuterVertices P l D D' w P₀ P' R
  by_cases hW : W.Nonempty
  · refine ⟨W.min' hW, W.max' hW, ?_, ?_, ?_⟩
    · exact ((mem_huaTypeIIInnerWindowOnOuterVertices_iff
        P l D D' w P₀ (W.min' hW) P' R).1 (W.min'_mem hW)).1
    · exact ((mem_huaTypeIIInnerWindowOnOuterVertices_iff
        P l D D' w P₀ (W.max' hW) P' R).1 (W.max'_mem hW)).2.1
    · change W = Finset.Icc (W.min' hW) (W.max' hW)
      ext v
      constructor
      · intro hv
        exact Finset.mem_Icc.mpr ⟨W.min'_le v hv, W.le_max' v hv⟩
      · intro hv
        exact hua_typeII_innerWindow_mem_of_between P l D D' w P₀ P' R
          (W.min'_mem hW) (W.max'_mem hW)
          (Finset.mem_Icc.mp hv).1 (Finset.mem_Icc.mp hv).2
  · refine ⟨1, 0, le_refl _, Nat.zero_le _, ?_⟩
    change W = Finset.Icc 1 0
    rw [Finset.not_nonempty_iff_eq_empty.mp hW]
    simp

/-- Exchanging the finite sums retains the outer index and replaces its
support predicate by the exact inner interval, without losing a signed
support multiplicity. -/
theorem sum_huaTypeIIInnerWindowOnOuterVertices_swap
    (P l D D' w P₀ : ℕ) (P' : ℝ)
    (O : Finset ℕ) (R : ℕ → Finset ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ v ∈ Finset.Icc 1 P₀,
      ∑ u ∈ O.filter (fun u =>
        ∀ r ∈ R u, r ∈ huaTypeIICommonOuterWindow P l D D' v w P'), f v u) =
      ∑ u ∈ O,
        ∑ v ∈ huaTypeIIInnerWindowOnOuterVertices P l D D' w P₀ P' (R u),
          f v u := by
  classical
  unfold huaTypeIIInnerWindowOnOuterVertices
  simp_rw [Finset.sum_filter]
  exact Finset.sum_comm

/-- Triangle inequality after the exact exchange: cancellation is used only
inside each surviving inner interval, never for an arbitrary signed weight. -/
theorem norm_sum_huaTypeIIInnerWindowOnOuterVertices_le
    (P l D D' w P₀ : ℕ) (P' : ℝ)
    (O : Finset ℕ) (R : ℕ → Finset ℕ) (f : ℕ → ℕ → ℂ) :
    ‖∑ v ∈ Finset.Icc 1 P₀,
      ∑ u ∈ O.filter (fun u =>
        ∀ r ∈ R u, r ∈ huaTypeIICommonOuterWindow P l D D' v w P'), f v u‖ ≤
      ∑ u ∈ O,
        ‖∑ v ∈ huaTypeIIInnerWindowOnOuterVertices P l D D' w P₀ P' (R u),
          f v u‖ := by
  rw [sum_huaTypeIIInnerWindowOnOuterVertices_swap]
  exact norm_sum_le _ _

/-- The two extreme vertices give exactly the original eight outer-shift
tests, so the general interval result applies to the actual cubic cube. -/
theorem mem_huaTypeIIInnerWindowOnOuterCube_iff
    (P l D D' w P₀ v u ξ₁ ξ₂ ξ₃ : ℕ) (P' : ℝ) :
    let U := huaTypeIICommonOuterWindow P l D D' v w P'
    v ∈ huaTypeIIInnerWindowOnOuterVertices P l D D' w P₀ P'
      {u, u + ξ₃ + ξ₂ + ξ₁} ↔
      1 ≤ v ∧ v ≤ P₀ ∧
        (u ∈ U ∧ u + ξ₁ ∈ U ∧ u + ξ₂ ∈ U ∧ u + ξ₂ + ξ₁ ∈ U ∧
          u + ξ₃ ∈ U ∧ u + ξ₃ + ξ₁ ∈ U ∧ u + ξ₃ + ξ₂ ∈ U ∧
          u + ξ₃ + ξ₂ + ξ₁ ∈ U) := by
  dsimp only
  rw [mem_huaTypeIIInnerWindowOnOuterVertices_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  have hcube := hua_typeII_commonWindow_eightShift_iff_endpoints
    P l D D' v w u ξ₁ ξ₂ ξ₃ P'
  dsimp only at hcube
  rw [hcube]

/-- The third outer difference, constant in the outer variable, is the
actual cubic phase in the inner variable with its fixed paired constant. -/
theorem hua_typeII_thirdOuterPhase_eq_innerCubicPhase
    (a q l w u v ξ₁ ξ₂ ξ₃ : ℕ) :
    generalCubicPhase 0 0 0
      (6 * (((a : ℝ) / q) * (l : ℝ) ^ 3 *
        ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)) * ξ₁ * ξ₂ * ξ₃) u =
      generalCubicPhase
        (6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * ξ₁ * ξ₂ * ξ₃) 0 0
        (-(6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * ξ₁ * ξ₂ * ξ₃) * (w : ℝ) ^ 3) v := by
  unfold generalCubicPhase generalCubicPolynomial
  congr 1
  push_cast
  ring

/-- After three outer differences, retain the outer index in the finite
exchange and use triangle inequality only outside the actual inner intervals.
All eight original outer membership tests remain on the left. -/
theorem hua_typeII_threeOuter_sum_norm_le_innerWindow_norm_sum
    (P l D D' w P₀ a q ξ₁ ξ₂ ξ₃ : ℕ) (P' : ℝ) (O : Finset ℕ) :
    let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
    let θ := 6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * ξ₁ * ξ₂ * ξ₃
    ‖∑ v ∈ Finset.Icc 1 P₀,
      ∑ u ∈ O.filter (fun u =>
        u ∈ U v ∧ u + ξ₁ ∈ U v ∧ u + ξ₂ ∈ U v ∧ u + ξ₂ + ξ₁ ∈ U v ∧
          u + ξ₃ ∈ U v ∧ u + ξ₃ + ξ₁ ∈ U v ∧ u + ξ₃ + ξ₂ ∈ U v ∧
          u + ξ₃ + ξ₂ + ξ₁ ∈ U v),
        generalCubicPhase 0 0 0
          (6 * (((a : ℝ) / q) * (l : ℝ) ^ 3 *
            ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)) * ξ₁ * ξ₂ * ξ₃) u‖ ≤
      ∑ u ∈ O,
        ‖∑ v ∈ huaTypeIIInnerWindowOnOuterVertices P l D D' w P₀ P'
            {u, u + ξ₃ + ξ₂ + ξ₁},
          generalCubicPhase θ 0 0 (-θ * (w : ℝ) ^ 3) v‖ := by
  classical
  dsimp only
  have hsupport (v : ℕ) :
      O.filter (fun u =>
        u ∈ huaTypeIICommonOuterWindow P l D D' v w P' ∧
        u + ξ₁ ∈ huaTypeIICommonOuterWindow P l D D' v w P' ∧
        u + ξ₂ ∈ huaTypeIICommonOuterWindow P l D D' v w P' ∧
        u + ξ₂ + ξ₁ ∈ huaTypeIICommonOuterWindow P l D D' v w P' ∧
        u + ξ₃ ∈ huaTypeIICommonOuterWindow P l D D' v w P' ∧
        u + ξ₃ + ξ₁ ∈ huaTypeIICommonOuterWindow P l D D' v w P' ∧
        u + ξ₃ + ξ₂ ∈ huaTypeIICommonOuterWindow P l D D' v w P' ∧
        u + ξ₃ + ξ₂ + ξ₁ ∈ huaTypeIICommonOuterWindow P l D D' v w P') =
      O.filter (fun u => ∀ r ∈ ({u, u + ξ₃ + ξ₂ + ξ₁} : Finset ℕ),
        r ∈ huaTypeIICommonOuterWindow P l D D' v w P') := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      forall_eq_or_imp, forall_eq]
    have hcube := hua_typeII_commonWindow_eightShift_iff_endpoints
      P l D D' v w u ξ₁ ξ₂ ξ₃ P'
    dsimp only at hcube
    rw [hcube]
  simp_rw [hsupport, hua_typeII_thirdOuterPhase_eq_innerCubicPhase]
  exact norm_sum_huaTypeIIInnerWindowOnOuterVertices_le
    P l D D' w P₀ P' O (fun u => {u, u + ξ₃ + ξ₂ + ξ₁})
      (fun v _ => generalCubicPhase
        (6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * ξ₁ * ξ₂ * ξ₃) 0 0
        (-(6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * ξ₁ * ξ₂ * ξ₃) * (w : ℝ) ^ 3) v)

/-- The actual inner interval after three outer shifts obeys the two-inner-
shift Weyl envelope with Hua's exact natural five-shift frequency. Lower
coefficients have canceled by the outer differences, while the fixed paired
constant is retained through the interval theorem. -/
theorem hua_typeII_innerWindow_four_le_mixedFrequency_envelope
    (P l D D' w P₀ a q ξ₁ ξ₂ ξ₃ : ℕ) (P' : ℝ) (R : Finset ℕ) :
    let θ := 6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * ξ₁ * ξ₂ * ξ₃
    ‖∑ v ∈ huaTypeIIInnerWindowOnOuterVertices P l D D' w P₀ P' R,
      generalCubicPhase θ 0 0 (-θ * (w : ℝ) ^ 3) v‖ ^ 4 ≤
      6 * (P₀ : ℝ) ^ 3 + 16 * (P₀ : ℝ) *
        (∑ η₁ ∈ Finset.Icc 1 P₀, ∑ η₂ ∈ Finset.Icc 1 P₀,
          linearDistanceEnvelope (P₀ : ℝ)
            (((a : ℝ) / q) *
              (huaTypeIICubicShiftFrequency l (ξ₁, ξ₂, ξ₃, η₁, η₂) : ℝ))) := by
  dsimp only
  obtain ⟨lo, hi, hlo, hhi, hwindow⟩ :=
    exists_huaTypeIIInnerWindowOnOuterVertices_eq_Icc P l D D' w P₀ P' R
  rw [hwindow]
  have h := norm_generalCubicPhase_sum_Icc_four_le_innerWeyl_envelope
    (6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * ξ₁ * ξ₂ * ξ₃) 0 0
    (-(6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * ξ₁ * ξ₂ * ξ₃) * (w : ℝ) ^ 3)
    lo hi P₀ hlo hhi
  have hfreq (η₁ η₂ : ℕ) :
      6 * (6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * ξ₁ * ξ₂ * ξ₃) * (η₁ * η₂ : ℕ) =
        ((a : ℝ) / q) *
          (huaTypeIICubicShiftFrequency l (ξ₁, ξ₂, ξ₃, η₁, η₂) : ℝ) := by
    unfold huaTypeIICubicShiftFrequency
    push_cast
    ring
  simpa only [hfreq] using h

#print axioms hua_typeII_innerWindow_mem_of_between
#print axioms exists_huaTypeIIInnerWindowOnOuterVertices_eq_Icc
#print axioms sum_huaTypeIIInnerWindowOnOuterVertices_swap
#print axioms norm_sum_huaTypeIIInnerWindowOnOuterVertices_le
#print axioms mem_huaTypeIIInnerWindowOnOuterCube_iff
#print axioms hua_typeII_thirdOuterPhase_eq_innerCubicPhase
#print axioms hua_typeII_threeOuter_sum_norm_le_innerWindow_norm_sum
#print axioms hua_typeII_innerWindow_four_le_mixedFrequency_envelope

end SystolicGrowth.CookMagyarCircle
