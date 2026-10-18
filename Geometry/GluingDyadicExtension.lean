module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Topology.UnitInterval

@[expose] public section

/-!
# Extension of the actual dyadic interval maps

The dyadic points of the unit interval are dense by a floor approximation.
A map on this concrete domain with a proved scaled distance identity is
uniformly continuous, so the native dense extension into a complete metric
space preserves that identity on the whole interval. The scale may be zero.
This is the extension constituent for the actual midpoint grids; no native
geometric distance identity is taken as an unconstructed input here.
-/

open Set Filter Topology

namespace SystolicGrowth

/-- The actual dyadic points retained in the closed unit interval. -/
def gluingDyadicUnitSet : Set unitInterval :=
  {t | ∃ n k : ℕ, k ≤ 2 ^ n ∧ (t : ℝ) = (k : ℝ) / (2 : ℝ) ^ n}

/-- The concrete dense domain of the midpoint-grid map. -/
abbrev GluingDyadicUnitInterval := gluingDyadicUnitSet

/-- A bounded grid index gives an actual dyadic unit-interval point. -/
noncomputable def gluingDyadicUnitPoint (n k : ℕ) (hk : k ≤ 2 ^ n) :
    GluingDyadicUnitInterval :=
  ⟨⟨(k : ℝ) / (2 : ℝ) ^ n, by
    constructor
    · positivity
    · apply (div_le_one (by positivity : (0 : ℝ) < 2 ^ n)).2
      exact_mod_cast hk⟩, n, k, hk, rfl⟩

@[simp]
theorem gluingDyadicUnitPoint_val (n k : ℕ) (hk : k ≤ 2 ^ n) :
    ((gluingDyadicUnitPoint n k hk : unitInterval) : ℝ) = (k : ℝ) / (2 : ℝ) ^ n := rfl

/-- Floor approximations with increasingly fine powers of two prove actual density. -/
theorem gluingDyadicUnitSet_dense : Dense gluingDyadicUnitSet := by
  intro t
  apply Metric.mem_closure_iff.2
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  let k : ℕ := ⌊(t : ℝ) * (2 : ℝ) ^ n⌋₊
  have hk : k ≤ 2 ^ n := by
    apply Nat.floor_le_of_le
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    exact mul_le_of_le_one_left hp.le t.property.2
  have hfloor : (k : ℝ) ≤ (t : ℝ) * (2 : ℝ) ^ n :=
    Nat.floor_le (mul_nonneg t.property.1 hp.le)
  have hq : (k : ℝ) / (2 : ℝ) ^ n ≤ (t : ℝ) :=
    (div_le_iff₀ hp).2 hfloor
  have herror : (t : ℝ) - (k : ℝ) / (2 : ℝ) ^ n < 1 / (2 : ℝ) ^ n := by
    apply (lt_div_iff₀ hp).2
    rw [sub_mul, div_mul_cancel₀ _ hp.ne']
    have h := Nat.lt_floor_add_one ((t : ℝ) * (2 : ℝ) ^ n)
    change (t : ℝ) * (2 : ℝ) ^ n < (k : ℝ) + 1 at h
    linarith
  refine ⟨(gluingDyadicUnitPoint n k hk : unitInterval),
    (gluingDyadicUnitPoint n k hk).property, ?_⟩
  change dist (t : ℝ) ((k : ℝ) / (2 : ℝ) ^ n) < ε
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hq)]
  apply herror.trans
  simpa only [one_div_pow] using hn

/-- A proved dyadic scaled distance identity extends to the whole interval.
Completeness is the only target-space extension requirement; zero scale is included. -/
theorem exists_gluingDyadicUnitInterval_extension
    {M : Type*} [MetricSpace M] [CompleteSpace M]
    (d : ℝ) (hd : 0 ≤ d) (f : GluingDyadicUnitInterval → M)
    (h_dist : ∀ s t : GluingDyadicUnitInterval,
      dist (f s) (f t) = d * |((s : unitInterval) : ℝ) - ((t : unitInterval) : ℝ)|) :
    ∃ γ : unitInterval → M, Continuous γ ∧
      (∀ s : GluingDyadicUnitInterval, γ s = f s) ∧
      ∀ s t : unitInterval, dist (γ s) (γ t) = d * |(s : ℝ) - (t : ℝ)| := by
  have hLip : LipschitzWith ⟨d, hd⟩ f := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [h_dist]
    change d * |((s : unitInterval) : ℝ) - ((t : unitInterval) : ℝ)| ≤
      d * dist (((s : unitInterval) : ℝ)) (((t : unitInterval) : ℝ))
    rw [Real.dist_eq]
  have hu : UniformContinuous f := hLip.uniformContinuous
  let γ : unitInterval → M := gluingDyadicUnitSet_dense.extend f
  have hγ : Continuous γ := gluingDyadicUnitSet_dense.uniformContinuous_extend hu |>.continuous
  have hagree (s : GluingDyadicUnitInterval) : γ s = f s :=
    gluingDyadicUnitSet_dense.extend_of_ind hu s
  refine ⟨γ, hγ, hagree, ?_⟩
  refine isClosed_property2 (p := fun s t : unitInterval =>
    dist (γ s) (γ t) = d * |(s : ℝ) - (t : ℝ)|)
    gluingDyadicUnitSet_dense.denseRange_val ?_ ?_
  · exact isClosed_eq ((hγ.comp continuous_fst).dist (hγ.comp continuous_snd))
      (continuous_const.mul
        (((continuous_subtype_val.comp continuous_fst).sub
          (continuous_subtype_val.comp continuous_snd)).abs))
  · intro s t
    rw [hagree s, hagree t]
    exact h_dist s t

#print axioms gluingDyadicUnitSet_dense
#print axioms exists_gluingDyadicUnitInterval_extension

end SystolicGrowth
