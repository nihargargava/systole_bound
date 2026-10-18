module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Algebra.Order.Interval.Set.Monoid
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Exact variation of the complementary arc of a closed path

The complementary arc follows the final portion of the original path and
then its initial portion. Closedness identifies their common endpoint.
Monotone translations preserve variation on each leg, and interval
additivity gives the exact total, including zero legs and infinite variation.
-/

open Set

namespace SystolicGrowth

/-- An explicit complementary arc of a continuous closed path, parametrized
by the sum of the two original parameter lengths. Its variation is exactly
the sum of the variations of those two legs. -/
theorem exists_closed_path_complementary_arc
    {M : Type*} [PseudoEMetricSpace M] {A B u v : ℝ}
    (γ : ℝ → M) (hγ : ContinuousOn γ (Icc A B)) (hclose : γ A = γ B)
    (hAu : A ≤ u) (huv : u ≤ v) (hvB : v ≤ B) :
    ∃ κ : ℝ → M,
      ContinuousOn κ (Icc 0 ((B - v) + (u - A))) ∧
      κ 0 = γ v ∧ κ ((B - v) + (u - A)) = γ u ∧
      eVariationOn κ (Icc 0 ((B - v) + (u - A))) =
        eVariationOn γ (Icc v B) + eVariationOn γ (Icc A u) := by
  classical
  let c := B - v
  let d := (B - v) + (u - A)
  let κ : ℝ → M := fun t => if t ≤ c then γ (v + t) else γ ((A - c) + t)
  have hc : 0 ≤ c := sub_nonneg.mpr hvB
  have hcd : c ≤ d := by dsimp [c, d]; linarith
  have hvc : v + c = B := by dsimp [c]; ring
  have hAc : (A - c) + c = A := by ring
  have hAd : (A - c) + d = u := by dsimp [c, d]; ring
  have hleft : EqOn κ (fun t => γ (v + t)) (Icc 0 c) := by
    intro t ht
    exact if_pos ht.2
  have hright : EqOn κ (fun t => γ ((A - c) + t)) (Icc c d) := by
    intro t ht
    by_cases htc : t ≤ c
    · have ht' : t = c := htc.antisymm ht.1
      subst t
      dsimp only [κ]
      rw [if_pos le_rfl, hvc, hAc]
      exact hclose.symm
    · exact if_neg htc
  have hleftMap : MapsTo (fun t : ℝ => v + t) (Icc 0 c) (Icc A B) := by
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2, hvc]
  have hrightMap : MapsTo (fun t : ℝ => (A - c) + t) (Icc c d) (Icc A B) := by
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2, hAd]
  have hleftCont : ContinuousOn κ (Icc 0 c) :=
    (hγ.comp (continuous_const.add continuous_id).continuousOn hleftMap).congr hleft
  have hrightCont : ContinuousOn κ (Icc c d) :=
    (hγ.comp (continuous_const.add continuous_id).continuousOn hrightMap).congr hright
  have hcont : ContinuousOn κ (Icc 0 d) := by
    rw [← Icc_union_Icc_eq_Icc hc hcd]
    exact hleftCont.union_of_isClosed hrightCont isClosed_Icc isClosed_Icc
  have hstart : κ 0 = γ v := by
    rw [hleft ⟨le_rfl, hc⟩]
    simp
  have hfinish : κ d = γ u := by
    exact (hright ⟨hcd, le_rfl⟩).trans (congrArg γ hAd)
  have hleftVar : eVariationOn κ (Icc 0 c) = eVariationOn γ (Icc v B) := by
    calc
      _ = eVariationOn (fun t => γ (v + t)) (Icc 0 c) := eVariationOn.congr hleft
      _ = eVariationOn γ ((fun t : ℝ => v + t) '' Icc 0 c) :=
        eVariationOn.comp_eq_of_monotoneOn γ _ (fun _ _ _ _ h => add_le_add le_rfl h)
      _ = eVariationOn γ (Icc v B) := by
        rw [image_const_add_Icc, add_zero, hvc]
  have hrightVar : eVariationOn κ (Icc c d) = eVariationOn γ (Icc A u) := by
    calc
      _ = eVariationOn (fun t => γ ((A - c) + t)) (Icc c d) := eVariationOn.congr hright
      _ = eVariationOn γ ((fun t : ℝ => (A - c) + t) '' Icc c d) :=
        eVariationOn.comp_eq_of_monotoneOn γ _
          (fun _ _ _ _ h => add_le_add le_rfl h)
      _ = eVariationOn γ (Icc A u) := by
        rw [image_const_add_Icc, hAc, hAd]
  refine ⟨κ, hcont, hstart, hfinish, ?_⟩
  calc
    _ = eVariationOn κ (Icc 0 c) + eVariationOn κ (Icc c d) := by
      simpa only [univ_inter] using
        (eVariationOn.Icc_add_Icc κ (s := univ) hc hcd (mem_univ c)).symm
    _ = eVariationOn γ (Icc v B) + eVariationOn γ (Icc A u) := by
      rw [hleftVar, hrightVar]

#print axioms exists_closed_path_complementary_arc

end SystolicGrowth
