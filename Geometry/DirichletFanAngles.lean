module

/-
Copyright (c) 2026 Will (Ziang) Li.
Released under Apache 2.0 license.

The two-halfspace angle-splitting argument is adapted from
RiemannDynamics/Teichmuller/FuchsianGeometry/Polygon/Fan.lean,
`sectorAngle_eq_add_basepoint`, at commit
b3fa37cc0f18a23ea66b654ea3f73eb472129010. The split point is generalized
from the Dirichlet basepoint to any point strictly inside both supporting
halfspaces. Native fan specializations below retain the boundary apex.
-/
public import Geometry.DirichletVertexFan
public import Geometry.DirichletPolygonBridge
public import Geometry.QuotientAreaMeasure
public import Vendored.RiemannDynamics.Teichmuller.PolygonGeometry

@[expose] public section

/-!
# Corner-angle regrouping for the original boundary-apex fan

At an internal boundary vertex, the actual two incident distance halfspaces
place the original apex strictly inside its angle. Thus the two incident
fan-triangle angles sum to the original polygon interior angle. This uses
actual supporting inequalities, not an assumed angle identity.
-/

open Set UpperHalfPlane MeasureTheory
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth

open Vendored.RiemannDynamics

set_option maxHeartbeats 400000 in
/-- A point strictly inside both incident distance halfspaces splits their
sector angle. The boundary directions are strictly inside the opposite
halfspace, so no assumed angle ordering is needed. -/
theorem sectorAngle_eq_add_of_strict_support
    {o p q v w₁ w₂ a : ℍ}
    (hop : o ≠ p) (hoq : o ≠ q)
    (hvp : dist v o = dist v p) (hvq : dist v o = dist v q)
    (hw₁p : dist w₁ o = dist w₁ p) (hw₂q : dist w₂ o = dist w₂ q)
    (hw₁q : dist w₁ o < dist w₁ q) (hw₂p : dist w₂ o < dist w₂ p)
    (hap : dist a o < dist a p) (haq : dist a o < dist a q)
    (hw₁v : w₁ ≠ v) (hw₂v : w₂ ≠ v) :
    sectorAngle v w₁ w₂ = sectorAngle v w₁ a + sectorAngle v a w₂ := by
  obtain ⟨g₁, ε₁, hε₁, hle₁, hge₁⟩ := bisector_normalizer hop
  obtain ⟨g₂, ε₂, hε₂, hle₂, hge₂⟩ := bisector_normalizer hoq
  obtain ⟨m₁, _, hf₁eq, hf₁lt⟩ := functional_sign hε₁ hle₁ hge₁ hvp
  obtain ⟨m₂, _, hf₂eq, hf₂lt⟩ := functional_sign hε₂ hle₂ hge₂ hvq
  have hu₁ : discChart v w₁ ≠ 0 := discChart_ne_zero hw₁v
  have hu₂ : discChart v w₂ ≠ 0 := discChart_ne_zero hw₂v
  have E₁ : ε₁ * (m₁ * discChart v w₁).im = 0 := hf₁eq w₁ hw₁p
  have E₂ : ε₂ * (m₂ * discChart v w₂).im = 0 := hf₂eq w₂ hw₂q
  have P12 : 0 < ε₁ * (m₁ * discChart v w₂).im := hf₁lt w₂ hw₂p
  have P1a : 0 < ε₁ * (m₁ * discChart v a).im := hf₁lt a hap
  have P21 : 0 < ε₂ * (m₂ * discChart v w₁).im := hf₂lt w₁ hw₁q
  have P2a : 0 < ε₂ * (m₂ * discChart v a).im := hf₂lt a haq
  have hac : discChart v a ≠ 0 := by
    intro h
    rw [h, mul_zero] at P1a
    simp at P1a
  rw [functional_ratio hε₁ hu₁ E₁ (discChart v w₂)] at P12
  rw [functional_ratio hε₁ hu₁ E₁ (discChart v a)] at P1a
  rw [functional_ratio hε₂ hu₂ E₂ (discChart v w₁)] at P21
  rw [functional_ratio hε₂ hu₂ E₂ (discChart v a)] at P2a
  have hsgn_pp : ∀ b c : ℝ, 0 < b * c → 0 < b → 0 < c := by
    intro b c hbc hb
    nlinarith
  have hsgn_nn : ∀ b c : ℝ, 0 < b * c → b < 0 → c < 0 := by
    intro b c hbc hb
    nlinarith
  have hsgn_bp : ∀ b c : ℝ, 0 < b * c → 0 < c → 0 < b := by
    intro b c hbc hc
    nlinarith
  have hsgn_bn : ∀ b c : ℝ, 0 < b * c → c < 0 → b < 0 := by
    intro b c hbc hc
    nlinarith
  have hABeq : discChart v a / discChart v w₁ * (discChart v w₂ / discChart v a)
      = discChart v w₂ / discChart v w₁ := by
    field_simp
  have hNC : 0 < Complex.normSq (discChart v w₂ / discChart v w₁) :=
    Complex.normSq_pos.mpr (div_ne_zero hu₂ hu₁)
  have hNa : 0 < Complex.normSq (discChart v a / discChart v w₂) :=
    Complex.normSq_pos.mpr (div_ne_zero hac hu₂)
  have hCinv : (discChart v w₁ / discChart v w₂).im
      = -(discChart v w₂ / discChart v w₁).im
        / Complex.normSq (discChart v w₂ / discChart v w₁) := by
    rw [← inv_div (discChart v w₂) (discChart v w₁), Complex.inv_im]
  have hBinv : (discChart v w₂ / discChart v a).im
      = -(discChart v a / discChart v w₂).im
        / Complex.normSq (discChart v a / discChart v w₂) := by
    rw [← inv_div (discChart v a) (discChart v w₂), Complex.inv_im]
  have hCne0 : (discChart v w₂ / discChart v w₁).im ≠ 0 := by
    intro h
    rw [h, mul_zero] at P12
    exact lt_irrefl 0 P12
  have key : 0 < (discChart v a / discChart v w₁).im
        ∧ 0 < (discChart v w₂ / discChart v a).im
        ∧ 0 < (discChart v w₂ / discChart v w₁).im
      ∨ (discChart v a / discChart v w₁).im < 0
        ∧ (discChart v w₂ / discChart v a).im < 0
        ∧ (discChart v w₂ / discChart v w₁).im < 0 := by
    rcases lt_or_gt_of_ne hCne0 with hC | hC
    · right
      have hq₁ : ε₁ * (m₁ * discChart v w₁).re < 0 := hsgn_bn _ _ P12 hC
      have hA : (discChart v a / discChart v w₁).im < 0 := hsgn_nn _ _ P1a hq₁
      have hu₁₂ : 0 < (discChart v w₁ / discChart v w₂).im := by
        rw [hCinv]
        exact div_pos (by linarith) hNC
      have hq₂ : 0 < ε₂ * (m₂ * discChart v w₂).re := hsgn_bp _ _ P21 hu₁₂
      have ha₂ : 0 < (discChart v a / discChart v w₂).im := hsgn_pp _ _ P2a hq₂
      have hB : (discChart v w₂ / discChart v a).im < 0 := by
        rw [hBinv]
        exact div_neg_of_neg_of_pos (by linarith) hNa
      exact ⟨hA, hB, hC⟩
    · left
      have hq₁ : 0 < ε₁ * (m₁ * discChart v w₁).re := hsgn_bp _ _ P12 hC
      have hA : 0 < (discChart v a / discChart v w₁).im := hsgn_pp _ _ P1a hq₁
      have hu₁₂ : (discChart v w₁ / discChart v w₂).im < 0 := by
        rw [hCinv]
        exact div_neg_of_neg_of_pos (by linarith) hNC
      have hq₂ : ε₂ * (m₂ * discChart v w₂).re < 0 := hsgn_bn _ _ P21 hu₁₂
      have ha₂ : (discChart v a / discChart v w₂).im < 0 := hsgn_nn _ _ P2a hq₂
      have hB : 0 < (discChart v w₂ / discChart v a).im := by
        rw [hBinv]
        exact div_pos (by linarith) hNa
      exact ⟨hA, hB, hC⟩
  rw [← hABeq] at key
  have hfinal := abs_arg_mul_of_same_side key
  rw [hABeq] at hfinal
  simp only [sectorAngle]
  exact hfinal

namespace DirichletBoundarySegments

/-- The original cyclic vertex at a corner of the fixed boundary-apex fan. -/
noncomputable def intrinsicVertexFanCornerVertexIndex
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3) :
    Fin B.intrinsicBoundaryRadialCuts.card :=
  if c.2 = 0 then ⟨0, by have := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩
  else if c.2 = 1 then B.intrinsicVertexFanSideIndex c.1
  else finRotate B.intrinsicBoundaryRadialCuts.card (B.intrinsicVertexFanSideIndex c.1)

/-- The three corner angles in precisely the native triangle-deficit order. -/
noncomputable def intrinsicVertexFanCornerAngle
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3) : ℝ :=
  let t := B.intrinsicVertexFanVertices c.1
  if c.2 = 0 then sectorAngle t.1 t.2.1 t.2.2
  else if c.2 = 1 then sectorAngle t.2.1 t.1 t.2.2
  else sectorAngle t.2.2 t.1 t.2.1

/-- Corner index zero contributes to cyclic vertex zero; the other corner
indices have the ordinary non-wrapping vertex numbers `k + 1`, `k + 2`. -/
theorem intrinsicVertexFanCornerVertexIndex_val
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3) :
    (B.intrinsicVertexFanCornerVertexIndex c).1 =
      if c.2 = 0 then 0 else if c.2 = 1 then c.1.1 + 1 else c.1.1 + 2 := by
  unfold intrinsicVertexFanCornerVertexIndex
  split_ifs
  · rfl
  · rfl
  · rw [B.intrinsicVertexFanSideIndex_next]

/-- The apex corner fiber consists of the apex angle in every fan triangle. -/
theorem sum_intrinsicVertexFanCornerAngle_apex
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    (∑ c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3
      with (B.intrinsicVertexFanCornerVertexIndex c).1 = 0,
        B.intrinsicVertexFanCornerAngle c) =
      ∑ k : Fin (B.intrinsicBoundaryRadialCuts.card - 2),
        B.intrinsicVertexFanCornerAngle (k, 0) := by
  classical
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  simp [intrinsicVertexFanCornerVertexIndex_val, Fin.sum_univ_succ]

/-- Every nonapex corner fiber is precisely the two possible base corners:
the initial base corner at index `i - 1`, and the terminal one at `i - 2`.
The formula naturally omits an index when the vertex is an endpoint. -/
theorem sum_intrinsicVertexFanCornerAngle_nonapex
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (hi : i.1 ≠ 0) :
    (∑ c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3
      with (B.intrinsicVertexFanCornerVertexIndex c).1 = i.1,
        B.intrinsicVertexFanCornerAngle c) =
      (∑ k : Fin (B.intrinsicBoundaryRadialCuts.card - 2),
        if k.1 + 1 = i.1 then B.intrinsicVertexFanCornerAngle (k, 1) else 0) +
      ∑ k : Fin (B.intrinsicBoundaryRadialCuts.card - 2),
        if k.1 + 2 = i.1 then B.intrinsicVertexFanCornerAngle (k, 2) else 0 := by
  classical
  rw [Finset.sum_filter, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp [intrinsicVertexFanCornerVertexIndex_val, Fin.sum_univ_succ, Ne.symm hi]

private theorem sum_ite_val_add {n : ℕ} (f : Fin n → ℝ) (k : Fin n) (a : ℕ) :
    (∑ j : Fin n, if j.1 + a = k.1 + a then f j else 0) = f k := by
  classical
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    have hne : j.1 + a ≠ k.1 + a := by
      intro h
      exact hj (Fin.ext (Nat.add_right_cancel h))
    exact if_neg hne
  · simp

/-- At an internal polygon vertex, exactly the terminal corner of one
triangle and initial base corner of the next triangle occur in its fiber. -/
theorem sum_intrinsicVertexFanCornerAngle_internal
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (k : Fin (B.intrinsicBoundaryRadialCuts.card - 3)) :
    (∑ c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3
      with (B.intrinsicVertexFanCornerVertexIndex c).1 = k.1 + 2,
        B.intrinsicVertexFanCornerAngle c) =
      B.intrinsicVertexFanCornerAngle (⟨k.1, by have := k.2; omega⟩, 2) +
      B.intrinsicVertexFanCornerAngle (⟨k.1 + 1, by have := k.2; omega⟩, 1) := by
  let i : Fin B.intrinsicBoundaryRadialCuts.card := ⟨k.1 + 2, by have := k.2; omega⟩
  rw [B.sum_intrinsicVertexFanCornerAngle_nonapex i (by dsimp [i]; omega)]
  have h₁ := sum_ite_val_add
    (fun j => B.intrinsicVertexFanCornerAngle (j, 1))
    (⟨k.1 + 1, by have := k.2; omega⟩ : Fin (B.intrinsicBoundaryRadialCuts.card - 2)) 1
  have h₂ := sum_ite_val_add
    (fun j => B.intrinsicVertexFanCornerAngle (j, 2))
    (⟨k.1, by have := k.2; omega⟩ : Fin (B.intrinsicBoundaryRadialCuts.card - 2)) 2
  dsimp only [i]
  have h₁' : (∑ j : Fin (B.intrinsicBoundaryRadialCuts.card - 2),
      if j.1 + 1 = k.1 + 2 then B.intrinsicVertexFanCornerAngle (j, 1) else 0) =
      B.intrinsicVertexFanCornerAngle (⟨k.1 + 1, by have := k.2; omega⟩, 1) := by
    simpa only [Fin.val_mk, Nat.add_assoc] using h₁
  rw [h₁', h₂, add_comm]

/-- The first boundary vertex after the apex has only the first triangle's
initial base corner, not an extra degenerate triangle. -/
theorem sum_intrinsicVertexFanCornerAngle_first
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    (∑ c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3
      with (B.intrinsicVertexFanCornerVertexIndex c).1 = 1,
        B.intrinsicVertexFanCornerAngle c) =
      B.intrinsicVertexFanCornerAngle
        (⟨0, by have := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩, 1) := by
  let i : Fin B.intrinsicBoundaryRadialCuts.card :=
    ⟨1, by have := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩
  rw [B.sum_intrinsicVertexFanCornerAngle_nonapex i (by dsimp [i]; omega)]
  dsimp only [i]
  have h₁ := sum_ite_val_add
    (fun j => B.intrinsicVertexFanCornerAngle (j, 1))
    (⟨0, by have := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩ :
      Fin (B.intrinsicBoundaryRadialCuts.card - 2)) 1
  rw [h₁]
  have h₂ : (∑ j : Fin (B.intrinsicBoundaryRadialCuts.card - 2),
      if j.1 + 2 = 1 then B.intrinsicVertexFanCornerAngle (j, 2) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (by omega)]
  rw [h₂, add_zero]

/-- The final boundary vertex before the apex has only the final triangle's
terminal base corner. -/
theorem sum_intrinsicVertexFanCornerAngle_last
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    (∑ c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3
      with (B.intrinsicVertexFanCornerVertexIndex c).1 = B.intrinsicBoundaryRadialCuts.card - 1,
        B.intrinsicVertexFanCornerAngle c) =
      B.intrinsicVertexFanCornerAngle
        (⟨B.intrinsicBoundaryRadialCuts.card - 3,
          by have := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩, 2) := by
  have hn := B.three_le_intrinsicBoundaryRadialCuts_card
  let i : Fin B.intrinsicBoundaryRadialCuts.card :=
    ⟨B.intrinsicBoundaryRadialCuts.card - 1, by omega⟩
  rw [B.sum_intrinsicVertexFanCornerAngle_nonapex i (by dsimp [i]; omega)]
  dsimp only [i]
  have h₁ : (∑ j : Fin (B.intrinsicBoundaryRadialCuts.card - 2),
      if j.1 + 1 = B.intrinsicBoundaryRadialCuts.card - 1
        then B.intrinsicVertexFanCornerAngle (j, 1) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (by have := j.2; omega)]
  have h₂ := sum_ite_val_add
    (fun j => B.intrinsicVertexFanCornerAngle (j, 2))
    (⟨B.intrinsicBoundaryRadialCuts.card - 3, by omega⟩ :
      Fin (B.intrinsicBoundaryRadialCuts.card - 2)) 2
  rw [h₁, zero_add]
  simpa only [Fin.val_mk, show B.intrinsicBoundaryRadialCuts.card - 3 + 2 =
    B.intrinsicBoundaryRadialCuts.card - 1 by omega] using h₂

/-- Rotation at a nonterminal cyclic index is its ordinary successor. -/
theorem intrinsicCyclicIndex_next_of_lt
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (hi : i.1 + 1 < B.intrinsicBoundaryRadialCuts.card) :
    finRotate B.intrinsicBoundaryRadialCuts.card i = ⟨i.1 + 1, hi⟩ := by
  have hn := B.three_le_intrinsicBoundaryRadialCuts_card
  haveI : NeZero B.intrinsicBoundaryRadialCuts.card := ⟨by omega⟩
  apply Fin.ext
  rw [finRotate_apply, Fin.val_add, Fin.val_one']
  rw [Nat.mod_eq_of_lt (by omega : 1 < B.intrinsicBoundaryRadialCuts.card)]
  exact Nat.mod_eq_of_lt hi

/-- The two fan-triangle corners meeting at an internal boundary vertex
regroup to its actual angle between the two incident full polygon sides. -/
theorem intrinsicVertexFan_internal_angle
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (k : Fin (B.intrinsicBoundaryRadialCuts.card - 3)) :
    let a := B.intrinsicCyclicVertex
      ⟨0, by have := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩
    let w₁ := B.intrinsicCyclicVertex ⟨k.1 + 1, by have := k.2; omega⟩
    let v := B.intrinsicCyclicVertex ⟨k.1 + 2, by have := k.2; omega⟩
    let w₂ := B.intrinsicCyclicVertex ⟨k.1 + 3, by have := k.2; omega⟩
    sectorAngle v w₁ w₂ = sectorAngle v a w₁ + sectorAngle v a w₂ := by
  dsimp only
  let ip : Fin B.intrinsicBoundaryRadialCuts.card := ⟨k.1 + 1, by have := k.2; omega⟩
  let iv : Fin B.intrinsicBoundaryRadialCuts.card := ⟨k.1 + 2, by have := k.2; omega⟩
  let iq : Fin B.intrinsicBoundaryRadialCuts.card := ⟨k.1 + 3, by have := k.2; omega⟩
  let ia : Fin B.intrinsicBoundaryRadialCuts.card :=
    ⟨0, by have := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩
  have hpnext : finRotate B.intrinsicBoundaryRadialCuts.card ip = iv := by
    exact B.intrinsicCyclicIndex_next_of_lt ip (by have := k.2; dsimp [ip]; omega)
  have hvnext : finRotate B.intrinsicBoundaryRadialCuts.card iv = iq := by
    exact B.intrinsicCyclicIndex_next_of_lt iv (by have := k.2; dsimp [iv]; omega)
  have hmemleft (i : Fin B.intrinsicBoundaryRadialCuts.card) :
      B.intrinsicCyclicVertex i ∈
        B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) := by
    rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
    exact left_mem_geodSeg _ _
  have hvleft : B.intrinsicCyclicVertex iv ∈
      B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge ip) := by
    rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg, hpnext]
    exact right_mem_geodSeg _ _
  have hqright : B.intrinsicCyclicVertex iq ∈
      B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge iv) := by
    rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg, hvnext]
    exact right_mem_geodSeg _ _
  have hp0 : o ≠ (B.intrinsicCyclicEdge ip).1.1.1 • o := by
    intro h
    exact (Finset.ne_of_mem_erase (B.intrinsicCyclicEdge ip).1.1.2.1)
      (X.free _ o h.symm)
  have hq0 : o ≠ (B.intrinsicCyclicEdge iv).1.1.1 • o := by
    intro h
    exact (Finset.ne_of_mem_erase (B.intrinsicCyclicEdge iv).1.1.2.1)
      (X.free _ o h.symm)
  have hne (i j : Fin B.intrinsicBoundaryRadialCuts.card) (hij : i.1 ≠ j.1) :
      B.intrinsicCyclicVertex i ≠ B.intrinsicCyclicVertex j := by
    intro h
    exact hij (congrArg Fin.val (B.intrinsicCyclicVertex_injective h))
  have hangle := sectorAngle_eq_add_of_strict_support hp0 hq0
    (B.intrinsicCyclicClosedEdge_mem_bisector ip hvleft)
    (B.intrinsicCyclicClosedEdge_mem_bisector iv (hmemleft iv))
    (B.intrinsicCyclicClosedEdge_mem_bisector ip (hmemleft ip))
    (B.intrinsicCyclicClosedEdge_mem_bisector iv hqright)
    (B.intrinsicCyclicVertex_dist_lt_of_not_incident iv ip
      (by intro h; have := congrArg Fin.val h; dsimp [ip, iv] at this; omega)
      (by rw [hvnext]; intro h; have := congrArg Fin.val h; dsimp [ip, iq] at this; omega))
    (B.intrinsicCyclicVertex_dist_lt_of_not_incident ip iq
      (by intro h; have := congrArg Fin.val h; dsimp [ip, iq] at this; omega)
      (by rw [hpnext]; intro h; have := congrArg Fin.val h; dsimp [iv, iq] at this; omega))
    (B.intrinsicCyclicVertex_dist_lt_of_not_incident ip ia
      (by intro h; have := congrArg Fin.val h; dsimp [ip, ia] at this; omega)
      (by rw [hpnext]; intro h; have := congrArg Fin.val h; dsimp [iv, ia] at this; omega))
    (B.intrinsicCyclicVertex_dist_lt_of_not_incident iv ia
      (by intro h; have := congrArg Fin.val h; dsimp [iv, ia] at this; omega)
      (by rw [hvnext]; intro h; have := congrArg Fin.val h; dsimp [iq, ia] at this; omega))
    (hne ip iv (by dsimp [ip, iv]; omega))
    (hne iq iv (by dsimp [iq, iv]; omega))
  rw [sectorAngle_comm (B.intrinsicCyclicVertex iv) (B.intrinsicCyclicVertex ip)
    (B.intrinsicCyclicVertex ia)] at hangle
  exact hangle

/-- The complete native corner fiber at any internal boundary vertex sums
to its geometric sector between the actual previous and next vertices. -/
theorem sum_intrinsicVertexFanCornerAngle_internal_eq_sector
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (k : Fin (B.intrinsicBoundaryRadialCuts.card - 3)) :
    (∑ c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3
      with (B.intrinsicVertexFanCornerVertexIndex c).1 = k.1 + 2,
        B.intrinsicVertexFanCornerAngle c) =
      sectorAngle
        (B.intrinsicCyclicVertex ⟨k.1 + 2, by have := k.2; omega⟩)
        (B.intrinsicCyclicVertex ⟨k.1 + 1, by have := k.2; omega⟩)
        (B.intrinsicCyclicVertex ⟨k.1 + 3, by have := k.2; omega⟩) := by
  rw [B.sum_intrinsicVertexFanCornerAngle_internal]
  simp only [intrinsicVertexFanCornerAngle, Fin.reduceEq, if_false, if_true]
  simp only [intrinsicVertexFanVertices, B.intrinsicVertexFanSideIndex_next]
  simp only [intrinsicVertexFanSideIndex]
  exact (B.intrinsicVertexFan_internal_angle k).symm

/-- The first nonapex vertex's complete corner fiber is its actual angle in
the first native triangle. -/
theorem sum_intrinsicVertexFanCornerAngle_first_eq_sector
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    let k : Fin (B.intrinsicBoundaryRadialCuts.card - 2) :=
      ⟨0, by have := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩
    let t := B.intrinsicVertexFanVertices k
    (∑ c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3
      with (B.intrinsicVertexFanCornerVertexIndex c).1 = 1,
        B.intrinsicVertexFanCornerAngle c) = sectorAngle t.2.1 t.1 t.2.2 := by
  dsimp only
  rw [B.sum_intrinsicVertexFanCornerAngle_first]
  rfl

/-- The final nonapex vertex's complete corner fiber is its actual angle in
the final native triangle. -/
theorem sum_intrinsicVertexFanCornerAngle_last_eq_sector
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    let k : Fin (B.intrinsicBoundaryRadialCuts.card - 2) :=
      ⟨B.intrinsicBoundaryRadialCuts.card - 3,
        by have := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩
    let t := B.intrinsicVertexFanVertices k
    (∑ c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3
      with (B.intrinsicVertexFanCornerVertexIndex c).1 = B.intrinsicBoundaryRadialCuts.card - 1,
        B.intrinsicVertexFanCornerAngle c) = sectorAngle t.2.2 t.1 t.2.1 := by
  dsimp only
  rw [B.sum_intrinsicVertexFanCornerAngle_last]
  rfl

/-- Every corner fiber except the boundary apex regroups to the angle of
its two actual incident polygon sides, including the two end vertices. -/
theorem sum_intrinsicVertexFanCornerAngle_of_ne_apex_eq_sector
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (hi : i.1 ≠ 0) :
    (∑ c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3
      with (B.intrinsicVertexFanCornerVertexIndex c).1 = i.1,
        B.intrinsicVertexFanCornerAngle c) =
      sectorAngle (B.intrinsicCyclicVertex i)
        (B.intrinsicCyclicVertex ((finRotate B.intrinsicBoundaryRadialCuts.card).symm i))
        (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i)) := by
  have hn := B.three_le_intrinsicBoundaryRadialCuts_card
  let ip : Fin B.intrinsicBoundaryRadialCuts.card := ⟨i.1 - 1, by have := i.2; omega⟩
  have hprev : (finRotate B.intrinsicBoundaryRadialCuts.card).symm i = ip := by
    apply (finRotate B.intrinsicBoundaryRadialCuts.card).injective
    rw [Equiv.apply_symm_apply]
    have hnext := B.intrinsicCyclicIndex_next_of_lt ip (by
      dsimp [ip]
      have := i.2
      omega)
    rw [hnext]
    apply Fin.ext
    dsimp [ip]
    omega
  rw [hprev]
  by_cases hi1 : i.1 = 1
  · have hnext := B.intrinsicCyclicIndex_next_of_lt i (by omega)
    rw [hnext]
    have hfirst := B.sum_intrinsicVertexFanCornerAngle_first_eq_sector
    dsimp only at hfirst
    simp only [intrinsicVertexFanVertices, B.intrinsicVertexFanSideIndex_next] at hfirst
    simp only [intrinsicVertexFanSideIndex] at hfirst
    have hvi : i = ⟨1, by omega⟩ := Fin.ext hi1
    have hvp : ip = ⟨0, by omega⟩ := by apply Fin.ext; dsimp [ip]; omega
    have hvn : (⟨i.1 + 1, by omega⟩ : Fin B.intrinsicBoundaryRadialCuts.card) =
        ⟨2, by omega⟩ := by apply Fin.ext; change i.1 + 1 = 2; omega
    simpa only [hi1, hvi, hvp, hvn] using hfirst
  by_cases hilast : i.1 + 1 = B.intrinsicBoundaryRadialCuts.card
  · haveI : NeZero B.intrinsicBoundaryRadialCuts.card := ⟨by omega⟩
    have hnext : finRotate B.intrinsicBoundaryRadialCuts.card i = ⟨0, by omega⟩ := by
      apply Fin.ext
      rw [finRotate_apply, Fin.val_add, Fin.val_one']
      change (i.1 + 1 % B.intrinsicBoundaryRadialCuts.card) %
        B.intrinsicBoundaryRadialCuts.card = 0
      rw [Nat.mod_eq_of_lt (by omega : 1 < B.intrinsicBoundaryRadialCuts.card),
        hilast, Nat.mod_self]
    rw [hnext, sectorAngle_comm]
    have hlast := B.sum_intrinsicVertexFanCornerAngle_last_eq_sector
    dsimp only at hlast
    simp only [intrinsicVertexFanVertices, B.intrinsicVertexFanSideIndex_next] at hlast
    simp only [intrinsicVertexFanSideIndex] at hlast
    have hiv : i.1 = B.intrinsicBoundaryRadialCuts.card - 1 := by omega
    have hvi : i = ⟨B.intrinsicBoundaryRadialCuts.card - 3 + 2, by omega⟩ := by
      apply Fin.ext
      change i.1 = B.intrinsicBoundaryRadialCuts.card - 3 + 2
      omega
    have hvp : ip = ⟨B.intrinsicBoundaryRadialCuts.card - 3 + 1, by omega⟩ := by
      apply Fin.ext
      dsimp [ip]
      omega
    simpa only [hvi, hvp, Fin.val_mk,
      show B.intrinsicBoundaryRadialCuts.card - 3 + 2 =
        B.intrinsicBoundaryRadialCuts.card - 1 by omega] using hlast
  · let k : Fin (B.intrinsicBoundaryRadialCuts.card - 3) := ⟨i.1 - 2, by have := i.2; omega⟩
    have hnext := B.intrinsicCyclicIndex_next_of_lt i (by have := i.2; omega)
    rw [hnext]
    have hval : k.1 + 2 = i.1 := by dsimp [k]; omega
    have hvi : (⟨k.1 + 2, by have := k.2; omega⟩ : Fin B.intrinsicBoundaryRadialCuts.card) =
        i := Fin.ext hval
    have hvp : (⟨k.1 + 1, by have := k.2; omega⟩ : Fin B.intrinsicBoundaryRadialCuts.card) =
        ip := by apply Fin.ext; dsimp [k, ip]; omega
    have hvn : (⟨k.1 + 3, by have := k.2; omega⟩ : Fin B.intrinsicBoundaryRadialCuts.card) =
        ⟨i.1 + 1, by have := i.2; omega⟩ := by apply Fin.ext; dsimp [k]; omega
    simpa only [hval, hvi, hvp, hvn] using
      B.sum_intrinsicVertexFanCornerAngle_internal_eq_sector k

/-- Exact area additivity for the original `n - 2` fan, using its proved
coverage and almost-everywhere disjointness; no polygon-angle field is used. -/
theorem volume_dirichletDomain_eq_ofReal_sum_intrinsicVertexFanDeficit
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    volume (dirichletDomain X.deckGroup o) =
      ENNReal.ofReal (∑ k : Fin (B.intrinsicBoundaryRadialCuts.card - 2),
        B.intrinsicVertexFanTriangleFundamentalDomain.angleDeficit k) := by
  rw [← B.iUnion_intrinsicVertexFan_triangle_eq_dirichletDomain,
    measure_iUnion₀ B.intrinsicVertexFan_triangle_ae_disjoint
      (fun k => (B.intrinsicVertexFan_triangle_measurable k).nullMeasurableSet),
    tsum_fintype]
  have htri (k : Fin (B.intrinsicBoundaryRadialCuts.card - 2)) :
      volume (hyperbolicTriangle (B.intrinsicVertexFanVertices k).1
        (B.intrinsicVertexFanVertices k).2.1 (B.intrinsicVertexFanVertices k).2.2) =
        ENNReal.ofReal (B.intrinsicVertexFanTriangleFundamentalDomain.angleDeficit k) := by
    exact volume_geodesicTriangle_eq_angleDeficit _ _ _
      (B.intrinsicVertexFanVertices_pairwise_ne k).1
      (B.intrinsicVertexFanVertices_pairwise_ne k).2.1
      (B.intrinsicVertexFanVertices_pairwise_ne k).2.2
  simp_rw [htri]
  exact (ENNReal.ofReal_sum_of_nonneg (fun k _ =>
    B.intrinsicVertexFanTriangleFundamentalDomain.angleDeficit_nonneg k)).symm

/-- The native corner-angle sum and angular-defect sum partition precisely
the `n - 2` copies of π. -/
theorem sum_intrinsicVertexFanCornerAngle_eq_pi_mul_sub_deficit
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    (∑ c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3,
      B.intrinsicVertexFanCornerAngle c) =
      Real.pi * (B.intrinsicBoundaryRadialCuts.card - 2 : ℕ) -
        ∑ k : Fin (B.intrinsicBoundaryRadialCuts.card - 2),
          B.intrinsicVertexFanTriangleFundamentalDomain.angleDeficit k := by
  let d : Fin (B.intrinsicBoundaryRadialCuts.card - 2) → ℝ :=
    fun k => B.intrinsicVertexFanTriangleFundamentalDomain.angleDeficit k
  change (∑ c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3,
    B.intrinsicVertexFanCornerAngle c) =
      Real.pi * (B.intrinsicBoundaryRadialCuts.card - 2 : ℕ) - ∑ k, d k
  have hcorner (k : Fin (B.intrinsicBoundaryRadialCuts.card - 2)) :
      (∑ j : Fin 3, B.intrinsicVertexFanCornerAngle (k, j)) =
        Real.pi - d k := by
    simp [d, Fin.sum_univ_succ, intrinsicVertexFanCornerAngle,
      FiniteTriangleFundamentalDomain.angleDeficit,
      intrinsicVertexFanTriangleFundamentalDomain]
    ring
  rw [Fintype.sum_prod_type]
  simp_rw [hcorner]
  simp [Finset.sum_sub_distrib, mul_comm]

/-- The angle of the two original full sides meeting at a native vertex. -/
noncomputable def intrinsicCyclicInteriorAngle
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) : ℝ :=
  sectorAngle (B.intrinsicCyclicVertex i)
    (B.intrinsicCyclicVertex ((finRotate B.intrinsicBoundaryRadialCuts.card).symm i))
    (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i))

/-- The native cyclic angles satisfy the imported polygon angle contract. -/
theorem intrinsicCyclicInteriorAngle_isInteriorAngleAt
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    IsInteriorAngleAt X.deckGroup o (B.intrinsicCyclicVertex i)
      (B.intrinsicCyclicInteriorAngle i) :=
  B.intrinsicCyclicVertex_prev_next_isInteriorAngleAt i

/-- Reindex the imported total interior-angle identity by the actual native
cyclic vertices, without identifying or changing the polygon. -/
theorem sum_intrinsicCyclicInteriorAngle
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    (∑ i : Fin B.intrinsicBoundaryRadialCuts.card, B.intrinsicCyclicInteriorAngle i) =
      2 * Real.pi * (polygonVertexClassCount X.deckGroup o : ℝ) := by
  classical
  let α : ℍ → ℝ := Function.extend B.intrinsicCyclicVertex
    B.intrinsicCyclicInteriorAngle (fun _ => 0)
  have hα : ∀ v ∈ polygonVertices X.deckGroup o,
      IsInteriorAngleAt X.deckGroup o v (α v) := by
    rw [← B.range_intrinsicCyclicVertex_eq_polygonVertices]
    rintro _ ⟨i, rfl⟩
    dsimp only [α]
    rw [B.intrinsicCyclicVertex_injective.extend_apply]
    exact B.intrinsicCyclicInteriorAngle_isInteriorAngleAt i
  obtain ⟨R, hdense⟩ := X.exists_dirichlet_orbit_density_bound o
  have hsum := sum_interiorAngle_total
    (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
    X.deck_fixing_point_acts_trivially (X.basepoint_mem_interior_dirichletDomain o) hdense hα
  rw [← B.range_intrinsicCyclicVertex_eq_polygonVertices,
    finsum_mem_range B.intrinsicCyclicVertex_injective, finsum_eq_sum_of_fintype] at hsum
  simpa only [α, B.intrinsicCyclicVertex_injective.extend_apply] using hsum

/-- The original fan's complete corner-angle total is computed from its
independent exact area identity and the imported Gauss--Bonnet theorem. This
does not use the unfinished native polygon certificate. -/
theorem sum_intrinsicVertexFanCornerAngle
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    (∑ c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3,
      B.intrinsicVertexFanCornerAngle c) =
      2 * Real.pi * (polygonVertexClassCount X.deckGroup o : ℝ) := by
  obtain ⟨R, hdense⟩ := X.exists_dirichlet_orbit_density_bound o
  have hgb := volume_dirichletDomain_gaussBonnet
    (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
    X.deck_fixing_point_acts_trivially (X.basepoint_mem_interior_dirichletDomain o) hdense
  have hpos : 0 < 2 * Real.pi *
      ((polygonSideCount X.deckGroup o : ℝ) - 1 - (polygonVertexClassCount X.deckGroup o : ℝ)) := by
    apply ENNReal.ofReal_pos.mp
    rw [← hgb, ← X.covolume_eq_dirichletDomain_volume o]
    exact pos_iff_ne_zero.mpr X.covolume_ne_zero
  have hdef : (∑ k : Fin (B.intrinsicBoundaryRadialCuts.card - 2),
      B.intrinsicVertexFanTriangleFundamentalDomain.angleDeficit k) =
      2 * Real.pi * ((polygonSideCount X.deckGroup o : ℝ) - 1 -
        (polygonVertexClassCount X.deckGroup o : ℝ)) := by
    apply (ENNReal.ofReal_eq_ofReal_iff
      (Finset.sum_nonneg (fun k _ =>
        B.intrinsicVertexFanTriangleFundamentalDomain.angleDeficit_nonneg k)) hpos.le).mp
    exact B.volume_dirichletDomain_eq_ofReal_sum_intrinsicVertexFanDeficit.symm.trans hgb
  have hside : B.intrinsicBoundaryRadialCuts.card = 2 * polygonSideCount X.deckGroup o := by
    rw [← B.ncard_polygonSides_eq_intrinsicBoundaryRadialCuts_card]
    exact ncard_polygonSides
      (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
      X.deck_fixing_point_acts_trivially (X.basepoint_mem_interior_dirichletDomain o) hdense
  have hside_real : (B.intrinsicBoundaryRadialCuts.card : ℝ) =
      2 * (polygonSideCount X.deckGroup o : ℝ) := by exact_mod_cast hside
  have hpi := congrArg (fun r : ℝ => Real.pi * r) hside_real
  rw [B.sum_intrinsicVertexFanCornerAngle_eq_pi_mul_sub_deficit, hdef,
    Nat.cast_sub (by have := B.three_le_intrinsicBoundaryRadialCuts_card; omega)]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hpi]

/-- Every original fan corner fiber, including the boundary apex, sums to
its actual polygon interior angle. The apex case follows by subtracting the
already proved nonapex fibers from the two independent global angle totals. -/
theorem sum_intrinsicVertexFanCornerAngle_eq_interiorAngle
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (∑ c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3
      with (B.intrinsicVertexFanCornerVertexIndex c).1 = i.1,
        B.intrinsicVertexFanCornerAngle c) = B.intrinsicCyclicInteriorAngle i := by
  classical
  let f : Fin B.intrinsicBoundaryRadialCuts.card → ℝ := fun j =>
    ∑ c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3
      with (B.intrinsicVertexFanCornerVertexIndex c).1 = j.1,
        B.intrinsicVertexFanCornerAngle c
  have hsum_f : (∑ j, f j) =
      2 * Real.pi * (polygonVertexClassCount X.deckGroup o : ℝ) := by
    have hregroup := Finset.sum_fiberwise
      (Finset.univ : Finset (Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3))
      B.intrinsicVertexFanCornerVertexIndex B.intrinsicVertexFanCornerAngle
    have hregroup' : (∑ j, f j) = ∑ c, B.intrinsicVertexFanCornerAngle c := by
      simpa only [f, Fin.ext_iff] using hregroup
    exact hregroup'.trans B.sum_intrinsicVertexFanCornerAngle
  by_cases hi : i.1 ≠ 0
  · exact B.sum_intrinsicVertexFanCornerAngle_of_ne_apex_eq_sector i hi
  · have hi0 : i.1 = 0 := not_ne_iff.mp hi
    have hdiff : (∑ j, (f j - B.intrinsicCyclicInteriorAngle j)) = 0 := by
      rw [Finset.sum_sub_distrib, hsum_f, B.sum_intrinsicCyclicInteriorAngle, sub_self]
    have hsingle : (∑ j, (f j - B.intrinsicCyclicInteriorAngle j)) =
        f i - B.intrinsicCyclicInteriorAngle i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        have hj : j.1 ≠ 0 := by
          intro hj0
          exact hji (Fin.ext (hj0.trans hi0.symm))
        exact sub_eq_zero.mpr (B.sum_intrinsicVertexFanCornerAngle_of_ne_apex_eq_sector j hj)
      · simp
    change f i = B.intrinsicCyclicInteriorAngle i
    linarith only [hdiff, hsingle]

end DirichletBoundarySegments

#print axioms sectorAngle_eq_add_of_strict_support
#print axioms DirichletBoundarySegments.intrinsicVertexFan_internal_angle
#print axioms DirichletBoundarySegments.sum_intrinsicVertexFanCornerAngle_internal_eq_sector
#print axioms DirichletBoundarySegments.sum_intrinsicVertexFanCornerAngle_first_eq_sector
#print axioms DirichletBoundarySegments.sum_intrinsicVertexFanCornerAngle_last_eq_sector
#print axioms DirichletBoundarySegments.sum_intrinsicVertexFanCornerAngle_of_ne_apex_eq_sector
#print axioms DirichletBoundarySegments.volume_dirichletDomain_eq_ofReal_sum_intrinsicVertexFanDeficit
#print axioms DirichletBoundarySegments.sum_intrinsicVertexFanCornerAngle_eq_pi_mul_sub_deficit
#print axioms DirichletBoundarySegments.sum_intrinsicCyclicInteriorAngle
#print axioms DirichletBoundarySegments.sum_intrinsicVertexFanCornerAngle
#print axioms DirichletBoundarySegments.sum_intrinsicVertexFanCornerAngle_eq_interiorAngle

end SystolicGrowth
