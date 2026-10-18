module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletBoundaryIncidence

@[expose] public section

/-!
# Interval coordinates on regular Dirichlet boundary germs

Geodesic interpolation gives a distance-linear parameter on a nondegenerate
segment. At a boundary point away from the finite exceptional set, this
parameter will chart a neighborhood of the actual Dirichlet frontier.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth

/-- A nondegenerate hyperbolic geodesic segment is homeomorphic to the unit
closed interval via geodesic interpolation. -/
noncomputable def geodSegHomeomorph (a b : ℍ) (hab : a ≠ b) :
    Set.Icc (0 : ℝ) 1 ≃ₜ Vendored.RiemannDynamics.geodSeg a b where
  toFun t := ⟨Vendored.RiemannDynamics.geodInterp a b t.1,
    Vendored.RiemannDynamics.geodInterp_mem_geodSeg a b t.2⟩
  invFun z := ⟨dist a z.1 / dist a b, by
    have hseg : dist a z.1 + dist z.1 b = dist a b := z.2
    have hd : 0 < dist a b := dist_pos.mpr hab
    exact ⟨by positivity, (div_le_one hd).mpr (by nlinarith [dist_nonneg (x := z.1) (y := b)])⟩⟩
  left_inv t := by
    apply Subtype.ext
    change dist a (Vendored.RiemannDynamics.geodInterp a b t.1) / dist a b = t.1
    rw [Vendored.RiemannDynamics.dist_geodInterp_left a b t.2]
    exact mul_div_cancel_right₀ _ (dist_pos.mpr hab).ne'
  right_inv z := by
    apply Subtype.ext
    have hz : z.1 ∈ Vendored.RiemannDynamics.geodInterp a b '' Set.Icc (0 : ℝ) 1 := by
      rw [← Vendored.RiemannDynamics.geodSeg_eq_image_geodInterp]
      exact z.2
    obtain ⟨t, ht, htz⟩ := hz
    change Vendored.RiemannDynamics.geodInterp a b (dist a z.1 / dist a b) = z.1
    rw [← htz, Vendored.RiemannDynamics.dist_geodInterp_left a b ht]
    simp [(dist_pos.mpr hab).ne']
  continuous_toFun := by
    have hpair : Continuous (fun t : ℝ => (a, b, t)) := by fun_prop
    have hpath : Continuous (fun t : ℝ => Vendored.RiemannDynamics.geodInterp a b t) :=
      Vendored.RiemannDynamics.continuous_geodInterp.comp hpair
    exact Continuous.subtype_mk (hpath.comp continuous_subtype_val) _
  continuous_invFun := by
    apply Continuous.subtype_mk
    fun_prop

#print axioms geodSegHomeomorph

namespace DirichletBoundarySegments

/-- On a nondegenerate candidate side, only finitely many interpolation
parameters map to exceptional boundary points. -/
theorem exceptional_parameter_set_finite
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B) :
    {t : ℝ | t ∈ Set.Icc 0 1 ∧
      Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints}.Finite := by
  let a := (B.endpoints i.1).1
  let b := (B.endpoints i.1).2
  have hab : a ≠ b := i.2
  have hdne : dist a b ≠ 0 := (dist_pos.mpr hab).ne'
  apply (B.exceptionalPoints_finite.image (fun z : ℍ => dist a z / dist a b)).subset
  intro t ht
  refine ⟨Vendored.RiemannDynamics.geodInterp a b t, ht.2, ?_⟩
  change dist a (Vendored.RiemannDynamics.geodInterp a b t) / dist a b = t
  rw [Vendored.RiemannDynamics.dist_geodInterp_left a b ht.1]
  exact mul_div_cancel_right₀ _ hdne

#print axioms exceptional_parameter_set_finite

/-- The exceptional parameters on one nondegenerate candidate side, together
with its two endpoints, form a concrete finite set of subdivision cuts. -/
theorem exists_finite_parameter_cuts
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B) :
    ∃ cuts : Finset ℝ, ∀ t : ℝ,
      t ∈ cuts ↔ t = 0 ∨ t = 1 ∨
        (t ∈ Set.Icc 0 1 ∧
          Vendored.RiemannDynamics.geodInterp
            (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints) := by
  classical
  let cuts : Finset ℝ :=
    insert 0 (insert 1 (B.exceptional_parameter_set_finite i).toFinset)
  refine ⟨cuts, ?_⟩
  intro t
  simp only [cuts, Finset.mem_insert, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

#print axioms exists_finite_parameter_cuts

/-- Between adjacent endpoint-inclusive cuts, no point of the interpolated
side lies in the exceptional boundary set. This is an order-theoretic
consequence of the cut characterization, not a cyclic polygon assertion. -/
theorem geodInterp_not_exceptional_of_adjacent_cuts
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    (cuts : Finset ℝ)
    (hcuts : ∀ t : ℝ, t ∈ cuts ↔ t = 0 ∨ t = 1 ∨
      (t ∈ Set.Icc 0 1 ∧
        Vendored.RiemannDynamics.geodInterp
          (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints))
    {l r : ℝ} (_hl : l ∈ cuts) (_hr : r ∈ cuts)
    (h0l : 0 ≤ l) (hr1 : r ≤ 1) (_hlr : l < r)
    (hadj : ∀ c ∈ cuts, c ≤ l ∨ r ≤ c) :
    ∀ t ∈ Set.Ioo l r,
      Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t ∉ B.exceptionalPoints := by
  intro t ht htex
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_trans h0l (le_of_lt ht.1), le_trans (le_of_lt ht.2) hr1⟩
  have htcut : t ∈ cuts :=
    (hcuts t).2 (Or.inr (Or.inr ⟨htIcc, htex⟩))
  rcases hadj t htcut with htl | hrt
  · exact (not_le_of_gt ht.1) htl
  · exact (not_le_of_gt ht.2) hrt

#print axioms geodInterp_not_exceptional_of_adjacent_cuts

/-- An interior parameter outside a finite endpoint-inclusive cut set lies
between consecutive cuts in the ordinary linear order on real numbers. -/
theorem exists_adjacent_cuts_around (cuts : Finset ℝ)
    (hzero : (0 : ℝ) ∈ cuts) (hone : (1 : ℝ) ∈ cuts)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (htnot : t ∉ cuts) :
    ∃ l r : ℝ, l ∈ cuts ∧ r ∈ cuts ∧ 0 ≤ l ∧ r ≤ 1 ∧ l < t ∧ t < r ∧
      ∀ c ∈ cuts, c ≤ l ∨ r ≤ c := by
  classical
  let L := cuts.filter (fun c => c < t)
  let R := cuts.filter (fun c => t < c)
  have h0L : (0 : ℝ) ∈ L := Finset.mem_filter.mpr ⟨hzero, ht.1⟩
  have h1R : (1 : ℝ) ∈ R := Finset.mem_filter.mpr ⟨hone, ht.2⟩
  have hL : L.Nonempty := ⟨0, h0L⟩
  have hR : R.Nonempty := ⟨1, h1R⟩
  let l := L.max' hL
  let r := R.min' hR
  have ⟨hlcuts, hlt⟩ := Finset.mem_filter.mp (Finset.max'_mem L hL)
  have ⟨hrcuts, htr⟩ := Finset.mem_filter.mp (Finset.min'_mem R hR)
  have h0l : 0 ≤ l := Finset.le_max' L 0 h0L
  have hr1 : r ≤ 1 := Finset.min'_le R 1 h1R
  refine ⟨l, r, hlcuts, hrcuts, h0l, hr1, hlt, htr, ?_⟩
  intro c hc
  rcases lt_trichotomy c t with hct | hct | htc
  · exact Or.inl (Finset.le_max' L c (Finset.mem_filter.mpr ⟨hc, hct⟩))
  · rw [hct] at hc
    exact (htnot hc).elim
  · exact Or.inr (Finset.min'_le R c (Finset.mem_filter.mpr ⟨hc, htc⟩))

#print axioms exists_adjacent_cuts_around

/-- Every regular interior parameter of a nondegenerate candidate side has an
open parameter interval on which interpolation avoids exceptional points. -/
theorem exists_nonexceptional_parameter_interval
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hregular : Vendored.RiemannDynamics.geodInterp
      (B.endpoints i.1).1 (B.endpoints i.1).2 t ∉ B.exceptionalPoints) :
    ∃ l r : ℝ, 0 ≤ l ∧ r ≤ 1 ∧ l < t ∧ t < r ∧
      ∀ u ∈ Set.Ioo l r, Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 u ∉ B.exceptionalPoints := by
  obtain ⟨cuts, hcuts⟩ := B.exists_finite_parameter_cuts i
  have hzero : (0 : ℝ) ∈ cuts := (hcuts 0).2 (Or.inl rfl)
  have hone : (1 : ℝ) ∈ cuts := (hcuts 1).2 (Or.inr (Or.inl rfl))
  have htnot : t ∉ cuts := by
    intro htcuts
    rcases (hcuts t).1 htcuts with htzero | htone | htex
    · exact (ne_of_gt ht.1) htzero
    · exact (ne_of_lt ht.2) htone
    · exact hregular htex.2
  obtain ⟨l, r, hl, hr, h0l, hr1, hlt, htr, hadj⟩ :=
    exists_adjacent_cuts_around cuts hzero hone ht htnot
  refine ⟨l, r, h0l, hr1, hlt, htr, ?_⟩
  exact B.geodInterp_not_exceptional_of_adjacent_cuts i cuts hcuts
    hl hr h0l hr1 (lt_trans hlt htr) hadj

#print axioms exists_nonexceptional_parameter_interval

/-- Every nonexceptional frontier point has an ambient open neighborhood
whose frontier is homeomorphic to a real open interval. The chart is the
actual geodesic interpolation of its unique nondegenerate candidate section.
No compatibility between charts or global cyclic order is asserted. -/
theorem exists_open_interval_frontier_chart
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o z : ℍ}
    (B : DirichletBoundarySegments X o)
    (hzfront : z ∈ frontier
      (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o))
    (hzregular : z ∉ B.exceptionalPoints) :
    ∃ i : NondegenerateIndex B, ∃ l r : ℝ, ∃ V : Set ℍ,
      l < r ∧ IsOpen V ∧ z ∈ V ∧
      ∃ e : ↥(Set.Ioo l r) ≃ₜ
          ↥(V ∩ frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)),
        (∃ t : Set.Ioo l r, (e t).1 = z) ∧
        ∀ t : Set.Ioo l r, (e t).1 =
          Vendored.RiemannDynamics.geodInterp
            (B.endpoints i.1).1 (B.endpoints i.1).2 t.1 := by
  classical
  obtain ⟨i, U, hUopen, hzU, hUfront, _⟩ :=
    B.exists_open_unique_section_germ hzfront hzregular
  let a := (B.endpoints i.1).1
  let b := (B.endpoints i.1).2
  have hab : a ≠ b := i.2
  have hzi : z ∈ Vendored.RiemannDynamics.geodSeg a b := by
    have h : z ∈ U ∩ frontier
        (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := ⟨hzU, hzfront⟩
    exact (Set.ext_iff.mp hUfront z).mp h |>.2
  have hza : z ≠ a := by
    intro h
    exact hzregular (Or.inl ⟨i.1, Or.inl h⟩)
  have hzb : z ≠ b := by
    intro h
    exact hzregular (Or.inl ⟨i.1, Or.inr h⟩)
  let E := geodSegHomeomorph a b hab
  let t₀ : Set.Icc (0 : ℝ) 1 := E.symm ⟨z, hzi⟩
  have hzt₀ : Vendored.RiemannDynamics.geodInterp a b t₀.1 = z := by
    have h := congrArg Subtype.val (E.apply_symm_apply ⟨z, hzi⟩)
    exact h
  have ht₀ne0 : t₀.1 ≠ 0 := by
    intro h
    apply hza
    rw [← hzt₀, h, Vendored.RiemannDynamics.geodInterp_zero]
  have ht₀ne1 : t₀.1 ≠ 1 := by
    intro h
    apply hzb
    rw [← hzt₀, h, Vendored.RiemannDynamics.geodInterp_one]
  have ht₀pos : 0 < t₀.1 := lt_of_le_of_ne t₀.2.1 (Ne.symm ht₀ne0)
  have ht₀lt : t₀.1 < 1 := lt_of_le_of_ne t₀.2.2 ht₀ne1
  have hpath : Continuous (fun t : ℝ =>
      Vendored.RiemannDynamics.geodInterp a b t) := by
    have hpair : Continuous (fun t : ℝ => (a, b, t)) := by fun_prop
    exact Vendored.RiemannDynamics.continuous_geodInterp.comp hpair
  let P : Set ℝ :=
    (fun t => Vendored.RiemannDynamics.geodInterp a b t) ⁻¹' U ∩ Set.Ioo 0 1
  have hPopen : IsOpen P := (hUopen.preimage hpath).inter isOpen_Ioo
  have ht₀P : t₀.1 ∈ P := by
    exact ⟨by simpa [hzt₀], ⟨ht₀pos, ht₀lt⟩⟩
  obtain ⟨l, r, ht₀lr, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hPopen.mem_nhds ht₀P)
  have hdpos : 0 < dist a b := dist_pos.mpr hab
  have hdne : dist a b ≠ 0 := hdpos.ne'
  let V : Set ℍ := U ∩
    {w : ℍ | l < dist a w / dist a b ∧ dist a w / dist a b < r}
  have hcoord_cont : Continuous (fun w : ℍ => dist a w / dist a b) := by fun_prop
  have hVopen : IsOpen V := by
    change IsOpen (U ∩
      ({w : ℍ | l < dist a w / dist a b} ∩
        {w : ℍ | dist a w / dist a b < r}))
    exact hUopen.inter
      ((isOpen_lt continuous_const hcoord_cont).inter
        (isOpen_lt hcoord_cont continuous_const))
  have hzcoord : dist a z / dist a b = t₀.1 := by
    rw [← hzt₀, Vendored.RiemannDynamics.dist_geodInterp_left a b t₀.2]
    exact mul_div_cancel_right₀ _ hdne
  have hzV : z ∈ V := ⟨hzU, by simpa [hzcoord] using ht₀lr⟩
  let hchart : ↥(Set.Ioo l r) ≃ₜ
      ↥(V ∩ frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)) := {
    toFun t := by
      have htP : t.1 ∈ P := hsub t.2
      have htIcc : t.1 ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨le_of_lt htP.2.1, le_of_lt htP.2.2⟩
      have htseg := Vendored.RiemannDynamics.geodInterp_mem_geodSeg a b htIcc
      have htcoord : dist a (Vendored.RiemannDynamics.geodInterp a b t.1) /
          dist a b = t.1 := by
        rw [Vendored.RiemannDynamics.dist_geodInterp_left a b htIcc]
        exact mul_div_cancel_right₀ _ hdne
      refine ⟨Vendored.RiemannDynamics.geodInterp a b t.1,
        ⟨⟨htP.1, ?_⟩, B.segment_subset_frontier i.1 htseg⟩⟩
      change l < dist a (Vendored.RiemannDynamics.geodInterp a b t.1) /
        dist a b ∧
        dist a (Vendored.RiemannDynamics.geodInterp a b t.1) / dist a b < r
      rw [htcoord]
      exact t.2
    invFun w := ⟨dist a w.1 / dist a b, w.2.1.2⟩
    left_inv t := by
      apply Subtype.ext
      have htP : t.1 ∈ P := hsub t.2
      have htIcc : t.1 ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨le_of_lt htP.2.1, le_of_lt htP.2.2⟩
      change dist a (Vendored.RiemannDynamics.geodInterp a b t.1) /
        dist a b = t.1
      rw [Vendored.RiemannDynamics.dist_geodInterp_left a b htIcc]
      exact mul_div_cancel_right₀ _ hdne
    right_inv w := by
      apply Subtype.ext
      have hwseg : w.1 ∈ Vendored.RiemannDynamics.geodSeg a b := by
        have h : w.1 ∈ U ∩ frontier
            (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) :=
          ⟨w.2.1.1, w.2.2⟩
        exact (Set.ext_iff.mp hUfront w.1).mp h |>.2
      have h := congrArg Subtype.val (E.apply_symm_apply ⟨w.1, hwseg⟩)
      exact h
    continuous_toFun := by
      exact Continuous.subtype_mk (hpath.comp continuous_subtype_val) _
    continuous_invFun := by
      apply Continuous.subtype_mk
      fun_prop
  }
  refine ⟨i, l, r, V, lt_trans ht₀lr.1 ht₀lr.2, hVopen, hzV, hchart, ?_, ?_⟩
  · refine ⟨⟨t₀.1, ht₀lr⟩, ?_⟩
    exact hzt₀
  · intro t
    rfl

#print axioms exists_open_interval_frontier_chart

end DirichletBoundarySegments

end SystolicGrowth
