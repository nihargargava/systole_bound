module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletCyclicBoundary
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Topology.Separation.Connected

@[expose] public section

/-!
# Cyclic enumeration of the actual intrinsic Dirichlet boundary

The finite radial cuts are sorted by their actual complex arguments. The
successor permutation closes the last-to-first arc across the argument
branch cut. Consecutive complementary arcs are matched to the existing
intrinsic edge indices, retaining their genuine endpoints and deck pairing.
No cyclic traversal is supplied as a premise.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth

private theorem mem_range_circle_path_iff_of_arg_lt {a b ξ : Circle}
    (hab : Complex.arg (a : ℂ) < Complex.arg (b : ℂ)) :
    ξ ∈ Set.range (Circle.path a b) ↔
      Complex.arg (ξ : ℂ) ∈ Set.Icc (Complex.arg (a : ℂ)) (Complex.arg (b : ℂ)) := by
  have hend : Circle.angleDiff a b + Complex.arg (a : ℂ) = Complex.arg (b : ℂ) := by
    simp [Circle.angleDiff, hab.le]
  rw [Circle.range_path, hend]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [Circle.arg_exp ((Complex.neg_pi_lt_arg _).trans_le ht.1)
      (ht.2.trans (Complex.arg_le_pi _))]
    exact ht
  · intro hξ
    exact ⟨Complex.arg (ξ : ℂ), hξ, Circle.exp_arg ξ⟩

private theorem mem_circle_open_arc_iff_arg {a b ξ : Circle} (hab : a ≠ b) :
    ξ ∈ Circle.path a b '' Set.Ioo 0 1 ↔
      if Complex.arg (a : ℂ) ≤ Complex.arg (b : ℂ) then
        Complex.arg (a : ℂ) < Complex.arg (ξ : ℂ) ∧
          Complex.arg (ξ : ℂ) < Complex.arg (b : ℂ)
      else Complex.arg (a : ℂ) < Complex.arg (ξ : ℂ) ∨
        Complex.arg (ξ : ℂ) < Complex.arg (b : ℂ) := by
  by_cases harg : Complex.arg (a : ℂ) ≤ Complex.arg (b : ℂ)
  · rw [if_pos harg]
    have harglt : Complex.arg (a : ℂ) < Complex.arg (b : ℂ) :=
      lt_of_le_of_ne harg (fun h => hab (Circle.injective_arg h))
    have hopen : ξ ∈ Circle.path a b '' Set.Ioo 0 1 ↔
        ξ ∈ Set.range (Circle.path a b) ∧ ξ ≠ a ∧ ξ ≠ b := by
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨Set.mem_range_self t,
          fun h => ht.1.ne' (Circle.path_injective_of_ne hab
            (h.trans (Circle.path a b).source.symm)),
          fun h => ht.2.ne (Circle.path_injective_of_ne hab
            (h.trans (Circle.path a b).target.symm))⟩
      · rintro ⟨⟨t, rfl⟩, hta, htb⟩
        refine ⟨t, ⟨?_, ?_⟩, rfl⟩
        · exact lt_of_le_of_ne (by exact bot_le)
            (fun h => hta (h.symm ▸ (Circle.path a b).source))
        · exact lt_of_le_of_ne (by exact le_top)
            (fun h => htb (h ▸ (Circle.path a b).target))
    rw [hopen, mem_range_circle_path_iff_of_arg_lt harglt]
    simp only [Set.mem_Icc]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hξa, hξb⟩
      exact ⟨lt_of_le_of_ne hlo (fun h => hξa (Circle.injective_arg h.symm)),
        lt_of_le_of_ne hhi (fun h => hξb (Circle.injective_arg h))⟩
    · intro hξ
      exact ⟨⟨hξ.1.le, hξ.2.le⟩,
        fun h => hξ.1.ne (congrArg (fun z : Circle => Complex.arg (z : ℂ)) h.symm),
        fun h => hξ.2.ne (congrArg (fun z : Circle => Complex.arg (z : ℂ)) h)⟩
  · rw [if_neg harg, ← Circle.compl_range_path hab.symm,
      Set.mem_compl_iff, mem_range_circle_path_iff_of_arg_lt (lt_of_not_ge harg)]
    simp only [Set.mem_Icc, not_and_or, not_le]
    exact or_comm

private theorem finRotate_ne_self_of_two_le {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    finRotate n i ≠ i := by
  cases n with
  | zero => omega
  | succ n =>
    by_cases hi : i = Fin.last n
    · subst i
      rw [finRotate_last]
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_last] at hv
      omega
    · intro h
      have hv := coe_finRotate_of_ne_last hi
      rw [h] at hv
      omega

private theorem closure_circle_open_arc {a b : Circle} :
    closure (Circle.path a b '' Set.Ioo 0 1) = Set.range (Circle.path a b) := by
  apply Set.Subset.antisymm
  · exact closure_minimal (Set.image_subset_range _ _)
      (isCompact_range (Circle.path a b).continuous).isClosed
  · have hclosure : closure (Set.Ioo (0 : unitInterval) 1) = Set.univ := by
      rw [closure_Ioo (show (0 : unitInterval) ≠ 1 from zero_lt_one.ne)]
      exact unitInterval.univ_eq_Icc.symm
    calc
      Set.range (Circle.path a b) = Circle.path a b '' closure (Set.Ioo 0 1) := by
        rw [hclosure, Set.image_univ]
      _ ⊆ closure (Circle.path a b '' Set.Ioo 0 1) :=
        image_closure_subset_closure_image (Circle.path a b).continuous

private theorem range_circle_path_eq_open_union_endpoints (a b : Circle) :
    Set.range (Circle.path a b) = Circle.path a b '' Set.Ioo 0 1 ∪ {a, b} := by
  rw [← Set.image_univ, unitInterval.univ_eq_Icc,
    ← Set.Ioo_union_both (show (0 : unitInterval) ≤ 1 from bot_le), Set.image_union]
  simp only [Set.image_pair, Path.source, Path.target]

private theorem connectedComponentIn_circle_cutComplement_eq_arc
    {C : Set Circle} {a b ξ : Circle} (hab : a ≠ b) (ha : a ∈ C) (hb : b ∈ C)
    (hdisj : Disjoint (Circle.path a b '' Set.Ioo 0 1) C)
    (hξ : ξ ∈ Circle.path a b '' Set.Ioo 0 1) :
    connectedComponentIn Cᶜ ξ = Circle.path a b '' Set.Ioo 0 1 := by
  let U := Circle.path a b '' Set.Ioo 0 1
  have hUR : U ⊆ Cᶜ := hdisj.subset_compl_right
  have heq : ((↑) ⁻¹' U : Set ↥(Cᶜ)) = (↑) ⁻¹' Set.range (Circle.path a b) := by
    ext ζ
    constructor
    · rintro ⟨t, _, ht⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      have hta : t ≠ 0 := by
        intro h
        subst t
        have hζa : ζ.1 = a := ht.symm.trans (Circle.path a b).source
        exact ζ.2 (hζa.symm ▸ ha)
      have htb : t ≠ 1 := by
        intro h
        subst t
        have hζb : ζ.1 = b := ht.symm.trans (Circle.path a b).target
        exact ζ.2 (hζb.symm ▸ hb)
      exact ⟨t, ⟨lt_of_le_of_ne bot_le hta.symm, lt_of_le_of_ne le_top htb⟩, ht⟩
  have hUo : IsOpen U := by
    rw [show U = (Set.range (Circle.path b a))ᶜ from
      (Circle.compl_range_path hab.symm).symm]
    exact (isCompact_range (Circle.path b a).continuous).isClosed.isOpen_compl
  have hclopen : IsClopen ((↑) ⁻¹' U : Set ↥(Cᶜ)) := by
    refine ⟨?_, hUo.preimage continuous_subtype_val⟩
    rw [heq]
    exact (isCompact_range (Circle.path a b).continuous).isClosed.preimage continuous_subtype_val
  have hξR : ξ ∈ Cᶜ := hUR hξ
  apply Set.Subset.antisymm
  · rw [connectedComponentIn_eq_image hξR]
    rintro ζ ⟨v, hv, rfl⟩
    exact isPreconnected_connectedComponent.subset_isClopen hclopen
      ⟨(⟨ξ, hξR⟩ : ↥(Cᶜ)), mem_connectedComponent, hξ⟩ hv
  · exact ((isConnected_Ioo (by exact zero_lt_one : (0 : unitInterval) < 1)).image _
      (Circle.path a b).continuous.continuousOn).isPreconnected.subset_connectedComponentIn hξ hUR

private theorem sorted_consecutive_circle_arcs_disjoint_range
    {n : ℕ} (hn : 2 ≤ n) (v : Fin n → Circle)
    (hv : StrictMono (fun i => Complex.arg (v i : ℂ))) (i : Fin n) :
    Disjoint (Circle.path (v i) (v (finRotate n i)) '' Set.Ioo 0 1) (Set.range v) := by
  cases n with
  | zero => omega
  | succ n =>
    apply Set.disjoint_left.mpr
    rintro ξ hξ ⟨j, rfl⟩
    by_cases hi : i = Fin.last n
    · subst i
      rw [finRotate_last] at hξ
      have harg : Complex.arg (v (0 : Fin (n + 1)) : ℂ) <
          Complex.arg (v (Fin.last n) : ℂ) := hv (by change 0 < n; omega)
      rw [mem_circle_open_arc_iff_arg (fun h => harg.ne
        (congrArg (fun z : Circle => Complex.arg (z : ℂ)) h.symm)),
        if_neg (not_le_of_gt harg)] at hξ
      rcases hξ with hξ | hξ
      · exact (not_lt_of_ge (hv.monotone j.le_last)) hξ
      · exact (not_lt_of_ge (hv.monotone (by exact bot_le))) hξ
    · have hnext : i < finRotate (n + 1) i := (lt_finRotate_iff_ne_last i).mpr hi
      have harg := hv hnext
      rw [mem_circle_open_arc_iff_arg (fun h => harg.ne
        (congrArg (fun z : Circle => Complex.arg (z : ℂ)) h)), if_pos harg.le] at hξ
      have hlo : i < j := hv.lt_iff_lt.mp hξ.1
      have hhi : j < finRotate (n + 1) i := hv.lt_iff_lt.mp hξ.2
      have hval := coe_finRotate_of_ne_last hi
      simp only [Fin.lt_def] at hlo hhi
      omega

private theorem sorted_circle_arc_disjoint_range_implies_successor
    {n : ℕ} (v : Fin n → Circle) (hv : StrictMono (fun i => Complex.arg (v i : ℂ)))
    {i j : Fin n} (hij : i ≠ j)
    (hdisj : Disjoint (Circle.path (v i) (v j) '' Set.Ioo 0 1) (Set.range v)) :
    j = finRotate n i := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    have hne : v i ≠ v j := fun h => hij (hv.injective
      (congrArg (fun z : Circle => Complex.arg (z : ℂ)) h))
    by_cases hi : i = Fin.last n
    · subst i
      rw [finRotate_last]
      by_contra hj
      have hjlt : j < Fin.last n := (Fin.lt_last_iff_ne_last).mpr hij.symm
      have hjpos : (0 : Fin (n + 1)) < j := bot_lt_iff_ne_bot.mpr hj
      have harg := hv hjlt
      have hmem : v 0 ∈ Circle.path (v (Fin.last n)) (v j) '' Set.Ioo 0 1 := by
        rw [mem_circle_open_arc_iff_arg hne, if_neg (not_le_of_gt harg)]
        exact Or.inr (hv hjpos)
      exact Set.disjoint_left.mp hdisj hmem (Set.mem_range_self 0)
    · have hnext : i < finRotate (n + 1) i := (lt_finRotate_iff_ne_last i).mpr hi
      have hilj : i < j := by
        by_contra hijle
        have hjli : j < i := lt_of_le_of_ne (le_of_not_gt hijle) hij.symm
        have hmem : v (finRotate (n + 1) i) ∈ Circle.path (v i) (v j) '' Set.Ioo 0 1 := by
          rw [mem_circle_open_arc_iff_arg hne, if_neg (not_le_of_gt (hv hjli))]
          exact Or.inl (hv hnext)
        exact Set.disjoint_left.mp hdisj hmem (Set.mem_range_self _)
      by_contra hj
      have hnextj : finRotate (n + 1) i < j := by
        have hval := coe_finRotate_of_ne_last hi
        have hvne : (j : ℕ) ≠ (finRotate (n + 1) i : ℕ) := fun h => hj (Fin.ext h)
        simp only [Fin.lt_def] at hilj ⊢
        omega
      have hmem : v (finRotate (n + 1) i) ∈ Circle.path (v i) (v j) '' Set.Ioo 0 1 := by
        rw [mem_circle_open_arc_iff_arg hne, if_pos (hv hilj).le]
        exact ⟨hv hnext, hv hnextj⟩
      exact Set.disjoint_left.mp hdisj hmem (Set.mem_range_self _)

private theorem sorted_consecutive_circle_arcs_pairwise_disjoint
    {n : ℕ} (v : Fin n → Circle) (hv : StrictMono (fun i => Complex.arg (v i : ℂ)))
    {i j : Fin n} (hij : i ≠ j) :
    Disjoint (Circle.path (v i) (v (finRotate n i)) '' Set.Ioo 0 1)
      (Circle.path (v j) (v (finRotate n j)) '' Set.Ioo 0 1) := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    have hordinary (k : Fin (n + 1)) (hk : k ≠ Fin.last n) {ξ : Circle}
        (hξ : ξ ∈ Circle.path (v k) (v (finRotate (n + 1) k)) '' Set.Ioo 0 1) :
        Complex.arg (v k : ℂ) < Complex.arg (ξ : ℂ) ∧
          Complex.arg (ξ : ℂ) < Complex.arg (v (finRotate (n + 1) k) : ℂ) := by
      have harg := hv ((lt_finRotate_iff_ne_last k).mpr hk)
      rwa [mem_circle_open_arc_iff_arg (fun h => harg.ne
        (congrArg (fun z : Circle => Complex.arg (z : ℂ)) h)), if_pos harg.le] at hξ
    have hwrap {k : Fin (n + 1)} (hk : k ≠ Fin.last n) {ξ : Circle}
        (hξ : ξ ∈ Circle.path (v (Fin.last n)) (v (finRotate (n + 1) (Fin.last n))) ''
          Set.Ioo 0 1)
        (hξk : ξ ∈ Circle.path (v k) (v (finRotate (n + 1) k)) '' Set.Ioo 0 1) : False := by
      have hn : 0 < n := by
        have hklt := Fin.val_lt_last hk
        omega
      have harg := hv (show (0 : Fin (n + 1)) < Fin.last n from hn)
      rw [finRotate_last, mem_circle_open_arc_iff_arg (fun h => harg.ne
        (congrArg (fun z : Circle => Complex.arg (z : ℂ)) h.symm)),
        if_neg (not_le_of_gt harg)] at hξ
      have hkarg := hordinary k hk hξk
      rcases hξ with hξ | hξ
      · exact (not_lt_of_ge (hv.monotone (finRotate (n + 1) k).le_last))
          (hξ.trans hkarg.2)
      · exact (not_lt_of_ge (hv.monotone (show (0 : Fin (n + 1)) ≤ k from bot_le)))
          (hkarg.1.trans hξ)
    apply Set.disjoint_left.mpr
    intro ξ hξi hξj
    by_cases hi : i = Fin.last n
    · subst i
      exact hwrap hij.symm hξi hξj
    by_cases hj : j = Fin.last n
    · subst j
      exact hwrap hij hξj hξi
    have hai := hordinary i hi hξi
    have haj := hordinary j hj hξj
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hnextle : finRotate (n + 1) i ≤ j := by
        have hval := coe_finRotate_of_ne_last hi
        simp only [Fin.lt_def] at hijlt
        change (finRotate (n + 1) i : ℕ) ≤ j
        omega
      exact (hai.2.trans_le (hv.monotone hnextle)).not_gt haj.1
    · have hnextle : finRotate (n + 1) j ≤ i := by
        have hval := coe_finRotate_of_ne_last hj
        simp only [Fin.lt_def] at hjilt
        change (finRotate (n + 1) j : ℕ) ≤ i
        omega
      exact (haj.2.trans_le (hv.monotone hnextle)).not_gt hai.1

namespace DirichletBoundarySegments

/-- The actual radial cuts include the two distinct endpoints of an actual
edge. Such an edge exists because a finite set cannot exhaust the circle. -/
theorem two_le_intrinsicBoundaryRadialCuts_card
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) : 2 ≤ B.intrinsicBoundaryRadialCuts.card := by
  classical
  letI : Nontrivial Circle := ⟨⟨-1, 1, Circle.neg_ne_self 1⟩⟩
  letI : Infinite Circle := PreconnectedSpace.infinite
  obtain ⟨ξ, hξ⟩ := B.intrinsicBoundaryRadialCuts.exists_notMem
  obtain ⟨s, _⟩ := (B.not_mem_intrinsicBoundaryRadialCuts_iff_exists_openEdge ξ).mp hξ
  obtain ⟨a, ha, b, hb, hab, _⟩ := B.exists_intrinsicOpenEdgeRadialImage_adjacent_arc s
  calc
    2 = ({a, b} : Finset Circle).card := by simp [hab]
    _ ≤ B.intrinsicBoundaryRadialCuts.card := Finset.card_le_card (by
      intro ζ hζ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hζ
      rcases hζ with rfl | rfl <;> assumption)

/-- Increasing argument enumeration of the actual finite intrinsic radial
cuts. The linear order is local to this construction and is not a new
global ordering on `Circle`. -/
noncomputable def intrinsicRadialCutEnumeration
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    Fin B.intrinsicBoundaryRadialCuts.card ≃ B.intrinsicBoundaryRadialCuts := by
  classical
  letI : LinearOrder Circle :=
    LinearOrder.lift' (fun ξ : Circle => Complex.arg (ξ : ℂ)) Circle.injective_arg
  exact (B.intrinsicBoundaryRadialCuts.orderIsoOfFin rfl).toEquiv

/-- The actual cut enumeration is strictly increasing in argument. -/
theorem intrinsicRadialCutEnumeration_strictMono_arg
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    StrictMono (fun i => Complex.arg ((B.intrinsicRadialCutEnumeration i).1 : ℂ)) := by
  classical
  letI : LinearOrder Circle :=
    LinearOrder.lift' (fun ξ : Circle => Complex.arg (ξ : ℂ)) Circle.injective_arg
  exact (B.intrinsicBoundaryRadialCuts.orderIsoOfFin rfl).strictMono

/-- Every consecutive directed arc of the sorted actual cut list avoids
all intrinsic radial cuts, including the last-to-first arc. -/
theorem intrinsicRadialCutEnumeration_consecutive_arc_disjoint
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Disjoint
      (Circle.path (B.intrinsicRadialCutEnumeration i).1
        (B.intrinsicRadialCutEnumeration (finRotate B.intrinsicBoundaryRadialCuts.card i)).1 ''
          Set.Ioo 0 1)
      (↑B.intrinsicBoundaryRadialCuts : Set Circle) := by
  have hdisj := sorted_consecutive_circle_arcs_disjoint_range
    B.two_le_intrinsicBoundaryRadialCuts_card
    (fun j => (B.intrinsicRadialCutEnumeration j).1)
    B.intrinsicRadialCutEnumeration_strictMono_arg i
  apply hdisj.mono_right
  intro ξ hξ
  obtain ⟨j, hj⟩ := B.intrinsicRadialCutEnumeration.surjective ⟨ξ, hξ⟩
  exact ⟨j, congrArg Subtype.val hj⟩

/-- Distinct actual intrinsic radial open-edge images are disjoint. The
actual radial injectivity carries this from the existing hyperbolic edges. -/
theorem intrinsicOpenEdgeRadialImage_pairwise_disjoint
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    {s t : DirichletOpenEdgeIndex B B.intrinsicCornerCuts} (hst : s ≠ t) :
    Disjoint
      ((↑) ⁻¹' (hyperbolicRadialDirection o '' B.openEdgeImage B.intrinsicCornerCuts s) :
        Set Circle)
      ((↑) ⁻¹' (hyperbolicRadialDirection o '' B.openEdgeImage B.intrinsicCornerCuts t)) := by
  apply Set.disjoint_left.mpr
  rintro ξ ⟨z, hz, hzξ⟩ ⟨w, hw, hwξ⟩
  have hzw : z = w := X.hyperbolicRadialDirection_injOn_frontier o
    (B.intrinsicOpenEdgeImage_subset_regular_frontier s hz).1
    (B.intrinsicOpenEdgeImage_subset_regular_frontier t hw).1 (hzξ.trans hwξ.symm)
  exact Set.disjoint_left.mp (B.intrinsicOpenEdgeImage_pairwise_disjoint hst) hz (hzw ▸ hw)

/-- A consecutive actual directed arc is the radial image of exactly one
existing intrinsic edge. This constructs the edge assignment rather than
assuming an enumeration of the boundary pieces. -/
theorem existsUnique_intrinsicOpenEdge_of_consecutive_radialCuts
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    ∃! s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts,
      ((↑) ⁻¹' (hyperbolicRadialDirection o '' B.openEdgeImage B.intrinsicCornerCuts s) :
        Set Circle) =
      Circle.path (B.intrinsicRadialCutEnumeration i).1
        (B.intrinsicRadialCutEnumeration (finRotate B.intrinsicBoundaryRadialCuts.card i)).1 ''
          Set.Ioo 0 1 := by
  let a := (B.intrinsicRadialCutEnumeration i).1
  let b := (B.intrinsicRadialCutEnumeration (finRotate B.intrinsicBoundaryRadialCuts.card i)).1
  let U := Circle.path a b '' Set.Ioo 0 1
  have hab : a ≠ b := by
    intro h
    have hi := B.intrinsicRadialCutEnumeration.injective (Subtype.ext h)
    exact finRotate_ne_self_of_two_le B.two_le_intrinsicBoundaryRadialCuts_card i hi.symm
  have hU : IsConnected U :=
    (isConnected_Ioo (by exact zero_lt_one : (0 : unitInterval) < 1)).image _
      (Circle.path a b).continuous.continuousOn
  obtain ⟨ξ, hξ⟩ := hU.nonempty
  have hξnot : ξ ∉ B.intrinsicBoundaryRadialCuts :=
    Set.disjoint_left.mp (B.intrinsicRadialCutEnumeration_consecutive_arc_disjoint i) hξ
  obtain ⟨s, hξs⟩ := (B.not_mem_intrinsicBoundaryRadialCuts_iff_exists_openEdge ξ).mp hξnot
  have heq : ((↑) ⁻¹' (hyperbolicRadialDirection o ''
      B.openEdgeImage B.intrinsicCornerCuts s) : Set Circle) = U := by
    rw [← B.connectedComponentIn_radialCutComplement_eq_intrinsicOpenEdge s hξs]
    exact connectedComponentIn_circle_cutComplement_eq_arc hab
      (B.intrinsicRadialCutEnumeration i).2
      (B.intrinsicRadialCutEnumeration (finRotate B.intrinsicBoundaryRadialCuts.card i)).2
      (B.intrinsicRadialCutEnumeration_consecutive_arc_disjoint i) hξ
  refine ⟨s, heq, ?_⟩
  intro t ht
  by_contra hts
  exact Set.disjoint_left.mp (B.intrinsicOpenEdgeRadialImage_pairwise_disjoint hts)
    (ht.symm ▸ hξ) hξs

/-- The existing intrinsic edge occupying one consecutive argument arc.
Existence and uniqueness were proved from actual frontier coverage. -/
noncomputable def intrinsicCyclicEdge
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    DirichletOpenEdgeIndex B B.intrinsicCornerCuts :=
  Classical.choose (B.existsUnique_intrinsicOpenEdge_of_consecutive_radialCuts i)

/-- The selected existing edge has exactly the consecutive directed arc
specified by the actual sorted cuts. -/
theorem intrinsicCyclicEdge_radialImage
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    ((↑) ⁻¹' (hyperbolicRadialDirection o ''
      B.openEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i)) : Set Circle) =
      Circle.path (B.intrinsicRadialCutEnumeration i).1
        (B.intrinsicRadialCutEnumeration (finRotate B.intrinsicBoundaryRadialCuts.card i)).1 ''
          Set.Ioo 0 1 :=
  (Classical.choose_spec (B.existsUnique_intrinsicOpenEdge_of_consecutive_radialCuts i)).1

/-- Different places in the cyclic cut enumeration give different actual
edges, because consecutive directed arcs have disjoint interiors. -/
theorem intrinsicCyclicEdge_injective
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) : Function.Injective B.intrinsicCyclicEdge := by
  intro i j hij
  by_contra hne
  obtain ⟨ξ, hξ⟩ := (B.isConnected_intrinsicOpenEdgeRadialImage (B.intrinsicCyclicEdge i)).nonempty
  have hξi := B.intrinsicCyclicEdge_radialImage i ▸ hξ
  have hξj := B.intrinsicCyclicEdge_radialImage j ▸ (hij ▸ hξ)
  exact Set.disjoint_left.mp
    (sorted_consecutive_circle_arcs_pairwise_disjoint
      (fun k => (B.intrinsicRadialCutEnumeration k).1)
      B.intrinsicRadialCutEnumeration_strictMono_arg hne) hξi hξj

/-- Every actual intrinsic edge occurs in the cyclic enumeration. Its
proved adjacent directed arc forces its terminal cut to be the successor
of its initial cut in the argument-sorted list. -/
theorem intrinsicCyclicEdge_surjective
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) : Function.Surjective B.intrinsicCyclicEdge := by
  intro s
  obtain ⟨a, ha, b, hb, hab, himage, hdisj⟩ :=
    B.exists_intrinsicOpenEdgeRadialImage_adjacent_arc s
  obtain ⟨i, hi⟩ := B.intrinsicRadialCutEnumeration.surjective ⟨a, ha⟩
  obtain ⟨j, hj⟩ := B.intrinsicRadialCutEnumeration.surjective ⟨b, hb⟩
  have hi' : (B.intrinsicRadialCutEnumeration i).1 = a := congrArg Subtype.val hi
  have hj' : (B.intrinsicRadialCutEnumeration j).1 = b := congrArg Subtype.val hj
  have hij : i ≠ j := by
    intro h
    subst j
    exact hab (hi'.symm.trans hj')
  have hnext : j = finRotate B.intrinsicBoundaryRadialCuts.card i := by
    apply sorted_circle_arc_disjoint_range_implies_successor
      (fun k => (B.intrinsicRadialCutEnumeration k).1)
      B.intrinsicRadialCutEnumeration_strictMono_arg hij
    rw [hi', hj']
    exact hdisj.mono_right (fun ξ hξ => by
      obtain ⟨k, rfl⟩ := hξ
      exact (B.intrinsicRadialCutEnumeration k).2)
  have hs : ((↑) ⁻¹' (hyperbolicRadialDirection o ''
      B.openEdgeImage B.intrinsicCornerCuts s) : Set Circle) =
      Circle.path (B.intrinsicRadialCutEnumeration i).1
        (B.intrinsicRadialCutEnumeration (finRotate B.intrinsicBoundaryRadialCuts.card i)).1 ''
          Set.Ioo 0 1 := by
    rw [← hnext, hi', hj']
    exact himage
  refine ⟨i, ?_⟩
  exact ((Classical.choose_spec
    (B.existsUnique_intrinsicOpenEdge_of_consecutive_radialCuts i)).2 s hs).symm

/-- The actual finite intrinsic edges are bijectively enumerated by the
cyclically consecutive actual radial cuts. No extra edge family is created. -/
noncomputable def intrinsicCyclicEdgeEnumeration
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    Fin B.intrinsicBoundaryRadialCuts.card ≃ DirichletOpenEdgeIndex B B.intrinsicCornerCuts :=
  Equiv.ofBijective B.intrinsicCyclicEdge
    ⟨B.intrinsicCyclicEdge_injective, B.intrinsicCyclicEdge_surjective⟩

@[simp]
theorem intrinsicCyclicEdgeEnumeration_apply
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicCyclicEdgeEnumeration i = B.intrinsicCyclicEdge i := rfl

/-- The actual closed edge at a cyclic position has exactly the closed
directed arc as its radial image, by closure under the actual homeomorphism. -/
theorem intrinsicCyclicEdge_closedRadialImage
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    ((↑) ⁻¹' (hyperbolicRadialDirection o ''
      B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i)) : Set Circle) =
      Set.range (Circle.path (B.intrinsicRadialCutEnumeration i).1
        (B.intrinsicRadialCutEnumeration (finRotate B.intrinsicBoundaryRadialCuts.card i)).1) := by
  let F := frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)
  let s := B.intrinsicCyclicEdge i
  have hsub : B.openEdgeImage B.intrinsicCornerCuts s ⊆ F :=
    fun _ hz => (B.intrinsicOpenEdgeImage_subset_regular_frontier s hz).1
  have hclosedsub : B.closedEdgeImage B.intrinsicCornerCuts s ⊆ F := by
    rw [← B.closure_openEdgeImage_eq_closedEdgeImage]
    exact closure_minimal hsub isClosed_frontier
  have hclosure : closure ((↑) ⁻¹' B.openEdgeImage B.intrinsicCornerCuts s : Set F) =
      (↑) ⁻¹' B.closedEdgeImage B.intrinsicCornerCuts s := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
      Subtype.image_preimage_coe, Set.inter_eq_right.mpr hsub,
      B.closure_openEdgeImage_eq_closedEdgeImage]
  rw [← X.image_radialHomeomorph_preimage_of_subset_frontier o hclosedsub,
    ← hclosure, (X.dirichletBoundaryRadialHomeomorph o).image_closure,
    X.image_radialHomeomorph_preimage_of_subset_frontier o hsub,
    B.intrinsicCyclicEdge_radialImage i, closure_circle_open_arc]

/-- The cyclic vertices are the genuine intrinsic exception points at the
sorted radial positions, recovered by the actual frontier homeomorphism. -/
noncomputable def intrinsicCyclicVertex
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) : ℍ :=
  ((X.dirichletBoundaryRadialHomeomorph o).symm (B.intrinsicRadialCutEnumeration i).1).1

/-- The unordered genuine endpoints of each existing edge agree with its
two consecutive cyclic vertices. No endpoint incidence is assumed. -/
theorem intrinsicCyclicEdge_endpoints_eq_or_swap
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.closedEdgeEndpoints B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) =
        (B.intrinsicCyclicVertex i,
          B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i)) ∨
      B.closedEdgeEndpoints B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) =
        (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i),
          B.intrinsicCyclicVertex i) := by
  let s := B.intrinsicCyclicEdge i
  let H := X.dirichletBoundaryRadialHomeomorph o
  let a := (B.intrinsicRadialCutEnumeration i).1
  let b := (B.intrinsicRadialCutEnumeration (finRotate B.intrinsicBoundaryRadialCuts.card i)).1
  have hend (z : ℍ) (hz : z ∈ B.closedEdgeEndpointSet B.intrinsicCornerCuts s) :
      z = B.intrinsicCyclicVertex i ∨
        z = B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i) := by
    have hzexc := B.intrinsicClosedEdgeEndpointSet_subset_exceptional s hz
    let ζ : Circle := H ⟨z, B.intrinsicExceptionalPoints_subset_frontier hzexc⟩
    have hζrange : ζ ∈ Set.range (Circle.path a b) := by
      rw [← B.intrinsicCyclicEdge_closedRadialImage i]
      refine ⟨z, ?_, rfl⟩
      rw [B.closedEdgeImage_eq_open_union_endpoints]
      exact Or.inr hz
    have hζnot : ζ ∉ Circle.path a b '' Set.Ioo 0 1 := by
      intro hζ
      have hcut : ζ ∈ B.intrinsicBoundaryRadialCuts :=
        (B.mem_intrinsicBoundaryRadialCuts_iff ζ).mpr ⟨z, hzexc, rfl⟩
      exact Set.disjoint_left.mp (B.intrinsicRadialCutEnumeration_consecutive_arc_disjoint i)
        hζ hcut
    rw [range_circle_path_eq_open_union_endpoints] at hζrange
    have hζends := hζrange.resolve_left hζnot
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hζends
    have hrecover : (H.symm ζ).1 = z := congrArg Subtype.val (H.symm_apply_apply _)
    rcases hζends with hζa | hζb
    · exact Or.inl (hrecover.symm.trans (congrArg (fun ξ => (H.symm ξ).1) hζa))
    · exact Or.inr (hrecover.symm.trans (congrArg (fun ξ => (H.symm ξ).1) hζb))
  have hl := hend (B.closedEdgeEndpoints B.intrinsicCornerCuts s).1
    (by simp [closedEdgeEndpointSet])
  have hr := hend (B.closedEdgeEndpoints B.intrinsicCornerCuts s).2
    (by simp [closedEdgeEndpointSet])
  rcases hl with hl | hl <;> rcases hr with hr | hr
  · exact (B.closedEdgeEndpoints_ne B.intrinsicCornerCuts s (hl.trans hr.symm)).elim
  · exact Or.inl (Prod.ext hl hr)
  · exact Or.inr (Prod.ext hl hr)
  · exact (B.closedEdgeEndpoints_ne B.intrinsicCornerCuts s (hl.trans hr.symm)).elim

/-- Each actual closed edge is the hyperbolic segment between its
consecutive genuine cyclic vertices, independent of its parameter orientation. -/
theorem intrinsicCyclicEdge_closedImage_eq_geodSeg
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) =
      Vendored.RiemannDynamics.geodSeg (B.intrinsicCyclicVertex i)
        (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i)) := by
  rw [B.closedEdgeImage_eq_geodSeg]
  rcases B.intrinsicCyclicEdge_endpoints_eq_or_swap i with h | h
  · rw [h]
  · rw [h, Vendored.RiemannDynamics.geodSeg_comm]

/-- Distinct cyclic positions give distinct genuine hyperbolic vertices. -/
theorem intrinsicCyclicVertex_injective
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) : Function.Injective B.intrinsicCyclicVertex := by
  intro i j hij
  apply B.intrinsicRadialCutEnumeration.injective
  apply Subtype.ext
  exact (X.dirichletBoundaryRadialHomeomorph o).symm.injective (Subtype.ext hij)

/-- The cyclic vertex list enumerates exactly the finite intrinsic
exception set, not a independently chosen candidate list. -/
theorem range_intrinsicCyclicVertex_eq_intrinsicExceptionalPoints
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    Set.range B.intrinsicCyclicVertex = B.intrinsicExceptionalPoints := by
  let H := X.dirichletBoundaryRadialHomeomorph o
  have hrecover {ξ : Circle} {z : ℍ} (hz : z ∈ B.intrinsicExceptionalPoints)
      (hzξ : hyperbolicRadialDirection o z = (ξ : ℂ)) : (H.symm ξ).1 = z := by
    have hH : H ⟨z, B.intrinsicExceptionalPoints_subset_frontier hz⟩ = ξ :=
      Circle.coe_injective hzξ
    exact congrArg Subtype.val ((congrArg H.symm hH).symm.trans (H.symm_apply_apply _))
  apply Set.Subset.antisymm
  · rintro z ⟨i, rfl⟩
    obtain ⟨w, hw, hwξ⟩ :=
      (B.mem_intrinsicBoundaryRadialCuts_iff (B.intrinsicRadialCutEnumeration i).1).mp
        (B.intrinsicRadialCutEnumeration i).2
    have hvertex : B.intrinsicCyclicVertex i = w := hrecover hw hwξ
    exact hvertex.symm ▸ hw
  · intro z hz
    let ξ : Circle := H ⟨z, B.intrinsicExceptionalPoints_subset_frontier hz⟩
    have hξcut : ξ ∈ B.intrinsicBoundaryRadialCuts :=
      (B.mem_intrinsicBoundaryRadialCuts_iff ξ).mpr ⟨z, hz, rfl⟩
    obtain ⟨i, hi⟩ := B.intrinsicRadialCutEnumeration.surjective ⟨ξ, hξcut⟩
    refine ⟨i, ?_⟩
    change (H.symm (B.intrinsicRadialCutEnumeration i).1).1 = z
    rw [show (B.intrinsicRadialCutEnumeration i).1 = ξ from congrArg Subtype.val hi]
    exact congrArg Subtype.val (H.symm_apply_apply _)

/-- The cyclically enumerated genuine closed edges cover exactly the actual
Dirichlet frontier, including all their cut vertices. -/
theorem iUnion_intrinsicCyclicClosedEdge_eq_frontier
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    (⋃ i : Fin B.intrinsicBoundaryRadialCuts.card,
      B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i)) =
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
    have hsub : B.openEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) ⊆
        frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) :=
      fun _ h => (B.intrinsicOpenEdgeImage_subset_regular_frontier _ h).1
    rw [← B.closure_openEdgeImage_eq_closedEdgeImage] at hzi
    exact closure_minimal hsub isClosed_frontier hzi
  · intro z hz
    by_cases he : z ∈ B.intrinsicExceptionalPoints
    · rw [← B.range_intrinsicCyclicVertex_eq_intrinsicExceptionalPoints] at he
      obtain ⟨i, rfl⟩ := he
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
      exact Vendored.RiemannDynamics.left_mem_geodSeg _ _
    · obtain ⟨s, hs⟩ := B.exists_intrinsicOpenEdgeImage_of_mem_regular_frontier ⟨hz, he⟩
      obtain ⟨i, hi⟩ := B.intrinsicCyclicEdge_surjective s
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      rw [hi, B.closedEdgeImage_eq_open_union_endpoints]
      exact Or.inl hs

/-- The genuine cyclic boundary has at least three vertices. Two vertices
would make both different directed edges the same hyperbolic segment,
contradicting the already proved intrinsic edge injectivity. -/
theorem three_le_intrinsicBoundaryRadialCuts_card
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) : 3 ≤ B.intrinsicBoundaryRadialCuts.card := by
  by_contra hthree
  have htwo := B.two_le_intrinsicBoundaryRadialCuts_card
  have hc : B.intrinsicBoundaryRadialCuts.card = 2 := by omega
  let i : Fin B.intrinsicBoundaryRadialCuts.card := ⟨0, by omega⟩
  let j : Fin B.intrinsicBoundaryRadialCuts.card := ⟨1, by omega⟩
  haveI : NeZero B.intrinsicBoundaryRadialCuts.card := ⟨by omega⟩
  have hri : finRotate B.intrinsicBoundaryRadialCuts.card i = j := by
    apply Fin.ext
    rw [finRotate_apply]
    simp [hc, i, j]
  have hrj : finRotate B.intrinsicBoundaryRadialCuts.card j = i := by
    apply Fin.ext
    rw [finRotate_apply]
    simp [Fin.val_add, hc, i, j]
  have hclosed : B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) =
      B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge j) := by
    rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg i,
      B.intrinsicCyclicEdge_closedImage_eq_geodSeg j, hri, hrj,
      Vendored.RiemannDynamics.geodSeg_comm]
  have hopen : B.openEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) =
      B.openEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge j) := by
    rw [B.intrinsicOpenEdgeImage_eq_closedEdgeImage_inter_regularFrontier,
      B.intrinsicOpenEdgeImage_eq_closedEdgeImage_inter_regularFrontier, hclosed]
  have hij := B.intrinsicCyclicEdge_injective (B.intrinsicOpenEdgeImage_injective hopen)
  have hval := congrArg Fin.val hij
  change (0 : ℕ) = 1 at hval
  omega

/-- The original inverse-deck pairing, transported through the proved
cyclic enumeration, with no newly chosen geometric pairing. -/
noncomputable def intrinsicCyclicPairing
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) : Equiv.Perm (Fin B.intrinsicBoundaryRadialCuts.card) :=
  (B.intrinsicCyclicEdgeEnumeration.trans B.intrinsicOpenEdgePairing).trans
    B.intrinsicCyclicEdgeEnumeration.symm

@[simp]
theorem intrinsicCyclicEdge_pairing
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicCyclicEdge (B.intrinsicCyclicPairing i) =
      B.inverseIntrinsicOpenEdge (B.intrinsicCyclicEdge i) := by
  change B.intrinsicCyclicEdgeEnumeration
    (B.intrinsicCyclicEdgeEnumeration.symm
      (B.intrinsicOpenEdgePairing (B.intrinsicCyclicEdgeEnumeration i))) = _
  exact B.intrinsicCyclicEdgeEnumeration.apply_symm_apply _

/-- Cyclic indexing preserves the original fixed-point-free involution. -/
theorem intrinsicCyclicPairing_involutive
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) : Function.Involutive B.intrinsicCyclicPairing := by
  intro i
  apply B.intrinsicCyclicEdge_injective
  rw [B.intrinsicCyclicEdge_pairing, B.intrinsicCyclicEdge_pairing,
    B.inverseIntrinsicOpenEdge_inverseIntrinsicOpenEdge]

theorem intrinsicCyclicPairing_ne_self
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicCyclicPairing i ≠ i := by
  intro hi
  have he := congrArg B.intrinsicCyclicEdge hi
  rw [B.intrinsicCyclicEdge_pairing] at he
  exact B.inverseIntrinsicOpenEdge_ne_self _ he

/-- The cyclic boundary retains the exact inverse-deck transport of its
actual closed edges. -/
theorem image_inv_smul_intrinsicCyclicClosedEdge
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (fun z : ℍ => (B.intrinsicCyclicEdge i).1.1.1⁻¹ • z) ''
      B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) =
      B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge (B.intrinsicCyclicPairing i)) := by
  rw [B.intrinsicCyclicEdge_pairing]
  exact B.image_inv_smul_intrinsicClosedEdge _

#print axioms intrinsicRadialCutEnumeration
#print axioms intrinsicRadialCutEnumeration_strictMono_arg
#print axioms intrinsicRadialCutEnumeration_consecutive_arc_disjoint
#print axioms existsUnique_intrinsicOpenEdge_of_consecutive_radialCuts
#print axioms intrinsicCyclicEdge_surjective
#print axioms intrinsicCyclicEdgeEnumeration
#print axioms intrinsicCyclicEdge_closedImage_eq_geodSeg
#print axioms iUnion_intrinsicCyclicClosedEdge_eq_frontier
#print axioms three_le_intrinsicBoundaryRadialCuts_card
#print axioms intrinsicCyclicPairing_involutive
#print axioms intrinsicCyclicPairing_ne_self
#print axioms image_inv_smul_intrinsicCyclicClosedEdge

end DirichletBoundarySegments
end SystolicGrowth
