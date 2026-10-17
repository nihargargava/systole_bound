module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletGapDisjointness
public import Geometry.DirichletSectionPairing

@[expose] public section

/-!
# Intrinsic corner transport under inverse side pairing

An actual Dirichlet corner on the section labeled by `γ` is a point of the
Dirichlet domain equidistant from the basepoint and the orbit points labeled
by `γ` and a second, distinct nonidentity deck element. Inverse deck action
transports this condition exactly to the section labeled by `γ⁻¹`. The
finite candidate exceptional set in `DirichletBoundaryIncidence` additionally
depends on a chosen finite label family; its invariance is not assumed here.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth
namespace ClosedHyperbolicSurface

/-- Actual two-label corners on one Dirichlet bisector section, defined using
the full deck group rather than a chosen finite boundary presentation. -/
def dirichletSectionCorners {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (γ : X.deckGroup) : Set ℍ :=
  {z | z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∧
    dist z o = dist z (γ • o) ∧
    ∃ δ : X.deckGroup, δ ≠ 1 ∧ δ ≠ γ ∧
      dist z o = dist z (δ • o)}

/-- The inverse side pairing carries a genuine two-label corner to a genuine
corner on the paired section; the second label becomes `γ⁻¹ * δ`. -/
theorem inv_smul_mem_dirichletSectionCorners
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ)
    (γ : X.deckGroup) {z : ℍ}
    (hz : z ∈ X.dirichletSectionCorners o γ) :
    γ⁻¹ • z ∈ X.dirichletSectionCorners o γ⁻¹ := by
  obtain ⟨hzD, hzγ, δ, hδone, hδγ, hzδ⟩ := hz
  have hpair := X.inv_smul_mem_dirichlet_bisector_section o γ ⟨hzD, hzγ⟩
  have hδ'one : γ⁻¹ * δ ≠ 1 := by
    intro h
    exact hδγ (inv_mul_eq_one.mp h).symm
  have hδ'inv : γ⁻¹ * δ ≠ γ⁻¹ := by
    intro h
    have h' : γ⁻¹ * δ = γ⁻¹ * 1 := by simpa using h
    exact hδone (mul_left_cancel h')
  refine ⟨hpair.1, hpair.2, γ⁻¹ * δ, hδ'one, hδ'inv, ?_⟩
  have hleft : dist (γ⁻¹ • z) o = dist z (γ • o) := by
    rw [← dist_smul γ (γ⁻¹ • z) o, smul_inv_smul]
  calc
    dist (γ⁻¹ • z) o = dist z (γ • o) := hleft
    _ = dist z o := hzγ.symm
    _ = dist z (δ • o) := hzδ
    _ = dist (γ⁻¹ • z) ((γ⁻¹ * δ) • o) := by
      rw [mul_smul]
      exact (dist_smul γ⁻¹ z (δ • o)).symm

/-- Intrinsic cornerhood on a section is equivalent to cornerhood after the
inverse deck action on its paired section. -/
theorem mem_dirichletSectionCorners_iff_inv_smul
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ)
    (γ : X.deckGroup) (z : ℍ) :
    z ∈ X.dirichletSectionCorners o γ ↔
      γ⁻¹ • z ∈ X.dirichletSectionCorners o γ⁻¹ := by
  constructor
  · exact X.inv_smul_mem_dirichletSectionCorners o γ
  · intro hz
    have h := X.inv_smul_mem_dirichletSectionCorners o γ⁻¹ hz
    simpa only [inv_inv, smul_inv_smul] using h

/-- Inverse deck action pairs the full intrinsic corner sets exactly. -/
theorem image_inv_smul_dirichletSectionCorners
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ)
    (γ : X.deckGroup) :
    (fun z : ℍ => γ⁻¹ • z) '' X.dirichletSectionCorners o γ =
      X.dirichletSectionCorners o γ⁻¹ := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact X.inv_smul_mem_dirichletSectionCorners o γ hw
  · intro hz
    refine ⟨γ • z, ?_, inv_smul_smul γ z⟩
    simpa only [inv_inv] using
      X.inv_smul_mem_dirichletSectionCorners o γ⁻¹ hz

/-- A nonidentity section has only finitely many genuine two-label corners.
Compactness bounds all labels active at a corner, and distinct bisectors
with the same first focus meet at most once. -/
theorem dirichletSectionCorners_finite
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ)
    (γ : X.deckGroup) (hγ : γ ≠ 1) :
    (X.dirichletSectionCorners o γ).Finite := by
  obtain ⟨K, hK, hcover⟩ := X.exists_compact_covering
  have hcompact := X.isCompact_dirichletDomain_of_compact_covering o K hK hcover
  obtain ⟨R, hbound⟩ :=
    (Metric.isBounded_iff_subset_closedBall o).mp hcompact.isBounded
  let F := deckElementsDistLE X o (2 * R)
  let J := {δ : X.deckGroup // δ ∈ F ∧ δ ≠ 1 ∧ δ ≠ γ}
  have hJ : ({δ : X.deckGroup | δ ∈ F ∧ δ ≠ 1 ∧ δ ≠ γ} : Set X.deckGroup).Finite := by
    apply F.finite_toSet.subset
    intro δ hδ
    exact hδ.1
  letI : Finite J := hJ.to_subtype
  have hγfocus : o ≠ γ • o := by
    intro h
    exact hγ (X.free γ o h.symm)
  have hfinite :
      (⋃ δ : J,
        ({z : ℍ | dist z o = dist z (γ • o)} ∩
          {z : ℍ | dist z o = dist z (δ.1 • o)})).Finite := by
    apply Set.finite_iUnion
    intro δ
    have hδfocus : o ≠ δ.1 • o := by
      intro h
      exact δ.2.2.1 (X.free δ.1 o h.symm)
    have hfocus_ne : γ • o ≠ δ.1 • o := by
      intro h
      have hfix : (γ⁻¹ * δ.1) • o = o := by
        calc
          (γ⁻¹ * δ.1) • o = γ⁻¹ • (δ.1 • o) := mul_smul _ _ _
          _ = γ⁻¹ • (γ • o) := congrArg (fun z => γ⁻¹ • z) h.symm
          _ = o := inv_smul_smul _ _
      have hlabels : γ = δ.1 := inv_mul_eq_one.mp (X.free _ o hfix)
      exact δ.2.2.2 hlabels.symm
    exact (hyperbolic_bisectors_inter_subsingleton
      hγfocus hδfocus hfocus_ne).finite
  apply hfinite.subset
  intro z hz
  obtain ⟨hzD, hzγ, δ, hδone, hδγ, hzδ⟩ := hz
  have hzR : dist z o ≤ R := Metric.mem_closedBall.mp (hbound hzD)
  have hdisplacement : dist o (δ • o) ≤ 2 * R := by
    calc
      dist o (δ • o) ≤ dist o z + dist z (δ • o) := dist_triangle _ _ _
      _ = dist z o + dist z o := by rw [dist_comm o z, ← hzδ]
      _ ≤ R + R := add_le_add hzR hzR
      _ = 2 * R := by ring
  have hδF : δ ∈ F :=
    (mem_deckElementsDistLE X o (2 * R) δ).mpr hdisplacement
  exact Set.mem_iUnion.mpr ⟨⟨δ, hδF, hδone, hδγ⟩, ⟨hzγ, hzδ⟩⟩

#print axioms inv_smul_mem_dirichletSectionCorners
#print axioms mem_dirichletSectionCorners_iff_inv_smul
#print axioms image_inv_smul_dirichletSectionCorners
#print axioms dirichletSectionCorners_finite

end ClosedHyperbolicSurface

namespace DirichletBoundarySegments

/-- Only finitely many unit-interval parameters on a nondegenerate actual
section are genuine two-label corners. -/
theorem intrinsic_corner_parameter_set_finite
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B) :
    {t : ℝ | t ∈ Set.Icc 0 1 ∧
      Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈
          X.dirichletSectionCorners o i.1.1}.Finite := by
  let a := (B.endpoints i.1).1
  let b := (B.endpoints i.1).2
  have hdne : dist a b ≠ 0 := (dist_pos.mpr i.2).ne'
  apply ((X.dirichletSectionCorners_finite o i.1.1
    (Finset.ne_of_mem_erase i.1.2.1)).image
      (fun z : ℍ => dist a z / dist a b)).subset
  intro t ht
  refine ⟨Vendored.RiemannDynamics.geodInterp a b t, ht.2, ?_⟩
  change dist a (Vendored.RiemannDynamics.geodInterp a b t) / dist a b = t
  rw [Vendored.RiemannDynamics.dist_geodInterp_left a b ht.1]
  exact mul_div_cancel_right₀ _ hdne

/-- Endpoint-inclusive cuts at all genuine two-label corners of one actual
section. Unlike candidate `exceptionalPoints`, this is defined from the full
deck group and is therefore compatible with inverse side pairing. -/
noncomputable def intrinsicCornerCuts
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B) : Finset ℝ :=
  insert 0 (insert 1 (B.intrinsic_corner_parameter_set_finite i).toFinset)

/-- Exact membership characterization for the genuine corner cuts. -/
theorem mem_intrinsicCornerCuts_iff
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    (t : ℝ) :
    t ∈ B.intrinsicCornerCuts i ↔ t = 0 ∨ t = 1 ∨
      (t ∈ Set.Icc 0 1 ∧
        Vendored.RiemannDynamics.geodInterp
          (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈
            X.dirichletSectionCorners o i.1.1) := by
  simp only [intrinsicCornerCuts, Finset.mem_insert, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq]

/-- Every genuine corner cut is in the closed unit parameter interval. -/
theorem intrinsicCornerCuts_subset_Icc
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    {t : ℝ} (ht : t ∈ B.intrinsicCornerCuts i) :
    t ∈ Set.Icc (0 : ℝ) 1 := by
  rcases (B.mem_intrinsicCornerCuts_iff i t).mp ht with h0 | h1 | h
  · simp [h0]
  · simp [h1]
  · exact h.1

#print axioms intrinsic_corner_parameter_set_finite
#print axioms intrinsicCornerCuts
#print axioms mem_intrinsicCornerCuts_iff

/-- On a nondegenerate actual section, inverse side pairing preserves the
intrinsic corner condition at each parameter, either at the same parameter
or at its reversal. No orientation of the chosen endpoints is assumed. -/
theorem inverse_section_corner_parameters_eq_or_reverse
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈
          X.dirichletSectionCorners o i.1.1 ↔
      Vendored.RiemannDynamics.geodInterp
        (B.endpoints (B.inverseIndex i.1)).1
        (B.endpoints (B.inverseIndex i.1)).2 t ∈
          X.dirichletSectionCorners o i.1.1⁻¹) ∨
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈
          X.dirichletSectionCorners o i.1.1 ↔
      Vendored.RiemannDynamics.geodInterp
        (B.endpoints (B.inverseIndex i.1)).1
        (B.endpoints (B.inverseIndex i.1)).2 (1 - t) ∈
          X.dirichletSectionCorners o i.1.1⁻¹) := by
  have hcorner (z : ℍ) :
      z ∈ X.dirichletSectionCorners o i.1.1 ↔
        i.1.1⁻¹ • z ∈ X.dirichletSectionCorners o i.1.1⁻¹ := by
    constructor
    · exact X.inv_smul_mem_dirichletSectionCorners o i.1.1
    · intro hz
      have h := X.inv_smul_mem_dirichletSectionCorners o i.1.1⁻¹ hz
      simpa only [inv_inv, smul_inv_smul] using h
  rcases B.inverse_section_geodInterp_eq_or_reverse i with hsame | hreverse
  · left
    intro t ht
    rw [← hsame t ht]
    exact hcorner _
  · right
    intro t ht
    rw [← hreverse t ht]
    exact hcorner _

/-- The finite genuine-corner cuts of paired sections agree in the chosen
parameter or after reflection `t ↦ 1-t`. This is a cut-set statement, not a
cyclic boundary ordering. -/
theorem inverse_intrinsicCornerCuts_eq_or_reverse
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      t ∈ B.intrinsicCornerCuts i ↔
        t ∈ B.intrinsicCornerCuts (B.inverseNondegenerateIndex i)) ∨
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      t ∈ B.intrinsicCornerCuts i ↔
        1 - t ∈ B.intrinsicCornerCuts (B.inverseNondegenerateIndex i)) := by
  rcases B.inverse_section_corner_parameters_eq_or_reverse i with hsame | hreverse
  · left
    intro t ht
    rw [B.mem_intrinsicCornerCuts_iff i t,
      B.mem_intrinsicCornerCuts_iff (B.inverseNondegenerateIndex i) t]
    change (t = 0 ∨ t = 1 ∨ (t ∈ Set.Icc 0 1 ∧
      Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈
          X.dirichletSectionCorners o i.1.1)) ↔
      (t = 0 ∨ t = 1 ∨ (t ∈ Set.Icc 0 1 ∧
        Vendored.RiemannDynamics.geodInterp
          (B.endpoints (B.inverseIndex i.1)).1
          (B.endpoints (B.inverseIndex i.1)).2 t ∈
            X.dirichletSectionCorners o i.1.1⁻¹))
    rw [hsame t ht]
  · right
    intro t ht
    have ht' : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> dsimp at * <;> linarith [ht.1, ht.2]
    rw [B.mem_intrinsicCornerCuts_iff i t,
      B.mem_intrinsicCornerCuts_iff (B.inverseNondegenerateIndex i) (1 - t)]
    change (t = 0 ∨ t = 1 ∨ (t ∈ Set.Icc 0 1 ∧
      Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈
          X.dirichletSectionCorners o i.1.1)) ↔
      (1 - t = 0 ∨ 1 - t = 1 ∨ (1 - t ∈ Set.Icc 0 1 ∧
        Vendored.RiemannDynamics.geodInterp
          (B.endpoints (B.inverseIndex i.1)).1
          (B.endpoints (B.inverseIndex i.1)).2 (1 - t) ∈
            X.dirichletSectionCorners o i.1.1⁻¹))
    constructor
    · rintro (h0 | h1 | hcorner)
      · exact Or.inr (Or.inl (by rw [h0]; ring))
      · exact Or.inl (by rw [h1]; ring)
      · exact Or.inr (Or.inr ⟨ht', (hreverse t ht).mp hcorner.2⟩)
    · rintro (h0 | h1 | hcorner)
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inr ⟨ht, (hreverse t ht).mpr hcorner.2⟩)

/-- A point shared by two differently labeled sections is a genuine corner
of either one, independently of the finite boundary-label cutoff. -/
theorem mem_dirichletSectionCorners_of_two_sections
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o z : ℍ}
    (B : DirichletBoundarySegments X o)
    (i j : DirichletBoundarySegmentIndex X o B.radius) (hij : i ≠ j)
    (hzi : z ∈ Vendored.RiemannDynamics.geodSeg
      (B.endpoints i).1 (B.endpoints i).2)
    (hzj : z ∈ Vendored.RiemannDynamics.geodSeg
      (B.endpoints j).1 (B.endpoints j).2) :
    z ∈ X.dirichletSectionCorners o i.1 := by
  have hi : z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
      {w : ℍ | dist w o = dist w (i.1 • o)} := by
    rw [B.section_eq_segment i]
    exact hzi
  have hj : z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
      {w : ℍ | dist w o = dist w (j.1 • o)} := by
    rw [B.section_eq_segment j]
    exact hzj
  refine ⟨hi.1, hi.2, j.1, Finset.ne_of_mem_erase j.2.1, ?_, hj.2⟩
  intro h
  exact hij (Subtype.ext h.symm)

/-- On a nondegenerate candidate section, every old finite-family
exceptional point is either one of this section's endpoints or a genuine
two-label corner. Thus the new compatible cuts refine the old cuts. -/
theorem exceptional_on_section_endpoint_or_corner
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o z : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    (hzi : z ∈ Vendored.RiemannDynamics.geodSeg
      (B.endpoints i.1).1 (B.endpoints i.1).2)
    (hzex : z ∈ B.exceptionalPoints) :
    z = (B.endpoints i.1).1 ∨ z = (B.endpoints i.1).2 ∨
      z ∈ X.dirichletSectionCorners o i.1.1 := by
  rcases hzex with hend | hdeg | hinter
  · obtain ⟨j, hzj⟩ := hend
    by_cases hji : j = i.1
    · subst j
      exact hzj.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))
    · right; right
      apply B.mem_dirichletSectionCorners_of_two_sections i.1 j (Ne.symm hji) hzi
      rcases hzj with h | h
      · rw [h]
        exact Vendored.RiemannDynamics.left_mem_geodSeg _ _
      · rw [h]
        exact Vendored.RiemannDynamics.right_mem_geodSeg _ _
  · obtain ⟨j, hjdeg, hzj⟩ := hdeg
    have hji : j ≠ i.1 := by
      intro h
      subst j
      exact i.2 hjdeg
    exact Or.inr (Or.inr
      (B.mem_dirichletSectionCorners_of_two_sections i.1 j (Ne.symm hji) hzi hzj))
  · obtain ⟨j, k, hjk, hzj, hzk⟩ := hinter
    by_cases hji : j = i.1
    · subst j
      exact Or.inr (Or.inr
        (B.mem_dirichletSectionCorners_of_two_sections i.1 k hjk hzi hzk))
    · exact Or.inr (Or.inr
        (B.mem_dirichletSectionCorners_of_two_sections i.1 j (Ne.symm hji) hzi hzj))

/-- Every endpoint-and-candidate-exceptional cut used by the regular-frontier
subdivision is retained by the intrinsic, pairing-compatible corner cuts. -/
theorem old_cuts_subset_intrinsicCornerCuts
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    (cuts : Finset ℝ)
    (hcuts : ∀ t : ℝ, t ∈ cuts ↔ t = 0 ∨ t = 1 ∨
      (t ∈ Set.Icc 0 1 ∧ Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints)) :
    cuts ⊆ B.intrinsicCornerCuts i := by
  intro t ht
  apply (B.mem_intrinsicCornerCuts_iff i t).mpr
  rcases (hcuts t).mp ht with h0 | h1 | ⟨htIcc, htex⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · have hseg := Vendored.RiemannDynamics.geodInterp_mem_geodSeg
      (B.endpoints i.1).1 (B.endpoints i.1).2 htIcc
    rcases B.exceptional_on_section_endpoint_or_corner i hseg htex with hleft | hright | hcorner
    · left
      have h0 := geodInterp_injective_of_ne _ _ i.2
        (hleft.trans (Vendored.RiemannDynamics.geodInterp_zero _ _).symm)
      exact h0
    · right; left
      have h1 := geodInterp_injective_of_ne _ _ i.2
        (hright.trans (Vendored.RiemannDynamics.geodInterp_one _ _).symm)
      exact h1
    · exact Or.inr (Or.inr ⟨htIcc, hcorner⟩)

/-- The intrinsic pairing-compatible subdivision is a genuine refinement of
the earlier regular-frontier subdivision: no interior point of one of its
gaps is an old candidate exceptional point. -/
theorem intrinsicCornerGap_interior_not_exceptional
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    (e : DirichletParameterGap (B.intrinsicCornerCuts i))
    {u : ℝ} (hu : u ∈ Set.Ioo (e.left : ℝ) (e.right : ℝ)) :
    Vendored.RiemannDynamics.geodInterp
      (B.endpoints i.1).1 (B.endpoints i.1).2 u ∉ B.exceptionalPoints := by
  have hl := B.intrinsicCornerCuts_subset_Icc i e.left.2
  have hr := B.intrinsicCornerCuts_subset_Icc i e.right.2
  have huIcc : u ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_trans hl.1 hu.1.le, le_trans hu.2.le hr.2⟩
  intro hux
  obtain ⟨cuts, hcuts⟩ := B.exists_finite_parameter_cuts i
  have huold : u ∈ cuts := (hcuts u).mpr (Or.inr (Or.inr ⟨huIcc, hux⟩))
  have hunew : u ∈ B.intrinsicCornerCuts i :=
    B.old_cuts_subset_intrinsicCornerCuts i cuts hcuts huold
  rcases e.adjacent u hunew with hleft | hright
  · exact (not_le_of_gt hu.1 hleft).elim
  · exact (not_le_of_gt hu.2 hright).elim

private theorem intrinsicCornerCuts_same_of_interp_same
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    (hparam : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      i.1.1⁻¹ • Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t =
      Vendored.RiemannDynamics.geodInterp
        (B.endpoints (B.inverseIndex i.1)).1
        (B.endpoints (B.inverseIndex i.1)).2 t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      t ∈ B.intrinsicCornerCuts i ↔
        t ∈ B.intrinsicCornerCuts (B.inverseNondegenerateIndex i) := by
  intro t ht
  have hc := X.mem_dirichletSectionCorners_iff_inv_smul o i.1.1
    (Vendored.RiemannDynamics.geodInterp
      (B.endpoints i.1).1 (B.endpoints i.1).2 t)
  rw [hparam t ht] at hc
  rw [B.mem_intrinsicCornerCuts_iff i t,
    B.mem_intrinsicCornerCuts_iff (B.inverseNondegenerateIndex i) t]
  change (t = 0 ∨ t = 1 ∨ (t ∈ Set.Icc 0 1 ∧
    Vendored.RiemannDynamics.geodInterp
      (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈
        X.dirichletSectionCorners o i.1.1)) ↔
    (t = 0 ∨ t = 1 ∨ (t ∈ Set.Icc 0 1 ∧
      Vendored.RiemannDynamics.geodInterp
        (B.endpoints (B.inverseIndex i.1)).1
        (B.endpoints (B.inverseIndex i.1)).2 t ∈
          X.dirichletSectionCorners o i.1.1⁻¹))
  rw [hc]

private theorem intrinsicCornerCuts_reverse_of_interp_reverse
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    (hparam : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      i.1.1⁻¹ • Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t =
      Vendored.RiemannDynamics.geodInterp
        (B.endpoints (B.inverseIndex i.1)).1
        (B.endpoints (B.inverseIndex i.1)).2 (1 - t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      t ∈ B.intrinsicCornerCuts i ↔
        1 - t ∈ B.intrinsicCornerCuts (B.inverseNondegenerateIndex i) := by
  intro t ht
  have ht' : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hc := X.mem_dirichletSectionCorners_iff_inv_smul o i.1.1
    (Vendored.RiemannDynamics.geodInterp
      (B.endpoints i.1).1 (B.endpoints i.1).2 t)
  rw [hparam t ht] at hc
  rw [B.mem_intrinsicCornerCuts_iff i t,
    B.mem_intrinsicCornerCuts_iff (B.inverseNondegenerateIndex i) (1 - t)]
  change (t = 0 ∨ t = 1 ∨ (t ∈ Set.Icc 0 1 ∧
    Vendored.RiemannDynamics.geodInterp
      (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈
        X.dirichletSectionCorners o i.1.1)) ↔
    (1 - t = 0 ∨ 1 - t = 1 ∨ (1 - t ∈ Set.Icc 0 1 ∧
      Vendored.RiemannDynamics.geodInterp
        (B.endpoints (B.inverseIndex i.1)).1
        (B.endpoints (B.inverseIndex i.1)).2 (1 - t) ∈
          X.dirichletSectionCorners o i.1.1⁻¹))
  constructor
  · rintro (h0 | h1 | hcorner)
    · exact Or.inr (Or.inl (by rw [h0]; ring))
    · exact Or.inl (by rw [h1]; ring)
    · exact Or.inr (Or.inr ⟨ht', hc.mp hcorner.2⟩)
  · rintro (h0 | h1 | hcorner)
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inr ⟨ht, hc.mpr hcorner.2⟩)

private theorem transport_gap_same
    (A C : Finset ℝ)
    (hA : ∀ t ∈ A, t ∈ Set.Icc (0 : ℝ) 1)
    (hC : ∀ t ∈ C, t ∈ Set.Icc (0 : ℝ) 1)
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ A ↔ t ∈ C)
    (e : DirichletParameterGap A) :
    ∃ f : DirichletParameterGap C,
      (f.left : ℝ) = (e.left : ℝ) ∧
        (f.right : ℝ) = (e.right : ℝ) := by
  let f : DirichletParameterGap C :=
    ⟨⟨e.left.1, (hmem e.left.1 (hA e.left.1 e.left.2)).mp e.left.2⟩,
      ⟨e.right.1, (hmem e.right.1 (hA e.right.1 e.right.2)).mp e.right.2⟩,
      e.left_lt_right,
      by
        intro c hc
        exact e.adjacent c ((hmem c (hC c hc)).mpr hc)⟩
  exact ⟨f, rfl, rfl⟩

private theorem transport_gap_reverse
    (A C : Finset ℝ)
    (hA : ∀ t ∈ A, t ∈ Set.Icc (0 : ℝ) 1)
    (hC : ∀ t ∈ C, t ∈ Set.Icc (0 : ℝ) 1)
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ A ↔ 1 - t ∈ C)
    (e : DirichletParameterGap A) :
    ∃ f : DirichletParameterGap C,
      (f.left : ℝ) = 1 - (e.right : ℝ) ∧
        (f.right : ℝ) = 1 - (e.left : ℝ) := by
  let f : DirichletParameterGap C :=
    ⟨⟨1 - e.right.1,
        (hmem e.right.1 (hA e.right.1 e.right.2)).mp e.right.2⟩,
      ⟨1 - e.left.1,
        (hmem e.left.1 (hA e.left.1 e.left.2)).mp e.left.2⟩,
      by dsimp; linarith [e.left_lt_right],
      by
        intro c hc
        have hcIcc := hC c hc
        have hreflect : 1 - c ∈ Set.Icc (0 : ℝ) 1 := by
          constructor <;> linarith [hcIcc.1, hcIcc.2]
        have hcut : 1 - c ∈ A :=
          (hmem (1 - c) hreflect).mpr (by simpa using hc)
        rcases e.adjacent (1 - c) hcut with hlow | hhigh
        · right
          dsimp
          linarith
        · left
          dsimp
          linarith⟩
  exact ⟨f, rfl, rfl⟩

/-- Inverse deck action maps the open geodesic image of each genuine-corner
gap exactly onto an open gap image of the paired section. The selected target
gap follows the same parameter orientation as the actual endpoint pairing;
no arbitrary finite candidate cut family is assumed invariant. -/
theorem exists_inverse_intrinsicCornerGap_image
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    (e : DirichletParameterGap (B.intrinsicCornerCuts i)) :
    ∃ f : DirichletParameterGap
        (B.intrinsicCornerCuts (B.inverseNondegenerateIndex i)),
      (fun z : ℍ => i.1.1⁻¹ • z) ''
          ((fun u : ℝ => Vendored.RiemannDynamics.geodInterp
            (B.endpoints i.1).1 (B.endpoints i.1).2 u) ''
              Set.Ioo (e.left : ℝ) (e.right : ℝ)) =
        (fun v : ℝ => Vendored.RiemannDynamics.geodInterp
          (B.endpoints (B.inverseIndex i.1)).1
          (B.endpoints (B.inverseIndex i.1)).2 v) ''
            Set.Ioo (f.left : ℝ) (f.right : ℝ) ∧
      (((f.left : ℝ) = (e.left : ℝ) ∧
          (f.right : ℝ) = (e.right : ℝ)) ∨
        ((f.left : ℝ) = 1 - (e.right : ℝ) ∧
          (f.right : ℝ) = 1 - (e.left : ℝ))) := by
  have hA : ∀ t ∈ B.intrinsicCornerCuts i, t ∈ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    exact B.intrinsicCornerCuts_subset_Icc i ht
  have hC : ∀ t ∈ B.intrinsicCornerCuts (B.inverseNondegenerateIndex i),
      t ∈ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    exact B.intrinsicCornerCuts_subset_Icc _ ht
  have hgapIcc (u : ℝ) (hu : u ∈ Set.Ioo (e.left : ℝ) (e.right : ℝ)) :
      u ∈ Set.Icc (0 : ℝ) 1 := by
    have hl := hA e.left.1 e.left.2
    have hr := hA e.right.1 e.right.2
    exact ⟨le_trans hl.1 hu.1.le, le_trans hu.2.le hr.2⟩
  rcases B.inverse_section_geodInterp_eq_or_reverse i with hparam | hparam
  · have hmem := B.intrinsicCornerCuts_same_of_interp_same i hparam
    obtain ⟨f, hl, hr⟩ := transport_gap_same _ _ hA hC hmem e
    refine ⟨f, ?_, Or.inl ⟨hl, hr⟩⟩
    ext z
    constructor
    · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
      have hu' : u ∈ Set.Ioo (f.left : ℝ) (f.right : ℝ) := by
        rw [hl, hr]
        exact hu
      exact ⟨u, hu', (hparam u (hgapIcc u hu)).symm⟩
    · rintro ⟨u, hu, rfl⟩
      have hu' : u ∈ Set.Ioo (e.left : ℝ) (e.right : ℝ) := by
        rw [← hl, ← hr]
        exact hu
      exact ⟨_, ⟨u, hu', rfl⟩, hparam u (hgapIcc u hu')⟩
  · have hmem := B.intrinsicCornerCuts_reverse_of_interp_reverse i hparam
    obtain ⟨f, hl, hr⟩ := transport_gap_reverse _ _ hA hC hmem e
    refine ⟨f, ?_, Or.inr ⟨hl, hr⟩⟩
    ext z
    constructor
    · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
      have hu' : 1 - u ∈ Set.Ioo (f.left : ℝ) (f.right : ℝ) := by
        rw [hl, hr]
        constructor <;> dsimp at * <;> linarith [hu.1, hu.2]
      exact ⟨1 - u, hu', (hparam u (hgapIcc u hu)).symm⟩
    · rintro ⟨v, hv, rfl⟩
      have hu : 1 - v ∈ Set.Ioo (e.left : ℝ) (e.right : ℝ) := by
        rw [hl, hr] at hv
        constructor <;> dsimp at * <;> linarith [hv.1, hv.2]
      refine ⟨_, ⟨1 - v, hu, rfl⟩, ?_⟩
      have h := hparam (1 - v) (hgapIcc (1 - v) hu)
      have hsub : (1 : ℝ) - (1 - v) = v := by ring
      rw [hsub] at h
      exact h

#print axioms inverse_section_corner_parameters_eq_or_reverse
#print axioms inverse_intrinsicCornerCuts_eq_or_reverse
#print axioms mem_dirichletSectionCorners_of_two_sections
#print axioms exceptional_on_section_endpoint_or_corner
#print axioms old_cuts_subset_intrinsicCornerCuts
#print axioms intrinsicCornerGap_interior_not_exceptional
#print axioms exists_inverse_intrinsicCornerGap_image

end DirichletBoundarySegments
end SystolicGrowth
