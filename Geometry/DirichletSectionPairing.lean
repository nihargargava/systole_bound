module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletBoundaryIntersections

@[expose] public section

/-!
# Inverse-deck pairing of actual Dirichlet sections

The section labeled by `γ` maps to the section labeled by `γ⁻¹` under
`γ⁻¹`. These are the actual bisector sections, not an assumed polygon.
Endpoints of paired nondegenerate sections agree up to a swap. No cyclic
order, selected endpoint orientation or vertex-angle tiling is asserted.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth

/-- Two nondegenerate geodesic segments coincide exactly when their endpoint
pairs agree in either order. The chosen orientation is not assumed. -/
theorem geodSeg_eq_iff_endpoints_eq_or_swap
    {a b c d : ℍ} (hab : a ≠ b) (hcd : c ≠ d) :
    Vendored.RiemannDynamics.geodSeg a b = Vendored.RiemannDynamics.geodSeg c d ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro hseg
    have ha := Vendored.RiemannDynamics.isSegEndpoint_left hab
    have hb : Vendored.RiemannDynamics.IsSegEndpoint
        (Vendored.RiemannDynamics.geodSeg a b) b :=
      (Vendored.RiemannDynamics.isSegEndpoint_geodSeg_iff hab).mpr (Or.inr rfl)
    rw [hseg] at ha hb
    have ha' := (Vendored.RiemannDynamics.isSegEndpoint_geodSeg_iff hcd).mp ha
    have hb' := (Vendored.RiemannDynamics.isSegEndpoint_geodSeg_iff hcd).mp hb
    rcases ha' with hac | had <;> rcases hb' with hbc | hbd
    · exact (hab (hac.trans hbc.symm)).elim
    · exact Or.inl ⟨hac, hbd⟩
    · exact Or.inr ⟨had, hbc⟩
    · exact (hab (had.trans hbd.symm)).elim
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Vendored.RiemannDynamics.geodSeg_comm _ _

/-- Geodesic interpolation on the unit interval commutes with the actual
isometric special-linear action. -/
theorem smul_geodInterp_of_mem_Icc
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (a b : ℍ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    γ • Vendored.RiemannDynamics.geodInterp a b t =
      Vendored.RiemannDynamics.geodInterp (γ • a) (γ • b) t := by
  have hz : γ • Vendored.RiemannDynamics.geodInterp a b t ∈
      Vendored.RiemannDynamics.geodSeg (γ • a) (γ • b) := by
    rw [← Vendored.RiemannDynamics.smul_geodSeg]
    exact ⟨_, Vendored.RiemannDynamics.geodInterp_mem_geodSeg a b ht, rfl⟩
  have hw := Vendored.RiemannDynamics.geodInterp_mem_geodSeg (γ • a) (γ • b) ht
  apply Vendored.RiemannDynamics.eq_on_geodSeg_of_dist_eq hz hw
  rw [dist_smul, Vendored.RiemannDynamics.dist_geodInterp_left a b ht,
    Vendored.RiemannDynamics.dist_geodInterp_left (γ • a) (γ • b) ht, dist_smul]

/-- Reversing the endpoints of a geodesic segment reverses its unit parameter. -/
theorem geodInterp_reverse_of_mem_Icc
    (a b : ℍ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Vendored.RiemannDynamics.geodInterp b a t =
      Vendored.RiemannDynamics.geodInterp a b (1 - t) := by
  have ht' : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  have hz := Vendored.RiemannDynamics.geodInterp_mem_geodSeg b a ht
  have hw : Vendored.RiemannDynamics.geodInterp a b (1 - t) ∈
      Vendored.RiemannDynamics.geodSeg b a := by
    rw [Vendored.RiemannDynamics.geodSeg_comm]
    exact Vendored.RiemannDynamics.geodInterp_mem_geodSeg a b ht'
  apply Vendored.RiemannDynamics.eq_on_geodSeg_of_dist_eq hz hw
  rw [Vendored.RiemannDynamics.dist_geodInterp_left b a ht,
    dist_comm b (Vendored.RiemannDynamics.geodInterp a b (1 - t)),
    Vendored.RiemannDynamics.dist_geodInterp_right_abs,
    show 1 - (1 - t) = t by ring, abs_of_nonneg ht.1, dist_comm b a]

namespace ClosedHyperbolicSurface

/-- A nonidentity deck transformation cannot equal its inverse: an involutive
isometry would fix the midpoint between a point and its image, violating
the free deck action. -/
theorem inv_ne_self_of_ne_one
    {g : ℕ} (X : ClosedHyperbolicSurface g) (γ : X.deckGroup) (hγ : γ ≠ 1) :
    γ⁻¹ ≠ γ := by
  intro hinv
  let o : ℍ := I
  let z : ℍ := Vendored.RiemannDynamics.geodInterp o (γ • o) (1 / 2)
  have hz : z ∈ Vendored.RiemannDynamics.geodSeg o (γ • o) :=
    Vendored.RiemannDynamics.geodInterp_mem_geodSeg o (γ • o) (by norm_num)
  have hsq : γ • γ • o = o := by
    simpa only [hinv] using inv_smul_smul γ o
  have hdL : dist o z = (1 / 2 : ℝ) * dist o (γ • o) :=
    Vendored.RiemannDynamics.dist_geodInterp_left o (γ • o) (by norm_num)
  have hdR : dist z (γ • o) = (1 / 2 : ℝ) * dist o (γ • o) := by
    dsimp [z]
    rw [Vendored.RiemannDynamics.dist_geodInterp_right_abs]
    norm_num
  have hγL : dist o (γ • z) = dist z (γ • o) := by
    calc
      _ = dist (γ • γ • o) (γ • z) := by rw [hsq]
      _ = dist (γ • o) z := dist_smul γ _ _
      _ = _ := dist_comm _ _
  have hγR : dist (γ • z) (γ • o) = dist o z := by
    rw [dist_smul, dist_comm]
  have hγz : γ • z ∈ Vendored.RiemannDynamics.geodSeg o (γ • o) := by
    rw [Vendored.RiemannDynamics.mem_geodSeg, hγL, hγR, hdL, hdR]
    ring
  have hfix : γ • z = z :=
    Vendored.RiemannDynamics.eq_on_geodSeg_of_dist_eq hγz hz (by rw [hγL, hdL, hdR])
  exact hγ (X.free γ z hfix)

/-- A point on the `γ` bisector section moves into the inverse section. -/
theorem inv_smul_mem_dirichlet_bisector_section
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (γ : X.deckGroup)
    {z : ℍ}
    (hz : z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
      {w : ℍ | dist w o = dist w (γ • o)}) :
    γ⁻¹ • z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
      {w : ℍ | dist w o = dist w (γ⁻¹ • o)} := by
  have hleft : dist (γ⁻¹ • z) o = dist z (γ • o) := by
    rw [← dist_smul γ (γ⁻¹ • z) o, smul_inv_smul]
  have hright : dist (γ⁻¹ • z) (γ⁻¹ • o) = dist z o := dist_smul _ _ _
  refine ⟨?_, ?_⟩
  · apply Vendored.RiemannDynamics.mem_dirichletDomain.mpr
    intro δ
    have hδ : dist (γ⁻¹ • z) (δ • o) = dist z ((γ * δ) • o) := by
      rw [← dist_smul γ (γ⁻¹ • z) (δ • o), smul_inv_smul, mul_smul]
    rw [hleft, ← hz.2, hδ]
    exact (Vendored.RiemannDynamics.mem_dirichletDomain.mp hz.1) (γ * δ)
  · exact hleft.trans (hz.2.symm.trans hright.symm)

/-- Inverse deck action pairs whole nonempty bisector sections exactly. -/
theorem image_inv_smul_dirichlet_bisector_section
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (γ : X.deckGroup) :
    (fun z : ℍ => γ⁻¹ • z) ''
        (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
          {z : ℍ | dist z o = dist z (γ • o)}) =
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
        {z : ℍ | dist z o = dist z (γ⁻¹ • o)} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact X.inv_smul_mem_dirichlet_bisector_section o γ hw
  · intro hz
    refine ⟨γ • z, ?_, inv_smul_smul γ z⟩
    simpa only [inv_inv] using X.inv_smul_mem_dirichlet_bisector_section o γ⁻¹ hz

end ClosedHyperbolicSurface

namespace DirichletBoundarySegments

/-- Inverting a finite section label preserves its displacement and nonempty
section; hence it defines another index in the same actual finite family. -/
noncomputable def inverseIndex
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : DirichletBoundarySegmentIndex X o B.radius) :
    DirichletBoundarySegmentIndex X o B.radius := by
  refine ⟨i.1⁻¹, ?_, ?_⟩
  · apply Finset.mem_erase.mpr
    refine ⟨inv_ne_one.mpr (Finset.ne_of_mem_erase i.2.1), ?_⟩
    apply (mem_deckElementsDistLE X o (2 * B.radius) i.1⁻¹).mpr
    have hi := (mem_deckElementsDistLE X o (2 * B.radius) i.1).mp
      (Finset.mem_of_mem_erase i.2.1)
    have heq : dist o (i.1⁻¹ • o) = dist o (i.1 • o) := by
      rw [← dist_smul i.1 o (i.1⁻¹ • o), smul_inv_smul, dist_comm]
    exact heq.trans_le hi
  · obtain ⟨z, hz⟩ := i.2.2
    exact ⟨i.1⁻¹ • z, X.inv_smul_mem_dirichlet_bisector_section o i.1 hz⟩

/-- The underlying deck label of the partner is exactly the inverse. -/
@[simp] theorem inverseIndex_val
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : DirichletBoundarySegmentIndex X o B.radius) :
    (B.inverseIndex i).1 = i.1⁻¹ := rfl

/-- Actual inverse-deck pairing is an involution on the finite section labels. -/
@[simp] theorem inverseIndex_inverseIndex
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : DirichletBoundarySegmentIndex X o B.radius) :
    B.inverseIndex (B.inverseIndex i) = i := by
  apply Subtype.ext
  exact inv_inv i.1

/-- The finite section-pairing involution has no fixed label. -/
theorem inverseIndex_ne_self
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : DirichletBoundarySegmentIndex X o B.radius) :
    B.inverseIndex i ≠ i := by
  intro h
  exact X.inv_ne_self_of_ne_one i.1 (Finset.ne_of_mem_erase i.2.1)
    (congrArg Subtype.val h)

/-- The chosen segment of the inverse label is the exact inverse-deck image
of the original chosen segment, regardless of the chosen endpoint orientation. -/
theorem image_inv_smul_segment_eq
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : DirichletBoundarySegmentIndex X o B.radius) :
    (fun z : ℍ => i.1⁻¹ • z) ''
        Vendored.RiemannDynamics.geodSeg (B.endpoints i).1 (B.endpoints i).2 =
      Vendored.RiemannDynamics.geodSeg
        (B.endpoints (B.inverseIndex i)).1 (B.endpoints (B.inverseIndex i)).2 := by
  rw [← B.section_eq_segment i, ← B.section_eq_segment (B.inverseIndex i)]
  exact X.image_inv_smul_dirichlet_bisector_section o i.1

/-- Inverse-deck transport preserves nondegeneracy of an actual section. -/
theorem inverseIndex_nondegenerate
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B) :
    (B.endpoints (B.inverseIndex i.1)).1 ≠
      (B.endpoints (B.inverseIndex i.1)).2 := by
  intro hdeg
  have hleft : i.1.1⁻¹ • (B.endpoints i.1).1 ∈
      Vendored.RiemannDynamics.geodSeg
        (B.endpoints (B.inverseIndex i.1)).1
        (B.endpoints (B.inverseIndex i.1)).2 := by
    rw [← B.image_inv_smul_segment_eq i.1]
    exact ⟨_, Vendored.RiemannDynamics.left_mem_geodSeg _ _, rfl⟩
  have hright : i.1.1⁻¹ • (B.endpoints i.1).2 ∈
      Vendored.RiemannDynamics.geodSeg
        (B.endpoints (B.inverseIndex i.1)).1
        (B.endpoints (B.inverseIndex i.1)).2 := by
    rw [← B.image_inv_smul_segment_eq i.1]
    exact ⟨_, Vendored.RiemannDynamics.right_mem_geodSeg _ _, rfl⟩
  rw [hdeg, Vendored.RiemannDynamics.geodSeg_self, Set.mem_singleton_iff] at hleft hright
  have heq := congrArg (fun z : ℍ => i.1.1 • z) (hleft.trans hright.symm)
  simp only [smul_inv_smul] at heq
  exact i.2 heq

/-- The inverse deck map sends the two endpoints of a nondegenerate section
to the two chosen endpoints of its paired section, in one of the two orders.
The proof does not choose an orientation or assume endpoint equivariance. -/
theorem inverse_section_endpoints_eq_or_swap
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B) :
    (i.1.1⁻¹ • (B.endpoints i.1).1 = (B.endpoints (B.inverseIndex i.1)).1 ∧
      i.1.1⁻¹ • (B.endpoints i.1).2 = (B.endpoints (B.inverseIndex i.1)).2) ∨
    (i.1.1⁻¹ • (B.endpoints i.1).1 = (B.endpoints (B.inverseIndex i.1)).2 ∧
      i.1.1⁻¹ • (B.endpoints i.1).2 = (B.endpoints (B.inverseIndex i.1)).1) := by
  have hne : i.1.1⁻¹ • (B.endpoints i.1).1 ≠
      i.1.1⁻¹ • (B.endpoints i.1).2 := by
    intro h
    have heq := congrArg (fun z : ℍ => i.1.1 • z) h
    simp only [smul_inv_smul] at heq
    exact i.2 heq
  apply (geodSeg_eq_iff_endpoints_eq_or_swap hne (B.inverseIndex_nondegenerate i)).mp
  calc
    _ = (fun z : ℍ => i.1.1⁻¹ • z) ''
        Vendored.RiemannDynamics.geodSeg (B.endpoints i.1).1 (B.endpoints i.1).2 := by
      exact (Vendored.RiemannDynamics.smul_geodSeg
        ((i.1.1⁻¹ : X.deckGroup) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
        (B.endpoints i.1).1 (B.endpoints i.1).2).symm
    _ = _ := B.image_inv_smul_segment_eq i.1

/-- The inverse deck map carries the whole unit-parameter section into its
chosen partner parametrization, either preserving or reversing the parameter.
Which alternative holds is determined by the actual endpoint transport. -/
theorem inverse_section_geodInterp_eq_or_reverse
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      i.1.1⁻¹ • Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t =
      Vendored.RiemannDynamics.geodInterp
        (B.endpoints (B.inverseIndex i.1)).1 (B.endpoints (B.inverseIndex i.1)).2 t) ∨
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      i.1.1⁻¹ • Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t =
      Vendored.RiemannDynamics.geodInterp
        (B.endpoints (B.inverseIndex i.1)).1 (B.endpoints (B.inverseIndex i.1)).2 (1 - t)) := by
  have hsmul (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      i.1.1⁻¹ • Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t =
      Vendored.RiemannDynamics.geodInterp
        (i.1.1⁻¹ • (B.endpoints i.1).1) (i.1.1⁻¹ • (B.endpoints i.1).2) t := by
    exact smul_geodInterp_of_mem_Icc
      ((i.1.1⁻¹ : X.deckGroup) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (B.endpoints i.1).1 (B.endpoints i.1).2 ht
  rcases B.inverse_section_endpoints_eq_or_swap i with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · left
    intro t ht
    rw [hsmul t ht, hleft, hright]
  · right
    intro t ht
    rw [hsmul t ht, hleft, hright]
    exact geodInterp_reverse_of_mem_Icc _ _ ht

/-- Pairing restricted to the actual nondegenerate section labels. -/
noncomputable def inverseNondegenerateIndex
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B) :
    NondegenerateIndex B :=
  ⟨B.inverseIndex i.1, B.inverseIndex_nondegenerate i⟩

/-- The restricted side-label pairing remains involutive. -/
@[simp] theorem inverseNondegenerateIndex_inverseNondegenerateIndex
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B) :
    B.inverseNondegenerateIndex (B.inverseNondegenerateIndex i) = i := by
  apply Subtype.ext
  exact B.inverseIndex_inverseIndex i.1

/-- No nondegenerate actual section is paired to its own label. -/
theorem inverseNondegenerateIndex_ne_self
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B) :
    B.inverseNondegenerateIndex i ≠ i := by
  intro h
  exact B.inverseIndex_ne_self i.1 (congrArg Subtype.val h)

#print axioms inverseIndex
#print axioms inverseIndex_inverseIndex
#print axioms inverseIndex_ne_self
#print axioms image_inv_smul_segment_eq
#print axioms inverse_section_endpoints_eq_or_swap
#print axioms inverse_section_geodInterp_eq_or_reverse
#print axioms inverseNondegenerateIndex
#print axioms inverseNondegenerateIndex_ne_self

end DirichletBoundarySegments

#print axioms ClosedHyperbolicSurface.image_inv_smul_dirichlet_bisector_section
#print axioms ClosedHyperbolicSurface.inv_ne_self_of_ne_one
#print axioms geodSeg_eq_iff_endpoints_eq_or_swap
#print axioms smul_geodInterp_of_mem_Icc
#print axioms geodInterp_reverse_of_mem_Icc

end SystolicGrowth
