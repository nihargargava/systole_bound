module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletCyclicEnumeration

@[expose] public section

/-!
# Reversal of the actual cyclic side-pairing orientations

Special-linear deck maps rotate disc-chart radial directions. In a mirror
normalization the two Dirichlet centres are exchanged by reflection, and
their common bisector is fixed pointwise. Thus inverse-deck transport on
that side acts on radial positions by a unit rotation followed by inversion.
This reverses the directed circle arc, and rules out equal-order endpoint
transport for the already constructed actual cyclic boundary.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth

/-- The special-linear action transports radial directions by an actual
unit rotation, obtained from the existing disc-chart transformation formula. -/
theorem exists_radialRotation_smul
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (o : ℍ) :
    ∃ η : Circle, ∀ z : ℍ,
      hyperbolicRadialDirection (A • o) (A • z) =
        (η : ℂ) * hyperbolicRadialDirection o z := by
  let d : ℂ := ((A 1 0 : ℝ) : ℂ) * (o : ℂ) + ((A 1 1 : ℝ) : ℂ)
  have hd : d ≠ 0 :=
    Vendored.RiemannDynamics.denom_ne_zero A (by
      rw [UpperHalfPlane.coe_im]
      exact o.im_pos.ne')
  let η := Circle.ofConjDivSelf d hd
  refine ⟨η, ?_⟩
  intro z
  have hchart : Vendored.RiemannDynamics.discChart (A • o) (A • z) =
      (η : ℂ) * Vendored.RiemannDynamics.discChart o z := by
    rw [Vendored.RiemannDynamics.discChart_smul]
    dsimp [η, Circle.ofConjDivSelf, d]
    simp only [map_add, map_mul, Complex.conj_ofReal]
  unfold hyperbolicRadialDirection
  rw [hchart, norm_mul, Circle.norm_coe, one_mul, mul_div_assoc]

/-- Reflection conjugates the actual radial direction. -/
theorem hyperbolicRadialDirection_J (o z : ℍ) :
    hyperbolicRadialDirection (UpperHalfPlane.J • o) (UpperHalfPlane.J • z) =
      (starRingEnd ℂ) (hyperbolicRadialDirection o z) := by
  simp [hyperbolicRadialDirection, Vendored.RiemannDynamics.discChart_J,
    map_div₀]

namespace ClosedHyperbolicSurface

/-- Inverse transport along an actual Dirichlet bisector acts on radial
positions by one unit rotation followed by complex conjugation. The mirror
normalizer is constructed from the two actual, distinct deck centres. -/
theorem exists_inverse_bisector_radial_antirotation
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (γ : X.deckGroup) (hγ : γ ≠ 1) :
    ∃ u : Circle, ∀ z : ℍ, dist z o = dist z (γ • o) →
      hyperbolicRadialDirection o (γ⁻¹ • z) =
        (u : ℂ) * (starRingEnd ℂ) (hyperbolicRadialDirection o z) := by
  have hpq : o ≠ γ • o := fun h => hγ (X.free γ o h.symm)
  obtain ⟨A, him, hre, h0⟩ := Vendored.RiemannDynamics.exists_mirror_normalizer hpq
  obtain ⟨ηp, hηp⟩ := exists_radialRotation_smul A o
  obtain ⟨ηq, hηq⟩ := exists_radialRotation_smul A (γ • o)
  obtain ⟨ηr, hηr⟩ := exists_radialRotation_smul (γ⁻¹ : X.deckGroup).1 (γ • o)
  have hmirror : UpperHalfPlane.J • (A • o) = A • (γ • o) := by
    apply Vendored.RiemannDynamics.ext_re_im
    · rw [Vendored.RiemannDynamics.J_smul_re, hre]
    · rw [Vendored.RiemannDynamics.J_smul_im, him]
  refine ⟨ηr * ηq⁻¹ * ηp⁻¹, ?_⟩
  intro z hz
  have hzaxis := (Vendored.RiemannDynamics.bisector_re_eq_zero him hre h0 z).mp hz
  have hzfix : UpperHalfPlane.J • (A • z) = A • z := by
    apply Vendored.RiemannDynamics.ext_re_im
    · rw [Vendored.RiemannDynamics.J_smul_re, hzaxis, neg_zero]
    · exact Vendored.RiemannDynamics.J_smul_im _
  have hreflect : (ηq : ℂ) * hyperbolicRadialDirection (γ • o) z =
      (starRingEnd ℂ) ((ηp : ℂ) * hyperbolicRadialDirection o z) := by
    rw [← hηq z, ← hmirror, ← hzfix, hyperbolicRadialDirection_J, hηp z]
  have hrq : hyperbolicRadialDirection (γ • o) z =
      (ηq : ℂ)⁻¹ * (starRingEnd ℂ) (ηp : ℂ) *
        (starRingEnd ℂ) (hyperbolicRadialDirection o z) := by
    have h := congrArg (fun w : ℂ => (ηq : ℂ)⁻¹ * w) hreflect
    simpa only [map_mul, ← mul_assoc, inv_mul_cancel₀ ηq.coe_ne_zero, one_mul] using h
  have htransport := hηr z
  change hyperbolicRadialDirection (γ⁻¹ • (γ • o)) (γ⁻¹ • z) = _ at htransport
  rw [inv_smul_smul, hrq] at htransport
  rw [htransport]
  simp only [Circle.coe_mul, Circle.coe_inv, ← Circle.coe_inv_eq_conj]
  ring

end ClosedHyperbolicSurface

#print axioms ClosedHyperbolicSurface.exists_inverse_bisector_radial_antirotation

private theorem circle_angleDiff_antirotation (u a b : Circle) :
    Circle.angleDiff (u * b⁻¹) (u * a⁻¹) = Circle.angleDiff a b := by
  have hexp (x y : Circle) : Circle.exp (Circle.angleDiff x y) = y / x := by
    apply mul_right_cancel (b := x)
    rw [Circle.exp_angleDiff_mul, div_mul_cancel]
  apply Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
    ⟨Circle.angleDiff_nonneg _ _, Circle.angleDiff_lt_two_pi _ _⟩
    ⟨Circle.angleDiff_nonneg _ _, Circle.angleDiff_lt_two_pi _ _⟩
  rw [hexp, hexp]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, inv_inv]
  calc
    u * a⁻¹ * (b * u⁻¹) = (u * u⁻¹) * (b * a⁻¹) := by ac_rfl
    _ = b * a⁻¹ := by simp

private theorem circle_path_eq_exp_angleDiff_mul (a b : Circle) (t : unitInterval) :
    Circle.path a b t = Circle.exp ((t : ℝ) * Circle.angleDiff a b) * a := by
  rw [Circle.path_apply]
  have hline : Path.segment (Complex.arg (a : ℂ))
      (Circle.angleDiff a b + Complex.arg (a : ℂ)) t =
      Complex.arg (a : ℂ) + (t : ℝ) * Circle.angleDiff a b := by
    rw [Path.segment_apply, AffineMap.lineMap_apply_ring]
    ring
  rw [hline, Circle.exp_add, Circle.exp_arg, mul_comm]

private theorem circle_antirotation_path (u a b : Circle) (t : unitInterval) :
    u * (Circle.path a b t)⁻¹ =
      Circle.path (u * b⁻¹) (u * a⁻¹) (unitInterval.symm t) := by
  rw [circle_path_eq_exp_angleDiff_mul, circle_path_eq_exp_angleDiff_mul,
    circle_angleDiff_antirotation, unitInterval.coe_symm_eq]
  let D := Circle.angleDiff a b
  change u * (Circle.exp ((t : ℝ) * D) * a)⁻¹ =
    Circle.exp ((1 - (t : ℝ)) * D) * (u * b⁻¹)
  have hexp : Circle.exp ((1 - (t : ℝ)) * D) =
      Circle.exp (-(t : ℝ) * D) * Circle.exp D := by
    rw [← Circle.exp_add]
    congr 1
    ring
  have hbinv : b⁻¹ = a⁻¹ * (Circle.exp D)⁻¹ := by
    have hb : b = Circle.exp D * a := Circle.exp_angleDiff_mul.symm
    exact congrArg Inv.inv hb |>.trans (mul_inv_rev _ _)
  rw [hexp, show -(t : ℝ) * D = -((t : ℝ) * D) by ring, Circle.exp_neg, hbinv]
  simp [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

/-- A unit rotation followed by inversion reverses the directed open arc
between its actual endpoint images. -/
private theorem image_circle_open_arc_antirotation (u a b : Circle) :
    (fun ξ : Circle => u * ξ⁻¹) '' (Circle.path a b '' Set.Ioo 0 1) =
      Circle.path (u * b⁻¹) (u * a⁻¹) '' Set.Ioo 0 1 := by
  let f : Circle → Circle := fun ξ => u * ξ⁻¹
  have hf (ξ : Circle) : f (f ξ) = ξ := by
    dsimp [f]
    rw [mul_inv_rev, inv_inv]
    calc
      u * (ξ * u⁻¹) = (u * u⁻¹) * ξ := by ac_rfl
      _ = ξ := by simp
  have hmaps (x y : Circle) : Set.MapsTo f (Circle.path x y '' Set.Ioo 0 1)
      (Circle.path (f y) (f x) '' Set.Ioo 0 1) := by
    rintro ξ ⟨t, ht, rfl⟩
    refine ⟨unitInterval.symm t, ⟨?_, ?_⟩, (circle_antirotation_path u x y t).symm⟩
    · change (0 : ℝ) < 1 - (t : ℝ)
      have ht1 : (t : ℝ) < 1 := ht.2
      linarith
    · change 1 - (t : ℝ) < 1
      have ht0 : (0 : ℝ) < t := ht.1
      linarith
  change f '' (Circle.path a b '' Set.Ioo 0 1) =
    Circle.path (f b) (f a) '' Set.Ioo 0 1
  apply Set.Subset.antisymm
  · rintro ξ ⟨ζ, hζ, rfl⟩
    exact hmaps a b hζ
  · intro ξ hξ
    have hfx := hmaps (f b) (f a) hξ
    change f ξ ∈ Circle.path (f (f a)) (f (f b)) '' Set.Ioo 0 1 at hfx
    rw [hf, hf] at hfx
    exact ⟨f ξ, hfx, hf ξ⟩

namespace DirichletBoundarySegments

/-- Each constructed cyclic vertex has its enumerated actual radial
position, by the inverse of the proved frontier homeomorphism. -/
theorem hyperbolicRadialDirection_intrinsicCyclicVertex
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    hyperbolicRadialDirection o (B.intrinsicCyclicVertex i) =
      ((B.intrinsicRadialCutEnumeration i).1 : ℂ) :=
  congrArg (fun ξ : Circle => (ξ : ℂ))
    ((X.dirichletBoundaryRadialHomeomorph o).apply_symm_apply _)

/-- Consecutive genuine cyclic vertices are distinct. -/
theorem intrinsicCyclicVertex_next_ne
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicCyclicVertex i ≠
      B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i) := by
  intro hi
  have hne := B.closedEdgeEndpoints_ne B.intrinsicCornerCuts (B.intrinsicCyclicEdge i)
  rcases B.intrinsicCyclicEdge_endpoints_eq_or_swap i with h | h
  · rw [h] at hne
    exact hne hi
  · rw [h] at hne
    exact hne hi.symm

/-- A point of an actual cyclic closed side belongs to the bisector of its
retained actual deck label. -/
theorem intrinsicCyclicClosedEdge_mem_bisector
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o z : ℍ}
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (hz : z ∈ B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i)) :
    dist z o = dist z ((B.intrinsicCyclicEdge i).1.1.1 • o) := by
  let s := B.intrinsicCyclicEdge i
  obtain ⟨t, ht, rfl⟩ := hz
  have hleft := B.intrinsicCornerCuts_subset_Icc s.1 s.2.left.2
  have hright := B.intrinsicCornerCuts_subset_Icc s.1 s.2.right.2
  have htunit : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hleft.1.trans ht.1, ht.2.trans hright.2⟩
  have hzseg := Vendored.RiemannDynamics.geodInterp_mem_geodSeg
    (B.endpoints s.1.1).1 (B.endpoints s.1.1).2 htunit
  rw [← B.section_eq_segment s.1.1] at hzseg
  exact hzseg.2

/-- The actual inverse-deck side pairing reverses the constructed cyclic
endpoint order. The alternative equal-order transport would send a directed
circle arc to its disjoint reverse through the actual bisector reflection. -/
theorem inverse_smul_intrinsicCyclicVertices_eq_reverse
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (B.intrinsicCyclicEdge i).1.1.1⁻¹ • B.intrinsicCyclicVertex i =
        B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card (B.intrinsicCyclicPairing i)) ∧
      (B.intrinsicCyclicEdge i).1.1.1⁻¹ •
          B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i) =
        B.intrinsicCyclicVertex (B.intrinsicCyclicPairing i) := by
  let s := B.intrinsicCyclicEdge i
  let γ : X.deckGroup := s.1.1.1
  let j := B.intrinsicCyclicPairing i
  let ni := finRotate B.intrinsicBoundaryRadialCuts.card i
  let nj := finRotate B.intrinsicBoundaryRadialCuts.card j
  have hab := B.intrinsicCyclicVertex_next_ne i
  have hcd := B.intrinsicCyclicVertex_next_ne j
  have hseg : Vendored.RiemannDynamics.geodSeg (γ⁻¹ • B.intrinsicCyclicVertex i)
        (γ⁻¹ • B.intrinsicCyclicVertex ni) =
      Vendored.RiemannDynamics.geodSeg (B.intrinsicCyclicVertex j) (B.intrinsicCyclicVertex nj) := by
    have hsmul := Vendored.RiemannDynamics.smul_geodSeg (γ⁻¹ : X.deckGroup).1
      (B.intrinsicCyclicVertex i) (B.intrinsicCyclicVertex ni)
    change (fun z : ℍ => γ⁻¹ • z) ''
      Vendored.RiemannDynamics.geodSeg (B.intrinsicCyclicVertex i) (B.intrinsicCyclicVertex ni) =
      Vendored.RiemannDynamics.geodSeg (γ⁻¹ • B.intrinsicCyclicVertex i)
        (γ⁻¹ • B.intrinsicCyclicVertex ni) at hsmul
    rw [← hsmul, ← B.intrinsicCyclicEdge_closedImage_eq_geodSeg i,
      B.image_inv_smul_intrinsicCyclicClosedEdge i,
      B.intrinsicCyclicEdge_closedImage_eq_geodSeg j]
  have hends := (geodSeg_eq_iff_endpoints_eq_or_swap
    (fun h => hab (smul_left_cancel γ⁻¹ h)) hcd).mp hseg
  rcases hends with hsame | hreverse
  · have hγ : γ ≠ 1 := Finset.ne_of_mem_erase s.1.1.2.1
    obtain ⟨u, hu⟩ := X.exists_inverse_bisector_radial_antirotation o γ hγ
    let a := (B.intrinsicRadialCutEnumeration i).1
    let b := (B.intrinsicRadialCutEnumeration ni).1
    let c := (B.intrinsicRadialCutEnumeration j).1
    let d := (B.intrinsicRadialCutEnumeration nj).1
    have hfa : u * a⁻¹ = c := by
      apply Circle.coe_injective
      rw [Circle.coe_mul, Circle.coe_inv_eq_conj]
      have hbis : dist (B.intrinsicCyclicVertex i) o =
          dist (B.intrinsicCyclicVertex i) (γ • o) :=
        B.intrinsicCyclicClosedEdge_mem_bisector i (by
          rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
          exact Vendored.RiemannDynamics.left_mem_geodSeg _ _)
      have h := hu (B.intrinsicCyclicVertex i) hbis
      rw [hsame.1, B.hyperbolicRadialDirection_intrinsicCyclicVertex,
        B.hyperbolicRadialDirection_intrinsicCyclicVertex] at h
      exact h.symm
    have hfb : u * b⁻¹ = d := by
      apply Circle.coe_injective
      rw [Circle.coe_mul, Circle.coe_inv_eq_conj]
      have hbis : dist (B.intrinsicCyclicVertex ni) o =
          dist (B.intrinsicCyclicVertex ni) (γ • o) :=
        B.intrinsicCyclicClosedEdge_mem_bisector i (by
          rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
          exact Vendored.RiemannDynamics.right_mem_geodSeg _ _)
      have h := hu (B.intrinsicCyclicVertex ni) hbis
      rw [hsame.2, B.hyperbolicRadialDirection_intrinsicCyclicVertex,
        B.hyperbolicRadialDirection_intrinsicCyclicVertex] at h
      exact h.symm
    obtain ⟨z, hz⟩ := B.intrinsicOpenEdgeImage_nonempty s
    let H := X.dirichletBoundaryRadialHomeomorph o
    let ξ : Circle := H ⟨z, (B.intrinsicOpenEdgeImage_subset_regular_frontier s hz).1⟩
    have hξ : ξ ∈ Circle.path a b '' Set.Ioo 0 1 := by
      rw [← B.intrinsicCyclicEdge_radialImage i]
      exact ⟨z, hz, rfl⟩
    have hξrev : u * ξ⁻¹ ∈ Circle.path d c '' Set.Ioo 0 1 := by
      rw [← hfa, ← hfb, ← image_circle_open_arc_antirotation]
      exact ⟨ξ, hξ, rfl⟩
    have hzinv : γ⁻¹ • z ∈ B.openEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge j) := by
      rw [B.intrinsicCyclicEdge_pairing, ← B.image_inv_smul_intrinsicOpenEdge s]
      exact ⟨z, hz, rfl⟩
    have hzbis : dist z o = dist z (γ • o) :=
      B.intrinsicCyclicClosedEdge_mem_bisector i (by
        rw [B.closedEdgeImage_eq_open_union_endpoints]
        exact Or.inl hz)
    have hξfwd : u * ξ⁻¹ ∈ Circle.path c d '' Set.Ioo 0 1 := by
      rw [← B.intrinsicCyclicEdge_radialImage j]
      refine ⟨γ⁻¹ • z, hzinv, ?_⟩
      rw [Circle.coe_mul, Circle.coe_inv_eq_conj]
      exact hu z hzbis
    have hcd' : c ≠ d := by
      intro h
      have hv := congrArg (fun ζ : Circle => (H.symm ζ).1) h
      exact hcd hv
    have hdisj := (Circle.disjoint_path_image_Ioc hcd').mono
      (Set.image_mono Set.Ioo_subset_Ioc_self) (Set.image_mono Set.Ioo_subset_Ioc_self)
    exact (Set.disjoint_left.mp hdisj hξfwd hξrev).elim
  · exact hreverse

#print axioms inverse_smul_intrinsicCyclicVertices_eq_reverse

/-- Inverse deck transport of the actual cyclic side uses exactly the
reversed unit parameter on its paired cyclic side. -/
theorem inverse_smul_intrinsicCyclicGeodInterp_eq_reverse
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (B.intrinsicCyclicEdge i).1.1.1⁻¹ •
        Vendored.RiemannDynamics.geodInterp (B.intrinsicCyclicVertex i)
          (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i)) t =
      Vendored.RiemannDynamics.geodInterp (B.intrinsicCyclicVertex (B.intrinsicCyclicPairing i))
        (B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card (B.intrinsicCyclicPairing i))) (1 - t) := by
  let γ : X.deckGroup := (B.intrinsicCyclicEdge i).1.1.1
  have hsmul := smul_geodInterp_of_mem_Icc (γ⁻¹ : X.deckGroup).1
    (B.intrinsicCyclicVertex i)
    (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i)) ht
  change γ⁻¹ • Vendored.RiemannDynamics.geodInterp _ _ t =
    Vendored.RiemannDynamics.geodInterp (γ⁻¹ • B.intrinsicCyclicVertex i)
      (γ⁻¹ • B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i)) t at hsmul
  rw [hsmul, (B.inverse_smul_intrinsicCyclicVertices_eq_reverse i).1,
    (B.inverse_smul_intrinsicCyclicVertices_eq_reverse i).2]
  exact geodInterp_reverse_of_mem_Icc _ _ ht

#print axioms inverse_smul_intrinsicCyclicGeodInterp_eq_reverse

end DirichletBoundarySegments

end SystolicGrowth
