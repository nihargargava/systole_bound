module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.QuotientOrbitBall
public import Geometry.HyperbolicArea

@[expose] public section

/-!
# Actual punctured components for a finite gluing chain

The component numbered `i : Fin n` loses its left open disk precisely when
`0 < i`, and its right open disk precisely when `i + 1 < n`. The deleted
sets are the actual orbit-ball images in the original compact quotient.
The remaining carriers are compact subspaces. Sphere and collar images
retain their genuine upstairs quotient charts; no glued metric, surface
marking or curvature certificate is assumed.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth
namespace ClosedHyperbolicSurface

/-- An orbit ball is open in the actual quotient topology. -/
theorem isOpen_orbitBall {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r : ℝ) : IsOpen (X.orbitBall o r) := by
  exact isOpenMap_quotient_mk'_mul (Metric.ball o r) Metric.isOpen_ball

/-- The disks genuinely deleted from component `i` of a finite path. The
first component has no left puncture and the last has no right puncture. -/
def punctureDeletedSet {g n : ℕ} (X : ClosedHyperbolicSurface g)
    (left right : ℍ) (r : ℝ) (i : Fin n) : Set X.Carrier :=
  (if 0 < i.1 then X.orbitBall left r else ∅) ∪
    (if i.1 + 1 < n then X.orbitBall right r else ∅)

/-- The actual closed subset retained after the prescribed open-disk deletions. -/
def puncturedComponentSet {g n : ℕ} (X : ClosedHyperbolicSurface g)
    (left right : ℍ) (r : ℝ) (i : Fin n) : Set X.Carrier :=
  (X.punctureDeletedSet left right r i)ᶜ

/-- The punctured component carrier, as a subspace of the original quotient. -/
abbrev PuncturedComponent {g n : ℕ} (X : ClosedHyperbolicSurface g)
    (left right : ℍ) (r : ℝ) (i : Fin n) :=
  {q : X.Carrier // q ∈ X.puncturedComponentSet left right r i}

theorem isOpen_punctureDeletedSet {g n : ℕ} (X : ClosedHyperbolicSurface g)
    (left right : ℍ) (r : ℝ) (i : Fin n) :
    IsOpen (X.punctureDeletedSet left right r i) := by
  unfold punctureDeletedSet
  apply IsOpen.union
  · split_ifs
    · exact X.isOpen_orbitBall left r
    · exact isOpen_empty
  · split_ifs
    · exact X.isOpen_orbitBall right r
    · exact isOpen_empty

theorem isClosed_puncturedComponentSet {g n : ℕ} (X : ClosedHyperbolicSurface g)
    (left right : ℍ) (r : ℝ) (i : Fin n) :
    IsClosed (X.puncturedComponentSet left right r i) :=
  (X.isOpen_punctureDeletedSet left right r i).isClosed_compl

/-- Compactness comes from the given actual compact surface quotient and
openness of the deleted disks, not from an assumed gluing carrier. -/
theorem isCompact_puncturedComponentSet {g n : ℕ} (X : ClosedHyperbolicSurface g)
    (left right : ℍ) (r : ℝ) (i : Fin n) :
    IsCompact (X.puncturedComponentSet left right r i) := by
  letI := X.carrierCompactSpace
  exact (X.isClosed_puncturedComponentSet left right r i).isCompact

instance puncturedComponentCompactSpace {g n : ℕ} (X : ClosedHyperbolicSurface g)
    (left right : ℍ) (r : ℝ) (i : Fin n) :
    CompactSpace (X.PuncturedComponent left right r i) :=
  isCompact_iff_compactSpace.mp (X.isCompact_puncturedComponentSet left right r i)

/-- The actual quotient image of the radius-`r` upstairs circle. -/
def punctureCircle {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (r : ℝ) :
    Set X.Carrier :=
  (fun z : ℍ => (Quotient.mk'' z : X.Carrier)) '' Metric.sphere o r

/-- The actual quotient collar between the retained inner boundary and an
open radius-`R` embedded chart. -/
def punctureCollar {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (r R : ℝ) :
    Set X.Carrier :=
  (fun z : ℍ => (Quotient.mk'' z : X.Carrier)) ''
    (Metric.ball o R \ Metric.ball o r)

theorem isCompact_punctureCircle {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r : ℝ) : IsCompact (X.punctureCircle o r) :=
  (isCompact_sphere o r).image continuous_quotient_mk'

/-- The actual quotient map is an open embedding on every ball below
half the systole. This is the chart later used on both sides of a seam. -/
theorem quotientBall_isOpenEmbedding {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (R : ℝ) (hR : 2 * R < X.systole) :
    Topology.IsOpenEmbedding
      (fun z : Metric.ball o R => (Quotient.mk'' z.1 : X.Carrier)) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_quotient_mk'.comp continuous_subtype_val
  · intro z w h
    exact Subtype.ext (quotientMk_injOn_ball X o R hR z.2 w.2 h)
  · exact isOpenMap_quotient_mk'_mul.comp Metric.isOpen_ball.isOpenMap_subtype_val

/-- The genuine circle map is an embedding obtained by restricting the
actual embedded outer ball chart. -/
theorem quotientSphere_isEmbedding {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r R : ℝ) (hrR : r < R) (hR : 2 * R < X.systole) :
    Topology.IsEmbedding
      (fun z : Metric.sphere o r => (Quotient.mk'' z.1 : X.Carrier)) :=
  (X.quotientBall_isOpenEmbedding o R hR).isEmbedding.comp
    (Topology.IsEmbedding.inclusion (Metric.sphere_subset_ball hrR))

/-- An upstairs inner circle is homeomorphic to its actual quotient image,
so later seam identifications act on this circle rather than on postulated
boundary data. -/
noncomputable def punctureCircleHomeomorph {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r R : ℝ) (hrR : r < R) (hR : 2 * R < X.systole) :
    Metric.sphere o r ≃ₜ X.punctureCircle o r :=
  (X.quotientSphere_isEmbedding o r R hrR hR).toHomeomorph.trans
    (Homeomorph.setCongr (by
      ext q
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨z.1, z.2, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hz⟩, rfl⟩))

/-- Full-orbit separation, rather than separation of just two selected
lifts, makes the corresponding actual quotient orbit balls disjoint. -/
theorem disjoint_orbitBalls_of_orbit_separated {g : ℕ}
    (X : ClosedHyperbolicSurface g) (left right : ℍ) (a b : ℝ)
    (hsep : ∀ γ : X.deckGroup, a + b ≤ dist left (γ • right)) :
    Disjoint (X.orbitBall left a) (X.orbitBall right b) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨z, hz, hzq⟩ ⟨w, hw, hwq⟩
  have hrel : MulAction.orbitRel X.deckGroup ℍ z w :=
    Quotient.exact (hzq.trans hwq.symm)
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
  have hzd : dist left z < a := by simpa only [Metric.mem_ball, dist_comm] using hz
  have hwd : dist z (γ • right) < b := by
    rw [← hγ, dist_smul]
    exact hw
  have hlt : dist left (γ • right) < a + b :=
    lt_of_le_of_lt (dist_triangle left z (γ • right)) (add_lt_add hzd hwd)
  exact (not_lt_of_ge (hsep γ)) hlt

/-- The same full-orbit separation is symmetric in the two centers. -/
theorem orbit_separation_symm {g : ℕ} (X : ClosedHyperbolicSurface g)
    (left right : ℍ) (D : ℝ)
    (hsep : ∀ γ : X.deckGroup, D ≤ dist left (γ • right)) :
    ∀ γ : X.deckGroup, D ≤ dist right (γ • left) := by
  intro γ
  calc
    D ≤ dist left (γ⁻¹ • right) := hsep γ⁻¹
    _ = dist (γ • left) (γ • (γ⁻¹ • right)) := (dist_smul γ _ _).symm
    _ = dist (γ • left) right := by rw [smul_inv_smul]
    _ = dist right (γ • left) := dist_comm _ _

/-- The two inner disks are disjoint under the actual chain parameter
separation `D = R + r`; the strict inequality `r < R` pays for `2r < D`. -/
theorem disjoint_innerOrbitBalls {g : ℕ} (X : ClosedHyperbolicSurface g)
    (left right : ℍ) (r R : ℝ) (hrR : r < R)
    (hsep : ∀ γ : X.deckGroup, R + r ≤ dist left (γ • right)) :
    Disjoint (X.orbitBall left r) (X.orbitBall right r) := by
  apply X.disjoint_orbitBalls_of_orbit_separated left right r r
  intro γ
  exact (by linarith : r + r ≤ R + r).trans (hsep γ)

theorem punctureCollar_subset_orbitBall {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r R : ℝ) : X.punctureCollar o r R ⊆ X.orbitBall o R :=
  Set.image_mono Set.sdiff_subset

/-- The actual radius-`R` left collar avoids the other radius-`r` deleted
disk, even if the two outer radius-`R` disks happen to overlap. -/
theorem punctureCollar_left_disjoint_right_inner {g : ℕ}
    (X : ClosedHyperbolicSurface g) (left right : ℍ) (r R : ℝ)
    (hsep : ∀ γ : X.deckGroup, R + r ≤ dist left (γ • right)) :
    Disjoint (X.punctureCollar left r R) (X.orbitBall right r) :=
  (X.disjoint_orbitBalls_of_orbit_separated left right R r hsep).mono
    (X.punctureCollar_subset_orbitBall left r R) Set.Subset.rfl

/-- The symmetric collar avoidance follows from the same full-orbit bound. -/
theorem punctureCollar_right_disjoint_left_inner {g : ℕ}
    (X : ClosedHyperbolicSurface g) (left right : ℍ) (r R : ℝ)
    (hsep : ∀ γ : X.deckGroup, R + r ≤ dist left (γ • right)) :
    Disjoint (X.punctureCollar right r R) (X.orbitBall left r) :=
  (X.disjoint_orbitBalls_of_orbit_separated right left R r
    (X.orbit_separation_symm left right (R + r) hsep)).mono
      (X.punctureCollar_subset_orbitBall right r R) Set.Subset.rfl

/-- Embeddedness of the outer chart prevents its retained annulus from
returning to the same deleted inner orbit disk through a deck translate. -/
theorem punctureCollar_disjoint_own_inner {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r R : ℝ) (hrR : r < R) (hR : 2 * R < X.systole) :
    Disjoint (X.punctureCollar o r R) (X.orbitBall o r) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨z, ⟨hzR, hzr⟩, hzq⟩ ⟨w, hw, hwq⟩
  have hwR := Metric.ball_subset_ball hrR.le hw
  have hzw := quotientMk_injOn_ball X o R hR hzR hwR (hzq.trans hwq.symm)
  exact hzr (by simpa only [hzw] using hw)

/-- The quotient inner circle is contained in the retained collar. -/
theorem punctureCircle_subset_collar {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r R : ℝ) (hrR : r < R) :
    X.punctureCircle o r ⊆ X.punctureCollar o r R := by
  rintro q ⟨z, hz, rfl⟩
  refine ⟨z, ⟨Metric.sphere_subset_ball hrR hz, ?_⟩, rfl⟩
  exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hz

/-- The entire actual left collar lies in the retained component, for the
prescribed endpoint or interior disk-deletion pattern. -/
theorem punctureCollar_left_subset_puncturedComponentSet {g n : ℕ}
    (X : ClosedHyperbolicSurface g) (left right : ℍ) (r R : ℝ) (i : Fin n)
    (hrR : r < R) (hR : 2 * R < X.systole)
    (hsep : ∀ γ : X.deckGroup, R + r ≤ dist left (γ • right)) :
    X.punctureCollar left r R ⊆ X.puncturedComponentSet left right r i := by
  intro q hq
  have hnleft := Set.disjoint_left.mp
    (X.punctureCollar_disjoint_own_inner left r R hrR hR) hq
  have hnright := Set.disjoint_left.mp
    (X.punctureCollar_left_disjoint_right_inner left right r R hsep) hq
  simp [puncturedComponentSet, punctureDeletedSet, hnleft, hnright]

/-- Both collars are genuine retained subspaces of the same component. -/
theorem punctureCollar_right_subset_puncturedComponentSet {g n : ℕ}
    (X : ClosedHyperbolicSurface g) (left right : ℍ) (r R : ℝ) (i : Fin n)
    (hrR : r < R) (hR : 2 * R < X.systole)
    (hsep : ∀ γ : X.deckGroup, R + r ≤ dist left (γ • right)) :
    X.punctureCollar right r R ⊆ X.puncturedComponentSet left right r i := by
  intro q hq
  have hnleft := Set.disjoint_left.mp
    (X.punctureCollar_right_disjoint_left_inner left right r R hsep) hq
  have hnright := Set.disjoint_left.mp
    (X.punctureCollar_disjoint_own_inner right r R hrR hR) hq
  simp [puncturedComponentSet, punctureDeletedSet, hnleft, hnright]

/-- The left quotient circle is retained in the actual punctured carrier. -/
theorem punctureCircle_left_subset_puncturedComponentSet {g n : ℕ}
    (X : ClosedHyperbolicSurface g) (left right : ℍ) (r R : ℝ) (i : Fin n)
    (hrR : r < R) (hR : 2 * R < X.systole)
    (hsep : ∀ γ : X.deckGroup, R + r ≤ dist left (γ • right)) :
    X.punctureCircle left r ⊆ X.puncturedComponentSet left right r i :=
  (X.punctureCircle_subset_collar left r R hrR).trans
    (X.punctureCollar_left_subset_puncturedComponentSet left right r R i hrR hR hsep)

/-- The right quotient circle is retained in the same punctured carrier. -/
theorem punctureCircle_right_subset_puncturedComponentSet {g n : ℕ}
    (X : ClosedHyperbolicSurface g) (left right : ℍ) (r R : ℝ) (i : Fin n)
    (hrR : r < R) (hR : 2 * R < X.systole)
    (hsep : ∀ γ : X.deckGroup, R + r ≤ dist left (γ • right)) :
    X.punctureCircle right r ⊆ X.puncturedComponentSet left right r i :=
  (X.punctureCircle_subset_collar right r R hrR).trans
    (X.punctureCollar_right_subset_puncturedComponentSet left right r R i hrR hR hsep)

/-- The actual left circle map into the punctured component. Only indices
with a predecessor will be used as left seams of the gluing chain. -/
noncomputable def leftPunctureCircleMap {g n : ℕ} (X : ClosedHyperbolicSurface g)
    (left right : ℍ) (r R : ℝ) (i : Fin n)
    (hrR : r < R) (hR : 2 * R < X.systole)
    (hsep : ∀ γ : X.deckGroup, R + r ≤ dist left (γ • right)) :
    Metric.sphere left r → X.PuncturedComponent left right r i :=
  fun z => ⟨Quotient.mk'' z.1,
    X.punctureCircle_left_subset_puncturedComponentSet left right r R i hrR hR hsep
      ⟨z.1, z.2, rfl⟩⟩

/-- The actual right circle map into the punctured component. Only indices
with a successor will be used as right seams of the gluing chain. -/
noncomputable def rightPunctureCircleMap {g n : ℕ} (X : ClosedHyperbolicSurface g)
    (left right : ℍ) (r R : ℝ) (i : Fin n)
    (hrR : r < R) (hR : 2 * R < X.systole)
    (hsep : ∀ γ : X.deckGroup, R + r ≤ dist left (γ • right)) :
    Metric.sphere right r → X.PuncturedComponent left right r i :=
  fun z => ⟨Quotient.mk'' z.1,
    X.punctureCircle_right_subset_puncturedComponentSet left right r R i hrR hR hsep
      ⟨z.1, z.2, rfl⟩⟩

/-- The left seam-circle map is a genuine embedding of the upstairs circle
into the retained component subspace. -/
theorem leftPunctureCircleMap_isEmbedding {g n : ℕ}
    (X : ClosedHyperbolicSurface g) (left right : ℍ) (r R : ℝ) (i : Fin n)
    (hrR : r < R) (hR : 2 * R < X.systole)
    (hsep : ∀ γ : X.deckGroup, R + r ≤ dist left (γ • right)) :
    Topology.IsEmbedding (X.leftPunctureCircleMap left right r R i hrR hR hsep) :=
  (X.quotientSphere_isEmbedding left r R hrR hR).codRestrict
    (X.puncturedComponentSet left right r i) _

/-- The right seam-circle map likewise uses the actual embedded chart. -/
theorem rightPunctureCircleMap_isEmbedding {g n : ℕ}
    (X : ClosedHyperbolicSurface g) (left right : ℍ) (r R : ℝ) (i : Fin n)
    (hrR : r < R) (hR : 2 * R < X.systole)
    (hsep : ∀ γ : X.deckGroup, R + r ≤ dist left (γ • right)) :
    Topology.IsEmbedding (X.rightPunctureCircleMap left right r R i hrR hR hsep) :=
  (X.quotientSphere_isEmbedding right r R hrR hR).codRestrict
    (X.puncturedComponentSet left right r i) _

end ClosedHyperbolicSurface

#print axioms ClosedHyperbolicSurface.isCompact_puncturedComponentSet
#print axioms ClosedHyperbolicSurface.quotientBall_isOpenEmbedding
#print axioms ClosedHyperbolicSurface.punctureCircleHomeomorph
#print axioms ClosedHyperbolicSurface.disjoint_innerOrbitBalls
#print axioms ClosedHyperbolicSurface.punctureCollar_left_subset_puncturedComponentSet
#print axioms ClosedHyperbolicSurface.punctureCollar_right_subset_puncturedComponentSet
#print axioms ClosedHyperbolicSurface.leftPunctureCircleMap_isEmbedding
#print axioms ClosedHyperbolicSurface.rightPunctureCircleMap_isEmbedding

end SystolicGrowth
