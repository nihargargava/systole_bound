module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingManifoldCharts

@[expose] public section

/-!
# Concrete evaluations of the native glued charts

These formulas expose the sources, targets and inverse evaluations of the
existing interior and real-angular seam charts. They do not alter the
native atlas or its topology. The signed branch formulas refer to the
actual polar points in the original component carriers, including the
reflected identification at signed radius zero.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

@[simp] theorem gluingChartFromOpenEmbeddings_target
    {U M H : Type*} [TopologicalSpace U] [TopologicalSpace M] [TopologicalSpace H]
    [Nonempty U] (f : U → M) (j : U → H)
    (hf : Topology.IsOpenEmbedding f) (hj : Topology.IsOpenEmbedding j) :
    (gluingChartFromOpenEmbeddings f j hf hj).target = range j := by
  simp [gluingChartFromOpenEmbeddings]

@[simp] theorem gluingChartFromOpenEmbeddings_symm_apply
    {U M H : Type*} [TopologicalSpace U] [TopologicalSpace M] [TopologicalSpace H]
    [Nonempty U] (f : U → M) (j : U → H)
    (hf : Topology.IsOpenEmbedding f) (hj : Topology.IsOpenEmbedding j) (u : U) :
    (gluingChartFromOpenEmbeddings f j hf hj).symm (j u) = f u := by
  simp [gluingChartFromOpenEmbeddings, hj.toOpenPartialHomeomorph_left_inv]

@[simp] theorem gluingSeamAngularModel_re (C : ℝ) (g : ℕ) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) :
    (gluingSeamAngularModel C g θ p).re = p.1.1 := rfl

@[simp] theorem gluingSeamAngularModel_im (C : ℝ) (g : ℕ) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) :
    (gluingSeamAngularModel C g θ p).im = p.2.1 := rfl

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

section Interior

variable (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
  (z : ℍ) (ρ : ℝ) (hρ : 0 < ρ)
  (hq : ∀ w : ball z ρ,
    (Quotient.mk'' w.1 : (X i).Carrier) ∈ P.componentInteriorSet i)
  (hf : Topology.IsOpenEmbedding (fun w : ball z ρ =>
    P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq w⟩)))

@[simp] theorem gluedInteriorComplexChart_source :
    (P.gluedInteriorComplexChart i z ρ hρ hq hf).source =
      range (fun w : ball z ρ =>
        P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq w⟩)) := by
  simp [gluedInteriorComplexChart]

@[simp] theorem gluedInteriorComplexChart_target :
    (P.gluedInteriorComplexChart i z ρ hρ hq hf).target =
      range (fun w : ball z ρ => (w.1 : ℂ)) := by
  simp [gluedInteriorComplexChart]

@[simp] theorem gluedInteriorComplexChart_apply (w : ball z ρ) :
    P.gluedInteriorComplexChart i z ρ hρ hq hf
      (P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq w⟩)) = (w.1 : ℂ) := by
  simp [gluedInteriorComplexChart]

@[simp] theorem gluedInteriorComplexChart_symm_apply (w : ball z ρ) :
    (P.gluedInteriorComplexChart i z ρ hρ hq hf).symm (w.1 : ℂ) =
      P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq w⟩) := by
  simp [gluedInteriorComplexChart]

end Interior

@[simp] theorem seamAngularComplexChart_target
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    (P.seamAngularComplexChart k θ).target = range (gluingSeamAngularModel C g θ) := by
  simp [seamAngularComplexChart]

@[simp] theorem seamAngularComplexChart_symm_apply
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) :
    (P.seamAngularComplexChart k θ).symm (gluingSeamAngularModel C g θ p) =
      P.seamAngularPoint k θ p := by
  simp [seamAngularComplexChart]

/-- The seam chart target is the actual signed-radius/angle rectangle in
the existing complex model, with both endpoints open. -/
theorem mem_seamAngularComplexChart_target
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) (w : ℂ) :
    w ∈ (P.seamAngularComplexChart k θ).target ↔
      w.re ∈ Ioo (-gluingDepth C g) (gluingDepth C g) ∧
        w.im ∈ GluingAngularInterval θ := by
  rw [P.seamAngularComplexChart_target]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1.2, p.2.2⟩
  · rintro ⟨ht, ha⟩
    refine ⟨(⟨w.re, ht⟩, ⟨w.im, ha⟩), ?_⟩
    exact Complex.ext rfl rfl

/-- Equality of two real-angular parametrizations of the same actual seam
neighborhood reads precisely equality of signed radii and circle angles. -/
theorem seamAngularPoint_eq_iff
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ ψ : ℝ)
    (p : GluingSeamAngularDomain C g θ) (q : GluingSeamAngularDomain C g ψ) :
    P.seamAngularPoint k θ p = P.seamAngularPoint k ψ q ↔
      p.1.1 = q.1.1 ∧ Circle.exp p.2.1 = Circle.exp q.2.1 := by
  constructor
  · intro h
    have hc := (P.seamCylinderHomeomorph k).injective (Subtype.ext h)
    exact ⟨congrArg (fun a : GluingSeamCylinder C g => a.2.1) hc,
      congrArg (fun a : GluingSeamCylinder C g => a.1) hc⟩
  · rintro ⟨ht, ha⟩
    have hc : (Circle.exp p.2.1, p.1) = (Circle.exp q.2.1, q.1) :=
      Prod.ext ha (Subtype.ext ht)
    exact congrArg (fun a : GluingSeamCylinder C g => (P.seamCylinderHomeomorph k a).1) hc

/-- On the outgoing side, the signed coordinate is the deficit from the
inner radius. The formula includes the actual seam at signed radius zero. -/
theorem seamAngularPoint_of_nonpos
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) (hp : p.1.1 ≤ 0) :
    P.seamAngularPoint k θ p = P.gluedMk (P.seamOutgoingPolarPoint k
      (Circle.exp p.2.1, ⟨gluingRadius C g - p.1.1, by
        constructor
        · linarith
        · change gluingRadius C g - p.1.1 < gluingRadius C g + gluingDepth C g
          linarith [p.1.2.1]⟩)) := by
  let q : Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g) :=
    (Circle.exp p.2.1, ⟨gluingRadius C g - p.1.1, by
      constructor
      · linarith
      · change gluingRadius C g - p.1.1 < gluingRadius C g + gluingDepth C g
        linarith [p.1.2.1]⟩)
  have hi : (P.seamCylinderHomeomorph k).symm
      (P.seamNeighborhoodProjection k
        ⟨P.seamOutgoingPolarPoint k q, P.seamOutgoingPolarPoint_mem k q⟩) =
      (Circle.exp p.2.1, p.1) := by
    rw [P.seamCylinderHomeomorph_symm_outgoing]
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp [q]
      ring
  have hh := congrArg (P.seamCylinderHomeomorph k) hi
  rw [Homeomorph.apply_symm_apply] at hh
  exact (congrArg Subtype.val hh).symm

/-- On the incoming side, the signed coordinate is the excess over the
inner radius and the original component angle is reflected. -/
theorem seamAngularPoint_of_nonneg
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) (hp : 0 ≤ p.1.1) :
    P.seamAngularPoint k θ p = P.gluedMk (P.seamIncomingPolarPoint k
      ((Circle.exp p.2.1)⁻¹, ⟨gluingRadius C g + p.1.1, by
        constructor
        · linarith
        · change gluingRadius C g + p.1.1 < gluingRadius C g + gluingDepth C g
          linarith [p.1.2.2]⟩)) := by
  let q : Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g) :=
    ((Circle.exp p.2.1)⁻¹, ⟨gluingRadius C g + p.1.1, by
      constructor
      · linarith
      · change gluingRadius C g + p.1.1 < gluingRadius C g + gluingDepth C g
        linarith [p.1.2.2]⟩)
  have hi : (P.seamCylinderHomeomorph k).symm
      (P.seamNeighborhoodProjection k
        ⟨P.seamIncomingPolarPoint k q, P.seamIncomingPolarPoint_mem k q⟩) =
      (Circle.exp p.2.1, p.1) := by
    rw [P.seamCylinderHomeomorph_symm_incoming]
    apply Prod.ext
    · exact inv_inv _
    · apply Subtype.ext
      dsimp [q]
      ring
  have hh := congrArg (P.seamCylinderHomeomorph k) hi
  rw [Homeomorph.apply_symm_apply] at hh
  exact (congrArg Subtype.val hh).symm

/-- Signed radius zero is the image of the actual outgoing seam circle,
not a new circle selected by the angular chart. -/
theorem seamAngularPoint_of_zero
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) (hp : p.1.1 = 0) :
    P.seamAngularPoint k θ p = P.gluedMk (P.seamSource k
      ⟨gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2
        (Circle.exp p.2.1) (gluingRadius C g), by
        rw [mem_sphere, dist_comm, dist_gluingPolarPoint _ _ P.radius_pos.le]⟩) := by
  calc
    P.seamAngularPoint k θ p = P.gluedMk (P.seamOutgoingPolarPoint k
        (Circle.exp p.2.1, ⟨gluingRadius C g, le_rfl, P.radius_lt_embeddedRadius⟩)) := by
      simpa only [hp, sub_zero] using P.seamAngularPoint_of_nonpos k θ p hp.le
    _ = _ := by
      apply congrArg P.gluedMk
      apply Sigma.ext rfl
      apply heq_of_eq
      apply Subtype.ext
      rfl

/-- A native seam point with signed radius zero cannot coincide in the
actual quotient with any point of a retained component's original interior. -/
theorem seamAngularPoint_ne_componentInteriorPoint_of_zero
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) (hp : p.1.1 = 0)
    (i : Fin n) (q : P.componentInteriorSet i) :
    P.seamAngularPoint k θ p ≠ P.gluedMk (P.componentInteriorPoint i q) := by
  let z : sphere (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) :=
    ⟨gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2
      (Circle.exp p.2.1) (gluingRadius C g), by
      rw [mem_sphere, dist_comm, dist_gluingPolarPoint _ _ P.radius_pos.le]⟩
  have hz : P.seamAngularPoint k θ p = P.gluedMk (P.seamSource k z) :=
    P.seamAngularPoint_of_zero k θ p hp
  have hs : P.seamSource k z ∈ P.chainSeamSet :=
    ⟨P.seamTarget k z, Or.inl ⟨k, z, rfl, rfl⟩⟩
  intro h
  have hh : P.componentInteriorPoint i q = P.seamSource k z :=
    P.gluedMk_eq_of_not_mem_chainSeamSet
      (a := P.componentInteriorPoint i q) (b := P.seamSource k z)
      (P.componentInteriorPoint_not_mem_chainSeamSet i q) (h.symm.trans hz)
  exact P.componentInteriorPoint_not_mem_chainSeamSet i q (hh.symm ▸ hs)

end ExerciseGluingPreparation

#print axioms ExerciseGluingPreparation.gluedInteriorComplexChart_symm_apply
#print axioms ExerciseGluingPreparation.seamAngularComplexChart_symm_apply
#print axioms ExerciseGluingPreparation.mem_seamAngularComplexChart_target
#print axioms ExerciseGluingPreparation.seamAngularPoint_eq_iff
#print axioms ExerciseGluingPreparation.seamAngularPoint_of_nonpos
#print axioms ExerciseGluingPreparation.seamAngularPoint_of_nonneg
#print axioms ExerciseGluingPreparation.seamAngularPoint_of_zero
#print axioms ExerciseGluingPreparation.seamAngularPoint_ne_componentInteriorPoint_of_zero

end SystolicGrowth
