module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChartCoverage
public import Geometry.GluingSeamCharts
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section

/-!
# Native local charts for the actual glued carrier

The interior charts use the actual hyperbolic ball embeddings. Angular
coordinates use the exponential on an explicit interval shorter than a
full turn. These are topological charts; smooth transition maps and a
compatible global Riemannian metric remain separate obligations.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

/-- A fixed thin width, strictly inside the original native collar depth. -/
noncomputable def gluingThinSeamWidth (C : ℝ) (g : ℕ) : ℝ := gluingDepth C g / 4

/-- Two open embeddings of the same coordinate domain determine a native chart. -/
noncomputable def gluingChartFromOpenEmbeddings
    {U M H : Type*} [TopologicalSpace U] [TopologicalSpace M] [TopologicalSpace H]
    [Nonempty U] (f : U → M) (j : U → H)
    (hf : Topology.IsOpenEmbedding f) (hj : Topology.IsOpenEmbedding j) :
    OpenPartialHomeomorph M H :=
  (hf.toOpenPartialHomeomorph f).symm.trans (hj.toOpenPartialHomeomorph j)

@[simp] theorem gluingChartFromOpenEmbeddings_source
    {U M H : Type*} [TopologicalSpace U] [TopologicalSpace M] [TopologicalSpace H]
    [Nonempty U] (f : U → M) (j : U → H)
    (hf : Topology.IsOpenEmbedding f) (hj : Topology.IsOpenEmbedding j) :
    (gluingChartFromOpenEmbeddings f j hf hj).source = range f := by
  simp [gluingChartFromOpenEmbeddings]

@[simp] theorem gluingChartFromOpenEmbeddings_apply
    {U M H : Type*} [TopologicalSpace U] [TopologicalSpace M] [TopologicalSpace H]
    [Nonempty U] (f : U → M) (j : U → H)
    (hf : Topology.IsOpenEmbedding f) (hj : Topology.IsOpenEmbedding j) (u : U) :
    gluingChartFromOpenEmbeddings f j hf hj (f u) = j u := by
  simp [gluingChartFromOpenEmbeddings, hf.toOpenPartialHomeomorph_left_inv]

/-- An explicit local angular domain, of width `π`, centered at the chosen lift. -/
abbrev GluingAngularInterval (θ : ℝ) := Ioo (θ - Real.pi / 2) (θ + Real.pi / 2)

/-- The angular coordinate map is the actual circle exponential. -/
noncomputable def gluingAngularIntervalMap (θ : ℝ) (a : GluingAngularInterval θ) : Circle :=
  Circle.exp a.1

theorem gluingAngularIntervalMap_isOpenEmbedding (θ : ℝ) :
    Topology.IsOpenEmbedding (gluingAngularIntervalMap θ) := by
  have hinj : InjOn Circle.exp (Icc (θ - Real.pi / 2) (θ + Real.pi / 2)) :=
    Circle.exp_injOn_Icc (by linarith [Real.pi_pos])
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact isLocalHomeomorph_circleExp.continuous.comp continuous_subtype_val
  · intro a b hab
    exact Subtype.ext (hinj (Ioo_subset_Icc_self a.2) (Ioo_subset_Icc_self b.2) hab)
  · exact isLocalHomeomorph_circleExp.isOpenMap.comp isOpen_Ioo.isOpenEmbedding_subtypeVal.isOpenMap

/-- Signed radial and real angular coordinates for a seam chart. -/
abbrev GluingSeamAngularDomain (C : ℝ) (g : ℕ) (θ : ℝ) :=
  Ioo (-gluingDepth C g) (gluingDepth C g) × GluingAngularInterval θ

/-- The complex model has signed radius as real part and lifted angle as imaginary part. -/
noncomputable def gluingSeamAngularModel (C : ℝ) (g : ℕ) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) : ℂ :=
  Complex.equivRealProdCLM.symm (p.1.1, p.2.1)

theorem gluingSeamAngularModel_isOpenEmbedding (C : ℝ) (g : ℕ) (θ : ℝ) :
    Topology.IsOpenEmbedding (gluingSeamAngularModel C g θ) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.isOpenEmbedding.comp
    (isOpen_Ioo.isOpenEmbedding_subtypeVal.prodMap isOpen_Ioo.isOpenEmbedding_subtypeVal)

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual closed strip used by localized seam smoothing. The definition
is placed with the atlas so the canonical chart selector can choose a seam
chart on this set without depending on later curvature modules. -/
def closedThinSeamCollar (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) : Set P.GluedCarrier :=
  (fun p : GluingSeamCylinder C g => (P.seamCylinderHomeomorph k p).1) ''
    {p | |p.2.1| ≤ gluingThinSeamWidth C g}

/-- The closed smoothing strip lies in the corresponding original seam collar. -/
theorem closedThinSeamCollar_subset_original_collar
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.closedThinSeamCollar k ⊆ P.gluedMk '' P.seamNeighborhood k := by
  rintro y ⟨p, hp, rfl⟩
  exact (P.seamCylinderHomeomorph k p).2

/-- A concrete native chart obtained from one of the actual interior ball embeddings. -/
noncomputable def gluedInteriorComplexChart
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (z : ℍ) (ρ : ℝ) (hρ : 0 < ρ)
    (hq : ∀ w : ball z ρ,
      (Quotient.mk'' w.1 : (X i).Carrier) ∈ P.componentInteriorSet i)
    (hf : Topology.IsOpenEmbedding (fun w : ball z ρ =>
      P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq w⟩))) :
    OpenPartialHomeomorph P.GluedCarrier ℂ := by
  letI : Nonempty (ball z ρ) := ⟨⟨z, by simpa using hρ⟩⟩
  exact gluingChartFromOpenEmbeddings _ (fun w : ball z ρ => (w.1 : ℂ)) hf
    (UpperHalfPlane.isOpenEmbedding_coe.comp Metric.isOpen_ball.isOpenEmbedding_subtypeVal)

/-- The seam chart's forward parametrization uses the actual signed cylinder homeomorphism. -/
noncomputable def seamAngularPoint (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : ℝ) (p : GluingSeamAngularDomain C g θ) : P.GluedCarrier :=
  (P.seamCylinderHomeomorph k (Circle.exp p.2.1, p.1)).1

theorem seamAngularPoint_isOpenEmbedding (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : ℝ) : Topology.IsOpenEmbedding (P.seamAngularPoint k θ) := by
  have hs : Topology.IsOpenEmbedding
      (fun p : GluingSeamAngularDomain C g θ => (Circle.exp p.2.1, p.1)) :=
    (Homeomorph.prodComm _ _).isOpenEmbedding.comp
      (Topology.IsOpenEmbedding.id.prodMap (gluingAngularIntervalMap_isOpenEmbedding θ))
  exact (P.gluedSeamNeighborhood_isOpen k).isOpenEmbedding_subtypeVal.comp
    ((P.seamCylinderHomeomorph k).isOpenEmbedding.comp hs)

/-- A genuine two-dimensional chart, including the seam at signed radius zero. -/
noncomputable def seamAngularComplexChart (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : ℝ) : OpenPartialHomeomorph P.GluedCarrier ℂ := by
  letI : Nonempty (GluingSeamAngularDomain C g θ) :=
    ⟨(⟨0, by constructor <;> linarith [P.depth_pos]⟩,
      ⟨θ, by constructor <;> linarith [Real.pi_pos]⟩)⟩
  exact gluingChartFromOpenEmbeddings (P.seamAngularPoint k θ)
    (gluingSeamAngularModel C g θ) (P.seamAngularPoint_isOpenEmbedding k θ)
    (gluingSeamAngularModel_isOpenEmbedding C g θ)

@[simp] theorem seamAngularComplexChart_source
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    (P.seamAngularComplexChart k θ).source = range (P.seamAngularPoint k θ) := by
  simp [seamAngularComplexChart]

@[simp] theorem seamAngularComplexChart_apply
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) :
    P.seamAngularComplexChart k θ (P.seamAngularPoint k θ p) =
      gluingSeamAngularModel C g θ p := by
  simp [seamAngularComplexChart]

/-- All concrete small interior charts, retaining the all-pairs isometry radius bound. -/
def IsGluedInteriorComplexChart (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) : Prop :=
  ∃ (i : Fin n) (z : ℍ) (ρ : ℝ) (hρ : 0 < ρ) (_h4 : 4 * ρ < (X i).systole)
    (hq : ∀ w : ball z ρ,
      (Quotient.mk'' w.1 : (X i).Carrier) ∈ P.componentInteriorSet i)
    (hf : Topology.IsOpenEmbedding (fun w : ball z ρ =>
      P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq w⟩))),
    e = P.gluedInteriorComplexChart i z ρ hρ hq hf

/-- The actual atlas contains the concrete interior charts and every real-angular seam chart. -/
def gluedComplexAtlas (P : ExerciseGluingPreparation C g n genera X) :
    Set (OpenPartialHomeomorph P.GluedCarrier ℂ) :=
  {e | P.IsGluedInteriorComplexChart e ∨
    ∃ (k : Fin (n - 1)) (θ : ℝ), e = P.seamAngularComplexChart k θ}

/-- Every original interior point is covered by one of the concrete atlas charts. -/
theorem exists_gluedComponentInterior_atlas_chart
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.componentInteriorSet i) :
    ∃ e ∈ P.gluedComplexAtlas,
      P.gluedMk (P.componentInteriorPoint i q) ∈ e.source := by
  obtain ⟨z, ρ, hρ, h4, hz, hq, hf⟩ :=
    P.exists_gluedComponentInterior_ball_chart i q
  refine ⟨P.gluedInteriorComplexChart i z ρ hρ hq hf,
    Or.inl ⟨i, z, ρ, hρ, h4, hq, hf, rfl⟩, ?_⟩
  simp only [gluedInteriorComplexChart, gluingChartFromOpenEmbeddings_source]
  refine ⟨⟨z, by simpa using hρ⟩, ?_⟩
  simp only [hz]

/-- The genuine interior ball charts give native complex-model charts at each
original interior point of the actual quotient. -/
theorem exists_gluedComponentInterior_complex_chart
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.componentInteriorSet i) :
    ∃ e : OpenPartialHomeomorph P.GluedCarrier ℂ,
      P.gluedMk (P.componentInteriorPoint i q) ∈ e.source := by
  obtain ⟨e, _he, hq⟩ := P.exists_gluedComponentInterior_atlas_chart i q
  exact ⟨e, hq⟩

/-- Every actual seam-neighborhood point is covered by a real-angular chart. -/
theorem exists_gluedSeam_atlas_chart (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (q : ↥(P.gluedMk '' P.seamNeighborhood k)) :
    ∃ e ∈ P.gluedComplexAtlas, q.1 ∈ e.source := by
  let p := (P.seamCylinderHomeomorph k).symm q
  let θ := Complex.arg (p.1 : ℂ)
  let a : GluingSeamAngularDomain C g θ :=
    (p.2, ⟨θ, by constructor <;> linarith [Real.pi_pos]⟩)
  refine ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩, ?_⟩
  rw [seamAngularComplexChart_source]
  refine ⟨a, ?_⟩
  change (P.seamCylinderHomeomorph k (Circle.exp (Complex.arg (p.1 : ℂ)), p.2)).1 = q.1
  rw [Circle.exp_arg]
  exact congrArg Subtype.val ((P.seamCylinderHomeomorph k).apply_symm_apply q)

/-- The interior/seam coverage theorem constructs an atlas on the actual carrier. -/
theorem exists_gluedComplexAtlas_chart (P : ExerciseGluingPreparation C g n genera X)
    (q : P.GluedCarrier) : ∃ e ∈ P.gluedComplexAtlas, q ∈ e.source := by
  rcases P.gluedPoint_mem_interior_or_seamNeighborhood q with ⟨i, p, rfl⟩ | ⟨k, hq⟩
  · exact P.exists_gluedComponentInterior_atlas_chart i p
  · exact P.exists_gluedSeam_atlas_chart k ⟨q, hq⟩

/-- **Math.** A chart witness that places the canonical chart in the seam atlas
on every closed smoothing strip. Off all such strips, any member of the
already-proved atlas cover is valid. -/
theorem exists_gluedComplexAtlas_chart_for_curvature
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedCarrier) :
    ∃ e ∈ P.gluedComplexAtlas, q ∈ e.source ∧
      ((∃ k : Fin (n - 1), ∃ θ : ℝ,
          q ∈ P.closedThinSeamCollar k ∧ e = P.seamAngularComplexChart k θ) ∨
        ∀ k : Fin (n - 1), q ∉ P.closedThinSeamCollar k) := by
  classical
  by_cases hc : ∃ k : Fin (n - 1), q ∈ P.closedThinSeamCollar k
  · obtain ⟨k, hk⟩ := hc
    have hcollar := P.closedThinSeamCollar_subset_original_collar k hk
    let q' : ↥(P.gluedMk '' P.seamNeighborhood k) := ⟨q, hcollar⟩
    let p := (P.seamCylinderHomeomorph k).symm q'
    let θ := Complex.arg (p.1 : ℂ)
    let a : GluingSeamAngularDomain C g θ :=
      (p.2, ⟨θ, by constructor <;> linarith [Real.pi_pos]⟩)
    refine ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩, ?_,
      Or.inl ⟨k, θ, hk, rfl⟩⟩
    rw [seamAngularComplexChart_source]
    refine ⟨a, ?_⟩
    change (P.seamCylinderHomeomorph k
      (Circle.exp (Complex.arg (p.1 : ℂ)), p.2)).1 = q
    rw [Circle.exp_arg]
    exact congrArg Subtype.val ((P.seamCylinderHomeomorph k).apply_symm_apply q')
  · obtain ⟨e, he, hs⟩ := P.exists_gluedComplexAtlas_chart q
    refine ⟨e, he, hs, Or.inr ?_⟩
    intro k hk
    exact hc ⟨k, hk⟩

/-- The native charted-space structure uses precisely the concrete atlas proved above. -/
noncomputable instance gluedCarrierChartedSpace
    (P : ExerciseGluingPreparation C g n genera X) : ChartedSpace ℂ P.GluedCarrier where
  atlas := P.gluedComplexAtlas
  chartAt q := (P.exists_gluedComplexAtlas_chart_for_curvature q).choose
  mem_chart_source q :=
    (P.exists_gluedComplexAtlas_chart_for_curvature q).choose_spec.2.1
  chart_mem_atlas q :=
    (P.exists_gluedComplexAtlas_chart_for_curvature q).choose_spec.1

/-- Compactness and the genuine two-dimensional atlas give second countability. -/
instance gluedCarrierSecondCountableTopology
    (P : ExerciseGluingPreparation C g n genera X) : SecondCountableTopology P.GluedCarrier :=
  ChartedSpace.secondCountable_of_sigmaCompact ℂ P.GluedCarrier

end ExerciseGluingPreparation

#print axioms gluingAngularIntervalMap_isOpenEmbedding
#print axioms ExerciseGluingPreparation.exists_gluedComponentInterior_complex_chart
#print axioms ExerciseGluingPreparation.seamAngularPoint_isOpenEmbedding
#print axioms ExerciseGluingPreparation.exists_gluedComplexAtlas_chart
#print axioms ExerciseGluingPreparation.gluedCarrierChartedSpace
#print axioms ExerciseGluingPreparation.gluedCarrierSecondCountableTopology

end SystolicGrowth
