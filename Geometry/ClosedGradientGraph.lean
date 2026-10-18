module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.HilbertGraphResolvent
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Sequences

@[expose] public section

/-!
# Completion of an actual gradient graph

Two linear maps on a common space of smooth test functions record their
function values and derivatives in Hilbert spaces. Taking the closure of
their joint image constructs a complete Hilbert graph. Its two projections
are actual bounded maps; linear weak-derivative identities pass to the
closure by continuity. The coercive inverse is therefore constructed on
this graph, with no existence premise for a weak solution.

The manifold application must supply the two actual smooth-function maps
and establish their coordinate integration-by-parts identities.
-/

namespace SystolicGrowth

open ContinuousLinearMap InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

variable {D H G : Type*} [AddCommGroup D] [Module ℝ D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- The literal pair consisting of the function and its smooth derivative. -/
def smoothGradientGraphMap (value : D →ₗ[ℝ] H) (derivative : D →ₗ[ℝ] G) :
    D →ₗ[ℝ] WithLp 2 (H × G) :=
  (WithLp.linearEquiv 2 ℝ (H × G)).symm.toLinearMap.comp (value.prod derivative)

/-- The completed graph, constructed by closure in the Hilbert product. -/
def closedGradientGraph (value : D →ₗ[ℝ] H) (derivative : D →ₗ[ℝ] G) :
    Submodule ℝ (WithLp 2 (H × G)) :=
  (smoothGradientGraphMap value derivative).range.topologicalClosure

instance closedGradientGraph_completeSpace (value : D →ₗ[ℝ] H)
    (derivative : D →ₗ[ℝ] G) : CompleteSpace (closedGradientGraph value derivative) := by
  unfold closedGradientGraph
  infer_instance

/-- A smooth test function determines a genuine element of the completed graph. -/
def closedGradientGraphOfSmooth (value : D →ₗ[ℝ] H) (derivative : D →ₗ[ℝ] G) (f : D) :
    closedGradientGraph value derivative :=
  ⟨smoothGradientGraphMap value derivative f,
    (smoothGradientGraphMap value derivative).range.le_topologicalClosure ⟨f, rfl⟩⟩

/-- The actual function component of the completed graph. -/
def closedGradientGraphValue (value : D →ₗ[ℝ] H) (derivative : D →ₗ[ℝ] G) :
    closedGradientGraph value derivative →L[ℝ] H :=
  (WithLp.fstL 2 ℝ H G).comp (closedGradientGraph value derivative).subtypeL

/-- The actual derivative component of the completed graph. -/
def closedGradientGraphDerivative (value : D →ₗ[ℝ] H) (derivative : D →ₗ[ℝ] G) :
    closedGradientGraph value derivative →L[ℝ] G :=
  (WithLp.sndL 2 ℝ H G).comp (closedGradientGraph value derivative).subtypeL

omit [CompleteSpace H] [CompleteSpace G] in
@[simp] theorem closedGradientGraphValue_ofSmooth
    (value : D →ₗ[ℝ] H) (derivative : D →ₗ[ℝ] G) (f : D) :
    closedGradientGraphValue value derivative (closedGradientGraphOfSmooth value derivative f) =
      value f := rfl

omit [CompleteSpace H] [CompleteSpace G] in
@[simp] theorem closedGradientGraphDerivative_ofSmooth
    (value : D →ₗ[ℝ] H) (derivative : D →ₗ[ℝ] G) (f : D) :
    closedGradientGraphDerivative value derivative
      (closedGradientGraphOfSmooth value derivative f) = derivative f := rfl

omit [CompleteSpace H] [CompleteSpace G] in
theorem closedGradientGraphValue_norm_le
    (value : D →ₗ[ℝ] H) (derivative : D →ₗ[ℝ] G)
    (v : closedGradientGraph value derivative) :
    ‖closedGradientGraphValue value derivative v‖ ≤ ‖v‖ :=
  WithLp.norm_fst_le (p := 2) H v.val

omit [CompleteSpace H] [CompleteSpace G] in
theorem closedGradientGraphDerivative_norm_le
    (value : D →ₗ[ℝ] H) (derivative : D →ₗ[ℝ] G)
    (v : closedGradientGraph value derivative) :
    ‖closedGradientGraphDerivative value derivative v‖ ≤ ‖v‖ :=
  WithLp.norm_snd_le (p := 2) H v.val

omit [CompleteSpace H] [CompleteSpace G] in
/-- The graph inner product is exactly the sum of the two component inner products. -/
theorem closedGradientGraph_inner (value : D →ₗ[ℝ] H) (derivative : D →ₗ[ℝ] G)
    (v w : closedGradientGraph value derivative) :
    ⟪v, w⟫_ℝ =
      ⟪closedGradientGraphValue value derivative v,
        closedGradientGraphValue value derivative w⟫_ℝ +
      ⟪closedGradientGraphDerivative value derivative v,
        closedGradientGraphDerivative value derivative w⟫_ℝ := rfl

omit [CompleteSpace H] [CompleteSpace G] in
/-- Every bounded weak-derivative test identity on the smooth graph survives
completion. This is the closure argument used for coordinate weak derivatives. -/
theorem closedGradientGraph_weak_identity
    (value : D →ₗ[ℝ] H) (derivative : D →ₗ[ℝ] G)
    (a : H →L[ℝ] ℝ) (b : G →L[ℝ] ℝ)
    (h : ∀ f : D, a (value f) = b (derivative f))
    (v : closedGradientGraph value derivative) :
    a (closedGradientGraphValue value derivative v) =
      b (closedGradientGraphDerivative value derivative v) := by
  have hs : IsClosed {z : WithLp 2 (H × G) |
      a (WithLp.fstL 2 ℝ H G z) = b (WithLp.sndL 2 ℝ H G z)} :=
    isClosed_eq (a.continuous.comp (WithLp.fstL 2 ℝ H G).continuous)
      (b.continuous.comp (WithLp.sndL 2 ℝ H G).continuous)
  apply hs.closure_subset_iff.mpr ?_ v.property
  rintro z ⟨f, rfl⟩
  exact h f

/-- In a completed gradient graph the abstract energy is literally the
Dirichlet inner product plus the mass times the function inner product. -/
theorem closedGradientGraph_energy (value : D →ₗ[ℝ] H) (derivative : D →ₗ[ℝ] G)
    (mass : ℝ) (v w : closedGradientGraph value derivative) :
    hilbertGraphEnergy (closedGradientGraphValue value derivative) mass v w =
      mass * ⟪closedGradientGraphValue value derivative v,
        closedGradientGraphValue value derivative w⟫_ℝ +
      ⟪closedGradientGraphDerivative value derivative v,
        closedGradientGraphDerivative value derivative w⟫_ℝ := by
  rw [hilbertGraphEnergy_apply, closedGradientGraph_inner]
  ring

/-- The constructed inverse solves the actual graph energy equation for every test. -/
theorem closedGradientGraph_resolvent_weak
    (value : D →ₗ[ℝ] H) (derivative : D →ₗ[ℝ] G)
    {mass : ℝ} (hmass : 1 ≤ mass) (f : H)
    (w : closedGradientGraph value derivative) :
    let J := closedGradientGraphValue value derivative
    let u := hilbertGraphResolventLift J hmass f
    mass * ⟪J u, J w⟫_ℝ +
      ⟪closedGradientGraphDerivative value derivative u,
        closedGradientGraphDerivative value derivative w⟫_ℝ = ⟪f, J w⟫_ℝ := by
  dsimp only
  rw [← closedGradientGraph_energy]
  exact hilbertGraphResolventLift_weak _ hmass f w

/-- The completed graph supplies the resolvent bound, with no additional
contractivity hypothesis on its function projection. -/
theorem closedGradientGraph_resolvent_opNorm_le
    (value : D →ₗ[ℝ] H) (derivative : D →ₗ[ℝ] G)
    {mass : ℝ} (hmass : 1 ≤ mass) :
    ‖hilbertGraphResolvent (closedGradientGraphValue value derivative) hmass‖ ≤ mass⁻¹ :=
  hilbertGraphResolvent_opNorm_le _ (closedGradientGraphValue_norm_le value derivative) hmass

omit [CompleteSpace H] [CompleteSpace G] in
/-- Every completed graph vector has actual smooth approximants whose
function and derivative components converge strongly in their Hilbert norms. -/
theorem closedGradientGraph_exists_smooth_approximation
    (value : D →ₗ[ℝ] H) (derivative : D →ₗ[ℝ] G)
    (v : closedGradientGraph value derivative) :
    ∃ f : ℕ → D,
      Filter.Tendsto (fun n => value (f n)) Filter.atTop
        (nhds (closedGradientGraphValue value derivative v)) ∧
      Filter.Tendsto (fun n => derivative (f n)) Filter.atTop
        (nhds (closedGradientGraphDerivative value derivative v)) := by
  have hv : (v : WithLp 2 (H × G)) ∈
      closure ((smoothGradientGraphMap value derivative).range : Set (WithLp 2 (H × G))) :=
    v.property
  obtain ⟨z, hz, ht⟩ := mem_closure_iff_seq_limit.mp hv
  choose f hf using hz
  have heq : z = fun n => smoothGradientGraphMap value derivative (f n) :=
    funext fun n => (hf n).symm
  rw [heq] at ht
  refine ⟨f, ?_, ?_⟩
  · exact ((WithLp.fstL 2 ℝ H G).continuous.tendsto v.val).comp ht
  · exact ((WithLp.sndL 2 ℝ H G).continuous.tendsto v.val).comp ht

#print axioms closedGradientGraph_weak_identity
#print axioms closedGradientGraph_resolvent_weak
#print axioms closedGradientGraph_resolvent_opNorm_le
#print axioms closedGradientGraph_exists_smooth_approximation

end

end SystolicGrowth
