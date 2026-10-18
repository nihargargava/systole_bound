module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingSeamHomotopy
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

/-!
# The based fundamental group of an actual seam neighborhood

The native radial homotopy fixes the included circle, so the induced
retraction and inclusion are inverse based group maps, without a change of
basepoint. Mathlib's real exponential quotient covering identifies the
circle group with the opposite of `Multiplicative ℤ`; its positive one-turn
loop maps to the positive generator. The native generator is the original
outgoing polar boundary, and the identified incoming boundary has inverse
angular coordinate. No surface genus or van Kampen conclusion is assumed.
-/

open Set
open scoped ContinuousMap unitInterval

namespace SystolicGrowth

noncomputable section

def Internal.GluingSeamFundamentalGroupHelpers.circleDeckIntegerEquiv : AddSubgroup.zmultiples (2 * Real.pi) ≃+ ℤ :=
  (AddEquiv.ofBijective
    ((zmultiplesHom ℝ (2 * Real.pi)).codRestrict _
      (AddSubgroup.zsmul_mem_zmultiples (2 * Real.pi))) (by
        constructor
        · intro m n h
          have h' : (m : ℝ) * (2 * Real.pi) = (n : ℝ) * (2 * Real.pi) := by
            have hv := congrArg Subtype.val h
            change m • (2 * Real.pi) = n • (2 * Real.pi) at hv
            simpa only [zsmul_eq_mul] using hv
          have h'' : (m : ℝ) = (n : ℝ) := (mul_left_inj' Real.two_pi_pos.ne').mp h'
          exact_mod_cast h''
        · rintro ⟨x, n, hn⟩
          exact ⟨n, Subtype.ext hn⟩)).symm

/-- The actual exponential covering gives the circle's based fundamental
group its integer marking. The opposite records Mathlib's loop convention. -/
def circleFundamentalGroupEquivIntegers (θ : Circle) :
    FundamentalGroup Circle θ ≃* (Multiplicative ℤ)ᵐᵒᵖ :=
  (Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
    ⟨(θ : ℂ).arg, Circle.exp_arg θ⟩).trans
      (MulEquiv.op (AddEquiv.toMultiplicative Internal.GluingSeamFundamentalGroupHelpers.circleDeckIntegerEquiv))

/-- The genuine positively oriented one-turn loop, based at the given angle. -/
def circleOneTurnLoop (θ : Circle) : Path θ θ :=
  ((Path.segment (θ : ℂ).arg ((θ : ℂ).arg + 2 * Real.pi)).map Circle.exp.continuous).cast
    (Circle.exp_arg θ).symm (by rw [Circle.exp_add_two_pi, Circle.exp_arg])

/-- The loop follows the actual angle `arg θ + 2πt`. -/
theorem circleOneTurnLoop_apply (θ : Circle) (t : unitInterval) :
    circleOneTurnLoop θ t = Circle.exp ((θ : ℂ).arg + 2 * Real.pi * (t : ℝ)) := by
  change Circle.exp (AffineMap.lineMap (θ : ℂ).arg
    ((θ : ℂ).arg + 2 * Real.pi) (t : ℝ)) = _
  congr 1
  simp only [AffineMap.lineMap_apply, smul_eq_mul, vsub_eq_sub, vadd_eq_add]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The real lift ends exactly one positive period above its initial point. -/
theorem circleFundamentalGroupEquivIntegers_oneTurn (θ : Circle) :
    circleFundamentalGroupEquivIntegers θ ⟦circleOneTurnLoop θ⟧ =
      MulOpposite.op (Multiplicative.ofAdd (1 : ℤ)) := by
  let e : Circle.exp ⁻¹' {θ} := ⟨(θ : ℂ).arg, Circle.exp_arg θ⟩
  let e' : Circle.exp ⁻¹' {θ} :=
    ⟨(θ : ℂ).arg + 2 * Real.pi, by
      change Circle.exp ((θ : ℂ).arg + 2 * Real.pi) = θ
      rw [Circle.exp_add_two_pi, Circle.exp_arg]⟩
  let γ : FundamentalGroup Circle θ := ⟦circleOneTurnLoop θ⟧
  have hmono : Circle.isCoveringMap_exp.monodromy γ e = e' :=
    Circle.isCoveringMap_exp.monodromy_eq_of_map_eq ⟦Path.segment e.1 e'.1⟧ rfl
  let period : AddSubgroup.zmultiples (2 * Real.pi) :=
    ⟨2 * Real.pi, AddSubgroup.mem_zmultiples _⟩
  have hcover : Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv e γ =
      MulOpposite.op (Multiplicative.ofAdd period) := by
    change Circle.isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite e γ = _
    rw [IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff, hmono]
    change (2 * Real.pi) + (θ : ℂ).arg = (θ : ℂ).arg + 2 * Real.pi
    exact add_comm _ _
  have hperiod : Internal.GluingSeamFundamentalGroupHelpers.circleDeckIntegerEquiv period = 1 := by
    apply Internal.GluingSeamFundamentalGroupHelpers.circleDeckIntegerEquiv.symm.injective
    rw [AddEquiv.symm_apply_apply]
    apply Subtype.ext
    change 2 * Real.pi = (1 : ℤ) • (2 * Real.pi)
    simp
  change (MulEquiv.op (AddEquiv.toMultiplicative Internal.GluingSeamFundamentalGroupHelpers.circleDeckIntegerEquiv))
    (Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv e γ) = _
  rw [hcover]
  change MulOpposite.op (Multiplicative.ofAdd (Internal.GluingSeamFundamentalGroupHelpers.circleDeckIntegerEquiv period)) = _
  rw [hperiod]

/-- The inverse angular parametrization of the positive one-turn based at
`1` is precisely its reverse path. -/
theorem circleOneTurnLoop_one_inverse_eq_symm :
    (circleOneTurnLoop (1 : Circle)).map
        (continuous_inv : Continuous fun z : Circle => z⁻¹) =
      (circleOneTurnLoop 1).symm.cast (by simp) (by simp) := by
  apply Path.ext
  funext t
  simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, Path.symm_apply]
  rw [circleOneTurnLoop_apply, circleOneTurnLoop_apply]
  have harg : ((1 : Circle) : ℂ).arg = 0 := by norm_num
  rw [harg, zero_add]
  rw [unitInterval.coe_symm_eq t]
  rw [← Circle.exp_neg]
  rw [show 2 * Real.pi * (1 - (t : ℝ)) = -(2 * Real.pi * (t : ℝ)) + 2 * Real.pi by ring,
    zero_add, Circle.exp_add_two_pi]

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual open seam neighborhood is path connected, as its proved
signed-cylinder homeomorphism has a connected interval factor. -/
theorem gluedSeamNeighborhood_isPathConnected
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsPathConnected (P.gluedMk '' P.seamNeighborhood k) := by
  have hinterval : IsPathConnected (Ioo (-gluingDepth C g) (gluingDepth C g)) :=
    (convex_Ioo _ _).isPathConnected ⟨0, neg_lt_zero.mpr P.depth_pos, P.depth_pos⟩
  letI : PathConnectedSpace (Ioo (-gluingDepth C g) (gluingDepth C g)) :=
    isPathConnected_iff_pathConnectedSpace.mp hinterval
  exact isPathConnected_iff_pathConnectedSpace.mpr
    ((P.seamCylinderHomeomorph k).surjective.pathConnectedSpace
      (P.seamCylinderHomeomorph k).continuous)

theorem Internal.GluingSeamFundamentalGroupHelpers.retract_include_loop (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : Circle) (p : Path θ θ) :
    ((p.map (P.gluedSeamCircleInclusion k).continuous).map
      (P.gluedSeamCircleRetraction k).continuous).cast
        (P.gluedSeamCircleRetraction_inclusion k θ).symm
        (P.gluedSeamCircleRetraction_inclusion k θ).symm = p := by
  apply Path.ext
  funext t
  exact P.gluedSeamCircleRetraction_inclusion k (p t)

theorem Internal.GluingSeamFundamentalGroupHelpers.include_retract_loop (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : Circle)
    (p : Path (P.gluedSeamCircleInclusion k θ) (P.gluedSeamCircleInclusion k θ)) :
    (((p.map (P.gluedSeamCircleRetraction k).continuous).cast
      (P.gluedSeamCircleRetraction_inclusion k θ).symm
      (P.gluedSeamCircleRetraction_inclusion k θ).symm).map
        (P.gluedSeamCircleInclusion k).continuous).Homotopic p := by
  refine ⟨{
    toFun := fun q => P.gluedSeamRadialHomotopy k (q.1, p q.2)
    continuous_toFun := (P.gluedSeamRadialHomotopy k).continuous.comp
      (continuous_fst.prodMk (p.continuous.comp continuous_snd))
    map_zero_left := by intro t; simp
    map_one_left := by intro t; simp
    prop' := ?_
  }⟩
  intro t u hu
  rcases hu with hu | hu
  · subst u
    simp
  · have hu : u = 1 := by simpa using hu
    subst u
    simp

/-- The based equivalence uses exactly the native circle retraction forward
and native inclusion backward. Their homotopies fix the actual basepoint. -/
def gluedSeamCircleFundamentalGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    FundamentalGroup ↥(P.gluedMk '' P.seamNeighborhood k) (P.gluedSeamCircleInclusion k θ) ≃*
      FundamentalGroup Circle θ where
  toFun := FundamentalGroup.mapOfEq (P.gluedSeamCircleRetraction k)
    (P.gluedSeamCircleRetraction_inclusion k θ)
  invFun := FundamentalGroup.map (P.gluedSeamCircleInclusion k) θ
  left_inv := by
    intro γ
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
      ← Path.Homotopic.Quotient.mk_map, Path.Homotopic.Quotient.eq]
    exact Internal.GluingSeamFundamentalGroupHelpers.include_retract_loop P k θ p
  right_inv := by
    intro γ
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_cast, Internal.GluingSeamFundamentalGroupHelpers.retract_include_loop]
  map_mul' := (FundamentalGroup.mapOfEq (P.gluedSeamCircleRetraction k)
    (P.gluedSeamCircleRetraction_inclusion k θ)).map_mul

theorem gluedSeamCircleFundamentalGroupEquiv_toMonoidHom
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    (P.gluedSeamCircleFundamentalGroupEquiv k θ).toMonoidHom =
      FundamentalGroup.mapOfEq (P.gluedSeamCircleRetraction k)
        (P.gluedSeamCircleRetraction_inclusion k θ) := rfl

theorem gluedSeamCircleFundamentalGroupEquiv_symm_toMonoidHom
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    (P.gluedSeamCircleFundamentalGroupEquiv k θ).symm.toMonoidHom =
      FundamentalGroup.map (P.gluedSeamCircleInclusion k) θ := rfl

/-- Every circle loop retains its exact based class under inclusion followed
by the actual seam-neighborhood group marking. -/
@[simp] theorem gluedSeamCircleFundamentalGroupEquiv_map_loop
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle)
    (p : Path θ θ) :
    P.gluedSeamCircleFundamentalGroupEquiv k θ
      ⟦p.map (P.gluedSeamCircleInclusion k).continuous⟧ = ⟦p⟧ :=
  (P.gluedSeamCircleFundamentalGroupEquiv k θ).apply_symm_apply ⟦p⟧

/-- The actual based one-turn boundary loop in the original seam neighborhood. -/
def gluedSeamOneTurnLoop
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    Path (P.gluedSeamCircleInclusion k θ) (P.gluedSeamCircleInclusion k θ) :=
  (circleOneTurnLoop θ).map (P.gluedSeamCircleInclusion k).continuous

/-- The native generator has exactly the original outgoing polar boundary
representative at every time, including both endpoints. -/
theorem gluedSeamOneTurnLoop_apply_outgoing
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (θ : Circle) (t : unitInterval) :
    P.gluedSeamOneTurnLoop k θ t = P.seamNeighborhoodProjection k
      ⟨P.seamOutgoingPolarPoint k
          (circleOneTurnLoop θ t,
            ⟨gluingRadius C g, le_rfl, P.radius_lt_embeddedRadius⟩),
        P.seamOutgoingPolarPoint_mem k _⟩ :=
  P.gluedSeamCircleInclusion_eq_outgoing k (circleOneTurnLoop θ t)

/-- The very same loop is represented on the incoming boundary by the
inverse angular coordinate, as prescribed by the original gluing. -/
theorem gluedSeamOneTurnLoop_apply_incoming
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (θ : Circle) (t : unitInterval) :
    P.gluedSeamOneTurnLoop k θ t = P.seamNeighborhoodProjection k
      ⟨P.seamIncomingPolarPoint k
          ((circleOneTurnLoop θ t)⁻¹,
            ⟨gluingRadius C g, le_rfl, P.radius_lt_embeddedRadius⟩),
        P.seamIncomingPolarPoint_mem k _⟩ := by
  rw [P.gluedSeamOneTurnLoop_apply_outgoing k θ t]
  exact Subtype.ext (P.seamPolarBoundary_eq k (circleOneTurnLoop θ t))

/-- The literal positive incoming polar circle of a retained component,
included into the original quotient. This avoids replacing the carrier by a
collar model. -/
noncomputable def retainedLeftPolarSphereMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    C(Circle, Metric.sphere (P.centers i).1 (gluingRadius C g)) := by
  refine ⟨fun θ => ⟨gluingPolarPoint (P.centers i).1 θ (gluingRadius C g), ?_⟩, ?_⟩
  · rw [Metric.mem_sphere, dist_comm,
      dist_gluingPolarPoint _ θ P.radius_pos.le]
  · have hθ : Continuous (fun θ : Circle => (θ, gluingRadius C g)) :=
      continuous_id.prodMk continuous_const
    exact ((gluingPolarPoint_continuous (P.centers i).1).comp hθ).subtype_mk
      (fun θ => by
        simp only [Function.comp_apply]
        rw [Metric.mem_sphere, dist_comm,
          dist_gluingPolarPoint _ θ P.radius_pos.le])

/-- The original positive incoming boundary circle, included through the
retained chain component into the literal glued carrier. -/
noncomputable def gluedIncomingRetainedPolarBoundaryMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    C(Circle, P.GluedCarrier) := by
  let s := P.retainedLeftPolarSphereMap i
  exact ⟨fun θ => P.gluedMk ⟨i, P.leftCirclePoint i (s θ)⟩,
    P.gluedMk_continuous.comp (continuous_sigmaMk.comp
      ((P.leftCirclePoint_isEmbedding i).continuous.comp s.continuous))⟩

/-- The seam's incoming collar point on the inner circle is exactly the
original retained left-circle point in the next component. -/
private theorem seamIncomingPolarPoint_eq_leftCirclePoint
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (u : Circle) :
    P.seamIncomingPolarPoint k
        (u, ⟨gluingRadius C g, le_rfl, P.radius_lt_embeddedRadius⟩) =
      ⟨gluingChainEdgeRight k,
        P.leftCirclePoint (gluingChainEdgeRight k)
          ⟨gluingPolarPoint (P.centers (gluingChainEdgeRight k)).1 u
              (gluingRadius C g), by
            rw [Metric.mem_sphere, dist_comm,
              dist_gluingPolarPoint _ u P.radius_pos.le]⟩⟩ := by
  unfold seamIncomingPolarPoint
  apply congrArg (Sigma.mk (gluingChainEdgeRight k))
  apply Subtype.ext
  change (Quotient.mk'' (gluingPolarPoint (P.centers (gluingChainEdgeRight k)).1
      u (gluingRadius C g)) : (X (gluingChainEdgeRight k)).Carrier) =
    Quotient.mk'' (gluingPolarPoint (P.centers (gluingChainEdgeRight k)).1
      u (gluingRadius C g))
  rfl

theorem gluedSeamCircleInclusion_one_eq_incomingRetainedBasepoint
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    (P.gluedSeamCircleInclusion k 1).1 =
      P.gluedIncomingRetainedPolarBoundaryMap (gluingChainEdgeRight k) 1 := by
  rw [P.gluedSeamCircleInclusion_eq_outgoing]
  change P.gluedMk (P.seamOutgoingPolarPoint k
    (1, ⟨gluingRadius C g, le_rfl, P.radius_lt_embeddedRadius⟩)) = _
  rw [P.seamPolarBoundary_eq k 1]
  rw [inv_one]
  rw [seamIncomingPolarPoint_eq_leftCirclePoint]
  rfl

/-- The incoming seam one-turn, included into the whole glued carrier, is
the reverse of the original positive retained incoming one-turn. -/
theorem gluedSeamOneTurnLoop_map_eq_incomingRetainedPolarBoundaryLoop_symm
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    (P.gluedSeamOneTurnLoop k 1).map continuous_subtype_val =
      (((circleOneTurnLoop 1).map
        (P.gluedIncomingRetainedPolarBoundaryMap (gluingChainEdgeRight k)).continuous).symm).cast
          (P.gluedSeamCircleInclusion_one_eq_incomingRetainedBasepoint k)
          (P.gluedSeamCircleInclusion_one_eq_incomingRetainedBasepoint k) := by
  apply Path.ext
  funext t
  simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, Path.symm_apply]
  rw [P.gluedSeamOneTurnLoop_apply_incoming k 1 t]
  simp only [seamNeighborhoodProjection]
  rw [seamIncomingPolarPoint_eq_leftCirclePoint]
  have ht : (circleOneTurnLoop 1 t)⁻¹ = circleOneTurnLoop 1 (σ t) := by
    have h := congrArg (fun p : Path (1⁻¹) (1⁻¹) => p t)
      circleOneTurnLoop_one_inverse_eq_symm
    simpa only [Path.cast_coe, Path.map_coe, Function.comp_apply,
      Path.symm_apply] using h
  change P.gluedIncomingRetainedPolarBoundaryMap (gluingChainEdgeRight k)
      ((circleOneTurnLoop 1 t)⁻¹) =
    P.gluedIncomingRetainedPolarBoundaryMap (gluingChainEdgeRight k)
      (circleOneTurnLoop 1 (σ t))
  exact congrArg (P.gluedIncomingRetainedPolarBoundaryMap (gluingChainEdgeRight k)) ht

/-- The same incoming orientation identity at the level of actual based
fundamental-group classes in the glued carrier. -/
theorem gluedSeamOneTurnLoop_map_class_eq_incomingRetainedPolarBoundaryLoop_symm
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    (⟦(P.gluedSeamOneTurnLoop k 1).map continuous_subtype_val⟧ :
      FundamentalGroup P.GluedCarrier ((P.gluedSeamCircleInclusion k 1).1)) =
    (⟦(((circleOneTurnLoop 1).map
      (P.gluedIncomingRetainedPolarBoundaryMap (gluingChainEdgeRight k)).continuous).symm).cast
        (P.gluedSeamCircleInclusion_one_eq_incomingRetainedBasepoint k)
        (P.gluedSeamCircleInclusion_one_eq_incomingRetainedBasepoint k)⟧ :
      FundamentalGroup P.GluedCarrier ((P.gluedSeamCircleInclusion k 1).1)) := by
  exact congrArg (fun p : Path ((P.gluedSeamCircleInclusion k 1).1)
      ((P.gluedSeamCircleInclusion k 1).1) => ⟦p⟧)
    (P.gluedSeamOneTurnLoop_map_eq_incomingRetainedPolarBoundaryLoop_symm k)

/-- The actual seam-neighborhood fundamental group is explicitly infinite
cyclic, with its original included circle as the marking. -/
def gluedSeamFundamentalGroupEquivIntegers
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    FundamentalGroup ↥(P.gluedMk '' P.seamNeighborhood k) (P.gluedSeamCircleInclusion k θ) ≃*
      (Multiplicative ℤ)ᵐᵒᵖ :=
  (P.gluedSeamCircleFundamentalGroupEquiv k θ).trans (circleFundamentalGroupEquivIntegers θ)

/-- The actual outgoing one-turn boundary loop maps to the positive integer
generator, not an unspecified generator of an abstract cyclic group. -/
@[simp] theorem gluedSeamFundamentalGroupEquivIntegers_oneTurn
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    P.gluedSeamFundamentalGroupEquivIntegers k θ ⟦P.gluedSeamOneTurnLoop k θ⟧ =
      MulOpposite.op (Multiplicative.ofAdd (1 : ℤ)) := by
  change circleFundamentalGroupEquivIntegers θ
    (P.gluedSeamCircleFundamentalGroupEquiv k θ
      ⟦(circleOneTurnLoop θ).map (P.gluedSeamCircleInclusion k).continuous⟧) = _
  rw [P.gluedSeamCircleFundamentalGroupEquiv_map_loop,
    circleFundamentalGroupEquivIntegers_oneTurn]

#print axioms circleOneTurnLoop_one_inverse_eq_symm
#print axioms ExerciseGluingPreparation.gluedSeamOneTurnLoop_map_eq_incomingRetainedPolarBoundaryLoop_symm
#print axioms ExerciseGluingPreparation.gluedSeamOneTurnLoop_map_class_eq_incomingRetainedPolarBoundaryLoop_symm

end ExerciseGluingPreparation

end

end SystolicGrowth
