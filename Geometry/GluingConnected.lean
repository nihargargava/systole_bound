module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarCoordinates
public import Geometry.GluingInteriorCharts
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Piecewise

@[expose] public section

/-!
# Connectivity of the actual retained components and chain

The actual deleted disks have connected frontiers: their frontiers are
the genuine embedded quotient circles. Continuous maps to `Bool` extend
constantly across each disk, proving connectivity of the retained pieces.
No connectivity or frontier identity is postulated in the geometric data.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane Topology

namespace SystolicGrowth

private theorem exists_constant_on_preconnected
    {A : Type*} [TopologicalSpace A] {s : Set A} (hs : IsPreconnected s)
    (f : A → Bool) (hf : ContinuousOn f s) :
    ∃ c : Bool, ∀ x ∈ s, c = f x := by
  rcases s.eq_empty_or_nonempty with h | ⟨a, ha⟩
  · exact ⟨false, by simp [h]⟩
  · exact ⟨f a, fun x hx => hs.constant hf ha hx⟩

private theorem isPreconnected_compl_of_frontier
    {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    {U : Set A} (hU : IsOpen U) (hF : IsPreconnected (frontier U)) :
    IsPreconnected Uᶜ := by
  classical
  apply isPreconnected_of_forall_constant
  intro f hf x hx y hy
  have hsub : frontier U ⊆ Uᶜ := by
    intro a ha
    rw [frontier, hU.interior_eq] at ha
    exact ha.2
  obtain ⟨c, hc⟩ := exists_constant_on_preconnected hF f (hf.mono hsub)
  have hcont : Continuous (U.piecewise (fun _ => c) f) :=
    continuous_piecewise hc continuousOn_const (by
      simpa only [hU.isClosed_compl.closure_eq] using hf)
  have h := PreconnectedSpace.constant (inferInstance : PreconnectedSpace A)
    hcont (x := x) (y := y)
  simpa only [piecewise_eq_of_notMem U _ _ hx, piecewise_eq_of_notMem U _ _ hy] using h

private theorem isPreconnected_compl_union_of_frontiers
    {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    {U V : Set A} (hU : IsOpen U) (hV : IsOpen V)
    (hFU : IsPreconnected (frontier U)) (hFV : IsPreconnected (frontier V))
    (hUV : frontier U ⊆ Vᶜ) : IsPreconnected (U ∪ V)ᶜ := by
  classical
  apply isPreconnected_of_forall_constant
  intro f hf x hx y hy
  have hsub : frontier U ⊆ (U ∪ V)ᶜ := by
    intro a ha
    exact fun h => h.elim
      (fun h => (disjoint_frontier_iff_isOpen.mpr hU).le_bot ⟨ha, h⟩)
      (hUV ha)
  obtain ⟨c, hc⟩ := exists_constant_on_preconnected hFU f (hf.mono hsub)
  have hcont : ContinuousOn (U.piecewise (fun _ => c) f) Vᶜ := by
    apply ContinuousOn.piecewise (fun a ha => hc a ha.2) continuousOn_const
    simpa only [hU.isClosed_compl.closure_eq, compl_union, inter_comm] using hf
  have h := (isPreconnected_compl_of_frontier hV hFV).constant hcont
    (show x ∈ Vᶜ from fun h => hx (Or.inr h))
    (show y ∈ Vᶜ from fun h => hy (Or.inr h))
  simpa only [piecewise_eq_of_notMem U _ _ (fun h => hx (Or.inl h)),
    piecewise_eq_of_notMem U _ _ (fun h => hy (Or.inl h))] using h

namespace ClosedHyperbolicSurface

/-- The original carrier is a quotient of the genuinely connected upper half-plane. -/
instance carrierConnectedSpace {g : ℕ} (X : ClosedHyperbolicSurface g) :
    ConnectedSpace X.Carrier := by
  dsimp only [Carrier]
  infer_instance

end ClosedHyperbolicSurface

/-- The actual centered positive-radius hyperbolic circle is connected. -/
theorem hyperbolic_sphere_isConnected (o : ℍ) {r : ℝ} (hr : 0 < r) :
    IsConnected (sphere o r) := by
  have himage : (fun u : Circle => gluingPolarPoint o u r) '' univ = sphere o r := by
    ext z
    constructor
    · rintro ⟨u, _, rfl⟩
      simpa only [mem_sphere, dist_comm] using dist_gluingPolarPoint o u hr.le
    · intro hz
      have hrad : dist o z = r := by simpa only [mem_sphere, dist_comm] using hz
      let H := gluingPolarCollarHomeomorph o (r / 2) (r + 1) (by linarith)
      let q : GluingPolarAnnulus o (r / 2) (r + 1) := ⟨z, by rw [hrad]; constructor <;> linarith⟩
      have h := congrArg Subtype.val (H.symm_apply_apply q)
      change gluingPolarPoint o (H q).1 (H q).2.1 = z at h
      have hρ : (H q).2.1 = r := hrad
      rw [hρ] at h
      exact ⟨(H q).1, mem_univ _, h⟩
  rw [← himage]
  exact isConnected_univ.image _
    ((gluingPolarPoint_continuous o).comp (continuous_id.prodMk continuous_const)).continuousOn

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The frontier of each actual small orbit disk is exactly its actual quotient circle. -/
theorem frontier_orbitBall_eq_punctureCircle
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ) :
    frontier ((X i).orbitBall o (gluingRadius C g)) =
      (X i).punctureCircle o (gluingRadius C g) := by
  have h2r : 2 * gluingRadius C g < (X i).systole := by
    linarith [P.radius_lt_embeddedRadius, P.twice_outer_lt_systole i]
  have hs : (X i).punctureCircle o (gluingRadius C g) =
      sphere (Quotient.mk'' o : (X i).Carrier) (gluingRadius C g) :=
    (X i).image_quotientMk_sphere_eq_carrier_sphere o _ h2r
  rw [← (X i).carrier_ball_eq_orbitBall, hs]
  refine frontier_ball_subset_sphere.antisymm ?_
  intro q hq
  have hc := punctureCircle_subset_closure_orbitBall (X i) o P.radius_pos (hs.symm ▸ hq)
  rw [← (X i).carrier_ball_eq_orbitBall] at hc
  rw [frontier, isOpen_ball.interior_eq]
  exact ⟨hc, disjoint_left.mp sphere_disjoint_ball hq⟩

theorem punctureCircle_isConnected
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ) :
    IsConnected ((X i).punctureCircle o (gluingRadius C g)) :=
  (hyperbolic_sphere_isConnected o P.radius_pos).image _ continuous_quotient_mk'.continuousOn

/-- Both genuine circle frontiers remain connected in the original carrier topology. -/
theorem frontier_orbitBall_isConnected
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ) :
    IsConnected (frontier ((X i).orbitBall o (gluingRadius C g))) := by
  rw [P.frontier_orbitBall_eq_punctureCircle]
  exact P.punctureCircle_isConnected i o

/-- The prescribed one- or two-disk deletion leaves an actual connected retained set. -/
theorem puncturedComponentSet_isConnected
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    IsConnected ((X i).puncturedComponentSet (P.centers i).1 (P.centers i).2
      (gluingRadius C g) i) := by
  have hleft := P.frontier_orbitBall_isConnected i (P.centers i).1
  have hright := P.frontier_orbitBall_isConnected i (P.centers i).2
  have hUV : frontier ((X i).orbitBall (P.centers i).1 (gluingRadius C g)) ⊆
      ((X i).orbitBall (P.centers i).2 (gluingRadius C g))ᶜ := by
    rw [P.frontier_orbitBall_eq_punctureCircle]
    exact fun q hq => disjoint_left.mp
      ((X i).punctureCollar_left_disjoint_right_inner _ _ _ _ (P.separated_outer_add_inner i))
      ((X i).punctureCircle_subset_collar _ _ _ P.radius_lt_embeddedRadius hq)
  have hpre : IsPreconnected ((X i).puncturedComponentSet
      (P.centers i).1 (P.centers i).2 (gluingRadius C g) i) := by
    unfold ClosedHyperbolicSurface.puncturedComponentSet
      ClosedHyperbolicSurface.punctureDeletedSet
    split_ifs
    · exact isPreconnected_compl_union_of_frontiers
        ((X i).isOpen_orbitBall _ _) ((X i).isOpen_orbitBall _ _)
        hleft.isPreconnected hright.isPreconnected hUV
    · simpa only [union_empty] using isPreconnected_compl_of_frontier
        ((X i).isOpen_orbitBall _ _) hleft.isPreconnected
    · simpa only [empty_union] using isPreconnected_compl_of_frontier
        ((X i).isOpen_orbitBall _ _) hright.isPreconnected
    · simpa only [union_empty, compl_empty] using
        (isPreconnected_univ : IsPreconnected (univ : Set (X i).Carrier))
  let z : sphere (P.centers i).1 (gluingRadius C g) :=
    ⟨gluingPolarPoint (P.centers i).1 1 (gluingRadius C g), by
      simpa only [mem_sphere, dist_comm] using
        dist_gluingPolarPoint (P.centers i).1 1 P.radius_pos.le⟩
  exact ⟨⟨(P.leftCirclePoint i z).1, (P.leftCirclePoint i z).2⟩, hpre⟩

/-- Connectivity is proved for the actual retained subspace, not added to its contract. -/
instance chainComponentConnectedSpace
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ConnectedSpace (P.ChainComponent i) :=
  isConnected_iff_connectedSpace.mp (P.puncturedComponentSet_isConnected i)

/-- The actual finite chain quotient is preconnected, including the empty-chain case. -/
instance gluedCarrierPreconnectedSpace
    (P : ExerciseGluingPreparation C g n genera X) : PreconnectedSpace P.GluedCarrier := by
  classical
  apply preconnectedSpace_of_forall_constant
  intro f hf x y
  have hcomponent (i : Fin n) (a b : P.ChainComponent i) :
      f (P.gluedMk ⟨i, a⟩) = f (P.gluedMk ⟨i, b⟩) :=
    PreconnectedSpace.constant (inferInstance : PreconnectedSpace (P.ChainComponent i))
      ((hf.comp P.gluedMk_continuous).comp continuous_sigmaMk)
  cases n with
  | zero =>
    obtain ⟨a, _⟩ := Quotient.mk_surjective x
    exact Fin.elim0 a.1
  | succ m =>
    let q₀ : P.ChainComponent (0 : Fin (m + 1)) := Classical.choice inferInstance
    have hindex (i : Fin (m + 1)) : ∀ a : P.ChainComponent i,
        f (P.gluedMk ⟨i, a⟩) = f (P.gluedMk ⟨0, q₀⟩) := by
      induction i using Fin.induction with
      | zero =>
        intro a
        exact hcomponent 0 a q₀
      | succ i ih =>
        intro a
        let k : Fin ((m + 1) - 1) := ⟨i.1, by simp⟩
        let z : sphere (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) :=
          ⟨gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2 1 (gluingRadius C g), by
            simpa only [mem_sphere, dist_comm] using
              dist_gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2 1 P.radius_pos.le⟩
        calc
          f (P.gluedMk ⟨i.succ, a⟩) = f (P.gluedMk (P.seamTarget k z)) :=
            hcomponent i.succ a (P.leftCirclePoint _
              (gluingBoundaryCircleIsometry _ _ _ z))
          _ = f (P.gluedMk (P.seamSource k z)) :=
            congrArg f (P.gluedMk_seamSource_eq_seamTarget k z).symm
          _ = f (P.gluedMk ⟨0, q₀⟩) := ih (P.rightCirclePoint _ z)
    obtain ⟨⟨i, a⟩, rfl⟩ := Quotient.mk_surjective x
    obtain ⟨⟨j, b⟩, rfl⟩ := Quotient.mk_surjective y
    exact (hindex i a).trans (hindex j b).symm

/-- A nonempty finite path of actual retained components has connected quotient. -/
theorem gluedCarrierConnectedSpace
    (P : ExerciseGluingPreparation C g n genera X) (hn : 0 < n) :
    ConnectedSpace P.GluedCarrier where
  toPreconnectedSpace := P.gluedCarrierPreconnectedSpace
  toNonempty := by
    let i : Fin n := ⟨0, hn⟩
    let q : P.ChainComponent i := Classical.choice inferInstance
    exact ⟨P.gluedMk ⟨i, q⟩⟩

end ExerciseGluingPreparation

#print axioms hyperbolic_sphere_isConnected
#print axioms ExerciseGluingPreparation.frontier_orbitBall_eq_punctureCircle
#print axioms ExerciseGluingPreparation.puncturedComponentSet_isConnected
#print axioms ExerciseGluingPreparation.chainComponentConnectedSpace
#print axioms ExerciseGluingPreparation.gluedCarrierPreconnectedSpace
#print axioms ExerciseGluingPreparation.gluedCarrierConnectedSpace

end SystolicGrowth
