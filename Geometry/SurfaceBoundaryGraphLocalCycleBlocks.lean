module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceBoundaryGraphVertexCycleAdapter

@[expose] public section

/-!
# Actual local blocks for quotient vertices

At a quotient vertex, the complete Dirichlet contact cycle gives a concrete
list of the actual terminal side darts. The endpoint orientation chooses
either the displayed native sides or their actual paired orientations.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane Classical

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

private theorem contact_side_index_periodic
    (B : DirichletBoundarySegments X o)
    {n : ℕ} {e : ℕ → X.deckGroup}
    (hperiodic : ∀ k, e (k + n) = e k)
    {s : ℕ → Fin B.intrinsicBoundaryRadialCuts.card}
    (hsideLabel : ∀ k,
      (B.intrinsicCyclicEdge (s k)).1.1.1 = (e k)⁻¹ * e (k + 1)) :
    ∀ k, s (k + n) = s k := by
  intro k
  apply B.intrinsicCyclicEdge_label_injective
  calc
    (B.intrinsicCyclicEdge (s (k + n))).1.1.1 = (e (k + n))⁻¹ * e (k + n + 1) :=
      hsideLabel (k + n)
    _ = (e k)⁻¹ * e (k + 1) := by
      rw [hperiodic k, show k + n + 1 = (k + 1) + n by omega, hperiodic (k + 1)]
    _ = (B.intrinsicCyclicEdge (s k)).1.1.1 := (hsideLabel k).symm

private theorem contact_side_index_mod_periodic
    (B : DirichletBoundarySegments X o)
    {n : ℕ} {e : ℕ → X.deckGroup}
    (hperiodic : ∀ k, e (k + n) = e k)
    {s : ℕ → Fin B.intrinsicBoundaryRadialCuts.card}
    (hsideLabel : ∀ k,
      (B.intrinsicCyclicEdge (s k)).1.1.1 = (e k)⁻¹ * e (k + 1)) :
    ∀ k, s k = s (k % n) := by
  intro k
  conv_lhs => rw [show k = k % n + n * (k / n) from (Nat.mod_add_div k n).symm]
  have hperiodicSide := contact_side_index_periodic B hperiodic hsideLabel
  have hmain : ∀ q, s (k % n + n * q) = s (k % n) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, hperiodicSide, ih]
  exact hmain (k / n)

private theorem formPerm_ofFn_apply
    {α : Type*} [DecidableEq α] {n : ℕ} (f : Fin n → α)
    (hnodup : (List.ofFn f).Nodup) (i : Fin n) :
    (List.ofFn f).formPerm (f i) = f (finRotate n i) := by
  classical
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    exact Fin.elim0 i
  letI : NeZero n := ⟨hn.ne'⟩
  let l := List.ofFn f
  have hlen : l.length = n := by simp [l]
  have hi : i.val < l.length := by rw [hlen]; exact i.isLt
  have hstep := List.formPerm_apply_getElem l hnodup i.val hi
  have hleft : l[i.val] = f i := by simp [l]
  have hmod : (i.val + 1) % l.length < l.length := Nat.mod_lt _ (by omega)
  have hright : l[(i.val + 1) % l.length]'hmod = f (finRotate n i) := by
    simp only [l, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp [finRotate_apply, Fin.add_def]
  rw [hleft, hright] at hstep
  exact hstep

private theorem formPerm_reverse_ofFn_apply
    {α : Type*} [DecidableEq α] {n : ℕ} (f : Fin n → α)
    (hnodup : (List.ofFn f).Nodup) (i : Fin n) :
    ((List.ofFn f).reverse).formPerm (f i) =
      f ((finRotate n).symm i) := by
  classical
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    exact Fin.elim0 i
  letI : NeZero n := ⟨hn.ne'⟩
  have hreverse : ((List.ofFn f).reverse).formPerm =
      ((List.ofFn f).formPerm).symm := by
    rw [List.formPerm_reverse]
    exact Equiv.ext (fun _ => rfl)
  rw [hreverse]
  have hstep := formPerm_ofFn_apply f hnodup ((finRotate n).symm i)
  rw [Equiv.apply_symm_apply] at hstep
  rw [← hstep]
  exact Equiv.symm_apply_apply _ _

private theorem contact_side_index_injective_of_endpoint_orientation
    (B : DirichletBoundarySegments X o) {v : ℍ}
    {n : ℕ} {e : ℕ → X.deckGroup} {s : ℕ → Fin B.intrinsicBoundaryRadialCuts.card}
    (hcontact : ∀ k, e k ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v)
    (huniq : ∀ γ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v,
      ∃! k, k < n ∧ γ • o = e k • o)
    (hendpoint : ∀ k,
      (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k) ∨
        (e k)⁻¹ • v = B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card (s k)))
    (horientation : ∀ k,
      ((e k)⁻¹ • v = B.intrinsicCyclicVertex (s k)) ↔
        ((e 0)⁻¹ • v = B.intrinsicCyclicVertex (s 0)))
    {a b : ℕ} (ha : a < n) (hb : b < n) (hab : s a = s b) : a = b := by
  classical
  have heq : e a = e b := by
    by_cases hstart0 : (e 0)⁻¹ • v = B.intrinsicCyclicVertex (s 0)
    · have hpointA : (e a)⁻¹ • v = B.intrinsicCyclicVertex (s a) :=
        (horientation a).mpr hstart0
      have hpointB : (e b)⁻¹ • v = B.intrinsicCyclicVertex (s a) := by
        rw [(horientation b).mpr hstart0, hab]
      have hactB : e b • B.intrinsicCyclicVertex (s a) = v := by
        calc
          e b • B.intrinsicCyclicVertex (s a) =
              e b • ((e b)⁻¹ • v) := congrArg (fun z => e b • z) hpointB.symm
          _ = v := by rw [smul_inv_smul]
      have hfix : ((e a)⁻¹ * e b) • B.intrinsicCyclicVertex (s a) =
          B.intrinsicCyclicVertex (s a) := by
        rw [mul_smul]
        calc
          (e a)⁻¹ • (e b • B.intrinsicCyclicVertex (s a)) = (e a)⁻¹ • v :=
            congrArg (fun z => (e a)⁻¹ • z) hactB
          _ = B.intrinsicCyclicVertex (s a) := hpointA
      have htrivial := X.free ((e a)⁻¹ * e b) _ hfix
      exact inv_mul_eq_one.mp htrivial
    · have htailA : (e a)⁻¹ • v = B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card (s a)) := by
        rcases hendpoint a with h | h
        · exact False.elim (hstart0 ((horientation a).mp h))
        · exact h
      have htailB : (e b)⁻¹ • v = B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card (s a)) := by
        rcases hendpoint b with h | h
        · exact False.elim (hstart0 ((horientation b).mp h))
        · rw [← hab] at h
          exact h
      have hactB : e b • B.intrinsicCyclicVertex
            (finRotate B.intrinsicBoundaryRadialCuts.card (s a)) = v := by
        calc
          e b • B.intrinsicCyclicVertex (finRotate _ (s a)) =
              e b • ((e b)⁻¹ • v) := congrArg (fun z => e b • z) htailB.symm
          _ = v := by rw [smul_inv_smul]
      have hfix : ((e a)⁻¹ * e b) •
          B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card (s a)) =
          B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card (s a)) := by
        rw [mul_smul]
        calc
          (e a)⁻¹ • (e b • B.intrinsicCyclicVertex (finRotate _ (s a))) = (e a)⁻¹ • v :=
            congrArg (fun z => (e a)⁻¹ • z) hactB
          _ = B.intrinsicCyclicVertex (finRotate _ (s a)) := htailA
      have htrivial := X.free ((e a)⁻¹ * e b) _ hfix
      exact inv_mul_eq_one.mp htrivial
  obtain ⟨r, hr, hrunique⟩ := huniq (e a) (hcontact a)
  have hra : a = r := hrunique a ⟨ha, rfl⟩
  have hrb : b = r := hrunique b ⟨hb, by rw [heq]⟩
  exact hra.trans hrb.symm

private theorem contact_cycle_terminal_fiber_occurrence
    (B : DirichletBoundarySegments X o) (j : Fin B.intrinsicBoundaryRadialCuts.card)
    {v : ℍ}
    (hv : v ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o)
    (hj : v = B.intrinsicCyclicVertex
      (finRotate B.intrinsicBoundaryRadialCuts.card j))
    {n : ℕ} {e : ℕ → X.deckGroup} {s : ℕ → Fin B.intrinsicBoundaryRadialCuts.card}
    (hn : 3 ≤ n)
    (hperiodic : ∀ k, e (k + n) = e k)
    (hcontact : ∀ k, e k ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v)
    (huniq : ∀ γ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v,
      ∃! k, k < n ∧ γ • o = e k • o)
    (hadjacent : ∀ k, Vendored.RiemannDynamics.IsSideElement X.deckGroup o
      ((e k)⁻¹ * e (k + 1)))
    (hsideLabel : ∀ k,
      (B.intrinsicCyclicEdge (s k)).1.1.1 = (e k)⁻¹ * e (k + 1))
    (hendpoint : ∀ k,
      (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k) ∨
        (e k)⁻¹ • v = B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card (s k)))
    (horientation : ∀ k,
      ((e k)⁻¹ • v = B.intrinsicCyclicVertex (s k)) ↔
        ((e 0)⁻¹ • v = B.intrinsicCyclicVertex (s 0)))
    (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (hfiber : B.intrinsicBoundaryGraphSideEnd i =
      B.intrinsicBoundaryGraphSideEnd j) :
    if (e 0)⁻¹ • v = B.intrinsicCyclicVertex (s 0) then
      ∃ k, k < n ∧ i = B.intrinsicCyclicPairing (s k)
    else ∃ k, k < n ∧ i = s k := by
  classical
  let xi := B.intrinsicCyclicVertex
    (finRotate B.intrinsicBoundaryRadialCuts.card i)
  have hquot : Quotient.mk B.intrinsicBoundaryGraphVertexSetoid
        (finRotate B.intrinsicBoundaryRadialCuts.card i) =
      Quotient.mk B.intrinsicBoundaryGraphVertexSetoid
        (finRotate B.intrinsicBoundaryRadialCuts.card j) := by
    simpa [intrinsicBoundaryGraphSideEnd, intrinsicBoundaryGraphSideStart] using hfiber
  obtain ⟨γ, hγxi⟩ :=
    (B.intrinsicBoundaryGraphVertexSetoid_iff _ _).mp (Quotient.exact hquot)
  have hγv : γ • xi = v := by
    calc
      γ • xi = γ • B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card i) := rfl
      _ = B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card j) := hγxi
      _ = v := hj.symm
  let sideLabel := (B.intrinsicCyclicEdge i).1.1.1
  have hxiSide : xi ∈
      Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o sideLabel := by
    dsimp [xi, sideLabel]
    rw [← B.intrinsicCyclicClosedEdge_eq_dirichletSideSet i,
      B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
    exact Vendored.RiemannDynamics.right_mem_geodSeg _ _
  have hxiDomain : xi ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := hxiSide.1
  have hLabelContact : sideLabel ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o xi :=
    Vendored.RiemannDynamics.mem_contactSet_of_mem_sideSet hxiSide
  have hγcontact : γ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v := by
    have h := (Vendored.RiemannDynamics.contact_shift γ 1 xi).mp
      (Vendored.RiemannDynamics.one_mem_contactSet hxiDomain)
    simpa only [mul_one, hγv] using h
  have hγLabelContact : γ * sideLabel ∈
      Vendored.RiemannDynamics.contactSet X.deckGroup o v := by
    have h := (Vendored.RiemannDynamics.contact_shift γ sideLabel xi).mp hLabelContact
    simpa only [hγv] using h
  obtain ⟨a, ha, huniqCenter⟩ := huniq γ hγcontact
  have hea : e a = γ := X.deck_smul_injective o ha.2.symm
  have hrelative : (e a)⁻¹ * (γ * sideLabel) = sideLabel := by
    rw [hea]
    group
  have hrelativeSide : Vendored.RiemannDynamics.IsSideElement X.deckGroup o
      ((e a)⁻¹ * (γ * sideLabel)) := by
    rw [hrelative]
    exact B.intrinsicCyclicEdge_isSideElement i
  have hneighbor := contact_side_neighbor_of_cycle hv hn hperiodic hcontact huniq
    hadjacent ha.1 hγLabelContact hrelativeSide
  have hγinv : (e a)⁻¹ • v =
      B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i) := by
    calc
      (e a)⁻¹ • v = γ⁻¹ • v := by rw [hea]
      _ = γ⁻¹ • (γ • xi) := congrArg (fun z => γ⁻¹ • z) hγv.symm
      _ = xi := by rw [inv_smul_smul]
  have hperiodicSide := contact_side_index_periodic B hperiodic hsideLabel
  have hmodSide := contact_side_index_mod_periodic B hperiodic hsideLabel
  by_cases hstart0 : (e 0)⁻¹ • v = B.intrinsicCyclicVertex (s 0)
  · rw [if_pos hstart0]
    rcases hneighbor with hforward | hback
    · have hLabelForward : sideLabel = (e a)⁻¹ * e (a + 1) := by
        calc
          sideLabel = γ⁻¹ * (γ * sideLabel) := by group
          _ = γ⁻¹ * e (a + 1) := by rw [hforward]
          _ = (e a)⁻¹ * e (a + 1) := by rw [hea]
      have hindex : s a = i := B.intrinsicCyclicEdge_label_injective <| by
        calc
          (B.intrinsicCyclicEdge (s a)).1.1.1 = (e a)⁻¹ * e (a + 1) := hsideLabel a
          _ = sideLabel := hLabelForward.symm
          _ = (B.intrinsicCyclicEdge i).1.1.1 := rfl
      have hstartA := (horientation a).mpr hstart0
      have hγinv' : (e a)⁻¹ • v = B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card (s a)) := by
        simpa only [hindex] using hγinv
      have hcontra := hstartA.symm.trans hγinv'
      exact False.elim (B.intrinsicCyclicVertex_next_ne (s a) hcontra)
    · let prev := a + (n - 1)
      have hprev_next : prev + 1 = a + n := by dsimp [prev]; omega
      have hprev_center : e (prev + 1) = e a := by rw [hprev_next, hperiodic]
      have hLabelBack : sideLabel = (e a)⁻¹ * e prev := by
        calc
          sideLabel = γ⁻¹ * (γ * sideLabel) := by group
          _ = γ⁻¹ * e prev := by rw [hback]
          _ = (e a)⁻¹ * e prev := by rw [hea]
      have hpreviousLabel : (B.intrinsicCyclicEdge (s prev)).1.1.1 = sideLabel⁻¹ := by
        rw [hsideLabel prev, hprev_center, hLabelBack]
        group
      have hpairedLabel :
          (B.intrinsicCyclicEdge (B.intrinsicCyclicPairing (s prev))).1.1.1 = sideLabel := by
        rw [B.intrinsicCyclicEdge_pairing, B.inverseIntrinsicOpenEdge_label,
          hpreviousLabel]
        simp
      have hpaired : B.intrinsicCyclicPairing (s prev) = i :=
        B.intrinsicCyclicEdge_label_injective (by
          simpa [sideLabel] using hpairedLabel)
      refine ⟨prev % n, Nat.mod_lt _ (by omega), ?_⟩
      calc
        i = B.intrinsicCyclicPairing (s prev) := hpaired.symm
        _ = B.intrinsicCyclicPairing (s (prev % n)) := by rw [hmodSide prev]
  · rw [if_neg hstart0]
    rcases hneighbor with hforward | hback
    · have hLabelForward : sideLabel = (e a)⁻¹ * e (a + 1) := by
        calc
          sideLabel = γ⁻¹ * (γ * sideLabel) := by group
          _ = γ⁻¹ * e (a + 1) := by rw [hforward]
          _ = (e a)⁻¹ * e (a + 1) := by rw [hea]
      have hindex : s a = i := B.intrinsicCyclicEdge_label_injective <| by
        calc
          (B.intrinsicCyclicEdge (s a)).1.1.1 = (e a)⁻¹ * e (a + 1) := hsideLabel a
          _ = sideLabel := hLabelForward.symm
          _ = (B.intrinsicCyclicEdge i).1.1.1 := rfl
      exact ⟨a, ha.1, hindex.symm⟩
    · let prev := a + (n - 1)
      have hprev_next : prev + 1 = a + n := by dsimp [prev]; omega
      have hprev_center : e (prev + 1) = e a := by rw [hprev_next, hperiodic]
      have hLabelBack : sideLabel = (e a)⁻¹ * e prev := by
        calc
          sideLabel = γ⁻¹ * (γ * sideLabel) := by group
          _ = γ⁻¹ * e prev := by rw [hback]
          _ = (e a)⁻¹ * e prev := by rw [hea]
      have hpreviousLabel : (B.intrinsicCyclicEdge (s prev)).1.1.1 = sideLabel⁻¹ := by
        rw [hsideLabel prev, hprev_center, hLabelBack]
        group
      have hpairedLabel :
          (B.intrinsicCyclicEdge (B.intrinsicCyclicPairing (s prev))).1.1.1 = sideLabel := by
        rw [B.intrinsicCyclicEdge_pairing, B.inverseIntrinsicOpenEdge_label,
          hpreviousLabel]
        simp
      have hpaired : B.intrinsicCyclicPairing (s prev) = i :=
        B.intrinsicCyclicEdge_label_injective (by
          simpa [sideLabel] using hpairedLabel)
      have htailPrev : (e prev)⁻¹ • v =
          B.intrinsicCyclicVertex
            (finRotate B.intrinsicBoundaryRadialCuts.card (s prev)) := by
        rcases hendpoint prev with h | h
        · exact False.elim (hstart0 ((horientation prev).mp h))
        · exact h
      have htrans : (e a)⁻¹ • v =
          ((e prev)⁻¹ * e a)⁻¹ • ((e prev)⁻¹ • v) := by
        rw [← mul_smul]
        congr 1
        group
      have hprevLabel : (B.intrinsicCyclicEdge (s prev)).1.1.1 =
          (e prev)⁻¹ * e a := by rw [hsideLabel prev, hprev_center]
      have hterminalPair : (e a)⁻¹ • v =
          B.intrinsicCyclicVertex (B.intrinsicCyclicPairing (s prev)) := by
        calc
          (e a)⁻¹ • v = ((e prev)⁻¹ * e a)⁻¹ • ((e prev)⁻¹ • v) := htrans
          _ = (B.intrinsicCyclicEdge (s prev)).1.1.1⁻¹ •
              B.intrinsicCyclicVertex
                (finRotate B.intrinsicBoundaryRadialCuts.card (s prev)) := by
            rw [← hprevLabel, htailPrev]
          _ = B.intrinsicCyclicVertex (B.intrinsicCyclicPairing (s prev)) :=
            (B.inverse_smul_intrinsicCyclicVertices_eq_reverse (s prev)).2
      have hnotEq := B.intrinsicCyclicVertex_next_ne
        (B.intrinsicCyclicPairing (s prev))
      have hbad : B.intrinsicCyclicVertex
          (B.intrinsicCyclicPairing (s prev)) =
        B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card
          (B.intrinsicCyclicPairing (s prev))) := by
        calc
          B.intrinsicCyclicVertex (B.intrinsicCyclicPairing (s prev)) =
              (e a)⁻¹ • v := hterminalPair.symm
          _ = B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i) := hγinv
          _ = B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card
              (B.intrinsicCyclicPairing (s prev))) := by rw [hpaired]
      exact False.elim (hnotEq hbad)

/-- For a fixed native representative, the complete local block is an explicit
nodup enumeration of its terminal-side fiber. Its order is reversed in the
start-endpoint convention so the block's cyclic successor agrees with the
native vertex permutation. -/
theorem exists_intrinsicBoundaryTerminalFiberBlock_ordered
    (B : DirichletBoundarySegments X o)
    (j : Fin B.intrinsicBoundaryRadialCuts.card) :
    ∃ block : List (Fin B.intrinsicBoundaryRadialCuts.card),
      block.Nodup ∧
        (∀ d, d ∈ block ↔
          B.intrinsicBoundaryGraphSideEnd d = B.intrinsicBoundaryGraphSideEnd j) ∧
        (∀ d, d ∈ block →
          block.formPerm d = B.intrinsicBoundaryOriginalVertexPerm d) := by
  classical
  let v := B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card j)
  have hv : v ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o :=
    B.intrinsicCyclicVertex_mem_polygonVertices _
  have hj : v = B.intrinsicCyclicVertex
      (finRotate B.intrinsicBoundaryRadialCuts.card j) := rfl
  obtain ⟨n, e, s, hn, hperiodic, hcontact, huniq, hadjacent, hsideLabel,
    hendpoint⟩ := B.exists_contact_cycle_native_sides hv
  have horientation := B.contact_cycle_endpoint_orientation_constant hv hn hperiodic
    hcontact huniq hsideLabel hendpoint
  by_cases hstart0 : (e 0)⁻¹ • v = B.intrinsicCyclicVertex (s 0)
  · let f : Fin n → Fin B.intrinsicBoundaryRadialCuts.card :=
      fun k => B.intrinsicCyclicPairing (s k)
    let block := (List.ofFn f).reverse
    have hsInjective : ∀ a b : Fin n,
        B.intrinsicCyclicPairing (s a) = B.intrinsicCyclicPairing (s b) → a = b := by
      intro a b hab
      have hs : s a = s b :=
        (Function.Involutive.injective B.intrinsicCyclicPairing_involutive) hab
      apply Fin.ext
      exact contact_side_index_injective_of_endpoint_orientation B hcontact huniq
        hendpoint horientation a.isLt b.isLt hs
    have hbaseNodup : (List.ofFn f).Nodup := List.nodup_ofFn.mpr hsInjective
    have hnodup : block.Nodup := by
      dsimp [block]
      apply List.nodup_reverse.mpr
      exact hbaseNodup
    have hstartAll : ∀ k, (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k) :=
      fun k => (horientation k).mpr hstart0
    refine ⟨block, hnodup, ?_, ?_⟩
    · intro d
      constructor
      · intro hd
        have hd' : d ∈ List.ofFn f :=
          List.mem_reverse.mp (by simpa [block] using hd)
        rw [List.mem_ofFn] at hd'
        obtain ⟨k, hdk⟩ := hd'
        subst d
        have hpoint : e k • B.intrinsicCyclicVertex (s k) = v := by
          calc
            e k • B.intrinsicCyclicVertex (s k) = e k • ((e k)⁻¹ • v) :=
              congrArg (fun z => e k • z) (hstartAll k).symm
            _ = v := by rw [smul_inv_smul]
        have hstartEq : B.intrinsicBoundaryGraphSideStart (s k) =
            B.intrinsicBoundaryGraphSideEnd j := by
          change Quotient.mk B.intrinsicBoundaryGraphVertexSetoid (s k) =
            Quotient.mk B.intrinsicBoundaryGraphVertexSetoid
              (finRotate B.intrinsicBoundaryRadialCuts.card j)
          apply Quotient.sound
          apply (B.intrinsicBoundaryGraphVertexSetoid_iff _ _).2
          exact ⟨e k, hpoint.trans hj.symm⟩
        exact (B.intrinsicBoundaryGraphSide_pair_endpoints (s k)).2 ▸ hstartEq
      · intro hfiber
        have hcovered := contact_cycle_terminal_fiber_occurrence B j hv hj hn hperiodic
          hcontact huniq hadjacent hsideLabel hendpoint horientation d hfiber
        rw [if_pos hstart0] at hcovered
        obtain ⟨k, hk, hdk⟩ := hcovered
        apply List.mem_reverse.mpr
        rw [List.mem_ofFn]
        exact ⟨⟨k, hk⟩, hdk.symm⟩
    · intro d hd
      have hd' : d ∈ List.ofFn f :=
        List.mem_reverse.mp (by simpa [block] using hd)
      rw [List.mem_ofFn] at hd'
      obtain ⟨k, hdk⟩ := hd'
      subst d
      have hperm := formPerm_reverse_ofFn_apply f hbaseNodup k
      let kprev := (finRotate n).symm k
      have hseq : s (kprev.val + 1) = s k.val := by
        have hrotval : (((finRotate n).symm k).val + 1) % n = k.val := by
          have h := congrArg Fin.val (Equiv.apply_symm_apply (finRotate n) k)
          simpa [finRotate_apply, Fin.add_def] using h
        calc
          s (kprev.val + 1) = s ((kprev.val + 1) % n) :=
            contact_side_index_mod_periodic B hperiodic hsideLabel _
          _ = s k.val := by rw [hrotval]
      have hnative := B.contact_cycle_paired_side_predecessor hv hn hperiodic
        hcontact huniq hsideLabel hendpoint hstartAll kprev.val
      have hnative' : B.intrinsicBoundaryOriginalVertexPerm (f k) = f kprev := by
        dsimp [f, kprev] at hnative ⊢
        rw [← hseq]
        exact hnative
      calc
        block.formPerm (f k) = f ((finRotate n).symm k) := by
          simpa [block, kprev] using hperm
        _ = B.intrinsicBoundaryOriginalVertexPerm (f k) := hnative'.symm
  · let f : Fin n → Fin B.intrinsicBoundaryRadialCuts.card := fun k => s k.val
    let block := List.ofFn f
    have hsInjective : Function.Injective f := by
      intro a b hab
      apply Fin.ext
      exact contact_side_index_injective_of_endpoint_orientation B hcontact huniq
        hendpoint horientation a.isLt b.isLt (by simpa [f] using hab)
    have hbaseNodup : (List.ofFn f).Nodup := List.nodup_ofFn.mpr hsInjective
    have hnodup : block.Nodup := by
      dsimp [block]
      exact hbaseNodup
    have hterminal : ∀ k, ¬ (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k) := by
      intro k hk
      exact hstart0 ((horientation k).mp hk)
    refine ⟨block, hnodup, ?_, ?_⟩
    · intro d
      constructor
      · intro hd
        rw [List.mem_ofFn] at hd
        obtain ⟨k, hdk⟩ := hd
        subst d
        dsimp [f]
        have hterminalPoint : (e k)⁻¹ • v =
            B.intrinsicCyclicVertex
              (finRotate B.intrinsicBoundaryRadialCuts.card (s k)) := by
          rcases hendpoint k with hstart | hterm
          · exact False.elim (hterminal k hstart)
          · exact hterm
        have hpoint : e k • B.intrinsicCyclicVertex
            (finRotate B.intrinsicBoundaryRadialCuts.card (s k)) = v := by
          calc
            e k • B.intrinsicCyclicVertex (finRotate _ (s k)) = e k • ((e k)⁻¹ • v) :=
              congrArg (fun z => e k • z) hterminalPoint.symm
            _ = v := by rw [smul_inv_smul]
        change Quotient.mk B.intrinsicBoundaryGraphVertexSetoid
            (finRotate B.intrinsicBoundaryRadialCuts.card (s k)) = _
        apply Quotient.sound
        apply (B.intrinsicBoundaryGraphVertexSetoid_iff _ _).2
        exact ⟨e k, hpoint.trans hj.symm⟩
      · intro hfiber
        have hcovered := contact_cycle_terminal_fiber_occurrence B j hv hj hn hperiodic
          hcontact huniq hadjacent hsideLabel hendpoint horientation d hfiber
        rw [if_neg hstart0] at hcovered
        obtain ⟨k, hk, hdk⟩ := hcovered
        rw [List.mem_ofFn]
        exact ⟨⟨k, hk⟩, by simpa [f] using hdk.symm⟩
    · intro d hd
      rw [List.mem_ofFn] at hd
      obtain ⟨k, hdk⟩ := hd
      subst d
      have hform := formPerm_ofFn_apply f hbaseNodup k
      have hrotate : (finRotate n k).val = (k.val + 1) % n := by
        simp [finRotate_apply, Fin.add_def]
      have hseq : s (k.val + 1) = s (finRotate n k).val := by
        calc
          s (k.val + 1) = s ((k.val + 1) % n) :=
            contact_side_index_mod_periodic B hperiodic hsideLabel _
          _ = s (finRotate n k).val := by rw [← hrotate]
      have hstep := (B.contact_cycle_native_side_successor hv hn hperiodic hcontact
        huniq hsideLabel hendpoint k.val).2 (hterminal k.val)
      calc
        block.formPerm (f k) = f (finRotate n k) := by simpa [block] using hform
        _ = B.intrinsicBoundaryOriginalVertexPerm (f k) := by
          change s (finRotate n k).val =
            B.intrinsicBoundaryOriginalVertexPerm (s k.val)
          rw [← hseq]
          exact hstep.symm

theorem exists_intrinsicBoundaryTerminalFiberBlock
    (B : DirichletBoundarySegments X o)
    (j : Fin B.intrinsicBoundaryRadialCuts.card) :
    ∃ block : List (Fin B.intrinsicBoundaryRadialCuts.card),
      block.Nodup ∧ ∀ d, d ∈ block ↔
        B.intrinsicBoundaryGraphSideEnd d = B.intrinsicBoundaryGraphSideEnd j := by
  obtain ⟨block, hnodup, hfiber, _⟩ :=
    B.exists_intrinsicBoundaryTerminalFiberBlock_ordered j
  exact ⟨block, hnodup, hfiber⟩

#print axioms exists_intrinsicBoundaryTerminalFiberBlock

/-- The constructor for every actual finite quotient vertex, choosing its
native incoming side index via the quotient's actual representative. -/
noncomputable def intrinsicBoundaryVertexBlock
    (B : DirichletBoundarySegments X o)
    (q : B.IntrinsicBoundaryGraphVertex) :
    List (Fin B.intrinsicBoundaryRadialCuts.card) := by
  classical
  let p := Quotient.out q
  let j := (finRotate B.intrinsicBoundaryRadialCuts.card).symm p
  exact Classical.choose (B.exists_intrinsicBoundaryTerminalFiberBlock j)

theorem intrinsicBoundaryVertexBlock_nodup
    (B : DirichletBoundarySegments X o)
    (q : B.IntrinsicBoundaryGraphVertex) :
    (B.intrinsicBoundaryVertexBlock q).Nodup := by
  classical
  let p := Quotient.out q
  let j := (finRotate B.intrinsicBoundaryRadialCuts.card).symm p
  have hj : B.intrinsicBoundaryGraphSideEnd j = q := by
    change Quotient.mk B.intrinsicBoundaryGraphVertexSetoid
        (finRotate B.intrinsicBoundaryRadialCuts.card j) = q
    rw [Equiv.apply_symm_apply]
    exact Quotient.out_eq q
  have hspec := Classical.choose_spec (B.exists_intrinsicBoundaryTerminalFiberBlock j)
  exact hspec.1

theorem intrinsicBoundaryVertexBlock_mem_iff
    (B : DirichletBoundarySegments X o)
    (q : B.IntrinsicBoundaryGraphVertex)
    (d : Fin B.intrinsicBoundaryRadialCuts.card) :
    d ∈ B.intrinsicBoundaryVertexBlock q ↔
      B.intrinsicBoundaryGraphSideEnd d = q := by
  classical
  let p := Quotient.out q
  let j := (finRotate B.intrinsicBoundaryRadialCuts.card).symm p
  have hj : B.intrinsicBoundaryGraphSideEnd j = q := by
    change Quotient.mk B.intrinsicBoundaryGraphVertexSetoid
        (finRotate B.intrinsicBoundaryRadialCuts.card j) = q
    rw [Equiv.apply_symm_apply]
    exact Quotient.out_eq q
  have hspec := Classical.choose_spec (B.exists_intrinsicBoundaryTerminalFiberBlock j)
  change d ∈ Classical.choose (B.exists_intrinsicBoundaryTerminalFiberBlock j) ↔ _
  rw [hspec.2 d]
  exact ⟨fun h => h.trans hj, fun h => h.trans hj.symm⟩

/-- The ordered counterpart to `intrinsicBoundaryVertexBlock`. This chooses
the same actual terminal fiber, but retains the contact-cycle order needed to
identify its list permutation with the native vertex transition. -/
noncomputable def intrinsicBoundaryOrderedVertexBlock
    (B : DirichletBoundarySegments X o)
    (q : B.IntrinsicBoundaryGraphVertex) :
    List (Fin B.intrinsicBoundaryRadialCuts.card) := by
  classical
  let p := Quotient.out q
  let j := (finRotate B.intrinsicBoundaryRadialCuts.card).symm p
  exact Classical.choose (B.exists_intrinsicBoundaryTerminalFiberBlock_ordered j)

theorem intrinsicBoundaryOrderedVertexBlock_nodup
    (B : DirichletBoundarySegments X o)
    (q : B.IntrinsicBoundaryGraphVertex) :
    (B.intrinsicBoundaryOrderedVertexBlock q).Nodup := by
  classical
  let p := Quotient.out q
  let j := (finRotate B.intrinsicBoundaryRadialCuts.card).symm p
  have hspec := Classical.choose_spec
    (B.exists_intrinsicBoundaryTerminalFiberBlock_ordered j)
  exact hspec.1

theorem intrinsicBoundaryOrderedVertexBlock_mem_iff
    (B : DirichletBoundarySegments X o)
    (q : B.IntrinsicBoundaryGraphVertex)
    (d : Fin B.intrinsicBoundaryRadialCuts.card) :
    d ∈ B.intrinsicBoundaryOrderedVertexBlock q ↔
      B.intrinsicBoundaryGraphSideEnd d = q := by
  classical
  let p := Quotient.out q
  let j := (finRotate B.intrinsicBoundaryRadialCuts.card).symm p
  have hj : B.intrinsicBoundaryGraphSideEnd j = q := by
    change Quotient.mk B.intrinsicBoundaryGraphVertexSetoid
        (finRotate B.intrinsicBoundaryRadialCuts.card j) = q
    rw [Equiv.apply_symm_apply]
    exact Quotient.out_eq q
  have hspec := Classical.choose_spec
    (B.exists_intrinsicBoundaryTerminalFiberBlock_ordered j)
  change d ∈ Classical.choose
    (B.exists_intrinsicBoundaryTerminalFiberBlock_ordered j) ↔ _
  rw [hspec.2.1 d]
  exact ⟨fun h => h.trans hj, fun h => h.trans hj.symm⟩

theorem intrinsicBoundaryOrderedVertexBlock_formPerm
    (B : DirichletBoundarySegments X o)
    (q : B.IntrinsicBoundaryGraphVertex)
    (d : Fin B.intrinsicBoundaryRadialCuts.card)
    (hd : d ∈ B.intrinsicBoundaryOrderedVertexBlock q) :
    (B.intrinsicBoundaryOrderedVertexBlock q).formPerm d =
      B.intrinsicBoundaryOriginalVertexPerm d := by
  classical
  let p := Quotient.out q
  let j := (finRotate B.intrinsicBoundaryRadialCuts.card).symm p
  have hspec := Classical.choose_spec
    (B.exists_intrinsicBoundaryTerminalFiberBlock_ordered j)
  change d ∈ Classical.choose
    (B.exists_intrinsicBoundaryTerminalFiberBlock_ordered j) at hd
  exact hspec.2.2 d hd

#print axioms intrinsicBoundaryVertexBlock_mem_iff
#print axioms exists_intrinsicBoundaryTerminalFiberBlock_ordered
#print axioms intrinsicBoundaryOrderedVertexBlock_formPerm
