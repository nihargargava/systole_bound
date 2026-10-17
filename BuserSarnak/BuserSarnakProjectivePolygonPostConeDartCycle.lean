module

public import BuserSarnak.BuserSarnakProjectivePolygonPostConeCut
public import BuserSarnak.BuserSarnakProjectivePolygonDarts

@[expose] public section

/-!
# Crossing cycles around a post-cone polygon vertex

The eight face-side darts meeting one primal vertex form a rotation cycle.
This module proves the elementary cycle fact used by the cut argument: if the
other seven darts do not cross the root component, neither does the remaining
one.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete

noncomputable local instance buserSarnakProjectivePolygonPostConeDartCycleRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

/-- A face-side dart crosses when its two incident polygon faces lie in
different root-component classes of the physical post-cone quiver. -/
def projectivePolygonPostConeDartCrossing
    {p : ℕ} [NeZero p]
    (d : BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide) : Prop :=
  projectivePolygonPostConeCrossing d.1 d.2

/-- If rotations one through seven of an octagon dart are noncrossings, the
original dart is also a noncrossing. -/
theorem projectivePolygonPostConeDart_not_crossing_of_rotations_not_crossing
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (hrot : ∀ n : ℕ, 1 ≤ n → n ≤ 7 →
      ¬ projectivePolygonPostConeDartCrossing
        (((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonVertexRotateDart^[n])
          (q, s))) :
    ¬ projectivePolygonPostConeDartCrossing (q, s) := by
  classical
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  let rot := S.polygonVertexRotateDart
  let d : BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide := (q, s)
  let C : BuserSarnakProjectiveReductionRange p → Prop :=
    projectivePolygonPostConeRootComponent p
  have step (n : ℕ) (hn1 : 1 ≤ n) (hn7 : n ≤ 7) :
      C ((rot^[n]) d).1 ↔ C ((rot^[n + 1]) d).1 := by
    have hnot : ¬ projectivePolygonPostConeDartCrossing ((rot^[n]) d) := by
      simpa [S, rot, d] using hrot n hn1 hn7
    have hiff : C ((rot^[n]) d).1 ↔
        C (S.polygonSidePartner ((rot^[n]) d).1 ((rot^[n]) d).2).1 := by
      exact Classical.not_not.mp hnot
    have hnext : ((rot^[n + 1]) d).1 =
        (S.polygonSidePartner ((rot^[n]) d).1 ((rot^[n]) d).2).1 := by
      rw [show n + 1 = Nat.succ n by omega, Function.iterate_succ_apply']
      rfl
    rw [hnext]
    exact hiff
  have h1 := step 1 (by omega) (by omega)
  have h2 := step 2 (by omega) (by omega)
  have h3 := step 3 (by omega) (by omega)
  have h4 := step 4 (by omega) (by omega)
  have h5 := step 5 (by omega) (by omega)
  have h6 := step 6 (by omega) (by omega)
  have h7 := step 7 (by omega) (by omega)
  have hchain : C ((rot^[1]) d).1 ↔ C ((rot^[8]) d).1 :=
    h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))
  have hcycle : (rot^[8]) d = d := by
    simpa [S, rot, d] using S.polygonVertexRotateDart_iterate_eight q s
  rw [hcycle] at hchain
  have horig : C d.1 ↔ C ((rot^[1]) d).1 := hchain.symm
  change ¬ ¬ (projectivePolygonPostConeRootComponent p q ↔
    projectivePolygonPostConeRootComponent p (S.polygonSidePartner q s).1)
  apply Classical.not_not.mpr
  simpa [C, rot, d, BuserSarnakProjectiveQuotientSectionData.polygonVertexRotateDart,
    BuserSarnakProjectiveQuotientSectionData.polygonVertexRotate] using horig

end

end SystolicGrowth
