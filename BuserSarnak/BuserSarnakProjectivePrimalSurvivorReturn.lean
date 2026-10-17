module

public import BuserSarnak.BuserSarnakProjectivePostConeSurvivorClassification
public import BuserSarnak.BuserSarnakProjectivePrimalTreeSemantics
public import BuserSarnak.FinitePermutationFirstReturn

@[expose] public section

/-!
# First return of the physical primal contraction on retained darts

The retained signed alphabet is equivalent to the actual survivor subset of
original polygon darts. Transport first return of the natural primal-tree
modified vertex permutation through that equivalence. The ordered literal
root-contour rotation still has to be identified with this map; this module
does not assume that identification.
-/

namespace SystolicGrowth

noncomputable section

open scoped Classical

local instance survivorReturnDecidablePred
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    DecidablePred (canonicalProjectivePostConeSurvivorSet hp hp2) :=
  Classical.decPred _

/-- The least positive physical hit from a retained endpoint occurrence. -/
def canonicalProjectivePrimalSurvivorReturnTime
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) : ℕ :=
  finitePermutationFirstReturnTime (canonicalProjectivePrimalTreeModifiedVertexPerm p)
    (canonicalProjectivePostConeSurvivorSet hp hp2)
    (canonicalProjectivePostConeSurvivorPhysicalEquiv hp hp2 d)

/-- First return of the natural primal-contracted physical permutation,
decoded in the retained signed endpoint alphabet. -/
def canonicalProjectivePrimalSurvivorReturn
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    CanonicalProjectivePostConeSurvivingDart hp hp2 →
      CanonicalProjectivePostConeSurvivingDart hp hp2 := fun d =>
  (canonicalProjectivePostConeSurvivorPhysicalEquiv hp hp2).symm
    (finitePermutationFirstReturn (canonicalProjectivePrimalTreeModifiedVertexPerm p)
      (canonicalProjectivePostConeSurvivorSet hp hp2)
      (canonicalProjectivePostConeSurvivorPhysicalEquiv hp hp2 d))

/-- Exact physical meaning of the retained return map. -/
theorem canonicalProjectivePrimalSurvivorReturn_embedding
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) :
    canonicalProjectivePostConeSurvivingDart_embedding hp hp2
        (canonicalProjectivePrimalSurvivorReturn hp hp2 d) =
      (canonicalProjectivePrimalTreeModifiedVertexPerm p)^[
        canonicalProjectivePrimalSurvivorReturnTime hp hp2 d]
        (canonicalProjectivePostConeSurvivingDart_embedding hp hp2 d) := by
  have h := congrArg Subtype.val
    ((canonicalProjectivePostConeSurvivorPhysicalEquiv hp hp2).apply_symm_apply
      (finitePermutationFirstReturn (canonicalProjectivePrimalTreeModifiedVertexPerm p)
        (canonicalProjectivePostConeSurvivorSet hp hp2)
        (canonicalProjectivePostConeSurvivorPhysicalEquiv hp hp2 d)))
  exact h

theorem canonicalProjectivePrimalSurvivorReturnTime_pos
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) :
    0 < canonicalProjectivePrimalSurvivorReturnTime hp hp2 d :=
  finitePermutationFirstReturnTime_pos _ _ _

/-- Before the return time, all positive iterates are omitted physical darts. -/
theorem canonicalProjectivePrimalSurvivorReturnTime_min
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) {n : ℕ}
    (hn : 0 < n) (hlt : n < canonicalProjectivePrimalSurvivorReturnTime hp hp2 d) :
    (canonicalProjectivePrimalTreeModifiedVertexPerm p)^[n]
        (canonicalProjectivePostConeSurvivingDart_embedding hp hp2 d) ∉
      canonicalProjectivePostConeSurvivorSet hp hp2 :=
  finitePermutationFirstReturnTime_min _ _ _ hn hlt

/-- Every intermediate positive step uses one of the two actual deletion
rules; cone normalization introduces no third kind of omitted dart. -/
theorem canonicalProjectivePrimalSurvivorReturnTime_intermediate_carrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) {n : ℕ}
    (hn : 0 < n) (hlt : n < canonicalProjectivePrimalSurvivorReturnTime hp hp2 d) :
    (∃ z : CanonicalBuserSarnakProjectiveDegenerateSymbol p,
      IsCanonicalProjectivePolygonTreeCarrier z
        ((canonicalProjectivePrimalTreeModifiedVertexPerm p)^[n]
          (canonicalProjectivePostConeSurvivingDart_embedding hp hp2 d))) ∨
      IsCanonicalProjectivePostConeDualTreeCarrier hp hp2
        ((canonicalProjectivePrimalTreeModifiedVertexPerm p)^[n]
          (canonicalProjectivePostConeSurvivingDart_embedding hp hp2 d)) :=
  (not_mem_canonicalProjectivePostConeSurvivorSet_iff hp hp2 _).mp
    (canonicalProjectivePrimalSurvivorReturnTime_min hp hp2 d hn hlt)

/-- The actual retained first-return map has one orbit. This is not yet the
one-orbit theorem for the literal root-contour rotation. -/
theorem canonicalProjectivePrimalSurvivorReturn_one_orbit
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ d e : CanonicalProjectivePostConeSurvivingDart hp hp2,
      ∃ n : ℕ, (canonicalProjectivePrimalSurvivorReturn hp hp2)^[n] d = e := by
  apply one_orbit_of_conjugate
    (finitePermutationFirstReturn (canonicalProjectivePrimalTreeModifiedVertexPerm p)
      (canonicalProjectivePostConeSurvivorSet hp hp2))
    (canonicalProjectivePrimalSurvivorReturn hp hp2)
    (canonicalProjectivePostConeSurvivorPhysicalEquiv hp hp2).symm
  · intro x
    simp only [canonicalProjectivePrimalSurvivorReturn, Equiv.apply_symm_apply]
  · exact finitePermutationFirstReturn_one_orbit _ _
      (canonicalProjectivePrimalTreeModifiedVertexPerm_one_orbit p)

/-- At a removed primal carrier, physical traversal skips the same-face side. -/
theorem canonicalProjectivePrimalTreeModifiedVertexPerm_apply_primalCarrier
    {p : ℕ} [NeZero p] (d : CanonicalProjectivePolygonDart p)
    (hd : ∃ z : CanonicalBuserSarnakProjectiveDegenerateSymbol p,
      IsCanonicalProjectivePolygonTreeCarrier z d) :
    canonicalProjectivePrimalTreeModifiedVertexPerm p d = (d.1, d.2.next) := by
  rw [canonicalProjectivePrimalTreeModifiedVertexPerm_apply_faceSuccessor, if_pos hd]

/-- At a removed dual carrier, physical traversal crosses the paired face. -/
theorem canonicalProjectivePrimalTreeModifiedVertexPerm_apply_dualCarrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p)
    (hd : IsCanonicalProjectivePostConeDualTreeCarrier hp hp2 d) :
    canonicalProjectivePrimalTreeModifiedVertexPerm p d =
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonVertexRotateDart d := by
  rw [canonicalProjectivePrimalTreeModifiedVertexPerm_apply_faceSuccessor,
    if_neg (canonicalProjectivePostConeDualTreeCarrier_not_primal hp hp2 d hd)]

/-- At a retained dart the tree swap is the identity, so traversal is the
original vertex rotation. -/
theorem canonicalProjectivePrimalTreeModifiedVertexPerm_apply_survivor
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p)
    (hd : d ∈ canonicalProjectivePostConeSurvivorSet hp hp2) :
    canonicalProjectivePrimalTreeModifiedVertexPerm p d =
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonVertexRotateDart d := by
  rw [canonicalProjectivePrimalTreeModifiedVertexPerm_apply_faceSuccessor,
    if_neg ((mem_canonicalProjectivePostConeSurvivorSet_iff hp hp2 d).mp hd).1]

/-- Literal positions and retained physical darts are the same domain.
This equivalence asserts nothing about literal cyclic successor. -/
def canonicalProjectivePostConeRawRootContourPosition_physicalEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Fin (canonicalProjectivePostConeRawRootContour hp hp2).length ≃
      canonicalProjectivePostConeSurvivorSet hp hp2 :=
  (canonicalProjectivePostConeRawRootContourPosition_endpointEquiv hp hp2).trans
    (canonicalProjectivePostConeSurvivorPhysicalEquiv hp hp2)

@[simp] theorem canonicalProjectivePostConeRawRootContourPosition_physicalEquiv_apply_val
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) :
    (canonicalProjectivePostConeRawRootContourPosition_physicalEquiv hp hp2 i).val =
      canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding hp hp2 i := rfl

#print axioms canonicalProjectivePrimalSurvivorReturn_embedding
#print axioms canonicalProjectivePrimalSurvivorReturnTime_min
#print axioms canonicalProjectivePrimalSurvivorReturnTime_intermediate_carrier
#print axioms canonicalProjectivePrimalSurvivorReturn_one_orbit
#print axioms canonicalProjectivePrimalTreeModifiedVertexPerm_apply_dualCarrier
#print axioms canonicalProjectivePostConeRawRootContourPosition_physicalEquiv

end

end SystolicGrowth
