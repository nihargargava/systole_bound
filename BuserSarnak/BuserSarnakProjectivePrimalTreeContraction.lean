module

public import BuserSarnak.BuserSarnakProjectivePrimalTreeRegions
public import BuserSarnak.BuserSarnakProjectiveVertexOrbitSupport
public import BuserSarnak.FiniteRootedCycleContraction

@[expose] public section

/-!
# The global canonical primal-tree cycle

The canonical-word regions supply the actual finite rooted tree for the
cycle-contraction induction. All local support, disjointness, and pivot
conditions are proved here; no global orbit hypothesis is supplied as data.
The resulting trace records every actual child splice, with its ordered
permutation product, and its root word contains every original polygon dart.
Identification with the literal post-cone contour remains a separate theorem.
-/

namespace SystolicGrowth

noncomputable section

noncomputable local instance primalContractionRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

noncomputable local instance primalContractionEdgeFintype
    (p : ℕ) [NeZero p] : Fintype (CanonicalBuserSarnakProjectiveDegenerateSymbol p) :=
  Fintype.ofFinite _

/-- The finite ordered list of actual primal edges leaving a vertex. -/
def canonicalProjectivePrimalChildren (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    List (CanonicalBuserSarnakProjectiveDegenerateSymbol p) := by
  classical
  exact (Finset.univ.filter fun z => z.1.1 = q).toList

@[simp] theorem mem_canonicalProjectivePrimalChildren
    {p : ℕ} [NeZero p] (q : BuserSarnakProjectiveReductionRange p)
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    z ∈ canonicalProjectivePrimalChildren p q ↔ z.1.1 = q := by
  classical
  simp [canonicalProjectivePrimalChildren]

theorem canonicalProjectivePrimalChildren_nodup
    {p : ℕ} [NeZero p] (q : BuserSarnakProjectiveReductionRange p) :
    (canonicalProjectivePrimalChildren p q).Nodup := by
  classical
  exact Finset.nodup_toList _

/-- The canonical primal tree satisfies every local contract of the global
cycle-contraction induction. Its regions are primal, not dual face regions. -/
def canonicalProjectivePrimalCycleTreeData (p : ℕ) [NeZero p] :
    RootedCycleTreeData
      (BuserSarnakProjectiveReductionRange p)
      (CanonicalBuserSarnakProjectiveDegenerateSymbol p)
      (CanonicalProjectivePolygonDart p) := by
  classical
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  exact {
    height := canonicalProjectiveWordHeight p
    children := canonicalProjectivePrimalChildren p
    children_nodup := canonicalProjectivePrimalChildren_nodup
    target := canonicalProjectiveTreeTarget p
    height_child := by
      intro q z hz
      have h := canonicalProjectiveWordHeight_lt_treeTarget z
      rw [(mem_canonicalProjectivePrimalChildren q z).mp hz] at h
      exact h
    ancestor := canonicalProjectivePrimalAncestor p
    height_ancestor := by
      intro q r hqr
      exact canonicalProjectivePrimalAncestor_height_le hqr
    ancestor_partition := by
      intro q r
      simpa only [mem_canonicalProjectivePrimalChildren] using
        canonicalProjectivePrimalAncestor_iff_eq_or_child q r
    sibling_disjoint := by
      intro q z w hz hw hne r hzr hwr
      have hsource : z.1.1 = w.1.1 :=
        ((mem_canonicalProjectivePrimalChildren q z).mp hz).trans
          ((mem_canonicalProjectivePrimalChildren q w).mp hw).symm
      exact hne (canonicalProjectivePrimalAncestor_sibling_unique hsource hzr hwr)
    vertex := fun d => S.polygonSideStart d.1 d.2
    block := projectivePrimalVertexDartOrbitList S
    block_nodup := projectivePrimalVertexDartOrbitList_nodup S
    mem_block_iff := mem_projectivePrimalVertexDartOrbitList_iff S
    sourceDart := canonicalProjectivePolygonTreeSourceDart
    targetDart := canonicalProjectivePolygonTreeTargetDart
    sourceDart_mem := by
      intro q z hz
      apply (mem_projectivePrimalVertexDartOrbitList_iff S q _).mpr
      exact (polygonSideStart_canonicalProjectivePolygonTreeSourceDart z).trans
        ((mem_canonicalProjectivePrimalChildren q z).mp hz)
    targetDart_mem := by
      intro q z _hz
      apply (mem_projectivePrimalVertexDartOrbitList_iff S
        (canonicalProjectiveTreeTarget p z) _).mpr
      exact polygonSideStart_canonicalProjectivePolygonTreeTargetDart z }

/-- Each actual primal region has a nodup merged cycle list with exactly its
dart support and a trace of all child splices. -/
theorem canonicalProjectivePrimalRegion_cycle_exists
    {p : ℕ} [NeZero p] (q : BuserSarnakProjectiveReductionRange p) :
    ∃ merged : List (CanonicalProjectivePolygonDart p),
      merged.Nodup ∧
      (∀ d, d ∈ merged ↔ canonicalProjectivePrimalAncestor p q
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart d.1 d.2)) ∧
      RootedCycleContractionTrace (canonicalProjectivePrimalCycleTreeData p) q merged := by
  classical
  exact rootedCycleContraction_exists (canonicalProjectivePrimalCycleTreeData p) q

/-- At the root, the actual recursively spliced list exhausts all polygon
darts, with the contraction trace retained. -/
theorem canonicalProjectivePrimalRoot_cycle_exists
    (p : ℕ) [NeZero p] :
    ∃ merged : List (CanonicalProjectivePolygonDart p),
      merged.Nodup ∧ (∀ d, d ∈ merged) ∧
      RootedCycleContractionTrace (canonicalProjectivePrimalCycleTreeData p) 1 merged := by
  obtain ⟨merged, hn, hmem, htrace⟩ := canonicalProjectivePrimalRegion_cycle_exists
    (p := p) 1
  exact ⟨merged, hn, fun d => (hmem d).mpr (canonicalProjectivePrimalAncestor_root _),
    htrace⟩

/-- A selected global cycle comes with its verified, literal contraction
trace. Selection does not assert a contour conjugacy or a Nielsen program. -/
def canonicalProjectivePrimalContractedWord (p : ℕ) [NeZero p] :
    List (CanonicalProjectivePolygonDart p) :=
  (canonicalProjectivePrimalRoot_cycle_exists p).choose

theorem canonicalProjectivePrimalContractedWord_nodup (p : ℕ) [NeZero p] :
    (canonicalProjectivePrimalContractedWord p).Nodup :=
  (canonicalProjectivePrimalRoot_cycle_exists p).choose_spec.1

@[simp] theorem mem_canonicalProjectivePrimalContractedWord
    (p : ℕ) [NeZero p] (d : CanonicalProjectivePolygonDart p) :
    d ∈ canonicalProjectivePrimalContractedWord p :=
  (canonicalProjectivePrimalRoot_cycle_exists p).choose_spec.2.1 d

theorem canonicalProjectivePrimalContractedWord_trace (p : ℕ) [NeZero p] :
    RootedCycleContractionTrace (canonicalProjectivePrimalCycleTreeData p) 1
      (canonicalProjectivePrimalContractedWord p) :=
  (canonicalProjectivePrimalRoot_cycle_exists p).choose_spec.2.2

/-- The root cycle retains at least the eight distinct darts of its original
local vertex block. -/
theorem canonicalProjectivePrimalContractedWord_length_ge_eight
    (p : ℕ) [NeZero p] : 8 ≤ (canonicalProjectivePrimalContractedWord p).length := by
  classical
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  have hsub : (projectivePrimalVertexDartOrbitList S 1).toFinset ⊆
      (canonicalProjectivePrimalContractedWord p).toFinset := by
    intro d _hd
    exact List.mem_toFinset.mpr (mem_canonicalProjectivePrimalContractedWord p d)
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (projectivePrimalVertexDartOrbitList_nodup S 1),
    List.toFinset_card_of_nodup (canonicalProjectivePrimalContractedWord_nodup p),
    projectivePrimalVertexDartOrbitList_length] at hcard
  exact hcard

/-- The permutation represented by the fully spliced primal root cycle. -/
def canonicalProjectivePrimalContractedPerm (p : ℕ) [NeZero p] :
    Equiv.Perm (CanonicalProjectivePolygonDart p) := by
  classical
  exact List.formPerm (canonicalProjectivePrimalContractedWord p)

theorem canonicalProjectivePrimalContractedPerm_isCycle (p : ℕ) [NeZero p] :
    Equiv.Perm.IsCycle (canonicalProjectivePrimalContractedPerm p) := by
  classical
  apply List.isCycle_formPerm (canonicalProjectivePrimalContractedWord_nodup p)
  have h := canonicalProjectivePrimalContractedWord_length_ge_eight p
  omega

theorem canonicalProjectivePrimalContractedPerm_ne_self
    (p : ℕ) [NeZero p] (d : CanonicalProjectivePolygonDart p) :
    canonicalProjectivePrimalContractedPerm p d ≠ d := by
  classical
  apply (List.formPerm_apply_mem_ne_self_iff _
    (canonicalProjectivePrimalContractedWord_nodup p) d
    (mem_canonicalProjectivePrimalContractedWord p d)).mpr
  have h := canonicalProjectivePrimalContractedWord_length_ge_eight p
  omega

/-- The fully traced primal-tree contraction is transitive on every original
dart. This is not yet transitivity of the literal post-cone root contour. -/
theorem canonicalProjectivePrimalContractedPerm_one_orbit (p : ℕ) [NeZero p] :
    ∀ d e : CanonicalProjectivePolygonDart p,
      ∃ k : ℕ, (canonicalProjectivePrimalContractedPerm p)^[k] d = e := by
  intro d e
  obtain ⟨k, hk⟩ := (canonicalProjectivePrimalContractedPerm_isCycle p).exists_pow_eq
    (canonicalProjectivePrimalContractedPerm_ne_self p d)
    (canonicalProjectivePrimalContractedPerm_ne_self p e)
  exact ⟨k, by simpa only [Equiv.Perm.coe_pow] using hk⟩

end

#print axioms canonicalProjectivePrimalCycleTreeData
#print axioms canonicalProjectivePrimalRegion_cycle_exists
#print axioms canonicalProjectivePrimalRoot_cycle_exists
#print axioms canonicalProjectivePrimalContractedWord_trace
#print axioms canonicalProjectivePrimalContractedPerm_one_orbit

end SystolicGrowth
