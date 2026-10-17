module

public import BuserSarnak.BuserSarnakProjectivePrimalTreeContraction
public import BuserSarnak.BuserSarnakProjectivePrimalVertexPermutation
public import BuserSarnak.FinitePermutationFold

@[expose] public section

/-!
# Exact semantics of the recursively contracted primal tree

The verified contraction trace determines the natural geometric permutation
`σ * α_T`. The intermediate restricted permutations below only encode actual
primal regions; no global permutation or transitivity assertion is an input.
-/

namespace SystolicGrowth

noncomputable section

open scoped Classical

noncomputable local instance primalSemanticsEdgeFintype
    (p : ℕ) [NeZero p] : Fintype (CanonicalBuserSarnakProjectiveDegenerateSymbol p) :=
  Fintype.ofFinite _

/-- Original vertex rotation, restricted to a specified collection of primal
vertices and extended by identity outside it. -/
def canonicalProjectiveRestrictedVertexPerm
    {p : ℕ} [NeZero p] (A : BuserSarnakProjectiveReductionRange p → Prop) :
    Equiv.Perm (CanonicalProjectivePolygonDart p) := by
  classical
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  exact Equiv.Perm.ofSubtype
    ((projectivePolygonVertexRotationPerm S).subtypePerm
      (p := fun d => A (S.polygonSideStart d.1 d.2)) (by
        intro d
        change A (S.polygonSideStart (S.polygonVertexRotate d.1 d.2).1
          (S.polygonVertexRotate d.1 d.2).2) ↔ A (S.polygonSideStart d.1 d.2)
        rw [S.polygonVertexRotate_start]))

theorem canonicalProjectiveRestrictedVertexPerm_apply
    {p : ℕ} [NeZero p] (A : BuserSarnakProjectiveReductionRange p → Prop)
    (d : CanonicalProjectivePolygonDart p) :
    canonicalProjectiveRestrictedVertexPerm A d =
      if A ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart d.1 d.2)
      then (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonVertexRotateDart d
      else d := by
  classical
  unfold canonicalProjectiveRestrictedVertexPerm
  dsimp only
  split_ifs with h
  · rw [Equiv.Perm.ofSubtype_apply_of_mem
      (p := fun d : CanonicalProjectivePolygonDart p =>
        A ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart
        d.1 d.2)) _ h]
    rfl
  · exact Equiv.Perm.ofSubtype_apply_of_not_mem _ h

theorem canonicalProjectiveRestrictedVertexPerm_start
    {p : ℕ} [NeZero p] (A : BuserSarnakProjectiveReductionRange p → Prop)
    (d : CanonicalProjectivePolygonDart p) :
    (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart
      (canonicalProjectiveRestrictedVertexPerm A d).1
      (canonicalProjectiveRestrictedVertexPerm A d).2 =
    (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart d.1 d.2 := by
  rw [canonicalProjectiveRestrictedVertexPerm_apply]
  split_ifs
  · exact (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonVertexRotate_start _ _
  · rfl

theorem canonicalProjectiveRestrictedVertexPerm_congr
    {p : ℕ} [NeZero p] {A B : BuserSarnakProjectiveReductionRange p → Prop}
    (h : ∀ q, A q ↔ B q) :
    canonicalProjectiveRestrictedVertexPerm A = canonicalProjectiveRestrictedVertexPerm B := by
  apply Equiv.ext
  intro d
  simp only [canonicalProjectiveRestrictedVertexPerm_apply, h]

theorem canonicalProjectiveRestrictedVertexPerm_mul
    {p : ℕ} [NeZero p] (A B : BuserSarnakProjectiveReductionRange p → Prop)
    (hdis : ∀ q, A q → ¬ B q) :
    canonicalProjectiveRestrictedVertexPerm A * canonicalProjectiveRestrictedVertexPerm B =
      canonicalProjectiveRestrictedVertexPerm (fun q => A q ∨ B q) := by
  classical
  apply Equiv.ext
  intro d
  rw [Equiv.Perm.mul_apply, canonicalProjectiveRestrictedVertexPerm_apply A,
    canonicalProjectiveRestrictedVertexPerm_start]
  by_cases hA : A ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart d.1 d.2)
  · have hB := hdis _ hA
    simp only [hA, hB, if_true, if_false, canonicalProjectiveRestrictedVertexPerm_apply,
      true_or]
  · by_cases hB : B ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart d.1 d.2)
    · simp only [hA, hB, if_false, canonicalProjectiveRestrictedVertexPerm_apply,
        false_or]
    · simp only [hA, hB, if_false, canonicalProjectiveRestrictedVertexPerm_apply,
        false_or]

@[simp] theorem canonicalProjectiveRestrictedVertexPerm_false
    {p : ℕ} [NeZero p] :
    canonicalProjectiveRestrictedVertexPerm (p := p) (fun _ => False) = 1 := by
  apply Equiv.ext
  intro d
  simp [canonicalProjectiveRestrictedVertexPerm_apply]

/-- The product of precisely the physical swaps in an edge predicate. -/
def canonicalProjectiveRestrictedTreeSwapPerm
    {p : ℕ} [NeZero p] (B : CanonicalBuserSarnakProjectiveDegenerateSymbol p → Prop) :
    Equiv.Perm (CanonicalProjectivePolygonDart p) :=
  ((Finset.univ.filter B).toList.map canonicalProjectivePrimalTreeCarrierSwap).prod

theorem canonicalProjectiveRestrictedTreeSwapPerm_apply
    {p : ℕ} [NeZero p] (B : CanonicalBuserSarnakProjectiveDegenerateSymbol p → Prop)
    (d : CanonicalProjectivePolygonDart p) :
    canonicalProjectiveRestrictedTreeSwapPerm B d =
      if ∃ z, B z ∧ IsCanonicalProjectivePolygonTreeCarrier z d then
        (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner d.1 d.2
      else d := by
  unfold canonicalProjectiveRestrictedTreeSwapPerm
  rw [canonicalProjectivePrimalTreeCarrierSwap_list_prod_apply _ (Finset.nodup_toList _)]
  simp

theorem canonicalProjectiveRestrictedTreeSwapPerm_congr
    {p : ℕ} [NeZero p] {A B : CanonicalBuserSarnakProjectiveDegenerateSymbol p → Prop}
    (h : ∀ z, A z ↔ B z) :
    canonicalProjectiveRestrictedTreeSwapPerm A = canonicalProjectiveRestrictedTreeSwapPerm B := by
  apply Equiv.ext
  intro d
  simp only [canonicalProjectiveRestrictedTreeSwapPerm_apply, h]

@[simp] theorem canonicalProjectiveRestrictedTreeSwapPerm_false
    {p : ℕ} [NeZero p] :
    canonicalProjectiveRestrictedTreeSwapPerm (p := p) (fun _ => False) = 1 := by
  apply Equiv.ext
  intro d
  simp [canonicalProjectiveRestrictedTreeSwapPerm_apply]

theorem canonicalProjectiveRestrictedTreeSwapPerm_mul
    {p : ℕ} [NeZero p]
    (A B : CanonicalBuserSarnakProjectiveDegenerateSymbol p → Prop)
    (hdis : ∀ z, A z → ¬ B z) :
    canonicalProjectiveRestrictedTreeSwapPerm A * canonicalProjectiveRestrictedTreeSwapPerm B =
      canonicalProjectiveRestrictedTreeSwapPerm (fun z => A z ∨ B z) := by
  classical
  apply Equiv.ext
  intro d
  have hpartner : ∀ C : CanonicalBuserSarnakProjectiveDegenerateSymbol p → Prop,
      (∃ z, C z ∧ IsCanonicalProjectivePolygonTreeCarrier z
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner d.1 d.2)) ↔
      ∃ z, C z ∧ IsCanonicalProjectivePolygonTreeCarrier z d := by
    intro C
    simp only [isCanonicalProjectivePolygonTreeCarrier_partner_iff]
  have hnotboth : (∃ z, A z ∧ IsCanonicalProjectivePolygonTreeCarrier z d) →
      ¬ ∃ z, B z ∧ IsCanonicalProjectivePolygonTreeCarrier z d := by
    rintro ⟨z, hz, hzd⟩ ⟨w, hw, hwd⟩
    have heq := isCanonicalProjectivePolygonTreeCarrier_unique hzd hwd
    exact hdis z hz (heq ▸ hw)
  have hunion : (∃ z, (A z ∨ B z) ∧ IsCanonicalProjectivePolygonTreeCarrier z d) ↔
      (∃ z, A z ∧ IsCanonicalProjectivePolygonTreeCarrier z d) ∨
        (∃ z, B z ∧ IsCanonicalProjectivePolygonTreeCarrier z d) := by
    simp only [or_and_right, exists_or]
  rw [Equiv.Perm.mul_apply, canonicalProjectiveRestrictedTreeSwapPerm_apply B,
    canonicalProjectiveRestrictedTreeSwapPerm_apply (fun z => A z ∨ B z)]
  simp only [hunion]
  by_cases hB : ∃ z, B z ∧ IsCanonicalProjectivePolygonTreeCarrier z d
  · have hA : ¬ ∃ z, A z ∧ IsCanonicalProjectivePolygonTreeCarrier z d :=
      fun h => hnotboth h hB
    rw [if_pos hB, if_pos (Or.inr hB), canonicalProjectiveRestrictedTreeSwapPerm_apply,
      if_neg (by simpa only [hpartner] using hA)]
  · rw [if_neg hB, canonicalProjectiveRestrictedTreeSwapPerm_apply]
    simp only [hB, or_false]

theorem canonicalProjectiveRestrictedTreeSwapPerm_singleton
    {p : ℕ} [NeZero p] (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    canonicalProjectiveRestrictedTreeSwapPerm (fun w => w = z) =
      canonicalProjectivePrimalTreeCarrierSwap z := by
  classical
  apply Equiv.ext
  intro d
  rw [canonicalProjectiveRestrictedTreeSwapPerm_apply]
  simp only [exists_eq_left]
  split_ifs with h
  · exact (canonicalProjectivePrimalTreeCarrierSwap_apply_of_carrier z d h).symm
  · exact (canonicalProjectivePrimalTreeCarrierSwap_apply_of_not_carrier z d h).symm

/-- Disjoint physical and local vertex supports allow the exact product
factorization, without confusing primal and dual regions. -/
theorem canonicalProjectiveRestrictedTreeSwapPerm_disjoint_vertexPerm
    {p : ℕ} [NeZero p]
    (A : CanonicalBuserSarnakProjectiveDegenerateSymbol p → Prop)
    (B : BuserSarnakProjectiveReductionRange p → Prop)
    (hsource : ∀ z, A z → ¬ B z.1.1)
    (htarget : ∀ z, A z → ¬ B (canonicalProjectiveTreeTarget p z)) :
    Equiv.Perm.Disjoint (canonicalProjectiveRestrictedTreeSwapPerm A)
      (canonicalProjectiveRestrictedVertexPerm B) := by
  classical
  intro d
  by_cases hB : B ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart d.1 d.2)
  · left
    rw [canonicalProjectiveRestrictedTreeSwapPerm_apply, if_neg]
    rintro ⟨z, hz, hzd | hzd⟩
    · rw [hzd, polygonSideStart_canonicalProjectivePolygonTreeSourceDart] at hB
      exact hsource z hz hB
    · rw [hzd, polygonSideStart_canonicalProjectivePolygonTreeTargetDart] at hB
      exact htarget z hz hB
  · right
    rw [canonicalProjectiveRestrictedVertexPerm_apply, if_neg hB]

private theorem primalSemantics_foldl_mul {M I : Type*} [Monoid M]
    (l : List I) (f : I → M) (a : M) :
    l.foldl (fun b i => b * f i) a = a * (l.map f).prod := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih => simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih, mul_assoc]

theorem canonicalProjectiveRestrictedVertexPerm_list_prod
    {p : ℕ} [NeZero p] {I : Type*} (l : List I)
    (A : I → BuserSarnakProjectiveReductionRange p → Prop)
    (hdis : l.Pairwise (fun i j => ∀ q, A i q → ¬ A j q)) :
    (l.map (fun i => canonicalProjectiveRestrictedVertexPerm (A i))).prod =
      canonicalProjectiveRestrictedVertexPerm (fun q => ∃ i ∈ l, A i q) := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [List.map_cons, List.prod_cons, ih (List.pairwise_cons.mp hdis).2,
        canonicalProjectiveRestrictedVertexPerm_mul]
      · apply canonicalProjectiveRestrictedVertexPerm_congr
        intro q
        simp
      · intro q hi
        rintro ⟨j, hj, hjq⟩
        exact (List.pairwise_cons.mp hdis).1 j hj q hi hjq

theorem canonicalProjectiveRestrictedTreeSwapPerm_list_prod
    {p : ℕ} [NeZero p] {I : Type*} (l : List I)
    (A : I → CanonicalBuserSarnakProjectiveDegenerateSymbol p → Prop)
    (hdis : l.Pairwise (fun i j => ∀ z, A i z → ¬ A j z)) :
    (l.map (fun i => canonicalProjectiveRestrictedTreeSwapPerm (A i))).prod =
      canonicalProjectiveRestrictedTreeSwapPerm (fun z => ∃ i ∈ l, A i z) := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [List.map_cons, List.prod_cons, ih (List.pairwise_cons.mp hdis).2,
        canonicalProjectiveRestrictedTreeSwapPerm_mul]
      · apply canonicalProjectiveRestrictedTreeSwapPerm_congr
        intro z
        simp
      · intro z hi
        rintro ⟨j, hj, hjz⟩
        exact (List.pairwise_cons.mp hdis).1 j hj z hi hjz

/-- A child's combined internal and incoming edge predicate. -/
def canonicalProjectivePrimalChildEdgeRegion
    {p : ℕ} [NeZero p] (e z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) : Prop :=
  canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p e) z.1.1 ∨ z = e

theorem canonicalProjectivePrimalChildEdgeRegion_off_sibling
    {p : ℕ} [NeZero p]
    {e f : CanonicalBuserSarnakProjectiveDegenerateSymbol p}
    (hsource : e.1.1 = f.1.1) (hne : e ≠ f)
    {z : CanonicalBuserSarnakProjectiveDegenerateSymbol p}
    (hz : canonicalProjectivePrimalChildEdgeRegion e z) :
    ¬ canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p f) z.1.1 ∧
      ¬ canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p f)
        (canonicalProjectiveTreeTarget p z) := by
  rcases hz with hz | rfl
  · constructor
    · intro hf
      exact hne (canonicalProjectivePrimalAncestor_sibling_unique hsource hz hf)
    · intro hf
      exact hne (canonicalProjectivePrimalAncestor_sibling_unique hsource
        (canonicalProjectivePrimalAncestor_trans hz (canonicalProjectivePrimalAncestor_of_child z)) hf)
  · constructor
    · rw [hsource]
      exact canonicalProjectivePrimalAncestor_not_child_parent f
    · intro hf
      exact hne (canonicalProjectivePrimalAncestor_sibling_unique hsource
        (canonicalProjectivePrimalAncestor_refl _) hf)

theorem canonicalProjectivePrimalChildEdgeRegion_sibling_disjoint
    {p : ℕ} [NeZero p]
    {e f : CanonicalBuserSarnakProjectiveDegenerateSymbol p}
    (hsource : e.1.1 = f.1.1) (hne : e ≠ f)
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p)
    (he : canonicalProjectivePrimalChildEdgeRegion e z) :
    ¬ canonicalProjectivePrimalChildEdgeRegion f z := by
  intro hf
  rcases hf with hf | rfl
  · exact (canonicalProjectivePrimalChildEdgeRegion_off_sibling hsource hne he).1 hf
  · rcases he with he | he
    · exact canonicalProjectivePrimalAncestor_not_child_parent e (hsource ▸ he)
    · exact hne he.symm

theorem canonicalProjectivePrimalChildSwapPerm_eq_union
    {p : ℕ} [NeZero p] (e : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    canonicalProjectiveRestrictedTreeSwapPerm
        (fun z => canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p e) z.1.1) *
      canonicalProjectivePrimalTreeCarrierSwap e =
    canonicalProjectiveRestrictedTreeSwapPerm (canonicalProjectivePrimalChildEdgeRegion e) := by
  rw [← canonicalProjectiveRestrictedTreeSwapPerm_singleton,
    canonicalProjectiveRestrictedTreeSwapPerm_mul]
  · rfl
  · intro z hz hze
    subst z
    exact canonicalProjectivePrimalAncestor_not_child_parent e hz

/-- All child regions and incoming edges partition precisely the edges of
the parent primal region. -/
theorem canonicalProjectivePrimalChildEdgeRegion_exists_iff
    {p : ℕ} [NeZero p] (q : BuserSarnakProjectiveReductionRange p)
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    (∃ e ∈ canonicalProjectivePrimalChildren p q,
      canonicalProjectivePrimalChildEdgeRegion e z) ↔
      canonicalProjectivePrimalAncestor p q z.1.1 := by
  constructor
  · rintro ⟨e, he, hz | rfl⟩
    · have hqe := canonicalProjectivePrimalAncestor_of_child e
      rw [(mem_canonicalProjectivePrimalChildren q e).mp he] at hqe
      exact canonicalProjectivePrimalAncestor_trans hqe hz
    · rw [(mem_canonicalProjectivePrimalChildren q z).mp he]
      exact canonicalProjectivePrimalAncestor_refl _
  · intro hz
    rcases (canonicalProjectivePrimalAncestor_iff_eq_or_child q z.1.1).mp hz with hz | ⟨e, he, hz⟩
    · exact ⟨z, (mem_canonicalProjectivePrimalChildren q z).mpr hz, Or.inr rfl⟩
    · exact ⟨e, (mem_canonicalProjectivePrimalChildren q e).mpr he, Or.inl hz⟩

theorem canonicalProjectivePrimalChildren_vertexProduct
    {p : ℕ} [NeZero p] (q : BuserSarnakProjectiveReductionRange p) :
    List.formPerm
        (projectivePrimalVertexDartOrbitList (canonicalBuserSarnakProjectiveQuotientSectionData p) q) *
      ((canonicalProjectivePrimalChildren p q).map (fun e =>
        canonicalProjectiveRestrictedVertexPerm
          (canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p e)))).prod =
    canonicalProjectiveRestrictedVertexPerm (canonicalProjectivePrimalAncestor p q) := by
  classical
  have hlocal : List.formPerm
      (projectivePrimalVertexDartOrbitList (canonicalBuserSarnakProjectiveQuotientSectionData p) q) =
      canonicalProjectiveRestrictedVertexPerm (fun r => r = q) := by
    apply Equiv.ext
    intro d
    rw [projectivePrimalVertexDartOrbitList_formPerm_apply,
      canonicalProjectiveRestrictedVertexPerm_apply]
    simp
  have hdis : (canonicalProjectivePrimalChildren p q).Pairwise
      (fun e f => ∀ r,
        canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p e) r →
        ¬ canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p f) r) := by
    apply (canonicalProjectivePrimalChildren_nodup q).pairwise_of_forall_ne
    intro e he f hf hne r her hfr
    exact hne (canonicalProjectivePrimalAncestor_sibling_unique
      (((mem_canonicalProjectivePrimalChildren q e).mp he).trans
        ((mem_canonicalProjectivePrimalChildren q f).mp hf).symm) her hfr)
  rw [hlocal, canonicalProjectiveRestrictedVertexPerm_list_prod _ _ hdis,
    canonicalProjectiveRestrictedVertexPerm_mul]
  · apply canonicalProjectiveRestrictedVertexPerm_congr
    intro r
    simpa only [mem_canonicalProjectivePrimalChildren] using
      (canonicalProjectivePrimalAncestor_iff_eq_or_child q r).symm
  · intro r hr
    subst r
    rintro ⟨e, he, heq⟩
    have hsource := (mem_canonicalProjectivePrimalChildren q e).mp he
    exact canonicalProjectivePrimalAncestor_not_child_parent e (hsource ▸ heq)

theorem canonicalProjectivePrimalChildren_swapProduct
    {p : ℕ} [NeZero p] (q : BuserSarnakProjectiveReductionRange p) :
    ((canonicalProjectivePrimalChildren p q).map (fun e =>
      canonicalProjectiveRestrictedTreeSwapPerm
          (fun z => canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p e) z.1.1) *
        canonicalProjectivePrimalTreeCarrierSwap e)).prod =
    canonicalProjectiveRestrictedTreeSwapPerm (fun z => canonicalProjectivePrimalAncestor p q z.1.1) := by
  simp_rw [canonicalProjectivePrimalChildSwapPerm_eq_union]
  rw [canonicalProjectiveRestrictedTreeSwapPerm_list_prod]
  · exact canonicalProjectiveRestrictedTreeSwapPerm_congr
      (canonicalProjectivePrimalChildEdgeRegion_exists_iff q)
  · apply (canonicalProjectivePrimalChildren_nodup q).pairwise_of_forall_ne
    intro e he f hf hne
    exact canonicalProjectivePrimalChildEdgeRegion_sibling_disjoint
      (((mem_canonicalProjectivePrimalChildren q e).mp he).trans
        ((mem_canonicalProjectivePrimalChildren q f).mp hf).symm) hne

private theorem primalSemantics_foldl_congr {I M : Type*}
    (l : List I) (f g : M → I → M) (a : M)
    (h : ∀ i ∈ l, ∀ b, f b i = g b i) : l.foldl f a = l.foldl g a := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
      simp only [List.foldl_cons]
      rw [h i List.mem_cons_self]
      exact ih _ (fun j hj => h j (List.mem_cons_of_mem i hj))

theorem canonicalProjectivePrimalChildren_swap_vertex_commute
    {p : ℕ} [NeZero p] (q : BuserSarnakProjectiveReductionRange p) :
    (canonicalProjectivePrimalChildren p q).Pairwise (fun e f =>
      Commute
        (canonicalProjectiveRestrictedTreeSwapPerm
            (fun z => canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p e) z.1.1) *
          canonicalProjectivePrimalTreeCarrierSwap e)
        (canonicalProjectiveRestrictedVertexPerm
          (canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p f)))) := by
  apply (canonicalProjectivePrimalChildren_nodup q).pairwise_of_forall_ne
  intro e he f hf hne
  rw [canonicalProjectivePrimalChildSwapPerm_eq_union]
  apply Equiv.Perm.Disjoint.commute
  apply canonicalProjectiveRestrictedTreeSwapPerm_disjoint_vertexPerm
  · intro z hz
    exact (canonicalProjectivePrimalChildEdgeRegion_off_sibling
      (((mem_canonicalProjectivePrimalChildren q e).mp he).trans
        ((mem_canonicalProjectivePrimalChildren q f).mp hf).symm) hne hz).1
  · intro z hz
    exact (canonicalProjectivePrimalChildEdgeRegion_off_sibling
      (((mem_canonicalProjectivePrimalChildren q e).mp he).trans
        ((mem_canonicalProjectivePrimalChildren q f).mp hf).symm) hne hz).2

/-- Every actual recursive contraction trace has precisely the regional
rotation followed by its internal physical edge swaps. -/
theorem canonicalProjectivePrimalContractionTrace_semantics
    {p : ℕ} [NeZero p] {q : BuserSarnakProjectiveReductionRange p}
    {merged : List (CanonicalProjectivePolygonDart p)}
    (h : RootedCycleContractionTrace (canonicalProjectivePrimalCycleTreeData p) q merged) :
    List.formPerm merged =
      canonicalProjectiveRestrictedVertexPerm (canonicalProjectivePrimalAncestor p q) *
        canonicalProjectiveRestrictedTreeSwapPerm
          (fun z => canonicalProjectivePrimalAncestor p q z.1.1) := by
  classical
  induction h with
  | node q childWords merged hchild hn hs hperm hphysical ih =>
      rw [hphysical]
      change (canonicalProjectivePrimalChildren p q).foldl
          (fun π e => π * List.formPerm (childWords e) * canonicalProjectivePrimalTreeCarrierSwap e)
          (List.formPerm (projectivePrimalVertexDartOrbitList
            (canonicalBuserSarnakProjectiveQuotientSectionData p) q)) = _
      let rho := fun e : CanonicalBuserSarnakProjectiveDegenerateSymbol p =>
        canonicalProjectiveRestrictedVertexPerm
          (canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p e))
      let tau := fun e : CanonicalBuserSarnakProjectiveDegenerateSymbol p =>
        canonicalProjectiveRestrictedTreeSwapPerm
          (fun z => canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p e) z.1.1)
      let chi := @canonicalProjectivePrimalTreeCarrierSwap p _
      let rho0 := List.formPerm (projectivePrimalVertexDartOrbitList
        (canonicalBuserSarnakProjectiveQuotientSectionData p) q)
      have hfold : (canonicalProjectivePrimalChildren p q).foldl
          (fun π e => π * List.formPerm (childWords e) * chi e) rho0 =
        (canonicalProjectivePrimalChildren p q).foldl
          (fun π e => π * (rho e * tau e) * chi e) rho0 := by
        apply primalSemantics_foldl_congr
        intro e he π
        rw [ih e he]
        rfl
      have hsplit := foldl_interleaved_eq_split (canonicalProjectivePrimalChildren p q)
        rho tau chi rho0 1 (by intro e he; exact Commute.one_left _)
        (canonicalProjectivePrimalChildren_swap_vertex_commute q)
      simp only [mul_one] at hsplit
      have hswapFold : (canonicalProjectivePrimalChildren p q).foldl
          (fun π e => π * tau e * chi e) 1 =
          ((canonicalProjectivePrimalChildren p q).map (fun e => tau e * chi e)).prod := by
        simpa only [mul_assoc, one_mul] using primalSemantics_foldl_mul
          (canonicalProjectivePrimalChildren p q) (fun e => tau e * chi e) 1
      rw [hfold, hsplit, hswapFold, primalSemantics_foldl_mul]
      exact congrArg₂ (· * ·)
        (canonicalProjectivePrimalChildren_vertexProduct q)
        (canonicalProjectivePrimalChildren_swapProduct q)

/-- The globally constructed primal cycle is the actual geometric
full-dart map `σ * α_T`, not merely an arbitrary cycle on the same support. -/
theorem canonicalProjectivePrimalContractedPerm_eq_modifiedVertexPerm
    (p : ℕ) [NeZero p] :
    canonicalProjectivePrimalContractedPerm p =
      canonicalProjectivePrimalTreeModifiedVertexPerm p := by
  have hvertex : canonicalProjectiveRestrictedVertexPerm
      (canonicalProjectivePrimalAncestor p 1) =
      projectivePolygonVertexRotationPerm (canonicalBuserSarnakProjectiveQuotientSectionData p) := by
    apply Equiv.ext
    intro d
    simp [canonicalProjectiveRestrictedVertexPerm_apply]
  have hswap : canonicalProjectiveRestrictedTreeSwapPerm
      (fun z => canonicalProjectivePrimalAncestor p 1 z.1.1) =
      canonicalProjectivePrimalTreeSwapPerm p := by
    apply Equiv.ext
    intro d
    simp only [canonicalProjectiveRestrictedTreeSwapPerm_apply,
      canonicalProjectivePrimalTreeSwapPerm_apply, canonicalProjectivePrimalAncestor_root,
      true_and]
  exact (canonicalProjectivePrimalContractionTrace_semantics
    (canonicalProjectivePrimalContractedWord_trace p)).trans
      (by rw [hvertex, hswap]; rfl)

/-- The actual primal-tree-modified geometric rotation has one orbit on all
original polygon darts, with no transitivity premise. -/
theorem canonicalProjectivePrimalTreeModifiedVertexPerm_one_orbit
    (p : ℕ) [NeZero p] :
    ∀ d e : CanonicalProjectivePolygonDart p,
      ∃ k : ℕ, (canonicalProjectivePrimalTreeModifiedVertexPerm p)^[k] d = e := by
  rw [← canonicalProjectivePrimalContractedPerm_eq_modifiedVertexPerm p]
  exact canonicalProjectivePrimalContractedPerm_one_orbit p

theorem canonicalProjectivePrimalTreeModifiedVertexPerm_isCycle
    (p : ℕ) [NeZero p] :
    Equiv.Perm.IsCycle (canonicalProjectivePrimalTreeModifiedVertexPerm p) := by
  rw [← canonicalProjectivePrimalContractedPerm_eq_modifiedVertexPerm p]
  exact canonicalProjectivePrimalContractedPerm_isCycle p

theorem canonicalProjectivePrimalTreeModifiedVertexPerm_ne_self
    (p : ℕ) [NeZero p] (d : CanonicalProjectivePolygonDart p) :
    canonicalProjectivePrimalTreeModifiedVertexPerm p d ≠ d := by
  rw [← canonicalProjectivePrimalContractedPerm_eq_modifiedVertexPerm p]
  exact canonicalProjectivePrimalContractedPerm_ne_self p d

#print axioms canonicalProjectivePrimalContractionTrace_semantics
#print axioms canonicalProjectivePrimalContractedPerm_eq_modifiedVertexPerm
#print axioms canonicalProjectivePrimalTreeModifiedVertexPerm_one_orbit
#print axioms canonicalProjectivePrimalTreeModifiedVertexPerm_ne_self

end

end SystolicGrowth
