module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaTypeIIDifferencing

@[expose] public section

/-!
# Exact mixed-shift support for Hua's Type-II common intervals

Three outer shifts give eight vertices in each original common window;
two variable-inner shifts require four such windows. This module records
their 32 membership tests without changing any strict lower or weak upper
endpoint. The all-vertex condition reduces to the two extreme outer
vertices in each of the four windows. These are support identities only;
the missing five-shift Cauchy inequality must justify their use in sums.
-/

namespace SystolicGrowth.CookMagyarCircle

/-- Four variable-inner indices produced by two positive shifts. As a
finite set this remains valid when shifts are zero and vertices coincide. -/
def huaTypeIIMixedInnerVertices (v η₁ η₂ : ℕ) : Finset ℕ :=
  {v, v + η₁, v + η₂, v + η₁ + η₂}

/-- The finite inner-vertex set has exactly the four source positions,
allowing coincidences when a shift is zero. -/
theorem mem_huaTypeIIMixedInnerVertices_iff
    (v η₁ η₂ z : ℕ) :
    z ∈ huaTypeIIMixedInnerVertices v η₁ η₂ ↔
      z = v ∨ z = v + η₁ ∨ z = v + η₂ ∨ z = v + η₁ + η₂ := by
  simp [huaTypeIIMixedInnerVertices]

/-- All four variable-inner membership predicates and all eight outer
vertices in each of their original common windows are equivalent to the
same four inner predicates and the two extreme outer vertices in each
window. The arbitrary source set `V` is not enlarged, and `W` is exactly
its ordered-pair filter `w<z`. -/
theorem hua_typeII_mixed_32vertex_support_iff_extremes
    (P l D D' v w u ξ₁ ξ₂ ξ₃ η₁ η₂ : ℕ) (P' : ℝ) (V : Finset ℕ) :
    let W := V.filter (fun z => w < z)
    let U := fun z => huaTypeIICommonOuterWindow P l D D' z w P'
    let Z := huaTypeIIMixedInnerVertices v η₁ η₂
    (∀ z ∈ Z, z ∈ W ∧
      (u ∈ U z ∧ u + ξ₁ ∈ U z ∧ u + ξ₂ ∈ U z ∧
        u + ξ₂ + ξ₁ ∈ U z ∧ u + ξ₃ ∈ U z ∧
        u + ξ₃ + ξ₁ ∈ U z ∧ u + ξ₃ + ξ₂ ∈ U z ∧
        u + ξ₃ + ξ₂ + ξ₁ ∈ U z)) ↔
      (∀ z ∈ Z, z ∈ W ∧
        (u ∈ U z ∧ u + ξ₃ + ξ₂ + ξ₁ ∈ U z)) := by
  dsimp only
  constructor
  · intro hall z hz
    obtain ⟨hzW, hvertices⟩ := hall z hz
    exact ⟨hzW,
      (hua_typeII_commonWindow_eightShift_iff_endpoints
        P l D D' z w u ξ₁ ξ₂ ξ₃ P').1 hvertices⟩
  · intro hall z hz
    obtain ⟨hzW, hendpoints⟩ := hall z hz
    exact ⟨hzW,
      (hua_typeII_commonWindow_eightShift_iff_endpoints
        P l D D' z w u ξ₁ ξ₂ ξ₃ P').2 hendpoints⟩

/-- Actual finite support for the 3-outer/2-inner mixed autocorrelation
tests: the outer index remains in `D<u≤D'`, all four inner vertices lie
in the original ordered `V`-filter, and all 32 corresponding outer
vertices lie in their *own* common windows. -/
noncomputable def huaTypeIIMixedOrderedSupport
    (P l D D' v w ξ₁ ξ₂ ξ₃ η₁ η₂ : ℕ)
    (P' : ℝ) (V : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc (D + 1) D').filter (fun u =>
    ∀ z ∈ huaTypeIIMixedInnerVertices v η₁ η₂,
      z ∈ V.filter (fun z => w < z) ∧
      (u ∈ huaTypeIICommonOuterWindow P l D D' z w P' ∧
        u + ξ₁ ∈ huaTypeIICommonOuterWindow P l D D' z w P' ∧
        u + ξ₂ ∈ huaTypeIICommonOuterWindow P l D D' z w P' ∧
        u + ξ₂ + ξ₁ ∈ huaTypeIICommonOuterWindow P l D D' z w P' ∧
        u + ξ₃ ∈ huaTypeIICommonOuterWindow P l D D' z w P' ∧
        u + ξ₃ + ξ₁ ∈ huaTypeIICommonOuterWindow P l D D' z w P' ∧
        u + ξ₃ + ξ₂ ∈ huaTypeIICommonOuterWindow P l D D' z w P' ∧
        u + ξ₃ + ξ₂ + ξ₁ ∈ huaTypeIICommonOuterWindow P l D D' z w P'))

/-- Membership in the mixed finite support is exactly the four original
inner tests times eight unchanged common-window outer tests. The
apparently extra `D<u≤D'` filter in the definition follows from the test
at the unshifted inner vertex `v`, so it adds no hidden hypothesis. -/
theorem mem_huaTypeIIMixedOrderedSupport_iff
    (P l D D' v w u ξ₁ ξ₂ ξ₃ η₁ η₂ : ℕ) (P' : ℝ) (V : Finset ℕ) :
    let W := V.filter (fun z => w < z)
    let U := fun z => huaTypeIICommonOuterWindow P l D D' z w P'
    let Z := huaTypeIIMixedInnerVertices v η₁ η₂
    u ∈ huaTypeIIMixedOrderedSupport
      P l D D' v w ξ₁ ξ₂ ξ₃ η₁ η₂ P' V ↔
      (∀ z ∈ Z, z ∈ W ∧
        (u ∈ U z ∧ u + ξ₁ ∈ U z ∧ u + ξ₂ ∈ U z ∧
          u + ξ₂ + ξ₁ ∈ U z ∧ u + ξ₃ ∈ U z ∧
          u + ξ₃ + ξ₁ ∈ U z ∧ u + ξ₃ + ξ₂ ∈ U z ∧
          u + ξ₃ + ξ₂ + ξ₁ ∈ U z)) := by
  classical
  dsimp only
  constructor
  · intro hu
    exact (Finset.mem_filter.mp hu).2
  · intro hall
    have hvZ : v ∈ huaTypeIIMixedInnerVertices v η₁ η₂ := by
      simp [huaTypeIIMixedInnerVertices]
    have huU : u ∈ huaTypeIICommonOuterWindow P l D D' v w P' :=
      (hall v hvZ).2.1
    obtain ⟨hDu, huD', _, _, _, _⟩ :=
      (mem_huaTypeIICommonOuterWindow_iff P l D D' v w u P').1 huU
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, huD'⟩, hall⟩

/-- The same actual finite support can be checked with only the two
extreme outer vertices in each of the four original common windows. -/
theorem mem_huaTypeIIMixedOrderedSupport_iff_extremes
    (P l D D' v w u ξ₁ ξ₂ ξ₃ η₁ η₂ : ℕ) (P' : ℝ) (V : Finset ℕ) :
    let W := V.filter (fun z => w < z)
    let U := fun z => huaTypeIICommonOuterWindow P l D D' z w P'
    let Z := huaTypeIIMixedInnerVertices v η₁ η₂
    u ∈ huaTypeIIMixedOrderedSupport
      P l D D' v w ξ₁ ξ₂ ξ₃ η₁ η₂ P' V ↔
      (∀ z ∈ Z, z ∈ W ∧
        (u ∈ U z ∧ u + ξ₃ + ξ₂ + ξ₁ ∈ U z)) := by
  exact (mem_huaTypeIIMixedOrderedSupport_iff
    P l D D' v w u ξ₁ ξ₂ ξ₃ η₁ η₂ P' V).trans
      (hua_typeII_mixed_32vertex_support_iff_extremes
        P l D D' v w u ξ₁ ξ₂ ξ₃ η₁ η₂ P' V)

#print axioms mem_huaTypeIIMixedInnerVertices_iff
#print axioms hua_typeII_mixed_32vertex_support_iff_extremes
#print axioms mem_huaTypeIIMixedOrderedSupport_iff
#print axioms mem_huaTypeIIMixedOrderedSupport_iff_extremes

end SystolicGrowth.CookMagyarCircle
