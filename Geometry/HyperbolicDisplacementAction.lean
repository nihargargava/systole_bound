module

public import Core.SystolicCore
public import Mathlib.Topology.Algebra.Group.Basic

@[expose] public section

/-!
# Freeness and discreteness from a positive displacement bound

The final chain constructor already requires a uniform positive lower bound
for every nonidentity image element. That bound implies freeness and isolates
the identity in the inherited subgroup topology; no independent proper-action
or projective lifting hypothesis is needed for these two consequences.
-/

open Set UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane

namespace SystolicGrowth

/-- A positive displacement bound excludes every nonidentity fixed point. -/
theorem subgroup_free_of_displacement_lower
    (H : Subgroup SL(2, ℝ)) {L : ℝ} (hL : 0 < L)
    (hdisp : ∀ γ : H, γ ≠ 1 → ∀ z : ℍ, L ≤ dist z (γ • z)) :
    ∀ γ : H, ∀ z : ℍ, γ • z = z → γ = 1 := by
  intro γ z hfix
  by_contra hγ
  have h := hdisp γ hγ z
  rw [hfix, dist_self] at h
  exact (not_le_of_gt hL) h

/-- A positive displacement gap at one point isolates the subgroup identity.
Translations then make the entire inherited subgroup topology discrete. -/
theorem subgroup_isDiscrete_of_displacement_lower_at
    (H : Subgroup SL(2, ℝ)) {L : ℝ} (hL : 0 < L) (z : ℍ)
    (hdisp : ∀ γ : H, γ ≠ 1 → L ≤ dist z (γ • z)) :
    IsDiscrete (H : Set SL(2, ℝ)) := by
  have hopen : IsOpen {γ : H | dist z (γ • z) < L} :=
    isOpen_lt (continuous_const.dist
      (continuous_subtype_val.smul continuous_const)) continuous_const
  have hset : {γ : H | dist z (γ • z) < L} = ({1} : Set H) := by
    ext γ
    constructor
    · intro hγ
      apply Set.mem_singleton_iff.mpr
      by_contra hne
      exact (not_lt_of_ge (hdisp γ hne)) hγ
    · intro hγ
      rcases Set.mem_singleton_iff.mp hγ with rfl
      change dist z ((1 : H) • z) < L
      simpa only [one_smul, dist_self] using hL
  have hsingleton : IsOpen ({1} : Set H) := hset ▸ hopen
  letI : DiscreteTopology H := discreteTopology_of_isOpen_singleton_one hsingleton
  exact isDiscrete_iff_discreteTopology.mpr inferInstance

/-- The all-points displacement contract of the chain constructor supplies
the identity gap in particular at the standard upper-half-plane point. -/
theorem subgroup_isDiscrete_of_displacement_lower
    (H : Subgroup SL(2, ℝ)) {L : ℝ} (hL : 0 < L)
    (hdisp : ∀ γ : H, γ ≠ 1 → ∀ z : ℍ, L ≤ dist z (γ • z)) :
    IsDiscrete (H : Set SL(2, ℝ)) :=
  subgroup_isDiscrete_of_displacement_lower_at H hL I
    (fun γ hγ => hdisp γ hγ I)

#print axioms subgroup_free_of_displacement_lower
#print axioms subgroup_isDiscrete_of_displacement_lower_at
#print axioms subgroup_isDiscrete_of_displacement_lower

end SystolicGrowth
