module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

@[expose] public section

/-!
# Fundamental-group transport along a basepoint equality

The maps are the literal identity-map transports used by the native seam
diagram, rather than basepoint changes along a chosen path.
-/

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false in
theorem fundamentalGroup_mapOfEq_id_apply
    {Y : Type*} [TopologicalSpace Y] {x y : Y}
    (h : x = y) (γ : FundamentalGroup Y x) :
    FundamentalGroup.mapOfEq (ContinuousMap.id Y) h γ =
      γ.toPath.cast h.symm h.symm := by
  rw [FundamentalGroup.mapOfEq_apply]
  congr 1
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
  rfl

/-- The based-group equivalence induced by an equality of the actual points. -/
def fundamentalGroupBasepointEquivOfEq
    {Y : Type*} [TopologicalSpace Y] {x y : Y} (h : x = y) :
    FundamentalGroup Y x ≃* FundamentalGroup Y y where
  toFun := FundamentalGroup.mapOfEq (ContinuousMap.id Y) h
  invFun := FundamentalGroup.mapOfEq (ContinuousMap.id Y) h.symm
  left_inv γ := by
    cases h
    simp only [fundamentalGroup_mapOfEq_id_apply,
      Path.Homotopic.Quotient.cast_rfl_rfl]
  right_inv γ := by
    cases h
    simp only [fundamentalGroup_mapOfEq_id_apply,
      Path.Homotopic.Quotient.cast_rfl_rfl]
  map_mul' := (FundamentalGroup.mapOfEq (ContinuousMap.id Y) h).map_mul

theorem fundamentalGroupBasepointEquivOfEq_apply
    {Y : Type*} [TopologicalSpace Y] {x y : Y}
    (h : x = y) (γ : FundamentalGroup Y x) :
    fundamentalGroupBasepointEquivOfEq h γ =
      FundamentalGroup.mapOfEq (ContinuousMap.id Y) h γ := rfl

theorem fundamentalGroupBasepointEquivOfEq_symm_apply
    {Y : Type*} [TopologicalSpace Y] {x y : Y}
    (h : x = y) (γ : FundamentalGroup Y y) :
    (fundamentalGroupBasepointEquivOfEq h).symm γ =
      FundamentalGroup.mapOfEq (ContinuousMap.id Y) h.symm γ := rfl

theorem fundamentalGroupBasepointEquivOfEq_apply_loop
    {Y : Type*} [TopologicalSpace Y] {x y : Y}
    (h : x = y) (p : Path x x) :
    fundamentalGroupBasepointEquivOfEq h
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (p.cast h.symm h.symm)) := by
  rw [fundamentalGroupBasepointEquivOfEq_apply,
    fundamentalGroup_mapOfEq_id_apply, Path.Homotopic.Quotient.mk_cast]

theorem fundamentalGroupBasepointEquivOfEq_symm_apply_loop
    {Y : Type*} [TopologicalSpace Y] {x y : Y}
    (h : x = y) (p : Path y y) :
    (fundamentalGroupBasepointEquivOfEq h).symm
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (p.cast h h)) := by
  rw [fundamentalGroupBasepointEquivOfEq_symm_apply,
    fundamentalGroup_mapOfEq_id_apply, Path.Homotopic.Quotient.mk_cast]

set_option backward.isDefEq.respectTransparency false in
theorem fundamentalGroupBasepointEquivOfEq_comp_map
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (h : f x = y) :
    (fundamentalGroupBasepointEquivOfEq h).toMonoidHom.comp
        (FundamentalGroup.map f x) = FundamentalGroup.mapOfEq f h := by
  ext γ
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
  change FundamentalGroup.mapOfEq (ContinuousMap.id Y) h
      (FundamentalGroup.map f x ⟦p⟧) = FundamentalGroup.mapOfEq f h ⟦p⟧
  rw [fundamentalGroup_mapOfEq_id_apply, FundamentalGroup.map_apply,
    FundamentalGroup.mapOfEq_apply]

theorem fundamentalGroupBasepointEquivOfEq_apply_map
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (h : f x = y)
    (γ : FundamentalGroup X x) :
    fundamentalGroupBasepointEquivOfEq h (FundamentalGroup.map f x γ) =
      FundamentalGroup.mapOfEq f h γ :=
  DFunLike.congr_fun (fundamentalGroupBasepointEquivOfEq_comp_map f h) γ

set_option backward.isDefEq.respectTransparency false in
theorem fundamentalGroupBasepointEquivOfEq_comp_mapOfEq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y z : Y} (f : C(X, Y)) (h : f x = y) (k : y = z) :
    (fundamentalGroupBasepointEquivOfEq k).toMonoidHom.comp
        (FundamentalGroup.mapOfEq f h) =
      FundamentalGroup.mapOfEq f (h.trans k) := by
  cases k
  ext γ
  change FundamentalGroup.mapOfEq (ContinuousMap.id Y) rfl
      (FundamentalGroup.mapOfEq f h γ) = FundamentalGroup.mapOfEq f h γ
  rw [fundamentalGroup_mapOfEq_id_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl]

theorem fundamentalGroupBasepointEquivOfEq_apply_mapOfEq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y z : Y} (f : C(X, Y)) (h : f x = y) (k : y = z)
    (γ : FundamentalGroup X x) :
    fundamentalGroupBasepointEquivOfEq k (FundamentalGroup.mapOfEq f h γ) =
      FundamentalGroup.mapOfEq f (h.trans k) γ :=
  DFunLike.congr_fun (fundamentalGroupBasepointEquivOfEq_comp_mapOfEq f h k) γ

end

end SystolicGrowth
