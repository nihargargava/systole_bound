module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfacePrefixPeripheralAmalgam
public import Geometry.SurfaceClosedPeripheralAmalgam
public import Core.SystolicCore
public import Mathlib.Data.List.OfFn
public import Vendored.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorAddition

@[expose] public section

/-!
# Ordered concatenation of surface relators

Flattening the handles of two consecutive surfaces preserves their order and
turns the prefix/outgoing and final/closed peripheral amalgams into the
standard presentation at the sum genus.
-/

open scoped commutatorElement
open ReidemeisterSchreier.Discrete.Presentations

namespace SystolicGrowth

noncomputable section

/-- Flatten the ordered handle generators of two consecutive surfaces. -/
def surfaceGeneratorAddEquiv (g h : ℕ) :
    SurfaceGenerator g ⊕ SurfaceGenerator h ≃ SurfaceGenerator (g + h) :=
  (Equiv.sumProdDistrib (Fin g) (Fin h) Bool).symm.trans
    (finSumFinEquiv.prodCongr (Equiv.refl Bool))

@[simp]
theorem surfaceGeneratorAddEquiv_inl (g h : ℕ) (i : Fin g) (b : Bool) :
    surfaceGeneratorAddEquiv g h (Sum.inl (i, b)) = (Fin.castAdd h i, b) := by
  simp [surfaceGeneratorAddEquiv]

@[simp]
theorem surfaceGeneratorAddEquiv_inr (g h : ℕ) (i : Fin h) (b : Bool) :
    surfaceGeneratorAddEquiv g h (Sum.inr (i, b)) = (Fin.natAdd g i, b) := by
  simp [surfaceGeneratorAddEquiv]

/-- The two ordered component relators concatenate to the standard relator
without commuting any free-group factors. -/
private theorem surfaceRelatorAddEquiv_map_left (g h : ℕ) :
    FreeGroup.map (surfaceGeneratorAddEquiv g h)
      (FreeGroup.map (Sum.inl : SurfaceGenerator g → SurfaceGenerator g ⊕ SurfaceGenerator h)
        (surfaceRelator g)) =
      (List.ofFn fun i : Fin g =>
        ⁅FreeGroup.of (Fin.castAdd h i, false), FreeGroup.of (Fin.castAdd h i, true)⁆).prod := by
  rw [FreeGroup.map.comp (Sum.inl) (surfaceGeneratorAddEquiv g h)
    (surfaceRelator g)]
  rw [surfaceRelator, map_list_prod, List.map_ofFn]
  congr 1

private theorem surfaceRelatorAddEquiv_map_right (g h : ℕ) :
    FreeGroup.map (surfaceGeneratorAddEquiv g h)
      (FreeGroup.map (Sum.inr : SurfaceGenerator h → SurfaceGenerator g ⊕ SurfaceGenerator h)
        (surfaceRelator h)) =
      (List.ofFn fun i : Fin h =>
        ⁅FreeGroup.of (Fin.natAdd g i, false), FreeGroup.of (Fin.natAdd g i, true)⁆).prod := by
  rw [FreeGroup.map.comp (Sum.inr) (surfaceGeneratorAddEquiv g h)
    (surfaceRelator h)]
  rw [surfaceRelator, map_list_prod, List.map_ofFn]
  congr 1

theorem surfaceRelatorAddEquiv_map (g h : ℕ) :
    FreeGroup.map (surfaceGeneratorAddEquiv g h)
      (FreeGroup.map (Sum.inl : SurfaceGenerator g → SurfaceGenerator g ⊕ SurfaceGenerator h)
          (surfaceRelator g) *
        FreeGroup.map (Sum.inr : SurfaceGenerator h → SurfaceGenerator g ⊕ SurfaceGenerator h)
          (surfaceRelator h)) =
      surfaceRelator (g + h) := by
  rw [map_mul, surfaceRelatorAddEquiv_map_left, surfaceRelatorAddEquiv_map_right,
    surfaceRelator]
  rw [← List.prod_append, List.ofFn_add]
  congr 1

/-- The prefix amalgam after adjoining a closed component's outgoing letter,
flattened to the standard generators at the cumulative genus. -/
def surfacePrefixPeripheralGenusEquiv (g h : ℕ) :
    Monoid.PushoutI
      (surfacePrefixPeripheralBaseMap (B := SurfaceGenerator h) (surfaceRelator g)) ≃*
        FreeGroup (SurfaceGenerator (g + h)) :=
  (surfacePrefixPeripheralAmalgamEquiv (B := SurfaceGenerator h)
    (surfaceRelator g)).trans (FreeGroup.freeGroupCongr (surfaceGeneratorAddEquiv g h))

/-- The actual outgoing prefix word becomes the inverse standard relator. -/
theorem surfacePrefixPeripheralGenusEquiv_outgoing (g h : ℕ) :
    surfacePrefixPeripheralGenusEquiv g h
      (Monoid.PushoutI.of false
        ((FreeGroup.of (Sum.inr ()) *
          FreeGroup.map (Sum.inl : SurfaceGenerator h → SurfaceGenerator h ⊕ Unit)
            (surfaceRelator h))⁻¹)) =
      (surfaceRelator (g + h))⁻¹ := by
  change FreeGroup.map (surfaceGeneratorAddEquiv g h)
    ((surfacePrefixPeripheralAmalgamEquiv (B := SurfaceGenerator h)
      (surfaceRelator g))
      (Monoid.PushoutI.of false
        ((FreeGroup.of (Sum.inr ()) *
          FreeGroup.map (Sum.inl : SurfaceGenerator h → SurfaceGenerator h ⊕ Unit)
            (surfaceRelator h))⁻¹))) = _
  rw [surfacePrefixPeripheralAmalgamEquiv_outgoing, map_inv,
    surfaceRelatorAddEquiv_map]

/-- Flattening carries the endpoint amalgam's single ordered relation to the
standard surface relator at the sum genus. -/
theorem Internal.SurfaceRelatorConcatenationHelpers.surfaceClosedRelator_image_eq (g h : ℕ) :
    FreeGroup.freeGroupCongr (surfaceGeneratorAddEquiv g h) ''
      ({surfaceClosedPeripheralRelator (surfaceRelator g) (surfaceRelator h)} :
        Set (FreeGroup (SurfaceGenerator g ⊕ SurfaceGenerator h))) =
      ({surfaceRelator (g + h)} : Set (FreeGroup (SurfaceGenerator (g + h)))) := by
  rw [Set.image_singleton]
  congr 1
  exact surfaceRelatorAddEquiv_map g h

/-- The final closed amalgam is the standard surface group of the sum genus.
The equivalence is induced by the exact normal-closure image of its ordered
peripheral relation. -/
noncomputable def surfaceClosedPeripheralSurfaceGroupEquiv (g h : ℕ) :
    Monoid.PushoutI (surfaceClosedPeripheralBaseMap
      (surfaceRelator g) (surfaceRelator h)) ≃* SurfaceGroup (g + h) :=
  (surfaceClosedPeripheralAmalgamEquiv (surfaceRelator g) (surfaceRelator h)).trans
    ((PresentedGroup.equivPresentedGroup
        ({surfaceClosedPeripheralRelator (surfaceRelator g) (surfaceRelator h)} :
          Set (FreeGroup (SurfaceGenerator g ⊕ SurfaceGenerator h)))
        (surfaceGeneratorAddEquiv g h)).trans
      (Presented.ofNormalClosureEq
        (congrArg Subgroup.normalClosure (Internal.SurfaceRelatorConcatenationHelpers.surfaceClosedRelator_image_eq g h))))

#print axioms surfaceGeneratorAddEquiv
#print axioms surfaceRelatorAddEquiv_map
#print axioms surfacePrefixPeripheralGenusEquiv_outgoing
#print axioms surfaceClosedPeripheralSurfaceGroupEquiv

end
end SystolicGrowth
