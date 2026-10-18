module

public import Core.SystolicCore
public import Mathlib.Data.List.OfFn
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# The first handle and the residual standard surface alphabet

The generator equivalence separates the first handle from the remaining
handles without introducing an arbitrary free-group equivalence. The
relator identities preserve the repository's outgoing commutator order.
-/

namespace SystolicGrowth

open scoped commutatorElement

/-- Split the first standard handle off from a positive-genus alphabet. -/
def surfaceHandleGeneratorEquiv (g : ℕ) :
    SurfaceGenerator (g + 1) ≃ Bool ⊕ SurfaceGenerator g where
  toFun := fun p => Fin.cases (Sum.inl p.2) (fun i => Sum.inr (i, p.2)) p.1
  invFun := Sum.elim (fun b => (0, b)) (fun p => (p.1.succ, p.2))
  left_inv := by
    rintro ⟨i, b⟩
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv := by
    intro p
    cases p with
    | inl b => rfl
    | inr p => rfl

@[simp] theorem surfaceHandleGeneratorEquiv_zero (g : ℕ) (b : Bool) :
    surfaceHandleGeneratorEquiv g (0, b) = Sum.inl b := rfl

@[simp] theorem surfaceHandleGeneratorEquiv_succ (g : ℕ) (i : Fin g) (b : Bool) :
    surfaceHandleGeneratorEquiv g (i.succ, b) = Sum.inr (i, b) := rfl

@[simp] theorem surfaceHandleGeneratorEquiv_symm_inl (g : ℕ) (b : Bool) :
    (surfaceHandleGeneratorEquiv g).symm (Sum.inl b) = (0, b) := rfl

@[simp] theorem surfaceHandleGeneratorEquiv_symm_inr (g : ℕ) (p : SurfaceGenerator g) :
    (surfaceHandleGeneratorEquiv g).symm (Sum.inr p) = (p.1.succ, p.2) := rfl

/-- Insert the residual standard alphabet after the first handle. -/
def surfaceTailGeneratorEmbedding (g : ℕ) :
    SurfaceGenerator g → SurfaceGenerator (g + 1) :=
  fun p => (p.1.succ, p.2)

/-- The residual alphabet embeds injectively into the enlarged alphabet. -/
theorem surfaceTailGeneratorEmbedding_injective (g : ℕ) :
    Function.Injective (surfaceTailGeneratorEmbedding g) := by
  intro p q h
  have hi := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  change p.1.succ = q.1.succ at hi
  change p.2 = q.2 at hb
  exact Prod.ext ((Fin.succ_injective g) hi) hb

@[simp] theorem surfaceHandleGeneratorEquiv_tail (g : ℕ) (p : SurfaceGenerator g) :
    surfaceHandleGeneratorEquiv g (surfaceTailGeneratorEmbedding g p) = Sum.inr p := by
  rcases p with ⟨i, b⟩
  rfl

/-- The genus-zero standard relator is the empty product. -/
@[simp] theorem surfaceRelator_zero : surfaceRelator 0 = 1 := by
  simp [surfaceRelator]

/-- The first standard outgoing commutator is followed by the lifted
residual surface relator in increasing handle order. -/
theorem surfaceRelator_succ_handle (g : ℕ) :
    surfaceRelator (g + 1) =
      ⁅FreeGroup.of ((0, false) : SurfaceGenerator (g + 1)),
        FreeGroup.of ((0, true) : SurfaceGenerator (g + 1))⁆ *
      FreeGroup.map (surfaceTailGeneratorEmbedding g) (surfaceRelator g) := by
  simp only [surfaceRelator]
  rw [List.ofFn_succ, List.prod_cons, map_list_prod, List.map_ofFn]
  congr 1

/-- The same exact relator identity in the explicitly split alphabet. This
is the target of the recursive extracted-handle normalization. -/
theorem surfaceRelator_handle_split (g : ℕ) :
    FreeGroup.map (surfaceHandleGeneratorEquiv g) (surfaceRelator (g + 1)) =
      ⁅FreeGroup.of (Sum.inl false : Bool ⊕ SurfaceGenerator g),
        FreeGroup.of (Sum.inl true : Bool ⊕ SurfaceGenerator g)⁆ *
      FreeGroup.map (Sum.inr : SurfaceGenerator g → Bool ⊕ SurfaceGenerator g)
        (surfaceRelator g) := by
  rw [surfaceRelator_succ_handle, map_mul, map_commutatorElement,
    FreeGroup.map.of, FreeGroup.map.of, surfaceHandleGeneratorEquiv_zero,
    surfaceHandleGeneratorEquiv_zero, FreeGroup.map.comp]
  congr 1

end SystolicGrowth

#print axioms SystolicGrowth.surfaceHandleGeneratorEquiv
#print axioms SystolicGrowth.surfaceTailGeneratorEmbedding_injective
#print axioms SystolicGrowth.surfaceRelator_succ_handle
#print axioms SystolicGrowth.surfaceRelator_handle_split
