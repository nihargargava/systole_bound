module

public import BuserSarnak.FreeGroupNielsenBasicPrograms

@[expose] public section

/-!
# Transport of elementary Nielsen programs

An injective alphabet map transports each existing elementary move. The
transported program agrees with the original program on the embedded free
group and fixes every generator outside the embedded alphabet. This is the
extension needed when recursively normalizing a residual alphabet.
-/

namespace SystolicGrowth

noncomputable section

namespace FreeGroupNielsenMove

variable {X Y : Type*}

/-- Transport one elementary move along an injective alphabet map. -/
def liftAlong (f : X → Y) (hf : Function.Injective f) :
    FreeGroupNielsenMove X → FreeGroupNielsenMove Y
  | .shear a b hab => .shear (f a) (f b) (fun h => hab (hf h))
  | .inversion a => .inversion (f a)

/-- The transported elementary automorphism agrees with the original one
on the embedded free group. -/
theorem liftAlong_map (f : X → Y) (hf : Function.Injective f)
    (move : FreeGroupNielsenMove X) (g : FreeGroup X) :
    toEquiv (liftAlong f hf move) (FreeGroup.map f g) =
      FreeGroup.map f (toEquiv move g) := by
  classical
  have hhom : (toEquiv (liftAlong f hf move)).toMonoidHom.comp (FreeGroup.map f) =
      (FreeGroup.map f).comp (toEquiv move).toMonoidHom := by
    apply FreeGroup.ext_hom
    intro x
    cases move with
    | shear a b hab =>
      by_cases hx : x = a
      · subst x
        simp [liftAlong, toEquiv]
      · have hfx : f x ≠ f a := fun h => hx (hf h)
        simp [liftAlong, toEquiv, hx, hfx]
    | inversion a =>
      by_cases hx : x = a
      · subst x
        simp [liftAlong, toEquiv]
      · have hfx : f x ≠ f a := fun h => hx (hf h)
        simp [liftAlong, toEquiv, hx, hfx]
  exact DFunLike.congr_fun hhom g

/-- No transported move affects a generator outside the alphabet image. -/
theorem liftAlong_apply_of_not_mem_range (f : X → Y) (hf : Function.Injective f)
    (move : FreeGroupNielsenMove X) (y : Y) (hy : y ∉ Set.range f) :
    toEquiv (liftAlong f hf move) (FreeGroup.of y) = FreeGroup.of y := by
  classical
  cases move with
  | shear a b hab =>
    have hya : y ≠ f a := fun h => hy ⟨a, h.symm⟩
    simp [liftAlong, toEquiv, hya]
  | inversion a =>
    have hya : y ≠ f a := fun h => hy ⟨a, h.symm⟩
    simp [liftAlong, toEquiv, hya]

end FreeGroupNielsenMove

namespace FreeGroupNielsenProgram

variable {X Y : Type*}

/-- Transport a literal elementary move trace without changing its order. -/
def liftProgram (f : X → Y) (hf : Function.Injective f)
    (P : List (FreeGroupNielsenMove X)) : List (FreeGroupNielsenMove Y) :=
  P.map (FreeGroupNielsenMove.liftAlong f hf)

@[simp] theorem liftProgram_nil (f : X → Y) (hf : Function.Injective f) :
    liftProgram f hf [] = [] := rfl

@[simp] theorem liftProgram_cons (f : X → Y) (hf : Function.Injective f)
    (move : FreeGroupNielsenMove X) (P : List (FreeGroupNielsenMove X)) :
    liftProgram f hf (move :: P) =
      FreeGroupNielsenMove.liftAlong f hf move :: liftProgram f hf P := rfl

@[simp] theorem liftProgram_append (f : X → Y) (hf : Function.Injective f)
    (P Q : List (FreeGroupNielsenMove X)) :
    liftProgram f hf (P ++ Q) = liftProgram f hf P ++ liftProgram f hf Q :=
  List.map_append

/-- The transported program has exactly the old action on the embedded free
group, for every group element rather than only for generators. -/
theorem liftProgram_map (f : X → Y) (hf : Function.Injective f)
    (P : List (FreeGroupNielsenMove X)) (g : FreeGroup X) :
    toEquiv (liftProgram f hf P) (FreeGroup.map f g) =
      FreeGroup.map f (toEquiv P g) := by
  induction P generalizing g with
  | nil => rfl
  | cons move P ih =>
    simp only [liftProgram_cons, toEquiv_cons, MulEquiv.trans_apply]
    rw [FreeGroupNielsenMove.liftAlong_map f hf move g]
    exact ih (FreeGroupNielsenMove.toEquiv move g)

/-- A transported residual-alphabet program fixes every generator outside
the residual image, including previously extracted handle generators. -/
theorem liftProgram_apply_of_not_mem_range (f : X → Y) (hf : Function.Injective f)
    (P : List (FreeGroupNielsenMove X)) (y : Y) (hy : y ∉ Set.range f) :
    toEquiv (liftProgram f hf P) (FreeGroup.of y) = FreeGroup.of y := by
  induction P with
  | nil => rfl
  | cons move P ih =>
    simp only [liftProgram_cons, toEquiv_cons, MulEquiv.trans_apply]
    rw [FreeGroupNielsenMove.liftAlong_apply_of_not_mem_range f hf move y hy]
    exact ih

/-- Transport through a genuine alphabet equivalence is conjugation by its
canonical free-group renaming, not by an arbitrary free-group equivalence. -/
theorem liftProgram_eq_conj (e : X ≃ Y) (P : List (FreeGroupNielsenMove X)) :
    toEquiv (liftProgram e e.injective P) =
      (FreeGroup.freeGroupCongr e).symm.trans
        ((toEquiv P).trans (FreeGroup.freeGroupCongr e)) := by
  ext g
  have h := liftProgram_map e e.injective P ((FreeGroup.freeGroupCongr e).symm g)
  change toEquiv (liftProgram e e.injective P)
      ((FreeGroup.freeGroupCongr e) ((FreeGroup.freeGroupCongr e).symm g)) =
    (FreeGroup.freeGroupCongr e)
      (toEquiv P ((FreeGroup.freeGroupCongr e).symm g)) at h
  simpa only [MulEquiv.apply_symm_apply, MulEquiv.trans_apply] using h

end FreeGroupNielsenProgram

end

end SystolicGrowth

#print axioms SystolicGrowth.FreeGroupNielsenMove.liftAlong_map
#print axioms SystolicGrowth.FreeGroupNielsenMove.liftAlong_apply_of_not_mem_range
#print axioms SystolicGrowth.FreeGroupNielsenProgram.liftProgram_map
#print axioms SystolicGrowth.FreeGroupNielsenProgram.liftProgram_apply_of_not_mem_range
#print axioms SystolicGrowth.FreeGroupNielsenProgram.liftProgram_eq_conj
