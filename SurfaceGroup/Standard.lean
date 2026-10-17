module

public import Core.SystolicCore
public import SurfaceGroup.Presentation
public import Mathlib.Data.List.OfFn

@[expose] public section

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete.Presentations

lemma cyclicPrefixProduct_eq_ofFn {G : Type*} [Group G]
    (W : ℕ → G) (n : ℕ) :
    cyclicPrefixProduct W n = (List.ofFn fun i : Fin n => W i.val).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [cyclicPrefixProduct_succ, List.ofFn_succ', List.prod_concat, ih]
      congr 1

def cyclicSurfaceGeneratorEquivSum (n d : ℕ) :
    CyclicSurfaceGenerator n d ≃ ((Fin 1 ⊕ (Fin d × Fin n)) × Bool) where
  toFun
    | .base side => (Sum.inl 0, side)
    | .rest sheet handle side => (Sum.inr (sheet, handle), side)
  invFun
    | (Sum.inl _, side) => .base side
    | (Sum.inr (sheet, handle), side) => .rest sheet handle side
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with ⟨handle, side⟩
    cases handle with
    | inl i =>
        have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
        subst i
        rfl
    | inr pair =>
        rcases pair with ⟨sheet, handle⟩
        rfl

def cyclicHandleEquivStandard (n d : ℕ) :
    (Fin 1 ⊕ (Fin d × Fin n)) ≃ Fin (1 + d * n) :=
  (Equiv.sumCongr (Equiv.refl (Fin 1)) finProdFinEquiv).trans finSumFinEquiv

def cyclicSurfaceGeneratorEquivStandard (n d : ℕ) :
    CyclicSurfaceGenerator n d ≃ SurfaceGenerator (1 + d * n) :=
  (cyclicSurfaceGeneratorEquivSum n d).trans
    (Equiv.prodCongr (cyclicHandleEquivStandard n d) (Equiv.refl Bool))

@[simp] lemma cyclicSurfaceGeneratorEquivStandard_base (n d : ℕ) (side : Bool) :
    cyclicSurfaceGeneratorEquivStandard n d (.base side) =
      ((0 : Fin (1 + d * n)), side) := by
  apply Prod.ext
  · apply Fin.ext
    rfl
  · rfl

@[simp] lemma cyclicSurfaceGeneratorEquivStandard_rest
    (n d : ℕ) (sheet : Fin d) (handle : Fin n) (side : Bool) :
    cyclicSurfaceGeneratorEquivStandard n d (.rest sheet handle side) =
      (Fin.natAdd 1 (finProdFinEquiv (sheet, handle)), side) := by
  apply Prod.ext
  · apply Fin.ext
    simp [cyclicSurfaceGeneratorEquivStandard, cyclicHandleEquivStandard,
      cyclicSurfaceGeneratorEquivSum, finProdFinEquiv]
  · rfl

def cyclicSurfaceToStandardGenerator (n d : ℕ) :
    CyclicSurfaceGenerator n d → FreeGroup (SurfaceGenerator (1 + d * n)) :=
  fun x => FreeGroup.of (cyclicSurfaceGeneratorEquivStandard n d x)

def cyclicStandardToSurfaceGenerator (n d : ℕ) :
    SurfaceGenerator (1 + d * n) → FreeGroup (CyclicSurfaceGenerator n d) :=
  fun x => FreeGroup.of ((cyclicSurfaceGeneratorEquivStandard n d).symm x)

def standardSurfaceHandleWord (g : ℕ) (i : Fin g) :
    FreeGroup (SurfaceGenerator g) :=
  FreeGroup.of (i, false) * FreeGroup.of (i, true) *
    (FreeGroup.of (i, false))⁻¹ * (FreeGroup.of (i, true))⁻¹

lemma surfaceRelator_eq_handleWords (g : ℕ) :
    surfaceRelator g = (List.ofFn (standardSurfaceHandleWord g)).prod := by
  rfl

lemma cyclicSurfaceToStandard_sheetWord (n d : ℕ) (sheet : Fin d) :
    FreeGroup.lift (cyclicSurfaceToStandardGenerator n d)
        (cyclicSurfaceSheetWord n d sheet) =
      (List.ofFn fun handle : Fin n =>
        standardSurfaceHandleWord (1 + d * n)
          (Fin.natAdd 1 (finProdFinEquiv (sheet, handle)))).prod := by
  rw [cyclicSurfaceSheetWord, map_list_prod]
  apply congrArg List.prod
  rw [List.map_ofFn, List.ofFn_inj]
  funext handle
  simp [standardSurfaceHandleWord, cyclicSurfaceToStandardGenerator,
    map_mul, map_inv]

lemma cyclicSurfaceToStandard_prefix (n d : ℕ) :
    FreeGroup.lift (cyclicSurfaceToStandardGenerator n d)
        (cyclicPrefixProduct (cyclicSurfaceSheetWordNat n d) d) =
      (List.ofFn fun sheet : Fin d =>
        (List.ofFn fun handle : Fin n =>
          standardSurfaceHandleWord (1 + d * n)
            (Fin.natAdd 1 (finProdFinEquiv (sheet, handle)))).prod).prod := by
  rw [cyclicPrefixProduct_eq_ofFn, map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  rw [List.ofFn_inj]
  funext sheet
  have hword : cyclicSurfaceSheetWordNat n d sheet.val =
      cyclicSurfaceSheetWord n d sheet := by
    unfold cyclicSurfaceSheetWordNat
    rw [dif_pos sheet.isLt]
  simp only [Function.comp_apply]
  rw [hword]
  exact cyclicSurfaceToStandard_sheetWord n d sheet

lemma standardSurfaceTail_eq_nested (n d : ℕ) :
    (List.ofFn fun i : Fin (d * n) =>
      standardSurfaceHandleWord (1 + d * n) (Fin.natAdd 1 i)).prod =
      (List.ofFn fun sheet : Fin d =>
        (List.ofFn fun handle : Fin n =>
          standardSurfaceHandleWord (1 + d * n)
            (Fin.natAdd 1 (finProdFinEquiv (sheet, handle)))).prod).prod := by
  have hlist :
      (List.ofFn fun i : Fin (d * n) =>
        standardSurfaceHandleWord (1 + d * n) (Fin.natAdd 1 i)) =
        List.flatten (List.ofFn fun sheet : Fin d =>
          List.ofFn fun handle : Fin n =>
            standardSurfaceHandleWord (1 + d * n)
              (Fin.natAdd 1 (finProdFinEquiv (sheet, handle)))) := by
    rw [List.ofFn_mul]
    apply congrArg List.flatten
    rw [List.ofFn_inj]
    funext sheet
    rw [List.ofFn_inj]
    funext handle
    apply congrArg (standardSurfaceHandleWord (1 + d * n))
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [hlist, List.prod_flatten, List.map_ofFn]
  congr 1

lemma surfaceRelator_cyclicExpansion (n d : ℕ) :
    surfaceRelator (1 + d * n) =
      standardSurfaceHandleWord (1 + d * n) 0 *
        (List.ofFn fun sheet : Fin d =>
          (List.ofFn fun handle : Fin n =>
            standardSurfaceHandleWord (1 + d * n)
              (Fin.natAdd 1 (finProdFinEquiv (sheet, handle)))).prod).prod := by
  rw [surfaceRelator_eq_handleWords, List.ofFn_add, List.prod_append,
    standardSurfaceTail_eq_nested]
  congr 1

lemma cyclicSurfaceRelator_maps_to_surfaceRelator (n d : ℕ) :
    FreeGroup.lift (cyclicSurfaceToStandardGenerator n d)
        (cyclicSurfaceRelator n d) =
      surfaceRelator (1 + d * n) := by
  rw [cyclicSurfaceRelator]
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of,
    cyclicSurfaceToStandardGenerator,
    cyclicSurfaceGeneratorEquivStandard_base]
  rw [cyclicSurfaceToStandard_prefix]
  exact (surfaceRelator_cyclicExpansion n d).symm

lemma cyclicStandard_lift_cyclicSurface_lift (n d : ℕ)
    (w : FreeGroup (CyclicSurfaceGenerator n d)) :
    FreeGroup.lift (cyclicStandardToSurfaceGenerator n d)
        (FreeGroup.lift (cyclicSurfaceToStandardGenerator n d) w) = w := by
  have hhom :
      (FreeGroup.lift (cyclicStandardToSurfaceGenerator n d)).comp
          (FreeGroup.lift (cyclicSurfaceToStandardGenerator n d)) =
        MonoidHom.id (FreeGroup (CyclicSurfaceGenerator n d)) := by
    ext x
    simp [cyclicSurfaceToStandardGenerator, cyclicStandardToSurfaceGenerator]
  exact congrArg (fun f : FreeGroup (CyclicSurfaceGenerator n d) →*
    FreeGroup (CyclicSurfaceGenerator n d) => f w) hhom

lemma cyclicSurface_lift_cyclicStandard_lift (n d : ℕ)
    (w : FreeGroup (SurfaceGenerator (1 + d * n))) :
    FreeGroup.lift (cyclicSurfaceToStandardGenerator n d)
        (FreeGroup.lift (cyclicStandardToSurfaceGenerator n d) w) = w := by
  have hhom :
      (FreeGroup.lift (cyclicSurfaceToStandardGenerator n d)).comp
          (FreeGroup.lift (cyclicStandardToSurfaceGenerator n d)) =
        MonoidHom.id (FreeGroup (SurfaceGenerator (1 + d * n))) := by
    ext x
    simp [cyclicSurfaceToStandardGenerator, cyclicStandardToSurfaceGenerator]
  exact congrArg (fun f : FreeGroup (SurfaceGenerator (1 + d * n)) →*
    FreeGroup (SurfaceGenerator (1 + d * n)) => f w) hhom

lemma surfaceRelator_maps_to_cyclicSurfaceRelator (n d : ℕ) :
    FreeGroup.lift (cyclicStandardToSurfaceGenerator n d)
        (surfaceRelator (1 + d * n)) =
      cyclicSurfaceRelator n d := by
  have h := congrArg (FreeGroup.lift (cyclicStandardToSurfaceGenerator n d))
    (cyclicSurfaceRelator_maps_to_surfaceRelator n d)
  rw [cyclicStandard_lift_cyclicSurface_lift] at h
  exact h.symm

lemma cyclicSurface_maps_standard_relators (n d : ℕ) :
    ∀ r ∈ ({cyclicSurfaceRelator n d} :
      Set (FreeGroup (CyclicSurfaceGenerator n d))),
      RelatorEquivalent ({surfaceRelator (1 + d * n)} :
        Set (FreeGroup (SurfaceGenerator (1 + d * n))))
        (FreeGroup.lift (cyclicSurfaceToStandardGenerator n d) r) 1 := by
  intro r hr
  rw [Set.mem_singleton_iff.mp hr,
    cyclicSurfaceRelator_maps_to_surfaceRelator]
  exact RelatorEquivalent.of_mem (Set.mem_singleton _)

lemma cyclicStandard_maps_surface_relators (n d : ℕ) :
    ∀ r ∈ ({surfaceRelator (1 + d * n)} :
      Set (FreeGroup (SurfaceGenerator (1 + d * n)))),
      RelatorEquivalent ({cyclicSurfaceRelator n d} :
        Set (FreeGroup (CyclicSurfaceGenerator n d)))
        (FreeGroup.lift (cyclicStandardToSurfaceGenerator n d) r) 1 := by
  intro r hr
  rw [Set.mem_singleton_iff.mp hr,
    surfaceRelator_maps_to_cyclicSurfaceRelator]
  exact RelatorEquivalent.of_mem (Set.mem_singleton _)

lemma cyclicSurface_standard_from_to (n d : ℕ) :
    ∀ x : CyclicSurfaceGenerator n d,
      RelatorEquivalent ({cyclicSurfaceRelator n d} :
        Set (FreeGroup (CyclicSurfaceGenerator n d)))
        (FreeGroup.lift (cyclicStandardToSurfaceGenerator n d)
          (cyclicSurfaceToStandardGenerator n d x))
        (FreeGroup.of x) := by
  intro x
  apply RelatorEquivalent.of_eq
  simpa [cyclicSurfaceToStandardGenerator] using
    cyclicStandard_lift_cyclicSurface_lift n d (FreeGroup.of x)

lemma cyclicSurface_standard_to_from (n d : ℕ) :
    ∀ x : SurfaceGenerator (1 + d * n),
      RelatorEquivalent ({surfaceRelator (1 + d * n)} :
        Set (FreeGroup (SurfaceGenerator (1 + d * n))))
        (FreeGroup.lift (cyclicSurfaceToStandardGenerator n d)
          (cyclicStandardToSurfaceGenerator n d x))
        (FreeGroup.of x) := by
  intro x
  apply RelatorEquivalent.of_eq
  simpa [cyclicStandardToSurfaceGenerator] using
    cyclicSurface_lift_cyclicStandard_lift n d (FreeGroup.of x)

def cyclicSurfaceTietzeEquivStandard (n d : ℕ) :
    TietzeEquiv
      ({cyclicSurfaceRelator n d} :
        Set (FreeGroup (CyclicSurfaceGenerator n d)))
      ({surfaceRelator (1 + d * n)} :
        Set (FreeGroup (SurfaceGenerator (1 + d * n)))) :=
  TietzeEquiv.ofGeneratorMapsRelatorEquivalent
    (cyclicSurfaceToStandardGenerator n d)
    (cyclicStandardToSurfaceGenerator n d)
    (cyclicSurface_maps_standard_relators n d)
    (cyclicStandard_maps_surface_relators n d)
    (cyclicSurface_standard_from_to n d)
    (cyclicSurface_standard_to_from n d)

noncomputable def cyclicSurfacePresentedEquivStandard (n d : ℕ) :
    PresentedGroup ({cyclicSurfaceRelator n d} :
      Set (FreeGroup (CyclicSurfaceGenerator n d))) ≃*
      SurfaceGroup (1 + d * n) :=
  (cyclicSurfaceTietzeEquivStandard n d).presentedEquiv

end
end SystolicGrowth
