module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Separation.Basic

@[expose] public section

/-!
# Compact lifts for finite-sheet-free coverings

A surjective covering of a compact Hausdorff base has a compact subset whose
image is the whole base. The construction uses finitely many evenly covered
neighborhoods and a local sheet over compact subsets subordinate to that cover;
it does not assume a compact fundamental domain or a finite fiber.
-/

open Set

namespace SystolicGrowth

universe u v

theorem exists_compact_set_surjecting_under_covering
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    [CompactSpace B] [T2Space B] (p : E → B)
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    ∃ K : Set E, IsCompact K ∧ p '' K = Set.univ := by
  classical
  let U : B → Set B := fun b => Classical.choose (hp b).2
  have hchart (b : B) :
      b ∈ U b ∧ IsOpen (U b) ∧ IsOpen (p ⁻¹' U b) ∧
        ∃ H : {e : E // p e ∈ U b} ≃ₜ U b × {e : E // p e = b},
          ∀ e, (H e).1.1 = p e :=
    Classical.choose_spec (hp b).2
  let H (b : B) : {e : E // p e ∈ U b} ≃ₜ U b × {e : E // p e = b} :=
    Classical.choose (hchart b).2.2.2
  have hH (b : B) (e : {z : E // p z ∈ U b}) :
      ((H b) e).1.1 = p e :=
    Classical.choose_spec (hchart b).2.2.2 e
  let e₀ (b : B) : E := Classical.choose (hsurj b)
  have he₀ (b : B) : p (e₀ b) = b := Classical.choose_spec (hsurj b)
  let localSection (b : B) (y : U b) : E :=
    ((H b).symm (y, ⟨e₀ b, he₀ b⟩)).1
  have localSection_projection (b : B) (y : U b) : p (localSection b y) = y := by
    have h := hH b ((H b).symm (y, ⟨e₀ b, he₀ b⟩))
    dsimp [localSection] at h ⊢
    simpa using h.symm
  have localSection_continuous (b : B) : Continuous (localSection b) :=
    continuous_subtype_val.comp ((H b).symm.continuous.comp
      (continuous_id.prodMk continuous_const))
  have hcover : (Set.univ : Set B) ⊆ ⋃ b, U b := by
    intro b _
    exact Set.mem_iUnion.mpr ⟨b, (hchart b).1⟩
  obtain ⟨t, hfinite⟩ := isCompact_univ.elim_finite_subcover U
    (fun b => (hchart b).2.1) hcover
  obtain ⟨K₀, hK₀compact, hK₀subset, hK₀cover⟩ :=
    isCompact_univ.finite_compact_cover t U
      (fun b hb => (hchart b).2.1) hfinite
  let lift (b : B) : Set E :=
    Set.range (fun z : ↥(K₀ b) => localSection b ⟨z.1, hK₀subset b z.2⟩)
  have hlift_compact (b : B) : IsCompact (lift b) := by
    letI : CompactSpace ↥(K₀ b) := isCompact_iff_compactSpace.mp (hK₀compact b)
    have hcontinuous : Continuous (fun z : ↥(K₀ b) =>
        localSection b ⟨z.1, hK₀subset b z.2⟩) :=
      (localSection_continuous b).comp
        (continuous_subtype_val.subtype_mk (fun z => hK₀subset b z.2))
    exact isCompact_range hcontinuous
  have hsection_projection (b : B) (z : ↥(K₀ b)) :
      p (localSection b ⟨z.1, hK₀subset b z.2⟩) = z.1 :=
    localSection_projection b ⟨z.1, hK₀subset b z.2⟩
  let K : Set E := ⋃ b ∈ t, lift b
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact t.isCompact_biUnion (fun b hb => hlift_compact b)
  have hKimage : p '' K = Set.univ := by
    ext b
    constructor
    · intro _
      exact Set.mem_univ b
    · intro _
      have hbK : b ∈ ⋃ i ∈ t, K₀ i := by
        rw [← hK₀cover]
        exact Set.mem_univ b
      rcases Set.mem_iUnion.mp hbK with ⟨i, hi⟩
      rcases Set.mem_iUnion.mp hi with ⟨hit, hbi⟩
      refine ⟨localSection i ⟨b, hK₀subset i hbi⟩, ?_, hsection_projection i ⟨b, hbi⟩⟩
      change localSection i ⟨b, hK₀subset i hbi⟩ ∈ ⋃ j ∈ t, lift j
      apply Set.mem_iUnion.mpr
      refine ⟨i, Set.mem_iUnion.mpr ⟨hit, ?_⟩⟩
      change localSection i ⟨b, hK₀subset i hbi⟩ ∈
        Set.range (fun z : ↥(K₀ i) => localSection i ⟨z.1, hK₀subset i z.2⟩)
      exact ⟨⟨b, hbi⟩, rfl⟩
  exact ⟨K, hKcompact, hKimage⟩

#print axioms exists_compact_set_surjecting_under_covering

end SystolicGrowth
