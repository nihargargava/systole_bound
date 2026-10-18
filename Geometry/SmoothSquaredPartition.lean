module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
# Smooth square partitions for the surface gradient

Normalizing a finite smooth bump covering by the square root of the sum
of its squares gives smooth functions whose squares sum to one. Their
supports remain inside the prescribed coordinate neighborhoods. These are
the exact weights for realizing the Riemannian gradient in a finite product
of ordinary `L²` spaces without choosing a global tangent frame.
-/

open Set Manifold
open scoped ContDiff

namespace SystolicGrowth

noncomputable section

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]
  {ι : Type*} [Fintype ι]

/-- The positive denominator of the square-normalized covering. -/
def smoothSquareCoverDenominator (f : ι → C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (x : M) : ℝ :=
  ∑ i, (f i x) ^ 2

theorem smoothSquareCoverDenominator_pos
    (f : ι → C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯)
    (hf : ∀ x : M, ∃ i, 0 < f i x) (x : M) :
    0 < smoothSquareCoverDenominator f x := by
  obtain ⟨i, hi⟩ := hf x
  exact Finset.sum_pos' (fun j _ => sq_nonneg (f j x))
    ⟨i, Finset.mem_univ i, sq_pos_of_pos hi⟩

theorem smoothSquareCoverDenominator_contMDiff
    (f : ι → C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (smoothSquareCoverDenominator f) := by
  apply contMDiff_finsetSum
  intro i _
  exact (f i).contMDiff.pow 2

/-- An actual smooth normalized bump, with unchanged support. -/
def smoothSquareCover (f : ι → C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯)
    (hf : ∀ x : M, ∃ i, 0 < f i x) (i : ι) : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯ :=
  ⟨fun x => f i x / Real.sqrt (smoothSquareCoverDenominator f x), by
    intro x
    have hd := smoothSquareCoverDenominator_pos f hf x
    have hs := (Real.contDiffAt_sqrt hd.ne').comp_contMDiffAt
      (smoothSquareCoverDenominator_contMDiff f x)
    exact ((f i).contMDiff x).div₀ hs (Real.sqrt_pos.mpr hd).ne'⟩

@[simp] theorem smoothSquareCover_apply
    (f : ι → C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯)
    (hf : ∀ x : M, ∃ i, 0 < f i x) (i : ι) (x : M) :
    smoothSquareCover f hf i x = f i x / Real.sqrt (smoothSquareCoverDenominator f x) := rfl

theorem smoothSquareCover_sum_sq
    (f : ι → C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯)
    (hf : ∀ x : M, ∃ i, 0 < f i x) (x : M) :
    ∑ i, (smoothSquareCover f hf i x) ^ 2 = 1 := by
  simp only [smoothSquareCover_apply, div_pow, ← Finset.sum_div]
  rw [Real.sq_sqrt (smoothSquareCoverDenominator_pos f hf x).le]
  exact div_self (smoothSquareCoverDenominator_pos f hf x).ne'

theorem smoothSquareCover_support
    (f : ι → C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯)
    (hf : ∀ x : M, ∃ i, 0 < f i x) (i : ι) :
    Function.support (smoothSquareCover f hf i) = Function.support (f i) := by
  ext x
  simp only [Function.mem_support, smoothSquareCover_apply]
  rw [div_ne_zero_iff]
  exact and_iff_left (Real.sqrt_pos.mpr (smoothSquareCoverDenominator_pos f hf x)).ne'

theorem smoothSquareCover_tsupport
    (f : ι → C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯)
    (hf : ∀ x : M, ∃ i, 0 < f i x) (i : ι) :
    tsupport (smoothSquareCover f hf i) = tsupport (f i) := by
  simp only [tsupport, smoothSquareCover_support]

theorem smoothSquareCover_nonneg
    (f : ι → C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯)
    (hf : ∀ x : M, ∃ i, 0 < f i x)
    (hnonneg : ∀ i x, 0 ≤ f i x) (i : ι) (x : M) :
    0 ≤ smoothSquareCover f hf i x :=
  div_nonneg (hnonneg i x) (Real.sqrt_nonneg _)

/-- A finite smooth square partition subordinate to any prescribed
neighborhoods on the compact surface. The finite family is constructed
from the smooth bump-covering theorem, not supplied as a premise. -/
theorem exists_smoothSquareCover_subordinate
    [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, ℂ) ∞ M]
    (U : M → Set M) (hU : ∀ x, U x ∈ nhds x) :
    ∃ (N : ℕ) (c : Fin N → M) (τ : Fin N → C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯),
      (∀ i, tsupport (τ i) ⊆ U (c i)) ∧
      (∀ i x, 0 ≤ τ i x) ∧ (∀ x, ∑ i, (τ i x) ^ 2 = 1) := by
  classical
  obtain ⟨κ, fs, hfs⟩ := SmoothBumpCovering.exists_isSubordinate 𝓘(ℝ, ℂ)
    (s := (univ : Set M)) isClosed_univ (fun x _ => hU x)
  letI : Fintype κ := fs.fintype
  let e := Fintype.equivFin κ
  let f : Fin (Fintype.card κ) → C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯ :=
    fun i => ⟨fs (e.symm i), (fs (e.symm i)).contMDiff⟩
  have hf : ∀ x : M, ∃ i, 0 < f i x := by
    intro x
    refine ⟨e (fs.ind x (mem_univ x)), ?_⟩
    change 0 < fs (e.symm (e (fs.ind x (mem_univ x)))) x
    rw [e.symm_apply_apply, fs.apply_ind]
    norm_num
  refine ⟨Fintype.card κ, fun i => fs.c (e.symm i), smoothSquareCover f hf, ?_, ?_, ?_⟩
  · intro i
    rw [smoothSquareCover_tsupport]
    exact hfs (e.symm i)
  · exact smoothSquareCover_nonneg f hf (fun i _ => (fs (e.symm i)).nonneg)
  · exact smoothSquareCover_sum_sq f hf

#print axioms smoothSquareCover_sum_sq
#print axioms smoothSquareCover_tsupport
#print axioms exists_smoothSquareCover_subordinate

end

end SystolicGrowth
