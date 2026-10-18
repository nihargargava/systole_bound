module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChartEvaluations
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-!
# Smooth transitions between the actual charts of one seam

On the exact overlap of two native angular charts at the same actual seam,
the signed radius is unchanged and the real angular lifts differ locally by
a fixed integer multiple of `2π`. Openness of the actual angular domains
then identifies the transition locally with an affine translation. This
proves smoothness of these actual transitions, including at the seam; it
does not assume a smooth angular inverse or assert a completed smooth atlas.
-/

open Set Filter UpperHalfPlane
open scoped UpperHalfPlane Topology

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Whenever a fixed angular shift lies in the target angular interval,
the actual same-seam transition is precisely that affine translation. -/
theorem seamAngularComplexChart_transition_eq_add
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (θ ψ : ℝ) (m : ℤ) {z : ℂ}
    (hz : z ∈ (P.seamAngularComplexChart k θ).target)
    (hshift : z.im + (m : ℝ) * (2 * Real.pi) ∈ GluingAngularInterval ψ) :
    P.seamAngularComplexChart k ψ ((P.seamAngularComplexChart k θ).symm z) =
      z + (((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
  rw [P.seamAngularComplexChart_target] at hz
  obtain ⟨a, ha⟩ := hz
  have hangle : a.2.1 + (m : ℝ) * (2 * Real.pi) ∈ GluingAngularInterval ψ := by
    simpa only [← ha, gluingSeamAngularModel_im] using hshift
  let b : GluingSeamAngularDomain C g ψ :=
    (a.1, ⟨a.2.1 + (m : ℝ) * (2 * Real.pi), hangle⟩)
  have hexp : Circle.exp a.2.1 = Circle.exp b.2.1 := by
    change Circle.exp a.2.1 = Circle.exp (a.2.1 + (m : ℝ) * (2 * Real.pi))
    rw [Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
  have hpoint : P.seamAngularPoint k θ a = P.seamAngularPoint k ψ b :=
    (P.seamAngularPoint_eq_iff k θ ψ a b).mpr ⟨rfl, hexp⟩
  calc
    P.seamAngularComplexChart k ψ ((P.seamAngularComplexChart k θ).symm z) =
        P.seamAngularComplexChart k ψ (P.seamAngularPoint k θ a) := by
          rw [← ha, P.seamAngularComplexChart_symm_apply]
    _ = P.seamAngularComplexChart k ψ (P.seamAngularPoint k ψ b) :=
      congrArg (P.seamAngularComplexChart k ψ) hpoint
    _ = gluingSeamAngularModel C g ψ b := P.seamAngularComplexChart_apply k ψ b
    _ = z + (((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      rw [← ha]
      apply Complex.ext <;> simp [b]

/-- Actual angular lifts at an overlap point differ by an integer multiple
of a full turn, and that same integer works throughout a neighborhood. -/
theorem seamAngularComplexChart_transition_eventually_eq_add
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (θ ψ : ℝ) {z : ℂ}
    (hz : z ∈ ((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart k ψ)).source) :
    ∃ m : ℤ, ∀ᶠ w in 𝓝 z,
      P.seamAngularComplexChart k ψ ((P.seamAngularComplexChart k θ).symm w) =
        w + (((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
  change z ∈ (P.seamAngularComplexChart k θ).target ∧
    (P.seamAngularComplexChart k θ).symm z ∈
      (P.seamAngularComplexChart k ψ).source at hz
  have htarget := hz.1
  rw [P.seamAngularComplexChart_target] at htarget
  obtain ⟨a, ha⟩ := htarget
  have hsource := hz.2
  rw [← ha, P.seamAngularComplexChart_symm_apply,
    P.seamAngularComplexChart_source] at hsource
  obtain ⟨b, hb⟩ := hsource
  have hexp := ((P.seamAngularPoint_eq_iff k θ ψ a b).mp hb.symm).2
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hexp.symm
  have hshift : z.im + (m : ℝ) * (2 * Real.pi) ∈ GluingAngularInterval ψ := by
    rw [← ha, gluingSeamAngularModel_im, ← hm]
    exact b.2.2
  have hθ : ∀ᶠ w in 𝓝 z, w ∈ (P.seamAngularComplexChart k θ).target :=
    (P.seamAngularComplexChart k θ).open_target.mem_nhds hz.1
  have hψ : ∀ᶠ w in 𝓝 z,
      w.im + (m : ℝ) * (2 * Real.pi) ∈ GluingAngularInterval ψ :=
    (isOpen_Ioo.preimage (Complex.continuous_im.add continuous_const)).mem_nhds hshift
  refine ⟨m, ?_⟩
  filter_upwards [hθ, hψ] with w hwθ hwψ
  exact P.seamAngularComplexChart_transition_eq_add k θ ψ m hwθ hwψ

/-- Every native transition between charts of the same actual seam is smooth
on its exact native source, including points with signed radius zero. -/
theorem seamAngularComplexChart_transition_contDiffOn
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ ψ : ℝ) :
    ContDiffOn ℝ ⊤
      (fun z : ℂ => P.seamAngularComplexChart k ψ
        ((P.seamAngularComplexChart k θ).symm z))
      (((P.seamAngularComplexChart k θ).symm.trans
        (P.seamAngularComplexChart k ψ)).source) := by
  intro z hz
  obtain ⟨m, hm⟩ := P.seamAngularComplexChart_transition_eventually_eq_add k θ ψ hz
  have h : ContDiff ℝ ⊤ (fun w : ℂ =>
      w + (((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) :=
    contDiff_id.add contDiff_const
  exact (h.contDiffAt.congr_of_eventuallyEq hm).contDiffWithinAt

/-- The same smoothness statement for the native composed partial homeomorphism. -/
theorem seamAngularComplexChart_trans_contDiffOn
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ ψ : ℝ) :
    ContDiffOn ℝ ⊤
      ((P.seamAngularComplexChart k θ).symm.trans (P.seamAngularComplexChart k ψ))
      (((P.seamAngularComplexChart k θ).symm.trans
        (P.seamAngularComplexChart k ψ)).source) :=
  P.seamAngularComplexChart_transition_contDiffOn k θ ψ

#print axioms seamAngularComplexChart_transition_eventually_eq_add
#print axioms seamAngularComplexChart_transition_contDiffOn
#print axioms seamAngularComplexChart_trans_contDiffOn

end SystolicGrowth.ExerciseGluingPreparation
