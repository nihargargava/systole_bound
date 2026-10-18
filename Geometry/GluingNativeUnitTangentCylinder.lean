module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingNativeUnitTangentFermi

@[expose] public section

/-!
# The actual native unit tangent bundle over a full seam cylinder

The principal-angle choice is used only to define a map. On every local
angular chart, actual chart independence identifies it with that chart's
continuous orthonormal unit-vector parametrization.
-/

open Set Filter Bundle ContinuousLinearMap
open scoped Manifold Topology

set_option backward.isDefEq.respectTransparency false

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The true native unit bundle restricted to the whole actual seam neighborhood. -/
abbrev NativeSeamUnitTangentOver
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :=
  {v : P.NativeUnitTangentCarrier // v.val.proj ∈ P.gluedMk '' P.seamNeighborhood k}

/-- A concrete angular chart center for a genuine point of the seam neighborhood. -/
noncomputable def nativeSeamUnitChartCenter
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (b : ↥(P.gluedMk '' P.seamNeighborhood k)) : ℝ :=
  Complex.arg (((P.seamCylinderHomeomorph k).symm b).1 : ℂ)

theorem nativeSeamUnitChartCenter_mem_source
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (b : ↥(P.gluedMk '' P.seamNeighborhood k)) :
    b.val ∈ (P.seamAngularComplexChart k (P.nativeSeamUnitChartCenter k b)).source := by
  let p := (P.seamCylinderHomeomorph k).symm b
  let θ := P.nativeSeamUnitChartCenter k b
  let a : GluingSeamAngularDomain C g θ :=
    (p.2, ⟨θ, by constructor <;> linarith [Real.pi_pos]⟩)
  rw [P.seamAngularComplexChart_source]
  refine ⟨a, ?_⟩
  change (P.seamCylinderHomeomorph k (Circle.exp (Complex.arg (p.1 : ℂ)), p.2)).1 = b.1
  rw [Circle.exp_arg]
  exact congrArg Subtype.val ((P.seamCylinderHomeomorph k).apply_symm_apply b)

/-- Orthonormal unit vectors over the actual seam neighborhood. -/
noncomputable def nativeSeamNeighborhoodUnitTangentParam
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : ↥(P.gluedMk '' P.seamNeighborhood k) × Circle) : P.NativeSeamUnitTangentOver k :=
  ⟨⟨⟨q.1.val, (P.nativeSeamUnitTangentParam k (P.nativeSeamUnitChartCenter k q.1) q.1.val
    (P.nativeSeamUnitChartCenter_mem_source k q.1) q.2).val⟩,
      (P.nativeSeamUnitTangentParam k (P.nativeSeamUnitChartCenter k q.1) q.1.val
        (P.nativeSeamUnitChartCenter_mem_source k q.1) q.2).property⟩, q.1.property⟩

/-- Recover the actual basepoint and its native seam orthonormal unit phase. -/
noncomputable def nativeSeamNeighborhoodUnitTangentAngle
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (v : P.NativeSeamUnitTangentOver k) : ↥(P.gluedMk '' P.seamNeighborhood k) × Circle :=
  let b : ↥(P.gluedMk '' P.seamNeighborhood k) := ⟨v.val.val.proj, v.property⟩
  (b, P.nativeSeamUnitTangentAngle k (P.nativeSeamUnitChartCenter k b) b.val
    (P.nativeSeamUnitChartCenter_mem_source k b) ⟨v.val.val.snd, v.val.property⟩)

@[simp] theorem nativeSeamNeighborhoodUnitTangentAngle_param
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : ↥(P.gluedMk '' P.seamNeighborhood k) × Circle) :
    P.nativeSeamNeighborhoodUnitTangentAngle k (P.nativeSeamNeighborhoodUnitTangentParam k q) = q := by
  apply Prod.ext
  · rfl
  · exact P.nativeSeamUnitTangentAngle_param k (P.nativeSeamUnitChartCenter k q.1) q.1.val
      (P.nativeSeamUnitChartCenter_mem_source k q.1) q.2

@[simp] theorem nativeSeamNeighborhoodUnitTangentParam_angle
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (v : P.NativeSeamUnitTangentOver k) :
    P.nativeSeamNeighborhoodUnitTangentParam k (P.nativeSeamNeighborhoodUnitTangentAngle k v) = v := by
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun w : P.NativeUnitTangentFiber v.val.val.proj =>
    TotalSpace.mk v.val.val.proj w.val) (P.nativeSeamUnitTangentParam_angle k _ _ _ _)

/-- On a genuine local angular chart the globally defined map is precisely
that chart's actual native orthonormal parametrization. -/
theorem nativeSeamNeighborhoodUnitTangentParam_local
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (q : ↥(P.gluedMk '' P.seamNeighborhood k) × Circle)
    (hq : q.1.val ∈ (P.seamAngularComplexChart k θ).source) :
    (P.nativeSeamNeighborhoodUnitTangentParam k q).val.val =
      TotalSpace.mk q.1.val (P.nativeSeamUnitTangentParam k θ q.1.val hq q.2).val := by
  exact congrArg (fun w : P.NativeUnitTangentFiber q.1.val => TotalSpace.mk q.1.val w.val)
    (P.nativeSeamUnitTangentParam_angularChart_independent k _ θ q.1.val _ hq q.2)

theorem nativeSeamUnitTangentAngle_angularChart_independent
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ ψ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source)
    (hb' : b ∈ (P.seamAngularComplexChart k ψ).source) (v : P.NativeUnitTangentFiber b) :
    P.nativeSeamUnitTangentAngle k θ b hb v = P.nativeSeamUnitTangentAngle k ψ b hb' v := by
  have h := P.nativeSeamUnitTangentParam_angularChart_independent k θ ψ b hb hb'
    (P.nativeSeamUnitTangentAngle k θ b hb v)
  rw [P.nativeSeamUnitTangentParam_angle] at h
  have ha := congrArg (P.nativeSeamUnitTangentAngle k ψ b hb') h
  simpa only [P.nativeSeamUnitTangentAngle_param] using ha.symm

theorem nativeSeamNeighborhoodUnitTangentAngle_local
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (v : P.NativeSeamUnitTangentOver k)
    (hv : v.val.val.proj ∈ (P.seamAngularComplexChart k θ).source) :
    (P.nativeSeamNeighborhoodUnitTangentAngle k v).2 =
      P.nativeSeamUnitTangentAngle k θ v.val.val.proj hv ⟨v.val.val.snd, v.val.property⟩ :=
  P.nativeSeamUnitTangentAngle_angularChart_independent k _ θ _
    (P.nativeSeamUnitChartCenter_mem_source k ⟨v.val.val.proj, v.property⟩) hv _

theorem nativeSeamNeighborhoodUnitTangentParam_continuous
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Continuous (P.nativeSeamNeighborhoodUnitTangentParam k) := by
  rw [continuous_iff_continuousAt]
  intro q₀
  apply ContinuousAt.codRestrict
  apply ContinuousAt.codRestrict
  let θ := P.nativeSeamUnitChartCenter k q₀.1
  let e := P.seamAngularComplexChart k θ
  let t := (tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
    (⟨e, Or.inr ⟨k, θ, rfl⟩⟩ : atlas ℂ P.GluedCarrier)
  have hb₀ : q₀.1.val ∈ e.source := P.nativeSeamUnitChartCenter_mem_source k q₀.1
  have hb : Continuous (fun q : ↥(P.gluedMk '' P.seamNeighborhood k) × Circle => q.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have ha : Continuous (fun q : ↥(P.gluedMk '' P.seamNeighborhood k) × Circle => (q.2 : ℂ)) :=
    continuous_subtype_val.comp continuous_snd
  have he : ContinuousAt (fun q : ↥(P.gluedMk '' P.seamNeighborhood k) × Circle => e q.1.val) q₀ :=
    (e.continuousAt hb₀).comp
      (f := fun q : ↥(P.gluedMk '' P.seamNeighborhood k) × Circle => q.1.val)
      (g := (e : P.GluedCarrier → ℂ)) (x := q₀) hb.continuousAt
  have hw := (gluingCollarWarp_continuous (gluingRadius C g)).continuousAt.comp
    (Complex.continuous_re.continuousAt.comp he)
  have hc : ContinuousAt (fun q : ↥(P.gluedMk '' P.seamNeighborhood k) × Circle =>
      gluingCollarOrthonormalCoord (gluingRadius C g) (e q.1.val) q.2) q₀ :=
    Complex.equivRealProdCLM.symm.continuousAt.comp
      ((Complex.continuous_re.comp ha).continuousAt.prodMk
        ((Complex.continuous_im.comp ha).continuousAt.div hw
          (gluingCollarWarp_pos P.radius_pos _).ne'))
  have hi : ContinuousAt (fun q : ↥(P.gluedMk '' P.seamNeighborhood k) × Circle =>
      t.toOpenPartialHomeomorph.symm (q.1.val,
        gluingCollarOrthonormalCoord (gluingRadius C g) (e q.1.val) q.2)) q₀ :=
    (t.toOpenPartialHomeomorph.symm.continuousAt
    (show (q₀.1.val, gluingCollarOrthonormalCoord (gluingRadius C g) (e q₀.1.val) q₀.2) ∈
      t.target from ⟨hb₀, mem_univ _⟩)).comp
        (f := fun q : ↥(P.gluedMk '' P.seamNeighborhood k) × Circle =>
          (q.1.val, gluingCollarOrthonormalCoord (gluingRadius C g) (e q.1.val) q.2))
        (g := t.toOpenPartialHomeomorph.symm)
        (x := q₀) (hb.continuousAt.prodMk hc)
  apply hi.congr_of_eventuallyEq
  filter_upwards [hb.continuousAt.eventually (e.open_source.mem_nhds hb₀)] with q hq
  exact (P.nativeSeamNeighborhoodUnitTangentParam_local k θ q hq).trans (by
    change TotalSpace.mk q.1.val (t.symmL ℝ q.1.val
      (gluingCollarOrthonormalCoord (gluingRadius C g) (e q.1.val) q.2)) = _
    rw [t.symmL_apply hq, t.mk_symm hq])

theorem nativeSeamNeighborhoodUnitTangentAngle_continuous
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Continuous (P.nativeSeamNeighborhoodUnitTangentAngle k) := by
  apply Continuous.prodMk
  · exact ((FiberBundle.continuous_proj ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)).comp
        (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  rw [continuous_iff_continuousAt]
  intro v₀
  apply ContinuousAt.codRestrict
  let b₀ : ↥(P.gluedMk '' P.seamNeighborhood k) := ⟨v₀.val.val.proj, v₀.property⟩
  let θ := P.nativeSeamUnitChartCenter k b₀
  let e := P.seamAngularComplexChart k θ
  let t := (tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
    (⟨e, Or.inr ⟨k, θ, rfl⟩⟩ : atlas ℂ P.GluedCarrier)
  have hb₀ : v₀.val.val.proj ∈ e.source := P.nativeSeamUnitChartCenter_mem_source k b₀
  have hv : Continuous (fun v : P.NativeSeamUnitTangentOver k => v.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hb := (FiberBundle.continuous_proj ℂ
    (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)).comp hv
  have ht : ContinuousAt (fun v : P.NativeSeamUnitTangentOver k => t v.val.val) v₀ :=
    (t.toOpenPartialHomeomorph.continuousAt (show v₀.val.val ∈ t.source from hb₀)).comp
      (f := fun v : P.NativeSeamUnitTangentOver k => v.val.val)
      (g := (t.toOpenPartialHomeomorph : TotalSpace ℂ
        (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) → P.GluedCarrier × ℂ))
      (x := v₀) hv.continuousAt
  have he : ContinuousAt (fun v : P.NativeSeamUnitTangentOver k => e v.val.val.proj) v₀ :=
    (e.continuousAt hb₀).comp (f := fun v : P.NativeSeamUnitTangentOver k => v.val.val.proj)
      (g := (e : P.GluedCarrier → ℂ)) (x := v₀) hb.continuousAt
  have hw := (gluingCollarWarp_continuous (gluingRadius C g)).continuousAt.comp
    (Complex.continuous_re.continuousAt.comp he)
  have hc : ContinuousAt (fun v : P.NativeSeamUnitTangentOver k =>
      gluingCollarOrthonormalComponents (gluingRadius C g) (e v.val.val.proj) (t v.val.val).2) v₀ :=
    Complex.equivRealProdCLM.symm.continuousAt.comp
      ((Complex.continuous_re.continuousAt.comp ht.snd).prodMk
        (hw.mul (Complex.continuous_im.continuousAt.comp ht.snd)))
  apply hc.congr_of_eventuallyEq
  filter_upwards [hb.continuousAt.eventually (e.open_source.mem_nhds hb₀)] with v hvb
  exact (congrArg (fun a : Circle => (a : ℂ))
    (P.nativeSeamNeighborhoodUnitTangentAngle_local k θ v hvb)).trans (by
      change gluingCollarOrthonormalComponents _ _ (P.nativeUnitTangentCoord e _ _ _) = _
      congr 1
      exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ t hvb v.val.val.snd)

/-- The full seam neighborhood's genuine native unit-bundle homeomorphism. -/
noncomputable def nativeSeamNeighborhoodUnitTangentHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    ↥(P.gluedMk '' P.seamNeighborhood k) × Circle ≃ₜ P.NativeSeamUnitTangentOver k where
  toFun := P.nativeSeamNeighborhoodUnitTangentParam k
  invFun := P.nativeSeamNeighborhoodUnitTangentAngle k
  left_inv := P.nativeSeamNeighborhoodUnitTangentAngle_param k
  right_inv := P.nativeSeamNeighborhoodUnitTangentParam_angle k
  continuous_toFun := P.nativeSeamNeighborhoodUnitTangentParam_continuous k
  continuous_invFun := P.nativeSeamNeighborhoodUnitTangentAngle_continuous k

/-- The actual complete signed seam cylinder trivializes the true native
unit tangent bundle over its image, including signed radius zero. -/
noncomputable def nativeSeamCylinderUnitTangentHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    GluingSeamCylinder C g × Circle ≃ₜ P.NativeSeamUnitTangentOver k :=
  ((P.seamCylinderHomeomorph k).prodCongr (Homeomorph.refl Circle)).trans
    (P.nativeSeamNeighborhoodUnitTangentHomeomorph k)

@[simp] theorem nativeSeamCylinderUnitTangentHomeomorph_proj
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : GluingSeamCylinder C g × Circle) :
    (P.nativeSeamCylinderUnitTangentHomeomorph k q).val.val.proj =
      (P.seamCylinderHomeomorph k q.1).val := rfl

/-- Its expression in every actual angular chart is the literal native
orthonormal parameter, with no orientation or phase change. -/
theorem nativeSeamCylinderUnitTangentHomeomorph_local_apply
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (q : GluingSeamCylinder C g × Circle)
    (hq : (P.seamCylinderHomeomorph k q.1).val ∈ (P.seamAngularComplexChart k θ).source) :
    (P.nativeSeamCylinderUnitTangentHomeomorph k q).val.val =
      TotalSpace.mk (P.seamCylinderHomeomorph k q.1).val
        (P.nativeSeamUnitTangentParam k θ (P.seamCylinderHomeomorph k q.1).val hq q.2).val :=
  P.nativeSeamNeighborhoodUnitTangentParam_local k θ _ hq

@[simp] theorem nativeSeamCylinderUnitTangentHomeomorph_symm_base
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (v : P.NativeSeamUnitTangentOver k) :
    ((P.nativeSeamCylinderUnitTangentHomeomorph k).symm v).1 =
      (P.seamCylinderHomeomorph k).symm ⟨v.val.val.proj, v.property⟩ := rfl

/-- The full-cylinder inverse reads exactly the native orthonormal phase in
every valid actual angular chart. -/
theorem nativeSeamCylinderUnitTangentHomeomorph_symm_local_angle
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (v : P.NativeSeamUnitTangentOver k)
    (hv : v.val.val.proj ∈ (P.seamAngularComplexChart k θ).source) :
    ((P.nativeSeamCylinderUnitTangentHomeomorph k).symm v).2 =
      P.nativeSeamUnitTangentAngle k θ v.val.val.proj hv ⟨v.val.val.snd, v.val.property⟩ :=
  P.nativeSeamNeighborhoodUnitTangentAngle_local k θ v hv

#print axioms nativeSeamNeighborhoodUnitTangentHomeomorph
#print axioms nativeSeamCylinderUnitTangentHomeomorph
#print axioms nativeSeamCylinderUnitTangentHomeomorph_local_apply
#print axioms nativeSeamCylinderUnitTangentHomeomorph_symm_local_angle

end SystolicGrowth.ExerciseGluingPreparation
