module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceBoundaryGraphPaths
public import Geometry.SurfaceBoundaryGraphOpenCover
public import Mathlib.Topology.Subpath

@[expose] public section

/-!
# Literal star–midsection–star subdivision of physical sides

The cuts at 3/10 and 7/10 lie in both neighboring members of the actual
disconnected open cover. All paths below are subpaths of the original physical
side, and their concatenation retains its original vertex endpoints.
-/

open Set UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

/-- The first cut lies strictly between 1/4 and 1/3. -/
def intrinsicBoundaryGraphSideInitialCut : unitInterval := ⟨3 / 10, by norm_num⟩

/-- The second cut lies strictly between 2/3 and 3/4. -/
def intrinsicBoundaryGraphSideTerminalCut : unitInterval := ⟨7 / 10, by norm_num⟩

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- The whole first closed subpath lies in its actual start-vertex star. -/
theorem intrinsicBoundaryGraphSideInitialSubpath_mem_start_star
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (t : unitInterval) :
    (B.intrinsicBoundaryGraphSidePath i).subpath 0 intrinsicBoundaryGraphSideInitialCut t ∈
      B.intrinsicBoundaryGraphVertexStar (B.intrinsicBoundaryGraphSideStart i) := by
  change Quotient.mk B.intrinsicBoundaryIntervalSetoid
    (i, Icc.convexComb 0 intrinsicBoundaryGraphSideInitialCut t) ∈ _
  apply (B.intrinsicBoundaryGraphVertexStar_mem_mk _ _).2
  refine Or.inl ⟨?_, rfl⟩
  change (1 - (t : ℝ)) * 0 + (t : ℝ) * (3 / 10) < 1 / 3
  nlinarith [t.2.2]

/-- The whole middle closed subpath lies in its actual physical-edge midsection. -/
theorem intrinsicBoundaryGraphSideMiddleSubpath_mem_midsection
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (t : unitInterval) :
    (B.intrinsicBoundaryGraphSidePath i).subpath
        intrinsicBoundaryGraphSideInitialCut intrinsicBoundaryGraphSideTerminalCut t ∈
      B.intrinsicBoundaryGraphEdgeMidsection i := by
  change Quotient.mk B.intrinsicBoundaryIntervalSetoid
    (i, Icc.convexComb intrinsicBoundaryGraphSideInitialCut
      intrinsicBoundaryGraphSideTerminalCut t) ∈ _
  apply (B.intrinsicBoundaryGraphEdgeMidsection_mem_mk i _).2
  refine ⟨Or.inl rfl, ?_, ?_⟩
  · change (1 / 4 : ℝ) < (1 - (t : ℝ)) * (3 / 10) + (t : ℝ) * (7 / 10)
    nlinarith [t.2.1]
  · change (1 - (t : ℝ)) * (3 / 10) + (t : ℝ) * (7 / 10) < 3 / 4
    nlinarith [t.2.2]

/-- The whole last closed subpath lies in its actual end-vertex star. -/
theorem intrinsicBoundaryGraphSideTerminalSubpath_mem_end_star
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (t : unitInterval) :
    (B.intrinsicBoundaryGraphSidePath i).subpath intrinsicBoundaryGraphSideTerminalCut 1 t ∈
      B.intrinsicBoundaryGraphVertexStar (B.intrinsicBoundaryGraphSideEnd i) := by
  change Quotient.mk B.intrinsicBoundaryIntervalSetoid
    (i, Icc.convexComb intrinsicBoundaryGraphSideTerminalCut 1 t) ∈ _
  apply (B.intrinsicBoundaryGraphVertexStar_mem_mk _ _).2
  refine Or.inr ⟨?_, rfl⟩
  change (2 / 3 : ℝ) < (1 - (t : ℝ)) * (7 / 10) + (t : ℝ) * 1
  nlinarith [t.2.1]

theorem intrinsicBoundaryGraphSideInitialSubpath_mem_starUnion
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (t : unitInterval) :
    (B.intrinsicBoundaryGraphSidePath i).subpath 0 intrinsicBoundaryGraphSideInitialCut t ∈
      B.intrinsicBoundaryGraphStarUnion :=
  mem_iUnion.mpr ⟨_, B.intrinsicBoundaryGraphSideInitialSubpath_mem_start_star i t⟩

theorem intrinsicBoundaryGraphSideMiddleSubpath_mem_midsectionUnion
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (t : unitInterval) :
    (B.intrinsicBoundaryGraphSidePath i).subpath
        intrinsicBoundaryGraphSideInitialCut intrinsicBoundaryGraphSideTerminalCut t ∈
      B.intrinsicBoundaryGraphMidsectionUnion :=
  mem_iUnion.mpr ⟨_, B.intrinsicBoundaryGraphSideMiddleSubpath_mem_midsection i t⟩

theorem intrinsicBoundaryGraphSideTerminalSubpath_mem_starUnion
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (t : unitInterval) :
    (B.intrinsicBoundaryGraphSidePath i).subpath intrinsicBoundaryGraphSideTerminalCut 1 t ∈
      B.intrinsicBoundaryGraphStarUnion :=
  mem_iUnion.mpr ⟨_, B.intrinsicBoundaryGraphSideTerminalSubpath_mem_end_star i t⟩

/-- The literal first side subpath as a genuine path in the union of vertex stars. -/
def intrinsicBoundaryGraphSideInitialStarPath
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Path
      (⟨B.intrinsicBoundaryGraphSidePath i 0, by
        simpa only [Path.source] using
          B.intrinsicBoundaryGraphSideInitialSubpath_mem_starUnion i 0⟩ :
        B.intrinsicBoundaryGraphStarUnion)
      ⟨B.intrinsicBoundaryGraphSidePath i intrinsicBoundaryGraphSideInitialCut, by
        simpa only [Path.target] using
          B.intrinsicBoundaryGraphSideInitialSubpath_mem_starUnion i 1⟩ where
  toFun t := ⟨(B.intrinsicBoundaryGraphSidePath i).subpath
    0 intrinsicBoundaryGraphSideInitialCut t,
    B.intrinsicBoundaryGraphSideInitialSubpath_mem_starUnion i t⟩
  continuous_toFun := ((B.intrinsicBoundaryGraphSidePath i).subpath
    0 intrinsicBoundaryGraphSideInitialCut).continuous.subtype_mk _
  source' := Subtype.ext (Path.source _)
  target' := Subtype.ext (Path.target _)

/-- The literal middle subpath as a genuine path in the union of physical midsections. -/
def intrinsicBoundaryGraphSideMiddleMidsectionPath
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Path
      (⟨B.intrinsicBoundaryGraphSidePath i intrinsicBoundaryGraphSideInitialCut, by
        simpa only [Path.source] using
          B.intrinsicBoundaryGraphSideMiddleSubpath_mem_midsectionUnion i 0⟩ :
        B.intrinsicBoundaryGraphMidsectionUnion)
      ⟨B.intrinsicBoundaryGraphSidePath i intrinsicBoundaryGraphSideTerminalCut, by
        simpa only [Path.target] using
          B.intrinsicBoundaryGraphSideMiddleSubpath_mem_midsectionUnion i 1⟩ where
  toFun t := ⟨(B.intrinsicBoundaryGraphSidePath i).subpath
    intrinsicBoundaryGraphSideInitialCut intrinsicBoundaryGraphSideTerminalCut t,
    B.intrinsicBoundaryGraphSideMiddleSubpath_mem_midsectionUnion i t⟩
  continuous_toFun := ((B.intrinsicBoundaryGraphSidePath i).subpath
    intrinsicBoundaryGraphSideInitialCut intrinsicBoundaryGraphSideTerminalCut).continuous.subtype_mk _
  source' := Subtype.ext (Path.source _)
  target' := Subtype.ext (Path.target _)

/-- The literal last side subpath as a genuine path in the union of vertex stars. -/
def intrinsicBoundaryGraphSideTerminalStarPath
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Path
      (⟨B.intrinsicBoundaryGraphSidePath i intrinsicBoundaryGraphSideTerminalCut, by
        simpa only [Path.source] using
          B.intrinsicBoundaryGraphSideTerminalSubpath_mem_starUnion i 0⟩ :
        B.intrinsicBoundaryGraphStarUnion)
      ⟨B.intrinsicBoundaryGraphSidePath i 1, by
        simpa only [Path.target] using
          B.intrinsicBoundaryGraphSideTerminalSubpath_mem_starUnion i 1⟩ where
  toFun t := ⟨(B.intrinsicBoundaryGraphSidePath i).subpath
    intrinsicBoundaryGraphSideTerminalCut 1 t,
    B.intrinsicBoundaryGraphSideTerminalSubpath_mem_starUnion i t⟩
  continuous_toFun := ((B.intrinsicBoundaryGraphSidePath i).subpath
    intrinsicBoundaryGraphSideTerminalCut 1).continuous.subtype_mk _
  source' := Subtype.ext (Path.source _)
  target' := Subtype.ext (Path.target _)

/-- Inclusion recovers the original initial subpath exactly. -/
@[simp]
theorem intrinsicBoundaryGraphSideInitialStarPath_map
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (B.intrinsicBoundaryGraphSideInitialStarPath i).map continuous_subtype_val =
      (B.intrinsicBoundaryGraphSidePath i).subpath 0 intrinsicBoundaryGraphSideInitialCut := by
  ext t
  rfl

/-- Inclusion recovers the original middle subpath exactly. -/
@[simp]
theorem intrinsicBoundaryGraphSideMiddleMidsectionPath_map
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (B.intrinsicBoundaryGraphSideMiddleMidsectionPath i).map continuous_subtype_val =
      (B.intrinsicBoundaryGraphSidePath i).subpath
        intrinsicBoundaryGraphSideInitialCut intrinsicBoundaryGraphSideTerminalCut := by
  ext t
  rfl

/-- Inclusion recovers the original terminal subpath exactly. -/
@[simp]
theorem intrinsicBoundaryGraphSideTerminalStarPath_map
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (B.intrinsicBoundaryGraphSideTerminalStarPath i).map continuous_subtype_val =
      (B.intrinsicBoundaryGraphSidePath i).subpath intrinsicBoundaryGraphSideTerminalCut 1 := by
  ext t
  rfl

/-- The actual concatenation of the three included subtype paths, with the original
physical side's true vertex endpoints. -/
def intrinsicBoundaryGraphSideSubdivision
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Path (B.intrinsicBoundaryGraphVertexInclusion (B.intrinsicBoundaryGraphSideStart i))
      (B.intrinsicBoundaryGraphVertexInclusion (B.intrinsicBoundaryGraphSideEnd i)) :=
  (((B.intrinsicBoundaryGraphSideInitialStarPath i).map continuous_subtype_val).trans
    ((B.intrinsicBoundaryGraphSideMiddleMidsectionPath i).map continuous_subtype_val)).trans
      ((B.intrinsicBoundaryGraphSideTerminalStarPath i).map continuous_subtype_val) |>.cast
        (B.intrinsicBoundaryGraphSidePath i).source.symm
        (B.intrinsicBoundaryGraphSidePath i).target.symm

/-- Actual concatenation of the three cover paths is homotopic to the unchanged side. -/
theorem intrinsicBoundaryGraphSideSubdivision_homotopic
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (B.intrinsicBoundaryGraphSideSubdivision i).Homotopic (B.intrinsicBoundaryGraphSidePath i) := by
  unfold intrinsicBoundaryGraphSideSubdivision
  rw [intrinsicBoundaryGraphSideInitialStarPath_map,
    intrinsicBoundaryGraphSideMiddleMidsectionPath_map,
    intrinsicBoundaryGraphSideTerminalStarPath_map]
  let γ := B.intrinsicBoundaryGraphSidePath i
  have hfirst : ((γ.subpath 0 intrinsicBoundaryGraphSideInitialCut).trans
      (γ.subpath intrinsicBoundaryGraphSideInitialCut intrinsicBoundaryGraphSideTerminalCut)).Homotopic
        (γ.subpath 0 intrinsicBoundaryGraphSideTerminalCut) :=
    ⟨Path.Homotopy.subpathTransSubpath γ 0 intrinsicBoundaryGraphSideInitialCut
      intrinsicBoundaryGraphSideTerminalCut⟩
  have hfull := (hfirst.hcomp
    (Path.Homotopic.refl (γ.subpath intrinsicBoundaryGraphSideTerminalCut 1))).trans
      ⟨Path.Homotopy.subpathTransSubpath γ 0 intrinsicBoundaryGraphSideTerminalCut 1⟩
  have hcast := hfull.pathCast γ.source.symm γ.target.symm
  have hlast : (γ.subpath 0 1).cast γ.source.symm γ.target.symm = γ := by
    apply Path.ext
    funext t
    simp only [Path.cast_coe, Path.subpath_zero_one]
  rw [hlast] at hcast
  exact hcast

#print axioms intrinsicBoundaryGraphSideInitialSubpath_mem_start_star
#print axioms intrinsicBoundaryGraphSideMiddleSubpath_mem_midsection
#print axioms intrinsicBoundaryGraphSideTerminalSubpath_mem_end_star
#print axioms intrinsicBoundaryGraphSideInitialStarPath
#print axioms intrinsicBoundaryGraphSideMiddleMidsectionPath
#print axioms intrinsicBoundaryGraphSideTerminalStarPath
#print axioms intrinsicBoundaryGraphSideSubdivision_homotopic

end

end SystolicGrowth.DirichletBoundarySegments
