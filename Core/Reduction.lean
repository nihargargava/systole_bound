module

public import BuserSarnak.BuserSarnak
public import CookMagyar.All

@[expose] public section

open Filter Set
open scoped BigOperators MatrixGroups Topology UpperHalfPlane

namespace SystolicGrowth

/-! ## Core.Reduction to the two arithmetic inputs

This file separates the proof into three layers:

1. `BuserSarnakInput` supplies the sparse family of arithmetic surfaces.
2. `CookMagyar.lean` derives `UniformCookMagyarInput`, a bounded decomposition
   of every large genus into comparable arithmetic genera, from a
   target-uniform prime-representation input.
3. `GeometricInput` packages the internal geometric construction from the
   draft: join the bounded family along a chain and retain the desired
   systolic lower bound.

The arithmetic and geometric paper inputs are kept as explicit parameters.
All asymptotic bookkeeping in this file is proved from those parameters.

Two repairs to the draft are important for that eventual formalization.
First, the glued compact surface is *locally* CAT(-1) (equivalently, its
universal cover is CAT(-1)); it cannot itself be a nontrivial compact CAT(-1)
space.  Second, the proof should organize a geodesic by genuine transitions
between punctured components, not claim that every contact with a seam is
transverse.  Choosing an extreme component genuinely entered by the curve
produces the required same-seam backtracking arc while allowing harmless seam
tangencies.
-/

/-- The target lower bound in the quantitative form of the main theorem. -/
noncomputable def targetSystole (C : ℝ) (g : ℕ) : ℝ :=
  (4 / 3 : ℝ) * Real.log g - 2 * Real.log (Real.log g) - C

/-- The geometric consequence of the Brooks--Buser--Sarnak construction used
in the draft.

The integer `h` fixes one arithmetic family.  For every prime `p > 3`, the
input gives a concrete closed hyperbolic surface of genus
`h * ((p^3-p)/24) + 1` and systole at least `4 log p`. -/
structure BuserSarnakInput where
  h : ℕ
  h_pos : 0 < h
  surface : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
    ClosedHyperbolicSurface (arithmeticGenus h p)
  systole_lower : ∀ (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3),
    4 * Real.log p ≤ (surface p hp hp2 hp3).systole

/-- The remaining geometric content of the Brooks--Buser--Sarnak construction.

All arithmetic, freeness, and systolic estimates for this deck group are proved
in `BuserSarnak.lean`; this structure asks only for the closed quotient and its
marking, together with identification of its deck group. -/
structure BuserSarnakGeometricConstruction where
  h : ℕ
  h_pos : 0 < h
  surface : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
    ClosedHyperbolicSurface (arithmeticGenus h p)
  deckGroup_eq : ∀ (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3),
    (surface p hp hp2 hp3).deckGroup =
      BuserSarnakQuaternionUnit.levelDeckGroup
        (a := 2) (b := 3) (by norm_num) (by norm_num) (p : ℤ)

/-- The verified arithmetic estimate turns the geometric construction into the
original Buser--Sarnak input package. -/
def BuserSarnakGeometricConstruction.toBuserSarnakInput
    (data : BuserSarnakGeometricConstruction) : BuserSarnakInput where
  h := data.h
  h_pos := data.h_pos
  surface := data.surface
  systole_lower := by
    intro p hp hp2 hp3
    exact BuserSarnakQuaternionUnit.systole_lower23_of_deckGroup_eq_of_genus_pos
      (by simp [arithmeticGenus]) hp hp2 (data.surface p hp hp2 hp3)
      (data.deckGroup_eq p hp hp2 hp3)

/-- The explicit `(2,3)` principal congruence deck group at an odd prime level. -/
noncomputable abbrev buserSarnakLevelGroup23 (p : ℕ) :=
  BuserSarnakQuaternionUnit.levelDeckGroup
    (a := 2) (b := 3) (by norm_num) (by norm_num) (p : ℤ)

/-- The remaining theorem needed for the explicit arithmetic group: its exact
surface-group presentation, including the genus calculation.  Cocompactness is
proved unconditionally in `BuserSarnak.lean`. -/
structure BuserSarnakQuotientConstruction where
  h : ℕ
  h_pos : 0 < h
  marking : ∀ (p : ℕ) (_hp : p.Prime) (_hp2 : p ≠ 2) (_hp3 : p ≠ 3),
    buserSarnakLevelGroup23 p ≃* SurfaceGroup (arithmeticGenus h p)

/-- Constructive cocompactness data: a compact subset of the upper half-plane
that meets every orbit of each explicit level group, together with the marking. -/
structure BuserSarnakFundamentalSetConstruction where
  h : ℕ
  h_pos : 0 < h
  fundamentalSet : ℕ → Set ℍ
  compact : ∀ (p : ℕ) (_hp : p.Prime) (_hp2 : p ≠ 2) (_hp3 : p ≠ 3),
    IsCompact (fundamentalSet p)
  orbit_cover : ∀ (p : ℕ) (_hp : p.Prime) (_hp2 : p ≠ 2) (_hp3 : p ≠ 3) (z : ℍ),
    ∃ gamma : buserSarnakLevelGroup23 p, gamma • z ∈ fundamentalSet p
  marking : ∀ (p : ℕ) (_hp : p.Prime) (_hp2 : p ≠ 2) (_hp3 : p ≠ 3),
    buserSarnakLevelGroup23 p ≃* SurfaceGroup (arithmeticGenus h p)

namespace BuserSarnakFundamentalSetConstruction

/-- A compact orbit-covering set proves cocompactness of the corresponding
level-group quotient. -/
noncomputable def toQuotientConstruction
    (data : BuserSarnakFundamentalSetConstruction) :
    BuserSarnakQuotientConstruction where
  h := data.h
  h_pos := data.h_pos
  marking := data.marking

end BuserSarnakFundamentalSetConstruction

namespace BuserSarnakQuotientConstruction

/-- Assemble the closed hyperbolic surface from the explicit group.  The
discreteness and free-action fields are discharged by `BuserSarnak.lean`. -/
noncomputable def surface (data : BuserSarnakQuotientConstruction)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ClosedHyperbolicSurface (arithmeticGenus data.h p) where
  deckGroup := buserSarnakLevelGroup23 p
  discrete := by
    exact BuserSarnakQuaternionUnit.levelDeckGroup_isDiscrete
      (a := 2) (b := 3) (by norm_num) (by norm_num) (p : ℤ)
  free := BuserSarnakQuaternionUnit.levelDeckGroup_free23 hp hp2
  compactQuotient := by
    let : NeZero p := ⟨hp.ne_zero⟩
    exact BuserSarnakQuaternionUnit.levelDeckGroup23_compactQuotient p
  marking := data.marking p hp hp2 hp3

/-- Forget the now-verified group-theoretic fields, retaining the older
surface-level interface used by the reduction. -/
noncomputable def toGeometricConstruction (data : BuserSarnakQuotientConstruction) :
    BuserSarnakGeometricConstruction where
  h := data.h
  h_pos := data.h_pos
  surface := data.surface
  deckGroup_eq := by
    intro p hp hp2 hp3
    rfl

/-- A compactness-and-marking proof for the explicit level groups supplies
the complete Buser--Sarnak input used by the main reduction. -/
noncomputable def toBuserSarnakInput
    (data : BuserSarnakQuotientConstruction) : BuserSarnakInput :=
  data.toGeometricConstruction.toBuserSarnakInput

end BuserSarnakQuotientConstruction

/-! ### The internal geometric layer -/

/-- A bounded collection of comparable large-systole surfaces can be joined
along a chain without losing more than `2 log log g + O(1)` from the systole.

The intended proof takes
`L = (4/3) log g - 2 log(log g) - C`,
`r = asinh(L / (2π))`, `d = L/2`, and `R = r+d`.  Embedded radius-`R`
disks follow from `R < systole/2`, while the diameter lower bound and the
component-genus comparison provide separated centers in internal components.
After gluing, the seam has length `2π sinh r = L`; a closed component-walk in
the chain has an immediate backtrack, which forces an excursion of length at
least `2d = L`.

The glued metric is **locally** CAT(-1): for the seam warping function
`f(t) = sinh (r + |t|)`, one has `f'' ≥ f` distributionally, including the
positive atom at `t = 0`.  Hyperbolic replacement then preserves the systolic
lower bound.

The second field needs only a uniform logarithmic upper bound for the
systole of a genus-`g` closed hyperbolic surface. This guarantees that
`Sys(g)` is taken over a bounded set and that its normalization is eventually
bounded; the sharp numerical constant in the classical disk-area bound is
not used by the liminf argument. -/
structure GeometricInput where
  connect_surfaces_along_chain :
    ∀ (N : ℕ) (a : ℝ), 0 < a → (K : ℝ) →
      ∃ C > 0, ∀ᶠ g : ℕ in atTop,
        ∀ (n : ℕ), 0 < n → n ≤ N →
        ∀ (genera : Fin n → ℕ)
          (X : ∀ i, ClosedHyperbolicSurface (genera i)),
          (∑ i, genera i) = g →
          (∀ i, a * (g : ℝ) ≤ (genera i : ℝ)) →
          (∀ i, (4 / 3 : ℝ) * Real.log g - K ≤ (X i).systole) →
          ∃ Y : ClosedHyperbolicSurface g, targetSystole C g ≤ Y.systole
  systole_upper_bound :
    ∃ K : ℝ, ∀ {g : ℕ}, 2 ≤ g → (X : ClosedHyperbolicSurface g) →
      X.systole ≤ K * Real.log (g : ℝ)

/-- Consequently, the real-valued systole spectrum is bounded above in every
genus at least two.  This is needed because `sSup` on `ℝ` is conditionally,
not completely, order-theoretic. -/
theorem systoleSpectrum_bddAbove (geo : GeometricInput) {g : ℕ} (hg : 2 ≤ g) :
    BddAbove (systoleSpectrum g) := by
  obtain ⟨K, hK⟩ := geo.systole_upper_bound
  refine ⟨K * Real.log (g : ℝ), ?_⟩
  rintro y ⟨Y, rfl⟩
  exact hK hg Y

/-- Every realized systole is bounded by the supremal systole `Sys(g)`. -/
theorem systole_le_Sys (geo : GeometricInput) {g : ℕ} (hg : 2 ≤ g)
    (X : ClosedHyperbolicSurface g) : X.systole ≤ Sys g :=
  le_csSup (systoleSpectrum_bddAbove geo hg) ⟨X, rfl⟩

/-! ### Assembly of the two inputs -/

/-- Buser--Sarnak plus Cook--Magyar give the quantitative surface-existence
statement appearing in Theorem 1.1 of the draft. -/
theorem quantitative_surface_bound_of_inputs
    (geo : GeometricInput) (bs : BuserSarnakInput)
    (cm : UniformCookMagyarInput bs.h) :
    ∃ C > 0, ∀ᶠ g : ℕ in atTop,
      ∃ X : ClosedHyperbolicSurface g, targetSystole C g ≤ X.systole := by
  obtain ⟨C, hC, hconnect⟩ :=
    geo.connect_surfaces_along_chain cm.maxSummands cm.componentFraction
      cm.componentFraction_pos (4 * cm.logLoss)
  obtain ⟨g₃ : ℕ, hg₃ :
      (arithmeticGenus bs.h 3 : ℝ) / cm.componentFraction < g₃⟩ :=
    exists_nat_gt ((arithmeticGenus bs.h 3 : ℝ) / cm.componentFraction)
  refine ⟨C, hC, ?_⟩
  filter_upwards [cm.decomposition, hconnect, eventually_ge_atTop g₃]
    with g hdecomp hconnect_g hg₃g
  rcases hdecomp with
    ⟨n, hn_pos, hn_le, primes, hprime, hodd, hgenus, hlog, hlarge⟩
  have hthree : ∀ i, primes i ≠ 3 := by
    intro i hp3
    have hcomponent := hlarge i
    rw [hp3] at hcomponent
    have hg₃g_real : (g₃ : ℝ) ≤ g := by exact_mod_cast hg₃g
    have hstrict : (arithmeticGenus bs.h 3 : ℝ) <
        cm.componentFraction * (g : ℝ) := by
      calc
        (arithmeticGenus bs.h 3 : ℝ) =
            cm.componentFraction *
              ((arithmeticGenus bs.h 3 : ℝ) / cm.componentFraction) := by
                field_simp [cm.componentFraction_pos.ne']
        _ < cm.componentFraction * (g₃ : ℝ) :=
          mul_lt_mul_of_pos_left hg₃ cm.componentFraction_pos
        _ ≤ cm.componentFraction * (g : ℝ) :=
          mul_le_mul_of_nonneg_left hg₃g_real cm.componentFraction_pos.le
    exact (not_lt_of_ge hcomponent) hstrict
  let genera : Fin n → ℕ := fun i ↦ arithmeticGenus bs.h (primes i)
  let X : ∀ i, ClosedHyperbolicSurface (genera i) := fun i ↦
    bs.surface (primes i) (hprime i) (hodd i) (hthree i)
  have hsys : ∀ i,
      (4 / 3 : ℝ) * Real.log g - 4 * cm.logLoss ≤ (X i).systole := by
    intro i
    calc
      (4 / 3 : ℝ) * Real.log g - 4 * cm.logLoss =
          4 * ((1 / 3 : ℝ) * Real.log g - cm.logLoss) := by ring
      _ ≤ 4 * Real.log (primes i) := by gcongr; exact hlog i
      _ ≤ (X i).systole := by
        simpa [X] using
          bs.systole_lower (primes i) (hprime i) (hodd i) (hthree i)
  exact hconnect_g n hn_pos hn_le genera X
    (by simpa [genera] using hgenus)
    (by intro i; simpa [genera] using hlarge i)
    hsys

/-- The quantitative surface bound implies the corresponding bound for
`Sys(g)`. -/
theorem quantitative_Sys_bound_of_inputs
    (geo : GeometricInput) (bs : BuserSarnakInput)
    (cm : UniformCookMagyarInput bs.h) :
    ∃ C > 0, ∀ᶠ g : ℕ in atTop, targetSystole C g ≤ Sys g := by
  obtain ⟨C, hC, hsurfaces⟩ := quantitative_surface_bound_of_inputs geo bs cm
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsurfaces, eventually_ge_atTop 2] with g hsurface hg
  obtain ⟨X, hX⟩ := hsurface
  exact hX.trans (systole_le_Sys geo hg X)

/-- The normalized quantitative bound is eventually larger than
`4/3 - ε` for every `ε > 0`. -/
theorem normalized_lower_bound_of_inputs
    (geo : GeometricInput) (bs : BuserSarnakInput)
    (cm : UniformCookMagyarInput bs.h)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ g : ℕ in atTop, (4 / 3 : ℝ) - ε ≤ Sys g / Real.log g := by
  obtain ⟨C, -, hquantitative⟩ := quantitative_Sys_bound_of_inputs geo bs cm
  have hlog : Tendsto (fun g : ℕ ↦ Real.log g) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog_div :
      Tendsto (fun g : ℕ ↦ Real.log (Real.log g) / Real.log g) atTop (𝓝 0) := by
    have h :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hlog
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using h
  have hC_div : Tendsto (fun g : ℕ ↦ C / Real.log g) atTop (𝓝 0) :=
    hlog.const_div_atTop C
  have hratio : Tendsto
      (fun g : ℕ ↦ targetSystole C g / Real.log g)
      atTop (𝓝 (4 / 3 : ℝ)) := by
    have hdecomposed : Tendsto
        (fun g : ℕ ↦
          (4 / 3 : ℝ) - 2 * (Real.log (Real.log g) / Real.log g) -
            C / Real.log g)
        atTop (𝓝 (4 / 3 : ℝ)) := by
      simpa using
        (tendsto_const_nhds.sub (hloglog_div.const_mul 2)).sub hC_div
    apply hdecomposed.congr'
    filter_upwards [hlog.eventually_gt_atTop 0] with g hg
    dsimp [targetSystole]
    field_simp
  have htarget :
      ∀ᶠ g : ℕ in atTop,
        (4 / 3 : ℝ) - ε < targetSystole C g / Real.log g :=
    hratio.eventually (Ioi_mem_nhds (sub_lt_self _ hε))
  filter_upwards [htarget, hquantitative, hlog.eventually_gt_atTop 0] with
    g htarget_g hquantitative_g hlog_g
  exact htarget_g.le.trans
    ((div_le_div_iff_of_pos_right hlog_g).2 hquantitative_g)

/-- The draft's main liminf theorem, reduced to the Buser--Sarnak and
Cook--Magyar inputs. -/
theorem main_theorem_of_inputs
    (geo : GeometricInput) (bs : BuserSarnakInput)
    (cm : UniformCookMagyarInput bs.h) :
    (4 / 3 : ℝ) ≤ liminf (fun g : ℕ ↦ Sys g / Real.log g) atTop := by
  let normalizedSys : ℕ → ℝ := fun g ↦ Sys g / Real.log g
  have hlower : ∀ᶠ g : ℕ in atTop, (4 / 3 : ℝ) - 1 ≤ normalizedSys g :=
    normalized_lower_bound_of_inputs geo bs cm one_pos
  have hboundedBelow :
      IsBoundedUnder (· ≥ ·) atTop normalizedSys :=
    isBoundedUnder_of_eventually_ge hlower
  obtain ⟨C, -, hsurfaces⟩ := quantitative_surface_bound_of_inputs geo bs cm
  obtain ⟨K, hK⟩ := geo.systole_upper_bound
  have hboundedAboveEventually : ∀ᶠ g : ℕ in atTop, normalizedSys g ≤ K := by
    filter_upwards [hsurfaces, eventually_ge_atTop 4] with g hsurface hg
    obtain ⟨X, -⟩ := hsurface
    have hg_real : (4 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    have hSys : Sys g ≤ K * Real.log (g : ℝ) := by
      apply csSup_le
      · exact ⟨X.systole, X, rfl⟩
      · rintro y ⟨Y, rfl⟩
        exact hK (by omega) Y
    have hlog_pos : 0 < Real.log (g : ℝ) := Real.log_pos (by nlinarith)
    dsimp [normalizedSys]
    exact (div_le_iff₀ hlog_pos).2 hSys
  have hcoboundedAbove :
      IsCoboundedUnder (· ≥ ·) atTop normalizedSys :=
    isCoboundedUnder_ge_of_eventually_le atTop hboundedAboveEventually
  rw [le_liminf_iff' hcoboundedAbove hboundedBelow]
  intro y hy
  have hε : 0 < (4 / 3 : ℝ) - y := sub_pos.mpr hy
  have h := normalized_lower_bound_of_inputs geo bs cm hε
  simpa [normalizedSys] using h

/-- The main theorem reduced to the geometric, Buser--Sarnak, and
target-uniform Cook--Magyar inputs. -/
theorem main_theorem_reduced_to_inputs
    (geo : GeometricInput) (bs : BuserSarnakInput)
    (cm : TargetUniformCookMagyarInput) :
    (4 / 3 : ℝ) ≤ liminf (fun g : ℕ ↦ Sys g / Real.log g) atTop :=
  main_theorem_of_inputs geo bs (uniformCookMagyar cm bs.h bs.h_pos)

end SystolicGrowth
