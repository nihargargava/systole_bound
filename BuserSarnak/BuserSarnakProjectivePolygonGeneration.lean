module

public import BuserSarnak.BuserSarnakProjectivePolygonPairing

@[expose] public section

/-!
# Generation by projective polygon side pairings

The six distinct side-pairing translations of the projective octagon already
generate its orbifold group.  This elementary algebraic fact is the group-side
input for proving that the finite polygon dual graph is connected; it avoids
assuming a spanning tree as extra target-presentation data.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

/-- The six distinct translations represented by the directed side pairings.
The remaining two directed sides are their opposite orientations. -/
inductive ProjectivePolygonPairingGenerator where
  | a | e1 | cInv | e2 | e3 | e4
  deriving DecidableEq

instance : Fintype ProjectivePolygonPairingGenerator :=
  Fintype.ofList [.a, .e1, .cInv, .e2, .e3, .e4] (by
    intro x
    cases x <;> simp)

/-- The directed polygon side representing each distinct side-pairing
translation. -/
def ProjectivePolygonPairingGenerator.side :
    ProjectivePolygonPairingGenerator → ProjectivePolygonSide
  | .a => .a
  | .e1 => .e1
  | .cInv => .cInv
  | .e2 => .e2
  | .e3 => .e3
  | .e4 => .e4

/-- The side-pairing translations, written in an arbitrary group satisfying
the projective octagon relations. -/
def projectivePolygonPairingGeneratorElement
    {G : Type*} [Group G] (a c e1 e2 e3 e4 : G) :
    ProjectivePolygonPairingGenerator → G
  | .a => a * e2 * c * e1 * a⁻¹
  | .e1 => a * e1 * a⁻¹
  | .cInv => a * e1 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹
  | .e2 => a * e1 * c⁻¹ * e2 * c * e1 * a⁻¹
  | .e3 => a * e1 * c⁻¹ * e2 * a⁻¹ * e3 * a * e2 * c * e1 * a⁻¹
  | .e4 =>
      a * e1 * c⁻¹ * e2 * a⁻¹ * e3 * c * e4 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹

private theorem polygon_relation_inverse
    {G : Type*} [Group G] (a c e1 e2 e3 e4 : G)
    (h1 : e1 * e1 = 1) (h2 : e2 * e2 = 1)
    (h3 : e3 * e3 = 1) (h4 : e4 * e4 = 1)
    (hp : a * e1 * c⁻¹ * e2 * a⁻¹ * e3 * c * e4 = 1) :
    e4 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹ = 1 := by
  have hinv1 : e1⁻¹ = e1 := by
    calc
      e1⁻¹ = e1⁻¹ * 1 := by simp
      _ = e1⁻¹ * (e1 * e1) := by rw [h1]
      _ = e1 := by group
  have hinv2 : e2⁻¹ = e2 := by
    calc
      e2⁻¹ = e2⁻¹ * 1 := by simp
      _ = e2⁻¹ * (e2 * e2) := by rw [h2]
      _ = e2 := by group
  have hinv3 : e3⁻¹ = e3 := by
    calc
      e3⁻¹ = e3⁻¹ * 1 := by simp
      _ = e3⁻¹ * (e3 * e3) := by rw [h3]
      _ = e3 := by group
  have hinv4 : e4⁻¹ = e4 := by
    calc
      e4⁻¹ = e4⁻¹ * 1 := by simp
      _ = e4⁻¹ * (e4 * e4) := by rw [h4]
      _ = e4 := by group
  calc
    e4 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹ =
        e4⁻¹ * c⁻¹ * e3⁻¹ * a * e2⁻¹ * c * e1⁻¹ * a⁻¹ := by
          rw [hinv1, hinv2, hinv3, hinv4]
    _ = (a * e1 * c⁻¹ * e2 * a⁻¹ * e3 * c * e4)⁻¹ := by group
    _ = 1 := by rw [hp]; simp

/-- Recover `a` from three side-pairing translations. -/
theorem a_eq_projectivePolygonPairingGeneratorElements
    {G : Type*} [Group G] (a c e1 e2 e3 e4 : G)
    (h1 : e1 * e1 = 1) (h2 : e2 * e2 = 1)
    (h3 : e3 * e3 = 1) (h4 : e4 * e4 = 1)
    (hp : a * e1 * c⁻¹ * e2 * a⁻¹ * e3 * c * e4 = 1) :
    a =
      projectivePolygonPairingGeneratorElement a c e1 e2 e3 e4 .e1 *
        projectivePolygonPairingGeneratorElement a c e1 e2 e3 e4 .cInv *
          projectivePolygonPairingGeneratorElement a c e1 e2 e3 e4 .e4 := by
  have hpinv := polygon_relation_inverse a c e1 e2 e3 e4 h1 h2 h3 h4 hp
  symm
  change
    (a * e1 * a⁻¹) *
        (a * e1 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹) *
        (a * e1 * c⁻¹ * e2 * a⁻¹ * e3 * c * e4 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹) = a
  calc
    (a * e1 * a⁻¹) *
        (a * e1 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹) *
        (a * e1 * c⁻¹ * e2 * a⁻¹ * e3 * c * e4 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹) =
      a * (e1 * e1) * c⁻¹ * e3 * a * e2 * c * (e1 * e1) * c⁻¹ * e2 * a⁻¹ *
          e3 * c * e4 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹ := by group
    _ = a * c⁻¹ * e3 * a * (e2 * e2) * a⁻¹ * e3 * c * e4 * c⁻¹ * e3 * a *
          e2 * c * e1 * a⁻¹ := by rw [h1]; group
    _ = a * c⁻¹ * (e3 * e3) * c * e4 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹ := by
      rw [h2]
      group
    _ = a * (e4 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹) := by rw [h3]; group
    _ = a := by rw [hpinv, mul_one]

/-- Recover `c` from three side-pairing translations. -/
theorem c_eq_projectivePolygonPairingGeneratorElements
    {G : Type*} [Group G] (a c e1 e2 e3 e4 : G)
    (h1 : e1 * e1 = 1) (h2 : e2 * e2 = 1)
    (h3 : e3 * e3 = 1) (h4 : e4 * e4 = 1)
    (hp : a * e1 * c⁻¹ * e2 * a⁻¹ * e3 * c * e4 = 1) :
    c =
      projectivePolygonPairingGeneratorElement a c e1 e2 e3 e4 .a *
        projectivePolygonPairingGeneratorElement a c e1 e2 e3 e4 .e3 *
          projectivePolygonPairingGeneratorElement a c e1 e2 e3 e4 .e4 := by
  have hpinv := polygon_relation_inverse a c e1 e2 e3 e4 h1 h2 h3 h4 hp
  symm
  change
    (a * e2 * c * e1 * a⁻¹) *
        (a * e1 * c⁻¹ * e2 * a⁻¹ * e3 * a * e2 * c * e1 * a⁻¹) *
        (a * e1 * c⁻¹ * e2 * a⁻¹ * e3 * c * e4 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹) = c
  calc
    (a * e2 * c * e1 * a⁻¹) *
        (a * e1 * c⁻¹ * e2 * a⁻¹ * e3 * a * e2 * c * e1 * a⁻¹) *
        (a * e1 * c⁻¹ * e2 * a⁻¹ * e3 * c * e4 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹) =
      a * e2 * c * (e1 * e1) * c⁻¹ * e2 * a⁻¹ * e3 * a * e2 * c * (e1 * e1) *
          c⁻¹ * e2 * a⁻¹ * e3 * c * e4 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹ := by
      group
    _ = a * (e2 * e2) * a⁻¹ * e3 * a * (e2 * e2) * a⁻¹ * e3 * c * e4 * c⁻¹ *
          e3 * a * e2 * c * e1 * a⁻¹ := by rw [h1]; group
    _ = (e3 * e3) * c * e4 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹ := by rw [h2]; group
    _ = c * (e4 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹) := by rw [h3]; group
    _ = c := by rw [hpinv, mul_one]

/-- The `e₄` side-pairing translation is exactly `e₄`. -/
theorem e4_eq_projectivePolygonPairingGeneratorElement
    {G : Type*} [Group G] (a c e1 e2 e3 e4 : G)
    (h1 : e1 * e1 = 1) (h2 : e2 * e2 = 1) (h3 : e3 * e3 = 1)
    (hp : a * e1 * c⁻¹ * e2 * a⁻¹ * e3 * c * e4 = 1) :
    e4 = projectivePolygonPairingGeneratorElement a c e1 e2 e3 e4 .e4 := by
  let pref := a * e1 * c⁻¹ * e2 * a⁻¹ * e3 * c
  have hinv3 : e3⁻¹ = e3 := by
    calc
      e3⁻¹ = e3⁻¹ * 1 := by simp
      _ = e3⁻¹ * (e3 * e3) := by rw [h3]
      _ = e3 := by group
  have hinv2 : e2⁻¹ = e2 := by
    calc
      e2⁻¹ = e2⁻¹ * 1 := by simp
      _ = e2⁻¹ * (e2 * e2) := by rw [h2]
      _ = e2 := by group
  have hinv1 : e1⁻¹ = e1 := by
    calc
      e1⁻¹ = e1⁻¹ * 1 := by simp
      _ = e1⁻¹ * (e1 * e1) := by rw [h1]
      _ = e1 := by group
  have hpref : pref = e4⁻¹ := by
    calc
      pref = (pref * e4) * e4⁻¹ := by group
      _ = e4⁻¹ := by rw [show pref * e4 = 1 by simpa [pref] using hp]; simp
  have hprefinv : pref⁻¹ = c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹ := by
    calc
      pref⁻¹ = c⁻¹ * e3⁻¹ * a * e2⁻¹ * c * e1⁻¹ * a⁻¹ := by
        dsimp [pref]
        group
      _ = c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹ := by rw [hinv1, hinv2, hinv3]
  symm
  change
    a * e1 * c⁻¹ * e2 * a⁻¹ * e3 * c * e4 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹ = e4
  calc
    a * e1 * c⁻¹ * e2 * a⁻¹ * e3 * c * e4 * c⁻¹ * e3 * a * e2 * c * e1 * a⁻¹ =
        pref * e4 * pref⁻¹ := by
          rw [hprefinv]
          dsimp [pref]
          group
    _ = e4 := by rw [hpref]; group

/-- Any group satisfying the projective octagon relation is generated by its
six indicated side-pairing translations. -/
theorem projectivePolygonPairingGeneratorElements_contain_generators
    {G : Type*} [Group G] (a c e1 e2 e3 e4 : G)
    (h1 : e1 * e1 = 1) (h2 : e2 * e2 = 1)
    (h3 : e3 * e3 = 1) (h4 : e4 * e4 = 1)
    (hp : a * e1 * c⁻¹ * e2 * a⁻¹ * e3 * c * e4 = 1) :
    let H := Subgroup.closure (Set.range
      (projectivePolygonPairingGeneratorElement a c e1 e2 e3 e4))
    a ∈ H ∧ c ∈ H ∧ e1 ∈ H ∧ e2 ∈ H ∧ e3 ∈ H ∧ e4 ∈ H := by
  dsimp only
  let H := Subgroup.closure (Set.range
    (projectivePolygonPairingGeneratorElement a c e1 e2 e3 e4))
  have hu (i : ProjectivePolygonPairingGenerator) :
      projectivePolygonPairingGeneratorElement a c e1 e2 e3 e4 i ∈ H :=
    Subgroup.subset_closure ⟨i, rfl⟩
  have ha : a ∈ H := by
    rw [a_eq_projectivePolygonPairingGeneratorElements a c e1 e2 e3 e4 h1 h2 h3 h4 hp]
    exact H.mul_mem (H.mul_mem (hu .e1) (hu .cInv)) (hu .e4)
  have hc : c ∈ H := by
    rw [c_eq_projectivePolygonPairingGeneratorElements a c e1 e2 e3 e4 h1 h2 h3 h4 hp]
    exact H.mul_mem (H.mul_mem (hu .a) (hu .e3)) (hu .e4)
  have he4 : e4 ∈ H := by
    rw [e4_eq_projectivePolygonPairingGeneratorElement a c e1 e2 e3 e4 h1 h2 h3 hp]
    exact hu .e4
  have he1eq : e1 = a⁻¹ *
      projectivePolygonPairingGeneratorElement a c e1 e2 e3 e4 .e1 * a := by
    change e1 = a⁻¹ * (a * e1 * a⁻¹) * a
    group
  have he1 : e1 ∈ H := by
    rw [he1eq]
    exact H.mul_mem (H.mul_mem (H.inv_mem ha) (hu .e1)) ha
  let p4 := a * e1 * c⁻¹
  have he1inv : e1⁻¹ = e1 := by
    calc
      e1⁻¹ = e1⁻¹ * 1 := by simp
      _ = e1⁻¹ * (e1 * e1) := by rw [h1]
      _ = e1 := by group
  have hu4eq :
      projectivePolygonPairingGeneratorElement a c e1 e2 e3 e4 .e2 =
        p4 * e2 * p4⁻¹ := by
    have hp4inv : p4⁻¹ = c * e1 * a⁻¹ := by
      calc
        p4⁻¹ = c * e1⁻¹ * a⁻¹ := by
          dsimp [p4]
          group
        _ = c * e1 * a⁻¹ := by rw [he1inv]
    change a * e1 * c⁻¹ * e2 * c * e1 * a⁻¹ = p4 * e2 * p4⁻¹
    rw [hp4inv]
    dsimp [p4]
    group
  have he2eq : e2 = p4⁻¹ *
      projectivePolygonPairingGeneratorElement a c e1 e2 e3 e4 .e2 * p4 := by
    rw [hu4eq]
    group
  have hp4 : p4 ∈ H := by
    dsimp [p4]
    exact H.mul_mem (H.mul_mem ha he1) (H.inv_mem hc)
  have he2 : e2 ∈ H := by
    rw [he2eq]
    exact H.mul_mem (H.mul_mem (H.inv_mem hp4) (hu .e2)) hp4
  let p5 := a * e1 * c⁻¹ * e2 * a⁻¹
  have he3eq : e3 = p5⁻¹ * e4⁻¹ * c⁻¹ := by
    calc
      e3 = p5⁻¹ * (p5 * e3 * c * e4) * e4⁻¹ * c⁻¹ := by group
      _ = p5⁻¹ * e4⁻¹ * c⁻¹ := by
        rw [show p5 * e3 * c * e4 = 1 by simpa [p5] using hp]
        simp
  have hp5 : p5 ∈ H := by
    dsimp [p5]
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem ha he1) (H.inv_mem hc)) he2) (H.inv_mem ha)
  have he3 : e3 ∈ H := by
    rw [he3eq]
    exact H.mul_mem (H.mul_mem (H.inv_mem hp5) (H.inv_mem he4)) (H.inv_mem hc)
  exact ⟨ha, hc, he1, he2, he3, he4⟩

/-- The six projective polygon side-pairing translations in the base octagon
group. -/
def projectivePolygonPairingElement :
    ProjectivePolygonPairingGenerator → ProjectiveOctagonGroup :=
  projectivePolygonPairingGeneratorElement
    (PresentedGroup.of .a) (PresentedGroup.of .c)
    (PresentedGroup.of .e1) (PresentedGroup.of .e2)
    (PresentedGroup.of .e3) (PresentedGroup.of .e4)

/-- Every standard projective octagon generator lies in the subgroup generated
by the six polygon side-pairing translations. -/
theorem projectivePolygonPairingElements_contain_projectiveGenerators
    (x : ProjectiveOctagonGenerator) :
    PresentedGroup.of x ∈
      Subgroup.closure (Set.range projectivePolygonPairingElement) := by
  have h1 : (PresentedGroup.of .e1 : ProjectiveOctagonGroup) * PresentedGroup.of .e1 = 1 := by
    simpa [pow_two] using projectiveOctagon_e1_sq
  have h2 : (PresentedGroup.of .e2 : ProjectiveOctagonGroup) * PresentedGroup.of .e2 = 1 := by
    simpa [pow_two] using projectiveOctagon_e2_sq
  have h3 : (PresentedGroup.of .e3 : ProjectiveOctagonGroup) * PresentedGroup.of .e3 = 1 := by
    simpa [pow_two] using projectiveOctagon_e3_sq
  have h4 : (PresentedGroup.of .e4 : ProjectiveOctagonGroup) * PresentedGroup.of .e4 = 1 := by
    simpa [pow_two] using projectiveOctagon_e4_sq
  have h := projectivePolygonPairingGeneratorElements_contain_generators
    (PresentedGroup.of .a : ProjectiveOctagonGroup) (PresentedGroup.of .c)
    (PresentedGroup.of .e1) (PresentedGroup.of .e2)
    (PresentedGroup.of .e3) (PresentedGroup.of .e4)
    h1 h2 h3 h4 projectiveOctagon_polygon
  simpa [projectivePolygonPairingElement] using
    (show x = .a ∨ x = .c ∨ x = .e1 ∨ x = .e2 ∨ x = .e3 ∨ x = .e4 from by
      cases x <;> simp) |> fun hx => by
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2.1
        · exact h.2.2.2.2.1
        · exact h.2.2.2.2.2

/-- The projective octagon group is generated by its six polygon side-pairing
translations. -/
theorem projectivePolygonPairingElements_generate :
    Subgroup.closure (Set.range projectivePolygonPairingElement) = ⊤ := by
  apply top_unique
  rw [← PresentedGroup.closure_range_of projectiveOctagonRelators]
  apply (Subgroup.closure_le _).2
  rintro _ ⟨x, rfl⟩
  exact projectivePolygonPairingElements_contain_projectiveGenerators x

end

end SystolicGrowth
