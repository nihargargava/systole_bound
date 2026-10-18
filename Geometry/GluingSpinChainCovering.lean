module

public import Geometry.GluingSpinChainQuotient
public import Geometry.GluingSeamIncidence
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

open UpperHalfPlane Topology
open scoped MatrixGroups UpperHalfPlane

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false

private theorem eqvGen_matching_iff {α : Type*} (r : α → α → Prop)
    (hno : ∀ a b c, r a b → r b c → False)
    (hright : ∀ a b c, r a b → r a c → b = c)
    (hleft : ∀ a b c, r a b → r c b → a = c) (a b : α) :
    Relation.EqvGen r a b ↔ a = b ∨ r a b ∨ r b a := by
  constructor
  · intro h
    induction h with
    | rel a b h => exact Or.inr (Or.inl h)
    | refl a => exact Or.inl rfl
    | symm a b h ih =>
      rcases ih with h | h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    | trans a b c hab hbc ihab ihbc =>
      rcases ihab with h | h | h
      · subst b
        exact ihbc
      · rcases ihbc with hc | hc | hc
        · subst c
          exact Or.inr (Or.inl h)
        · exact (hno _ _ _ h hc).elim
        · exact Or.inl (hleft _ _ _ h hc)
      · rcases ihbc with hc | hc | hc
        · subst c
          exact Or.inr (Or.inr h)
        · exact Or.inl (hright _ _ _ h hc)
        · exact (hno _ _ _ hc h).elim
  · rintro (h | h | h)
    · subst b
      exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ h
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h)

namespace ClosedHyperbolicSurface

/-- Compactness of the actual surface and circle gives compactness of its
genuine spin quotient, using actual compact deck-orbit representatives. -/
instance spinCarrierCompactSpace {g : ℕ} (X : ClosedHyperbolicSurface g) :
    CompactSpace X.SpinCarrier := by
  obtain ⟨K, hK, hcover⟩ := X.exists_compact_orbit_cover
  let f : ℍ × Circle → X.SpinCarrier := fun p =>
    Quotient.mk _ (halfPlaneSpinFrameHomeomorph.symm p)
  have hc : Continuous f :=
    continuous_quotient_mk'.comp halfPlaneSpinFrameHomeomorph.symm.continuous
  have he : f '' (K ×ˢ (Set.univ : Set Circle)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    induction q using Quotient.inductionOn with
    | h q =>
      obtain ⟨A, hA⟩ := hcover q.point
      let r : HalfPlaneSpinFrame := A • q
      refine ⟨(r.point, r.phase), ⟨hA, Set.mem_univ _⟩, ?_⟩
      apply Quotient.sound
      apply MulAction.orbitRel_apply.mpr
      exact MulAction.mem_orbit_iff.mpr ⟨A, rfl⟩
  apply isCompact_univ_iff.mp
  rw [← he]
  exact (hK.prod isCompact_univ).image hc

instance tangentFrameCarrierCompactSpace {g : ℕ} (X : ClosedHyperbolicSurface g) :
    CompactSpace X.TangentFrameCarrier := by
  obtain ⟨K, hK, hcover⟩ := X.exists_compact_orbit_cover
  let f : ℍ × Circle → X.TangentFrameCarrier := fun p =>
    Quotient.mk _ (halfPlaneTangentFrameHomeomorph.symm p)
  have hc : Continuous f :=
    continuous_quotient_mk'.comp halfPlaneTangentFrameHomeomorph.symm.continuous
  have he : f '' (K ×ˢ (Set.univ : Set Circle)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    induction q using Quotient.inductionOn with
    | h q =>
      obtain ⟨A, hA⟩ := hcover q.point
      let r : HalfPlaneTangentFrame := A • q
      refine ⟨(r.point, r.phase), ⟨hA, Set.mem_univ _⟩, ?_⟩
      apply Quotient.sound
      apply MulAction.orbitRel_apply.mpr
      exact MulAction.mem_orbit_iff.mpr ⟨A, rfl⟩
  apply isCompact_univ_iff.mp
  rw [← he]
  exact (hK.prod isCompact_univ).image hc

set_option backward.isDefEq.respectTransparency true in
theorem polarBoundary_isClosed {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ : ℝ) : IsClosed (X.polarBoundary o ρ) := by
  have hp : Continuous (fun u : Circle => gluingPolarPoint o u ρ) := by
    have ht : Continuous (fun u : Circle => (u, ρ)) :=
      continuous_id.prodMk continuous_const
    have h := (gluingPolarPoint_continuous o).comp ht
    dsimp only [Function.comp_def] at h
    exact h
  have hc : Continuous (fun u : Circle => X.orbitProjection (gluingPolarPoint o u ρ)) :=
    continuous_quotient_mk'.comp hp
  exact (isCompact_range hc).isClosed

instance spinBoundaryCarrierCompactSpace {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ : ℝ) : CompactSpace (X.SpinBoundaryCarrier o ρ) :=
  isCompact_iff_compactSpace.mp
    (((X.polarBoundary_isClosed o ρ).preimage X.continuous_spinBase).isCompact)

instance tangentBoundaryCarrierCompactSpace {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ : ℝ) : CompactSpace (X.TangentBoundaryCarrier o ρ) :=
  isCompact_iff_compactSpace.mp
    (((X.polarBoundary_isClosed o ρ).preimage X.continuous_tangentFrameBase).isCompact)

@[simp] theorem spinBase_spinAntipode {g : ℕ} (X : ClosedHyperbolicSurface g)
    (q : X.SpinCarrier) : X.spinBase (X.spinAntipode q) = X.spinBase q := by
  induction q using Quotient.inductionOn with
  | h q => rfl

def spinBoundaryAntipode {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (ρ : ℝ)
    (q : X.SpinBoundaryCarrier o ρ) : X.SpinBoundaryCarrier o ρ :=
  ⟨X.spinAntipode q.1, by simpa using q.2⟩

@[simp] theorem spinBoundaryAntipode_param {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ : ℝ) (p : Circle × Circle) :
    X.spinBoundaryAntipode o ρ (X.spinBoundaryParam o ρ p) =
      X.spinBoundaryParam o ρ (p.1, -p.2) := rfl

/-- The literal clutching respects actual antipodes, not a chosen sign rule. -/
theorem fermiSpinBoundaryHomeomorph_antipode {gIn gOut : ℕ}
    (XIn : ClosedHyperbolicSurface gIn) (XOut : ClosedHyperbolicSurface gOut)
    (oIn oOut : ℍ) {ρ RIn ROut : ℝ} (hρ : 0 < ρ)
    (hIn : ρ < RIn) (hOut : ρ < ROut)
    (hsIn : 2 * RIn < XIn.systole) (hsOut : 2 * ROut < XOut.systole)
    (q : XOut.SpinBoundaryCarrier oOut ρ) :
    XIn.spinBoundaryAntipode oIn ρ
      (fermiSpinBoundaryHomeomorph XIn XOut oIn oOut hρ hIn hOut hsIn hsOut q) =
        fermiSpinBoundaryHomeomorph XIn XOut oIn oOut hρ hIn hOut hsIn hsOut
          (XOut.spinBoundaryAntipode oOut ρ q) := by
  obtain ⟨p, rfl⟩ := XOut.spinBoundaryParam_surjective oOut ρ q
  rw [spinBoundaryAntipode_param, fermiSpinBoundaryHomeomorph_param,
    fermiSpinBoundaryHomeomorph_param, spinBoundaryAntipode_param]
  apply congrArg (XIn.spinBoundaryParam oIn ρ)
  apply Prod.ext
  · rfl
  · exact (mul_neg _ _).symm

end ClosedHyperbolicSurface

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

private theorem chainRelation_of_gluedMk_eq_of_adjacent
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (a b : P.ChainPieces) (ha : a.1 = gluingChainEdgeLeft k)
    (hb : b.1 = gluingChainEdgeRight k) (h : P.gluedMk a = P.gluedMk b) :
    P.chainRelation a b := by
  rcases (P.gluedMk_eq_iff a b).mp h with he | hr | hr
  · have hv := congrArg (fun q : P.ChainPieces => q.1.1) he
    rw [ha, hb] at hv
    change k.1 = k.1 + 1 at hv
    omega
  · exact hr
  · obtain ⟨l, z, hbs, hat⟩ := hr
    have hs := congrArg (fun q : P.ChainPieces => q.1.1) hbs
    have ht := congrArg (fun q : P.ChainPieces => q.1.1) hat
    rw [hb] at hs
    rw [ha] at ht
    change k.1 + 1 = l.1 at hs
    change k.1 = l.1 + 1 at ht
    omega

theorem spinChainRelation_base (P : ExerciseGluingPreparation C g n genera X)
    {a b : P.SpinChainPieces} (h : P.spinChainRelation a b) :
    P.chainRelation (P.spinChainPieceBase a) (P.spinChainPieceBase b) := by
  obtain ⟨k, q, rfl, rfl⟩ := h
  exact P.chainRelation_of_gluedMk_eq_of_adjacent k _ _ rfl rfl
    (P.gluedMk_spinSeamBase_eq k q)

theorem tangentChainRelation_base (P : ExerciseGluingPreparation C g n genera X)
    {a b : P.TangentChainPieces} (h : P.tangentChainRelation a b) :
    P.chainRelation (P.tangentChainPieceBase a) (P.tangentChainPieceBase b) := by
  obtain ⟨k, q, rfl, rfl⟩ := h
  exact P.chainRelation_of_gluedMk_eq_of_adjacent k _ _ rfl rfl
    (P.gluedMk_tangentSeamBase_eq k q)

theorem spinChainRelation_no_two_step (P : ExerciseGluingPreparation C g n genera X)
    {a b c : P.SpinChainPieces} (hab : P.spinChainRelation a b)
    (hbc : P.spinChainRelation b c) : False :=
  P.chainRelation_no_two_step (P.spinChainRelation_base hab) (P.spinChainRelation_base hbc)

theorem tangentChainRelation_no_two_step (P : ExerciseGluingPreparation C g n genera X)
    {a b c : P.TangentChainPieces} (hab : P.tangentChainRelation a b)
    (hbc : P.tangentChainRelation b c) : False :=
  P.chainRelation_no_two_step (P.tangentChainRelation_base hab) (P.tangentChainRelation_base hbc)

theorem spinChainRelation_right_unique (P : ExerciseGluingPreparation C g n genera X)
    {a b c : P.SpinChainPieces} (hab : P.spinChainRelation a b)
    (hac : P.spinChainRelation a c) : b = c := by
  obtain ⟨k, q, hak, hbk⟩ := hab
  obtain ⟨l, r, hal, hcl⟩ := hac
  have hs := hak.symm.trans hal
  have hv := congrArg (fun s : P.SpinChainPieces => s.1.1) hs
  change k.1 = l.1 at hv
  have hkl : k = l := Fin.ext hv
  subst l
  have hc := eq_of_heq (Sigma.mk.inj_iff.mp hs).2
  have hv : q.1 = r.1 :=
    congrArg (fun v : P.SpinChainComponent (gluingChainEdgeLeft k) => v.1) hc
  have hqr : q = r := Subtype.ext hv
  subst r
  exact hbk.trans hcl.symm

theorem tangentChainRelation_right_unique
    (P : ExerciseGluingPreparation C g n genera X)
    {a b c : P.TangentChainPieces} (hab : P.tangentChainRelation a b)
    (hac : P.tangentChainRelation a c) : b = c := by
  obtain ⟨k, q, hak, hbk⟩ := hab
  obtain ⟨l, r, hal, hcl⟩ := hac
  have hs := hak.symm.trans hal
  have hv := congrArg (fun s : P.TangentChainPieces => s.1.1) hs
  change k.1 = l.1 at hv
  have hkl : k = l := Fin.ext hv
  subst l
  have hc := eq_of_heq (Sigma.mk.inj_iff.mp hs).2
  have hv : q.1 = r.1 :=
    congrArg (fun v : P.TangentChainComponent (gluingChainEdgeLeft k) => v.1) hc
  have hqr : q = r := Subtype.ext hv
  subst r
  exact hbk.trans hcl.symm

theorem spinChainRelation_left_unique (P : ExerciseGluingPreparation C g n genera X)
    {a b c : P.SpinChainPieces} (hab : P.spinChainRelation a b)
    (hcb : P.spinChainRelation c b) : a = c := by
  obtain ⟨k, q, hak, hbk⟩ := hab
  obtain ⟨l, r, hcl, hbl⟩ := hcb
  have ht := hbk.symm.trans hbl
  have hv := congrArg (fun s : P.SpinChainPieces => s.1.1) ht
  change k.1 + 1 = l.1 + 1 at hv
  have hkl : k = l := Fin.ext (by omega)
  subst l
  have hc := eq_of_heq (Sigma.mk.inj_iff.mp ht).2
  have hv : (P.seamSpinHomeomorph k q).1 = (P.seamSpinHomeomorph k r).1 :=
    congrArg (fun v : P.SpinChainComponent (gluingChainEdgeRight k) => v.1) hc
  have hqr : q = r := (P.seamSpinHomeomorph k).injective (Subtype.ext hv)
  subst r
  exact hak.trans hcl.symm

theorem tangentChainRelation_left_unique
    (P : ExerciseGluingPreparation C g n genera X)
    {a b c : P.TangentChainPieces} (hab : P.tangentChainRelation a b)
    (hcb : P.tangentChainRelation c b) : a = c := by
  obtain ⟨k, q, hak, hbk⟩ := hab
  obtain ⟨l, r, hcl, hbl⟩ := hcb
  have ht := hbk.symm.trans hbl
  have hv := congrArg (fun s : P.TangentChainPieces => s.1.1) ht
  change k.1 + 1 = l.1 + 1 at hv
  have hkl : k = l := Fin.ext (by omega)
  subst l
  have hc := eq_of_heq (Sigma.mk.inj_iff.mp ht).2
  have hv : (P.seamTangentHomeomorph k q).1 = (P.seamTangentHomeomorph k r).1 :=
    congrArg (fun v : P.TangentChainComponent (gluingChainEdgeRight k) => v.1) hc
  have hqr : q = r := (P.seamTangentHomeomorph k).injective (Subtype.ext hv)
  subst r
  exact hak.trans hcl.symm

/-- The genuine spin seam relation remains a partial matching. -/
theorem eqvGen_spinChainRelation_iff (P : ExerciseGluingPreparation C g n genera X)
    (a b : P.SpinChainPieces) :
    Relation.EqvGen P.spinChainRelation a b ↔
      a = b ∨ P.spinChainRelation a b ∨ P.spinChainRelation b a :=
  eqvGen_matching_iff P.spinChainRelation (fun _ _ _ => P.spinChainRelation_no_two_step)
    (fun _ _ _ => P.spinChainRelation_right_unique)
    (fun _ _ _ => P.spinChainRelation_left_unique) a b

theorem eqvGen_tangentChainRelation_iff (P : ExerciseGluingPreparation C g n genera X)
    (a b : P.TangentChainPieces) :
    Relation.EqvGen P.tangentChainRelation a b ↔
      a = b ∨ P.tangentChainRelation a b ∨ P.tangentChainRelation b a :=
  eqvGen_matching_iff P.tangentChainRelation (fun _ _ _ => P.tangentChainRelation_no_two_step)
    (fun _ _ _ => P.tangentChainRelation_right_unique)
    (fun _ _ _ => P.tangentChainRelation_left_unique) a b

theorem gluedSpinMk_injective_component (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) :
    Function.Injective (fun q : P.SpinChainComponent i =>
      (Quotient.mk P.spinChainSetoid ⟨i, q⟩ : P.GluedSpinCarrier)) := by
  intro q r h
  rcases (P.eqvGen_spinChainRelation_iff ⟨i, q⟩ ⟨i, r⟩).mp (Quotient.exact h) with
    he | hr | hr
  · exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
  · exact (P.chainRelation_components_ne (P.spinChainRelation_base hr) rfl).elim
  · exact (P.chainRelation_components_ne (P.spinChainRelation_base hr) rfl).elim

theorem gluedTangentMk_injective_component (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) :
    Function.Injective (fun q : P.TangentChainComponent i =>
      (Quotient.mk P.tangentChainSetoid ⟨i, q⟩ : P.GluedTangentCarrier)) := by
  intro q r h
  rcases (P.eqvGen_tangentChainRelation_iff ⟨i, q⟩ ⟨i, r⟩).mp (Quotient.exact h) with
    he | hr | hr
  · exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
  · exact (P.chainRelation_components_ne (P.tangentChainRelation_base hr) rfl).elim
  · exact (P.chainRelation_components_ne (P.tangentChainRelation_base hr) rfl).elim

def spinChainComponentAntipode (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) (q : P.SpinChainComponent i) : P.SpinChainComponent i :=
  ⟨(X i).spinAntipode q.1, by simpa using q.2⟩

def spinChainPieceAntipode (P : ExerciseGluingPreparation C g n genera X)
    (q : P.SpinChainPieces) : P.SpinChainPieces :=
  ⟨q.1, P.spinChainComponentAntipode q.1 q.2⟩

theorem seamSpinHomeomorph_antipode
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : (X (gluingChainEdgeLeft k)).SpinBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    (X (gluingChainEdgeRight k)).spinBoundaryAntipode
      (P.centers (gluingChainEdgeRight k)).1 (gluingRadius C g)
        (P.seamSpinHomeomorph k q) =
          P.seamSpinHomeomorph k
            ((X (gluingChainEdgeLeft k)).spinBoundaryAntipode
              (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) q) :=
  ClosedHyperbolicSurface.fermiSpinBoundaryHomeomorph_antipode _ _ _ _ _ _ _ _ _ q

@[simp] theorem spinChainPieceAntipode_seamSource
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : (X (gluingChainEdgeLeft k)).SpinBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    P.spinChainPieceAntipode (P.spinSeamSource k q) = P.spinSeamSource k
      ((X (gluingChainEdgeLeft k)).spinBoundaryAntipode
        (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) q) := rfl

@[simp] theorem spinChainPieceAntipode_seamTarget
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : (X (gluingChainEdgeLeft k)).SpinBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    P.spinChainPieceAntipode (P.spinSeamTarget k q) = P.spinSeamTarget k
      ((X (gluingChainEdgeLeft k)).spinBoundaryAntipode
        (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) q) := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    change (X (gluingChainEdgeRight k)).spinAntipode (P.seamSpinHomeomorph k q).1 = _
    exact congrArg Subtype.val (P.seamSpinHomeomorph_antipode k q)

theorem spinChainRelation_antipode (P : ExerciseGluingPreparation C g n genera X)
    {a b : P.SpinChainPieces} (h : P.spinChainRelation a b) :
    P.spinChainRelation (P.spinChainPieceAntipode a) (P.spinChainPieceAntipode b) := by
  obtain ⟨k, q, rfl, rfl⟩ := h
  rw [P.spinChainPieceAntipode_seamSource, P.spinChainPieceAntipode_seamTarget]
  exact ⟨k, _, rfl, rfl⟩

theorem eqvGen_spinChainRelation_antipode
    (P : ExerciseGluingPreparation C g n genera X) {a b : P.SpinChainPieces}
    (h : Relation.EqvGen P.spinChainRelation a b) :
    Relation.EqvGen P.spinChainRelation
      (P.spinChainPieceAntipode a) (P.spinChainPieceAntipode b) := by
  induction h with
  | rel a b h => exact Relation.EqvGen.rel _ _ (P.spinChainRelation_antipode h)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b h ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab hbc ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc

/-- The genuine clutched quotient has its actual antipodal involution. -/
def gluedSpinAntipode (P : ExerciseGluingPreparation C g n genera X) :
    P.GluedSpinCarrier → P.GluedSpinCarrier :=
  Quotient.map P.spinChainPieceAntipode fun _ _ h => P.eqvGen_spinChainRelation_antipode h

@[simp] theorem spinChainPieceAntipode_involutive
    (P : ExerciseGluingPreparation C g n genera X) (q : P.SpinChainPieces) :
    P.spinChainPieceAntipode (P.spinChainPieceAntipode q) = q := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact (X q.1).spinAntipode_involutive q.2.1

@[simp] theorem gluedSpinAntipode_involutive
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedSpinCarrier) :
    P.gluedSpinAntipode (P.gluedSpinAntipode q) = q := by
  induction q using Quotient.inductionOn with
  | h q => exact congrArg (Quotient.mk _) (P.spinChainPieceAntipode_involutive q)

theorem gluedSpinAntipode_ne (P : ExerciseGluingPreparation C g n genera X)
    (q : P.GluedSpinCarrier) : P.gluedSpinAntipode q ≠ q := by
  induction q using Quotient.inductionOn with
  | h q =>
    intro h
    have he := P.gluedSpinMk_injective_component q.1 h
    exact (X q.1).spinAntipode_ne q.2.1 (congrArg Subtype.val he)

theorem continuous_gluedSpinAntipode
    (P : ExerciseGluingPreparation C g n genera X) : Continuous P.gluedSpinAntipode := by
  have hc : Continuous P.spinChainPieceAntipode := by
    change Continuous (Sigma.map id P.spinChainComponentAntipode)
    apply continuous_sigma_map.mpr
    intro i
    exact ((X i).continuous_spinAntipode.comp continuous_subtype_val).subtype_mk _
  exact (continuous_quotient_mk'.comp hc).quotient_lift _

@[simp] theorem spinChainPieceSquare_antipode
    (P : ExerciseGluingPreparation C g n genera X) (q : P.SpinChainPieces) :
    P.spinChainPieceSquare (P.spinChainPieceAntipode q) = P.spinChainPieceSquare q := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact ((X q.1).spinSquare_eq_iff _ _).mpr (Or.inr rfl)

/-- Before gluing, squaring identifies exactly two actual antipodal pieces. -/
theorem spinChainPieceSquare_eq_iff
    (P : ExerciseGluingPreparation C g n genera X) (a b : P.SpinChainPieces) :
    P.spinChainPieceSquare a = P.spinChainPieceSquare b ↔
      a = b ∨ a = P.spinChainPieceAntipode b := by
  constructor
  · rintro h
    rcases a with ⟨i, a⟩
    rcases b with ⟨j, b⟩
    have hij := congrArg Sigma.fst h
    change i = j at hij
    subst j
    have hc := congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
    rcases ((X i).spinSquare_eq_iff a.1 b.1).mp hc with he | he
    · exact Or.inl (congrArg (Sigma.mk i) (Subtype.ext he))
    · exact Or.inr (congrArg (Sigma.mk i) (Subtype.ext he))
  · rintro (h | h)
    · exact congrArg P.spinChainPieceSquare h
    · rw [h, P.spinChainPieceSquare_antipode]

/-- Every literal tangent seam pair lifts to a literal spin seam pair. -/
theorem tangentChainRelation_lift
    (P : ExerciseGluingPreparation C g n genera X) {a b : P.TangentChainPieces}
    (h : P.tangentChainRelation a b) :
    ∃ c d : P.SpinChainPieces,
      P.spinChainPieceSquare c = a ∧ P.spinChainPieceSquare d = b ∧
        P.spinChainRelation c d := by
  obtain ⟨k, q, rfl, rfl⟩ := h
  obtain ⟨r, hr⟩ := (X (gluingChainEdgeLeft k)).spinSquare_surjective q.1
  let r' : (X (gluingChainEdgeLeft k)).SpinBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) :=
    ⟨r, by simpa [← hr] using q.2⟩
  have he : (X (gluingChainEdgeLeft k)).spinBoundarySquare
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) r' = q := Subtype.ext hr
  refine ⟨P.spinSeamSource k r', P.spinSeamTarget k r', ?_, ?_, k, r', rfl, rfl⟩
  · rw [P.spinChainPieceSquare_seamSource, he]
  · rw [P.spinChainPieceSquare_seamTarget, he]

private theorem spinMk_eq_or_antipode_of_tangentChainRelation
    (P : ExerciseGluingPreparation C g n genera X) {a b : P.SpinChainPieces}
    (h : P.tangentChainRelation (P.spinChainPieceSquare a) (P.spinChainPieceSquare b)) :
    (Quotient.mk P.spinChainSetoid a : P.GluedSpinCarrier) = Quotient.mk _ b ∨
      Quotient.mk P.spinChainSetoid a = P.gluedSpinAntipode (Quotient.mk _ b) := by
  obtain ⟨c, d, hc, hd, hcd⟩ := P.tangentChainRelation_lift h
  have he : (Quotient.mk P.spinChainSetoid c : P.GluedSpinCarrier) = Quotient.mk _ d :=
    Quotient.sound (Relation.EqvGen.rel _ _ hcd)
  have ha : (Quotient.mk P.spinChainSetoid a : P.GluedSpinCarrier) = Quotient.mk _ c ∨
      Quotient.mk P.spinChainSetoid a = P.gluedSpinAntipode (Quotient.mk _ c) := by
    rcases (P.spinChainPieceSquare_eq_iff a c).mp hc.symm with h | h
    · exact Or.inl (congrArg (Quotient.mk _) h)
    · exact Or.inr (congrArg (Quotient.mk _) h)
  have hb : (Quotient.mk P.spinChainSetoid b : P.GluedSpinCarrier) = Quotient.mk _ d ∨
      Quotient.mk P.spinChainSetoid b = P.gluedSpinAntipode (Quotient.mk _ d) := by
    rcases (P.spinChainPieceSquare_eq_iff b d).mp hd.symm with h | h
    · exact Or.inl (congrArg (Quotient.mk _) h)
    · exact Or.inr (congrArg (Quotient.mk _) h)
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exact Or.inl (ha.trans (he.trans hb.symm))
    · right
      rw [hb, P.gluedSpinAntipode_involutive]
      exact ha.trans he
  · rcases hb with hb | hb
    · exact Or.inr (ha.trans (congrArg P.gluedSpinAntipode (he.trans hb.symm)))
    · exact Or.inl (ha.trans ((congrArg P.gluedSpinAntipode he).trans hb.symm))

@[simp] theorem gluedSpinSquare_gluedSpinAntipode
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedSpinCarrier) :
    P.gluedSpinSquare (P.gluedSpinAntipode q) = P.gluedSpinSquare q := by
  induction q using Quotient.inductionOn with
  | h q => exact congrArg (Quotient.mk _) (P.spinChainPieceSquare_antipode q)

/-- The actual finite seam quotient adds no extra square fibers. -/
theorem gluedSpinSquare_eq_iff (P : ExerciseGluingPreparation C g n genera X)
    (q r : P.GluedSpinCarrier) :
    P.gluedSpinSquare q = P.gluedSpinSquare r ↔
      q = r ∨ q = P.gluedSpinAntipode r := by
  induction q using Quotient.inductionOn with
  | h q =>
    induction r using Quotient.inductionOn with
    | h r =>
      constructor
      · intro h
        rcases (P.eqvGen_tangentChainRelation_iff _ _).mp (Quotient.exact h) with
          he | hr | hr
        · rcases (P.spinChainPieceSquare_eq_iff q r).mp he with he | he
          · exact Or.inl (congrArg (Quotient.mk _) he)
          · exact Or.inr (congrArg (Quotient.mk _) he)
        · exact P.spinMk_eq_or_antipode_of_tangentChainRelation hr
        · rcases P.spinMk_eq_or_antipode_of_tangentChainRelation hr with he | he
          · exact Or.inl he.symm
          · right
            rw [he, P.gluedSpinAntipode_involutive]
      · rintro (h | h)
        · exact congrArg P.gluedSpinSquare h
        · rw [h, P.gluedSpinSquare_gluedSpinAntipode]

theorem gluedSpinSquare_fiber (P : ExerciseGluingPreparation C g n genera X)
    (q : P.GluedSpinCarrier) :
    P.gluedSpinSquare ⁻¹' {P.gluedSpinSquare q} = {q, P.gluedSpinAntipode q} := by
  ext r
  exact P.gluedSpinSquare_eq_iff r q

/-- Every actual clutched tangent direction has exactly two distinct spins. -/
theorem gluedSpinSquare_fiber_ncard (P : ExerciseGluingPreparation C g n genera X)
    (q : P.GluedTangentCarrier) : (P.gluedSpinSquare ⁻¹' {q}).ncard = 2 := by
  obtain ⟨r, rfl⟩ := P.gluedSpinSquare_surjective q
  rw [P.gluedSpinSquare_fiber]
  exact Set.ncard_pair (P.gluedSpinAntipode_ne r).symm

instance spinChainComponentCompactSpace
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    CompactSpace (P.SpinChainComponent i) :=
  isCompact_iff_compactSpace.mp
    (((X i).isClosed_puncturedComponentSet _ _ _ i).preimage
      (X i).continuous_spinBase).isCompact

instance tangentChainComponentCompactSpace
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    CompactSpace (P.TangentChainComponent i) :=
  isCompact_iff_compactSpace.mp
    (((X i).isClosed_puncturedComponentSet _ _ _ i).preimage
      (X i).continuous_tangentFrameBase).isCompact

instance spinChainPiecesCompactSpace (P : ExerciseGluingPreparation C g n genera X) :
    CompactSpace P.SpinChainPieces := by
  dsimp only [SpinChainPieces]
  infer_instance

instance tangentChainPiecesCompactSpace (P : ExerciseGluingPreparation C g n genera X) :
    CompactSpace P.TangentChainPieces := by
  dsimp only [TangentChainPieces]
  infer_instance

instance gluedSpinCarrierCompactSpace (P : ExerciseGluingPreparation C g n genera X) :
    CompactSpace P.GluedSpinCarrier := Quotient.compactSpace

instance gluedTangentCarrierCompactSpace (P : ExerciseGluingPreparation C g n genera X) :
    CompactSpace P.GluedTangentCarrier := Quotient.compactSpace

theorem continuous_spinSeamSource (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) : Continuous (P.spinSeamSource k) := by
  have hc : Continuous (P.spinRightBoundaryInclusion (gluingChainEdgeLeft k)) :=
    continuous_subtype_val.subtype_mk _
  exact continuous_sigmaMk.comp hc

theorem continuous_spinSeamTarget (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) : Continuous (P.spinSeamTarget k) := by
  have hc : Continuous (P.spinLeftBoundaryInclusion (gluingChainEdgeRight k)) :=
    continuous_subtype_val.subtype_mk _
  exact continuous_sigmaMk.comp (hc.comp (P.seamSpinHomeomorph k).continuous)

theorem continuous_tangentSeamSource (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) : Continuous (P.tangentSeamSource k) := by
  have hc : Continuous (P.tangentRightBoundaryInclusion (gluingChainEdgeLeft k)) :=
    continuous_subtype_val.subtype_mk _
  exact continuous_sigmaMk.comp hc

theorem continuous_tangentSeamTarget (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) : Continuous (P.tangentSeamTarget k) := by
  have hc : Continuous (P.tangentLeftBoundaryInclusion (gluingChainEdgeRight k)) :=
    continuous_subtype_val.subtype_mk _
  exact continuous_sigmaMk.comp (hc.comp (P.seamTangentHomeomorph k).continuous)

theorem spinChainRelation_isClosed (P : ExerciseGluingPreparation C g n genera X) :
    IsClosed {p : P.SpinChainPieces × P.SpinChainPieces | P.spinChainRelation p.1 p.2} := by
  have hc (k : Fin (n - 1)) :
      IsClosed (Set.range (fun q => (P.spinSeamSource k q, P.spinSeamTarget k q))) :=
    (isCompact_range ((P.continuous_spinSeamSource k).prodMk
      (P.continuous_spinSeamTarget k))).isClosed
  convert isClosed_iUnion_of_finite hc using 1
  ext p
  constructor
  · rintro ⟨k, q, ha, hb⟩
    exact Set.mem_iUnion.mpr ⟨k, q, Prod.ext ha.symm hb.symm⟩
  · intro hp
    obtain ⟨k, q, hq⟩ := Set.mem_iUnion.mp hp
    exact ⟨k, q, (congrArg Prod.fst hq).symm, (congrArg Prod.snd hq).symm⟩

theorem tangentChainRelation_isClosed (P : ExerciseGluingPreparation C g n genera X) :
    IsClosed {p : P.TangentChainPieces × P.TangentChainPieces |
      P.tangentChainRelation p.1 p.2} := by
  have hc (k : Fin (n - 1)) :
      IsClosed (Set.range (fun q => (P.tangentSeamSource k q, P.tangentSeamTarget k q))) :=
    (isCompact_range ((P.continuous_tangentSeamSource k).prodMk
      (P.continuous_tangentSeamTarget k))).isClosed
  convert isClosed_iUnion_of_finite hc using 1
  ext p
  constructor
  · rintro ⟨k, q, ha, hb⟩
    exact Set.mem_iUnion.mpr ⟨k, q, Prod.ext ha.symm hb.symm⟩
  · intro hp
    obtain ⟨k, q, hq⟩ := Set.mem_iUnion.mp hp
    exact ⟨k, q, (congrArg Prod.fst hq).symm, (congrArg Prod.snd hq).symm⟩

theorem Internal.GluingSpinChainCoveringHelpers.t2Space_quotient_of_closed_relation {α : Type*} [TopologicalSpace α]
    [CompactSpace α] (s : Setoid α)
    (hs : IsClosed {p : α × α | s.r p.1 p.2}) : T2Space (Quotient s) := by
  let f : α → Quotient s := Quotient.mk s
  have hf : Continuous f := continuous_quotient_mk'
  have hc : IsClosedMap f := by
    intro K hK
    apply isQuotientMap_quotient_mk'.isClosed_preimage.mp
    change IsClosed (f ⁻¹' (f '' K))
    have he : f ⁻¹' (f '' K) =
        Prod.fst '' ({p : α × α | s.r p.1 p.2} ∩ Prod.snd ⁻¹' K) := by
      ext a
      constructor
      · rintro ⟨b, hb, hba⟩
        exact ⟨(a, b), ⟨Quotient.exact hba.symm, hb⟩, rfl⟩
      · rintro ⟨⟨a', b⟩, ⟨hrel, hb⟩, ha⟩
        dsimp only at ha
        subst a'
        exact ⟨b, hb, (Quotient.sound hrel).symm⟩
    rw [he]
    exact isClosedMap_fst_of_compactSpace _ (hs.inter (hK.preimage continuous_snd))
  have hp : IsProperMap f := by
    apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    refine ⟨hf, hc, ?_⟩
    intro q
    obtain ⟨a, rfl⟩ := Quotient.exists_rep q
    have he : f ⁻¹' {f a} = (fun b : α => (b, a)) ⁻¹' {p : α × α | s.r p.1 p.2} := by
      ext b
      exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
    rw [he]
    exact (hs.preimage (continuous_id.prodMk continuous_const)).isCompact
  apply t2_iff_isClosed_diagonal.mpr
  have hprod := hp.prodMap hp
  have hsurj : Function.Surjective (Prod.map f f) := by
    rintro ⟨a, b⟩
    obtain ⟨a', rfl⟩ := Quotient.exists_rep a
    obtain ⟨b', rfl⟩ := Quotient.exists_rep b
    exact ⟨(a', b'), rfl⟩
  apply (hprod.isClosedMap.isQuotientMap hprod.continuous hsurj).isClosed_preimage.mp
  convert hs using 1
  ext p
  exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

instance gluedSpinCarrierT2Space (P : ExerciseGluingPreparation C g n genera X) :
    T2Space P.GluedSpinCarrier := by
  apply Internal.GluingSpinChainCoveringHelpers.t2Space_quotient_of_closed_relation
  have hc := (isClosed_diagonal (X := P.SpinChainPieces)).union
    (P.spinChainRelation_isClosed.union
      (P.spinChainRelation_isClosed.preimage continuous_swap))
  convert hc using 1
  ext p
  exact P.eqvGen_spinChainRelation_iff p.1 p.2

instance gluedTangentCarrierT2Space (P : ExerciseGluingPreparation C g n genera X) :
    T2Space P.GluedTangentCarrier := by
  apply Internal.GluingSpinChainCoveringHelpers.t2Space_quotient_of_closed_relation
  have hc := (isClosed_diagonal (X := P.TangentChainPieces)).union
    (P.tangentChainRelation_isClosed.union
      (P.tangentChainRelation_isClosed.preimage continuous_swap))
  convert hc using 1
  ext p
  exact P.eqvGen_tangentChainRelation_iff p.1 p.2

theorem gluedSpinSquare_isQuotientMap (P : ExerciseGluingPreparation C g n genera X) :
    IsQuotientMap P.gluedSpinSquare :=
  .of_surjective_continuous P.gluedSpinSquare_surjective P.continuous_gluedSpinSquare

private theorem gluedSpinSquare_preimage_image
    (P : ExerciseGluingPreparation C g n genera X) (s : Set P.GluedSpinCarrier) :
    P.gluedSpinSquare ⁻¹' (P.gluedSpinSquare '' s) =
      s ∪ P.gluedSpinAntipode ⁻¹' s := by
  ext q
  constructor
  · rintro ⟨r, hr, h⟩
    rcases (P.gluedSpinSquare_eq_iff q r).mp h.symm with h | h
    · exact Or.inl (h ▸ hr)
    · right
      change P.gluedSpinAntipode q ∈ s
      rwa [h, P.gluedSpinAntipode_involutive]
  · rintro (h | h)
    · exact ⟨q, h, rfl⟩
    · exact ⟨P.gluedSpinAntipode q, h, P.gluedSpinSquare_gluedSpinAntipode q⟩

theorem gluedSpinSquare_isOpenMap (P : ExerciseGluingPreparation C g n genera X) :
    IsOpenMap P.gluedSpinSquare := by
  intro s hs
  apply P.gluedSpinSquare_isQuotientMap.isOpen_preimage.mp
  rw [P.gluedSpinSquare_preimage_image]
  exact hs.union (hs.preimage P.continuous_gluedSpinAntipode)

/-- Actual disjoint antipodal neighborhoods construct genuine inverse sheets. -/
theorem gluedSpinSquare_isLocalHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) :
    IsLocalHomeomorph P.gluedSpinSquare := by
  apply IsLocalHomeomorph.mk
  intro q
  letI : Nonempty P.GluedSpinCarrier := ⟨q⟩
  obtain ⟨U, V, hU, hV, hqU, haqV, hd⟩ := t2_separation (P.gluedSpinAntipode_ne q).symm
  let S : Set P.GluedSpinCarrier := U ∩ P.gluedSpinAntipode ⁻¹' V
  have hS : IsOpen S := hU.inter (hV.preimage P.continuous_gluedSpinAntipode)
  have hinj : Set.InjOn P.gluedSpinSquare S := by
    intro a ha b hb he
    rcases (P.gluedSpinSquare_eq_iff a b).mp he with h | h
    · exact h
    · exact (Set.disjoint_left.mp hd ha.1 (h ▸ hb.2)).elim
  let e := OpenPartialHomeomorph.ofContinuousOpen
    (hinj.toPartialEquiv P.gluedSpinSquare S)
    P.continuous_gluedSpinSquare.continuousOn P.gluedSpinSquare_isOpenMap hS
  exact ⟨e, ⟨hqU, haqV⟩, fun _ _ => rfl⟩

/-- The actual clutched square map is a genuine global two-sheeted covering. -/
theorem gluedSpinSquare_isCoveringMap
    (P : ExerciseGluingPreparation C g n genera X) : IsCoveringMap P.gluedSpinSquare := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  apply P.continuous_gluedSpinSquare.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
  · intro q _hq
    obtain ⟨r, rfl⟩ := P.gluedSpinSquare_surjective q
    rw [P.gluedSpinSquare_fiber]
    exact (Set.finite_singleton _).insert _
  · exact P.gluedSpinSquare_isLocalHomeomorph.isLocalHomeomorphOn

end ExerciseGluingPreparation

#print axioms ExerciseGluingPreparation.eqvGen_spinChainRelation_iff
#print axioms ExerciseGluingPreparation.eqvGen_tangentChainRelation_iff
#print axioms ExerciseGluingPreparation.gluedSpinMk_injective_component
#print axioms ExerciseGluingPreparation.seamSpinHomeomorph_antipode
#print axioms ExerciseGluingPreparation.gluedSpinAntipode_ne
#print axioms ExerciseGluingPreparation.continuous_gluedSpinAntipode
#print axioms ExerciseGluingPreparation.tangentChainRelation_lift
#print axioms ExerciseGluingPreparation.gluedSpinSquare_eq_iff
#print axioms ExerciseGluingPreparation.gluedSpinSquare_fiber_ncard
#print axioms ExerciseGluingPreparation.gluedSpinCarrierT2Space
#print axioms ExerciseGluingPreparation.gluedTangentCarrierT2Space
#print axioms ExerciseGluingPreparation.gluedSpinSquare_isCoveringMap

end
end SystolicGrowth
