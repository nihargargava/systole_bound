module

public import BuserSarnak.BuserSarnakProjectiveCenter

@[expose] public section

/-!
# Normalized free-product words for the octagon base

This module exposes the canonical reduced word of an octagon-base element,
together with its evaluation in the base group, in `PGL(2, ℝ)`, and under
the integer exponent homomorphism.
-/

namespace SystolicGrowth

noncomputable section

open scoped MatrixGroups

local instance : DecidableEq OctagonBaseFactor := Classical.decEq _
local instance (i : OctagonBaseFactor) :
    DecidableEq (OctagonBaseFactorGroup i) := Classical.decEq _

/-- The type of reduced words in the five free factors of the octagon base. -/
abbrev OctagonBaseReducedWord :=
  Monoid.CoprodI.Word OctagonBaseFactorGroup

/-- The canonical reduced free-product word representing a base element. -/
def octagonBaseReducedWord (g : OctagonBaseGroup) :
    OctagonBaseReducedWord :=
  Monoid.CoprodI.Word.equiv (octagonBaseToFreeProduct g)

/-- Multiplying the canonical word in the free product recovers the image
of the original base element. -/
lemma octagonBaseReducedWord_prod (g : OctagonBaseGroup) :
    (octagonBaseReducedWord g).prod = octagonBaseToFreeProduct g := by
  exact (Monoid.CoprodI.Word.equiv (M := OctagonBaseFactorGroup)).left_inv
    (octagonBaseToFreeProduct g)

/-- Interpret a dependent free-factor letter in the octagon base group. -/
def octagonBaseReducedLetterValue :
    (Σ i, OctagonBaseFactorGroup i) → OctagonBaseGroup
  | ⟨i, x⟩ => octagonBaseFactorInclusion i x

@[simp] lemma octagonBaseFreeProductToBase_of_letter
    (l : Σ i, OctagonBaseFactorGroup i) :
    octagonBaseFreeProductToBase (Monoid.CoprodI.of l.2) =
      octagonBaseReducedLetterValue l := by
  rcases l with ⟨i, x⟩
  change (x : OctagonBaseGroup) = (x : OctagonBaseGroup)
  rfl

private lemma octagonBaseFreeProductToBase_list_prod
    (l : List (Σ i, OctagonBaseFactorGroup i)) :
    octagonBaseFreeProductToBase
        (l.map (fun x => Monoid.CoprodI.of x.2)).prod =
      (l.map octagonBaseReducedLetterValue).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.map_cons, List.prod_cons, map_mul,
        octagonBaseFreeProductToBase_of_letter, ih,
        List.map_cons, List.prod_cons]

/-- Interpreting and multiplying all letters of the canonical word
reconstructs the original base element. -/
lemma octagonBaseReducedWord_value (g : OctagonBaseGroup) :
    ((octagonBaseReducedWord g).toList.map
      octagonBaseReducedLetterValue).prod = g := by
  calc
    _ = octagonBaseFreeProductToBase (octagonBaseReducedWord g).prod := by
      rw [Monoid.CoprodI.Word.prod,
        octagonBaseFreeProductToBase_list_prod]
    _ = octagonBaseFreeProductToBase (octagonBaseToFreeProduct g) := by
      rw [octagonBaseReducedWord_prod]
    _ = g := by
      exact DFunLike.congr_fun
        octagonBaseFreeProductToBase_comp_baseToFreeProduct g

/-- Interpret a reduced-word letter in the explicit projective action. -/
def octagonBaseReducedLetterPGL :
    (Σ i, OctagonBaseFactorGroup i) → PGL(2, ℝ) := fun l =>
  octagonBaseToPGL23 (octagonBaseReducedLetterValue l)

private lemma octagonBaseReducedLetterPGL_prod
    (l : List (Σ i, OctagonBaseFactorGroup i)) :
    (l.map octagonBaseReducedLetterPGL).prod =
      octagonBaseToPGL23 (l.map octagonBaseReducedLetterValue).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp [octagonBaseReducedLetterPGL, ih]

/-- The product of the projective interpretations of the canonical letters
is the projective image of the original base element. -/
lemma octagonBaseReducedWord_pgl (g : OctagonBaseGroup) :
    ((octagonBaseReducedWord g).toList.map
      octagonBaseReducedLetterPGL).prod = octagonBaseToPGL23 g := by
  rw [octagonBaseReducedLetterPGL_prod,
    octagonBaseReducedWord_value]

/-- Integer exponent contributed by one dependent free-factor letter. -/
def octagonBaseReducedLetterWeight :
    (Σ i, OctagonBaseFactorGroup i) → ℤ := fun l =>
  Multiplicative.toAdd
    (octagonBaseExponent (octagonBaseReducedLetterValue l))

private lemma octagonBaseReducedLetterWeight_sum
    (l : List (Σ i, OctagonBaseFactorGroup i)) :
    (l.map octagonBaseReducedLetterWeight).sum =
      Multiplicative.toAdd
        (octagonBaseExponent (l.map octagonBaseReducedLetterValue).prod) := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp [octagonBaseReducedLetterWeight, ih]

/-- The sum of letter weights in the canonical word is the exponent of the
represented base element. -/
lemma octagonBaseReducedWord_weight (g : OctagonBaseGroup) :
    ((octagonBaseReducedWord g).toList.map
      octagonBaseReducedLetterWeight).sum =
      Multiplicative.toAdd (octagonBaseExponent g) := by
  rw [octagonBaseReducedLetterWeight_sum,
    octagonBaseReducedWord_value]

end


end SystolicGrowth
