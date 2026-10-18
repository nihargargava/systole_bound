module

public import BuserSarnak.BuserSarnakProjectivePingPong
public import BuserSarnak.BuserSarnakHNNTransversal
public import BuserSarnak.BuserSarnakProjectiveLinePingPong

@[expose] public section

/-!
# A boundary ping-pong criterion for the octagon HNN extension

This file propagates local `MapsTo` statements through Mathlib's reduced HNN
words.  It then specializes the resulting injectivity criterion to the
explicit exponent-zero normal form and boundary intervals of the octagon.
-/

open Monoid Subgroup Function
open scoped Pointwise

namespace HNNExtension

variable {G H X : Type*} [Group G] [Group H] [MulAction H X]
  {A B : Subgroup G} {φ : A ≃* B}

open NormalWord

/-- The stable-letter tail represented by a reduced-word list. -/
def ReducedWord.stableTailProd (l : List (ℤˣ × G)) :
    HNNExtension G A B φ :=
  (l.map fun x => HNNExtension.t ^ (x.1 : ℤ) * HNNExtension.of x.2).prod

/-- The rightmost base coefficient sends the input set into the complement
needed by its adjacent stable letter. -/
def ReducedWord.LastBaseMapsOutside
    (F : HNNExtension G A B φ →* H) (P : ℤˣ → Set X) :
    List (ℤˣ × G) → Set X → Prop
  | [], _ => True
  | [(u, g)], R =>
      Set.MapsTo (fun z => F (HNNExtension.of g) • z) R (P (-u))ᶜ
  | _ :: b :: l, R => LastBaseMapsOutside F P (b :: l) R

/-- `LastBaseMapsOutside` only inspects the final stable-letter/base pair. -/
theorem ReducedWord.lastBaseMapsOutside_iff_getLast
    (F : HNNExtension G A B φ →* H) (P : ℤˣ → Set X)
    (a : ℤˣ × G) (l : List (ℤˣ × G)) (R : Set X) :
    LastBaseMapsOutside F P (a :: l) R ↔
      Set.MapsTo
        (fun z => F (HNNExtension.of ((a :: l).getLast (by simp)).2) • z)
        R (P (-((a :: l).getLast (by simp)).1))ᶜ := by
  induction l generalizing a with
  | nil => simp [LastBaseMapsOutside]
  | cons b l ih =>
      simpa [LastBaseMapsOutside, List.getLast_cons] using ih b

/-- Local stable-letter and base-coefficient separation propagates across a
reduced HNN tail. -/
theorem ReducedWord.stableTail_mapsTo
    (F : HNNExtension G A B φ →* H) (P : ℤˣ → Set X)
    (Q : ℤˣ → G → Prop)
    (hstable : ∀ u : ℤˣ,
      Set.MapsTo (fun z => F (HNNExtension.t ^ (u : ℤ)) • z)
        (P (-u))ᶜ (P u))
    (hbase : ∀ (u v : ℤˣ) (g : G), Q u g →
      (g ∈ toSubgroup A B u → u = v) →
        Set.MapsTo (fun z => F (HNNExtension.of g) • z)
          (P v) (P (-u))ᶜ)
    (a : ℤˣ × G) (l : List (ℤˣ × G))
    (hchain : (a :: l).IsChain
      (fun x y => x.2 ∈ toSubgroup A B x.1 → x.1 = y.1))
    (hcoeff : ∀ x ∈ a :: l, Q x.1 x.2)
    (R : Set X) (hlast : LastBaseMapsOutside F P (a :: l) R) :
    Set.MapsTo
      (fun z => F (stableTailProd (φ := φ) (a :: l)) • z) R (P a.1) := by
  induction l generalizing a with
  | nil =>
      intro z hz
      have hg := hlast hz
      have ht := hstable a.1 hg
      simpa [stableTailProd, map_mul, mul_smul] using ht
  | cons b l ih =>
      have hchainTail := (List.isChain_cons.mp hchain).2
      have hcoeffTail : ∀ x ∈ b :: l, Q x.1 x.2 := by
        intro x hx
        exact hcoeff x (List.mem_cons_of_mem a hx)
      have hlastTail : LastBaseMapsOutside F P (b :: l) R := by
        simpa [LastBaseMapsOutside] using hlast
      have htail := ih b hchainTail hcoeffTail hlastTail
      have hab : a.2 ∈ toSubgroup A B a.1 → a.1 = b.1 :=
        (List.isChain_cons.mp hchain).1 b (by simp)
      intro z hz
      have hzTail := htail hz
      have hg := hbase a.1 b.1 a.2 (hcoeff a (by simp)) hab hzTail
      have ht := hstable a.1 hg
      simpa [stableTailProd, map_mul, mul_smul] using ht

/-- An HNN homomorphism is injective if it is injective on the base and every
nonempty normal word maps one nonempty set into a disjoint set. -/
theorem hom_injective_of_reducedWord_mapsTo
    (d : NormalWord.TransversalPair G A B)
    (F : HNNExtension G A B φ →* H)
    (hbase : Function.Injective (F.comp HNNExtension.of))
    (hseparate : ∀ w : NormalWord d, w.toList ≠ [] →
      ∃ U V : Set X, U.Nonempty ∧ Disjoint U V ∧
        Set.MapsTo (fun z => F (w.prod φ) • z) U V) :
    Function.Injective F := by
  rw [injective_iff_map_eq_one]
  intro y hy
  let w : NormalWord d := (NormalWord.equiv φ d) y
  have hprod : w.prod φ = y := (NormalWord.equiv φ d).symm_apply_apply y
  have hmap : F (w.prod φ) = 1 := by
    rw [hprod]
    exact hy
  have hnil : w.toList = [] := by
    by_contra hn
    obtain ⟨U, V, hU, hUV, hmaps⟩ := hseparate w hn
    obtain ⟨z, hz⟩ := hU
    have hzV := hmaps hz
    simp only [hmap, one_smul] at hzV
    exact Set.disjoint_left.mp hUV hz hzV
  have hprodBase : w.prod φ = HNNExtension.of w.head := by
    simp [ReducedWord.prod, hnil]
  have hfhead : (F.comp HNNExtension.of) w.head = 1 := by
    have : F (HNNExtension.of w.head) = 1 := by
      rw [← hprodBase]
      exact hmap
    exact this
  have hhead : w.head = 1 := hbase (by simpa using hfhead)
  calc
    y = w.prod φ := hprod.symm
    _ = HNNExtension.of w.head := hprodBase
    _ = 1 := by simp [hhead]

/-- A two-domain form of `hom_injective_of_reducedWord_mapsTo`. -/
theorem hom_injective_of_reducedWord_mapsTo_pair
    (d : NormalWord.TransversalPair G A B)
    (F : HNNExtension G A B φ →* H)
    (hbase : Function.Injective (F.comp HNNExtension.of))
    (U V : Set X) (hU : U.Nonempty) (hV : V.Nonempty)
    (hUV : Disjoint U V)
    (hseparate : ∀ w : NormalWord d, w.toList ≠ [] →
      Set.MapsTo (fun z => F (w.prod φ) • z) U V ∨
        Set.MapsTo (fun z => F (w.prod φ) • z) V U) :
    Function.Injective F := by
  apply hom_injective_of_reducedWord_mapsTo (X := X) d F hbase
  intro w hw
  rcases hseparate w hw with h | h
  · exact ⟨U, V, hU, hUV, h⟩
  · exact ⟨V, U, hV, hUV.symm, h⟩

/-- A local HNN ping-pong criterion. Stable letters move complements between
the two domains, reduced base coefficients prepare the next stable letter,
and an endpoint set separates the resulting word from the identity. -/
theorem hom_injective_of_reducedWord_local_mapsTo
    (d : NormalWord.TransversalPair G A B)
    (F : HNNExtension G A B φ →* H)
    (hbaseInjective : Function.Injective (F.comp HNNExtension.of))
    (P : ℤˣ → Set X)
    (hstable : ∀ u : ℤˣ,
      Set.MapsTo (fun z => F (HNNExtension.t ^ (u : ℤ)) • z)
        (P (-u))ᶜ (P u))
    (hbase : ∀ (u v : ℤˣ) (g : G), g ∈ d.set u →
      (g ∈ toSubgroup A B u → u = v) →
        Set.MapsTo (fun z => F (HNNExtension.of g) • z)
          (P v) (P (-u))ᶜ)
    (hendpoint : ∀ (w : NormalWord d) (a : ℤˣ × G)
      (l : List (ℤˣ × G)), w.toList = a :: l →
        ∃ R : Set X, R.Nonempty ∧
          ReducedWord.LastBaseMapsOutside F P (a :: l) R ∧
          Disjoint R (F (HNNExtension.of w.head) • P a.1)) :
    Function.Injective F := by
  apply hom_injective_of_reducedWord_mapsTo (X := X) d F hbaseInjective
  intro w hw
  cases hlist : w.toList with
  | nil => exact (hw hlist).elim
  | cons a l =>
      obtain ⟨R, hR, hlast, hdis⟩ := hendpoint w a l hlist
      refine ⟨R, F (HNNExtension.of w.head) • P a.1, hR, hdis, ?_⟩
      have hchain : (a :: l).IsChain
          (fun x y => x.2 ∈ toSubgroup A B x.1 → x.1 = y.1) := by
        simpa only [hlist] using w.chain
      have hcoeff : ∀ x ∈ a :: l, x.2 ∈ d.set x.1 := by
        intro x hx
        exact w.mem_set x.1 x.2 (by simpa only [hlist] using hx)
      have htail := ReducedWord.stableTail_mapsTo F P
        (fun u g => g ∈ d.set u) hstable hbase
        a l hchain hcoeff R hlast
      intro z hz
      have hzTail := htail hz
      have hzTarget :
          F (HNNExtension.of w.head) •
              (F (ReducedWord.stableTailProd (φ := φ) (a :: l)) • z) ∈
            F (HNNExtension.of w.head) • P a.1 :=
        Set.smul_mem_smul_set hzTail
      simpa [ReducedWord.prod, ReducedWord.stableTailProd, hlist,
        map_mul, mul_smul] using hzTarget

end HNNExtension

open scoped MatrixGroups LinearAlgebra.Projectivization

namespace SystolicGrowth

noncomputable section

/-- The target interval for a positive stable letter and the source interval
for a negative stable letter. -/
def octagonHNNBoundarySet : ℤˣ → Set OctagonProjectiveBoundary := fun u =>
  if u = 1 then octagonHNNTargetBoundarySet else octagonHNNSourceBoundarySet

@[simp] lemma octagonHNNBoundarySet_one :
    octagonHNNBoundarySet 1 = octagonHNNTargetBoundarySet := rfl

@[simp] lemma octagonHNNBoundarySet_neg_one :
    octagonHNNBoundarySet (-1) = octagonHNNSourceBoundarySet := by
  simp [octagonHNNBoundarySet]

/-- The proved `C`-dynamics give both signed stable-letter hypotheses of the
generic HNN criterion. -/
lemma octagonHNNToPGL23_stable_maps_boundarySet (u : ℤˣ) :
    Set.MapsTo
      (fun p : OctagonProjectiveBoundary =>
        octagonHNNToPGL23 (HNNExtension.t ^ (u : ℤ)) • p)
      (octagonHNNBoundarySet (-u))ᶜ (octagonHNNBoundarySet u) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using octagonHNNToPGL23_t_maps_compl_sourceBoundary
  · simpa using octagonHNNToPGL23_t_inv_maps_compl_targetBoundary

/-- With the canonical exponent-zero transversal, only base-coefficient and
endpoint separation remain to prove faithfulness of the octagon HNN target. -/
theorem octagonHNNToPGL23_injective_of_exponentNormalWord_local_separation
    (hbase : ∀ (u v : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel →
      (g ∈ HNNExtension.toSubgroup
          octagonBaseSource octagonBaseTarget u → u = v) →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet v) (octagonHNNBoundarySet (-u))ᶜ)
    (hendpoint : ∀ (w : OctagonHNNExponentNormalWord)
      (a : ℤˣ × OctagonBaseGroup) (l : List (ℤˣ × OctagonBaseGroup)),
      w.toList = a :: l →
        ∃ R : Set OctagonProjectiveBoundary, R.Nonempty ∧
          HNNExtension.ReducedWord.LastBaseMapsOutside
            octagonHNNToPGL23 octagonHNNBoundarySet (a :: l) R ∧
          Disjoint R
            (octagonBaseToPGL23 w.head • octagonHNNBoundarySet a.1)) :
    Function.Injective octagonHNNToPGL23 := by
  apply HNNExtension.hom_injective_of_reducedWord_local_mapsTo
    octagonHNNExponentTransversalPair octagonHNNToPGL23
    (P := octagonHNNBoundarySet)
  · intro g h hgh
    apply octagonBaseToPGL23_injective
    simpa only [MonoidHom.comp_apply, octagonHNNToPGL23_of] using hgh
  · exact octagonHNNToPGL23_stable_maps_boundarySet
  · intro u v g hg hred
    have hg' : g ∈ octagonBaseExponentKernel := by
      change octagonBaseExponent g = 1
      change octagonBaseExponent g = 1 at hg
      exact hg
    simpa only [octagonHNNToPGL23_of] using hbase u v g hg' hred
  · intro w a l hlist
    obtain ⟨R, hR, hlast, hdis⟩ := hendpoint w a l hlist
    exact ⟨R, hR, hlast, by
      simpa only [octagonHNNToPGL23_of] using hdis⟩

/-- For exponent-zero coefficients, the reduced-chain condition splits into
cross-domain separation and nonidentity self-separation. -/
lemma octagonHNN_base_maps_of_cross_self
    (hcross : ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet (-u))ᶜ)
    (hself : ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel → g ≠ 1 →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet u)ᶜ) :
    ∀ (u v : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel →
      (g ∈ HNNExtension.toSubgroup
          octagonBaseSource octagonBaseTarget u → u = v) →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet v) (octagonHNNBoundarySet (-u))ᶜ := by
  intro u v g hg hred
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or v with rfl | rfl
  · exact hcross 1 g hg
  · apply hself (-1) g hg
    intro hgone
    subst g
    have h := hred (Subgroup.one_mem _)
    simp at h
  · apply hself 1 g hg
    intro hgone
    subst g
    have h := hred (Subgroup.one_mem _)
    simp at h
  · exact hcross (-1) g hg

/-- A geometric form of the canonical octagon HNN criterion. -/
theorem octagonHNNToPGL23_injective_of_cross_self_endpoint_separation
    (hcross : ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet (-u))ᶜ)
    (hself : ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel → g ≠ 1 →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet u)ᶜ)
    (hendpoint : ∀ (w : OctagonHNNExponentNormalWord)
      (a : ℤˣ × OctagonBaseGroup) (l : List (ℤˣ × OctagonBaseGroup)),
      w.toList = a :: l →
        ∃ R : Set OctagonProjectiveBoundary, R.Nonempty ∧
          HNNExtension.ReducedWord.LastBaseMapsOutside
            octagonHNNToPGL23 octagonHNNBoundarySet (a :: l) R ∧
          Disjoint R
            (octagonBaseToPGL23 w.head • octagonHNNBoundarySet a.1)) :
    Function.Injective octagonHNNToPGL23 := by
  apply octagonHNNToPGL23_injective_of_exponentNormalWord_local_separation
  · exact octagonHNN_base_maps_of_cross_self hcross hself
  · exact hendpoint

/-! ## Discharging the endpoint condition -/

/-- Every element of the source cyclic subgroup stabilizes the source
boundary interval. -/
lemma octagonBaseToPGL23_mem_sourceBoundary_stabilizer
    (g : OctagonBaseGroup) (hg : g ∈ octagonBaseSource) :
    octagonBaseToPGL23 g ∈
      MulAction.stabilizer (PGL(2, ℝ)) octagonHNNSourceBoundarySet := by
  rw [mem_octagonBaseSource_iff_eq_canonical_zpow] at hg
  rw [hg]
  apply MulAction.mem_stabilizer_set.mpr
  exact octagonBaseSourceElement_zpow_mem_sourceBoundary_iff _

/-- Every element of the target cyclic subgroup stabilizes the target
boundary interval. -/
lemma octagonBaseToPGL23_mem_targetBoundary_stabilizer
    (g : OctagonBaseGroup) (hg : g ∈ octagonBaseTarget) :
    octagonBaseToPGL23 g ∈
      MulAction.stabilizer (PGL(2, ℝ)) octagonHNNTargetBoundarySet := by
  rw [mem_octagonBaseTarget_iff_eq_canonical_zpow] at hg
  rw [hg]
  apply MulAction.mem_stabilizer_set.mpr
  exact octagonBaseTargetElement_zpow_mem_targetBoundary_iff _

/-- The subgroup associated to the opposite sign stabilizes the signed
boundary interval. -/
lemma octagonBaseToPGL23_toSubgroup_mem_boundary_stabilizer
    (u : ℤˣ) (g : OctagonBaseGroup)
    (hg : g ∈ HNNExtension.toSubgroup
      octagonBaseSource octagonBaseTarget (-u)) :
    octagonBaseToPGL23 g ∈
      MulAction.stabilizer (PGL(2, ℝ)) (octagonHNNBoundarySet u) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact octagonBaseToPGL23_mem_targetBoundary_stabilizer g hg
  · exact octagonBaseToPGL23_mem_sourceBoundary_stabilizer g hg

lemma octagonHNNBoundarySet_nonempty (u : ℤˣ) :
    (octagonHNNBoundarySet u).Nonempty := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact octagonHNNTargetBoundarySet_nonempty
  · exact octagonHNNSourceBoundarySet_nonempty

lemma octagonHNNBoundarySet_disjoint_neg (u : ℤˣ) :
    Disjoint (octagonHNNBoundarySet u) (octagonHNNBoundarySet (-u)) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact octagonHNNSourceBoundarySet_disjoint_target.symm
  · exact octagonHNNSourceBoundarySet_disjoint_target

/-- A neutral projective region outside both associated intervals. -/
def octagonHNNNeutralBoundarySet : Set OctagonProjectiveBoundary :=
  (octagonHNNSourceBoundarySet ∪ octagonHNNTargetBoundarySet)ᶜ

lemma octagonHNNNeutralBoundarySet_nonempty :
    octagonHNNNeutralBoundarySet.Nonempty := by
  let v : Fin 2 → ℝ := ![1, 0]
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num [v] at h0
  refine ⟨Projectivization.mk ℝ v hv, ?_⟩
  simp only [octagonHNNNeutralBoundarySet, Set.mem_compl_iff,
    Set.mem_union, not_or]
  constructor
  · rw [mem_octagonHNNSourceBoundarySet_mk_iff]
    simp [octagonHNNSourceBoundaryForm, v]
  · rw [mem_octagonHNNTargetBoundarySet_mk_iff]
    simp [octagonHNNTargetBoundaryForm, v]

lemma octagonHNNNeutralBoundarySet_disjoint (u : ℤˣ) :
    Disjoint octagonHNNNeutralBoundarySet (octagonHNNBoundarySet u) := by
  rw [Set.disjoint_left]
  intro p hp hpu
  change p ∉ octagonHNNSourceBoundarySet ∪
    octagonHNNTargetBoundarySet at hp
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact hp (Or.inr hpu)
  · exact hp (Or.inl hpu)

private lemma octagon_disjoint_smul_of_mapsTo_compl
    {g : PGL(2, ℝ)} {U V : Set OctagonProjectiveBoundary}
    (h : Set.MapsTo (fun p => g • p) U Vᶜ) :
    Disjoint V (g • U) := by
  rw [Set.disjoint_left]
  intro p hpV hpg
  obtain ⟨q, hq, rfl⟩ := Set.mem_smul_set.mp hpg
  exact h hq hpV

/-- Cross- and self-separation construct the endpoint set required by the
local normal-word criterion. -/
lemma octagonHNN_endpoint_separation_of_cross_self
    (hcross : ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet (-u))ᶜ)
    (hself : ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel → g ≠ 1 →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet u)ᶜ)
    (w : OctagonHNNExponentNormalWord)
    (a : ℤˣ × OctagonBaseGroup) (l : List (ℤˣ × OctagonBaseGroup))
    (hlist : w.toList = a :: l) :
    ∃ R : Set OctagonProjectiveBoundary, R.Nonempty ∧
      HNNExtension.ReducedWord.LastBaseMapsOutside
        octagonHNNToPGL23 octagonHNNBoundarySet (a :: l) R ∧
      Disjoint R
        (octagonBaseToPGL23 w.head • octagonHNNBoundarySet a.1) := by
  let hcomp : Subgroup.IsComplement
      (octagonBaseExponentKernel : Set OctagonBaseGroup)
      (HNNExtension.toSubgroup octagonBaseSource octagonBaseTarget (-a.1) :
        Set OctagonBaseGroup) := by
    rcases Int.units_eq_one_or a.1 with h | h
    · rw [h]
      simpa using octagonBaseExponentKernel_isComplement_target
    · rw [h]
      simpa using octagonBaseExponentKernel_isComplement_source
  let k : octagonBaseExponentKernel := (hcomp.equiv w.head).1
  let s : HNNExtension.toSubgroup
      octagonBaseSource octagonBaseTarget (-a.1) :=
    (hcomp.equiv w.head).2
  have hhead : (k : OctagonBaseGroup) * (s : OctagonBaseGroup) = w.head :=
    hcomp.equiv_fst_mul_equiv_snd w.head
  have hsStabilizes :=
    octagonBaseToPGL23_toSubgroup_mem_boundary_stabilizer
      a.1 (s : OctagonBaseGroup) s.2
  have hsSet : octagonBaseToPGL23 (s : OctagonBaseGroup) •
      octagonHNNBoundarySet a.1 = octagonHNNBoundarySet a.1 :=
    MulAction.mem_stabilizer_iff.mp hsStabilizes
  have hheadSet :
      octagonBaseToPGL23 w.head • octagonHNNBoundarySet a.1 =
        octagonBaseToPGL23 (k : OctagonBaseGroup) •
          octagonHNNBoundarySet a.1 := by
    rw [← hhead, map_mul, mul_smul, hsSet]
  let z : ℤˣ × OctagonBaseGroup := (a :: l).getLast (by simp)
  have hzList : z ∈ w.toList := by
    rw [hlist]
    exact List.getLast_mem _
  have hzKernel : z.2 ∈ octagonBaseExponentKernel := by
    have hz := w.mem_set z.1 z.2 hzList
    change octagonBaseExponent z.2 = 1
    change octagonBaseExponent z.2 = 1 at hz
    exact hz
  by_cases hv : z.1 = -a.1
  · refine ⟨octagonHNNBoundarySet z.1,
      octagonHNNBoundarySet_nonempty z.1, ?_, ?_⟩
    · apply (HNNExtension.ReducedWord.lastBaseMapsOutside_iff_getLast
        octagonHNNToPGL23 octagonHNNBoundarySet a l _).2
      simpa only [z, octagonHNNToPGL23_of] using hcross z.1 z.2 hzKernel
    · rw [hheadSet]
      have hm := hcross a.1 (k : OctagonBaseGroup) k.2
      have hd := octagon_disjoint_smul_of_mapsTo_compl hm
      simpa only [hv] using hd
  · have hva : z.1 = a.1 := by
      rcases Int.units_eq_one_or z.1 with hz | hz <;>
        rcases Int.units_eq_one_or a.1 with ha | ha
      · exact hz.trans ha.symm
      · exfalso
        apply hv
        rw [hz, ha]
        norm_num
      · exfalso
        apply hv
        rw [hz, ha]
      · exact hz.trans ha.symm
    by_cases hk : (k : OctagonBaseGroup) = 1
    · by_cases hz : z.2 = 1
      · refine ⟨octagonHNNNeutralBoundarySet,
          octagonHNNNeutralBoundarySet_nonempty, ?_, ?_⟩
        · apply (HNNExtension.ReducedWord.lastBaseMapsOutside_iff_getLast
            octagonHNNToPGL23 octagonHNNBoundarySet a l _).2
          intro p hp
          have hpnot : p ∉ octagonHNNBoundarySet (-z.1) :=
            Set.disjoint_left.mp
              (octagonHNNNeutralBoundarySet_disjoint (-z.1)) hp
          simpa only [z, hz, octagonHNNToPGL23_of, map_one, one_smul,
            Set.mem_compl_iff] using hpnot
        · rw [hheadSet, hk, map_one, one_smul, ← hva]
          exact octagonHNNNeutralBoundarySet_disjoint z.1
      · refine ⟨octagonHNNBoundarySet (-z.1),
          octagonHNNBoundarySet_nonempty (-z.1), ?_, ?_⟩
        · apply (HNNExtension.ReducedWord.lastBaseMapsOutside_iff_getLast
            octagonHNNToPGL23 octagonHNNBoundarySet a l _).2
          simpa only [z, octagonHNNToPGL23_of] using
            hself (-z.1) z.2 hzKernel hz
        · rw [hheadSet, hk, map_one, one_smul, ← hva]
          simpa only [neg_neg] using octagonHNNBoundarySet_disjoint_neg (-z.1)
    · refine ⟨octagonHNNBoundarySet z.1,
        octagonHNNBoundarySet_nonempty z.1, ?_, ?_⟩
      · apply (HNNExtension.ReducedWord.lastBaseMapsOutside_iff_getLast
          octagonHNNToPGL23 octagonHNNBoundarySet a l _).2
        simpa only [z, octagonHNNToPGL23_of] using hcross z.1 z.2 hzKernel
      · rw [hheadSet, ← hva]
        exact octagon_disjoint_smul_of_mapsTo_compl
          (hself z.1 (k : OctagonBaseGroup) k.2 hk)

/-- The remaining HNN faithfulness problem is exactly cross- and
self-separation for nontrivial exponent-zero base coefficients. -/
theorem octagonHNNToPGL23_injective_of_cross_self
    (hcross : ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet (-u))ᶜ)
    (hself : ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel → g ≠ 1 →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet u)ᶜ) :
    Function.Injective octagonHNNToPGL23 := by
  apply octagonHNNToPGL23_injective_of_cross_self_endpoint_separation
    hcross hself
  exact octagonHNN_endpoint_separation_of_cross_self hcross hself

/-- The same two concrete base-domain hypotheses imply faithfulness of the
projective octagon presentation. -/
theorem projectiveOctagonToPGL23_injective_of_cross_self
    (hcross : ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet (-u))ᶜ)
    (hself : ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel → g ≠ 1 →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet u)ᶜ) :
    Function.Injective projectiveOctagonToPGL23 := by
  rw [projectiveOctagonToPGL23_injective_iff_hnn]
  exact octagonHNNToPGL23_injective_of_cross_self hcross hself

/-- Direct normal-word boundary separation also suffices for octagon HNN
faithfulness. -/
theorem octagonHNNToPGL23_injective_of_normalWord_boundary_separation
    (d : HNNExtension.NormalWord.TransversalPair OctagonBaseGroup
      octagonBaseSource octagonBaseTarget)
    (hseparate : ∀ w : HNNExtension.NormalWord d, w.toList ≠ [] →
      ∃ U V : Set OctagonProjectiveBoundary,
        U.Nonempty ∧ Disjoint U V ∧
          Set.MapsTo
            (fun p => octagonHNNToPGL23
              (w.prod octagonBaseCyclicEquiv) • p) U V) :
    Function.Injective octagonHNNToPGL23 := by
  apply HNNExtension.hom_injective_of_reducedWord_mapsTo
    (X := OctagonProjectiveBoundary) d octagonHNNToPGL23
  · intro g h hg
    apply octagonBaseToPGL23_injective
    simpa only [MonoidHom.comp_apply, octagonHNNToPGL23_of] using hg
  · exact hseparate

/-- It is enough for every nonempty normal word to exchange the two fixed HNN
boundary intervals in one direction. -/
theorem octagonHNNToPGL23_injective_of_source_target_normalWord_separation
    (d : HNNExtension.NormalWord.TransversalPair OctagonBaseGroup
      octagonBaseSource octagonBaseTarget)
    (hseparate : ∀ w : HNNExtension.NormalWord d, w.toList ≠ [] →
      Set.MapsTo
          (fun p => octagonHNNToPGL23
            (w.prod octagonBaseCyclicEquiv) • p)
          octagonHNNSourceBoundarySet octagonHNNTargetBoundarySet ∨
        Set.MapsTo
          (fun p => octagonHNNToPGL23
            (w.prod octagonBaseCyclicEquiv) • p)
          octagonHNNTargetBoundarySet octagonHNNSourceBoundarySet) :
    Function.Injective octagonHNNToPGL23 := by
  apply HNNExtension.hom_injective_of_reducedWord_mapsTo_pair
    d octagonHNNToPGL23
    (U := octagonHNNSourceBoundarySet)
    (V := octagonHNNTargetBoundarySet)
  · intro g h hg
    apply octagonBaseToPGL23_injective
    simpa only [MonoidHom.comp_apply, octagonHNNToPGL23_of] using hg
  · exact octagonHNNSourceBoundarySet_nonempty
  · exact octagonHNNTargetBoundarySet_nonempty
  · exact octagonHNNSourceBoundarySet_disjoint_target
  · exact hseparate

end

end SystolicGrowth
