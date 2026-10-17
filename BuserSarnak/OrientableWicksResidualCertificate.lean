module

public import BuserSarnak.OrientableWicksHandleChoice
public import BuserSarnak.FiniteHandleSurgery
public import BuserSarnak.FiniteHandleAlphabet

@[expose] public section

/-!
# The residual certificate of a crossing-handle surgery

The residual alphabet removes the two crossing labels, while its literal
word has exactly the order `B₁ C₂ A C₁ B₂`. Signed occurrences and vertex
dynamics are transported without forgetting positions or using free
reduction. The resulting one-vertex certificate follows from the exact
first-return surgery law, rather than being supplied as a residual input.
-/

namespace SystolicGrowth

noncomputable section

/-- The physical signed-letter partner preserves its label and flips its sign. -/
def signedLetterPartnerPerm (X : Type*) : Equiv.Perm (X × Bool) where
  toFun := fun letter => (letter.1, !letter.2)
  invFun := fun letter => (letter.1, !letter.2)
  left_inv := by rintro ⟨x, sign⟩; cases sign <;> rfl
  right_inv := by rintro ⟨x, sign⟩; cases sign <;> rfl

@[simp] theorem signedLetterPartnerPerm_apply {X : Type*} (letter : X × Bool) :
    signedLetterPartnerPerm X letter = (letter.1, !letter.2) := rfl

namespace OrientableWicksCertificate

variable {X : Type*} [Fintype X] {w : SignedWord X}

/-- Every signed letter occurs in the literal word. -/
theorem literal_get_surjective (C : OrientableWicksCertificate w) :
    Function.Surjective w.get := by
  rintro ⟨x, sign⟩
  cases sign
  · exact ⟨C.negative x, C.negative_spec x⟩
  · exact ⟨C.positive x, C.positive_spec x⟩

/-- Literal positions and physical signed letters are equivalent. -/
def literalEquiv (C : OrientableWicksCertificate w) : Fin w.length ≃ X × Bool :=
  Equiv.ofBijective w.get ⟨C.literal_get_injective, C.literal_get_surjective⟩

@[simp] theorem literalEquiv_apply (C : OrientableWicksCertificate w)
    (i : Fin w.length) : C.literalEquiv i = w.get i := rfl

/-- The actual signed-letter vertex permutation is transitive. -/
theorem literal_vertex_one_orbit [DecidableEq X] (C : OrientableWicksCertificate w) :
    ∀ u v : X × Bool, ∃ n : ℕ,
      (w.formPerm * signedLetterPartnerPerm X)^[n] u = v := by
  apply one_orbit_of_conjugate C.rotation
    (w.formPerm * signedLetterPartnerPerm X) C.literalEquiv
  · intro i
    change w.get (C.rotation i) =
      w.formPerm (signedLetterPartnerPerm X (w.get i))
    rw [C.rotation_eq, ← list_formPerm_apply_cyclic_get w C.literal_nodup,
      C.partner_spec]
    rfl
  · exact C.one_orbit

end OrientableWicksCertificate

/-- An exhaustive nodup signed inventory with the actual physical vertex
orbit constructs a Wicks certificate. The residual use below derives this
physical orbit from the old certificate's first return. -/
def wicksCertificateOfPhysicalOrbit {X : Type*} [Fintype X] [DecidableEq X]
    (word : SignedWord X) (hn : word.Nodup)
    (hfull : ∀ letter : X × Bool, letter ∈ word)
    (horbit : ∀ u v : X × Bool, ∃ n : ℕ,
      (word.formPerm * signedLetterPartnerPerm X)^[n] u = v) :
    OrientableWicksCertificate word := by
  let e : Fin word.length ≃ X × Bool := Equiv.ofBijective word.get
    ⟨List.nodup_iff_injective_get.mp hn, fun letter => by
      obtain ⟨k, hk, hget⟩ := List.getElem_of_mem (hfull letter)
      exact ⟨⟨k, hk⟩, hget⟩⟩
  let partner : Fin word.length → Fin word.length :=
    fun i => e.symm (signedLetterPartnerPerm X (e i))
  let rotation : Fin word.length → Fin word.length :=
    fun i => cyclicSucc (partner i)
  have hpartner : ∀ i, word.get (partner i) = ((word.get i).1, !(word.get i).2) := by
    intro i
    exact e.apply_symm_apply _
  have hcommute : ∀ i, e (rotation i) =
      (word.formPerm * signedLetterPartnerPerm X) (e i) := by
    intro i
    change word.get (cyclicSucc (partner i)) =
      word.formPerm (signedLetterPartnerPerm X (word.get i))
    rw [← list_formPerm_apply_cyclic_get word hn, hpartner]
    rfl
  have hrotation : ∀ i j, ∃ n : ℕ, rotation^[n] i = j := by
    intro i j
    obtain ⟨n, hn⟩ := horbit (e i) (e j)
    refine ⟨n, e.injective ?_⟩
    exact ((show Function.Semiconj e rotation
      (word.formPerm * signedLetterPartnerPerm X) from hcommute).iterate_right n i).trans hn
  refine
    { positive := fun x => e.symm (x, true)
      negative := fun x => e.symm (x, false)
      positive_spec := fun x => e.apply_symm_apply (x, true)
      negative_spec := fun x => e.apply_symm_apply (x, false)
      exhaustive := ?_
      partner := partner
      partner_spec := hpartner
      rotation := rotation
      rotation_eq := fun _ => rfl
      one_orbit := hrotation }
  intro i
  cases hsign : (word.get i).2
  · right
    apply e.injective
    rw [e.apply_symm_apply]
    change word.get i = ((word.get i).1, false)
    exact Prod.ext rfl hsign
  · left
    apply e.injective
    rw [e.apply_symm_apply]
    change word.get i = ((word.get i).1, true)
    exact Prod.ext rfl hsign

/-- The residual alphabet deletes exactly the two extracted handle labels. -/
abbrev WicksResidualAlphabet {X : Type*} (x y : X) := HandleRemainingAlphabet x y

/-- Forget only the subtype proof; retain the physical signed occurrence. -/
def wicksResidualSignedProjection {X : Type*} (x y : X) :
    WicksResidualAlphabet x y × Bool → X × Bool :=
  fun letter => (letter.1.val, letter.2)

theorem wicksResidualSignedProjection_injective {X : Type*} (x y : X) :
    Function.Injective (wicksResidualSignedProjection x y) := by
  intro u v h
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst h)
  · exact congrArg (fun letter : X × Bool => letter.2) h

/-- Lift an avoiding raw signed word to the smaller alphabet, preserving
both literal order and every orientation bit. -/
def wicksResidualSignedWord {X : Type*} (x y : X) (raw : SignedWord X)
    (h : ∀ letter ∈ raw, letter.1 ≠ x ∧ letter.1 ≠ y) :
    SignedWord (WicksResidualAlphabet x y) :=
  raw.pmap (fun letter hl => (⟨letter.1, hl⟩, letter.2)) h

/-- Projection of the lifted word is the exact raw list, not a reduced word. -/
@[simp] theorem wicksResidualSignedWord_projection {X : Type*} (x y : X)
    (raw : SignedWord X) (h : ∀ letter ∈ raw, letter.1 ≠ x ∧ letter.1 ≠ y) :
    (wicksResidualSignedWord x y raw h).map (wicksResidualSignedProjection x y) = raw := by
  simp only [wicksResidualSignedWord, wicksResidualSignedProjection,
    List.map_pmap, Prod.mk.eta, List.pmap_eq_map]
  exact List.map_id _

section ResidualLetters

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
/-- Removing both signs of each marked label is equivalent to removing the labels. -/
theorem crossingHandle_signed_retained_iff (x y : X) (sx sy : Bool) (letter : X × Bool) :
    crossingHandleRetained (x, sx) (y, sy) (x, !sx) (y, !sy) letter ↔
      letter.1 ≠ x ∧ letter.1 ≠ y := by
  rcases letter with ⟨z, sign⟩
  cases sign <;> cases sx <;> cases sy <;>
    simp [crossingHandleRetained, Prod.mk.injEq, and_comm]

/-- The signed smaller alphabet is precisely the retained physical signed set. -/
def wicksResidualSignedEquiv (x y : X) (sx sy : Bool) :
    WicksResidualAlphabet x y × Bool ≃
      {letter : X × Bool //
        crossingHandleRetained (x, sx) (y, sy) (x, !sx) (y, !sy) letter} where
  toFun := fun letter => ⟨wicksResidualSignedProjection x y letter,
    (crossingHandle_signed_retained_iff x y sx sy _).mpr letter.1.property⟩
  invFun := fun letter =>
    (⟨letter.val.1, (crossingHandle_signed_retained_iff x y sx sy _).mp letter.property⟩,
      letter.val.2)
  left_inv := by intro letter; rfl
  right_inv := by intro letter; rfl

omit [DecidableEq X] in
/-- The residual alphabet loses exactly two generators. -/
theorem wicksResidualAlphabet_card (x y : X) (hxy : x ≠ y) :
    Fintype.card (WicksResidualAlphabet x y) = Fintype.card X - 2 :=
  handleRemainingAlphabet_card_eq_sub_two x y hxy

theorem Internal.OrientableWicksResidualCertificateHelpers.formPerm_map_apply_of_mem {A B : Type*}
    [DecidableEq A] [DecidableEq B] (f : A → B) (hf : Function.Injective f)
    (l : List A) (hn : l.Nodup) (x : A) (hx : x ∈ l) :
    (l.map f).formPerm (f x) = f (l.formPerm x) := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  rw [List.formPerm_apply_getElem l hn k hk]
  have hmap := List.formPerm_apply_getElem (l.map f) (List.Nodup.map hf hn) k
    (by simpa only [List.length_map] using hk)
  simpa only [List.getElem_map, List.length_map] using hmap

namespace OrientableWicksCertificate

variable {w : SignedWord X}

omit [DecidableEq X] in
theorem Internal.OrientableWicksResidualCertificateHelpers.residual_blocks_avoid (C : OrientableWicksCertificate w)
    (x y : X) (sx sy : Bool) (A B₁ B₂ C₁ C₂ : SignedWord X)
    (hsplit : w = A ++ (x, sx) :: (B₁ ++ (y, sy) ::
      (B₂ ++ (x, !sx) :: (C₁ ++ (y, !sy) :: C₂)))) :
    ∀ letter ∈ crossingHandleResidual A B₁ B₂ C₁ C₂,
      letter.1 ≠ x ∧ letter.1 ≠ y := by
  intro letter hletter
  apply C.blocks_avoid_crossing_labels x y sx sy A B₁ B₂ C₁ C₂ hsplit letter
  simpa only [crossingHandleResidual, List.mem_append, or_assoc, or_comm, or_left_comm]
    using hletter

/-- The literal residual is lifted to the smaller alphabet in its precise
handle-surgery order, with its original signs unchanged. -/
def crossingHandleResidualWord (C : OrientableWicksCertificate w)
    (x y : X) (sx sy : Bool) (A B₁ B₂ C₁ C₂ : SignedWord X)
    (hsplit : w = A ++ (x, sx) :: (B₁ ++ (y, sy) ::
      (B₂ ++ (x, !sx) :: (C₁ ++ (y, !sy) :: C₂)))) :
    SignedWord (WicksResidualAlphabet x y) :=
  wicksResidualSignedWord x y (crossingHandleResidual A B₁ B₂ C₁ C₂)
    (Internal.OrientableWicksResidualCertificateHelpers.residual_blocks_avoid C x y sx sy A B₁ B₂ C₁ C₂ hsplit)

omit [DecidableEq X] in
/-- The residual word projects to the exact new raw cyclic order. -/
@[simp] theorem crossingHandleResidualWord_projection (C : OrientableWicksCertificate w)
    (x y : X) (sx sy : Bool) (A B₁ B₂ C₁ C₂ : SignedWord X)
    (hsplit : w = A ++ (x, sx) :: (B₁ ++ (y, sy) ::
      (B₂ ++ (x, !sx) :: (C₁ ++ (y, !sy) :: C₂)))) :
    (C.crossingHandleResidualWord x y sx sy A B₁ B₂ C₁ C₂ hsplit).map
      (wicksResidualSignedProjection x y) = crossingHandleResidual A B₁ B₂ C₁ C₂ :=
  wicksResidualSignedWord_projection _ _ _ _

/-- Every field of the residual one-vertex certificate is constructed from
the old certificate and the literal crossing split. Its vertex orbit is the
old vertex permutation's exact positive first return. -/
def crossingHandleResidualWicksCertificate (C : OrientableWicksCertificate w)
    (x y : X) (_hxy : x ≠ y) (sx sy : Bool) (A B₁ B₂ C₁ C₂ : SignedWord X)
    (hsplit : w = A ++ (x, sx) :: (B₁ ++ (y, sy) ::
      (B₂ ++ (x, !sx) :: (C₁ ++ (y, !sy) :: C₂)))) :
    OrientableWicksCertificate
      (C.crossingHandleResidualWord x y sx sy A B₁ B₂ C₁ C₂ hsplit) := by
  let raw := crossingHandleResidual A B₁ B₂ C₁ C₂
  let lifted := C.crossingHandleResidualWord x y sx sy A B₁ B₂ C₁ C₂ hsplit
  let P : X × Bool → Prop :=
    crossingHandleRetained (x, sx) (y, sy) (x, !sx) (y, !sy)
  let partner := signedLetterPartnerPerm X
  let oldVertex := w.formPerm * partner
  let e := wicksResidualSignedEquiv x y sx sy
  have hword : w = crossingHandleOriginal A B₁ B₂ C₁ C₂
      (x, sx) (y, sy) (x, !sx) (y, !sy) := by
    simpa only [crossingHandleOriginal, List.cons_append, List.singleton_append,
      List.append_assoc, List.nil_append] using hsplit
  have hblocks : ∀ letter ∈ A ++ B₁ ++ B₂ ++ C₁ ++ C₂, P letter := by
    intro letter hletter
    exact (crossingHandle_signed_retained_iff x y sx sy letter).mpr
      (C.blocks_avoid_crossing_labels x y sx sy A B₁ B₂ C₁ C₂ hsplit letter hletter)
  have hfilter : (crossingHandleAugmented A B₁ B₂ C₁ C₂
      (x, sx) (y, sy) (x, !sx) (y, !sy)).filter (fun letter => decide (P letter)) = raw :=
    crossingHandleAugmented_filter _ _ _ _ _ _ _ _ _ hblocks
  have hnraw : raw.Nodup := by
    rw [← hfilter]
    exact (crossingHandleAugmented_nodup _ _ _ _ _ _ _ _ _
      (hword ▸ C.literal_nodup)).filter _
  have hprojection : lifted.map (wicksResidualSignedProjection x y) = raw :=
    C.crossingHandleResidualWord_projection x y sx sy A B₁ B₂ C₁ C₂ hsplit
  have hnlifted : lifted.Nodup := List.Nodup.of_map _ (hprojection ▸ hnraw)
  have hfullraw : ∀ letter : X × Bool, P letter → letter ∈ raw := by
    intro letter hletter
    rw [← hfilter]
    apply List.mem_filter.mpr
    refine ⟨?_, decide_eq_true hletter⟩
    apply (crossingHandleAugmented_perm A B₁ B₂ C₁ C₂
      (x, sx) (y, sy) (x, !sx) (y, !sy)).mem_iff.mpr
    rw [← hword]
    obtain ⟨i, hi⟩ := C.literal_get_surjective letter
    exact hi ▸ List.get_mem w i
  have hfull : ∀ letter : WicksResidualAlphabet x y × Bool, letter ∈ lifted := by
    intro letter
    have hmem : wicksResidualSignedProjection x y letter ∈
        lifted.map (wicksResidualSignedProjection x y) := by
      rw [hprojection]
      exact hfullraw _ (e letter).property
    obtain ⟨other, hother, heq⟩ := List.mem_map.mp hmem
    exact wicksResidualSignedProjection_injective x y heq ▸ hother
  have hphysical : ∀ letter : WicksResidualAlphabet x y × Bool,
      e ((lifted.formPerm * signedLetterPartnerPerm (WicksResidualAlphabet x y)) letter) =
        finitePermutationFirstReturn oldVertex P (e letter) := by
    intro letter
    apply Subtype.ext
    change wicksResidualSignedProjection x y
        (lifted.formPerm (signedLetterPartnerPerm (WicksResidualAlphabet x y) letter)) =
      (finitePermutationFirstReturn oldVertex P (e letter)).val
    rw [← Internal.OrientableWicksResidualCertificateHelpers.formPerm_map_apply_of_mem (wicksResidualSignedProjection x y)
      (wicksResidualSignedProjection_injective x y) lifted hnlifted _ (hfull _), hprojection]
    change raw.formPerm (partner (e letter).val) = _
    have hsurgery := crossingHandleResidual_vertex_firstReturn A B₁ B₂ C₁ C₂
      (x, sx) (y, sy) (x, !sx) (y, !sy) (hword ▸ C.literal_nodup) hblocks partner
      (by rfl) (by rfl) (by simp [partner]) (by simp [partner]) (e letter)
    simpa only [← hword] using hsurgery
  have hreturnOrbit : ∀ u v : {letter : X × Bool // P letter}, ∃ n : ℕ,
      (finitePermutationFirstReturn oldVertex P)^[n] u = v :=
    finitePermutationFirstReturn_one_orbit oldVertex P C.literal_vertex_one_orbit
  have horbit : ∀ u v : WicksResidualAlphabet x y × Bool, ∃ n : ℕ,
      (lifted.formPerm * signedLetterPartnerPerm (WicksResidualAlphabet x y))^[n] u = v := by
    apply one_orbit_of_conjugate (finitePermutationFirstReturn oldVertex P)
      (lifted.formPerm * signedLetterPartnerPerm (WicksResidualAlphabet x y)) e.symm
    · intro letter
      apply e.injective
      rw [e.apply_symm_apply, hphysical, e.apply_symm_apply]
    · exact hreturnOrbit
  exact wicksCertificateOfPhysicalOrbit lifted hnlifted hfull horbit

end OrientableWicksCertificate

end ResidualLetters

end

end SystolicGrowth

#print axioms SystolicGrowth.OrientableWicksCertificate.literal_vertex_one_orbit
#print axioms SystolicGrowth.wicksCertificateOfPhysicalOrbit
#print axioms SystolicGrowth.wicksResidualSignedWord_projection
#print axioms SystolicGrowth.wicksResidualAlphabet_card
#print axioms SystolicGrowth.OrientableWicksCertificate.crossingHandleResidualWicksCertificate
