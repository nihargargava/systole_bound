module

public import Geometry.TwoOpenCoverPathSubdivision
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

@[expose] public section

/-! Based-loop generation for an actual two-open-set cover. -/

open Set

namespace SystolicGrowth

noncomputable section

variable {X : Type*} [TopologicalSpace X]

private theorem loop_class_mem_inclusion_range {x : X} {U : Set X} (hx : x ∈ U)
    (p : Path x x) (hp : range p ⊆ U) :
    Path.Homotopic.Quotient.mk p ∈
      (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) ⟨x, hx⟩).range := by
  let q : Path (⟨x, hx⟩ : U) ⟨x, hx⟩ :=
    { toFun := fun t ↦ ⟨p t, hp ⟨t, rfl⟩⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  exact ⟨Path.Homotopic.Quotient.mk q, rfl⟩

private theorem lasso_concat_eq {x u v w : X} (a : Path x u) (p : Path u v)
    (b : Path x v) (r : Path v w) (c : Path x w) :
    Path.Homotopic.Quotient.mk ((a.trans (p.trans r)).trans c.symm) =
      (Path.Homotopic.Quotient.mk ((a.trans p).trans b.symm)).trans
        (Path.Homotopic.Quotient.mk ((b.trans r).trans c.symm)) := by
  simp only [Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.symm
    (Path.Homotopic.Quotient.mk b)) (Path.Homotopic.Quotient.mk b),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

private theorem lasso_concat_mem {x : X} (H : Subgroup (FundamentalGroup X x))
    {n : ℕ} (v : Fin (n + 1) → X)
    (F : (i : Fin n) → Path (v i.castSucc) (v i.succ))
    (q : (i : Fin (n + 1)) → Path x (v i))
    (h : ∀ i : Fin n,
      Path.Homotopic.Quotient.mk (((q i.castSucc).trans (F i)).trans (q i.succ).symm) ∈ H) :
    Path.Homotopic.Quotient.mk
      (((q 0).trans (Path.concat v F)).trans (q (Fin.last n)).symm) ∈ H := by
  induction n with
  | zero =>
    have heq : Path.Homotopic.Quotient.mk
        (((q 0).trans (Path.concat v F)).trans (q (Fin.last 0)).symm) =
        Path.Homotopic.Quotient.refl x := by
      simp [Path.concat_zero, Path.Homotopic.Quotient.mk_trans]
    rw [heq, ← FundamentalGroup.one_def]
    exact H.one_mem
  | succ n ih =>
    have hprefix := ih (v ∘ Fin.castSucc) (fun i ↦ F i.castSucc)
      (fun i ↦ q i.castSucc) (fun i ↦ h i.castSucc)
    have hlast := h (Fin.last n)
    have heq := lasso_concat_eq (q (Fin.castSucc 0))
      (Path.concat (v ∘ Fin.castSucc) (fun i ↦ F i.castSucc))
      (q (Fin.last n).castSucc) (F (Fin.last n)) (q (Fin.last n).succ)
    have hmul := H.mul_mem hlast hprefix
    change (Path.Homotopic.Quotient.mk
      (((q (Fin.castSucc 0)).trans (Path.concat (v ∘ Fin.castSucc) fun i ↦ F i.castSucc)).trans
        (q (Fin.last n).castSucc).symm)).trans
      (Path.Homotopic.Quotient.mk
        (((q (Fin.last n).castSucc).trans (F (Fin.last n))).trans
          (q (Fin.last n).succ).symm)) ∈ H at hmul
    rw [← heq] at hmul
    rw [Path.concat_succ]
    convert hmul using 1
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    rfl

private theorem exists_cover_connectors {x : X} {U V : Set X}
    (hcover : U ∪ V = univ) (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hUV : IsPathConnected (U ∩ V)) (hxU : x ∈ U) (hxV : x ∈ V) :
    ∀ y : X, ∃ q : Path x y,
      (y ∈ U → range q ⊆ U) ∧ (y ∈ V → range q ⊆ V) := by
  intro y
  by_cases hyU : y ∈ U
  · by_cases hyV : y ∈ V
    · let h := hUV.joinedIn x ⟨hxU, hxV⟩ y ⟨hyU, hyV⟩
      exact ⟨h.somePath, fun _ z ⟨t, ht⟩ ↦ ht ▸ (h.somePath_mem t).1,
        fun _ z ⟨t, ht⟩ ↦ ht ▸ (h.somePath_mem t).2⟩
    · let h := hU.joinedIn x hxU y hyU
      exact ⟨h.somePath, fun _ z ⟨t, ht⟩ ↦ ht ▸ h.somePath_mem t,
        fun hyV' ↦ (hyV hyV').elim⟩
  · have hyV : y ∈ V := by
      have hy : y ∈ U ∪ V := hcover.symm ▸ mem_univ y
      exact hy.resolve_left hyU
    let h := hV.joinedIn x hxV y hyV
    exact ⟨h.somePath, fun hyU' ↦ (hyU hyU').elim,
      fun _ z ⟨t, ht⟩ ↦ ht ▸ h.somePath_mem t⟩

private theorem connector_cast {x a b : X} (q : (y : X) → Path x y) (h : a = b) :
    q a = (q b).cast rfl h := by
  cases h
  rfl

/-- The actual side inclusions generate the based fundamental group of a two-open-set cover
whose sides and intersection are path connected. No restriction is imposed on the loops. -/
theorem fundamentalGroup_subgroup_eq_top_of_two_open_cover {x : X} {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hpcU : IsPathConnected U) (hpcV : IsPathConnected V)
    (hpcUV : IsPathConnected (U ∩ V)) (hxU : x ∈ U) (hxV : x ∈ V)
    (H : Subgroup (FundamentalGroup X x))
    (hUrange : (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) ⟨x, hxU⟩).range ≤ H)
    (hVrange : (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)) ⟨x, hxV⟩).range ≤ H) : H = ⊤ := by
  classical
  choose q hq using exists_cover_connectors hcover hpcU hpcV hpcUV hxU hxV
  apply (Subgroup.eq_top_iff' H).2
  intro α
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective α
  obtain ⟨n, _, t, ht0, ht1, _, hpieces⟩ :=
    exists_monotone_subpath_range_subset_two_open_cover p hU hV hcover
  let v := p ∘ t
  let F := fun i : Fin n ↦ p.subpath (t i.castSucc) (t i.succ)
  have hlocal : ∀ i : Fin n, Path.Homotopic.Quotient.mk
      (((q (v i.castSucc)).trans (F i)).trans (q (v i.succ)).symm) ∈ H := by
    intro i
    rcases hpieces i with hi | hi
    · have hstart : v i.castSucc ∈ U := hi (F i).source_mem_range
      have hend : v i.succ ∈ U := hi (F i).target_mem_range
      apply hUrange
      apply loop_class_mem_inclusion_range hxU
      rw [Path.trans_range, Path.trans_range, Path.symm_range]
      exact union_subset (union_subset ((hq _).1 hstart) hi) ((hq _).1 hend)
    · have hstart : v i.castSucc ∈ V := hi (F i).source_mem_range
      have hend : v i.succ ∈ V := hi (F i).target_mem_range
      apply hVrange
      apply loop_class_mem_inclusion_range hxV
      rw [Path.trans_range, Path.trans_range, Path.symm_range]
      exact union_subset (union_subset ((hq _).2 hstart) hi) ((hq _).2 hend)
  have hfull := lasso_concat_mem H v F (fun i ↦ q (v i)) hlocal
  have hhom := ((Path.Homotopic.refl (q (v 0))).hcomp
    (Path.Homotopic.concat_subpath p t)).hcomp
      (Path.Homotopic.refl (q (v (Fin.last n))).symm)
  have hsub : Path.Homotopic.Quotient.mk
      (((q (p (t 0))).trans (p.subpath (t 0) (t (Fin.last n)))).trans
        (q (p (t (Fin.last n)))).symm) ∈ H := by
    have heq := Path.Homotopic.Quotient.eq.2 hhom
    simpa only [v, F] using heq ▸ hfull
  rw [ht0, ht1, connector_cast q p.source, connector_cast q p.target,
    Path.subpath_zero_one] at hsub
  have hpath : (((q x).cast rfl p.source).trans (p.cast p.source p.target)).trans
      ((q x).cast rfl p.target).symm = ((q x).trans p).trans (q x).symm := by
    rfl
  rw [hpath] at hsub
  have hqx : Path.Homotopic.Quotient.mk (q x) ∈ H :=
    hUrange (loop_class_mem_inclusion_range hxU (q x) ((hq x).1 hxU))
  have hout := H.mul_mem (H.mul_mem hqx hsub) (H.inv_mem hqx)
  simp only [FundamentalGroup.mul_def, FundamentalGroup.inv_def,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl] at hout
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans] at hout
  exact hout

end

end SystolicGrowth
