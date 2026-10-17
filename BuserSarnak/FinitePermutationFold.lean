module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# Separating interleaved permutation products

An ordered family of local rotations can be moved to the left of the edge
factors when each earlier edge factor commutes with each later rotation.
The statement holds in any monoid and does not require the rotations to
commute with one another.
-/

namespace SystolicGrowth

/-- Separate an interleaved fold into a rotation fold and an edge-factor fold.
Only the commutations actually needed to preserve the original order are
assumed. -/
theorem foldl_interleaved_eq_split {G E : Type*} [Monoid G]
    (l : List E) (rho tau chi : E → G) (rho0 tau0 : G)
    (hinit : ∀ f ∈ l, Commute tau0 (rho f))
    (hcross : l.Pairwise (fun e f => Commute (tau e * chi e) (rho f))) :
    l.foldl (fun π e => π * (rho e * tau e) * chi e) (rho0 * tau0) =
      l.foldl (fun π e => π * rho e) rho0 *
        l.foldl (fun π e => π * tau e * chi e) tau0 := by
  induction l generalizing rho0 tau0 with
  | nil => rfl
  | cons e l ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hcross
      have hstart : (rho0 * tau0) * (rho e * tau e) * chi e =
          (rho0 * rho e) * (tau0 * tau e * chi e) := by
        calc
          _ = rho0 * (tau0 * rho e) * tau e * chi e := by simp only [mul_assoc]
          _ = rho0 * (rho e * tau0) * tau e * chi e := by
            rw [(hinit e List.mem_cons_self).eq]
          _ = _ := by simp only [mul_assoc]
      have hinit' : ∀ f ∈ l, Commute (tau0 * tau e * chi e) (rho f) := by
        intro f hf
        simpa only [mul_assoc] using
          (hinit f (List.mem_cons_of_mem e hf)).mul_left (hhead f hf)
      simpa only [List.foldl_cons, hstart] using
        ih (rho0 * rho e) (tau0 * tau e * chi e) hinit' htail

#print axioms foldl_interleaved_eq_split

end SystolicGrowth
