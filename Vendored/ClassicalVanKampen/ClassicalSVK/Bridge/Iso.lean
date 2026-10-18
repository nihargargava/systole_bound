module

public import Vendored.ClassicalVanKampen.ClassicalSVK.Bridge.Naturality2

@[expose] public section

/-
Vendored from https://github.com/Arthur742Ramos/classical-svk-lean
Author: Arthur Freitas Ramos; copyright (c) 2026 Arthur Freitas Ramos.
Frozen commit: 874680e16db88b4a41daadf56eafbac79fd2f748
Original path: ClassicalSVK/Bridge/Iso.lean
License: Apache-2.0; complete text in ../LICENSE-APACHE-2.0
(relative to ClassicalSVK).
Local modifications: imports relocated; namespace isolated under
SystolicGrowth.Vendored.ClassicalVanKampen; compatibility with Lean/mathlib
v4.33.0-rc1. Existing frozen-source comments and proofs are preserved.
-/

namespace SystolicGrowth.Vendored.ClassicalVanKampen

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped FundamentalCategory

universe u

namespace ClassicalSVK

section
variable {X : Type u} [TopologicalSpace X]
local instance : Preorder X := universalPreorder X
local instance : DirectedSpace X := DirectedSpace.Preorder X
attribute [local instance] Path.Homotopic.setoid Dipath.Dihomotopic.setoid

lemma directedToClassical_comp_classicalToDirected :
    directedToClassical (X := X) ⋙ classicalToDirected (X := X) = 𝟭 (FundamentalCategory X) := by
  refine CategoryTheory.Functor.ext (fun x => rfl) ?_
  intro x y f
  simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact pathClassToDirectedClass_directedClassToPathClass f

lemma classicalToDirected_comp_directedToClassical :
    classicalToDirected (X := X) ⋙ directedToClassical (X := X) = 𝟭 (FundamentalGroupoid X) := by
  refine CategoryTheory.Functor.ext (fun x => rfl) ?_
  intro x y f
  simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact directedClassToPathClass_pathClassToDirectedClass f

end
end ClassicalSVK

end SystolicGrowth.Vendored.ClassicalVanKampen

