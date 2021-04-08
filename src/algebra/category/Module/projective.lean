/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.projective
import algebra.category.Module.abelian
import linear_algebra.finsupp_vector_space

/-!
# The category of `R`-modules has enough projectives.
-/

universes v u

open category_theory
open category_theory.limits
open linear_map

namespace Module
variables {R : Type u} [ring R] {M : Module.{v} R}

/-- Modules that have a basis are projective. -/
lemma projective_of_free {ι : Type*} {v : ι → M} (hv : is_basis R v) : projective M :=
{ factors := begin
  introsI X E f e e_epi,
  have : ∀ i, ∃ x, e x = f (v i) := λ i, range_eq_top.1 (range_eq_top_of_epi e) (f (v i)),
  choose w h using this,
  exact ⟨hv.constr w, hv.ext (by simp [h])⟩
end }

/-- The category of modules has enough projectives, since every module is a quotient of a free
    module. -/
instance Module_enough_projectives : enough_projectives (Module.{u} R) :=
{ presentation :=
  λ M, have hb : is_basis R (λ m : M, finsupp.single m (1 : R)) := finsupp.is_basis_single_one,
  ⟨{ P := Module.of R (M →₀ R),
    projective := projective_of_free finsupp.is_basis_single_one,
    f := hb.constr id,
    epi := epi_of_range_eq_top _ (range_eq_top.2 (λ m, ⟨finsupp.single m (1 : R), by simp⟩)) }⟩, }

end Module
