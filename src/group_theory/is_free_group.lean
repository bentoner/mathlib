/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import group_theory.free_group
/-!
This file defines the universal property of free groups, and proves some things about
groups with this property. For an explicit construction of free groups, see
`group_theory/free_group`.
-/
noncomputable theory
universe u

/-- `is_free_group G` means that `G` has the universal property of a free group.
    That is, it has a family `generators G` of elements, such that a group homomorphism
    `G →* X` is uniquely determined by a function `generators G → X`. -/
class is_free_group (G) [group.{u} G] : Type (u+1) :=
(generators : Type u)
(of : generators → G)
(unique_lift : ∀ {X} [group.{u} X] (f : generators → X),
                ∃! F : G →* X, ∀ a, F (of a) = f a)

instance free_group_is_free_group {A} : is_free_group (free_group A) :=
{ generators := A,
  of := free_group.of,
  unique_lift := begin
    introsI X _ f,
    exact ⟨free_group.lift f,
      λ _, free_group.lift.of,
      λ g hg, monoid_hom.ext (λ _, free_group.lift.unique g hg)⟩
  end }

namespace is_free_group

variables {G H : Type u} [group G] [group H] [is_free_group G]

lemma end_is_id (f : G →* G) (h : ∀ a, f (of a) = of a) : ∀ g, f g = g :=
let ⟨_, _, u⟩ := unique_lift (f ∘ of) in
have claim : f = monoid_hom.id G := trans (u _ (λ _, rfl)) (u _ (by simp [h])).symm,
monoid_hom.ext_iff.mp claim

/-- Any free group is isomorphic to "the" free group. -/
def iso_free_group_of_is_free_group : G ≃* free_group (generators G) :=
let ⟨F, hF, uF⟩ := classical.indefinite_description _ (unique_lift free_group.of) in
{ to_fun := F,
  inv_fun := free_group.lift of,
  left_inv := end_is_id ((free_group.lift of).comp F) (by simp [hF]),
  right_inv := begin
    have : F.comp (free_group.lift of) = monoid_hom.id _,
    { apply free_group.ext_hom, simp [hF] },
    rwa monoid_hom.ext_iff at this,
  end,
  map_mul' := F.map_mul }

/-- Being a free group transports across group isomorphisms. -/
def of_mul_equiv (h : G ≃* H) : is_free_group H :=
{ generators := generators G,
  of := h ∘ of,
  unique_lift := begin
    introsI X _ f,
    rcases unique_lift f with ⟨F, hF, uF⟩,
    refine ⟨F.comp h.symm.to_monoid_hom, _, _⟩,
    { intro a, rw ←hF, apply congr_arg F,
      rw [function.comp_app, mul_equiv.coe_to_monoid_hom, mul_equiv.symm_apply_apply] },
    intros F' hF',
    suffices : F'.comp h.to_monoid_hom = F,
    { rw ←this, ext, apply congr_arg, symmetry, apply mul_equiv.apply_symm_apply },
    apply uF,
    apply hF',
  end }

end is_free_group
