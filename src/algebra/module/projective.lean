/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import algebra.module.basic
import linear_algebra.finsupp
import linear_algebra.basis

/-!

# Projective modules

This file contains a definition of a projective module, the proof that
our definition is equivalent to a lifting property, and the
proof that all free modules are projective.

## Main definitions

Let `R` be a ring (or a semiring) and let `M` be an `R`-module (or a semimodule).

* `is_projective R M` : the proposition saying that `M` is a projective `R`-module.

## Main theorems

* `is_projective.lifting_property` : a map from a projective module can be lifted along
  a surjection.

* `is_projective.of_lifting_property` : If for all R-module surjections `A →ₗ B`, all
  maps `M →ₗ B` lift to `M →ₗ A`, then `M` is projective.

* `is_projective.of_free` : Free modules are projective

## Implementation notes

The actual definition of projective we use is that the natural R-module map
from the free R-module on the type M down to M splits. This is more convenient
than certain other definitions which involve quantifying over universes,
and also universe-polymorphic (the ring and module can be in different universes).

Everything works for semirings and semimodules except that apparently
we don't have free semimodules, so here we stick to rings.

`is_projective.of_lifting_property` is not universe polymorphic.

## References

https://en.wikipedia.org/wiki/Projective_module

## Tags

projective module

-/

universes u v

/- The actual implementation we choose: `M` is projective if the natural surjection
   from the free `R`-module on `M` to `M` splits. -/
/-- An R-module is projective if it is a direct summand of a free module, or equivalently
  if maps from the module lift along surjections. There are several other equivalent
  definitions. -/
def is_projective
  (R : Type u) [semiring R] (M : Type v) [add_comm_monoid M] [semimodule R M] : Prop :=
∃ s : M →ₗ[R] (M →₀ R), function.left_inverse (finsupp.total M M R id) s

namespace is_projective

section semiring

variables {R : Type u} [semiring R] {M : Type v} [add_comm_monoid M] [semimodule R M]
  {A : Type*} [add_comm_group A] [semimodule R A] {B : Type*} [add_comm_group B] [semimodule R B]

/-- A projective R-module has the property that maps from it lift along surjections. -/
theorem lifting_property (h : is_projective R M) (f : A →ₗ[R] B) (g : M →ₗ[R] B)
  (hf : function.surjective f) : ∃ (h : M →ₗ[R] A), f.comp h = g :=
begin
  /-
  Recall that `X →₀ R` is Lean's way of talking about the free `R`-module
  on a type `X`. The universal property `finsupp.total` says that to a map
  `X → A` from a type to an `R`-module, we get an associated R-module map
  `(X →₀ R) →ₗ A`. Apply this to a (noncomputable) map `M → A` coming from the map
  `M → B` and a random splitting of the surjection `A → B`, and we get
  a map `φ : (M →₀ R) →ₗ A`.
  -/
  let φ : (M →₀ R) →ₗ[R] A := finsupp.total _ _ _ (λ m, function.surj_inv hf (g m)),
  -- By projectivity we have a map `M →ₗ (M →₀ R)`;
  cases h with s hs,
  -- Compose to get `M →ₗ A`. This works.
  use φ.comp s,
  ext m,
  conv_rhs {rw ← hs m},
  simp [φ, finsupp.total_apply, function.surj_inv_eq hf],
end

/-- A module which satisfies the universal property is projective. Note that the universe variables
in `huniv` are somewhat restricted. -/
theorem of_lifting_property {R : Type u} [semiring R]
  {M : Type v} [add_comm_monoid M] [semimodule R M]
  -- If for all surjections of R-modules A →ₗ B, all maps M →ₗ B lift to M →ₗ A,
  (huniv : ∀ {A : Type (max v u)} {B : Type v} [add_comm_monoid A] [add_comm_monoid B],
    by exactI
    ∀ [semimodule R A] [semimodule R B],
    by exactI
    ∀ (f : A →ₗ[R] B) (g : M →ₗ[R] B),
  function.surjective f → ∃ (h : M →ₗ[R] A), f.comp h = g) :
  -- then M is projective.
  is_projective R M :=
begin
  -- let `s` be the universal map `(M →₀ R) →ₗ[R] M` coming from the identity map `M →ₗ[R] M`.
  obtain ⟨s, hs⟩ : ∃ (s : M →ₗ[R] M →₀ R),
    (finsupp.total M M R id).comp s = linear_map.id :=
    huniv (finsupp.total M M R (id : M → M)) (linear_map.id : M →ₗ[R] M) _,
  -- This `s` works.
  { use s,
    rwa linear_map.ext_iff at hs },
  { intro m,
    use finsupp.single m 1,
    simp },
end

end semiring

section ring

variables {R : Type u} [ring R] {M : Type v} [add_comm_group M] [module R M]

/-- Free modules are projective -/
theorem of_free {ι : Type*} {b : ι → M} (hb : is_basis R b) : is_projective R M :=
begin
  -- need M →ₗ[R] (M →₀ R) for definition of projective.
  -- get it from `ι → (M →₀ R)` coming from `b`.
  use hb.constr (λ i, finsupp.single (b i) 1),
  intro m,
  simp only [hb.constr_apply, mul_one, id.def, finsupp.smul_single', finsupp.total_single,
    linear_map.map_finsupp_sum],
  exact hb.total_repr m,
end

end ring

end is_projective
