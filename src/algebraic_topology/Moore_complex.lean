/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebraic_topology.simplicial_object
import category_theory.abelian.basic
import category_theory.subobject
import algebra.homology.connective_chain_complex

universes v u

noncomputable theory

open category_theory category_theory.limits
open opposite

namespace algebraic_topology

variables {C : Type*} [category C] [abelian C]
local attribute [instance] abelian.has_pullbacks

instance : has_images C := by apply_instance

/-! The definitions in this namespace are all auxilliary definitions for `normalized_Moore_complex`
and should usually only be accessed via that. -/
namespace normalized_Moore_complex

open category_theory.subobject
variables (X : simplicial_object C)

/--
The normalized Moore complex in degree `n`, as a subobject of `X n`.
-/
@[simp]
def obj_X : Π n : ℕ, subobject (X.obj (op n))
| 0 := ⊤
| (n+1) := finset.univ.inf (λ k : fin (n+1), kernel_subobject (X.δ k.succ))

@[simp]
def obj_d : Π n : ℕ, (obj_X X (n+1) : C) ⟶ (obj_X X n : C)
| 0 := subobject.arrow _ ≫ X.δ (0 : fin 2) ≫ subobject.top_coe_iso_self.inv
| (n+1) :=
begin
  -- The differential is `subobject.arrow _ ≫ X.δ (0 : fin (n+3))`,
  -- factored through the intersection of the kernels.
  refine factor_thru _ (arrow _ ≫ X.δ (0 : fin (n+3))) _,
  -- We now need to show that it factors!
  -- A morphism factors through an intersection of subobjects if it factors through each.
  refine ((finset_inf_factors _).mpr (λ i m, _)),
  -- A morphism `f` factors through the kernel of `g` exactly if `f ≫ g = 0`.
  apply kernel_subobject_factors,
  -- Use a simplicial identity
  dsimp [obj_X],
  erw [category.assoc, ←X.δ_comp_δ (fin.zero_le i.succ), ←category.assoc],
  -- It's the first two factors which are zero.
  convert zero_comp,
  -- We can rewrite the arrow out of the intersection of all the kernels as a composition
  -- of a morphism we don't care about with the arrow out of the kernel of `X.δ i.succ.succ`.
  rw ←factor_thru_arrow _ _ (finset_inf_arrow_factors finset.univ _ i.succ (by simp)),
  -- It's the second two factors which are zero.
  rw [category.assoc],
  convert comp_zero,
  exact kernel_subobject_arrow_comp _,
end

lemma d_squared (n : ℕ) : obj_d X (n+1) ≫ obj_d X n = 0 :=
begin
  -- It's a pity we need to do a case split here;
  -- after the first simp the proofs are almost identical
  cases n; dsimp,
  { simp only [subobject.factor_thru_arrow_assoc],
    slice_lhs 2 3 { erw ←X.δ_comp_δ (fin.zero_le 0), },
    rw ←factor_thru_arrow _ _ (finset_inf_arrow_factors finset.univ _ (0 : fin 2) (by simp)),
    slice_lhs 2 3 { rw [kernel_subobject_arrow_comp], },
    simp, },
  { simp [factor_thru_right],
    slice_lhs 2 3 { erw ←X.δ_comp_δ (fin.zero_le 0), },
    rw ←factor_thru_arrow _ _ (finset_inf_arrow_factors finset.univ _ (0 : fin (n+3)) (by simp)),
    slice_lhs 2 3 { rw [kernel_subobject_arrow_comp], },
    simp, },
end

@[simps]
def obj : connective_chain_complex C :=
{ X := λ n, (obj_X X n : C), -- the coercion here picks a representative of the subobject
  d := obj_d X,
  d_squared' := d_squared X, }

variables {X} {Y : simplicial_object C} (f : X ⟶ Y)

@[simps]
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
{ f := λ n,
  begin
    refine factor_thru _ (arrow _ ≫ f.app (op n)) _,
    cases n; dsimp,
    { apply top_factors, },
    { refine (finset_inf_factors _).mpr (λ i m, _),
      apply kernel_subobject_factors,
      slice_lhs 2 3 { erw ←f.naturality, },
      rw ←factor_thru_arrow _ _ (finset_inf_arrow_factors finset.univ _ i (by simp)),
      slice_lhs 2 3 { erw [kernel_subobject_arrow_comp], },
      simp, }
  end,
  comm' := λ n,
  begin
    cases n; dsimp,
    { ext, simp, erw f.naturality, refl, },
    { ext, simp, erw f.naturality, refl, },
  end }

end normalized_Moore_complex

open normalized_Moore_complex

variables (C)

def normalized_Moore_complex : (simplicial_object C) ⥤ connective_chain_complex C :=
{ obj := obj,
  map := λ X Y f, map f,
  map_id' := λ X, by { ext n, cases n; simp, },
  map_comp' := λ X Y Z f g, by { ext n, cases n; simp, }, }

end algebraic_topology
