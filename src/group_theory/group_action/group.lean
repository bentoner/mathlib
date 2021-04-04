/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.group_action.defs
import algebra.group.units
import algebra.group_with_zero
import data.equiv.mul_add
import data.equiv.mul_add_aut
import group_theory.perm.basic

/-!
# Group actions applied to various types of group

This file contains lemmas about `smul` on `units`, `group_with_zero`, and `group`.
-/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

section mul_action

section units
variables [monoid α] [mul_action α β]

@[simp] lemma units.inv_smul_smul (u : units α) (x : β) :
  (↑u⁻¹:α) • (u:α) • x = x :=
by rw [smul_smul, u.inv_mul, one_smul]

@[simp] lemma units.smul_inv_smul (u : units α) (x : β) :
  (u:α) • (↑u⁻¹:α) • x = x :=
by rw [smul_smul, u.mul_inv, one_smul]

/-- If a monoid `α` acts on `β`, then each `u : units α` defines a permutation of `β`. -/
def units.smul_perm_hom : units α →* equiv.perm β :=
{ to_fun := λ u, ⟨λ x, (u:α) • x, λ x, (↑u⁻¹:α) • x, u.inv_smul_smul, u.smul_inv_smul⟩,
  map_one' := equiv.ext $ one_smul α,
  map_mul' := λ u₁ u₂, equiv.ext $ mul_smul (u₁:α) u₂ }

@[simp] lemma units.smul_left_cancel (u : units α) {x y : β} :
  (u:α) • x = (u:α) • y ↔ x = y :=
u.smul_perm_hom.apply_eq_iff_eq

lemma units.smul_eq_iff_eq_inv_smul (u : units α) {x y : β} :
  (u:α) • x = y ↔ x = (↑u⁻¹:α) • y :=
u.smul_perm_hom.apply_eq_iff_eq_symm_apply

lemma is_unit.smul_left_cancel {a : α} (ha : is_unit a) {x y : β} :
  a • x = a • y ↔ x = y :=
let ⟨u, hu⟩ := ha in hu ▸ u.smul_left_cancel

end units

section gwz
variables [group_with_zero α] [mul_action α β]

@[simp]
lemma inv_smul_smul' {c : α} (hc : c ≠ 0) (x : β) : c⁻¹ • c • x = x :=
(units.mk0 c hc).inv_smul_smul x

@[simp]
lemma smul_inv_smul' {c : α} (hc : c ≠ 0) (x : β) : c • c⁻¹ • x = x :=
(units.mk0 c hc).smul_inv_smul x

lemma inv_smul_eq_iff' {a : α} (ha : a ≠ 0) {x y : β} : a⁻¹ • x = y ↔ x = a • y :=
by { split; intro h, rw [← h, smul_inv_smul' ha], rw [h, inv_smul_smul' ha] }

lemma eq_inv_smul_iff' {a : α} (ha : a ≠ 0) {x y : β} : x = a⁻¹ • y ↔ a • x = y :=
by { split; intro h, rw [h, smul_inv_smul' ha], rw [← h, inv_smul_smul' ha] }

end gwz

section group
variables [group α] [mul_action α β]

@[simp] lemma inv_smul_smul (c : α) (x : β) : c⁻¹ • c • x = x :=
(to_units c).inv_smul_smul x

@[simp] lemma smul_inv_smul (c : α) (x : β) : c • c⁻¹ • x = x :=
(to_units c).smul_inv_smul x

lemma inv_smul_eq_iff {a : α} {x y : β} : a⁻¹ • x = y ↔ x = a • y :=
begin
  split;
  rintro rfl,
  {rw smul_inv_smul},
  {rw inv_smul_smul},
end

lemma eq_inv_smul_iff {a : α} {x y : β} : x = a⁻¹ • y ↔ a • x = y :=
begin
  split;
  rintro rfl,
  {rw smul_inv_smul},
  {rw inv_smul_smul},
end

variables (α) (β)

/-- Given an action of a group `α` on a set `β`, each `g : α` defines a permutation of `β`. -/
def mul_action.to_perm : α →* equiv.perm β :=
units.smul_perm_hom.comp to_units.to_monoid_hom

variables {α} {β}

protected lemma mul_action.bijective (g : α) : function.bijective (λ b : β, g • b) :=
(mul_action.to_perm α β g).bijective

end group

end mul_action

section distrib_mul_action
variables [monoid α] [add_monoid β] [distrib_mul_action α β]

theorem units.smul_eq_zero (u : units α) {x : β} : (u : α) • x = 0 ↔ x = 0 :=
⟨λ h, by rw [← u.inv_smul_smul x, h, smul_zero], λ h, h.symm ▸ smul_zero _⟩

theorem units.smul_ne_zero (u : units α) {x : β} : (u : α) • x ≠ 0 ↔ x ≠ 0 :=
not_congr u.smul_eq_zero

@[simp] theorem is_unit.smul_eq_zero {u : α} (hu : is_unit u) {x : β} :
  u • x = 0 ↔ x = 0 :=
exists.elim hu $ λ u hu, hu ▸ u.smul_eq_zero

end distrib_mul_action

section arrow

/-- If `G` acts on `A`, then it acts also on `A → B`, by `(g • F) a = F (g⁻¹ • a)`. -/
@[simps] def arrow_action {G A B : Type*} [group G] [mul_action G A] : mul_action G (A → B) :=
{ smul := λ g F a, F (g⁻¹ • a),
  one_smul := by simp only [one_inv, implies_true_iff, eq_self_iff_true, one_smul],
  mul_smul := by simp only [mul_smul, mul_inv_rev,
    forall_const, implies_true_iff, eq_self_iff_true] }

local attribute [instance] arrow_action

/-- Given groups `G H` with `G` acting on `A`, `G` acts by
  multiplicative automorphisms on `A → H`. -/
def mul_aut_arrow {G A H} [group G] [mul_action G A] [group H] : G →* mul_aut (A → H) :=
{ to_fun := λ g,
  { to_fun := λ F, g • F,
    inv_fun := λ F, g⁻¹ • F,
    left_inv := λ F, inv_smul_smul g F,
    right_inv := λ F, smul_inv_smul g F,
    map_mul' := by { intros, funext, simp only [arrow_action_to_has_scalar_smul, pi.mul_apply] } },
  map_one' := by { ext, simp only [mul_aut.one_apply, mul_equiv.coe_mk, one_smul] },
  map_mul' := by { intros, ext, simp only [mul_smul, mul_equiv.coe_mk, mul_aut.mul_apply] } }

@[simp] lemma mul_aut_arrow_apply {G A H : Type*} [group G] [mul_action G A] [group H]
  (g : G) (F : A → H) (a : A) : mul_aut_arrow g F a = F (g⁻¹ • a) := rfl

end arrow
