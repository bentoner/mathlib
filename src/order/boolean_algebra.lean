/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import order.bounded_lattice
/-!
# (Generalized) Boolean algebras

A generalized Boolean algebra is a distributive lattice admitting a relative complement operator,
written using "set difference" notation `x \ y`.

A Boolean algebra is a bounded distributive lattice with a complement operator. Boolean algebras
generalize the (classical) logic of propositions and the lattice of subsets of a set.

For convenience, the `boolean_algebra` type class is also bundled with a set difference operator
`sdiff`, written `\`.

## Main declarations

* `has_compl`: a type class for the complement operator
* `boolean_algebra`: a type class for Boolean algebras
* `boolean_algebra_Prop`: the Boolean algebra instance on `Prop`

## Notations

* `xᶜ` is notation for `compl x`
* `x \ y` is notation for `sdiff x y`.

## Tags

Boolean algebras, lattices

-/
set_option old_structure_cmd true

universes u v
variables {α : Type u} {w x y z : α}

/-!
### Generalized Boolean algebras
-/

/-- A generalized Boolean algebra is a distributive lattice with `⊥`
and a set difference operation `\` satisfying `(a ⊓ b) ⊔ (a \ b) = a`
and `(a ⊓ b) ⊓ (a \ b) = b`, i.e. `a \ b` is the complement of `b` in
`a`.

This is a generalization of Boolean algebras which applies to `finset α`
for arbitrary (not-necessarily-`fintype`) `α`. -/
class generalized_boolean_algebra α extends distrib_lattice α, order_bot α, has_sdiff α :=
(sup_inf_sdiff : ∀a b:α, (a ⊓ b) ⊔ (a \ b) = a)
(inf_inf_sdiff : ∀a b:α, (a ⊓ b) ⊓ (a \ b) = ⊥)

-- TODO: do we want a `is_compl_of` predicate generalizing `is_compl`?

section generalized_boolean_algebra
variables [generalized_boolean_algebra α]

namespace generalized_boolean_algebra

@[priority 100]
instance : semilattice_sup_bot α := { .. (infer_instance : generalized_boolean_algebra α) }
@[priority 100]
instance : semilattice_inf_bot α := { .. (infer_instance : generalized_boolean_algebra α) }

end generalized_boolean_algebra

theorem sup_inf_sdiff (x y : α) : (x ⊓ y) ⊔ (x \ y) = x :=
generalized_boolean_algebra.sup_inf_sdiff _ _
theorem inf_inf_sdiff (x y : α) : (x ⊓ y) ⊓ (x \ y) = ⊥ :=
generalized_boolean_algebra.inf_inf_sdiff _ _

-- TODO: in distributive lattices, relative complements are unique when they exist
theorem sdiff_unique (s : (x ⊓ y) ⊔ z = x) (i : (x ⊓ y) ⊓ z = ⊥) : x \ y = z :=
begin
  conv_rhs at s { rw [←sup_inf_sdiff x y, sup_comm] },
  conv_rhs at i { rw [←inf_inf_sdiff x y, inf_comm] },
  rw [sup_comm] at s,
  rw [inf_comm] at i,
  exact (eq_of_inf_eq_sup_eq i s).symm,
end

theorem sup_sdiff_same : x ⊔ (y \ x) = x ⊔ y :=
begin
  conv_rhs { congr, skip, rw [←sup_inf_sdiff y x], },
  rw [sup_inf_right, inf_sup_left],
  sorry
end

theorem inf_sdiff_same : x ⊓ (y \ x) = ⊥ := sorry
theorem sdiff_inf_same : (y \ x) ⊓ x = ⊥ := by rw [inf_comm, inf_sdiff_same]

theorem le_sup_sdiff : x ≤ y ⊔ (x \ y) :=
by rw [←left_eq_inf, sup_sdiff_same, sup_comm, inf_sup_self]

lemma sup_sdiff_left : x ⊔ (x \ y) = x :=
begin
  conv_rhs { rw [←sup_inf_sdiff x y, sup_inf_right] },
  sorry
end

theorem sdiff_eq_left (h : x ⊓ y = ⊥) : x \ y = x :=
by conv_rhs { rw [←sup_inf_sdiff x y, h, bot_sup_eq] }

@[simp] theorem sdiff_bot : x \ ⊥ = x := sdiff_eq_left inf_bot_eq

theorem sdiff_le_sdiff (h₁ : w ≤ y) (h₂ : z ≤ x) : w \ x ≤ y \ z :=
sorry
-- by rw [sdiff_eq, sdiff_eq]; from inf_le_inf h₁ (compl_le_compl h₂)

lemma sdiff_idem_left : x \ (x \ y) = y := sorry

@[simp] lemma sdiff_idem_right : x \ y \ y = x \ y :=
sorry
-- by rw [sdiff_eq, sdiff_eq, inf_assoc, inf_idem]

lemma sdiff_sdiff_sup_sdiff : z \ (x \ y ⊔ y \ x) = (z \ x ⊔ y) ⊓ (z \ y ⊔ x) := sorry

end generalized_boolean_algebra

/-!
### Boolean algebras
-/


/-- Set / lattice complement -/
class has_compl (α : Type*) := (compl : α → α)

export has_compl (compl)

postfix `ᶜ`:(max+1) := compl

/-- A Boolean algebra is a bounded distributive lattice with
a complement operator `ᶜ` such that `x ⊓ xᶜ = ⊥` and `x ⊔ xᶜ = ⊤`.
For convenience, it must also provide a set difference operation `\`
satisfying `x \ y = x ⊓ yᶜ`.

This is a generalization of (classical) logic of propositions, or
the powerset lattice. -/
class boolean_algebra α extends bounded_distrib_lattice α, has_compl α, has_sdiff α :=
(inf_compl_le_bot : ∀x:α, x ⊓ xᶜ ≤ ⊥)
(top_le_sup_compl : ∀x:α, ⊤ ≤ x ⊔ xᶜ)
(sdiff_eq : ∀x y:α, x \ y = x ⊓ yᶜ)

section boolean_algebra
variables [boolean_algebra α]

@[simp] theorem inf_compl_eq_bot : x ⊓ xᶜ = ⊥ :=
bot_unique $ boolean_algebra.inf_compl_le_bot x

@[simp] theorem compl_inf_eq_bot : xᶜ ⊓ x = ⊥ :=
eq.trans inf_comm inf_compl_eq_bot

@[simp] theorem sup_compl_eq_top : x ⊔ xᶜ = ⊤ :=
top_unique $ boolean_algebra.top_le_sup_compl x

@[simp] theorem compl_sup_eq_top : xᶜ ⊔ x = ⊤ :=
eq.trans sup_comm sup_compl_eq_top

theorem is_compl_compl : is_compl x xᶜ :=
is_compl.of_eq inf_compl_eq_bot sup_compl_eq_top

theorem is_compl.compl_eq (h : is_compl x y) : xᶜ = y :=
(h.right_unique is_compl_compl).symm

theorem disjoint_compl_right : disjoint x xᶜ := is_compl_compl.disjoint
theorem disjoint_compl_left : disjoint xᶜ x := disjoint_compl_right.symm

theorem sdiff_eq : x \ y = x ⊓ yᶜ :=
boolean_algebra.sdiff_eq x y

theorem top_sdiff : ⊤ \ x = xᶜ := by rw [sdiff_eq, top_inf_eq]

theorem compl_unique (i : x ⊓ y = ⊥) (s : x ⊔ y = ⊤) : xᶜ = y :=
(is_compl.of_eq i s).compl_eq

@[simp] theorem compl_top : ⊤ᶜ = (⊥:α) :=
is_compl_top_bot.compl_eq

@[simp] theorem compl_bot : ⊥ᶜ = (⊤:α) :=
is_compl_bot_top.compl_eq

@[simp] theorem compl_compl (x : α) : xᶜᶜ = x :=
is_compl_compl.symm.compl_eq

theorem compl_injective : function.injective (compl : α → α) :=
function.involutive.injective compl_compl

@[simp] theorem compl_inj_iff : xᶜ = yᶜ ↔ x = y :=
compl_injective.eq_iff

theorem is_compl.compl_eq_iff (h : is_compl x y) : zᶜ = y ↔ z = x :=
h.compl_eq ▸ compl_inj_iff

@[simp] theorem compl_eq_top : xᶜ = ⊤ ↔ x = ⊥ :=
is_compl_bot_top.compl_eq_iff

@[simp] theorem compl_eq_bot : xᶜ = ⊥ ↔ x = ⊤ :=
is_compl_top_bot.compl_eq_iff

@[simp] theorem compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ :=
(is_compl_compl.inf_sup is_compl_compl).compl_eq

@[simp] theorem compl_sup : (x ⊔ y)ᶜ = xᶜ ⊓ yᶜ :=
(is_compl_compl.sup_inf is_compl_compl).compl_eq

theorem compl_le_compl (h : y ≤ x) : xᶜ ≤ yᶜ :=
is_compl_compl.antimono is_compl_compl h

@[simp] theorem compl_le_compl_iff_le : yᶜ ≤ xᶜ ↔ x ≤ y :=
⟨assume h, by have h := compl_le_compl h; simp at h; assumption,
  compl_le_compl⟩

theorem le_compl_of_le_compl (h : y ≤ xᶜ) : x ≤ yᶜ :=
by simpa only [compl_compl] using compl_le_compl h

theorem compl_le_of_compl_le (h : yᶜ ≤ x) : xᶜ ≤ y :=
by simpa only [compl_compl] using compl_le_compl h

theorem le_compl_iff_le_compl : y ≤ xᶜ ↔ x ≤ yᶜ :=
⟨le_compl_of_le_compl, le_compl_of_le_compl⟩

theorem compl_le_iff_compl_le : xᶜ ≤ y ↔ yᶜ ≤ x :=
⟨compl_le_of_compl_le, compl_le_of_compl_le⟩

namespace boolean_algebra

@[priority 100]
instance : generalized_boolean_algebra α :=
{ sup_inf_sdiff := λ a b, by rw [sdiff_eq, ←inf_sup_left, sup_compl_eq_top, inf_top_eq],
  inf_inf_sdiff := λ a b, by rw [_root_.sdiff_eq, inf_left_right_swap, @inf_assoc _ _ a,
      compl_inf_eq_bot, inf_bot_eq, bot_inf_eq],
  ..(infer_instance : boolean_algebra α) }

@[priority 100]
instance : is_complemented α := ⟨λ x, ⟨xᶜ, is_compl_compl⟩⟩

end boolean_algebra

end boolean_algebra

instance boolean_algebra_Prop : boolean_algebra Prop :=
{ compl := not,
  sdiff := λ p q, p ∧ ¬ q,
  sdiff_eq := λ _ _, rfl,
  inf_compl_le_bot := λ p ⟨Hp, Hpc⟩, Hpc Hp,
  top_le_sup_compl := λ p H, classical.em p,
  .. bounded_distrib_lattice_Prop }

instance pi.boolean_algebra {α : Type u} {β : Type v} [boolean_algebra β] :
  boolean_algebra (α → β) :=
by pi_instance
