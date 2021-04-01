/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
import data.fintype.card
import linear_algebra.finsupp
import linear_algebra.linear_independent
import linear_algebra.linear_pmap
import linear_algebra.projection

/-!

# Bases

This file defines bases in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

## Main definitions

All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `basis ι R M` is the type of `ι`-indexed `R`-bases for a semimodule `M`,
  represented by a linear equiv `M ≃ₗ[R] ι →₀ R`.

* `basis.repr` is the isomorphism sending `x : M` and to its coordinates `basis.repr x : ι →₀ R`

* `basis.constr hv f` constructs a linear map `M₁ →ₗ[R] M₂` given the values `f : ι → M₂` at the
  basis elements `⇑b : ι → M₁`.

## Main statements

* `basis.mk`: a linear independent set of vectors spanning the whole module determines a basis

* `basis.ext` states that two linear maps are equal if they coincide on a basis.

* `nonempty_basis` states that every vector space has a basis.

## Implementation notes

We use families instead of sets because it allows us to say that two identical vectors are linearly
dependent. For bases, this is useful as well because we can easily derive ordered bases by using an
ordered index type `ι`.

## Tags

basis, bases

-/

noncomputable theory

universe u

open function set submodule
open_locale classical big_operators

variables {ι : Type*} {ι' : Type*} {R : Type*} {K : Type*}
variables {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

section semimodule

variables [semiring R]
variables [add_comm_monoid M] [semimodule R M] [add_comm_monoid M'] [semimodule R M']

section
variables (ι) (R) (M)

/-- A `basis ι R M` for a semimodule `M` is the type of `ι`-indexed `R`-bases of `M`.

The basis vectors are available as `coe_fn (b : basis ι R M) : ι → M`.
To turn a linear independent family of vectors spanning `M` into a basis, use `basis.mk`.
They are internally represented as linear equivs `M ≃ₗ[R] (ι →₀ R)`,
available as `basis.repr`.
-/
structure basis := of_repr :: (repr : M ≃ₗ[R] (ι →₀ R))

end

namespace basis

instance : inhabited (basis ι R (ι →₀ R)) := ⟨basis.of_repr (linear_equiv.refl _ _)⟩

variables (b b₁ : basis ι R M) (i : ι) (c : R) (x : M)

section repr

/-- `b i` is the `i`th basis vector. -/
instance : has_coe_to_fun (basis ι R M) :=
{ F := λ _, ι → M,
  coe := λ b i, b.repr.symm (finsupp.single i 1) }

@[simp] lemma coe_of_repr (e : M ≃ₗ[R] (ι →₀ R)) :
  ⇑(of_repr e) = λ i, e.symm (finsupp.single i 1) :=
rfl

protected lemma injective [nontrivial R] : injective b :=
b.repr.symm.injective.comp (λ _ _, (finsupp.single_left_inj (one_ne_zero : (1 : R) ≠ 0)).mp)

lemma repr_symm_single_one : b.repr.symm (finsupp.single i 1) = b i := rfl

lemma repr_symm_single : b.repr.symm (finsupp.single i c) = c • b i :=
calc b.repr.symm (finsupp.single i c)
    = b.repr.symm (c • finsupp.single i 1) : by rw [finsupp.smul_single', mul_one]
... = c • b i : by rw [linear_equiv.map_smul, repr_symm_single_one]

@[simp] lemma repr_self : b.repr (b i) = finsupp.single i 1 :=
linear_equiv.apply_symm_apply _ _

lemma repr_self_apply (j) : b.repr (b i) j = if i = j then 1 else 0 :=
by rw [repr_self, finsupp.single_apply]

@[simp] lemma repr_symm_apply (v) : b.repr.symm v = finsupp.total ι M R b v :=
calc b.repr.symm v = b.repr.symm (v.sum finsupp.single) : by simp
... = ∑ i in v.support, b.repr.symm (finsupp.single i (v i)) :
  by rw [finsupp.sum, linear_equiv.map_sum]
... = finsupp.total ι M R b v :
  by simp [repr_symm_single, finsupp.total_apply, finsupp.sum]

@[simp] lemma coe_repr_symm : ↑b.repr.symm = finsupp.total ι M R b :=
linear_map.ext (λ v, b.repr_symm_apply v)

@[simp] lemma repr_total (v) : b.repr (finsupp.total _ _ _ b v) = v :=
by { rw ← b.coe_repr_symm, exact b.repr.apply_symm_apply v }

@[simp] lemma total_repr : finsupp.total _ _ _ b (b.repr x) = x :=
by { rw ← b.coe_repr_symm, exact b.repr.symm_apply_apply x }

end repr

section ext

variables {M₁ : Type*} [add_comm_monoid M₁] [semimodule R M₁]

/-- Two linear maps are equal if they are equal on basis vectors. -/
theorem ext {f₁ f₂ : M →ₗ[R] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
by { ext x,
     rw [← b.total_repr x, finsupp.total_apply, finsupp.sum],
     simp only [linear_map.map_sum, linear_map.map_smul, h] }

/-- Two linear equivs are equal if they are equal on basis vectors. -/
theorem ext' {f₁ f₂ : M ≃ₗ[R] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
by { ext x,
      rw [← b.total_repr x, finsupp.total_apply, finsupp.sum],
      simp only [linear_equiv.map_sum, linear_equiv.map_smul, h] }

/-- Two elements are equal if their coordinates are equal. -/
theorem ext_elem {x y : M}
  (h : ∀ i, b.repr x i = b.repr y i) : x = y :=
by { rw [← b.total_repr x, ← b.total_repr y], congr' 1, ext i, exact h i }

lemma repr_eq_iff {b : basis ι R M} {f : M →ₗ[R] ι →₀ R} :
  ↑b.repr = f ↔ ∀ i, f (b i) = finsupp.single i 1 :=
⟨λ h i, h ▸ b.repr_self i,
 λ h, b.ext (λ i, (b.repr_self i).trans (h i).symm)⟩

lemma repr_eq_iff' {b : basis ι R M} {f : M ≃ₗ[R] ι →₀ R} :
  b.repr = f ↔ ∀ i, f (b i) = finsupp.single i 1 :=
⟨λ h i, h ▸ b.repr_self i,
  λ h, b.ext' (λ i, (b.repr_self i).trans (h i).symm)⟩

lemma apply_eq_iff {b : basis ι R M} {x : M} {i : ι} :
  b i = x ↔ b.repr x = finsupp.single i 1 :=
⟨λ h, h ▸ b.repr_self i,
 λ h, b.repr.injective ((b.repr_self i).trans h.symm)⟩

/-- An unbundled version of `repr_eq_iff` -/
lemma repr_apply_eq (f : M → ι → R)
  (hadd : ∀ x y, f (x + y) = f x + f y) (hsmul : ∀ (c : R) (x : M), f (c • x) = c • f x)
  (f_eq : ∀ i, f (b i) = finsupp.single i 1) (x : M) (i : ι) :
  b.repr x i = f x i :=
begin
  let f_i : M →ₗ[R] R :=
  { to_fun := λ x, f x i,
    map_add' := λ _ _, by rw [hadd, pi.add_apply],
    map_smul' := λ _ _, by rw [hsmul, pi.smul_apply] },
  have : (finsupp.lapply i).comp ↑b.repr = f_i,
  { refine b.ext (λ j, _),
    show b.repr (b j) i = f (b j) i,
    rw [b.repr_self, f_eq] },
  calc b.repr x i = f_i x : by { rw ← this, refl }
              ... = f x i : rfl
end

/-- Two bases are equal if they assign the same coordinates. -/
lemma eq_of_repr_eq_repr {b₁ b₂ : basis ι R M} (h : ∀ x i, b₁.repr x i = b₂.repr x i) :
  b₁ = b₂ :=
have b₁.repr = b₂.repr, by { ext, apply h },
by { cases b₁, cases b₂, simpa }

/-- Two bases are equal if their basis vectors are the same. -/
@[ext] lemma eq_of_apply_eq {b₁ b₂ : basis ι R M} (h : ∀ i, b₁ i = b₂ i) : b₁ = b₂ :=
suffices b₁.repr = b₂.repr, by { cases b₁, cases b₂, simpa },
repr_eq_iff'.mpr (λ i, by rw [h, b₂.repr_self])

end ext

section reindex

variables (b' : basis ι' R M')
variables (e : ι ≃ ι')

/-- `b.reindex (e : ι ≃ ι')` is a basis indexed by `ι'` -/
def reindex : basis ι' R M :=
basis.of_repr (b.repr.trans (finsupp.dom_lcongr e))

@[simp] lemma reindex_apply (i' : ι') : b.reindex e i' = b (e.symm i') :=
show (b.repr.trans (finsupp.dom_lcongr e)).symm (finsupp.single i' 1) =
  b.repr.symm (finsupp.single (e.symm i') 1),
by rw [linear_equiv.symm_trans_apply, finsupp.dom_lcongr_symm, finsupp.dom_lcongr_single]

@[simp] lemma coe_reindex_repr : ((b.reindex e).repr x : ι' → R) = b.repr x ∘ e.symm :=
funext $ λ i',
show (finsupp.dom_lcongr e : _ ≃ₗ[R] _) (b.repr x) i' = _,
from finsupp.dom_lcongr_apply _ _ _

@[simp] lemma reindex_repr (i' : ι') : (b.reindex e).repr x i' = b.repr x (e.symm i') :=
by rw coe_reindex_repr

/-- `b.reindex_range` is a basis indexed by `range b`, the basis vectors themselves. -/
def reindex_range [nontrivial R] : basis (range b) R M :=
b.reindex (equiv.of_injective b b.injective)

lemma finsupp.single_apply_left {α β γ : Type*} [has_zero γ]
  {f : α → β} (hf : function.injective f)
  (x z : α) (y : γ) :
  finsupp.single (f x) y (f z) = finsupp.single x y z :=
by simp [finsupp.single_apply, hf.eq_iff]

lemma reindex_range_self [nontrivial R] (i : ι) (h := set.mem_range_self i) :
  b.reindex_range ⟨b i, h⟩ = b i :=
by rw [reindex_range, reindex_apply, equiv.apply_of_injective_symm b b.injective, subtype.coe_mk]

lemma reindex_range_repr_self [nontrivial R] (i : ι) :
  b.reindex_range.repr (b i) = finsupp.single ⟨b i, mem_range_self i⟩ 1 :=
calc b.reindex_range.repr (b i) = b.reindex_range.repr (b.reindex_range ⟨b i, mem_range_self i⟩) :
  congr_arg _ (b.reindex_range_self _ _).symm
... = finsupp.single ⟨b i, mem_range_self i⟩ 1 : b.reindex_range.repr_self _

@[simp] lemma reindex_range_apply [nontrivial R] {bi : M} {i : ι} (h : b i = bi) :
  b.reindex_range ⟨bi, ⟨i, h⟩⟩ = b i :=
by { convert b.reindex_range_self i, rw h }

@[simp] lemma reindex_range_repr [nontrivial R] (x : M) {bi : M} {i : ι} (h : b i = bi) :
  b.reindex_range.repr x ⟨bi, ⟨i, h⟩⟩ = b.repr x i :=
begin
  subst h,
  refine (b.repr_apply_eq (λ x i, b.reindex_range.repr x ⟨b i, _⟩) _ _ _ x i).symm,
  { intros x y,
    ext i,
    simp only [pi.add_apply, linear_equiv.map_add, finsupp.coe_add] },
  { intros c x,
    ext i,
    simp only [pi.smul_apply, linear_equiv.map_smul, finsupp.coe_smul] },
  { intros i,
    ext j,
    simp only [reindex_range_repr_self],
    refine @finsupp.single_apply_left _ _ _ _ (λ i, (⟨b i, _⟩ : set.range b)) _ _ _ _,
    exact λ i j h, b.injective (subtype.mk.inj h) }
end

end reindex

protected lemma linear_independent : linear_independent R b :=
linear_independent_iff.mpr $ λ l hl,
calc l = b.repr (finsupp.total _ _ _ b l) : (b.repr_total l).symm
   ... = 0 : by rw [hl, linear_equiv.map_zero]

section constr

variables (S : Type*) [semiring S] [semimodule S M']
variables [smul_comm_class R S M']

@[simp] lemma finsupp.map_domain_single {α β M : Type*} [add_comm_monoid M]
  (f : α → β) (x : α) (y : M) :
  finsupp.map_domain f (finsupp.single x y) = finsupp.single (f x) y :=
by { ext i, simp [finsupp.map_domain] }

/-- Construct a linear map given the value at the basis.

This definition is parameterized over an extra `semiring S`,
such that `smul_comm_class R S M'` holds.
If `R` is commutative, you can set `S := R`; if `R` is not commutative,
you can recover an `add_equiv` by setting `S := ℕ`.
-/
def constr : (ι → M') ≃ₗ[S] (M →ₗ[R] M') :=
{ to_fun := λ f, (finsupp.total M' M' R id).comp $ (finsupp.lmap_domain R R f).comp b.repr,
  inv_fun := λ f i, f (b i),
  left_inv := λ f, by { ext, simp },
  right_inv := λ f, by { refine b.ext (λ i, _), simp },
  map_add' := λ f g, by { refine b.ext (λ i, _), simp },
  map_smul' := λ c f, by { refine b.ext (λ i, _), simp } }

theorem constr_def (f : ι → M') :
  b.constr S f = (finsupp.total M' M' R id).comp ((finsupp.lmap_domain R R f).comp b.repr) :=
rfl

theorem constr_apply (f : ι → M') (x : M) :
  b.constr S f x = (b.repr x).sum (λ b a, a • f b) :=
by { simp only [constr_def, linear_map.comp_apply, finsupp.lmap_domain_apply, finsupp.total_apply],
     rw finsupp.sum_map_domain_index; simp [add_smul] }

@[simp] lemma constr_basis {f : ι → M'} {i : ι} :
  (b.constr S f : M → M') (b i) = f i :=
by simp [basis.constr_apply, b.repr_self]

lemma constr_eq {g : ι → M'} {f : M →ₗ[R] M'}
  (h : ∀i, g i = f (b i)) : b.constr S g = f :=
b.ext $ λ i, (b.constr_basis S).trans (h i)

lemma constr_self (f : M →ₗ[R] M') : b.constr S (λ i, f (b i)) = f :=
b.constr_eq S $ λ x, rfl

lemma constr_range [nonempty ι] {f : ι  → M'} :
  (b.constr S f).range = span R (range f) :=
by rw [b.constr_def S f, linear_map.range_comp, linear_map.range_comp, linear_equiv.range,
       ← finsupp.supported_univ, finsupp.lmap_domain_supported, ←set.image_univ,
       ← finsupp.span_eq_map_total, set.image_id]

end constr

section equiv

variables (b' : basis ι' R M') (e : ι ≃ ι')
variables [add_comm_monoid M''] [semimodule R M'']

/-- If `b` is a basis for `M` and `b'` a basis for `M'`, and the index types are equivalent,
`b.equiv b' e` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `b' (e i)`. -/
protected def equiv : M ≃ₗ[R] M' :=
b.repr.trans (b'.reindex e.symm).repr.symm

@[simp] lemma equiv_apply : b.equiv b' e (b i) = b' (e i) :=
by simp [basis.equiv]

@[simp] lemma equiv_refl :
  b.equiv b (equiv.refl ι) = linear_equiv.refl R M :=
b.ext' (λ i, by simp)

@[simp] lemma equiv_symm : (b.equiv b' e).symm = b'.equiv b e.symm :=
b'.ext' $ λ i, (b.equiv b' e).injective (by simp)

@[simp] lemma equiv_trans {ι'' : Type*} (b'' : basis ι'' R M'')
  (e : ι ≃ ι') (e' : ι' ≃ ι'') :
  (b.equiv b' e).trans (b'.equiv b'' e') = b.equiv b'' (e.trans e') :=
b.ext' (λ i, by simp)

end equiv

section map

variables (f : M ≃ₗ[R] M')

/-- Apply the linear equivalence `f` to the basis vectors. -/
protected def map : basis ι R M' :=
of_repr (f.symm.trans b.repr)

@[simp] lemma map_apply (i) : b.map f i = f (b i) := rfl

end map

section prod

variables (b' : basis ι' R M')

/-- `basis.prod` maps a `ι`-indexed basis for `M` and a `ι'`-indexed basis for `M'`
to a `ι ⊕ ι'`-index basis for `M × M'`. -/
protected def prod : basis (ι ⊕ ι') R (M × M') :=
of_repr ((b.repr.prod b'.repr).trans (finsupp.sum_arrow_lequiv_prod_arrow R).symm)

@[simp]
lemma prod_repr_inl (x) (i) : (b.prod b').repr x (sum.inl i) = b.repr x.1 i := rfl

@[simp]
lemma prod_repr_inr (x) (i) : (b.prod b').repr x (sum.inr i) = b'.repr x.2 i := rfl

lemma prod_apply_inl_fst (i) :
  (b.prod b' (sum.inl i)).1 = b i :=
b.repr.injective $ by
{ ext j,
  simp only [basis.prod, basis.coe_of_repr, linear_equiv.symm_trans_apply, linear_equiv.prod_symm,
      linear_equiv.prod_apply, b.repr.apply_symm_apply, linear_equiv.symm_symm, repr_self,
      equiv.to_fun_as_coe, finsupp.fst_sum_arrow_lequiv_prod_arrow],
  apply finsupp.single_apply_left sum.inl_injective }

lemma prod_apply_inr_fst (i) :
(b.prod b' (sum.inr i)).1 = 0 :=
b.repr.injective $ by
{ ext i,
  simp only [basis.prod, basis.coe_of_repr, linear_equiv.symm_trans_apply, linear_equiv.prod_symm,
      linear_equiv.prod_apply, b.repr.apply_symm_apply, linear_equiv.symm_symm, repr_self,
      equiv.to_fun_as_coe, finsupp.fst_sum_arrow_lequiv_prod_arrow, linear_equiv.map_zero,
      finsupp.zero_apply],
  apply finsupp.single_eq_of_ne sum.inr_ne_inl }

lemma prod_apply_inl_snd (i) :
  (b.prod b' (sum.inl i)).2 = 0 :=
b'.repr.injective $ by
{ ext j,
  simp only [basis.prod, basis.coe_of_repr, linear_equiv.symm_trans_apply, linear_equiv.prod_symm,
      linear_equiv.prod_apply, b'.repr.apply_symm_apply, linear_equiv.symm_symm, repr_self,
      equiv.to_fun_as_coe, finsupp.snd_sum_arrow_lequiv_prod_arrow, linear_equiv.map_zero,
      finsupp.zero_apply],
  apply finsupp.single_eq_of_ne sum.inl_ne_inr }

lemma prod_apply_inr_snd (i) :
(b.prod b' (sum.inr i)).2 = b' i :=
b'.repr.injective $ by
{ ext i,
  simp only [basis.prod, basis.coe_of_repr, linear_equiv.symm_trans_apply, linear_equiv.prod_symm,
      linear_equiv.prod_apply, b'.repr.apply_symm_apply, linear_equiv.symm_symm, repr_self,
      equiv.to_fun_as_coe, finsupp.snd_sum_arrow_lequiv_prod_arrow],
  apply finsupp.single_apply_left sum.inr_injective }

@[simp]
lemma prod_apply (i) :
  b.prod b' i = sum.elim (linear_map.inl R M M' ∘ b) (linear_map.inr R M M' ∘ b') i :=
by { ext; cases i; simp only [prod_apply_inl_fst, sum.elim_inl, linear_map.inl_apply,
                              prod_apply_inr_fst, sum.elim_inr, linear_map.inr_apply,
                              prod_apply_inl_snd, prod_apply_inr_snd, comp_app] }

end prod

section no_zero_smul_divisors

-- Can't be an instance because the basis can't be inferred.
lemma no_zero_smul_divisors [no_zero_divisors R] (b : basis ι R M) :
  no_zero_smul_divisors R M :=
⟨λ c x hcx, or_iff_not_imp_right.mpr (λ hx, begin
  rw [← b.total_repr x, ← linear_map.map_smul] at hcx,
  have := linear_independent_iff.mp b.linear_independent (c • b.repr x) hcx,
  rw smul_eq_zero at this,
  exact this.resolve_right (λ hr, hx (b.repr.map_eq_zero_iff.mp hr))
end)⟩

lemma smul_eq_zero [no_zero_divisors R] (b : basis ι R M) {c : R} {x : M} :
  c • x = 0 ↔ c = 0 ∨ x = 0 :=
@smul_eq_zero _ _ _ _ _ b.no_zero_smul_divisors _ _

end no_zero_smul_divisors

section singleton

/-- `basis.singleton ι R` is the basis sending the unique element of `ι` to `1 : R`. -/
protected def singleton (ι R : Type*) [unique ι] [semiring R] :
  basis ι R R :=
of_repr
  { to_fun := λ x, finsupp.single (default ι) x,
    inv_fun := λ f, f (default ι),
    left_inv := λ x, by simp,
    right_inv := λ f, finsupp.unique_ext (by simp),
    map_add' := λ x y, by simp,
    map_smul' := λ c x, by simp }

@[simp] lemma singleton_apply (ι R : Type*) [unique ι] [semiring R] (i) :
  basis.singleton ι R i = 1 :=
apply_eq_iff.mpr (by simp [basis.singleton])

end singleton

section empty

/-- If `M` is a subsingleton and `ι` is empty, this is the unique `ι`-indexed basis for `M`. -/
protected def empty [subsingleton M] (h_empty : ¬ nonempty ι) : basis ι R M :=
of_repr
  { to_fun := λ x, 0,
    inv_fun := λ f, 0,
    left_inv := λ x, by simp,
    right_inv := λ f, by { ext i, cases h_empty ⟨i⟩ },
    map_add' := λ x y, by simp,
    map_smul' := λ c x, by simp }

lemma empty_unique [subsingleton M] (h_empty : ¬ nonempty ι)
  (b : basis ι R M) : b = basis.empty h_empty :=
by { ext i, cases h_empty ⟨i⟩ }

end empty

end basis

section fintype

open basis
open fintype

variables [fintype ι] (b : basis ι R M)

/-- A module over `R` with a finite basis is linearly equivalent to functions from its basis to `R`.
-/
def basis.equiv_fun : M ≃ₗ[R] (ι → R) :=
linear_equiv.trans b.repr
  { to_fun := coe_fn,
    map_add' := finsupp.coe_add,
    map_smul' := finsupp.coe_smul,
    ..finsupp.equiv_fun_on_fintype }

/-- A module over a finite ring that admits a finite basis is finite. -/
def module.fintype_of_fintype [fintype R] : fintype M :=
fintype.of_equiv _ b.equiv_fun.to_equiv.symm

theorem module.card_fintype [fintype R] [fintype M] :
  card M = (card R) ^ (card ι) :=
calc card M = card (ι → R)    : card_congr b.equiv_fun.to_equiv
        ... = card R ^ card ι : card_fun

/-- Given a basis `v` indexed by `ι`, the canonical linear equivalence between `ι → R` and `M` maps
a function `x : ι → R` to the linear combination `∑_i x i • v i`. -/
@[simp] lemma basis.equiv_fun_symm_apply (x : ι → R) :
  b.equiv_fun.symm x = ∑ i, x i • b i :=
by { simp [basis.equiv_fun, finsupp.total_apply, finsupp.sum_fintype],
     refl }

@[simp]
lemma basis.equiv_fun_apply (u : M) : b.equiv_fun u = b.repr u := rfl

lemma basis.sum_equiv_fun (u : M) : ∑ i, b.equiv_fun u i • b i = u :=
begin
  conv_rhs { rw ← b.total_repr u },
  simp [finsupp.total_apply, finsupp.sum_fintype, b.equiv_fun_apply]
end

@[simp]
lemma basis.equiv_fun_self (i j : ι) : b.equiv_fun (b i) j = if i = j then 1 else 0 :=
by { rw [b.equiv_fun_apply, b.repr_self_apply] }

variables (S : Type*) [semiring S] [semimodule S M']
variables [smul_comm_class R S M']

@[simp] theorem basis.constr_apply_fintype (f : ι → M') (x : M) :
  (b.constr S f : M → M') x = ∑ i, (b.equiv_fun x i) • f i :=
by simp [b.constr_apply, b.equiv_fun_apply, finsupp.sum_fintype]

end fintype

end semimodule

section comm_semiring

namespace basis

variables [comm_semiring R]
variables [add_comm_monoid M] [semimodule R M] [add_comm_monoid M'] [semimodule R M']
variables (b : basis ι R M) (b' : basis ι' R M')

/-- If `b` is a basis for `M` and `b'` a basis for `M'`,
and `f`, `g` form a bijection between the basis vectors,
`b.equiv' b' f g hf hg hgf hfg` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `f (b i)`.
-/
def equiv' (f : M → M') (g : M' → M)
  (hf : ∀ i, f (b i) ∈ range b') (hg : ∀ i, g (b' i) ∈ range b)
  (hgf : ∀i, g (f (b i)) = b i) (hfg : ∀i, f (g (b' i)) = b' i) :
  M ≃ₗ[R] M' :=
{ inv_fun := b'.constr R (g ∘ b'),
  left_inv :=
    have (b'.constr R (g ∘ b')).comp (b.constr R (f ∘ b)) = linear_map.id,
    from (b.ext $ λ i, exists.elim (hf i)
      (λ i' hi', by rw [linear_map.comp_apply, b.constr_basis, function.comp_apply, ← hi',
                        b'.constr_basis, function.comp_apply, hi', hgf, linear_map.id_apply])),
    λ x, congr_arg (λ (h : M →ₗ[R] M), h x) this,
  right_inv :=
    have (b.constr R (f ∘ b)).comp (b'.constr R (g ∘ b')) = linear_map.id,
    from (b'.ext $ λ i, exists.elim (hg i)
      (λ i' hi', by rw [linear_map.comp_apply, b'.constr_basis, function.comp_apply, ← hi',
                        b.constr_basis, function.comp_apply, hi', hfg, linear_map.id_apply])),
    λ x, congr_arg (λ (h : M' →ₗ[R] M'), h x) this,
  .. b.constr R (f ∘ b) }

@[simp] lemma equiv'_apply (f : M → M') (g : M' → M) (hf hg hgf hfg) (i : ι) :
  b.equiv' b' f g hf hg hgf hfg (b i) = f (b i) :=
b.constr_basis R

@[simp] lemma equiv'_symm_apply (f : M → M') (g : M' → M) (hf hg hgf hfg) (i : ι') :
  (b.equiv' b' f g hf hg hgf hfg).symm (b' i) = g (b' i) :=
b'.constr_basis R

end basis

end comm_semiring

section module

open linear_map

variables {v : ι → M}
variables [ring R] [add_comm_group M] [add_comm_group M'] [add_comm_group M'']
variables [module R M] [module R M'] [module R M'']
variables {c d : R} {x y : M}
variables (b : basis ι R M)

namespace basis

section mk

variables (hli : linear_independent R v) (hsp : span R (range v) = ⊤)

/-- A linear independent family of vectors spanning the whole module is a basis. -/
protected noncomputable def mk : basis ι R M :=
basis.of_repr
{ inv_fun := finsupp.total _ _ _ v,
  left_inv := λ x, hli.total_repr ⟨x, _⟩,
  right_inv := λ x, hli.repr_eq rfl,
  .. hli.repr.comp (linear_map.id.cod_restrict _ (λ h, hsp.symm ▸ submodule.mem_top)) }

@[simp] lemma mk_repr :
  (basis.mk hli hsp).repr x = hli.repr ⟨x, hsp.symm ▸ submodule.mem_top⟩ :=
rfl

lemma mk_apply (i : ι) : basis.mk hli hsp i = v i :=
show finsupp.total _ _ _ v _ = v i, by simp

@[simp] lemma coe_mk : ⇑(basis.mk hli hsp) = v :=
funext (mk_apply _ _)

end mk

section span

variables (hli : linear_independent R v)

/-- A linear independent family of vectors is a basis for their span. -/
protected noncomputable def span : basis ι R (span R (range v)) :=
basis.mk (linear_independent_span hli) $
begin
  rw eq_top_iff,
  intros x _,
  have h₁ : subtype.val '' set.range (λ i, subtype.mk (v i) _) = range v,
  by rw ←set.range_comp,
  have h₂ : map (submodule.subtype _) (span R (set.range (λ i, subtype.mk (v i) _)))
  = span R (range v),
  by rw [←span_image, submodule.subtype_eq_val, h₁],
  have h₃ : (x : M) ∈ map (submodule.subtype _) (span R (set.range (λ i, subtype.mk (v i) _))),
  by rw h₂; apply subtype.mem x,
  rcases mem_map.1 h₃ with ⟨y, hy₁, hy₂⟩,
  have h_x_eq_y : x = y,
  by rw [subtype.ext_iff, ← hy₂]; simp,
  rw h_x_eq_y,
  exact hy₁
end

end span

end basis

end module

section vector_space

variables [field K] [add_comm_group V] [add_comm_group V'] [vector_space K V] [vector_space K V']
variables {v : ι → V} {s t : set V} {x y z : V}

include K

open submodule

namespace basis

section exists_basis

/-- If `s` is a linear independent set of vectors, we can extend it to a basis. -/
noncomputable def extend (hs : linear_independent K (coe : s → V)) :
  basis _ K V :=
basis.mk
  (@linear_independent.restrict_of_comp_subtype _ _ _ id _ _ _ _ (hs.linear_independent_extend _))
  (eq_top_iff.mpr $ set_like.coe_subset_coe.mp $
    by simpa using hs.subset_span_extend (subset_univ s))

@[simp] lemma extend_apply_self (hs : linear_independent K (coe : s → V))
  (x : hs.extend _) :
  basis.extend hs x = x :=
basis.mk_apply _ _ _

@[simp] lemma range_extend (hs : linear_independent K (coe : s → V)) :
  range (basis.extend hs) = hs.extend (subset_univ _) :=
by { ext, simp only [set.mem_range, extend_apply_self, set_coe.exists, subtype.coe_mk,
                     exists_prop, exists_eq_right] }

/-- If `v` is a linear independent family of vectors, extend it to a basis indexed by a sum type. -/
noncomputable def sum_extend (hs : linear_independent K v) :
  basis (ι ⊕ _) K V :=
let s := set.range v,
    e : ι ≃ s := equiv.of_injective v hs.injective,
    b := hs.to_subtype_range.extend (subset_univ (set.range v)) in
(basis.extend hs.to_subtype_range).reindex $ equiv.symm $
  calc ι ⊕ (b \ s : set V) ≃ s ⊕ (b \ s : set V) : equiv.sum_congr e (equiv.refl _)
  ... ≃ b                   : equiv.set.sum_diff_subset (hs.to_subtype_range.subset_extend _)

section

variables (K V)

/-- A set used to index `basis.of_vector_space`. -/
noncomputable def of_vector_space_index : set V :=
(linear_independent_empty K V).extend (subset_univ _)

/-- Each vector space has a basis. -/
noncomputable def of_vector_space : basis (of_vector_space_index K V) K V :=
basis.extend (linear_independent_empty K V)

@[simp] lemma of_vector_space_apply_self (x : of_vector_space_index K V) :
  of_vector_space K V x = x :=
basis.mk_apply _ _ _

@[simp] lemma range_of_vector_space :
  range (of_vector_space K V) = of_vector_space_index K V :=
range_extend _

end

end exists_basis

end basis

lemma linear_map.exists_left_inverse_of_injective (f : V →ₗ[K] V')
  (hf_inj : f.ker = ⊥) : ∃g:V' →ₗ V, g.comp f = linear_map.id :=
begin
  let B := basis.of_vector_space_index K V,
  let hB := basis.of_vector_space K V,
  have hB₀ : _ := hB.linear_independent.to_subtype_range,
  have : linear_independent K (λ x, x : f '' B → V'),
  { have h₁ : linear_independent K (λ (x : ↥(⇑f '' range (basis.of_vector_space _ _))), ↑x) :=
         @linear_independent.image_subtype _ _ _ _ _ _ _ _ _ f hB₀
      (show disjoint _ _, by simp [hf_inj]),
    rwa [basis.range_of_vector_space K V] at h₁ },
  let C := this.extend (subset_univ _),
  have BC := this.subset_extend (subset_univ _),
  let hC := basis.extend this,
  haveI : inhabited V := ⟨0⟩,
  refine ⟨hC.constr K (C.restrict (inv_fun f)), hB.ext (λ b, _)⟩,
  rw image_subset_iff at BC,
  have fb_eq : f b = hC ⟨f b, BC b.2⟩,
  { change f b = basis.extend this _,
    rw [basis.extend_apply_self, subtype.coe_mk] },
  dsimp [hB],
  rw [basis.of_vector_space_apply_self, fb_eq, hC.constr_basis],
  exact left_inverse_inv_fun (linear_map.ker_eq_bot.1 hf_inj) _
end

lemma submodule.exists_is_compl (p : submodule K V) : ∃ q : submodule K V, is_compl p q :=
let ⟨f, hf⟩ := p.subtype.exists_left_inverse_of_injective p.ker_subtype in
⟨f.ker, linear_map.is_compl_of_proj $ linear_map.ext_iff.1 hf⟩

instance vector_space.submodule.is_complemented : is_complemented (submodule K V) :=
⟨submodule.exists_is_compl⟩

lemma linear_map.exists_right_inverse_of_surjective (f : V →ₗ[K] V')
  (hf_surj : f.range = ⊤) : ∃g:V' →ₗ V, f.comp g = linear_map.id :=
begin
  let C := basis.of_vector_space_index K V',
  let hC := basis.of_vector_space K V',
  haveI : inhabited V := ⟨0⟩,
  use hC.constr K (C.restrict (inv_fun f)),
  refine hC.ext (λ c, _),
  rw [linear_map.comp_apply, hC.constr_basis],
  simp [right_inverse_inv_fun (linear_map.range_eq_top.1 hf_surj) c]
end

/-- Any linear map `f : p →ₗ[K] V'` defined on a subspace `p` can be extended to the whole
space. -/
lemma linear_map.exists_extend {p : submodule K V} (f : p →ₗ[K] V') :
  ∃ g : V →ₗ[K] V', g.comp p.subtype = f :=
let ⟨g, hg⟩ := p.subtype.exists_left_inverse_of_injective p.ker_subtype in
⟨f.comp g, by rw [linear_map.comp_assoc, hg, f.comp_id]⟩

open submodule linear_map

/-- If `p < ⊤` is a subspace of a vector space `V`, then there exists a nonzero linear map
`f : V →ₗ[K] K` such that `p ≤ ker f`. -/
lemma submodule.exists_le_ker_of_lt_top (p : submodule K V) (hp : p < ⊤) :
  ∃ f ≠ (0 : V →ₗ[K] K), p ≤ ker f :=
begin
  rcases set_like.exists_of_lt hp with ⟨v, -, hpv⟩, clear hp,
  rcases (linear_pmap.sup_span_singleton ⟨p, 0⟩ v (1 : K) hpv).to_fun.exists_extend with ⟨f, hf⟩,
  refine ⟨f, _, _⟩,
  { rintro rfl, rw [linear_map.zero_comp] at hf,
    have := linear_pmap.sup_span_singleton_apply_mk ⟨p, 0⟩ v (1 : K) hpv 0 p.zero_mem 1,
    simpa using (linear_map.congr_fun hf _).trans this },
  { refine λ x hx, mem_ker.2 _,
    have := linear_pmap.sup_span_singleton_apply_mk ⟨p, 0⟩ v (1 : K) hpv x hx 0,
    simpa using (linear_map.congr_fun hf _).trans this }
end

theorem quotient_prod_linear_equiv (p : submodule K V) :
  nonempty ((p.quotient × p) ≃ₗ[K] V) :=
let ⟨q, hq⟩ := p.exists_is_compl in nonempty.intro $
((quotient_equiv_of_is_compl p q hq).prod (linear_equiv.refl _ _)).trans
  (prod_equiv_of_is_compl q p hq.symm)

open fintype
variables (K) (V)

theorem vector_space.card_fintype [fintype K] [fintype V] :
  ∃ n : ℕ, card V = (card K) ^ n :=
⟨card (basis.of_vector_space_index K V), module.card_fintype (basis.of_vector_space K V)⟩

end vector_space
