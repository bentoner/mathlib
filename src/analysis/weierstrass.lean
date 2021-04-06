import algebra.algebra.subalgebra
import topology.continuous_function.algebra
import topology.algebra.polynomial
import topology.continuous_function.bounded
import topology.algebra.affine
import linear_algebra.affine_space.ordered
import analysis.special_functions.bernstein
import topology.unit_interval

noncomputable theory

open continuous_map

variables {X : Type*} [topological_space X]
variables {R : Type*} [comm_ring R] [topological_space R] [topological_ring R]

open filter
open_locale topological_space unit_interval

/--
The special case of the Weierstrass approximation theorem for the interval `[0,1]`.
We do this first, because the Bernstein polynomials are specifically adapted to this interval.
-/
theorem polynomial_functions_closure_eq_top' :
  (polynomial_functions I).topological_closure = ⊤ :=
begin
  apply eq_top_iff.mpr,
  rintros f -,
  refine filter.frequently.mem_closure _,
  refine filter.tendsto.frequently (bernstein_approximation_uniform f) _,
  apply frequently_of_forall,
  intro n,
  sorry,
end

def pullback {X Y : Type*} [topological_space X] [topological_space Y] (f : C(X, Y)) :
  C(Y, ℝ) →ₐ[ℝ] C(X, ℝ) :=
{ to_fun := λ g, g.comp f,
  map_zero' := by { ext, simp, },
  map_add' := λ g₁ g₂, by { ext, simp, },
  map_one' := by { ext, simp, },
  map_mul' := λ g₁ g₂, by { ext, simp, },
  commutes' := λ r, by { ext, simp, }, }

@[simp] lemma pullback_apply
  {X Y : Type*} [topological_space X] [topological_space Y] (f : C(X, Y)) (g : C(Y, ℝ)):
  (pullback f) g = g.comp f :=
rfl

lemma pullback_continuous
  {X Y : Type*} [topological_space X] [compact_space X] [topological_space Y] [compact_space Y]
  (f : C(X, Y)) :
  continuous (pullback f) :=
begin
  change continuous (λ g : C(Y, ℝ), g.comp f),
  refine metric.continuous_iff.mpr _,
  intros g ε ε_pos,
  refine ⟨ε, ε_pos, λ g' h, _⟩,
  -- FIXME shouldn't need `erw`
  erw bounded_continuous_function.dist_lt_iff_of_compact ε_pos at h ⊢,
  { exact λ x, h (f x), },
  { assumption, },
  { assumption, },
end

def pullback_as_continuous_map
  {X Y : Type*} [topological_space X] [compact_space X] [topological_space Y] [compact_space Y]
  (f : C(X, Y)) : C(C(Y, ℝ), C(X, ℝ)) :=
{ to_fun := pullback f,
  continuous_to_fun := pullback_continuous f }

@[simp] lemma pullback_as_continuous_map_apply
  {X Y : Type*} [topological_space X] [compact_space X] [topological_space Y] [compact_space Y]
  (f : C(X, Y)) (g : C(Y, ℝ)) :
  (pullback_as_continuous_map f) g = g.comp f :=
rfl

open affine_map

def line_map_Icc (a b : ℝ) (h : a < b) : C(set.Icc (0 : ℝ) (1 : ℝ), set.Icc a b) :=
begin
  let f₁ : ℝ →ᵃ[ℝ] ℝ := affine_map.line_map a b,
  let f₂ : set.Icc (0 : ℝ) 1 → set.Icc a b :=
    λ x, ⟨f₁ x, begin
      rcases x with ⟨x, zero_le, le_one⟩,
      simp only [subtype.coe_mk, set.mem_Icc],
      fsplit,
      apply left_le_line_map_of_nonneg_of_le zero_le (le_of_lt h),
      apply line_map_le_right_of_le_one_of_le le_one (le_of_lt h),
    end⟩,
  have c : continuous f₂ :=
  begin
    apply continuous_subtype_mk,
    change continuous (f₁ ∘ subtype.val),
    continuity,
  end,
  exact ⟨f₂, c⟩,
end

@[simp] lemma line_map_Icc_apply (a b : ℝ) (h : a < b) (x : I) :
  (line_map_Icc a b h x : ℝ) = affine_map.line_map a b (x : ℝ) := rfl

/-- The preimage of polynomials on `[0,1]` under the pullback map by `x ↦ (b-a) * x + a`
is the polynomials on `[a,b]`. -/
lemma polynomial_functions.comap'_pullback_line_map_Icc (a b : ℝ) (h : a < b) :
  (polynomial_functions I).comap' (pullback (line_map_Icc a b h)) =
    polynomial_functions (set.Icc a b) :=
begin
  ext f,
  fsplit,
  { rintro ⟨p, ⟨-,w⟩⟩,
    rw continuous_map.ext_iff at w,
    dsimp at w,
    let q := p.comp ((b - a)⁻¹ • polynomial.X + polynomial.C (-a * (b-a)⁻¹)),
    refine ⟨q, ⟨_, _⟩⟩,
    { simp, },
    { ext x,
      simp only [neg_mul_eq_neg_mul_symm,
        ring_hom.map_neg, ring_hom.map_mul, alg_hom.coe_to_ring_hom,
        polynomial.eval_X, polynomial.eval_neg, polynomial.eval_C, polynomial.eval_smul,
        polynomial.eval_mul, polynomial.eval_add, polynomial.coe_aeval_eq_eval,
        polynomial.eval_comp, polynomial.as_continuous_map_on_alg_hom_apply,
        polynomial.as_continuous_map_on_to_fun, polynomial.as_continuous_map_to_fun],
      convert w ⟨_, _⟩; clear w,
      { -- FIXME why does `comm_ring.add` appear here?
        change x = line_map_Icc _ _ _ ⟨_ + _, _⟩,
        ext,
        simp only [line_map, line_map_Icc_apply,
          vsub_eq_sub, vadd_eq_add, function.const_apply, pi.add_apply, subtype.coe_mk,
          algebra.id.smul_eq_mul, affine_map.coe_add, affine_map.coe_const,
          linear_map.id_coe, id.def, linear_map.smul_right_apply, linear_map.coe_to_affine_map],
        replace h : b - a ≠ 0 := sub_ne_zero_of_ne h.ne.symm,
        simp only [add_mul],
        field_simp, },
      { change _ + _ ∈ I,
        rw [mul_comm (b-a)⁻¹, ←neg_mul_eq_neg_mul_symm, ←add_mul, ←sub_eq_add_neg],
        have w₁ : 0 < (b-a)⁻¹ := inv_pos.mpr (sub_pos.mpr h),
        have w₂ : 0 ≤ (x : ℝ) - a := sub_nonneg.mpr x.2.1,
        have w₃ : (x : ℝ) - a ≤ b - a := sub_le_sub_right x.2.2 a,
        fsplit,
        { exact mul_nonneg w₂ (le_of_lt w₁), },
        { rw [←div_eq_mul_inv, div_le_one (sub_pos.mpr h)],
          exact w₃, }, }, }, },
  { rintro ⟨p, ⟨-,rfl⟩⟩,
    let q := p.comp ((b - a) • polynomial.X + polynomial.C a),
    refine ⟨q, ⟨_, _⟩⟩,
    { simp, },
    { ext x, simp [line_map, mul_comm], }, },
end

lemma continuous_map.subsingleton_subalgebra_ext [subsingleton X] (s₁ s₂ : subalgebra R C(X, R)) :
  s₁ = s₂ :=
begin
  by_cases n : nonempty X,
  { obtain ⟨x⟩ := n,
    ext f,
    have h : f = algebra_map R C(X, R) (f x),
    { ext x', simp only [mul_one, algebra.id.smul_eq_mul, algebra_map_apply], congr, },
    rw h,
    simp only [subalgebra.algebra_map_mem], },
  { ext f,
    have h : f = 0,
    { ext x', exact false.elim (n ⟨x'⟩), },
    subst h,
    simp only [subalgebra.zero_mem], },
end

/--
The Weierstrass approximation theorem:
polynomials functions on `[a, b] ⊆ ℝ` are dense in `C([a,b],ℝ)`

(While we could deduce this as an application of the Stone-Weierstrass theorem,
our proof of that relies on the fact that `abs` is in the closure of polynomials on `[-M, M]`,
so we may as well get this done first.)
-/
theorem polynomial_functions_closure_eq_top (a b : ℝ) :
  (polynomial_functions (set.Icc a b)).topological_closure = ⊤ :=
begin
  by_cases h : a < b, -- (Otherwise it's easy; we'll deal with that later.)
  { -- We can pullback continuous functions to `[a,b]` to continuous functions on `[0,1]`,
    -- by precomposing with an affine map.
    let W : C(set.Icc a b, ℝ) →ₐ[ℝ] C(I, ℝ) := pullback (line_map_Icc a b h),
    -- This operation is itself a homeomorphism
    -- (with respect to the norm topologies on continuous functions).
    let W' : C(set.Icc a b, ℝ) ≃ₜ C(I, ℝ) := sorry,
    have w : (W : C(set.Icc a b, ℝ) → C(I, ℝ)) = W' := sorry,
    -- Thus we take the statement of the Weierstrass approximation theorem for `[0,1]`,
    have p := polynomial_functions_closure_eq_top',
    -- and pullback both sides, obtaining an equation between subalgebras of `C([a,b], ℝ)`.
    apply_fun (λ s, s.comap' W) at p,
    simp only [algebra.comap_top] at p,
    -- Since the pullback operation is continuous, it commutes with taking `topological_closure`,
    rw subalgebra.topological_closure_comap'_homeomorph _ W W' w at p,
    -- and precomposing with an affine map takes polynomial functions to polynomial functions.
    rw polynomial_functions.comap'_pullback_line_map_Icc at p,
    -- 🎉
    exact p },
  { -- Otherwise, `b ≤ a`, and the interval is a subsingleton,
    -- so all subalgebras are the same anyway.
    haveI : subsingleton (set.Icc a b) := ⟨λ x y, le_antisymm
      ((x.2.2.trans (not_lt.mp h)).trans y.2.1) ((y.2.2.trans (not_lt.mp h)).trans x.2.1)⟩,
    apply continuous_map.subsingleton_subalgebra_ext, }
end

theorem mem_polynomial_functions_closure (a b : ℝ) (f : C(set.Icc a b, ℝ)) :
  f ∈ (polynomial_functions (set.Icc a b)).topological_closure :=
begin
  rw polynomial_functions_closure_eq_top _ _,
  simp,
end
