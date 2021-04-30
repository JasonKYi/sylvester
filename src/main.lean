import linear_algebra.quadratic_form 
import analysis.special_functions.pow

/- 
Sylvester's law of inertia: 
- We would like to prove the complex version first: 
  A quadratic form `Q` over the field `R` is isometric to a quadratic form 
  in the form
  ` ∑ xᵢ^2 `
The idea is we would like to expand the API for `quadratic_form.equivalent`.
  Given a orthogonal basis wrt. some quadratic form, we should have a equivalent 
form. This will be constructed.
-/

open_locale big_operators classical

variables {R : Type*} [comm_ring R] [invertible (2 : R)] 
variables {M : Type*} [add_comm_group M] [module R M]
variables {M₁ : Type*} [add_comm_group M₁] [module R M₁]
variables {ι : Type*} [fintype ι] {v : ι → M}

-- Should be a def since it takes a parameter
def field.invertible {K : Type*} [field K] {z : K} (hz : z ≠ 0) : invertible z :=
{ inv_of := z⁻¹,
  inv_of_mul_self := inv_mul_cancel hz,
  mul_inv_of_self := mul_inv_cancel hz }

namespace quadratic_form

open finset bilin_form

/-- A quadratic form composed with a linear equiv is isometric to itself. -/
def isometry_of_comp_linear_equiv (Q : quadratic_form R M) (f : M₁ ≃ₗ[R] M) : 
  Q.isometry (Q.comp (f : M₁ →ₗ[R] M)) := 
{ map_app' := 
  begin
    intro,  
    simp only [comp_apply, linear_equiv.coe_coe, linear_equiv.to_fun_eq_coe, 
               linear_equiv.apply_symm_apply, f.apply_symm_apply],
  end, .. f.symm }

/-- Given a quadratic form `Q` and a basis, `of_is_basis` is the basis representation of `Q`. -/
noncomputable def of_is_basis (Q : quadratic_form R M) 
  (hv₁ : is_basis R v) : quadratic_form R (ι → R) := Q.comp hv₁.equiv_fun.symm

@[simp]
lemma isometry_of_is_basis_apply (Q : quadratic_form R M) (hv₁ : is_basis R v) 
  (w : ι → R) : Q.of_is_basis hv₁ w = Q (∑ i : ι, w i • v i) := 
by { rw ← hv₁.equiv_fun_symm_apply, refl }

/-- A quadratic form is isometric to its bases representations. -/
noncomputable def isometry_of_is_basis (Q : quadratic_form R M) (hv₁ : is_basis R v) : 
  isometry Q (Q.of_is_basis hv₁) :=
isometry_of_comp_linear_equiv Q hv₁.equiv_fun.symm

lemma isometry_of_is_Ortho_apply (Q : quadratic_form R M) (hv₁ : is_basis R v) 
  (hv₂ : (associated Q).is_Ortho v) (w : ι → R) : 
  Q.of_is_basis hv₁ w = ∑ i : ι, associated Q (v i) (v i) * w i * w i :=
begin
  rw [isometry_of_is_basis_apply, ← @associated_eq_self_apply R, sum_left], 
  refine sum_congr rfl (λ j hj, _),
  rw [sum_right, sum_eq_single j],
  { rw [smul_left, smul_right], ring },
  { intros i _ hij,
    rw [smul_left, smul_right, 
        show (associated_hom R) Q (v j) (v i) = 0, by exact hv₂ i j hij, 
        mul_zero, mul_zero] },
  { intro hnj, exact false.elim (hnj hj) }
end

/-- The weighted sum of squared with respect some weight. `weighted_sum_squares` is the 
quadratic form version of this. -/
def weighted_sum_squares' (w : ι → R) : (ι → R) → R := 
  λ x, ∑ i : ι, w i * x i * x i

lemma weighted_sum_squares'_smul {w : ι → R} (a : R) (x : ι → R) : 
  weighted_sum_squares' w (a • x) = a * a * weighted_sum_squares' w x :=
begin
  simp only [weighted_sum_squares', algebra.id.smul_eq_mul, pi.smul_apply], 
  conv_rhs { rw [mul_assoc, mul_sum, mul_sum] },
  refine sum_congr rfl (λ _ _, by ring),
end

lemma weighted_sum_squares'_polar_add_left {w : ι → R} (x x' y : ι → R) : 
  polar (weighted_sum_squares' w) (x + x') y = 
  polar (weighted_sum_squares' w) x y + polar (weighted_sum_squares' w) x' y :=
begin
  simp_rw [weighted_sum_squares', polar, pi.add_apply],
  iterate 7 { rw ← sum_add_distrib <|> rw ← sum_sub_distrib },
  refine sum_congr rfl (λ _ _, by ring),
end

lemma weighted_sum_squares'_polar_smul_left {w : ι → R} (a : R) (x y : ι → R) : 
  polar (weighted_sum_squares' w) (a • x) y = a • polar (weighted_sum_squares' w) x y := 
begin
  simp_rw [weighted_sum_squares', polar, pi.add_apply, pi.smul_apply],
  iterate 4 { rw ← sum_add_distrib <|> rw ← sum_sub_distrib },
  simp_rw [smul_sum, smul_eq_mul], 
  refine sum_congr rfl (λ _ _, by ring),
end

lemma weighted_sum_squares'_polar_add_right {w : ι → R} (x y y' : ι → R) : 
  polar (weighted_sum_squares' w) x (y + y') = 
  polar (weighted_sum_squares' w) x y + polar (weighted_sum_squares' w) x y' :=
begin
  simp_rw [weighted_sum_squares', polar, pi.add_apply],
  iterate 7 { rw ← sum_add_distrib <|> rw ← sum_sub_distrib },
  refine sum_congr rfl (λ _ _, by ring),
end

lemma weighted_sum_squares'_polar_smul_right {w : ι → R} (a : R) (x y : ι → R) : 
  polar (weighted_sum_squares' w) x (a • y) = a • polar (weighted_sum_squares' w) x y := 
begin
  simp_rw [weighted_sum_squares', polar, pi.add_apply, pi.smul_apply],
  iterate 4 { rw ← sum_add_distrib <|> rw ← sum_sub_distrib },
  simp_rw [smul_sum, smul_eq_mul], 
  refine sum_congr rfl (λ _ _, by ring),
end

/-- `weighted_sum_squares'` represented as a quadratic form. -/
def weighted_sum_squares (w : ι → R) : quadratic_form R (ι → R) := 
{ to_fun := weighted_sum_squares' w,
  to_fun_smul := weighted_sum_squares'_smul,
  polar_add_left' := weighted_sum_squares'_polar_add_left,
  polar_smul_left' := weighted_sum_squares'_polar_smul_left,
  polar_add_right' := weighted_sum_squares'_polar_add_right,
  polar_smul_right' := weighted_sum_squares'_polar_smul_right }

variables {V : Type*} {K : Type*} [field K] [invertible (2 : K)] 
variables [add_comm_group V] [module K V] [finite_dimensional K V]

@[simp] 
lemma weighted_sum_squares_apply (w v : ι → R) :
  weighted_sum_squares w v = ∑ i : ι, w i * v i * v i := rfl

lemma equivalent_weighted_sum_squares_of_nondegenerate' 
  (Q : quadratic_form K V) (hQ : (associated Q).nondegenerate) : 
  ∃ w : fin (finite_dimensional.finrank K V) → K, 
  (∀ i, w i ≠ 0) ∧ equivalent Q (weighted_sum_squares w) :=
begin
  obtain ⟨v, hv₁, hv₂, hv₃⟩ := exists_orthogonal_basis' hQ associated_is_sym,
  refine ⟨λ i, associated Q (v i) (v i), hv₃, _⟩,
  refine nonempty.intro _,
  convert Q.isometry_of_is_basis hv₂,
  ext w, 
  rw [isometry_of_is_Ortho_apply Q hv₂ hv₁], refl,
end

lemma equivalent_weighted_sum_squares_of_nondegenerate 
  (Q : quadratic_form K V) (hQ : (associated Q).nondegenerate) : 
  ∃ w : fin (finite_dimensional.finrank K V) → K, 
    equivalent Q (weighted_sum_squares w) :=
let ⟨w, _, hw₂⟩ := Q.equivalent_weighted_sum_squares_of_nondegenerate' hQ in ⟨w, hw₂⟩

-- Missing?
lemma smul_is_basis {v : ι → M} (hv : is_basis R v) 
  {w : ι → R} (hw₁ : ∀ i : ι, w i ≠ 0) (hw₂ : ∀ i : ι, invertible (w i)) : 
  is_basis R (λ i, w i • v i) := 
begin
  obtain ⟨hw₁', hw₁''⟩ := hv,
  refine ⟨_, _⟩,
  { rw linear_independent_iff'' at hw₁' ⊢,
    intros s g hgs hsum i, 
    have hw : g i * w i = 0 := hw₁' s (λ i, g i • w i) _ _ i,
    { suffices : g i * w i * (hw₂ i).inv_of = 0,
        rwa [mul_assoc, mul_inv_of_self, mul_one] at this,
      rw [hw, zero_mul] },
    { intros i hi,
      simp only [algebra.id.smul_eq_mul, hgs i hi, zero_mul] },
    { rw [← hsum, sum_congr rfl _],
      intros, simp only [smul_assoc] } },
  { rw eq_top_iff,
    intros j hj,
    rw ← hw₁'' at hj,
    rw submodule.mem_span at hj ⊢,
    refine λ p hp, hj p (λ u hu, _),
    obtain ⟨i, rfl⟩ := hu,
    have := p.smul_mem (⅟ (w i)) (hp ⟨i, rfl⟩),
    simp only [← smul_assoc, smul_eq_mul, inv_of_mul_self, one_smul] at this,
    exact this }
end

section complex

/-- The weighted sum of squares on the complex numbers as a quadratic form is equivalent 
to the sum of squares, i.e. `weighted_sum_squares` with weight `λ i : ι, 1`. -/
noncomputable def isometry_sum_squares (w : ι → ℂ) (hw : ∀ i : ι, w i ≠ 0) : 
  isometry (weighted_sum_squares w) (weighted_sum_squares (λ _, 1 : ι → ℂ)) := 
begin
  have hw' : ∀ i : ι, (w i) ^ - (1 / 2 : ℂ) ≠ 0, 
  { intros i hi,  
    exact hw i ((complex.cpow_eq_zero_iff _ _).1 hi).1 },
  convert (weighted_sum_squares w).isometry_of_is_basis 
    (smul_is_basis (pi.is_basis_fun ℂ ι) hw' (λ i, field.invertible (hw' i))),
  ext1 v,
  rw [isometry_of_is_basis_apply, weighted_sum_squares_apply, 
      weighted_sum_squares_apply],
  refine sum_congr rfl (λ j hj, _),
  have hsum : (∑ (i : ι), v i • w i ^ - (1 / 2 : ℂ) • 
    (linear_map.std_basis ℂ (λ (i : ι), ℂ) i) 1) j = 
    v j • w j ^ - (1 / 2 : ℂ), 
  { rw [sum_apply, sum_eq_single j, linear_map.std_basis_apply, pi.smul_apply, pi.smul_apply, 
        function.update_same, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one],
    intros i _ hij, 
    rw [linear_map.std_basis_apply, pi.smul_apply, pi.smul_apply, function.update_noteq hij.symm, 
        pi.zero_apply, smul_eq_mul, smul_eq_mul, mul_zero, mul_zero], 
    intro hj', exact false.elim (hj' hj) },
  rw [hsum, smul_eq_mul],
  suffices : 1 * v j * v j =  w j ^ - (1 / 2 : ℂ) * w j ^ - (1 / 2 : ℂ) * w j * v j * v j, 
  { rw this, ring },
  rw [← complex.cpow_add _ _ (hw j), show - (1 / 2 : ℂ) + - (1 / 2) = -1, by ring, 
      complex.cpow_neg_one, inv_mul_cancel (hw j)],
end .

/-- A nondegenerate quadratic form on the complex numbers is equivalent to 
the sum of squares, i.e. `weighted_sum_squares` with weight `λ i : ι, 1`. -/
theorem equivalent_sum_squared {M : Type*} [add_comm_group M] [module ℂ M] 
  [finite_dimensional ℂ M] (Q : quadratic_form ℂ M) (hQ : (associated Q).nondegenerate) : 
  equivalent Q (weighted_sum_squares (λ _, 1 : fin (finite_dimensional.finrank ℂ M) → ℂ)) := 
let ⟨w, hw₁, hw₂⟩ := Q.equivalent_weighted_sum_squares_of_nondegenerate' hQ in
  nonempty.intro $ (classical.choice hw₂).trans (isometry_sum_squares w hw₁)

end complex

-- Real version of Sylvester's law of inertia

section real

-- Move
noncomputable def sign (r : ℝ) : ℝ := if r < 0 then -1 else 1

lemma sign_apply_eq (r : ℝ) : sign r = -1 ∨ sign r = 1 :=
begin
  by_cases r < 0,
  { exact or.intro_left _ (if_pos h) },
  { exact or.intro_right _ (if_neg h) }
end

lemma sign_mul_nonneg (r : ℝ) : 0 ≤ sign r * r := 
begin
  by_cases r < 0, 
  { rw [sign, if_pos h],
    exact mul_nonneg_of_nonpos_of_nonpos (by norm_num) (le_of_lt h) },
  { rw [sign, if_neg h, one_mul],
    exact not_lt.1 h }
end

lemma sign_mul_ne_zero_pos (r : ℝ) (hr : r ≠ 0) : 0 < sign r * r :=
begin
  refine lt_of_le_of_ne (sign_mul_nonneg r) (λ h, _),
  rw zero_eq_mul at h,
  cases sign_apply_eq r with hneg hpos;
  cases h; { linarith <|> exact hr h }
end

lemma sign_inv_eq_self (r : ℝ) : (sign r)⁻¹ = sign r := 
begin
  cases sign_apply_eq r with h h,
  { rw h, norm_num },
  { rw h, exact inv_one }
end

lemma equivalent_one_neg_one_weighted_sum_squares' 
  {M : Type*} [add_comm_group M] [module ℝ M] [finite_dimensional ℝ M] 
  (u : ι → ℝ) (hu : ∀ i : ι, u i ≠ 0) : 
  ∃ w : ι → ℝ, (∀ i, w i = -1 ∨ w i = 1) ∧
  equivalent (weighted_sum_squares u) (weighted_sum_squares w) := 
begin
  refine ⟨sign ∘ u, λ i, sign_apply_eq (u i), _⟩,
  have hu' : ∀ i : ι, 0 < (sign (u i) * u i) ^ - (1 / 2 : ℝ), 
  { intro i, refine real.rpow_pos_of_pos (sign_mul_ne_zero_pos _ (hu i)) _ },
  have hu'' := λ i, (ne_of_lt (hu' i)).symm,
  convert nonempty.intro ((weighted_sum_squares u).isometry_of_is_basis 
    (smul_is_basis (pi.is_basis_fun ℝ ι) hu'' (λ i, field.invertible (hu'' i)))),
    ext1 v,
  rw [isometry_of_is_basis_apply, weighted_sum_squares_apply, weighted_sum_squares_apply],
  refine sum_congr rfl (λ j hj, _),
  have hsum : (∑ (i : ι), v i • (sign (u i) * u i) ^ - (1 / 2 : ℝ) • 
    (linear_map.std_basis ℝ (λ (i : ι), ℝ) i) 1) j = 
    v j • (sign (u j) * u j) ^ - (1 / 2 : ℝ), 
  { rw [sum_apply, sum_eq_single j, linear_map.std_basis_apply, pi.smul_apply, pi.smul_apply, 
        function.update_same, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one],
    intros i _ hij, 
    rw [linear_map.std_basis_apply, pi.smul_apply, pi.smul_apply, function.update_noteq hij.symm, 
        pi.zero_apply, smul_eq_mul, smul_eq_mul, mul_zero, mul_zero], 
    intro hj', exact false.elim (hj' hj) },
  rw [hsum, smul_eq_mul],
  suffices : (sign ∘ u) j * v j * v j = (sign (u j) * u j) ^ - (1 / 2 : ℝ) * 
    (sign (u j) * u j) ^ - (1 / 2 : ℝ) * u j * v j * v j, 
  { rw this, ring },
  rw [← real.rpow_add (sign_mul_ne_zero_pos _ (hu j)), 
      show - (1 / 2 : ℝ) + - (1 / 2) = -1, by ring, real.rpow_neg_one, mul_inv', 
      sign_inv_eq_self, mul_assoc (sign (u j)) (u j)⁻¹, inv_mul_cancel (hu j), mul_one], 
end

theorem equivalent_one_neg_one_weighted_sum_squared 
  {M : Type*} [add_comm_group M] [module ℝ M] [finite_dimensional ℝ M] 
  (Q : quadratic_form ℝ M) (hQ : (associated Q).nondegenerate) : 
  ∃ w : fin (finite_dimensional.finrank ℝ M) → ℝ, 
  (∀ i, w i = -1 ∨ w i = 1) ∧ equivalent Q (weighted_sum_squares w) :=
let ⟨w, hw₁, hw₂⟩ := Q.equivalent_weighted_sum_squares_of_nondegenerate' hQ in
let ⟨u, hu₁, hu₂⟩ := @equivalent_one_neg_one_weighted_sum_squares' _ _ M _ _ _ w hw₁ in
  ⟨u, hu₁, hw₂.trans hu₂⟩

end real

end quadratic_form