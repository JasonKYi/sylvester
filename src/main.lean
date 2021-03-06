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

variables {R : Type*} [ring R] 
variables {R₁ : Type*} [comm_ring R₁] [invertible (2 : R₁)] 
variables {M : Type*} [add_comm_group M] [module R M] [module R₁ M]
variables {M₁ : Type*} [add_comm_group M₁] [module R M₁]
variables {ι : Type*} [fintype ι] {v : ι → M}

-- Should be a def since it takes a parameter
def field.invertible {K : Type*} [field K] {z : K} (hz : z ≠ 0) : invertible z :=
{ inv_of := z⁻¹,
  inv_of_mul_self := inv_mul_cancel hz,
  mul_inv_of_self := mul_inv_cancel hz }

lemma is_basis.smul_of_invertible {v : ι → M} (hv : is_basis R v)
  {w : ι → R} (hw : ∀ i : ι, invertible (w i)) :
  is_basis R (λ i, w i • v i) :=
begin
  obtain ⟨hw₁', hw₁''⟩ := hv,
  split,
  { rw linear_independent_iff'' at hw₁' ⊢,
    intros s g hgs hsum i,
    have hw₁ : g i * w i = 0 := hw₁' s (λ i, g i • w i) _ _ i,
    { suffices : g i * w i * (hw i).inv_of = 0,
        rwa [mul_assoc, mul_inv_of_self, mul_one] at this,
      rw [hw₁, zero_mul] },
    { intros i hi,
      simp only [algebra.id.smul_eq_mul, hgs i hi, zero_smul] },
    { rw [← hsum, finset.sum_congr rfl _],
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

namespace quadratic_form

open finset bilin_form

/-- A quadratic form composed with a `linear_equiv` is isometric to itself. -/
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

lemma isometry_of_is_Ortho_apply [invertible (2 : R₁)]
  (Q : quadratic_form R₁ M) (hv₁ : is_basis R₁ v)
  (hv₂ : (associated Q).is_Ortho v) (w : ι → R₁) :
  Q.of_is_basis hv₁ w = ∑ i : ι, associated Q (v i) (v i) * w i * w i :=
begin
  rw [isometry_of_is_basis_apply, ← @associated_eq_self_apply R₁, sum_left],
  refine sum_congr rfl (λ j hj, _),
  rw [sum_right, sum_eq_single j],
  { rw [smul_left, smul_right], ring },
  { intros i _ hij,
    rw [smul_left, smul_right,
        show (associated_hom R₁) Q (v j) (v i) = 0, by exact hv₂ i j hij,
        mul_zero, mul_zero] },
  { contradiction }
end

/-- The weighted sum of squares with respect some weight as a quadratic form. -/
def weighted_sum_squares (w : ι → R₁) : quadratic_form R₁ (ι → R₁) :=
∑ i : ι, w i • proj i i

@[simp]
lemma weighted_sum_squares_apply (w v : ι → R₁) :
  weighted_sum_squares w v = ∑ i : ι, w i * (v i * v i) :=
quadratic_form.sum_apply _ _ _

variables {V : Type*} {K : Type*} [field K] [invertible (2 : K)]
variables [add_comm_group V] [module K V] [finite_dimensional K V]

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
  rw [isometry_of_is_Ortho_apply Q hv₂ hv₁, weighted_sum_squares_apply],
  refine finset.sum_congr rfl _,
  intros, rw ← mul_assoc,
end

lemma equivalent_weighted_sum_squares_of_nondegenerate
  (Q : quadratic_form K V) (hQ : (associated Q).nondegenerate) :
  ∃ w : fin (finite_dimensional.finrank K V) → K,
    equivalent Q (weighted_sum_squares w) :=
let ⟨w, _, hw₂⟩ := Q.equivalent_weighted_sum_squares_of_nondegenerate' hQ in ⟨w, hw₂⟩

section complex

/-- The isometry between a weighted sum of squares on the complex numbers and the
sum of squares, i.e. `weighted_sum_squares` with weight `λ i : ι, 1`. -/
noncomputable def isometry_sum_squares [decidable_eq ι] (w : ι → ℂ) (hw : ∀ i : ι, w i ≠ 0) :
  isometry (weighted_sum_squares w) (weighted_sum_squares (λ _, 1 : ι → ℂ)) :=
begin
  have hw' : ∀ i : ι, (w i) ^ - (1 / 2 : ℂ) ≠ 0,
  { intros i hi,
    exact hw i ((complex.cpow_eq_zero_iff _ _).1 hi).1 },
  convert (weighted_sum_squares w).isometry_of_is_basis
    (is_basis.smul_of_invertible (pi.is_basis_fun ℂ ι) (λ i, field.invertible (hw' i))),
  ext1 v,
  rw [isometry_of_is_basis_apply, weighted_sum_squares_apply, weighted_sum_squares_apply],
  refine sum_congr rfl (λ j hj, _),
  have hsum : (∑ (i : ι), v i • w i ^ - (1 / 2 : ℂ) •
    (linear_map.std_basis ℂ (λ (i : ι), ℂ) i) 1) j =
    v j • w j ^ - (1 / 2 : ℂ),
  { rw [finset.sum_apply, sum_eq_single j, linear_map.std_basis_apply, pi.smul_apply,
        pi.smul_apply, function.update_same, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one],
    intros i _ hij,
    rw [linear_map.std_basis_apply, pi.smul_apply, pi.smul_apply, function.update_noteq hij.symm,
        pi.zero_apply, smul_eq_mul, smul_eq_mul, mul_zero, mul_zero],
    intro hj', exact false.elim (hj' hj) },
  rw [hsum, smul_eq_mul],
  suffices : 1 * v j * v j =  w j ^ - (1 / 2 : ℂ) * w j ^ - (1 / 2 : ℂ) * w j * v j * v j,
  { rw [← mul_assoc, this], ring },
  rw [← complex.cpow_add _ _ (hw j), show - (1 / 2 : ℂ) + - (1 / 2) = -1, by ring,
      complex.cpow_neg_one, inv_mul_cancel (hw j)],
end .

/-- A nondegenerate quadratic form on the complex numbers is equivalent to
the sum of squares, i.e. `weighted_sum_squares` with weight `λ i : ι, 1`. -/
theorem equivalent_sum_squares {M : Type*} [add_comm_group M] [module ℂ M]
  [finite_dimensional ℂ M] (Q : quadratic_form ℂ M) (hQ : (associated Q).nondegenerate) :
  equivalent Q (weighted_sum_squares (λ _, 1 : fin (finite_dimensional.finrank ℂ M) → ℂ)) :=
let ⟨w, hw₁, hw₂⟩ := Q.equivalent_weighted_sum_squares_of_nondegenerate' hQ in
  nonempty.intro $ (classical.choice hw₂).trans (isometry_sum_squares w hw₁)

end complex

section real

/-- The sign function that maps negative real numbers to -1 and nonnegative numbers to 1. -/
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

/-- The isometry between a weighted sum of squares with weights `u` on the complex numbers
and the weighted sum of squares with weights `sign ∘ u`. -/
noncomputable def isometry_sign_weighted_sum_squares'
  [decidable_eq ι] (u : ι → ℝ) (hu : ∀ i : ι, u i ≠ 0) :
  isometry (weighted_sum_squares u) (weighted_sum_squares (sign ∘ u)) :=
begin
  have hu' : ∀ i : ι, 0 ≠ (sign (u i) * u i) ^ - (1 / 2 : ℝ),
  { intro i, exact ne_of_lt (real.rpow_pos_of_pos (sign_mul_ne_zero_pos _ (hu i)) _) },
  convert ((weighted_sum_squares u).isometry_of_is_basis
    (is_basis.smul_of_invertible (pi.is_basis_fun ℝ ι) (λ i, field.invertible (hu' i).symm))),
  ext1 v,
  rw [isometry_of_is_basis_apply, weighted_sum_squares_apply, weighted_sum_squares_apply],
  refine sum_congr rfl (λ j hj, _),
  have hsum : (∑ (i : ι), v i • (sign (u i) * u i) ^ - (1 / 2 : ℝ) •
    (linear_map.std_basis ℝ (λ (i : ι), ℝ) i) 1) j =
    v j • (sign (u j) * u j) ^ - (1 / 2 : ℝ),
  { rw [finset.sum_apply, sum_eq_single j, linear_map.std_basis_apply, pi.smul_apply,
        pi.smul_apply, function.update_same, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one],
    intros i _ hij,
    rw [linear_map.std_basis_apply, pi.smul_apply, pi.smul_apply, function.update_noteq hij.symm,
        pi.zero_apply, smul_eq_mul, smul_eq_mul, mul_zero, mul_zero],
    intro hj', exact false.elim (hj' hj) },
  rw [hsum, smul_eq_mul],
  suffices : (sign ∘ u) j * v j * v j = (sign (u j) * u j) ^ - (1 / 2 : ℝ) *
    (sign (u j) * u j) ^ - (1 / 2 : ℝ) * u j * v j * v j,
  { rw [← mul_assoc, this], ring },
  rw [← real.rpow_add (sign_mul_ne_zero_pos _ (hu j)),
      show - (1 / 2 : ℝ) + - (1 / 2) = -1, by ring, real.rpow_neg_one, mul_inv',
      sign_inv_eq_self, mul_assoc (sign (u j)) (u j)⁻¹, inv_mul_cancel (hu j), mul_one],
end

/-- Sylvester's law of inertia: A nondegenerate real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1. -/
theorem equivalent_one_neg_one_weighted_sum_squared
  {M : Type*} [add_comm_group M] [module ℝ M] [finite_dimensional ℝ M]
  (Q : quadratic_form ℝ M) (hQ : (associated Q).nondegenerate) :
  ∃ w : fin (finite_dimensional.finrank ℝ M) → ℝ,
  (∀ i, w i = -1 ∨ w i = 1) ∧ equivalent Q (weighted_sum_squares w) :=
let ⟨w, hw₁, hw₂⟩ := Q.equivalent_weighted_sum_squares_of_nondegenerate' hQ in
  ⟨sign ∘ w, λ i, sign_apply_eq (w i),
    hw₂.trans (nonempty.intro $ isometry_sign_weighted_sum_squares' w hw₁)⟩

end real

-- The idea now is to restrict a degenerate quadratic form onto a smaller subspace 
-- such that it becomes nondegenerate.

-- def restrict_nezero (Q : quadratic_form R₁ M) : submodule R₁ M := 
-- { carrier := { v : M | v ≠ 0 → Q v ≠ 0 },
--   zero_mem' := by contradiction,
--   add_mem' := 
--     begin
--       intros x y hx hy hxy,
--       rw [← @associated_eq_self_apply R₁ _ _ _ _ _ _ _ _ _ (x + y),
--           add_left, add_right, add_right],
--       swap, apply_instance, swap, apply_instance,
--       by_cases h₁ : x = 0; by_cases h₂ : y = 0,
--       { exact false.elim (hxy (h₁.symm ▸ h₂.symm ▸ zero_add _)) },
--       { subst h₁, simp only [zero_left, zero_right, zero_add],
--         rw associated_eq_self_apply, exact hy h₂ },
--       { 

--       }

--     end,
--   smul_mem' := _ }



end quadratic_form