import linear_algebra.quadratic_form 
import data.complex.basic
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

namespace quadratic_form

open finset bilin_form

def isometry_of_comp_linear_equiv (Q : quadratic_form R M) (f : M₁ ≃ₗ[R] M) : 
  Q.isometry (Q.comp (f : M₁ →ₗ[R] M)) := 
{ map_app' := 
  begin
    intro,  
    simp only [comp_apply, linear_equiv.coe_coe, linear_equiv.to_fun_eq_coe, 
               linear_equiv.apply_symm_apply, f.apply_symm_apply],
  end, .. f.symm }

noncomputable def isometry_of_is_basis' (Q : quadratic_form R M) 
  (hv₁ : is_basis R v) : quadratic_form R (ι → R) := Q.comp hv₁.equiv_fun.symm

@[simp]
lemma isometry_of_is_basis_apply (Q : quadratic_form R M) (hv₁ : is_basis R v) 
  (w : ι → R) : Q.isometry_of_is_basis' hv₁ w = Q (∑ i : ι, w i • v i) := 
by { rw ← hv₁.equiv_fun_symm_apply, refl }

noncomputable def isometry_of_is_basis (Q : quadratic_form R M) (hv₁ : is_basis R v) : 
  isometry Q (Q.isometry_of_is_basis' hv₁) :=
isometry_of_comp_linear_equiv Q hv₁.equiv_fun.symm

lemma isometry_of_is_Ortho_apply (Q : quadratic_form R M) (hv₁ : is_basis R v) 
  (hv₂ : (associated Q).is_Ortho v) (w : ι → R) : 
  Q.isometry_of_is_basis' hv₁ w = ∑ i : ι, associated Q (v i) (v i) * w i * w i :=
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

lemma equivalent_weighted_sum_squares_of_nondegenerate 
  (Q : quadratic_form K V) (hQ : (associated Q).nondegenerate) : 
  ∃ w : fin (finite_dimensional.finrank K V) → K, 
    equivalent Q (weighted_sum_squares w) :=
begin
  obtain ⟨v, hv₁, hv₂⟩ := exists_orthogonal_basis hQ associated_is_sym,
  refine ⟨λ i, associated Q (v i) (v i), _⟩,
  refine nonempty.intro _,
  convert Q.isometry_of_is_basis hv₂,
  ext w, 
  rw [isometry_of_is_Ortho_apply Q hv₂ hv₁], refl,
end

-- Basis lemma: PR
lemma smul_is_basis {v : ι → M} (hv : is_basis R v) 
  {w : ι → R} (hw : ∀ i : ι, w i ≠ 0) : is_basis R (λ i, w i • v i) := 
begin
  sorry
end

section complex

noncomputable instance two_invertible : invertible (2 : ℂ) := 
{ inv_of := 2⁻¹,
  inv_of_mul_self := by norm_num,
  mul_inv_of_self := by norm_num }
  
def isometry_sum_squares (w : ι → ℂ) (hw : ∀ i : ι, w i ≠ 0) : 
  isometry (weighted_sum_squares w) (weighted_sum_squares (λ _, 1 : ι → ℂ)) := 
begin
  -- have hw' : ∀ i : ι, (w i).sqrt⁻¹ ≠ 0, sorry,
  -- have := smul_is_basis (pi.is_basis_fun ℂ ι) hw', 
  -- dsimp at this,
  -- suffices : weighted_sum_squares (λ (_x : ι), 1 : ι → ℂ) 
  --   = (weighted_sum_squares w).isometry_of_is_basis' this, sorry,
  -- convert (weighted_sum_squares w).isometry_of_is_basis this,
  -- ext1 v,
  -- rw [isometry_of_is_basis_apply, weighted_sum_squares_apply, 
  --     weighted_sum_squares_apply],
  -- refine sum_congr rfl _,
  -- intros j _, 
  -- have : ∑ (i : ι), v i • ((linear_map.std_basis ℂ (λ (i : ι), ℂ) i) 1) j = 1,
  -- have hsum := @smul_sum _ (ι → ℂ) _ _ _ _ (v j) 
    -- (λ i, ((w i).sqrt)⁻¹ • (linear_map.std_basis ℂ (λ (i : ι), ℂ) i) 1) univ,
  -- dsimp at hsum,
  sorry
end

end complex

end quadratic_form