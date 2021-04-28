import linear_algebra.quadratic_form 
import data.complex.basic

/- 
Sylvester's law of inertia: 
- We would like to prove the complex version first: 
  A quadratic form `Q` over the field `ℂ` is isometric to a quadratic form 
  in the form
  ` ∑ xᵢ^2 `
-/

open_locale big_operators classical

namespace quadratic_form

open finset

variables {ι : Type*} [fintype ι]

noncomputable def weighted_sum_squared (w : ι → ℂ) : (ι → ℂ) → ℂ := 
  λ x, ∑ i : ι, w i * x i * x i

lemma weighted_sum_squared_smul {w : ι → ℂ} (a : ℂ) (x : ι → ℂ) : 
  weighted_sum_squared w (a • x) = a * a * weighted_sum_squared w x :=
begin
  simp only [weighted_sum_squared, algebra.id.smul_eq_mul, pi.smul_apply], 
  conv_rhs { rw [mul_assoc, mul_sum, mul_sum] },
  refine sum_congr rfl (λ _ _, by ring),
end

lemma weighted_sum_squared_polar_add_left {w : ι → ℂ} (x x' y : ι → ℂ) : 
  polar (weighted_sum_squared w) (x + x') y = 
  polar (weighted_sum_squared w) x y + polar (weighted_sum_squared w) x' y :=
begin
  simp_rw [weighted_sum_squared, polar, pi.add_apply],
  iterate 7 { rw ← sum_add_distrib <|> rw ← sum_sub_distrib },
  refine sum_congr rfl (λ _ _, by ring),
end

lemma weighted_sum_squared_polar_smul_left {w : ι → ℂ} (a : ℂ) (x y : ι → ℂ) : 
  polar (weighted_sum_squared w) (a • x) y = a • polar (weighted_sum_squared w) x y := 
begin
  simp_rw [weighted_sum_squared, polar, pi.add_apply, pi.smul_apply],
  iterate 4 { rw ← sum_add_distrib <|> rw ← sum_sub_distrib },
  simp_rw [smul_sum, smul_eq_mul], 
  refine sum_congr rfl (λ _ _, by ring),
end

lemma weighted_sum_squared_polar_add_right {w : ι → ℂ} (x y y' : ι → ℂ) : 
  polar (weighted_sum_squared w) x (y + y') = 
  polar (weighted_sum_squared w) x y + polar (weighted_sum_squared w) x y' :=
begin
  simp_rw [weighted_sum_squared, polar, pi.add_apply],
  iterate 7 { rw ← sum_add_distrib <|> rw ← sum_sub_distrib },
  refine sum_congr rfl (λ _ _, by ring),
end

lemma weighted_sum_squared_polar_smul_right {w : ι → ℂ} (a : ℂ) (x y : ι → ℂ) : 
  polar (weighted_sum_squared w) x (a • y) = a • polar (weighted_sum_squared w) x y := 
begin
  simp_rw [weighted_sum_squared, polar, pi.add_apply, pi.smul_apply],
  iterate 4 { rw ← sum_add_distrib <|> rw ← sum_sub_distrib },
  simp_rw [smul_sum, smul_eq_mul], 
  refine sum_congr rfl (λ _ _, by ring),
end

noncomputable def weighted_standard_form (w : ι → ℂ) : 
  quadratic_form ℂ (ι → ℂ) := 
{ to_fun := weighted_sum_squared w,
  to_fun_smul := weighted_sum_squared_smul,
  polar_add_left' := weighted_sum_squared_polar_add_left,
  polar_smul_left' := weighted_sum_squared_polar_smul_left,
  polar_add_right' := weighted_sum_squared_polar_add_right,
  polar_smul_right' := weighted_sum_squared_polar_smul_right }

end quadratic_form