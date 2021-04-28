import linear_algebra.quadratic_form 
import data.complex.basic

/- 
The idea is we would like to expand the API for `quadratic_form.equivalent`.
  Given a orthogonal basis wrt. some quadratic form, we should have a equivalent 
form. This will be constructed.

`def is_basis.equiv_fun : M ≃ₗ[R] (ι → R) :=`
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

noncomputable def isometry_of_is_basis (Q : quadratic_form R M) 
  (hv₁ : is_basis R v) : quadratic_form R (ι → R) := Q.comp hv₁.equiv_fun.symm

@[simp]
lemma isometry_of_is_basis_apply (Q : quadratic_form R M) (hv₁ : is_basis R v) 
  (w : ι → R) : Q.isometry_of_is_basis hv₁ w = Q (∑ i : ι, w i • v i) := 
by { rw ← hv₁.equiv_fun_symm_apply, refl }

noncomputable def isometry_of_is_basis' (Q : quadratic_form R M) (hv₁ : is_basis R v) : 
  isometry Q (Q.isometry_of_is_basis hv₁) :=
isometry_of_comp_linear_equiv Q hv₁.equiv_fun.symm

lemma isometry_of_is_Ortho_apply (Q : quadratic_form R M) (hv₁ : is_basis R v) 
  (hv₂ : (associated Q).is_Ortho v) (w : ι → R) : 
  Q.isometry_of_is_basis hv₁ w = ∑ i : ι, associated Q (v i) (v i) * w i * w i :=
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

end quadratic_form