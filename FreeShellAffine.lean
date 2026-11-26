module
public import MassShell
import all MassShell

public section
namespace MassShell.CompositionAndTransport
noncomputable section
open TensorProduct
open scoped TensorProduct ContDiff
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000

private theorem canonical_tensor (F G : S) :
    pair_calculus canonical_symbol (F ⊗ₜ[ℂ] G) =
      ∑ i : Fin 4, (partial_map (.inr i) F ⊗ₜ[ℂ] partial_map (.inl i) G -
        partial_map (.inl i) F ⊗ₜ[ℂ] partial_map (.inr i) G) := by
  let inst : AddCommGroup PairSpace := TensorProduct.addCommGroup
  unfold canonical_symbol contraction
  rw [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sub, map_mul, map_mul]
  change (_ : Module.End ℂ PairSpace) _ - (_ : Module.End ℂ PairSpace) _ = _
  simp [pair_calculus, pair_partial]

private theorem constant_partial (i : Axis) (A : SpinMatrix) :
    partial_map i (constant_matrix A) = 0 := by
  apply Subtype.ext
  funext z r j
  simp [partial_map, directional, constant_matrix]

private theorem affine_square (m : ℝ) (F : S) :
    pair_calculus canonical_symbol (pair_calculus canonical_symbol (free_generator m ⊗ₜ[ℂ] F)) = 0 ∧
    pair_calculus canonical_symbol (pair_calculus canonical_symbol (F ⊗ₜ[ℂ] free_generator m)) = 0 := by
  constructor <;> simp [canonical_tensor, lemma_free_momentum_derivative,
    (show ∀ i, partial_map (.inl i) (free_generator m) = 0 from lemma_free_generator_momentum_only m),
    constant_partial, map_sum]

private theorem higher_smooth_free (m : ℝ) (n : ℕ) (F : S) :
    moyal_family (n+2) (free_generator m) F = 0 ∧
    moyal_family (n+2) F (free_generator m) = 0 := by
  have vanish (z : PairSpace) (hz : pair_calculus canonical_symbol (pair_calculus canonical_symbol z) = 0) :
      tensor_operator (moyal_polynomial (n+2)) z = 0 := by
    simp [tensor_operator, moyal_polynomial, pow_add, pow_two, hz]
  exact ⟨vanish _ (affine_square m F).1, vanish _ (affine_square m F).2⟩

/-- All weak Moyal coefficients of order two or above vanish for the free pencil. -/
theorem free_distribution_moyal_higher (m : ℝ) (n : ℕ) (side : ProductSide) (W : EnsembleDistribution) :
    distribution_moyal_coefficient side (n+2) (free_generator m) W = 0 := by
  apply congrFun (g := fun _ => (0 : EnsembleDistribution)) _ W
  apply lemma_weak_action_ext (lemma_moyal_action_is_weak side (n+2) (free_generator m))
  · intro i j φ
    exact test_pairing.range.zero_mem
  · intro F
    rw [corollary_distribution_action_of_selected_product]
    cases side <;> simp [(higher_smooth_free m n F).1, (higher_smooth_free m n F).2]
/-- The first free Moyal coefficient is a signed spacetime derivative on either side. -/
theorem free_distribution_moyal_first (m : ℝ) (side : ProductSide) (W : EnsembleDistribution) :
    distribution_moyal_coefficient side 1 (free_generator m) W =
      (match side with | .generator_left => Complex.I / 2 | .generator_right => -(Complex.I / 2)) •
        ∑ i : Fin 4, mixed_multiplication side (constant_matrix (gamma_axis i))
          (distribution_directional (.inl i) W) := by
  let c : ℂ := match side with | .generator_left => Complex.I / 2 | .generator_right => -(Complex.I / 2)
  have pos (i : Fin 4) : partial_map (.inl i) (free_generator m) = 0 :=
    lemma_free_generator_momentum_only m i
  apply congrFun (g := fun U => c • ∑ i : Fin 4, mixed_multiplication side
    (constant_matrix (gamma_axis i)) (distribution_directional (.inl i) U)) _ W
  apply lemma_weak_action_ext (lemma_moyal_action_is_weak side 1 (free_generator m))
    (lemma_weak_action_smul c (lemma_weak_action_sum _ _ (fun i _ =>
      lemma_weak_action_comp (lemma_smooth_multiplier_is_weak side (constant_matrix (gamma_axis i)))
        (lemma_distribution_derivative_is_weak (.inl i)))))
  intro F
  rw [corollary_distribution_action_of_selected_product]
  simp only [lemma_distribution_derivative_extends_smooth, lemma_mixed_multiplication_extends,
    ← map_sum, ← map_smul]
  apply congrArg regular_ensemble
  cases side <;> apply Subtype.ext <;> rw [lemma_family_agrees] <;>
    simp [c, moyal_coefficient, lemma_canonical_poisson_on_fields, pos, lemma_free_momentum_derivative,
      show ∀ i, smooth_directional i F = partial_map i F from fun _ => rfl]

private theorem pencil_entries (p : FourMomentum) (a b : Fin 4) :
    four_component_factor p a b = ∑ i : Fin 4, (gamma_axis i a b) * (p i : ℂ) := by
  have decomp : (∑ i : Fin 4, p i • Pi.single i (1:ℝ)) = p := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have expand := congrArg four_component_factor decomp
  rw [map_sum] at expand
  simp only [map_smul] at expand
  rw [← expand]
  simp [gamma_axis, Matrix.sum_apply, Complex.real_smul, mul_comm]

private def componentTest {f : PhasePoint → ℂ} (hf : ContDiff ℝ ∞ f) :
    PhaseTests →L[ℂ] PhaseTests :=
  TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) hf

theorem free_generator_entry_smooth (m : ℝ) (a b : Fin 4) :
    ContDiff ℝ ∞ (fun z => (free_generator m).val z a b) :=
  (free_generator m).property a b

theorem free_generator_entry_multiplier (m : ℝ) (a b : Fin 4) (U : ScalarDistribution) :
    smooth_times_distribution (free_generator_entry_smooth m a b) U =
    (∑ i : Fin 4, gamma_axis i a b •
      smooth_times_distribution (coordinate_covector (.inr i)).contDiff U) -
      (m : ℂ) • ((1 : SpinMatrix) a b • U) := by
  ext φ
  have testEq : componentTest (free_generator_entry_smooth m a b) φ =
      (∑ i : Fin 4, gamma_axis i a b • componentTest (coordinate_covector (.inr i)).contDiff φ)
      - (m : ℂ) • ((1 : SpinMatrix) a b • φ) := by
    ext z
    simp only [Fin.sum_univ_four]
    change φ z * ((four_component_factor z.2 - m • (1 : SpinMatrix)) a b) =
      (((gamma_axis 0 a b * (φ z * (z.2 0 : ℂ)) + gamma_axis 1 a b * (φ z * (z.2 1 : ℂ))) +
        gamma_axis 2 a b * (φ z * (z.2 2 : ℂ))) + gamma_axis 3 a b * (φ z * (z.2 3 : ℂ))) -
      (m : ℂ) * ((1 : SpinMatrix) a b * φ z)
    rw [Matrix.sub_apply, Matrix.smul_apply, pencil_entries, Fin.sum_univ_four]
    simp only [Complex.real_smul]
    ring
  have h := congrArg (fun ψ => U ψ) testEq
  simpa [smooth_times_distribution, componentTest, Finset.sum_apply] using h

theorem constant_entry_multiplier (A : SpinMatrix) (a b : Fin 4) (U : ScalarDistribution) :
    smooth_times_distribution (f := fun _ : PhasePoint => A a b) contDiff_const U = A a b • U := by
  ext φ
  change U (componentTest _ φ) = A a b * U φ
  have h : componentTest (f := fun _ : PhasePoint => A a b) contDiff_const φ = A a b • φ := by
    ext z
    change φ z * A a b = A a b * φ z
    ring
  rw [h, map_smul]
  rfl

/-- The coefficient of each positive formal order uses only that state coefficient
and the spacetime derivatives of its predecessor. -/
theorem free_distribution_product_succ (s : ProductSide) (m : ℝ)
    (W : ℕ → EnsembleDistribution) (n : ℕ) :
    distribution_product_order s (n+1) (free_generator m) W =
      mixed_multiplication s (free_generator m) (W (n+1)) +
      distribution_moyal_coefficient s 1 (free_generator m) (W n) := by
  unfold distribution_product_order
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp [free_distribution_moyal_higher, lemma_distribution_order_zero]
  abel

end
end MassShell.CompositionAndTransport
