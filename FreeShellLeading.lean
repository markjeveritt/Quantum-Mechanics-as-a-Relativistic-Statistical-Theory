module
public import FreeShellRecursion
import all MassShell
import all FreeShellRadial
import all FreeShellRecursion
public section
namespace MassShell.CompositionAndTransport.FreeShellRadial
open scoped ContDiff
noncomputable section

private theorem left_mul_comp (F G : S) (U : EnsembleDistribution) :
    left_multiply (F*G) U = left_multiply F (left_multiply G U) := by
  apply congrFun (g := fun V => left_multiply F (left_multiply G V)) _ U
  apply lemma_weak_action_ext (lemma_smooth_multiplier_is_weak .generator_left (F*G))
    (lemma_weak_action_comp (lemma_smooth_multiplier_is_weak .generator_left F)
      (lemma_smooth_multiplier_is_weak .generator_left G))
  intro X
  simp [lemma_mixed_multiplication_extends, mul_assoc]

private def multTest {f : PhasePoint → ℂ} (hf : ContDiff ℝ ∞ f) : PhaseTests →L[ℂ] PhaseTests :=
  TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) hf

private def pTest (i : Fin 4) := multTest (coordinate_covector (.inr i)).contDiff

private theorem product_entry (m : ℝ) (r k : Fin 4) (U : ScalarDistribution) :
    smooth_times_distribution ((free_generator (-m)*free_generator m).property r k) U =
      (1 : SpinMatrix) r k • (shellOp U - (m : ℂ)^2 • U) := by
  ext φ
  have fact (p : Coordinates) :
      (four_component_factor p - (-m) • 1)*(four_component_factor p - m • 1) =
        (minkowski_pairing p p - m^2) • (1 : SpinMatrix) := by
    simpa only [neg_smul, sub_neg_eq_add, ← sub_eq_add_neg, neg_sq] using
      corollary_mass_shifted_factorisation four_component_factor theorem_four_components_are_sufficient p (-m)
  have tests : multTest ((free_generator (-m)*free_generator m).property r k) φ =
      (1 : SpinMatrix) r k • (pTest 0 (pTest 0 φ) - pTest 1 (pTest 1 φ) -
      pTest 2 (pTest 2 φ) - pTest 3 (pTest 3 φ) - (m:ℂ)^2 • φ) := by
    ext z
    change φ z * ((four_component_factor z.2 - (-m) • 1)*(four_component_factor z.2 - m • 1)) r k =
      (1 : SpinMatrix) r k * (φ z * (z.2 0 : ℂ) * (z.2 0 : ℂ) -
        φ z * (z.2 1 : ℂ) * (z.2 1 : ℂ) - φ z * (z.2 2 : ℂ) * (z.2 2 : ℂ) -
        φ z * (z.2 3 : ℂ) * (z.2 3 : ℂ) - (m:ℂ)^2 * φ z)
    rw [fact, Matrix.smul_apply, Complex.real_smul]
    simp only [minkowski_pairing, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  have h := congrArg (fun ψ => U ψ) tests
  change U (multTest _ φ) = (1 : SpinMatrix) r k * (U (pTest 0 (pTest 0 φ)) -
    U (pTest 1 (pTest 1 φ)) - U (pTest 2 (pTest 2 φ)) - U (pTest 3 (pTest 3 φ)) -
    (m : ℂ)^2 * U φ)
  simpa using h

/-- The ordinary left Dirac equation implies the scalar mass-shell constraint
on each distribution entry. -/
theorem shell_of_left_free (m : ℝ) (W : EnsembleDistribution)
    (left : left_multiply (free_generator m) W = 0) (r t : Fin 4) :
    shellOp (W r t) = (m : ℂ)^2 • W r t := by
  have zero : left_multiply (free_generator (-m)*free_generator m) W = 0 := by
    rw [left_mul_comp, left]
    ext a b φ
    simp [left_multiply, mixed_multiplication, smooth_times_distribution]
  have h := congrArg (fun V : EnsembleDistribution => V r t) zero
  change (∑ k, smooth_times_distribution ((free_generator (-m)*free_generator m).property r k) (W k t)) = 0 at h
  have z (T : ScalarDistribution) : (0 : ℂ) • T = 0 := by ext φ; change 0 * T φ = 0; ring
  simp [product_entry, Matrix.one_apply, ite_smul, z] at h
  exact sub_eq_zero.mp h

end
end MassShell.CompositionAndTransport.FreeShellRadial
