module
public import MassShell
import all MassShell
public section

namespace MassShell.CompositionAndTransport.FreeShellRadial
noncomputable section
open scoped Distributions ContDiff

abbrev Operator := Module.End ℂ ScalarDistribution

def momentum (j : Fin 4) : Operator where
  toFun := smooth_times_distribution (coordinate_covector (.inr j)).contDiff
  map_add' _ _ := rfl
  map_smul' _ _ := by ext φ; rfl

def «partial» (d : Axis) : Operator where
  toFun := weak_derivative d
  map_add' A B := by ext φ; exact neg_add _ _
  map_smul' c A := by ext φ; change -(c * A _) = c * (-A _); ring

theorem momentum_commute (i j : Fin 4) : Commute (momentum i) (momentum j) := by
  apply LinearMap.ext
  intro U
  apply ContinuousLinearMap.ext
  intro φ
  apply congrArg U
  ext z
  change (φ z * _)*_ = (φ z * _)*_
  ring

theorem partial_commute (i j : Axis) : Commute («partial» i) («partial» j) := by
  apply LinearMap.ext
  intro U
  have h := lemma_weak_partials_commute i j (fun _ _ => U)
  exact congrArg (fun w : EnsembleDistribution => w 0 0) h

private def testMul (j : Fin 4) : PhaseTests →L[ℂ] PhaseTests :=
  TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (coordinate_covector (.inr j)).contDiff

private def testD (i : Axis) : PhaseTests →L[ℂ] PhaseTests :=
  TestFunction.lineDerivCLM ℂ (direction i)

private theorem test_leibniz (d : Axis) (j : Fin 4) (φ : PhaseTests) :
    testD d (testMul j φ) =
    testMul j (testD d φ) + (coordinate_covector (.inr j) (direction d)) • φ := by
  ext z
  change fderiv ℝ (fun x => φ x * coordinate_covector (.inr j) x) z (direction d) =
    fderiv ℝ φ z (direction d) * coordinate_covector (.inr j) z +
    coordinate_covector (.inr j) (direction d) * φ z
  rw [fderiv_fun_mul (φ.contDiff.differentiable (by simp) z) ((coordinate_covector (.inr j)).differentiableAt)]
  simp [mul_comm, add_comm]

theorem partial_mul (d : Axis) (j : Fin 4) :
    «partial» d * momentum j = momentum j * «partial» d +
      coordinate_covector (.inr j) (direction d) • (1 : Operator) := by
  apply LinearMap.ext
  intro U
  apply ContinuousLinearMap.ext
  intro φ
  change -U (testMul j (testD d φ)) =
    -U (testD d (testMul j φ)) + coordinate_covector (.inr j) (direction d) * U φ
  rw [test_leibniz, map_add, map_smul]
  simp only [smul_eq_mul]
  ring

theorem partial_x_commute (i j : Fin 4) :
    Commute («partial» (.inl i)) (momentum j) := by
  simpa [Commute, SemiconjBy, coordinate_covector, direction] using partial_mul (.inl i) j

theorem partial_p_mul (i j : Fin 4) :
    «partial» (.inr i) * momentum j =
      momentum j * «partial» (.inr i) + (if i = j then 1 else 0) := by
  by_cases h : i = j <;>
    simp [partial_mul, coordinate_covector, direction, h]

end
end MassShell.CompositionAndTransport.FreeShellRadial
