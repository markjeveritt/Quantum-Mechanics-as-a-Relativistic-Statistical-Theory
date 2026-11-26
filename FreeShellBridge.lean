module
public import FreeShellAffine
public import FreeShellSeries
public import FreeShellDirac
public import FreeShellRadial
import all MassShell
import all FreeShellRadial
import all FreeShellDirac
import all FreeShellSeries
public section
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace MassShell.CompositionAndTransport.FreeShellBridge
noncomputable section
open FreeShellRadial
open scoped ContDiff Distributions

private theorem generator_entry (m : ℝ) (r s : Fin 4) (U : ScalarDistribution) :
    smooth_times_distribution ((free_generator m).property r s) U =
      (∑ i : Fin 4, gamma_axis i r s • momentum i U) -
      ((m : ℂ) * (1 : SpinMatrix) r s) • U := by
  have prod : (m:ℂ) • ((1 : SpinMatrix) r s • U) =
      ((m:ℂ) * (1 : SpinMatrix) r s) • U := by
    ext φ
    change (m:ℂ) * ((1:SpinMatrix) r s * U φ) = ((m:ℂ) * (1:SpinMatrix) r s) * U φ
    ring
  have hh := free_generator_entry_multiplier m r s U
  rw [prod] at hh
  convert hh using 1
  rfl

private theorem gamma_entry (i : Fin 4) (r s : Fin 4) (U : ScalarDistribution) :
    smooth_times_distribution ((constant_matrix (gamma_axis i)).property r s) U =
    gamma_axis i r s • U :=
  constant_entry_multiplier (gamma_axis i) r s U

theorem order_zero (m : ℝ) (s : ProductSide) (W : ℕ → EnsembleDistribution) :
    distribution_product_order s 0 (free_generator m) W =
      mixed_multiplication s (free_generator m) (W 0) := by
  simp [distribution_product_order,lemma_distribution_order_zero]

theorem order_succ (m : ℝ) (s : ProductSide) (W : ℕ → EnsembleDistribution) (n : ℕ) :
    distribution_product_order s (n+1) (free_generator m) W =
      mixed_multiplication s (free_generator m) (W (n+1)) +
      distribution_moyal_coefficient s 1 (free_generator m) (W n) :=
  free_distribution_product_succ s m W n

open MassShell.FreeSeries MassShell.FreeDirac
open scoped MassShell.FreeSeries
local instance : Module ℂ ℂ := Algebra.toModule
local instance : Module ℂ ScalarDistribution := ContinuousLinearMap.module

def coeff (u : Mat Seq) (n : ℕ) : EnsembleDistribution := fun r s => u r s n
def sign : ProductSide → ℂ
  | .generator_left => Complex.I/2
  | .generator_right => -(Complex.I/2)

def act (s : ProductSide) (P : Mat Poly) (u : Mat Seq) : Mat Seq :=
  match s with
  | .generator_left => leftAct P u
  | .generator_right => rightAct P u

private theorem diag_entry (m : ℂ) (r s : Fin 4) :
    ((MvPolynomial.C m : Poly) • (1 : Mat Poly)) r s =
    MvPolynomial.C (m * (1 : SpinMatrix) r s) := by
  by_cases h : r=s <;> simp [Matrix.one_apply, h]

private theorem entry_zero (m : ℝ) (c : ℂ) (r s : Fin 4) (v : Seq) :
    (((pencil (bopp c) - (MvPolynomial.C (m:ℂ) : Poly) • 1) r s) • v) 0 =
      smooth_times_distribution ((free_generator m).property r s) (v 0) := by
  have hz : c • (0 : ScalarDistribution) = 0 := by ext φ; change c * 0 = 0; ring
  rw [generator_entry]
  simp only [Matrix.sub_apply, diag_entry, pencil_entries, sub_smul, Pi.sub_apply,
    C_apply, Finset.sum_smul, Finset.sum_apply, MvPolynomial.algebraMap_eq, mul_smul,
    bopp, add_smul, Pi.add_apply, C_apply, px_apply, h_zero, hz, add_zero]

private theorem entry_succ (m : ℝ) (c : ℂ) (r s : Fin 4) (v : Seq) (n : ℕ) :
    (((pencil (bopp c) - (MvPolynomial.C (m:ℂ) : Poly) • 1) r s) • v) (n+1) =
      smooth_times_distribution ((free_generator m).property r s) (v (n+1)) +
      c • (∑ i : Fin 4, gamma_axis i r s • «partial» (.inl i) (v n)) := by
  rw [generator_entry]
  simp only [Matrix.sub_apply, diag_entry, pencil_entries, sub_smul, Pi.sub_apply,
    C_apply, Finset.sum_smul, Finset.sum_apply, MvPolynomial.algebraMap_eq, mul_smul,
    bopp, add_smul, Pi.add_apply, C_apply, px_apply, h_succ, dx_apply]
  apply ContinuousLinearMap.ext
  intro φ
  simp only [add_apply, sub_apply,
    smul_apply, sum_apply, smul_eq_mul,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  ring_nf
  simp [mul_left_comm, mul_comm, mul_assoc]
  abel

theorem coefficient_action (m : ℝ) (s : ProductSide) (u : Mat Seq) (n : ℕ) :
    coeff (act s (pencil (bopp (sign s)) - (MvPolynomial.C (m:ℂ) : Poly) • 1) u) n =
      distribution_product_order s n (free_generator m) (coeff u) := by
  cases n with
  | zero =>
    rw [order_zero]
    cases s <;> funext a b <;>
      simp only [coeff, act, leftAct, rightAct, Finset.sum_apply, entry_zero,
        mixed_multiplication, Matrix.of_apply]
  | succ n =>
    rw [order_succ, free_distribution_moyal_first]
    cases s <;> funext a b <;>
      simp only [coeff, act, leftAct, rightAct, Finset.sum_apply, entry_succ,
        mixed_multiplication, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.sum_apply, Finset.sum_add_distrib, ← Finset.smul_sum, gamma_entry, sign] <;>
      congr 2 <;> rw [Finset.sum_comm] <;> rfl

private theorem act_add (s : ProductSide) (A B : Mat Poly) (u : Mat Seq) :
    act s (A+B) u = act s A u + act s B u := by
  cases s <;> funext r t <;>
    simp only [act, leftAct, rightAct, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem head_numerator (m : ℝ) (s : ProductSide) (u : Mat Seq) :
    coeff (act s (pencil (bopp (sign s)) + (MvPolynomial.C (m:ℂ) : Poly) • 1) u) 0 =
      mixed_multiplication s (free_generator m) (coeff u 0) + (2 * (m:ℂ)) • coeff u 0 := by
  let a : Poly := MvPolynomial.C (m:ℂ)
  let K := pencil (bopp (sign s))
  have mat : K + a • 1 = (K - a • 1) + (MvPolynomial.C (2*(m:ℂ)) : Poly) • 1 := by
    rw [two_mul, map_add, add_smul]
    dsimp [a]
    abel
  change coeff (act s (K+a • 1) u) 0 = _
  rw [mat, act_add]
  have scalar : act s ((MvPolynomial.C (2*(m:ℂ)) : Poly) • 1) u =
      (MvPolynomial.C (2*(m:ℂ)) : Poly) • u := by
    cases s <;> first | apply left_scalar | apply right_scalar
  rw [scalar]
  have e := (coefficient_action m s u 0).trans (order_zero m s (coeff u))
  funext r t
  have et := congrArg (fun w : EnsembleDistribution => w r t) e
  change (act s (K - a • 1) u r t) 0 + ((MvPolynomial.C (2*(m:ℂ)) : Poly) • u r t) 0 = _
  rw [C_apply]
  exact congrArg (· + (2*(m:ℂ)) • u r t 0) et

private theorem mixed_smul (s : ProductSide) (H : S) (c : ℂ) (F : EnsembleDistribution) :
    mixed_multiplication s H (c • F) = c • mixed_multiplication s H F := by
  cases s <;> funext r t <;>
    simp only [mixed_multiplication, Matrix.of_apply, Matrix.smul_apply, Finset.smul_sum] <;>
    apply Finset.sum_congr rfl <;> intros <;> ext φ <;> rfl

theorem numerator_head_projected (m : ℝ) (u : Mat Seq)
    (classical_shell : ∀ s, mixed_multiplication s (free_generator m) (coeff u 0) = 0) :
    coeff (act .generator_left (pencil (bopp (sign .generator_left)) +
      (MvPolynomial.C (m:ℂ) : Poly) • 1) (act .generator_right
      (pencil (bopp (sign .generator_right)) + (MvPolynomial.C (m:ℂ) : Poly) • 1) u)) 0 =
        (4 * (m:ℂ)^2) • coeff u 0 := by
  rw [head_numerator, head_numerator, classical_shell, zero_add, mixed_smul,
    classical_shell]
  ext r t φ
  change (2*(m:ℂ)) * 0 + (2*(m:ℂ)) * ((2*(m:ℂ)) * _) = (4*(m:ℂ)^2) * _
  ring

end
end MassShell.CompositionAndTransport.FreeShellBridge
