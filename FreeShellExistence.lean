module
public import FreeShellSquare
public import FreeShellBridge
public import FreeShellLeading
public import FreeShellNecessity
import all FreeShellBridge
import all FreeShellDirac

/-! All-order existence for general compatible massive free data on full phase
space. The assumptions are the ordinary two-sided Dirac equations and transport
of the given leading distribution. -/

public section
namespace MassShell.CompositionAndTransport
open FreeDirac FreeSeries FreeShellBridge FreeShellRadial
open scoped MassShell.FreeSeries
noncomputable section
set_option synthInstance.maxHeartbeats 350000
set_option maxHeartbeats 2000000

private theorem act_smul (s : ProductSide) (P : Mat Poly) (a : Poly) (u : Mat Seq) :
    act s P (a • u) = a • act s P u := by
  cases s <;> funext i j <;> simp only [act,leftAct,rightAct, Matrix.smul_apply, Finset.smul_sum] <;>
    apply Finset.sum_congr rfl <;> intros <;> apply smul_comm

/-- For nonzero mass, a leading phase-space distribution admits a formal free
continuation exactly when it obeys the two ordinary shell equations and free
transport. Both products in the conclusion are the original weak Moyal actions. -/
theorem free_continuation_iff (m : ℝ) (hm : m ≠ 0) (F : EnsembleDistribution) :
    (∃ W : ℕ → EnsembleDistribution, W 0 = F ∧
      ∀ n side, distribution_product_order side n (free_generator m) W = 0) ↔
    (∀ side, mixed_multiplication side (free_generator m) F = 0) ∧
    ∀ i j, transportOp (F i j) = 0 := by
  constructor
  · rintro ⟨W, rfl, sol⟩
    exact ⟨fun s => (order_zero m s W).symm.trans (sol 0 s), solution_transport m W sol 0⟩
  · rintro ⟨shell, tr⟩
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    choose u u0 ut us0 us1 us using fun i j => exists_free_scalar_series ((m : ℂ)^2)
      (pow_ne_zero _ hm') (F i j) (shell_of_left_free m F (shell .generator_left) i j) (tr i j)
    let mass : Poly := MvPolynomial.C (m : ℂ)
    let l := bopp (sign .generator_left)
    let r := bopp (sign .generator_right)
    have squared (s : ProductSide) : (squareForm (bopp (sign s)) - mass^2) • (u : Mat Seq) = 0 := by
      have hc : (sign s)^2 = -(1/4) := by
        cases s <;> norm_num [sign, div_pow, Complex.I_sq]
      funext i j
      exact bopp_scalar_solution m (sign s) hc (u i j) (ut i j) (us0 i j) (us1 i j) (us i j)
    let projected := leftAct (pencil l + mass • 1) (rightAct (pencil r + mass • 1) u)
    have both := lift_two_sided l r mass u (squared .generator_left) (squared .generator_right)
    have eqzero (s : ProductSide) : act s (pencil (bopp (sign s)) - mass • 1) projected = 0 := by
      cases s with
      | generator_left => exact both.1
      | generator_right => exact both.2
    have first : coeff u 0 = F := funext fun i => funext (u0 i)
    have p0 : coeff projected 0 = (4 * (m : ℂ)^2) • F := by
      exact (numerator_head_projected m u (fun s => by rw [first]; exact shell s)).trans (congrArg ((4 * (m : ℂ)^2) • ·) first)
    let a : ℂ := (4*(m:ℂ)^2)⁻¹
    let w : Mat Seq := (MvPolynomial.C a : Poly) • projected
    refine ⟨coeff w, ?_, ?_⟩
    · have sw : coeff w 0 = a • coeff projected 0 := by
        funext i j
        exact C_apply a (projected i j) 0
      rw [sw, p0, smul_smul, inv_mul_cancel₀ (mul_ne_zero (by norm_num) (pow_ne_zero _ hm')), one_smul]
    · intro n s
      rw [← coefficient_action]
      change coeff (act s (pencil (bopp (sign s)) - mass • 1) ((MvPolynomial.C a : Poly) • projected)) n = 0
      rw [act_smul, eqzero]
      funext i j
      change ((MvPolynomial.C a : Poly) • (0 : Seq)) n = 0
      rw [C_apply]
      ext φ
      change a * 0 = 0
      exact mul_zero a

end
end MassShell.CompositionAndTransport
