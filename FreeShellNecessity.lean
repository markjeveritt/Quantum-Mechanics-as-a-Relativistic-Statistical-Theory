module
public import FreeShellBridge
public import FreeShellSquare
import all MassShell
import all FreeShellDirac
import all FreeShellSeries
import all FreeShellBridge

public section

namespace MassShell.FreeSeries
open MassShell.FreeDirac CompositionAndTransport CompositionAndTransport.FreeShellBridge
open CompositionAndTransport.FreeShellRadial
open scoped MassShell.FreeSeries
noncomputable section
set_option synthInstance.maxHeartbeats 350000
set_option maxHeartbeats 2000000

/-- Any formal two-sided free solution obeys the uncorrected transport equation
coefficient by coefficient. It follows by subtracting its squared equations. -/
theorem solution_transport (m : ℝ) (W : ℕ → EnsembleDistribution)
    (solution : ∀ n side, distribution_product_order side n (free_generator m) W = 0) :
    ∀ n i j, transportOp (W n i j) = 0 := by
  let u : Mat Seq := fun i j n => W n i j
  let mass : Poly := MvPolynomial.C (m : ℂ)
  have eqn (s : ProductSide) : act s (pencil (bopp (sign s)) - mass • 1) u = 0 := by
    funext i j n
    exact congrArg (fun w : EnsembleDistribution => w i j)
      ((coefficient_action m s u n).trans (solution n s))
  have left := eqn .generator_left
  have right := eqn .generator_right
  let l := bopp (sign .generator_left)
  let r := bopp (sign .generator_right)
  change leftAct (pencil l - mass • 1) u = 0 at left
  change rightAct (pencil r - mass • 1) u = 0 at right
  have l2 : (squareForm l - mass^2) • u = 0 := by
    rw [← left_scalar, ← (shifted_factor l mass).2, ← left_comp, left]
    ext i j
    simp [leftAct]
  have r2 : (squareForm r - mass^2) • u = 0 := by
    rw [← right_scalar, ← (shifted_factor r mass).1, ← right_comp, right]
    ext i j
    simp [rightAct]
  have diff : squareForm l - squareForm r = MvPolynomial.C (2 * Complex.I) * h * polyTransport := by
    have hc : (Complex.I / 2)^2 = -(1/4 : ℂ) := by rw [div_pow, Complex.I_sq]; norm_num
    have hd : (-(Complex.I/2))^2 = -(1/4 : ℂ) := by simpa using hc
    dsimp only [l, r, sign]
    rw [square_bopp _ hc, square_bopp _ hd]
    rw [show 2*(Complex.I/2) = Complex.I by ring,
      show 2*(-(Complex.I/2)) = -Complex.I by ring, map_neg, map_mul, map_ofNat]
    ring
  intro n i j
  have lentry : (squareForm l - mass^2) • (u i j) = 0 :=
    congrArg (fun w : Mat Seq => w i j) l2
  have rentry : (squareForm r - mass^2) • (u i j) = 0 :=
    congrArg (fun w : Mat Seq => w i j) r2
  have heq : (MvPolynomial.C (2 * Complex.I) * h * polyTransport) • (u i j) = 0 := by
    rw [← diff, show squareForm l - squareForm r =
      (squareForm l - mass^2) - (squareForm r - mass^2) by ring, sub_smul, lentry, rentry, sub_zero]
  have hentry := congrFun heq (n+1)
  rw [mul_smul, mul_smul, C_apply, h_succ, polyTransport_apply] at hentry
  ext φ
  have ht := DFunLike.congr_fun hentry φ
  change (2 * Complex.I) * transportOp (W n i j) φ = 0 at ht
  exact (mul_eq_zero.mp ht).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)

end
end MassShell.FreeSeries
