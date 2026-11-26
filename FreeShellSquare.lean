module
public import FreeShellSeries
public import FreeShellRecursion
import all FreeShellRecursion
import all FreeShellSeries
import all FreeShellDirac
public section
namespace MassShell.FreeSeries
open CompositionAndTransport CompositionAndTransport.FreeShellRadial FreeDirac
open scoped MassShell.FreeSeries
noncomputable section
set_option synthInstance.maxHeartbeats 350000
set_option maxHeartbeats 2000000

def polyShell : Poly := squareForm px
def polyTransport : Poly := px 0*dx 0 - px 1*dx 1 - px 2*dx 2 - px 3*dx 3
def polyWave : Poly := MvPolynomial.C (1/4 : ℂ) * squareForm dx

theorem square_bopp (c : ℂ) (hc : c^2 = -(1/4)) :
    squareForm (bopp c) = polyShell + MvPolynomial.C (2*c) * h * polyTransport - h^2 * polyWave := by
  have co : (MvPolynomial.C c : Poly)^2 = -MvPolynomial.C (1/4 : ℂ) := by
    rw [← map_pow, hc, map_neg]
  simp only [bopp,polyShell,polyTransport,polyWave,squareForm,map_mul,map_ofNat]
  linear_combination (norm := ring) h^2 * (dx 0^2 - dx 1^2 - dx 2^2 - dx 3^2) * co

theorem polyShell_apply (u : Seq) (n : ℕ) : (polyShell • u) n = shellOp (u n) := by
  simp only [polyShell, squareForm, pow_two, sub_smul, mul_smul, Pi.sub_apply, px_apply]
  rfl

theorem polyTransport_apply (u : Seq) (n : ℕ) : (polyTransport • u) n = transportOp (u n) := by
  simp only [polyTransport, sub_smul, mul_smul, Pi.sub_apply, px_apply, dx_apply]
  rfl

theorem polyWave_apply (u : Seq) (n : ℕ) : (polyWave • u) n = waveOp (u n) := by
  simp only [polyWave, squareForm, pow_two, sub_smul, mul_smul, Pi.sub_apply, C_apply, dx_apply]
  rfl

/-- The radial recursion solves both signs of the squared Dirac equation. -/
theorem bopp_scalar_solution (m c : ℂ) (hc : c^2 = -(1/4)) (u : Seq)
    (tr : ∀ n, transportOp (u n) = 0)
    (h0 : shellOp (u 0) = m^2 • u 0) (h1 : shellOp (u 1) = m^2 • u 1)
    (step : ∀ n, shellOp (u (n+2)) = m^2 • u (n+2) + waveOp (u n)) :
    (squareForm (bopp c) - (MvPolynomial.C m : Poly)^2) • u = 0 := by
  have ht : polyTransport • u = 0 := funext fun n => (polyTransport_apply u n).trans (tr n)
  rw [square_bopp c hc, sub_smul, sub_smul, add_smul, mul_smul, ht, smul_zero, add_zero,
    ← map_pow, pow_two h, mul_smul, mul_smul]
  funext n
  simp only [Pi.sub_apply, polyShell_apply, C_apply, Pi.zero_apply]
  cases n with
  | zero => rw [h_zero, sub_zero, h0, sub_self]
  | succ n =>
    cases n with
    | zero => rw [h_succ, h_zero, sub_zero, h1, sub_self]
    | succ n => rw [h_succ,h_succ,polyWave_apply,step]; abel

end
end MassShell.FreeSeries
