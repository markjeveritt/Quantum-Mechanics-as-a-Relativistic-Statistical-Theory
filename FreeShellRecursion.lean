module

public import FreeShellRadial
import all MassShell
import all FreeShellRadial

/-! Formal even-order correction of a transported leading distribution on a massive
shell. Here K multiplies by p², R is minus one half of the momentum Euler operator,
and B is one quarter of the spacetime wave operator. The proof takes place in the
subspace of data satisfying transport. -/

public section

namespace MassShell.FreeRecursion

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private noncomputable def next (R B : Module.End ℂ V) (a : ℂ) (n : ℕ) (v : V) : V :=
  (a * (n+1 : ℂ))⁻¹ • (R (B v) - (n : ℂ) • B v)

private theorem scaled_next (R B : Module.End ℂ V) {a : ℂ} (ha : a ≠ 0)
    (n : ℕ) (v : V) :
    (a * (n+1 : ℂ)) • next R B a n v = R (B v) - (n : ℂ) • B v := by
  have hn : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [next, smul_smul, mul_inv_cancel₀ (mul_ne_zero ha hn), one_smul]

/-- With j indexing coefficients of order 2j, construct all scalar coefficients
from the shell and transport conditions on u alone. -/
theorem exists_scalar_lift (K R B : Module.End ℂ V) (S : Submodule ℂ V)
    (a : ℂ) (ha : a ≠ 0)
    (euler : ∀ v, K (R v) = R (K v) + K v)
    (wave_shell : ∀ v, K (B v) = B (K v))
    (wave_euler : ∀ v, R (B v) = B (R v))
    (transport_euler : ∀ v ∈ S, R v ∈ S)
    (transport_wave : ∀ v ∈ S, B v ∈ S)
    (u : V) (shell : K u = a • u) (transport : u ∈ S) :
    ∃ U : ℕ → V, U 0 = u ∧ (∀ n, U n ∈ S) ∧
      ∀ n, K (U (n+1)) = a • U (n+1) + B (U n) := by
  let U : ℕ → V := Nat.rec u (next R B a)
  have step (n : ℕ) : (a * (n+1 : ℂ)) • U (n+1) = R (B (U n)) - (n : ℂ) • B (U n) :=
    scaled_next R B ha n (U n)
  refine ⟨U, rfl, ?_, ?_⟩
  · intro n
    induction n with
    | zero => exact transport
    | succ n ih =>
      change (a * (n+1 : ℂ))⁻¹ • (R (B (U n)) - (n : ℂ) • B (U n)) ∈ S
      exact S.smul_mem _ (S.sub_mem (transport_euler _ (transport_wave _ ih))
        (S.smul_mem _ (transport_wave _ ih)))
  · intro n
    induction n with
    | zero =>
      change K (next R B a 0 u) = a • next R B a 0 u + B u
      simp [next, euler, wave_shell, shell, ha, smul_add, smul_smul]
    | succ n ih =>
      have lift_step := congrArg B (step n)
      simp only [map_smul, map_sub, ← wave_euler] at lift_step
      have hn : ((n+1 : ℕ) + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n+1)
      have c := mul_ne_zero ha hn
      apply (smul_right_injective V c)
      dsimp only
      rw [← K.map_smul, step (n+1), map_sub, map_smul, euler, wave_shell, ih,
        map_add, map_smul, map_add, map_smul]
      conv_rhs => rw [smul_add, smul_comm _ a, step (n+1)]
      push_cast
      linear_combination (norm := module) -lift_step
end MassShell.FreeRecursion

namespace MassShell.CompositionAndTransport.FreeShellRadial
noncomputable section
open scoped Distributions ContDiff

local instance : Ring Operator := Module.End.instRing
local instance : AddCommGroup Operator := LinearMap.addCommGroup

abbrev spaceD (i : Fin 4) := «partial» (.inl i)

def pairOp (F G : Fin 4 → Operator) : Operator :=
  F 0 * G 0 - F 1 * G 1 - F 2 * G 2 - F 3 * G 3

def shellOp := pairOp momentum momentum
def transportOp := pairOp momentum spaceD
def waveOp := (1/4 : ℂ) • pairOp spaceD spaceD
private def eulerOp := ∑ i : Fin 4, momentum i * «partial» (.inr i)
private def raiseOp := (-1/2 : ℂ) • eulerOp

private def br (a b : Operator) := a*b-b*a
private theorem br_sub (a b c : Operator) : br a (b-c) = br a b - br a c := by
  simp [br, mul_sub, sub_mul]; abel
private theorem br_sub_left (a b c : Operator) : br (a-b) c = br a c - br b c := by
  simp [br, mul_sub, sub_mul]; abel
private theorem br_mul (a b c : Operator) : br a (b*c) = br a b * c + b * br a c := by
  simp [br, mul_sub, sub_mul, mul_assoc]
private theorem br_mul_left (a b c : Operator) : br (a*b) c = a * br b c + br a c * b := by
  simp [br, mul_sub, sub_mul, mul_assoc]
private theorem br_smul (a b : Operator) (s : ℂ) : br a (s • b) = s • br a b := by
  simp [br, smul_sub]
private theorem br_mom (i j : Fin 4) : br (momentum i) (momentum j) = 0 :=
  sub_eq_zero.mpr (momentum_commute i j).eq
private theorem br_d (d e : Axis) : br («partial» d) («partial» e) = 0 :=
  sub_eq_zero.mpr (partial_commute d e).eq
private theorem br_dp (i j : Fin 4) :
    br («partial» (.inr i)) (momentum j) = (if i=j then 1 else 0) := by
  simp [br, partial_p_mul, add_sub_cancel_left]
private theorem br_xp (i j : Fin 4) : br (spaceD i) (momentum j) = 0 := by
  exact sub_eq_zero.mpr (partial_x_commute i j).eq
private theorem br_px (i j : Fin 4) : br (momentum j) (spaceD i) = 0 :=
  sub_eq_zero.mpr (partial_x_commute i j).symm.eq
private theorem br_euler_p (j : Fin 4) : br eulerOp (momentum j) = momentum j := by
  have sum_br (F : Fin 4 → Operator) (a : Operator) :
      br (∑ i, F i) a = ∑ i, br (F i) a := by
    simp [br, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  simp [eulerOp, sum_br, br_mul_left, br_mom, br_dp, mul_ite]
private theorem br_euler_x (j : Fin 4) : br eulerOp (spaceD j) = 0 := by
  have eqn (i : Fin 4) : br (momentum i * «partial» (.inr i)) (spaceD j) = 0 := by
    simp [br_mul_left, spaceD, br_d, br_px]
  simp only [eulerOp, br, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_eq_zero fun i _ => eqn i

private theorem shell_raise (w : ScalarDistribution) :
    shellOp (raiseOp w) = raiseOp (shellOp w) + shellOp w := by
  have h : br eulerOp shellOp = shellOp + shellOp := by
    simp [shellOp, pairOp, br_sub, br_mul, br_euler_p]
    abel
  have op : shellOp * raiseOp = raiseOp * shellOp + shellOp := by
    unfold br at h
    simp only [raiseOp, mul_smul_comm, smul_mul_assoc]
    linear_combination (norm := module) (1/2 : ℂ) • h
  exact DFunLike.congr_fun op w

private theorem transport_raise (w : ScalarDistribution) (hw : transportOp w = 0) :
    transportOp (raiseOp w) = 0 := by
  have h : br eulerOp transportOp = transportOp := by
    simp [transportOp, pairOp, br_sub, br_mul, br_euler_p, br_euler_x]
  have op : transportOp * raiseOp = raiseOp * transportOp + (1/2 : ℂ) • transportOp := by
    unfold br at h
    simp only [raiseOp, mul_smul_comm, smul_mul_assoc]
    linear_combination (norm := module) (1/2 : ℂ) • h
  have hw' := DFunLike.congr_fun op w
  simpa only [mul_apply_eq_comp, LinearMap.add_apply, LinearMap.smul_apply,
    hw, map_zero, smul_zero, add_zero] using hw'

private theorem comm_wave (A : Operator) (h : ∀ i, br A (spaceD i) = 0) :
    Commute A waveOp := by
  apply sub_eq_zero.mp
  change br A waveOp = 0
  simp [waveOp, pairOp, br_smul, br_sub, br_mul, h]

private theorem shell_wave : Commute shellOp waveOp := by
  apply comm_wave
  intro i
  simp [shellOp, pairOp, br_sub_left, br_mul_left, br_px]

private theorem transport_wave : Commute transportOp waveOp := by
  apply comm_wave
  intro i
  simp [transportOp, pairOp, br_sub_left, br_mul_left, br_px, br_d, spaceD]

/-- Every transported leading scalar distribution on a massive free shell has
a formal lift solving the two squared equations. U j denotes the coefficient at
order 2j. The odd coefficients can all be chosen to vanish. -/
theorem exists_free_scalar_coefficients (a : ℂ) (ha : a ≠ 0) (u : ScalarDistribution)
    (shell : shellOp u = a • u) (transport : transportOp u = 0) :
    ∃ U : ℕ → ScalarDistribution, U 0 = u ∧ (∀ n, transportOp (U n) = 0) ∧
      ∀ n, shellOp (U (n+1)) = a • U (n+1) + waveOp (U n) := by
  apply MassShell.FreeRecursion.exists_scalar_lift shellOp raiseOp waveOp
    (LinearMap.ker transportOp) a ha shell_raise
    (fun v => DFunLike.congr_fun shell_wave.eq v)
    (fun v => DFunLike.congr_fun (((comm_wave eulerOp br_euler_x).smul_left (-1/2 : ℂ)).eq) v)
    transport_raise _ u shell transport
  intro w (h : transportOp w = 0)
  change transportOp (waveOp w) = 0
  rw [show transportOp (waveOp w) = waveOp (transportOp w) from DFunLike.congr_fun transport_wave.eq w,
    h, map_zero]

/-- Insert zeros in the odd orders of the scalar lift. The recurrence now uses
the order of the formal deformation parameter itself. -/
theorem exists_free_scalar_series (a : ℂ) (ha : a ≠ 0) (u : ScalarDistribution)
    (shell : shellOp u = a • u) (transport : transportOp u = 0) :
    ∃ U : ℕ → ScalarDistribution, U 0 = u ∧ (∀ n, transportOp (U n) = 0) ∧
      shellOp (U 0) = a • U 0 ∧ shellOp (U 1) = a • U 1 ∧
      ∀ n, shellOp (U (n+2)) = a • U (n+2) + waveOp (U n) := by
  obtain ⟨V, h0, ht, hk⟩ := exists_free_scalar_coefficients a ha u shell transport
  let U (n : ℕ) := if n % 2 = 0 then V (n / 2) else 0
  have hu : U 0 = u := by simpa [U] using h0
  have hz : a • (0 : ScalarDistribution) = 0 := by ext φ; change a * 0 = 0; ring
  refine ⟨U, hu, ?_, by simpa only [hu] using shell, by simp [U, hz], ?_⟩
  · intro n
    by_cases hn : n % 2 = 0 <;> simp [U, hn, ht]
  · intro n
    have div : (n+2)/2 = n/2+1 := by omega
    have parity : (n+2)%2 = n%2 := by omega
    by_cases hn : n % 2 = 0 <;> simp [U, parity, hn, div, hk, hz]

end
end MassShell.CompositionAndTransport.FreeShellRadial
