module
public import MassShell
import all MassShell
public section

/-! Polynomial Dirac factorisation acting on distributions by commuting momentum
multipliers and spacetime derivatives. The right action uses the opposite order. -/

namespace MassShell.FreeDirac
noncomputable section
variable {A M : Type*} [CommRing A] [Algebra ℂ A] [AddCommGroup M] [Module A M]

abbrev Mat (V : Type*) := Matrix (Fin 4) (Fin 4) V

def squareForm (p : Fin 4 → A) := p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2

def pencil (p : Fin 4 → A) : Mat A :=
  let i := algebraMap ℂ A Complex.I
  let t := p 0
  let x := p 1
  let y := p 2
  let z := p 3
  !![0,0,t+z,x-i*y; 0,0,x+i*y,t-z; t-z,-x+i*y,0,0; -x-i*y,t+z,0,0]

theorem pencil_squared (p : Fin 4 → A) :
    pencil p * pencil p = squareForm p • (1 : Mat A) := by
  have hi : (algebraMap ℂ A Complex.I)^2 = -1 := by rw [← map_pow, Complex.I_sq, map_neg, map_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pencil, squareForm, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring_nf <;> rw [hi] <;> ring

/-- Coefficients of the pencil in the coordinate basis. -/
theorem pencil_entries (z : Fin 4 → A) (a b : Fin 4) :
    pencil z a b = ∑ i : Fin 4, algebraMap ℂ A (gamma_axis i a b) * z i := by
  fin_cases a <;> fin_cases b <;>
    simp [pencil,gamma_axis,four_component_factor,four_component_pencil,Fin.sum_univ_four,Pi.single_apply] <;> ring

omit [Algebra ℂ A] in
section

def leftAct (F : Mat A) (u : Mat M) : Mat M := fun i j => ∑ k, F i k • u k j
def rightAct (G : Mat A) (u : Mat M) : Mat M := fun i j => ∑ k, G k j • u i k

theorem left_comp (F G : Mat A) (u : Mat M) :
    leftAct F (leftAct G u) = leftAct (F*G) u := by
  ext i j
  simp only [leftAct, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem right_comp (F G : Mat A) (u : Mat M) :
    rightAct F (rightAct G u) = rightAct (G*F) u := by
  ext i j
  simp only [rightAct, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem left_right (F G : Mat A) (u : Mat M) :
    leftAct F (rightAct G u) = rightAct G (leftAct F u) := by
  ext i j
  simp only [leftAct,rightAct, Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem left_scalar (a : A) (u : Mat M) : leftAct (a • (1 : Mat A)) u = a • u := by
  ext i j
  simp [leftAct, Matrix.one_apply]

theorem right_scalar (a : A) (u : Mat M) : rightAct (a • (1 : Mat A)) u = a • u := by
  ext i j
  simp [rightAct, Matrix.one_apply]

end

theorem shifted_factor (p : Fin 4 → A) (m : A) :
    (pencil p - m • 1) * (pencil p + m • 1) = (squareForm p - m^2) • (1 : Mat A) ∧
    (pencil p + m • 1) * (pencil p - m • 1) = (squareForm p - m^2) • (1 : Mat A) := by
  simp only [sub_mul, mul_sub, mul_add, add_mul, pencil_squared, mul_smul_comm, smul_mul_assoc,
    one_mul, mul_one, sub_smul, pow_two, smul_add, smul_sub, smul_smul]
  constructor <;> abel

/-- Applying the two Dirac numerators to any common solution of the squared
equations gives a solution of both first-order equations. -/
theorem lift_two_sided (l r : Fin 4 → A) (m : A) (u : Mat M)
    (hl : (squareForm l - m^2) • u = 0) (hr : (squareForm r - m^2) • u = 0) :
    let w := leftAct (pencil l + m • 1) (rightAct (pencil r + m • 1) u)
    leftAct (pencil l - m • 1) w = 0 ∧ rightAct (pencil r - m • 1) w = 0 := by
  dsimp only
  constructor
  · rw [left_comp, (shifted_factor l m).1, left_right, left_scalar, hl]
    ext i j
    simp [rightAct]
  · rw [← left_right, right_comp, (shifted_factor r m).2, right_scalar, hr]
    ext i j
    simp [leftAct]

end
end MassShell.FreeDirac
