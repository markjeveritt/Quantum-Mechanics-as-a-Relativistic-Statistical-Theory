module

public import Mathlib

/-!
# Mass-shell factorisation and the deformation hierarchy
Selected steps of M. Everitt, *Quantum Mechanics as a Relativistic Statistical Theory*
(14 October 2026). Equation numbers refer to the manuscript. The coefficient algebra A
can throughout Part I be taken to be `Matrix (Fin N) (Fin N) ℂ`.

## Reading the proof

For the minimal complex factor, start with `theorem_four_is_minimal`.
For the universal product, start with `theorem_exists_unique_product_from_field_ansatze`.
For the complete smooth-state implication in Section 5, start with
`theorem_minimal_argument_from_field_ansatze`. For singular states, see
`theorem_distribution_bimodule_associativity` and `theorem_nonzero_free_shell_solution`.

* A2 imposes the off-shell square. Polarisation gives the Clifford relations. Four is
  the minimum positive complex matrix size. The rest-sector generators act as the Pauli
  matrices, and every Lorentz isometry of the pencil is implemented by similarity.
* A12 allows a finite local differential polynomial at each point. Translation invariance
  forces constant coefficients. Canonical covariance on fields implies covariance of the
  polynomial. Matrix neutrality and associativity determine the matrix extension.
* Dimensional balance gives the order grading. Canonical covariance then gives Eq. (61). Associativity on three
  exponential fields gives Eq. (69), and the coefficient recurrence gives Eq. (71).
* Compatibility with the Dirac adjoint gives conjugate(aₙ) = (−1)ⁿ aₙ. In particular
  the first coefficient is purely imaginary. The signed Weyl normalisation of a single
  unit canonical pair fixes its imaginary part at 1/2. Thus a₁ = i/2 and Eq. (73)
  follows. The constructed family satisfies all the field-product hypotheses.
* A20 constrains a state at all orders. A21 selects its spectral sector. There are
  associative left and right actions with one distributional argument. A nonzero
  spacetime-homogeneous free state satisfies both zero-eigenvalue equations to all
  orders. General state continuation from arbitrary initial data is a separate problem.
* For Eq. (86), `theorem_projected_density_on_measured_shell` handles a locally finite
  measure carried on the shell. The local simple-root graph formula is `delta_chart_measure`.
  On each massive free sheet its transverse Jacobian weight is 1/(2|p₀|).
* For Section 4, `theorem_wigner_equation_from_spinor_amplitude` transforms an amplitude
  equation with a spectator spinor into the equation for one density-matrix entry.
  The two signs select the left and right endpoints. For the explicit pencil,
  `theorem_adjoint_dirac_equation` derives the adjoint amplitude equation for real potentials.
  The regularity hypotheses are
  differentiability in the centre in Schwartz space and temperate potential growth.
  The exact potential has a finite differential expansion for polynomial shifts.
  The two formal potential symbols agree at every order in
  `theorem_wigner_potential_symbols_match_moyal`.
  Smoothness alone cannot justify summing an infinite local expansion at fixed ℏ.
  A19 identifies the physical action scale experimentally.

For the free transport equation (23), `theorem_free_sector_transport_from_preservation`
starts with the commutator hierarchy and projects its first-order equation.
`theorem_free_transport_for_internal_distributions` gives the weak transport equation
for a distribution with values in the internal two-by-two matrices at fixed momentum.
At any order, `theorem_intersector_reaction_at_every_order` determines the off-diagonal
block where the spectral gap has a smooth inverse. For the shell measure, see
`theorem_phase_shell_regular_atlas` and `theorem_delta_measures_agree_on_overlap`.

Names beginning with `ansatz_` identify modelling assumptions. Proved declarations
use `lemma_`, `theorem_` and `corollary_` according to their role in the argument.

Checked with Lean 4.36.0 and Mathlib v4.36.0. The file has no project-local imports.
-/

public section

namespace MassShell

abbrev FourMomentum := Fin 4 → ℝ

/-- Lorentz signature (+,−,−,−), with the time component first. -/
def minkowski_pairing (p q : FourMomentum) : ℝ :=
  p 0 * q 0 - p 1 * q 1 - p 2 * q 2 - p 3 * q 3

noncomputable section Factorisation

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Ansatz 2 requires this identity even away from the mass shell. -/
def ansatz_reproduces_minkowski_square (factor : FourMomentum →ₗ[ℝ] A) : Prop :=
  ∀ p, factor p * factor p = minkowski_pairing p p • (1 : A)

/-- Mathlib's quadratic form for the (+,−,−,−) metric. -/
def minkowski_form : QuadraticForm ℝ FourMomentum :=
  QuadraticMap.proj 0 0 - QuadraticMap.proj 1 1 -
    QuadraticMap.proj 2 2 - QuadraticMap.proj 3 3

/-- The universal property extends the proposed factor to a Clifford representation. -/
def clifford_representation (factor : FourMomentum →ₗ[ℝ] A)
    (ansatz_square_identity : ansatz_reproduces_minkowski_square factor) :
    CliffordAlgebra minkowski_form →ₐ[ℝ] A :=
  CliffordAlgebra.lift minkowski_form ⟨factor, fun p => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact ansatz_square_identity p⟩

theorem lemma_clifford_representation_recovers_factor (factor : FourMomentum →ₗ[ℝ] A)
    (ansatz_square_identity : ansatz_reproduces_minkowski_square factor) (p : FourMomentum) :
    clifford_representation factor ansatz_square_identity (CliffordAlgebra.ι minkowski_form p) =
      factor p :=
  CliffordAlgebra.lift_ι_apply _ _ _

/-- Equation (4), contracted against two independently chosen four-momenta. -/
theorem theorem_factorisation_forces_clifford_relation
    (factor : FourMomentum →ₗ[ℝ] A)
    (ansatz_square_identity : ansatz_reproduces_minkowski_square factor) (p q : FourMomentum) :
    factor p * factor q + factor q * factor p = (2 * minkowski_pairing p q) • (1 : A) := by
  have polarised_square :
      minkowski_pairing (p + q) (p + q) =
        minkowski_pairing p p + minkowski_pairing q q + 2 * minkowski_pairing p q := by
    simp only [minkowski_pairing, Pi.add_apply]
    ring
  -- Expand K(p+q)², then cancel the two known squares in the additive group.
  have mixed_terms := ansatz_square_identity (p + q)
  rw [map_add, add_mul, mul_add, mul_add, ansatz_square_identity p, ansatz_square_identity q,
    polarised_square, add_smul, add_smul] at mixed_terms
  linear_combination (norm := abel) mixed_terms

/-- Equation (5). The scalar shift represents mc. -/
theorem corollary_mass_shifted_factorisation (factor : FourMomentum →ₗ[ℝ] A)
    (ansatz_square_identity : ansatz_reproduces_minkowski_square factor) (p : FourMomentum) (massScale : ℝ) :
    (factor p - massScale • 1) * (factor p + massScale • 1) =
      (minkowski_pairing p p - massScale ^ 2) • (1 : A) := by
  rw [sub_mul, mul_add, mul_add, ansatz_square_identity p]
  simp only [mul_smul_comm, smul_mul_assoc, one_mul, mul_one, smul_smul, sub_smul, pow_two]
  abel

/-- On either massive sheet the normalised factor is an involution. -/
theorem lemma_on_shell_normalisation (factor : FourMomentum →ₗ[ℝ] A)
    (ansatz_square_identity : ansatz_reproduces_minkowski_square factor) (p : FourMomentum)
    (massScale : ℝ) (massScale_ne_zero : massScale ≠ 0)
    (on_shell : minkowski_pairing p p = massScale ^ 2) :
    (massScale⁻¹ • factor p) * (massScale⁻¹ • factor p) = 1 := by
  rw [smul_mul_assoc, mul_smul_comm, ansatz_square_identity, on_shell, smul_smul, smul_smul]
  field_simp
  exact one_smul ℝ _

/-- Equation (10) for the selected sector, with J = K(p)/(mc). -/
def selected_projector (J : A) : A := (1/2 : ℝ) • (1 + J)

/-- J acts as the identity on the selected sector from either side. -/
theorem lemma_involution_fixes_projector (J : A) (square_is_one : J * J = 1) :
    J * selected_projector J = selected_projector J ∧
      selected_projector J * J = selected_projector J := by
  simp [selected_projector, mul_add, add_mul,
    square_is_one, add_comm]

theorem lemma_selected_projector_is_idempotent (J : A) (square_is_one : J * J = 1) :
    selected_projector J * selected_projector J = selected_projector J := by
  obtain ⟨left_action, _⟩ := lemma_involution_fixes_projector J square_is_one
  conv_lhs => lhs; unfold selected_projector
  rw [smul_mul_assoc, add_mul, one_mul, left_action]
  module

/-- Equation (15) in units of the nonzero generator scale.
The matrix between the projectors is arbitrary, including its internal coherences. -/
theorem theorem_projected_distribution_satisfies_both_constraints (J density : A)
    (square_is_one : J * J = 1) :
    let P := selected_projector J
    (J - 1) * (P * density * P) = 0 ∧ (P * density * P) * (J - 1) = 0 := by
  dsimp only
  obtain ⟨left_action, right_action⟩ := lemma_involution_fixes_projector J square_is_one
  constructor
  · rw [← mul_assoc, ← mul_assoc, sub_mul, one_mul, left_action, sub_self, zero_mul, zero_mul]
  · rw [mul_assoc, mul_sub, mul_one, right_action, sub_self, mul_zero]

/-- Equation (17) for the selected sign. The component on the right is pᵘ/(mc). -/
theorem lemma_projected_generator_component (J component : A) (normalised_momentum : ℝ)
    (square_is_one : J * J = 1)
    (clifford_relation : J * component + component * J = (2 * normalised_momentum) • (1 : A)) :
    let P := selected_projector J
    P * component * P = normalised_momentum • P := by
  let P := selected_projector J
  change P * component * P = normalised_momentum • P
  obtain ⟨left_action, right_action⟩ := lemma_involution_fixes_projector J square_is_one
  -- Sandwich the anticommutator. Each occurrence of J next to P then disappears.
  have sandwich := congrArg (fun X : A => P * X * P) clifford_relation
  change P * (J * component + component * J) * P = P * ((2 * normalised_momentum) • 1) * P at sandwich
  rw [mul_add, add_mul, ← mul_assoc P J, right_action, mul_assoc P (component * J),
    mul_assoc component J, left_action, ← mul_assoc, mul_smul_comm, mul_one,
    smul_mul_assoc, lemma_selected_projector_is_idempotent J square_is_one] at sandwich
  calc
    P * component * P = (1/2 : ℝ) • (P * component * P + P * component * P) := by module
    _ = normalised_momentum • P := by rw [sandwich, smul_smul]; congr 1; ring

/-- One summand of Eq. (22). D represents a spacetime derivative of the
distribution, supported in the selected sector because the projector is independent of x.
Both matrix orderings in the Weyl average give the same transport term. -/
theorem lemma_projected_weyl_transport_component (P component D : A) (v : ℝ)
    (projected_component : P * component * P = v • P)
    (left_support : P * D = D) (right_support : D * P = D) :
    P * ((1/2 : ℝ) • (component * D + D * component)) * P = v • D := by
  have first_ordering : P * (component * D) * P = v • D := by
    calc
      _ = P * component * (P * D) := by simp only [mul_assoc, right_support, left_support]
      _ = (P * component * P) * D := (mul_assoc _ _ _).symm
      _ = v • D := by rw [projected_component, smul_mul_assoc, left_support]
  have second_ordering : P * (D * component) * P = v • D := by
    calc
      _ = (D * P) * (component * P) := by rw [right_support, ← mul_assoc P D, left_support, mul_assoc]
      _ = D * (P * component * P) := by simp only [mul_assoc]
      _ = v • D := by rw [projected_component, mul_smul_comm, right_support]
  rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, first_ordering, second_ordering]
  module

/-- Free Weyl transport contracted with an arbitrary test direction q.
The common scalar c in the physical generator can be restored on both sides.
Taking q along each coordinate axis and summing gives the algebra in Eq. (22). -/
theorem corollary_free_transport_in_direction (factor : FourMomentum →ₗ[ℝ] A)
    (ansatz_square_identity : ansatz_reproduces_minkowski_square factor) (p q : FourMomentum)
    (massScale : ℝ) (massScale_ne_zero : massScale ≠ 0)
    (on_shell : minkowski_pairing p p = massScale ^ 2) (D : A) :
    let P := selected_projector (massScale⁻¹ • factor p)
    P * D = D → D * P = D →
      P * ((1/2 : ℝ) • (factor q * D + D * factor q)) * P =
        (massScale⁻¹ * minkowski_pairing p q) • D := by
  intro P left_support right_support
  apply lemma_projected_weyl_transport_component P (factor q) D _ _ left_support right_support
  apply lemma_projected_generator_component
  · exact lemma_on_shell_normalisation factor ansatz_square_identity p massScale massScale_ne_zero on_shell
  · rw [smul_mul_assoc, mul_smul_comm, ← smul_add,
      theorem_factorisation_forces_clifford_relation factor ansatz_square_identity, smul_smul]
    congr 1
    ring

/-- Equations (36)–(38), with the gap normalised so H = J up to a central shift.
Y includes the factor i multiplying the Weyl source. Its diagonal part is
(Y + JYJ)/2. Thus JYJ = −Y says precisely that the diagonal source vanishes. -/
theorem lemma_off_diagonal_source_iff_correction_exists (J source : A)
    (square_is_one : J * J = 1) :
    J * source * J = -source ↔
      ∃ correction : A, J * correction - correction * J + source = 0 := by
  constructor
  · intro off_diagonal
    -- Multiplication by J reverses the commutator on the off-diagonal blocks.
    use (-1/2 : ℝ) • (J * source)
    rw [mul_smul_comm, smul_mul_assoc, ← mul_assoc, square_is_one, one_mul, off_diagonal]
    module
  · rintro ⟨correction, cancellation⟩
    have source_from_correction : source = correction * J - J * correction := by
      linear_combination (norm := abel) cancellation
    rw [source_from_correction, mul_sub, sub_mul, ← mul_assoc J J, square_is_one,
      one_mul, mul_assoc J (correction * J) J,
      mul_assoc correction J J, square_is_one, mul_one]
    abel

end Factorisation

section SectorDimension

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A change of sign under an invertible involution forces the trace to vanish.
For a Dirac factor the chirality operator provides such an involution. -/
theorem lemma_trace_zero_of_anticommuting_involution (J chirality : Module.End ℂ V)
    (chirality_squares_to_one : chirality * chirality = 1)
    (anticommutes : chirality * J = -(J * chirality)) :
    LinearMap.trace ℂ V J = 0 := by
  have sign_change : chirality * J * chirality = -J := by
    rw [anticommutes, neg_mul, mul_assoc, chirality_squares_to_one, mul_one]
  have cyclic_trace := LinearMap.trace_mul_comm ℂ (chirality * J) chirality
  rw [sign_change, map_neg, ← mul_assoc, chirality_squares_to_one, one_mul] at cyclic_trace
  linear_combination -cyclic_trace / 2

/-- In a four-dimensional complex representation, a traceless on-shell involution
has a selected sector of dimension two. Rank here means the dimension of the image. -/
theorem lemma_selected_sector_has_dimension_two [FiniteDimensional ℂ V] (J : Module.End ℂ V)
    (ansatz_four_components : Module.finrank ℂ V = 4) (square_is_one : J * J = 1)
    (trace_is_zero : LinearMap.trace ℂ V J = 0) :
    Module.finrank ℂ (LinearMap.range (selected_projector J)) = 2 := by
  have idempotent : IsIdempotentElem (selected_projector J) :=
    lemma_selected_projector_is_idempotent J square_is_one
  have trace_of_projector : LinearMap.trace ℂ V (selected_projector J) = 2 := by
    unfold selected_projector
    rw [← Complex.coe_smul, map_smul, map_add, LinearMap.trace_one, ansatz_four_components, trace_is_zero]
    norm_num
  rw [((LinearMap.isProj_range_iff_isIdempotentElem _).mpr idempotent).trace] at trace_of_projector
  exact_mod_cast trace_of_projector

/-- Every component of a linear mass-shell factor is traceless. For each coordinate
generator choose a different coordinate axis. Its generator is invertible and anticommutes
with the first. Multiplication by i turns a spacelike generator into an involution. -/
theorem lemma_mass_shell_factor_is_traceless (factor : FourMomentum →ₗ[ℝ] Module.End ℂ V)
    (ansatz_square_identity : ansatz_reproduces_minkowski_square factor) (p : FourMomentum) :
    LinearMap.trace ℂ V (factor p) = 0 := by
  let axis (i : Fin 4) : FourMomentum := Pi.single i 1
  have axis_trace (i : Fin 4) : LinearMap.trace ℂ V (factor (axis i)) = 0 := by
    let j : Fin 4 := if i = 0 then 1 else 0
    have perpendicular : minkowski_pairing (axis j) (axis i) = 0 := by
      fin_cases i <;> norm_num [axis, j, minkowski_pairing, Pi.single_apply]
    have anticommutes := theorem_factorisation_forces_clifford_relation factor ansatz_square_identity (axis j) (axis i)
    rw [perpendicular, mul_zero, zero_smul] at anticommutes
    have swap := eq_neg_of_add_eq_zero_left anticommutes
    by_cases is_time : i = 0
    · have partner_square : factor (axis j) * factor (axis j) = -1 := by
        rw [ansatz_square_identity (axis j)]
        norm_num [j, is_time, axis, minkowski_pairing, Pi.single_apply]
      apply lemma_trace_zero_of_anticommuting_involution _ (Complex.I • factor (axis j))
      · rw [smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, partner_square]
        simp
      · rw [smul_mul_assoc, mul_smul_comm, swap, smul_neg]
    · apply lemma_trace_zero_of_anticommuting_involution _ (factor (axis j))
      · rw [ansatz_square_identity (axis j)]
        norm_num [j, is_time, axis, minkowski_pairing, Pi.single_apply]
      · exact swap
  -- Linearity now extends the trace identity from the four axes to arbitrary p.
  conv_lhs => arg 2; arg 2; rw [pi_eq_sum_univ' p]
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  change LinearMap.trace ℂ V (factor (p i • axis i)) = 0
  rw [map_smul, ← Complex.coe_smul, map_smul, axis_trace, smul_zero]

/-- Rank two on both sheets, in any four-dimensional complex realisation of Ansatz 2. -/
theorem corollary_massive_sector_has_dimension_two [FiniteDimensional ℂ V]
    (factor : FourMomentum →ₗ[ℝ] Module.End ℂ V)
    (ansatz_square_identity : ansatz_reproduces_minkowski_square factor) (ansatz_four_components : Module.finrank ℂ V = 4)
    (p : FourMomentum) (massScale : ℝ) (massScale_ne_zero : massScale ≠ 0)
    (on_shell : minkowski_pairing p p = massScale ^ 2) :
    Module.finrank ℂ (LinearMap.range (selected_projector (massScale⁻¹ • factor p))) = 2 := by
  apply lemma_selected_sector_has_dimension_two _ ansatz_four_components
  · exact lemma_on_shell_normalisation factor ansatz_square_identity p massScale massScale_ne_zero on_shell
  · rw [← Complex.coe_smul, map_smul, lemma_mass_shell_factor_is_traceless factor ansatz_square_identity, smul_zero]

end SectorDimension

/-- Equation (70) in coefficients. Comparing uʳwˢ in Φ(u+w) and Φ(u)Φ(w)
introduces the binomial coefficient on the left. -/
def exponential_coefficient_law (a : ℕ → ℂ) : Prop :=
  ∀ r s, ((r+s).choose r : ℂ) * a (r+s) = a r * a s

open Polynomial in
/-- The homogeneous term of total order n in Φ(tu)Φ(tv).
The scalar t records order only, so each such term is a finite polynomial. -/
noncomputable def symbol_product_term (a : ℕ → ℂ) (n : ℕ) (u v : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (a k * a (n-k)) * u ^ k * v ^ (n-k)

open Polynomial in
/-- From Eq. (69) to Eq. (70) and its binomial coefficient law. The premise
is associativity at the level of commuting symbols, after the differential-operator
comparison in the paper. Testing polynomial symbols allows exact coefficient extraction. -/
theorem lemma_symbol_associativity_forces_coefficient_law (a : ℕ → ℂ) (constant_term : a 0 = 1)
    (symbol_associativity : ∀ (n : ℕ) (u v w : ℂ[X]),
      symbol_product_term a n u (v+w) = symbol_product_term a n v (u+w)) :
    exponential_coefficient_law a := by
  intro r s
  let n := r+s
  have at_zero (z : ℂ[X]) : symbol_product_term a n 0 z = C (a n) * z ^ n := by
    unfold symbol_product_term
    rw [Finset.sum_eq_single 0]
    · simp [constant_term]
    · intro k _ k_ne_zero
      simp [zero_pow k_ne_zero]
    · simp
  have homogeneous_identity := symbol_associativity n X 0 1
  rw [zero_add, at_zero] at homogeneous_identity
  -- In the sum, only the term with k = r contributes to the coefficient of Xʳ.
  have coefficient_identity := congrArg (fun f : ℂ[X] => f.coeff r) homogeneous_identity
  simp only [symbol_product_term, one_pow, mul_one, finsetSum_coeff,
    coeff_C_mul, coeff_X_add_one_pow] at coefficient_identity
  have r_in_range : r ∈ Finset.range (n+1) := by simp [n]
  simpa [n, r_in_range, mul_comm] using coefficient_identity.symm

/-- Equation (71). Once symbol comparison gives the coefficient law,
the entire formal series is determined by its linear coefficient. -/
theorem lemma_coefficient_law_determines_exponential (a : ℕ → ℂ) (constant_term : a 0 = 1)
    (coefficient_law : exponential_coefficient_law a) (order : ℕ) :
    a order = a 1 ^ order / (order.factorial : ℂ) := by
  induction order with
  | zero => simp [constant_term]
  | succ n induction_hypothesis =>
    -- The coefficient of u wⁿ relates consecutive orders.
    have next_coefficient := coefficient_law 1 n
    rw [Nat.choose_one_right, Nat.add_comm 1 n, induction_hypothesis] at next_coefficient
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    push_cast at next_coefficient ⊢
    have factorial_ne_zero : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have successor_ne_zero : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp [factorial_ne_zero, successor_ne_zero] at next_coefficient ⊢
    linear_combination next_coefficient

/-- Equation (73) at coefficient level, with the first-order matching convention. -/
theorem corollary_moyal_weights (a : ℕ → ℂ) (constant_term : a 0 = 1)
    (coefficient_law : exponential_coefficient_law a)
    (first_order_matching : a 1 = Complex.I / 2) (order : ℕ) :
    a order = (Complex.I / 2) ^ order / (order.factorial : ℂ) := by
  rw [lemma_coefficient_law_determines_exponential a constant_term coefficient_law order,
    first_order_matching]

section FormalHierarchy

variable {Symbol : Type*} [AddCommGroup Symbol]

/-- Equation (78). C r is the r-th product coefficient and W k the k-th
distribution coefficient. The generator is independent of the formal parameter. -/
def commutator_coefficient (C : ℕ → Symbol → Symbol → Symbol)
    (H : Symbol) (W : ℕ → Symbol) (order : ℕ) : Symbol :=
  ∑ r ∈ Finset.range (order+1), (C r H (W (order-r)) - C r (W (order-r)) H)

/-- Equation (81) as equality of the two formal coefficient sequences. -/
theorem theorem_hierarchy_iff_left_and_right_products_agree (C : ℕ → Symbol → Symbol → Symbol)
    (H : Symbol) (W : ℕ → Symbol) :
    (∀ n, commutator_coefficient C H W n = 0) ↔
      (fun n => ∑ r ∈ Finset.range (n+1), C r H (W (n-r))) =
      (fun n => ∑ r ∈ Finset.range (n+1), C r (W (n-r)) H) := by
  simp only [commutator_coefficient, Finset.sum_sub_distrib, sub_eq_zero, funext_iff]

/-- Equations (79) and (80), before substituting the Weyl expression for the
antisymmetric part of C₁. The first-order equation also contains W₁. -/
theorem lemma_first_two_hierarchy_coefficients {A : Type*} [Ring A]
    (C : ℕ → A → A → A) (ordinary_product : ∀ F G, C 0 F G = F * G)
    (H : A) (W : ℕ → A) :
    commutator_coefficient C H W 0 = H * W 0 - W 0 * H ∧
    commutator_coefficient C H W 1 =
      (H * W 1 - W 1 * H) + (C 1 H (W 0) - C 1 (W 0) H) := by
  simp [commutator_coefficient, Finset.sum_range_succ, ordinary_product]
  abel

/-- Equations (83)–(84). The selected left-sector equation is an extra hypothesis.
For the zero sector, set the spectral value times the distribution to zero. -/
theorem corollary_right_spectral_equation (left_product right_product spectral_value_times_density : Symbol)
    (commutator_vanishes : left_product - right_product = 0)
    (selected_left_sector : left_product = spectral_value_times_density) :
    right_product = spectral_value_times_density :=
  (sub_eq_zero.mp commutator_vanishes).symm.trans selected_left_sector

end FormalHierarchy

namespace MinimalArgument

/-- Part I. The square identity supplies the involution and tracelessness through
two branches. Both facts are needed to compute the dimension of the selected sector. -/
theorem lemma_from_factorisation_to_rank_two
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (factor : FourMomentum →ₗ[ℝ] Module.End ℂ V)
    (ansatz_square_identity : ansatz_reproduces_minkowski_square factor)
    (ansatz_four_components : Module.finrank ℂ V = 4)
    (p : FourMomentum) (massScale : ℝ) (massScale_ne_zero : massScale ≠ 0)
    (on_shell : minkowski_pairing p p = massScale ^ 2) :
    Module.finrank ℂ (LinearMap.range (selected_projector (massScale⁻¹ • factor p))) = 2 := by
  let J := massScale⁻¹ • factor p
  have J_squares_to_one : J * J = 1 :=
    lemma_on_shell_normalisation factor ansatz_square_identity p massScale massScale_ne_zero on_shell
  -- The proof of tracelessness uses the Clifford anticommutator on perpendicular axes.
  have factor_is_traceless := lemma_mass_shell_factor_is_traceless factor ansatz_square_identity p
  have J_is_traceless : LinearMap.trace ℂ V J = 0 := by
    dsimp only [J]
    rw [← Complex.coe_smul, map_smul, factor_is_traceless, smul_zero]
  exact lemma_selected_sector_has_dimension_two J ansatz_four_components J_squares_to_one J_is_traceless

/-- From the classical sector to the first preservation equation. H is the free
generator in units of its nonzero mass scale. The derivative contribution is supplied
as source, and projected transport requires its diagonal part to vanish. -/
theorem lemma_from_classical_sector_to_first_correction
    {A : Type*} [Ring A] [Algebra ℝ A] (J density source : A)
    (on_shell_involution : J * J = 1) (projected_transport : J * source * J = -source) :
    let P := selected_projector J
    let W₀ := P * density * P
    let H := J - 1
    (H * W₀ = 0 ∧ W₀ * H = 0) ∧ ∃ W₁ : A, H * W₁ - W₁ * H + source = 0 := by
  dsimp only
  have classical_sector :=
    theorem_projected_distribution_satisfies_both_constraints J density on_shell_involution
  obtain ⟨W₁, correction_cancels_source⟩ :=
    (lemma_off_diagonal_source_iff_correction_exists J source on_shell_involution).mp projected_transport
  refine ⟨classical_sector, W₁, ?_⟩
  -- Subtracting the scalar identity from J leaves its commutator with W₁ unchanged.
  rw [sub_mul, mul_sub, one_mul, mul_one]
  linear_combination (norm := abel) correction_cancels_source

open Polynomial in
/-- Part II, Eqs. (69)–(73). This intermediate lemma uses Eq. (69), which
`theorem_reduced_associativity` derives below from the original product. The first-order convention enters in the final step. -/
theorem lemma_from_symbol_associativity_to_moyal_weights
    (a : ℕ → ℂ) (constant_term : a 0 = 1)
    (symbol_associativity : ∀ (n : ℕ) (u v w : ℂ[X]),
      symbol_product_term a n u (v+w) = symbol_product_term a n v (u+w))
    (first_order_matching : a 1 = Complex.I / 2) (n : ℕ) :
    a n = (Complex.I / 2) ^ n / (n.factorial : ℂ) := by
  have coefficient_law :=
    lemma_symbol_associativity_forces_coefficient_law a constant_term symbol_associativity
  calc
    a n = a 1 ^ n / (n.factorial : ℂ) :=
      lemma_coefficient_law_determines_exponential a constant_term coefficient_law n
    _ = (Complex.I / 2) ^ n / (n.factorial : ℂ) := by rw [first_order_matching]

/-- Part II, Eqs. (78)–(84). C is the family of product coefficients. This last
implication works for any such family, including the selected Moyal product.
The two physical requirements appear separately in the theorem statement. -/
theorem corollary_from_preservation_to_right_zero_sector
    {Symbol : Type*} [AddCommGroup Symbol] (C : ℕ → Symbol → Symbol → Symbol)
    (H : Symbol) (W : ℕ → Symbol)
    (all_orders_preserved : ∀ n, commutator_coefficient C H W n = 0)
    (selected_left_sector : ∀ n, (∑ r ∈ Finset.range (n+1), C r H (W (n-r))) = 0) :
    ∀ n, (∑ r ∈ Finset.range (n+1), C r (W (n-r)) H) = 0 := by
  have products_agree :=
    (theorem_hierarchy_iff_left_and_right_products_agree C H W).mp all_orders_preserved
  intro n
  -- Equality of the two formal series gives equality at this particular order.
  have equal_at_this_order := congrFun products_agree n
  calc
    (∑ r ∈ Finset.range (n+1), C r (W (n-r)) H) =
        ∑ r ∈ Finset.range (n+1), C r H (W (n-r)) := equal_at_this_order.symm
    _ = 0 := selected_left_sector n

end MinimalArgument
namespace CompositionAndTransport

/-! The factorisation has supplied a matrix ensemble. We now introduce the
independent composition postulate on that ensemble. The phase point is (x,p).
The following derivatives act on smooth ambient symbols. The final section extends
them to distribution-valued ensembles by transposition on compactly supported tests. -/

abbrev Coordinates := Fin 4 → ℝ
abbrev PhasePoint := Coordinates × Coordinates
abbrev SpinMatrix := Matrix (Fin 4) (Fin 4) ℂ
abbrev Symbol := PhasePoint → SpinMatrix

noncomputable section

/-- Lemma 7. The three constant-matrix identities are Eqs. (47)–(49)
after taking a coefficient of the associative product. Matrix units then force
ordinary contraction of the internal index. This proof uses right additivity only. -/
theorem lemma_matrix_neutrality_forces_internal_contraction
    (coefficient : Symbol → Symbol →+ Symbol)
    (left_constant : ∀ (A : SpinMatrix) F G,
      coefficient ((fun _ => A) * F) G = (fun _ => A) * coefficient F G)
    (middle_constant : ∀ (A : SpinMatrix) F G,
      coefficient (F * fun _ => A) G = coefficient F ((fun _ => A) * G))
    (right_constant : ∀ (A : SpinMatrix) F G,
      coefficient F (G * fun _ => A) = coefficient F G * fun _ => A) :
    ∃ scalar_coefficient : (PhasePoint → ℂ) → (PhasePoint → ℂ) → PhasePoint → ℂ,
      ∀ (F G : Symbol) z i j, coefficient F G z i j =
        ∑ k : Fin 4, scalar_coefficient (fun y => F y i k) (fun y => G y k j) z := by
  let E (i j : Fin 4) : Symbol := fun _ => Matrix.single i j 1
  let corner (f : PhasePoint → ℂ) : Symbol := fun y => Matrix.single 0 0 (f y)
  use fun f g z => coefficient (corner f) (corner g) z 0 0
  intro F G z i j
  have isolate (X : Symbol) (r s : Fin 4) :
      E 0 r * X * E s 0 = corner (fun y => X y r s) := by
    funext y
    simp [E, corner, Pi.mul_apply]
  have split_identity : (∑ k : Fin 4, E k 0 * E 0 k) = 1 := by
    funext y
    simp [E, Finset.sum_apply, Pi.mul_apply, Matrix.sum_single_one]
  let U := E 0 i * F
  let V := G * E j 0
  have outer_entries : coefficient U V z 0 0 = coefficient F G z i j := by
    change coefficient ((fun _ => Matrix.single 0 i 1) * F)
      (G * fun _ => Matrix.single j 0 1) z 0 0 = _
    rw [left_constant, right_constant]
    simp [Pi.mul_apply]
  rw [← outer_entries]
  have split_input : V = ∑ k : Fin 4, E k 0 * (E 0 k * V) := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, split_identity, one_mul]
  have split_output := congrArg (fun X : Symbol => coefficient U X z 0 0) split_input
  calc
    coefficient U V z 0 0 =
        ∑ k : Fin 4, coefficient U (E k 0 * (E 0 k * V)) z 0 0 := by
          simpa only [map_sum, Finset.sum_apply, Matrix.sum_apply] using split_output
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      change coefficient U ((fun _ => Matrix.single k 0 1) * (E 0 k * V)) z 0 0 = _
      rw [← middle_constant]
      change coefficient (E 0 i * F * E k 0) (E 0 k * (G * E j 0)) z 0 0 = _
      rw [← mul_assoc (E 0 k), isolate, isolate]

open scoped Matrix.Norms.Elementwise ContDiff
abbrev Axis := Fin 4 ⊕ Fin 4
inductive Slot | left | right deriving DecidableEq
instance : Fintype Slot := ⟨{.left, .right}, fun s => by cases s <;> simp⟩
abbrev Variable := Slot × Axis
abbrev DifferentialSymbol := MvPolynomial Variable ℂ

def direction : Axis → PhasePoint
  | .inl μ => (Pi.single μ 1, 0)
  | .inr μ => (0, Pi.single μ 1)

def directional (i : Axis) (F : Symbol) : Symbol := fun z r s => fderiv ℝ (fun y => F y r s) z (direction i)

/-- Apply a list of differentiations before multiplying the matrices. -/
def differentiated_product : List Variable → Symbol → Symbol → Symbol
  | [], F, G => F * G
  | (.left, i) :: rest, F, G => differentiated_product rest (directional i F) G
  | (.right, i) :: rest, F, G => differentiated_product rest F (directional i G)

def derivative_word (degree : Variable →₀ ℕ) : List Variable :=
  (Finset.univ : Finset Variable).toList.flatMap fun j => List.replicate (degree j) j

/-- Constant-coefficient bidifferential operator in commuting derivative coordinates.
The fixed ordering of each multi-index represents the mixed partials on smooth fields. -/
def differential_operator (F G : Symbol) : DifferentialSymbol →ₗ[ℂ] Symbol :=
  (Finsupp.linearCombination ℂ (fun degree => differentiated_product (derivative_word degree) F G)).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

def contraction (s t : Slot) : DifferentialSymbol :=
  ∑ μ : Fin 4, (MvPolynomial.X (s, Sum.inr μ) * MvPolynomial.X (t, Sum.inl μ) -
    MvPolynomial.X (s, Sum.inl μ) * MvPolynomial.X (t, Sum.inr μ))

def canonical_symbol := contraction .left .right

abbrev RealPhaseCovector := Axis → ℝ
def omega (x y : RealPhaseCovector) : ℝ :=
  ∑ μ : Fin 4, (x (.inr μ) * y (.inl μ) - x (.inl μ) * y (.inr μ))

theorem lemma_omega_skew (x y : RealPhaseCovector) : omega x y = -omega y x := by
  simp only [omega, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intros
  ring

theorem lemma_omega_self (x : RealPhaseCovector) : omega x x = 0 := by
  linarith [lemma_omega_skew x x]

theorem lemma_omega_linear_right (x y z : RealPhaseCovector) (r : ℝ) :
    omega x (y + r • z) = omega x y + r * omega x z := by
  simp only [omega, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros
  ring

theorem lemma_omega_linear_left (x y z : RealPhaseCovector) (r : ℝ) :
    omega (y + r • z) x = omega y x + r * omega z x := by
  rw [lemma_omega_skew (y + r • z), lemma_omega_linear_right,
    lemma_omega_skew x y, lemma_omega_skew x z]
  ring

theorem lemma_omega_sub_left (x y z : RealPhaseCovector) : omega (x-y) z = omega x z - omega y z := by
  simpa [sub_eq_add_neg] using lemma_omega_linear_left z x y (-1)

theorem lemma_omega_sub_right (x y z : RealPhaseCovector) : omega z (x-y) = omega z x - omega z y := by
  simpa [sub_eq_add_neg] using lemma_omega_linear_right z x y (-1)

/-- Symplectic transvection with direction d and strength t. -/
def shear (d : RealPhaseCovector) (t : ℝ) (x : RealPhaseCovector) := x + (t * omega d x) • d

theorem lemma_shear_preserves_pairing (d : RealPhaseCovector) (t : ℝ) (x y : RealPhaseCovector) :
    omega (shear d t x) (shear d t y) = omega x y := by
  simp only [shear, lemma_omega_linear_left, lemma_omega_linear_right, lemma_omega_self,
    mul_zero, add_zero]
  rw [lemma_omega_skew x d]
  ring

def canonical_shear (d : RealPhaseCovector) (t : ℝ) : RealPhaseCovector ≃ₗ[ℝ] RealPhaseCovector where
  toFun := shear d t
  invFun := shear d (-t)
  left_inv x := by
    simp only [shear, lemma_omega_linear_right, lemma_omega_self, mul_zero, add_zero]
    module
  right_inv x := by
    simp only [shear, lemma_omega_linear_right, lemma_omega_self, mul_zero, add_zero]
    module
  map_add' x y := by
    have h := lemma_omega_linear_right d x y 1
    simp at h
    simp only [shear, h]
    module
  map_smul' r x := by
    have lin : omega d (r • x) = r * omega d x := by
      simpa [show omega d 0 = 0 by simp [omega]] using lemma_omega_linear_right d 0 x r
    simp only [shear, lin, RingHom.id_apply]
    module

/-- A symplectic map carrying x to y whenever their pairing is nonzero. -/
def move (x y : RealPhaseCovector) := canonical_shear (y-x) (omega y x)⁻¹

theorem lemma_move_hits (x y : RealPhaseCovector) (h : omega y x ≠ 0) : move x y x = y := by
  change x + (_ * omega (y-x) x) • (y-x) = y
  rw [lemma_omega_sub_left, lemma_omega_self, sub_zero, inv_mul_cancel₀ h, one_smul]
  abel

theorem lemma_move_fixes (x y e : RealPhaseCovector) (h : omega y e = omega x e) : move x y e = e := by
  change e + (_ * omega (y-x) e) • (y-x) = e
  rw [lemma_omega_sub_left, h, sub_self, mul_zero, zero_smul, add_zero]

theorem lemma_move_preserves (x y a b : RealPhaseCovector) : omega (move x y a) (move x y b) = omega a b :=
  lemma_shear_preserves_pairing _ _ _ _

/-- A linear interpolation needs to avoid only two bad parameter values. -/
theorem lemma_choose_intermediate (a b c d : ℝ) (ha : a ≠ 0) (hd : d ≠ 0) :
    ∃ t : ℝ, a + t*b ≠ 0 ∧ c + t*d ≠ 0 := by
  by_cases hc : c = 0
  · by_cases hab : a+b = 0
    · exact ⟨2, by intro h; apply ha; linarith, by intro h; apply hd; linarith⟩
    · exact ⟨1, by simpa using hab, by simpa [hc] using hd⟩
  · exact ⟨0, by simpa using ha, by simpa using hc⟩

set_option maxHeartbeats 1600000 in
/-- Transitivity on ordered pairs with equal nonzero symplectic area. The first
two transvections place x at e. The remaining two fix e and place y at f. -/
theorem lemma_canonical_map_between_covector_pairs (x y e f : RealPhaseCovector) (area_ne : omega x y ≠ 0)
    (same_area : omega e f = omega x y) :
    ∃ T : RealPhaseCovector ≃ₗ[ℝ] RealPhaseCovector, (∀ a b, omega (T a) (T b) = omega a b) ∧ T x = e ∧ T y = f := by
  have hyx : omega y x ≠ 0 := by rw [lemma_omega_skew y x]; exact neg_ne_zero.mpr area_ne
  have hef : omega e f ≠ 0 := by rwa [same_area]
  obtain ⟨t, ht₁, ht₂⟩ := lemma_choose_intermediate
    (omega y x) (omega f x) (omega e y) (omega e f) hyx hef
  let middle := y + t • f
  let T := (move x middle).trans (move middle e)
  have T_preserves (a b) : omega (T a) (T b) = omega a b :=
    (lemma_move_preserves middle e (move x middle a) (move x middle b)).trans
      (lemma_move_preserves x middle a b)
  have Tx : T x = e := by
    change move middle e (move x middle x) = e
    rw [lemma_move_hits _ _ (by simpa [middle, lemma_omega_linear_left] using ht₁),
      lemma_move_hits _ _ (by simpa [middle, lemma_omega_linear_right] using ht₂)]
  let b := T y
  have heb : omega e b = omega e f := calc
    omega e b = omega (T x) (T y) := by rw [Tx]
    _ = omega x y := T_preserves x y
    _ = omega e f := same_area.symm
  by_cases direct : omega f b ≠ 0
  · refine ⟨T.trans (move b f), fun a c => (lemma_move_preserves b f (T a) (T c)).trans (T_preserves a c),
      ?_, lemma_move_hits b f direct⟩
    change move b f (T x) = e
    rw [Tx]
    apply lemma_move_fixes
    rw [lemma_omega_skew f e, lemma_omega_skew b e, heb]
  · let c := b + (1 : ℝ) • e
    have hcb : omega c b ≠ 0 := by
      change omega (b + (1:ℝ) • e) b ≠ 0
      rw [lemma_omega_linear_left, lemma_omega_self, zero_add, one_mul, heb]
      exact hef
    have hfc : omega f c ≠ 0 := by
      change omega f (b + (1:ℝ) • e) ≠ 0
      rw [lemma_omega_linear_right, not_ne_iff.mp direct, zero_add, one_mul, lemma_omega_skew f e]
      exact neg_ne_zero.mpr hef
    have hce : omega c e = omega b e := by
      change omega (b + (1:ℝ) • e) e = _
      rw [lemma_omega_linear_left, lemma_omega_self, mul_zero, add_zero]
    have hfe : omega f e = omega b e := by rw [lemma_omega_skew f e, lemma_omega_skew b e, heb]
    refine ⟨(T.trans (move b c)).trans (move c f), fun a d =>
      (lemma_move_preserves c f (move b c (T a)) (move b c (T d))).trans
        ((lemma_move_preserves b c (T a) (T d)).trans (T_preserves a d)), ?_, ?_⟩
    · change move c f (move b c (T x)) = e
      rw [Tx, lemma_move_fixes _ _ _ hce, lemma_move_fixes _ _ _ (hfe.trans hce.symm)]
    · change move c f (move b c b) = f
      rw [lemma_move_hits _ _ hcb, lemma_move_hits _ _ hfc]

/-- Evaluate a general differential symbol on two real covectors. Complex
coefficients are allowed. Covariance is required only for real canonical maps. -/
def real_variables (x y : RealPhaseCovector) : Variable → ℂ
  | (.left, i) => x i
  | (.right, i) => y i

def symbol_value (p : DifferentialSymbol) (x y : RealPhaseCovector) : ℂ :=
  MvPolynomial.eval (real_variables x y) p

def ansatz_symplectic_covariance (p : DifferentialSymbol) : Prop :=
  ∀ (T : RealPhaseCovector ≃ₗ[ℝ] RealPhaseCovector), (∀ x y, omega (T x) (T y) = omega x y) →
    ∀ x y, symbol_value p (T x) (T y) = symbol_value p x y

/-- A18. Only the grading in the second argument is needed for uniqueness. -/
def ansatz_order_homogeneity (n : ℕ) (p : DifferentialSymbol) : Prop :=
  ∀ (r : ℝ) x y, symbol_value p x (r • y) = (r : ℂ)^n * symbol_value p x y

def reference_p : RealPhaseCovector := Pi.single (.inr 0) 1
def reference_x : RealPhaseCovector := Pi.single (.inl 0) 1

theorem lemma_reference_pair : omega reference_p reference_x = 1 := by
  norm_num [omega, reference_p, reference_x, Fin.sum_univ_four, Pi.single_apply]

theorem lemma_canonical_symbol_value (x y : RealPhaseCovector) :
    symbol_value canonical_symbol x y = (omega x y : ℂ) := by
  simp [symbol_value, canonical_symbol, contraction, real_variables, omega]

theorem lemma_real_symbol_ext {p q : DifferentialSymbol}
    (agree : ∀ x y, symbol_value p x y = symbol_value q x y) : p = q := by
  apply MvPolynomial.funext_set (fun _ : Variable => Set.range ((↑) : ℝ → ℂ))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro v hv
  have real_at (j : Variable) : ∃ r : ℝ, (r : ℂ) = v j := hv j (Set.mem_univ j)
  choose w hw using real_at
  have coordinates : real_variables (fun i => w (.left,i)) (fun i => w (.right,i)) = v := by
    funext j
    obtain ⟨s,i⟩ := j
    cases s <;> exact hw _
  simpa only [symbol_value, coordinates] using
    agree (fun i => w (.left,i)) (fun i => w (.right,i))

/-- Classify an arbitrary polynomial in all sixteen derivative coordinates.
Pairs with the same nonzero Poisson pairing are related by a canonical transformation.
Covariance gives equal symbol values on these pairs. Grading fixes the power of the pairing. Multiplying by Ω before polynomial cancellation
also covers degenerate pairs, with no division on the zero-area locus. -/
theorem theorem_canonical_form_of_scalar_symbol (n : ℕ) (p : DifferentialSymbol)
    (covariant : ansatz_symplectic_covariance p)
    (homogeneous : ansatz_order_homogeneity n p) :
    p = symbol_value p reference_p reference_x • canonical_symbol ^ n := by
  have unit_value := lemma_canonical_symbol_value reference_p reference_x
  rw [lemma_reference_pair] at unit_value
  have nonzero : canonical_symbol ≠ 0 := by
    intro h
    simp [h, symbol_value] at unit_value
  apply mul_left_cancel₀ nonzero
  apply lemma_real_symbol_ext
  intro x y
  let area := omega x y
  change MvPolynomial.eval (real_variables x y) _ = MvPolynomial.eval (real_variables x y) _
  simp only [map_mul, MvPolynomial.smul_eq_C_mul, map_pow, MvPolynomial.eval_C]
  change symbol_value canonical_symbol x y * symbol_value p x y =
    symbol_value canonical_symbol x y * (_ * symbol_value canonical_symbol x y ^ n)
  rw [lemma_canonical_symbol_value]
  by_cases h : area = 0
  · simp [show omega x y = 0 from h]
  · have target_area : omega reference_p (area • reference_x) = omega x y := by
      simpa [lemma_reference_pair, show omega reference_p 0 = 0 by simp [omega], area] using
        lemma_omega_linear_right reference_p 0 reference_x area
    obtain ⟨T, canonical, Tx, Ty⟩ := lemma_canonical_map_between_covector_pairs x y reference_p (area • reference_x)
      h target_area
    have value := covariant T canonical x y
    rw [Tx, Ty, homogeneous] at value
    rw [← value]
    ring

def poisson_power (n : ℕ) (F G : Symbol) := differential_operator F G (canonical_symbol ^ n)

abbrev ComplexPhaseCovector := PhasePoint →L[ℝ] ℂ

/-- Auxiliary smooth field used to identify the coefficients of a differential operator.
Differentiation along v multiplies this field by ξ(v). Evaluating associativity
on three such fields therefore gives the scalar identity in Eq. (69). -/
def exponential_field (ξ : ComplexPhaseCovector) (A : SpinMatrix) : Symbol := fun z => Complex.exp (ξ z) • A

theorem lemma_exponential_field_derivative (ξ : ComplexPhaseCovector) (A : SpinMatrix) (i : Axis) :
    directional i (exponential_field ξ A) = exponential_field ξ ((ξ (direction i)) • A) := by
  funext z r s
  have deriv := ((ξ.hasFDerivAt (x := z)).cexp.smul_const (A r s)).fderiv
  change fderiv ℝ (fun y => Complex.exp (ξ y) • A r s) z (direction i) = _
  rw [deriv]
  simp [exponential_field, mul_assoc]

def derivative_coordinates (ξ η : ComplexPhaseCovector) : Variable → ℂ
  | (.left, i) => ξ (direction i)
  | (.right, i) => η (direction i)

theorem lemma_word_on_exponential_fields (word : List Variable) (ξ η : ComplexPhaseCovector) (A B : SpinMatrix) :
    differentiated_product word (exponential_field ξ A) (exponential_field η B) =
      exponential_field (ξ+η) ((word.map (derivative_coordinates ξ η)).prod • (A*B)) := by
  induction word generalizing A B with
  | nil =>
    funext z
    simp [differentiated_product, exponential_field, Pi.mul_apply, Complex.exp_add,
      smul_smul, mul_comm]
  | cons j rest ih =>
    obtain ⟨s,i⟩ := j
    cases s <;> simp [differentiated_product, lemma_exponential_field_derivative, ih, derivative_coordinates,
      smul_smul, mul_comm]

theorem lemma_word_weight (d : Variable →₀ ℕ) (v : Variable → ℂ) :
    ((derivative_word d).map v).prod = ∏ j, v j ^ d j := by
  have expand (xs : List Variable) :
      ((xs.flatMap fun j => List.replicate (d j) j).map v).prod =
        (xs.map fun j => v j ^ d j).prod := by
    induction xs with
    | nil => simp
    | cons i rest ih => simp [ih]
  exact (expand _).trans (Finset.prod_map_toList _ _)

theorem lemma_operator_on_exponential_fields (p : DifferentialSymbol) (ξ η : ComplexPhaseCovector) (A B : SpinMatrix) :
    differential_operator (exponential_field ξ A) (exponential_field η B) p =
      exponential_field (ξ+η) (MvPolynomial.eval (derivative_coordinates ξ η) p • (A*B)) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    change Finsupp.linearCombination ℂ (fun e => differentiated_product (derivative_word e) (exponential_field ξ A) (exponential_field η B)) (Finsupp.single d c) = _
    rw [Finsupp.linearCombination_single]
    simp only [lemma_word_on_exponential_fields, lemma_word_weight, MvPolynomial.eval_monomial,
      d.prod_fintype (fun j k => derivative_coordinates ξ η j ^ k) (fun _ => pow_zero _)]
    funext z
    simp [exponential_field, smul_smul, mul_left_comm]
  | add p q hp hq =>
    rw [map_add, hp, hq, map_add, add_smul]
    funext z
    simp [exponential_field, smul_add]

theorem lemma_operator_one (F G : Symbol) : differential_operator F G 1 = F * G := by
  change Finsupp.linearCombination ℂ (fun e => differentiated_product (derivative_word e) F G) (Finsupp.single 0 1) = _
  have empty_word : derivative_word 0 = [] := List.flatMap_eq_nil_iff.mpr (by simp)
  simp [empty_word, differentiated_product]

/-- A constant-coefficient bidifferential operator on matrix-neutral symbols is
specified by an arbitrary complex polynomial in the two sets of eight derivative
coordinates. The same scalar bidifferential operator acts on all matrix components,
with the ordinary internal contraction of Eq. (55). Translation invariance is
expressed by constant coefficients. No choice of Poisson contractions is made. -/
def ansatz_constant_differential_symbol (C : ℕ → Symbol → Symbol → Symbol)
    (p : ℕ → DifferentialSymbol) : Prop :=
  ∀ n F G, C n F G = differential_operator F G (p n)

def scalar_coefficient (p : ℕ → DifferentialSymbol) (n : ℕ) : ℂ :=
  symbol_value (p n) reference_p reference_x

/-- Eq. (61). At order n, canonical covariance and homogeneity reduce the scalar
operator to a coefficient times n Poisson contractions between the two fields. -/
theorem theorem_scalar_poisson_contraction_formula (C : ℕ → Symbol → Symbol → Symbol)
    (p : ℕ → DifferentialSymbol) (ansatz_locality : ansatz_constant_differential_symbol C p)
    (ansatz_covariance : ∀ n, ansatz_symplectic_covariance (p n))
    (ansatz_grading : ∀ n, ansatz_order_homogeneity n (p n))
    (n : ℕ) (F G : Symbol) : C n F G = scalar_coefficient p n • poisson_power n F G := by
  rw [ansatz_locality, theorem_canonical_form_of_scalar_symbol n (p n) (ansatz_covariance n)
    (ansatz_grading n), map_smul]
  rfl

/-- Contract the two phase-space covectors with the canonical Poisson tensor. -/
def pairing (ξ η : ComplexPhaseCovector) : ℂ := MvPolynomial.eval (derivative_coordinates ξ η) canonical_symbol

theorem lemma_pairing_formula (ξ η : ComplexPhaseCovector) :
    pairing ξ η = ∑ μ : Fin 4, (ξ (direction (.inr μ)) * η (direction (.inl μ)) -
      ξ (direction (.inl μ)) * η (direction (.inr μ))) := by
  simp [pairing, canonical_symbol, contraction, derivative_coordinates]

theorem lemma_poisson_power_on_exponential_fields (n : ℕ) (ξ η : ComplexPhaseCovector) (A B : SpinMatrix) :
    poisson_power n (exponential_field ξ A) (exponential_field η B) = exponential_field (ξ+η) (pairing ξ η ^ n • (A*B)) := by
  rw [poisson_power, lemma_operator_on_exponential_fields, map_pow]
  rfl

def smooth_symbol (F : Symbol) : Prop := ∀ i j, ContDiff ℝ ∞ (fun z => F z i j)

theorem lemma_exponential_field_is_smooth (ξ : ComplexPhaseCovector) (A : SpinMatrix) : smooth_symbol (exponential_field ξ A) := by
  intro i j
  exact ξ.contDiff.cexp.mul contDiff_const

/-- The algebra of smooth matrix symbols. Keeping smoothness in the type lets
A12 assert genuine bilinearity and closure under each product coefficient. -/
def smooth_matrix_algebra : Subalgebra ℂ Symbol where
  carrier := {F | smooth_symbol F}
  add_mem' hF hG := fun i j => (hF i j).add (hG i j)
  mul_mem' {F G} hF hG := by
    intro i j
    change ContDiff ℝ ∞ (fun z => ∑ k, F z i k * G z k j)
    exact ContDiff.sum (fun k _ => (hF i k).mul (hG k j))
  algebraMap_mem' c := fun _ _ => contDiff_const

abbrev SmoothMatrixSymbol := ↥smooth_matrix_algebra

theorem lemma_smooth_sum {ι : Type*} (s : Finset ι) (f : ι → SmoothMatrixSymbol) :
    ((∑ i ∈ s, f i : SmoothMatrixSymbol) : Symbol) = ∑ i ∈ s, (f i : Symbol) :=
  map_sum smooth_matrix_algebra.val f s

def constant_matrix (A : SpinMatrix) : SmoothMatrixSymbol := ⟨fun _ => A, fun _ _ => contDiff_const⟩

def corner (F : Symbol) (i j : Fin 4) : Symbol := fun z => Matrix.single 0 0 (F z i j)
def smooth_corner (F : SmoothMatrixSymbol) (i j : Fin 4) : SmoothMatrixSymbol := by
  refine ⟨corner F i j, ?_⟩
  intro r s
  by_cases h : (0 : Fin 4) = r ∧ (0 : Fin 4) = s
  · simpa only [corner, Matrix.single_apply, ite_eq_left h] using F.property i j
  · simp only [corner, Matrix.single_apply, ite_eq_right h]
    exact contDiff_const

/-- Assembling the scalar operator on the entries implements ordinary matrix
multiplication after differentiation. The equality is valid for any polynomial. -/
theorem lemma_operator_matrix_entries (p : DifferentialSymbol) (F G : Symbol)
    (z : PhasePoint) (i j : Fin 4) :
    differential_operator F G p z i j = ∑ k, differential_operator
      (corner F i k) (corner G k j) p z 0 0 := by
  have derivative_corner (d : Axis) (X : Symbol) (a b : Fin 4) :
      directional d (corner X a b) = corner (directional d X) a b := by
    funext y r s
    by_cases h : (0 : Fin 4) = r ∧ (0 : Fin 4) = s
    · simp only [corner, directional, Matrix.single_apply, ite_eq_left h]
    · simp only [corner, directional, Matrix.single_apply, ite_eq_right h, fderiv_const_apply, zero_apply]
  have word_entries (w : List Variable) (X Y : Symbol) :
      differentiated_product w X Y z i j = ∑ k, differentiated_product w
        (corner X i k) (corner Y k j) z 0 0 := by
    induction w generalizing X Y with
    | nil =>
      change (X z * Y z) i j = ∑ k, (Matrix.single 0 0 (X z i k) * Matrix.single 0 0 (Y z k j) : SpinMatrix) 0 0
      simp only [Matrix.single_mul_single_same, Matrix.single_apply_same]
      rfl
    | cons d rest ih =>
      obtain ⟨slot, axis⟩ := d
      cases slot <;> simp only [differentiated_product, derivative_corner] <;> apply ih
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have monomial (X Y : Symbol) : differential_operator X Y (MvPolynomial.monomial d c) =
        c • differentiated_product (derivative_word d) X Y :=
      Finsupp.linearCombination_single ..
    simp only [monomial, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      word_entries (derivative_word d) F G]
  | add p q hp hq => simp only [map_add, Pi.add_apply, Matrix.add_apply, Finset.sum_add_distrib, hp, hq]

abbrev CoefficientFamily := ℕ → SmoothMatrixSymbol →ₗ[ℂ] SmoothMatrixSymbol →ₗ[ℂ] SmoothMatrixSymbol

/-- A16, stated for the proposed product on the smooth matrix algebra. -/
def ansatz_matrix_associativity (C : CoefficientFamily) : Prop :=
  ∀ n F G K,
    (∑ k ∈ Finset.range (n+1), C (n-k) (C k F G) K) =
    (∑ k ∈ Finset.range (n+1), C (n-k) F (C k G K))

/-- A15, including ordinary multiplication at order zero on constant matrices. -/
def ansatz_constant_matrix_neutrality (C : CoefficientFamily) : Prop :=
  ∀ n A F, C n (constant_matrix A) F = (if n=0 then constant_matrix A * F else 0) ∧
    C n F (constant_matrix A) = (if n=0 then F * constant_matrix A else 0)

/-- Moving a constant through the two nested products in A16 and taking the
order-n coefficient gives all three balancing identities. -/
theorem lemma_balancing_from_associativity (C : CoefficientFamily)
    (assoc : ansatz_matrix_associativity C) (neutral : ansatz_constant_matrix_neutrality C)
    (n : ℕ) (A : SpinMatrix) (F G : SmoothMatrixSymbol) :
    C n (constant_matrix A * F) G = constant_matrix A * C n F G ∧
    C n (F * constant_matrix A) G = C n F (constant_matrix A * G) ∧
    C n F (G * constant_matrix A) = C n F G * constant_matrix A := by
  have first := assoc n (constant_matrix A) F G
  have middle := assoc n F (constant_matrix A) G
  have last := assoc n F G (constant_matrix A)
  have pick_last (f : ℕ → SmoothMatrixSymbol) :
      (∑ k ∈ Finset.range (n+1), if n-k=0 then f k else 0) = f n := by
    rw [Finset.sum_eq_single n]
    · simp
    · intro k hk hkn
      have pos : n-k ≠ 0 := by simp at hk; omega
      simp [pos]
    · simp
  simp only [(neutral _ _ _).1, (neutral _ _ _).2, apply_ite, DFunLike.ite_apply, LinearMap.zero_apply,
    map_zero, pick_last] at first middle last
  simpa using And.intro first (And.intro middle last.symm)

/-- Eq. (55) on smooth matrix fields. This form uses only A15, A16 and the
bilinearity in the coefficient type. The scalar coefficient is recovered by testing
matrices with a single nonzero entry, so the locality premise below is scalar. -/
theorem lemma_smooth_matrix_contraction (C : CoefficientFamily)
    (assoc : ansatz_matrix_associativity C) (neutral : ansatz_constant_matrix_neutrality C)
    (n : ℕ) (F G : SmoothMatrixSymbol) (z : PhasePoint) (i j : Fin 4) :
    (C n F G : Symbol) z i j = ∑ k, (C n (smooth_corner F i k) (smooth_corner G k j) : Symbol) z 0 0 := by
  let E (r s : Fin 4) := constant_matrix (Matrix.single r s 1)
  have isolate (X : SmoothMatrixSymbol) (r s : Fin 4) :
      E 0 r * X * E s 0 = smooth_corner X r s := by
    apply Subtype.ext
    funext y
    change Matrix.single 0 r 1 * (X : Symbol) y * Matrix.single s 0 1 = _
    simp [smooth_corner, corner]
  have split_identity : (∑ k : Fin 4, E k 0 * E 0 k) = 1 := by
    apply Subtype.ext
    change (∑ k : Fin 4, (E k 0 : Symbol) * (E 0 k : Symbol)) = 1
    funext y
    simp [E, constant_matrix, Finset.sum_apply, Pi.mul_apply, Matrix.sum_single_one]
  let U := E 0 i * F
  let V := G * E j 0
  have outer : C n U V = E 0 i * C n F G * E j 0 := by
    change C n (constant_matrix _ * F) (G * constant_matrix _) = _
    rw [(lemma_balancing_from_associativity C assoc neutral ..).1,
      (lemma_balancing_from_associativity C assoc neutral ..).2.2, mul_assoc]
  have split_input : V = ∑ k : Fin 4, E k 0 * (E 0 k * V) := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, split_identity, one_mul]
  have split_output := congrArg (fun X => C n U X) split_input
  simp only [map_sum] at split_output
  have term (k : Fin 4) : C n U (E k 0 * (E 0 k * V)) =
      C n (smooth_corner F i k) (smooth_corner G k j) := by
    rw [← (lemma_balancing_from_associativity C assoc neutral n (Matrix.single k 0 1) U (E 0 k * V)).2.1]
    change C n (E 0 i * F * E k 0) (E 0 k * (G * E j 0)) = _
    rw [← mul_assoc (E 0 k), isolate, isolate]
  simp_rw [term] at split_output
  rw [outer] at split_output
  have entry := congrArg (fun X : SmoothMatrixSymbol => (X : Symbol) z 0 0) split_output
  simpa [E, constant_matrix, Pi.mul_apply, Finset.sum_apply, Matrix.sum_apply] using entry

/-- A12 and A14 on the scalar corner only. Each scalar differential symbol
has arbitrary complex coefficients in sixteen variables. The scalar inputs
in this equation range over all smooth fields through the entries of F and G. -/
def ansatz_scalar_locality (C : CoefficientFamily) (p : ℕ → DifferentialSymbol) : Prop :=
  ∀ n (F G : SmoothMatrixSymbol) i k j z,
    (C n (smooth_corner F i k) (smooth_corner G k j) : Symbol) z 0 0 =
    differential_operator (corner F i k) (corner G k j) (p n) z 0 0

theorem theorem_neutral_extension (C : CoefficientFamily) (p : ℕ → DifferentialSymbol)
    (locality : ansatz_scalar_locality C p) (assoc : ansatz_matrix_associativity C)
    (neutral : ansatz_constant_matrix_neutrality C)
    (n : ℕ) (F G : SmoothMatrixSymbol) :
    (C n F G : Symbol) = differential_operator F G (p n) := by
  funext z i j
  rw [lemma_smooth_matrix_contraction C assoc neutral, lemma_operator_matrix_entries]
  exact Finset.sum_congr rfl (fun k _ => locality n F G i k j z)

/-- A16 for lambda-independent smooth arguments. Both sides are actual nested
products at order n of the same C used in transport. -/
def ansatz_associative_composition (C : ℕ → Symbol → Symbol → Symbol) : Prop :=
  ∀ n F G K, smooth_symbol F → smooth_symbol G → smooth_symbol K →
    (∑ k ∈ Finset.range (n+1), C (n-k) (C k F G) K) =
    (∑ k ∈ Finset.range (n+1), C (n-k) F (C k G K))

def coordinate_covector (i : Axis) : ComplexPhaseCovector :=
  let entry (μ : Fin 4) : Coordinates →L[ℝ] ℝ := ContinuousLinearMap.proj μ
  match i with
  | .inl μ => Complex.ofRealCLM.comp ((entry μ).comp (ContinuousLinearMap.fst ℝ _ _))
  | .inr μ => Complex.ofRealCLM.comp ((entry μ).comp (ContinuousLinearMap.snd ℝ _ _))

/-- Two canonical coordinate pairs realise all three pairwise contractions
independently, including the cases when one or more vanish. -/
theorem lemma_realise_three_pairings (u v w : ℂ) :
    ∃ ξ η ζ : ComplexPhaseCovector, pairing ξ η = u ∧ pairing η ζ = v ∧ pairing ξ ζ = w := by
  use coordinate_covector (.inr 0),
    u • coordinate_covector (.inl 0) + coordinate_covector (.inr 1),
    w • coordinate_covector (.inl 0) + v • coordinate_covector (.inl 1)
  simp [lemma_pairing_formula, Fin.sum_univ_four, coordinate_covector, direction, Pi.single_apply]

theorem lemma_pairing_add_left (ξ η ζ : ComplexPhaseCovector) :
    pairing (ξ+η) ζ = pairing ξ ζ + pairing η ζ := by
  simp only [lemma_pairing_formula, add_apply, add_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros
  ring

theorem lemma_pairing_add_right (ξ η ζ : ComplexPhaseCovector) :
    pairing ξ (η+ζ) = pairing ξ η + pairing ξ ζ := by
  simp only [lemma_pairing_formula, add_apply, mul_add,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros
  ring

theorem lemma_scalar_times_exponential_field (c : ℂ) (ξ : ComplexPhaseCovector) (A : SpinMatrix) :
    c • exponential_field ξ A = exponential_field ξ (c • A) := by
  funext z
  simp [exponential_field, smul_smul, mul_comm]

/-- Test A16 on exponential symbols times the identity matrix. Differentiation
and multiplication of these functions give the Poisson pairings on both sides.
Evaluation at the origin removes the common exponential. -/
theorem theorem_associativity_on_three_pairings (C : ℕ → Symbol → Symbol → Symbol)
    (a : ℕ → ℂ) (reduction : ∀ n F G, C n F G = a n • poisson_power n F G)
    (associativity : ansatz_associative_composition C) (n : ℕ) (u v w : ℂ) :
    (∑ k ∈ Finset.range (n+1), (a k * a (n-k)) * u^k * (v+w)^(n-k)) =
    (∑ k ∈ Finset.range (n+1), (a k * a (n-k)) * v^k * (u+w)^(n-k)) := by
  obtain ⟨ξ, η, ζ, first_pair, second_pair, outside_pair⟩ := lemma_realise_three_pairings u v w
  have product_on_exponential_fields (r : ℕ) (f g : ComplexPhaseCovector) (A B : SpinMatrix) :
      C r (exponential_field f A) (exponential_field g B) = exponential_field (f+g) ((a r * pairing f g ^ r) • (A*B)) := by
    rw [reduction, lemma_poisson_power_on_exponential_fields, lemma_scalar_times_exponential_field, smul_smul]
  have nested := associativity n (exponential_field ξ 1) (exponential_field η 1) (exponential_field ζ 1)
    (lemma_exponential_field_is_smooth _ _) (lemma_exponential_field_is_smooth _ _) (lemma_exponential_field_is_smooth _ _)
  have at_origin := congrArg (fun F : Symbol => F 0 0 0) nested
  simp only [product_on_exponential_fields, Finset.sum_apply, Matrix.sum_apply, exponential_field, map_zero,
    Complex.exp_zero, one_smul, one_mul, mul_one, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, lemma_pairing_add_left, lemma_pairing_add_right, first_pair, second_pair,
    outside_pair] at at_origin
  convert at_origin using 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

def ansatz_classical_product (C : ℕ → Symbol → Symbol → Symbol) : Prop :=
  ∀ F G, smooth_symbol F → smooth_symbol G → C 0 F G = F * G

def ansatz_first_order_weyl_matching (C : ℕ → Symbol → Symbol → Symbol) : Prop :=
  ∀ F G, smooth_symbol F → smooth_symbol G →
    C 1 F G - C 1 G F = (Complex.I / 2) • (poisson_power 1 F G - poisson_power 1 G F)

theorem lemma_pairing_skew (ξ η : ComplexPhaseCovector) : pairing η ξ = -pairing ξ η := by
  simp only [lemma_pairing_formula, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intros
  ring

theorem lemma_matching_fixes_weights (C : ℕ → Symbol → Symbol → Symbol) (a : ℕ → ℂ)
    (reduction : ∀ n F G, C n F G = a n • poisson_power n F G)
    (ansatz_classical_limit : ansatz_classical_product C)
    (ansatz_matching : ansatz_first_order_weyl_matching C) :
    a 0 = 1 ∧ a 1 = Complex.I / 2 := by
  obtain ⟨ξ, η, _, unit_pair, _, _⟩ := lemma_realise_three_pairings 1 0 0
  have order_zero := congrArg (fun F : Symbol => F 0 0 0)
    (ansatz_classical_limit (exponential_field ξ 1) (exponential_field η 1) (lemma_exponential_field_is_smooth _ _) (lemma_exponential_field_is_smooth _ _))
  have order_one := congrArg (fun F : Symbol => F 0 0 0)
    (ansatz_matching (exponential_field ξ 1) (exponential_field η 1) (lemma_exponential_field_is_smooth _ _) (lemma_exponential_field_is_smooth _ _))
  have reversed_pair := (lemma_pairing_skew ξ η).trans (congrArg Neg.neg unit_pair)
  simp [reduction, lemma_poisson_power_on_exponential_fields, exponential_field, Pi.mul_apply] at order_zero
  simp [reduction, lemma_poisson_power_on_exponential_fields, exponential_field, unit_pair, reversed_pair] at order_one
  exact ⟨order_zero, by linear_combination order_one / 2⟩


open Polynomial in
/-- Equation (69) for polynomial variables follows by evaluating the two
polynomials at arbitrary complex points and using nested-product associativity. -/
theorem theorem_reduced_associativity (C : ℕ → Symbol → Symbol → Symbol) (a : ℕ → ℂ)
    (reduction : ∀ n F G, C n F G = a n • poisson_power n F G)
    (associativity : ansatz_associative_composition C)
    (n : ℕ) (u v w : ℂ[X]) :
    symbol_product_term a n u (v+w) = symbol_product_term a n v (u+w) := by
  apply Polynomial.funext
  intro x
  simpa [symbol_product_term, Polynomial.eval_finsetSum] using
    theorem_associativity_on_three_pairings C a reduction associativity n
      (u.eval x) (v.eval x) (w.eval x)

def weyl_transport (H W : Symbol) : Symbol :=
  (1/2 : ℂ) • (poisson_power 1 H W - poisson_power 1 W H)

def moyal_coefficient (n : ℕ) (F G : Symbol) : Symbol :=
  ((Complex.I / 2) ^ n / (n.factorial : ℂ)) • poisson_power n F G

/-- Theorem 9. The reduction, Eq. (69) and the two initial coefficients are
all intermediate conclusions. The assumptions refer to the proposed product C. -/
theorem lemma_composition_is_moyal (C : ℕ → Symbol → Symbol → Symbol)
    (p : ℕ → DifferentialSymbol)
    (ansatz_locality : ansatz_constant_differential_symbol C p)
    (ansatz_covariance : ∀ n, ansatz_symplectic_covariance (p n))
    (ansatz_grading : ∀ n, ansatz_order_homogeneity n (p n))
    (ansatz_associativity : ansatz_associative_composition C)
    (ansatz_classical_limit : ansatz_classical_product C)
    (ansatz_matching : ansatz_first_order_weyl_matching C) :
    C = moyal_coefficient := by
  let a := scalar_coefficient p
  have reduction := theorem_scalar_poisson_contraction_formula C p ansatz_locality ansatz_covariance ansatz_grading
  have associativity_identity := theorem_reduced_associativity C a reduction ansatz_associativity
  obtain ⟨constant_term, first_order⟩ :=
    lemma_matching_fixes_weights C a reduction ansatz_classical_limit ansatz_matching
  funext n F G
  rw [reduction]
  change a n • poisson_power n F G = _
  rw [MinimalArgument.lemma_from_symbol_associativity_to_moyal_weights a constant_term
    associativity_identity first_order n]
  rfl

/-- Selection for a bilinear product on the algebra of smooth matrix symbols.
Locality is required only on a single scalar corner. The proof derives the
neutral extension, classifies its scalar differential symbol, and tests the very same
associative product to determine its weights. -/
theorem theorem_smooth_composition_is_moyal
    (C : CoefficientFamily) (p : ℕ → DifferentialSymbol)
    (ansatz_locality : ansatz_scalar_locality C p)
    (ansatz_covariance : ∀ n, ansatz_symplectic_covariance (p n))
    (ansatz_grading : ∀ n, ansatz_order_homogeneity n (p n))
    (ansatz_associativity : ansatz_matrix_associativity C)
    (ansatz_neutrality : ansatz_constant_matrix_neutrality C)
    (ansatz_classical_limit : ∀ F G, C 0 F G = F * G)
    (ansatz_matching : ∀ (F G : SmoothMatrixSymbol),
      (C 1 F G : Symbol) - (C 1 G F : Symbol) = Complex.I • weyl_transport F G) :
    ∀ n (F G : SmoothMatrixSymbol), (C n F G : Symbol) = moyal_coefficient n F G := by
  let D (n : ℕ) (F G : Symbol) := differential_operator F G (p n)
  have identified (n : ℕ) (F G : SmoothMatrixSymbol) : (C n F G : Symbol) = D n F G :=
    theorem_neutral_extension C p ansatz_locality ansatz_associativity ansatz_neutrality n F G
  have selected : D = moyal_coefficient := by
    apply lemma_composition_is_moyal D p (fun _ _ _ => rfl) ansatz_covariance ansatz_grading
    · intro n F G K hF hG hK
      let f : SmoothMatrixSymbol := ⟨F,hF⟩
      let g : SmoothMatrixSymbol := ⟨G,hG⟩
      let k : SmoothMatrixSymbol := ⟨K,hK⟩
      have left_term (r : ℕ) : (C (n-r) (C r f g) k : Symbol) =
          D (n-r) (D r F G) K := by rw [identified, identified]
      have right_term (r : ℕ) : (C (n-r) f (C r g k) : Symbol) =
          D (n-r) F (D r G K) := by rw [identified, identified]
      have assoc := congrArg (fun X : SmoothMatrixSymbol => (X : Symbol))
        (ansatz_associativity n f g k)
      simpa only [lemma_smooth_sum, left_term, right_term] using assoc
    · intro F G hF hG
      exact (identified 0 ⟨F,hF⟩ ⟨G,hG⟩).symm.trans
        (congrArg Subtype.val (ansatz_classical_limit ⟨F,hF⟩ ⟨G,hG⟩))
    · intro F G hF hG
      have match_first := ansatz_matching ⟨F,hF⟩ ⟨G,hG⟩
      rw [identified, identified, weyl_transport, smul_smul] at match_first
      simpa only [div_eq_mul_inv, one_mul] using match_first
  intro n F G
  rw [identified, selected]

/-- The derivative term supplied by the selected product, in the same symbol
algebra as the spectral equation. -/
theorem lemma_first_moyal_commutator (H W : Symbol) :
    moyal_coefficient 1 H W - moyal_coefficient 1 W H = Complex.I • weyl_transport H W := by
  simp only [moyal_coefficient, pow_one, Nat.factorial_one, Nat.cast_one, div_one,
    weyl_transport, smul_smul, ← smul_sub]
  congr 1
  ring

/-- Lemma 6 in the units of the actual generator H = ΔJ − bI. Absorb Δ into the
unknown correction to use the involution lemma. This keeps the gap 2Δ explicit. -/
theorem lemma_gap_solvability (J B : SpinMatrix) (Δ b : ℝ) (gap_nonzero : Δ ≠ 0)
    (involution : J * J = 1) :
    let H := Δ • J - b • 1
    (∃ Y : SpinMatrix, H * Y - Y * H + B = 0) ↔ J * B * J = -B := by
  dsimp only
  have shift_cancels (Y : SpinMatrix) :
      (Δ • J - b • 1) * Y - Y * (Δ • J - b • 1) =
        J * (Δ • Y) - (Δ • Y) * J := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  rw [lemma_off_diagonal_source_iff_correction_exists J B involution]
  constructor
  · rintro ⟨Y, equation⟩
    exact ⟨Δ • Y, by rwa [shift_cancels] at equation⟩
  · rintro ⟨scaled_correction, equation⟩
    use Δ⁻¹ • scaled_correction
    simpa only [shift_cancels, smul_smul, mul_inv_cancel₀ gap_nonzero, one_smul] using equation

/-- Theorem 10. Read this implication from left to right: the all-order condition
on the selected product supplies its first-order equation. The spectral theorem
then forces the diagonal transport condition at the same phase point.
Here J B J = −B is the vanishing of the diagonal blocks of B. -/
theorem theorem_preservation_implies_projected_transport
    (C : ℕ → Symbol → Symbol → Symbol) (selected_product : C = moyal_coefficient)
    (H : Symbol) (W : ℕ → Symbol) (z : PhasePoint)
    (J : SpinMatrix) (Δ b : ℝ) (gap_nonzero : Δ ≠ 0) (involution : J * J = 1)
    (generator_at_point : H z = Δ • J - b • 1)
    (preservation : ∀ n, commutator_coefficient C H W n = 0) :
    let B := (Complex.I • weyl_transport H (W 0)) z
    (H z * W 1 z - W 1 z * H z + B = 0) ∧ J * B * J = -B := by
  subst C
  have ordinary_product (F G : Symbol) : moyal_coefficient 0 F G = F * G := by
    simp [moyal_coefficient, poisson_power, lemma_operator_one]
  have first_order := (lemma_first_two_hierarchy_coefficients moyal_coefficient ordinary_product H W).2
  rw [lemma_first_moyal_commutator, preservation 1] at first_order
  have at_point := congrFun first_order.symm z
  change H z * W 1 z - W 1 z * H z + (Complex.I • weyl_transport H (W 0)) z = 0 at at_point
  refine ⟨at_point, ?_⟩
  apply (lemma_gap_solvability J _ Δ b gap_nonzero involution).mp
  refine ⟨W 1 z, ?_⟩
  rw [← generator_at_point]
  exact at_point

/-- The complementary part of the first correction is fixed. The left side
is 2Δ Q[Y]. This expression also shows why the diagonal part of Y is free. -/
theorem corollary_complementary_reaction (J Y B : SpinMatrix) (Δ b : ℝ)
    (involution : J * J = 1)
    (first_order : (Δ • J - b • 1) * Y - Y * (Δ • J - b • 1) + B = 0) :
    Δ • (Y - J * Y * J) = -(J * B) := by
  have multiply_by_J := congrArg (fun X : SpinMatrix => J * X) first_order
  simp only [mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one, ← mul_assoc, involution, mul_zero] at multiply_by_J
  rw [smul_sub]
  linear_combination (norm := abel) multiply_by_J

/-- Identify the concrete matrix projector with the endomorphism in the abstract
rank theorem. This makes the rank conclusion refer to the very block used by W₀. -/
theorem lemma_rank_of_matrix_sector (factor : FourMomentum →ₗ[ℝ] SpinMatrix)
    (ansatz_square_identity : ansatz_reproduces_minkowski_square factor)
    (p : FourMomentum) (b : ℝ) (mass_positive : 0 < b)
    (on_shell : minkowski_pairing p p = b ^ 2) :
    Module.finrank ℂ (LinearMap.range
      (Matrix.toLinAlgEquiv' (selected_projector (b⁻¹ • factor p)))) = 2 := by
  let action : SpinMatrix ≃ₐ[ℝ] Module.End ℂ (Fin 4 → ℂ) :=
    Matrix.toLinAlgEquiv'.restrictScalars ℝ
  let represented := action.toLinearMap.comp factor
  have represented_square : ansatz_reproduces_minkowski_square represented := by
    intro q
    change action (factor q) * action (factor q) = _
    rw [← map_mul, ansatz_square_identity q, map_smul, map_one]
  have rank_two := corollary_massive_sector_has_dimension_two represented represented_square
    (by simp) p b mass_positive.ne' on_shell
  change Module.finrank ℂ (LinearMap.range (action (selected_projector (b⁻¹ • factor p)))) = 2
  unfold selected_projector
  rw [map_smul, map_add, map_one, map_smul]
  exact rank_two

/-- A4. The leading ensemble has arbitrary matrix data inside the selected block. -/
def ansatz_selected_leading_density (W₀ P density : SpinMatrix) : Prop :=
  W₀ = P * density * P

/-- A20. Impose every coefficient of the hierarchy on the proposed product. -/
def ansatz_all_order_preservation (C : CoefficientFamily) (H : SmoothMatrixSymbol)
    (W : ℕ → SmoothMatrixSymbol) : Prop :=
  ∀ n, commutator_coefficient (fun r F G => C r F G) H W n = 0

/-- A21. Continue the classical choice of zero sector by the left star equation. -/
def ansatz_continues_left_zero_sector (C : CoefficientFamily) (H : SmoothMatrixSymbol)
    (W : ℕ → SmoothMatrixSymbol) : Prop :=
  ∀ n, (∑ r ∈ Finset.range (n+1), C r H (W (n-r))) = 0

/-- Combined argument at a massive phase point in the four-component
realisation. W is a formal sequence of smooth-symbol representatives. The leading
datum is arbitrary inside the selected block. Universal composition is introduced
on these matrix symbols. Matrix contraction, reduction to powers of P and the reduced
associativity identity are proved from the coefficient-level assumptions. A20 and A21 are distinct premises. No existence of a global formal
solution for arbitrary initial data is asserted. -/
theorem theorem_from_mass_shell_to_transport_and_spectral_equations
    (factor : FourMomentum →ₗ[ℝ] SpinMatrix)
    (ansatz_square_identity : ansatz_reproduces_minkowski_square factor)
    (κ : PhasePoint → FourMomentum) (b : ℝ) (mass_positive : 0 < b)
    (z : PhasePoint) (on_shell : minkowski_pairing (κ z) (κ z) = b ^ 2)
    (Hₛ : SmoothMatrixSymbol) (ansatz_generator : ∀ y, (Hₛ : Symbol) y = factor (κ y) - b • 1)
    (Wₛ : ℕ → SmoothMatrixSymbol) (density : SpinMatrix)
    (C : CoefficientFamily) (p : ℕ → DifferentialSymbol)
    (ansatz_locality : ansatz_scalar_locality C p)
    (ansatz_covariance : ∀ n, ansatz_symplectic_covariance (p n))
    (ansatz_grading : ∀ n, ansatz_order_homogeneity n (p n))
    (ansatz_associativity : ansatz_matrix_associativity C)
    (ansatz_neutrality : ansatz_constant_matrix_neutrality C)
    (ansatz_classical_limit : ∀ F G, C 0 F G = F * G)
    (ansatz_matching : ∀ (F G : SmoothMatrixSymbol),
      (C 1 F G : Symbol) - (C 1 G F : Symbol) = Complex.I • weyl_transport F G) :
    let W := fun n => (Wₛ n : Symbol)
    let J := b⁻¹ • factor (κ z)
    let P := selected_projector J
    let H : Symbol := Hₛ
    let B := (Complex.I • weyl_transport H (W 0)) z
    ansatz_selected_leading_density (W 0 z) P density →
    ansatz_all_order_preservation C Hₛ Wₛ →
    ansatz_continues_left_zero_sector C Hₛ Wₛ →
      Module.finrank ℂ (LinearMap.range (Matrix.toLinAlgEquiv' P)) = 2 ∧
      (H z * W 0 z = 0 ∧ W 0 z * H z = 0) ∧
      (∀ n (F G : SmoothMatrixSymbol), (C n F G : Symbol) = moyal_coefficient n F G) ∧
      (J * B * J = -B ∧ b • (W 1 z - J * W 1 z * J) = -(J * B)) ∧
      (∀ n, (∑ r ∈ Finset.range (n+1), moyal_coefficient r H (W (n-r))) = 0 ∧
        (∑ r ∈ Finset.range (n+1), moyal_coefficient r (W (n-r)) H) = 0) := by
  intro W J P H B ansatz_leading_sector ansatz_preservation ansatz_left_sector
  change W 0 z = P * density * P at ansatz_leading_sector
  have involution : J * J = 1 :=
    lemma_on_shell_normalisation factor ansatz_square_identity (κ z) b mass_positive.ne' on_shell
  have generator_at_point : H z = b • J - b • 1 := by
    simp [H, ansatz_generator, J, smul_smul, mass_positive.ne']
  have classical_constraints : H z * W 0 z = 0 ∧ W 0 z * H z = 0 := by
    have normalised := theorem_projected_distribution_satisfies_both_constraints J density involution
    have scaled_generator : H z = b • (J - 1) := by rw [generator_at_point, smul_sub]
    rw [scaled_generator, ansatz_leading_sector, smul_mul_assoc, mul_smul_comm,
      normalised.1, normalised.2, smul_zero]
    exact ⟨rfl, rfl⟩
  -- The composition postulate now applies to this matrix ensemble.
  have product_selected := theorem_smooth_composition_is_moyal C p ansatz_locality
    ansatz_covariance ansatz_grading ansatz_associativity ansatz_neutrality
    ansatz_classical_limit ansatz_matching
  have preservation (n : ℕ) : commutator_coefficient moyal_coefficient H W n = 0 := by
    have eqn := congrArg (fun X : SmoothMatrixSymbol => (X : Symbol)) (ansatz_preservation n)
    simpa only [commutator_coefficient, lemma_smooth_sum, Subalgebra.coe_sub,
      Subalgebra.coe_zero, product_selected] using eqn
  have left_sector (n : ℕ) : (∑ r ∈ Finset.range (n+1), moyal_coefficient r H (W (n-r))) = 0 := by
    have eqn := congrArg (fun X : SmoothMatrixSymbol => (X : Symbol)) (ansatz_left_sector n)
    simpa only [lemma_smooth_sum, Subalgebra.coe_zero, product_selected] using eqn
  obtain ⟨first_order, projected_transport⟩ := theorem_preservation_implies_projected_transport
    moyal_coefficient rfl H W z J b b mass_positive.ne' involution generator_at_point preservation
  have reaction := corollary_complementary_reaction J (W 1 z) B b b involution
    (by rw [← generator_at_point]; exact first_order)
  have right_sector := MinimalArgument.corollary_from_preservation_to_right_zero_sector moyal_coefficient H W
    preservation left_sector
  have rank_two := lemma_rank_of_matrix_sector factor ansatz_square_identity (κ z) b mass_positive on_shell
  refine ⟨rank_two, classical_constraints, product_selected, ⟨projected_transport, reaction⟩, ?_⟩
  intro n
  exact ⟨left_sector n, right_sector n⟩

end
end CompositionAndTransport
end MassShell

/-! ## A four-component realisation -/

namespace MassShell
noncomputable section
open Matrix
abbrev FourByFour := Matrix (Fin 4) (Fin 4) ℂ

/-- Weyl block form, with the spatial Pauli matrix in the upper right block. -/
def four_component_pencil (p : FourMomentum) : FourByFour :=
  let t : ℂ := p 0
  let x : ℂ := p 1
  let y : ℂ := p 2
  let z : ℂ := p 3
  !![0,0,t+z,x-Complex.I*y; 0,0,x+Complex.I*y,t-z;
     t-z,-x+Complex.I*y,0,0; -x-Complex.I*y,t+z,0,0]

def four_component_factor : FourMomentum →ₗ[ℝ] FourByFour where
  toFun := four_component_pencil
  map_add' p q := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [four_component_pencil] <;> ring
  map_smul' c p := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [four_component_pencil, Algebra.smul_def] <;> ring

theorem theorem_four_components_are_sufficient : ansatz_reproduces_minkowski_square
    four_component_factor := by
  intro p
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [four_component_factor, four_component_pencil, Matrix.mul_apply, Fin.sum_univ_four,
      minkowski_pairing, Algebra.smul_def] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring
end
end MassShell

/-! ## The lower bound on representation dimension -/

namespace MassShell
noncomputable section
open Matrix
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

private theorem lemma_pass_two {R : Type*} [Ring R] {a b c : R}
    (ab : a*b = -(b*a)) (ac : a*c = -(c*a)) : a*(b*c) = (b*c)*a := by
  rw [← mul_assoc, ab, neg_mul, mul_assoc, ac, mul_neg, neg_neg, mul_assoc]

/-- The joint positive projector of two commuting involutions has one quarter
of the total trace. The three nonconstant terms vanish by Clifford symmetry. -/
theorem theorem_four_divides_representation_dimension
    (factor : FourMomentum →ₗ[ℝ] Module.End ℂ V)
    (square : ansatz_reproduces_minkowski_square factor) : 4 ∣ Module.finrank ℂ V := by
  let axis (i : Fin 4) : FourMomentum := Pi.single i 1
  let g (i : Fin 4) := factor (axis i)
  have swap (i j : Fin 4) (h : i ≠ j) : g i * g j = -(g j * g i) := by
    apply eq_neg_of_add_eq_zero_left
    have e := theorem_factorisation_forces_clifford_relation factor square (axis i) (axis j)
    have orth : minkowski_pairing (axis i) (axis j) = 0 := by
      fin_cases i <;> fin_cases j <;> simp_all [axis, minkowski_pairing]
    simpa [orth, g] using e
  have spatial (j : Fin 4) (h : j ≠ 0) : g j * g j = -1 := by
    change factor _ * factor _ = _
    rw [square]
    fin_cases j <;> norm_num [axis, minkowski_pairing, Pi.single_apply] at *
  let J := g 0
  let K := Complex.I • (g 1 * g 2)
  have jj : J * J = 1 := by
    change factor _ * factor _ = _
    rw [square]
    norm_num [axis, minkowski_pairing, Pi.single_apply]
  have kk : K*K = 1 := by
    dsimp only [K]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I,
      mul_assoc, ← mul_assoc (g 2), swap 2 1 (by decide), neg_mul, mul_assoc (g 1),
      spatial 2 (by decide)]
    simp [spatial 1 (by decide)]
  have jk : J*K = K*J := by
    dsimp only [K,J]
    rw [mul_smul_comm, smul_mul_assoc, lemma_pass_two (swap 0 1 (by decide)) (swap 0 2 (by decide))]
  have traceJ : LinearMap.trace ℂ V J = 0 := lemma_mass_shell_factor_is_traceless factor square _
  have traceK : LinearMap.trace ℂ V K = 0 := by
    have e := LinearMap.trace_mul_comm ℂ (g 1) (g 2)
    rw [swap 2 1 (by decide), map_neg] at e
    have z : LinearMap.trace ℂ V (g 1 * g 2) = 0 := by linear_combination e / 2
    simp [K, z]
  have traceJK : LinearMap.trace ℂ V (J*K) = 0 := by
    apply lemma_trace_zero_of_anticommuting_involution _ (Complex.I • g 3)
    · rw [smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, spatial 3 (by decide)]
      simp
    · have comm : g 3*K = K*g 3 := by
        dsimp only [K]
        rw [mul_smul_comm, smul_mul_assoc, lemma_pass_two (swap 3 1 (by decide)) (swap 3 2 (by decide))]
      have sign : g 3 * (J*K) = -((J*K)*g 3) := by
        rw [← mul_assoc, show g 3 * J = -(J * g 3) from swap 3 0 (by decide), neg_mul,
          mul_assoc, comm, mul_assoc]
      exact (smul_mul_assoc _ _ _).trans ((congrArg (Complex.I • ·) sign).trans
        (by rw [smul_neg, mul_smul_comm Complex.I (J*K) (g 3)]))
  let P := selected_projector J * selected_projector K
  have commute : Commute (selected_projector J) (selected_projector K) := by
    change _ * _ = _ * _
    simp only [selected_projector, smul_mul_assoc, mul_smul_comm, add_mul, mul_add,
      one_mul, mul_one, jk, smul_add]
    abel
  have idem : IsIdempotentElem P := by
    change (_ * _) * (_ * _) = _
    rw [mul_assoc, ← mul_assoc (selected_projector K), ← commute.eq,
      mul_assoc (selected_projector J) (selected_projector K),
      lemma_selected_projector_is_idempotent K kk, ← mul_assoc,
      lemma_selected_projector_is_idempotent J jj]
  have rank := ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr idem).trace
  have tr : 4 * LinearMap.trace ℂ V P = (Module.finrank ℂ V : ℂ) := by
    simp only [P, selected_projector, ← Complex.coe_smul, smul_mul_assoc, mul_smul_comm,
      add_mul, mul_add, one_mul, mul_one, map_smul, map_add, traceJ, traceK, traceJK,
      LinearMap.trace_one, smul_eq_mul]
    push_cast
    ring
  rw [rank] at tr
  exact ⟨_, by exact_mod_cast tr.symm⟩

/-- A nonzero finite-dimensional complex representation needs at least four components. -/
theorem theorem_four_components_are_necessary [Nontrivial V]
    (factor : FourMomentum →ₗ[ℝ] Module.End ℂ V)
    (square : ansatz_reproduces_minkowski_square factor) : 4 ≤ Module.finrank ℂ V :=
  Nat.le_of_dvd Module.finrank_pos (theorem_four_divides_representation_dimension factor square)

/-- Four is the least positive matrix size admitting a linear Minkowski factor. -/
theorem theorem_four_is_minimal : IsLeast
    {n : ℕ | 0 < n ∧ ∃ f : FourMomentum →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ,
      ansatz_reproduces_minkowski_square f} 4 := by
  refine ⟨⟨by decide, four_component_factor, theorem_four_components_are_sufficient⟩, ?_⟩
  rintro n ⟨positive, f, square⟩
  let action : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℝ] Module.End ℂ (Fin n → ℂ) :=
    Matrix.toLinAlgEquiv'.restrictScalars ℝ
  have represented : ansatz_reproduces_minkowski_square (action.toLinearMap.comp f) := by
    intro q
    change action (f q) * action (f q) = _
    rw [← map_mul, square, map_smul, map_one]
  have divides := theorem_four_divides_representation_dimension _ represented
  apply Nat.le_of_dvd positive
  simpa using divides

end
end MassShell

/-! ## The Moyal differential symbol -/

namespace MassShell.CompositionAndTransport
noncomputable section
open scoped ContDiff Matrix.Norms.Elementwise
def moyal_weight (n : ℕ) := (Complex.I/2)^n / (n.factorial : ℂ)
def moyal_polynomial (n : ℕ) : DifferentialSymbol :=
  MvPolynomial.C (moyal_weight n) * canonical_symbol^n

theorem lemma_moyal_symbol_value (n : ℕ) (u v : RealPhaseCovector) :
    symbol_value (moyal_polynomial n) u v = moyal_weight n * (omega u v : ℂ)^n := by
  simp [symbol_value, moyal_polynomial, ← lemma_canonical_symbol_value, symbol_value]

theorem theorem_moyal_covariance (n : ℕ) : ansatz_symplectic_covariance (moyal_polynomial n) := by
  intro T preserves u v
  simp [lemma_moyal_symbol_value, preserves]

theorem theorem_moyal_grading (n : ℕ) : ansatz_order_homogeneity n (moyal_polynomial n) := by
  intro r x y
  have scale := lemma_omega_linear_right x 0 y r
  simp [omega] at scale
  simp only [lemma_moyal_symbol_value]
  have h : omega x (r • y) = r * omega x y := by simpa [omega] using scale
  rw [h, Complex.ofReal_mul, mul_pow]
  ring

theorem lemma_moyal_polynomial_acts (n : ℕ) (F G : Symbol) :
    differential_operator F G (moyal_polynomial n) = moyal_coefficient n F G := by
  rw [moyal_polynomial, MvPolynomial.C_mul', map_smul]
  rfl

theorem theorem_moyal_classical_limit : ansatz_classical_product moyal_coefficient := by
  intro F G _ _
  simp [moyal_coefficient, poisson_power, lemma_operator_one]

theorem theorem_moyal_weyl_matching : ansatz_first_order_weyl_matching moyal_coefficient := by
  intro F G _ _
  simp [moyal_coefficient, smul_sub]

/-- At total order n the convolution of two exponential series is the nth
term of their exponential sum. The argument works in any commutative complex algebra. -/
theorem lemma_moyal_binomial {R : Type*} [CommRing R] [Algebra ℂ R] (n : ℕ) (x y : R) :
    (∑ k ∈ Finset.range (n+1), (moyal_weight k * moyal_weight (n-k)) •
      (x^k * y^(n-k))) = moyal_weight n • (x+y)^n := by
  rw [add_pow, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have le : k ≤ n := by simpa using hk
  have hw : moyal_weight k * moyal_weight (n-k) =
      moyal_weight n * (n.choose k : ℂ) := by
    simp only [moyal_weight, Nat.cast_choose ℂ le]
    rw [← mul_div_mul_comm, ← pow_add, Nat.add_sub_of_le le]
    have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hn]
  rw [hw, mul_smul]
  congr 1
  rw [Algebra.smul_def]
  push_cast
  ring

theorem theorem_moyal_associative_symbol (n : ℕ) (u v w : DifferentialSymbol) :
    (∑ k ∈ Finset.range (n+1), (moyal_weight k * moyal_weight (n-k)) •
      (u^k * (v+w)^(n-k))) =
    ∑ k ∈ Finset.range (n+1), (moyal_weight k * moyal_weight (n-k)) •
      (v^k * (u+w)^(n-k)) := by
  rw [lemma_moyal_binomial, lemma_moyal_binomial, add_left_comm u v w]
end
end MassShell.CompositionAndTransport

/-! ## Commuting derivatives on tensor factors -/

namespace MassShell.CompositionAndTransport
noncomputable section
open scoped ContDiff TensorProduct IsMulCommutative
open TensorProduct
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 2500000
abbrev S := SmoothMatrixSymbol
abbrev PairSpace := S ⊗[ℂ] S
abbrev TripleSpace := PairSpace ⊗[ℂ] S
def partial_map (i : Axis) : S →ₗ[ℂ] S where
  toFun F := ⟨directional i F, fun r s =>
    ((F.property r s).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const⟩
  map_add' F G := by
    apply Subtype.ext
    funext z r s
    change fderiv ℝ (fun x => F.val x r s + G.val x r s) z _ = _ + _
    rw [fderiv_fun_add ((F.property r s).differentiable (by simp) z)
      ((G.property r s).differentiable (by simp) z)]
    rfl
  map_smul' c F := by
    apply Subtype.ext
    funext z r s
    change fderiv ℝ (fun x => c • F.val x r s) z _ = c • _
    rw [fderiv_fun_const_smul ((F.property r s).differentiable (by simp) z)]
    rfl

theorem lemma_partials_commute (i j : Axis) : Commute (partial_map i) (partial_map j) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext z r s
  let f := fun y => F.val y r s
  have hf : ContDiff ℝ ∞ f := F.property r s
  have d := (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  change fderiv ℝ (fun y => fderiv ℝ f y (direction j)) z (direction i) =
    fderiv ℝ (fun y => fderiv ℝ f y (direction i)) z (direction j)
  simp only [fderiv_clm_apply d (differentiableAt_const _), fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero,
    zero_add, ContinuousLinearMap.flip_apply]
  exact hf.contDiffAt.isSymmSndFDerivAt (by simp) _ _

theorem lemma_partial_product (i : Axis) (F G : S) :
    partial_map i (F*G) = partial_map i F * G + F * partial_map i G := by
  apply Subtype.ext
  funext z r s
  change fderiv ℝ (fun y => ∑ k, F.val y r k * G.val y k s) z _ = _ + _
  have diff (k : Fin 4) : DifferentiableAt ℝ (fun y => F.val y r k * G.val y k s) z := ((F.property r k).differentiable (by simp) z).mul
    ((G.property k s).differentiable (by simp) z)
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun k y => F.val y r k * G.val y k s) (fun k _ => diff k)]
  simp only [sum_apply, fderiv_fun_mul
    ((F.property _ _).differentiable (by simp) z) ((G.property _ _).differentiable (by simp) z),
    add_apply, smul_apply, smul_eq_mul]
  change _ = (∑ k : Fin 4, directional i F z r k * G.val z k s) +
    ∑ k : Fin 4, F.val z r k * directional i G z k s
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  change _ = fderiv ℝ _ z _ * G.val z k s + F.val z r k * fderiv ℝ _ z _
  ring

/-- Polynomial calculus for a commuting family of complex linear endomorphisms. -/
def commuting_calculus {ι E : Type*} [AddCommMonoid E] [Module ℂ E]
    (D : ι → Module.End ℂ E) (comm : ∀ i j, Commute (D i) (D j)) :
    MvPolynomial ι ℂ →ₐ[ℂ] Module.End ℂ E :=
  let A := Algebra.adjoin ℂ (Set.range D)
  letI : IsMulCommutative A := Algebra.isMulCommutative_adjoin ℂ
    (by rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _; exact comm i j)
  A.val.comp (MvPolynomial.aeval (fun i => (⟨D i, Algebra.subset_adjoin ⟨i,rfl⟩⟩ : A)))

@[simp] theorem lemma_calculus_variable {ι E : Type*} [AddCommMonoid E] [Module ℂ E]
    (D : ι → Module.End ℂ E) (comm) (i : ι) :
    commuting_calculus D comm (MvPolynomial.X i) = D i := by
  simp [commuting_calculus]

def pair_partial : Variable → Module.End ℂ PairSpace
  | (.left,i) => TensorProduct.map (partial_map i) LinearMap.id
  | (.right,i) => TensorProduct.map LinearMap.id (partial_map i)

theorem lemma_pair_partials_commute (a b : Variable) :
    Commute (pair_partial a) (pair_partial b) := by
  obtain ⟨a,i⟩ := a
  obtain ⟨b,j⟩ := b
  apply TensorProduct.ext'
  intro F G
  have h (X : S) : partial_map i (partial_map j X) = partial_map j (partial_map i X) :=
    DFunLike.congr_fun (lemma_partials_commute i j).eq X
  cases a <;> cases b <;> simp [pair_partial, h]

def pair_calculus : DifferentialSymbol →ₐ[ℂ] Module.End ℂ PairSpace := commuting_calculus (ι := Variable) (E := PairSpace) pair_partial lemma_pair_partials_commute
def matrix_multiply : PairSpace →ₗ[ℂ] S := LinearMap.mul' ℂ S


abbrev TriplePolynomial := MvPolynomial (Fin 3 × Axis) ℂ
def triple_partial (v : Fin 3 × Axis) : Module.End ℂ TripleSpace :=
  ![TensorProduct.map (pair_partial (.left,v.2)) LinearMap.id,
    TensorProduct.map (pair_partial (.right,v.2)) LinearMap.id,
    TensorProduct.map LinearMap.id (partial_map v.2)] v.1

theorem lemma_triple_partials_commute (a b : Fin 3 × Axis) :
    Commute (triple_partial a) (triple_partial b) := by
  obtain ⟨a,i⟩ := a
  obtain ⟨b,j⟩ := b
  apply TensorProduct.ext_threefold
  intro F G H
  have h (X : S) : partial_map i (partial_map j X) = partial_map j (partial_map i X) :=
    DFunLike.congr_fun (lemma_partials_commute i j).eq X
  fin_cases a <;> fin_cases b <;> simp [triple_partial, pair_partial, h]

def triple_calculus : TriplePolynomial →ₐ[ℂ] Module.End ℂ TripleSpace :=
  commuting_calculus (ι := Fin 3 × Axis) (E := TripleSpace) triple_partial lemma_triple_partials_commute

/-- Multiplication of linear endomorphisms applies the right factor first. -/
private theorem lemma_apply_endomorphism_product {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (L M : Module.End ℂ V) (v : V) : (L * M) v = L (M v) := rfl

/-- Moving a polynomial in derivatives through a linear map requires checking
only the individual derivatives. This is used for insertion and for multiplication. -/
theorem lemma_polynomial_intertwining {ι E F : Type*} [AddCommMonoid E] [Module ℂ E]
    [AddCommMonoid F] [Module ℂ F]
    (a : MvPolynomial ι ℂ →ₐ[ℂ] Module.End ℂ E)
    (b : MvPolynomial ι ℂ →ₐ[ℂ] Module.End ℂ F) (L : E →ₗ[ℂ] F)
    (generator_law : ∀ i x, L (a (MvPolynomial.X i) x) = b (MvPolynomial.X i) (L x))
    (p : MvPolynomial ι ℂ) (x : E) : L (a p x) = b p (L x) := by
  induction p using MvPolynomial.induction_on generalizing x with
  | C c =>
    rw [MvPolynomial.C_eq_algebraMap, a.commutes, b.commutes]
    exact L.map_smul c x
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp only [map_mul, lemma_apply_endomorphism_product, hp, generator_law]

def inner_variables (side : Slot) : Variable → TriplePolynomial
  | (.left,i) => MvPolynomial.X ((match side with | .left => 0 | .right => 1), i)
  | (.right,i) => MvPolynomial.X ((match side with | .left => 1 | .right => 2), i)

def outer_variables (side : Slot) : Variable → TriplePolynomial
  | (.left,i) => match side with
    | .left => MvPolynomial.X (0,i) + MvPolynomial.X (1,i)
    | .right => MvPolynomial.X (0,i)
  | (.right,i) => match side with
    | .left => MvPolynomial.X (2,i)
    | .right => MvPolynomial.X (1,i) + MvPolynomial.X (2,i)

def insert_tensor (side : Slot) (extra : S) : PairSpace →ₗ[ℂ] TripleSpace :=
  match side with
  | .left => (TensorProduct.mk ℂ PairSpace S).flip extra
  | .right => (TensorProduct.assoc ℂ S S S).symm.toLinearMap.comp
      (TensorProduct.mk ℂ S PairSpace extra)

def merge_tensor : Slot → TripleSpace →ₗ[ℂ] PairSpace
  | .left => TensorProduct.map matrix_multiply LinearMap.id
  | .right => (TensorProduct.map LinearMap.id matrix_multiply).comp
      (TensorProduct.assoc ℂ S S S).toLinearMap

theorem lemma_insert_calculus (s : Slot) (extra : S) (p : DifferentialSymbol) (x : PairSpace) :
    insert_tensor s extra (pair_calculus p x) =
    triple_calculus (MvPolynomial.aeval (inner_variables s) p) (insert_tensor s extra x) := by
  apply lemma_polynomial_intertwining (E := PairSpace) (F := TripleSpace) pair_calculus
    (triple_calculus.comp (MvPolynomial.aeval (inner_variables s))) (insert_tensor s extra) _ p x
  rintro ⟨slot,i⟩ y
  change _ = triple_calculus (MvPolynomial.aeval _ (MvPolynomial.X _)) _
  rw [MvPolynomial.aeval_X]
  apply DFunLike.congr_fun (f := (insert_tensor s extra).comp (pair_calculus (MvPolynomial.X (slot,i))))
    (g := (triple_calculus (inner_variables s (slot,i))).comp (insert_tensor s extra)) ?_ y
  apply TensorProduct.ext'
  intro F G
  cases s <;> cases slot <;>
    simp [pair_calculus, triple_calculus, insert_tensor, inner_variables, pair_partial, triple_partial]

theorem lemma_merge_calculus (s : Slot) (p : DifferentialSymbol) (x : TripleSpace) :
    merge_tensor s (triple_calculus (MvPolynomial.aeval (outer_variables s) p) x) =
    pair_calculus p (merge_tensor s x) := by
  apply lemma_polynomial_intertwining (E := TripleSpace) (F := PairSpace)
    (triple_calculus.comp (MvPolynomial.aeval (outer_variables s))) pair_calculus (merge_tensor s) _ p x
  rintro ⟨slot,i⟩ y
  change merge_tensor s (triple_calculus (MvPolynomial.aeval _ (MvPolynomial.X _) ) y) = _
  rw [MvPolynomial.aeval_X]
  apply DFunLike.congr_fun (f := (merge_tensor s).comp (triple_calculus (outer_variables s (slot,i))))
    (g := (pair_calculus (MvPolynomial.X (slot,i))).comp (merge_tensor s)) _ y
  apply TensorProduct.ext_threefold
  intro F G H
  cases s <;> cases slot <;>
    simp [pair_calculus, triple_calculus, merge_tensor, outer_variables, matrix_multiply,
      pair_partial, triple_partial, lemma_partial_product, TensorProduct.add_tmul, TensorProduct.tmul_add]


def tensor_operator (p : DifferentialSymbol) : PairSpace →ₗ[ℂ] S :=
  matrix_multiply.comp (pair_calculus p)

theorem lemma_tensor_operator_value (p : DifferentialSymbol) (F G : S) :
    ((tensor_operator p (F ⊗ₜ[ℂ] G) : S) : Symbol) = differential_operator F G p := by
  classical
  let X : Variable → DifferentialSymbol := MvPolynomial.X
  have word (w : List Variable) (U V : S) :
      ((tensor_operator (w.map X).prod (U ⊗ₜ[ℂ] V) : S) : Symbol) =
        differentiated_product w U V := by
    induction w generalizing U V with
    | nil => simp [tensor_operator, matrix_multiply, differentiated_product]
    | cons j tail ih =>
      obtain ⟨slot,i⟩ := j
      simp only [List.map_cons, List.prod_cons]
      rw [mul_comm, tensor_operator, map_mul]
      cases slot <;> simpa [X, pair_calculus, pair_partial, tensor_operator, differentiated_product,
        lemma_apply_endomorphism_product] using
        (by first | exact ih (partial_map i U) V | exact ih U (partial_map i V) : _)
  have word_polynomial (d : Variable →₀ ℕ) :
      ((derivative_word d).map X).prod = d.prod (fun j k => X j ^ k) := by
    rw [d.prod_fintype _ (fun _ => pow_zero _)]
    have expand (xs : List Variable) :
        ((xs.flatMap fun j => List.replicate (d j) j).map X).prod =
        (xs.map fun j => X j ^ d j).prod := by
      induction xs with
      | nil => simp
      | cons i rest ih => simp [ih]
    exact (expand _).trans (Finset.prod_map_toList _ _)
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have mono := MvPolynomial.monomial_eq (s := d) (a := c) (R := ℂ)
    change MvPolynomial.monomial d c = MvPolynomial.C c * d.prod (fun j k => X j ^ k) at mono
    rw [← word_polynomial, MvPolynomial.C_mul'] at mono
    conv_lhs => rw [mono]
    change (↑(matrix_multiply (pair_calculus _ _)) : Symbol) =
      Finsupp.linearCombination ℂ _ (Finsupp.single d c)
    rw [map_smul, Finsupp.linearCombination_single]
    change (↑(matrix_multiply (c • (pair_calculus _ (F ⊗ₜ[ℂ] G)))) : Symbol) = _
    rw [map_smul]
    exact congrArg (c • ·) (word (derivative_word d) F G)
  | add p q hp hq =>
    simp only [tensor_operator, map_add, LinearMap.comp_apply] at *
    change (↑(matrix_multiply (pair_calculus p _ + pair_calculus q _)) : Symbol) = _
    rw [map_add, Subalgebra.coe_add, hp,hq]

end
end MassShell.CompositionAndTransport

/-! ## Existence and uniqueness on smooth ensembles -/

namespace MassShell.CompositionAndTransport
noncomputable section
open scoped TensorProduct
open TensorProduct
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 2500000

def moyal_family : CoefficientFamily := fun n => TensorProduct.curry (tensor_operator (moyal_polynomial n))

theorem lemma_family_agrees (n : ℕ) (F G : S) :
    (moyal_family n F G : Symbol) = moyal_coefficient n F G :=
  (lemma_tensor_operator_value _ _ _).trans (lemma_moyal_polynomial_acts ..)

def triple_contraction (a b : Fin 3) : TriplePolynomial :=
  ∑ μ : Fin 4, (MvPolynomial.X (a,Sum.inr μ) * MvPolynomial.X (b,Sum.inl μ) -
    MvPolynomial.X (a,Sum.inl μ) * MvPolynomial.X (b,Sum.inr μ))

def nested_polynomial (s : Slot) (k l : ℕ) : TriplePolynomial :=
  MvPolynomial.aeval (outer_variables s) (moyal_polynomial l) *
  MvPolynomial.aeval (inner_variables s) (moyal_polynomial k)

theorem lemma_nested_polynomial_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), nested_polynomial .left k (n-k)) =
    ∑ k ∈ Finset.range (n+1), nested_polynomial .right k (n-k) := by
  let u := triple_contraction 0 1
  let v := triple_contraction 1 2
  let w := triple_contraction 0 2
  have left_outer : MvPolynomial.aeval (outer_variables .left) canonical_symbol = v+w := by
    simp only [canonical_symbol, contraction, outer_variables, map_sum, map_sub, map_mul,
      MvPolynomial.aeval_X, v,w,triple_contraction, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intros
    ring
  have right_outer : MvPolynomial.aeval (outer_variables .right) canonical_symbol = u+w := by
    simp only [canonical_symbol, contraction, outer_variables, map_sum, map_sub, map_mul,
      MvPolynomial.aeval_X, u,w,triple_contraction, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intros
    ring
  have innerL : MvPolynomial.aeval (inner_variables .left) canonical_symbol = u := by
    simp [canonical_symbol, contraction, u,triple_contraction,inner_variables]
  have innerR : MvPolynomial.aeval (inner_variables .right) canonical_symbol = v := by
    simp [canonical_symbol, contraction, v,triple_contraction,inner_variables]
  have coeff (s : Slot) (k l : ℕ) : nested_polynomial s k l =
      (moyal_weight k * moyal_weight l) •
      ((MvPolynomial.aeval (inner_variables s) canonical_symbol)^k *
       (MvPolynomial.aeval (outer_variables s) canonical_symbol)^l) := by
    simp [nested_polynomial, moyal_polynomial, Algebra.smul_def, mul_comm, mul_left_comm]
    ring
  simp only [coeff, innerL,innerR,left_outer,right_outer,lemma_moyal_binomial, add_left_comm u v w]

def triple_multiply := matrix_multiply.comp (merge_tensor .left)

theorem lemma_triple_multiply (s : Slot) : matrix_multiply.comp (merge_tensor s) =
    triple_multiply := by
  cases s with
  | left => rfl
  | right =>
    apply TensorProduct.ext_threefold
    intro F G H
    simp [triple_multiply, merge_tensor, matrix_multiply, mul_assoc]

theorem lemma_nested_tensor (s : Slot) (p q : DifferentialSymbol) (extra : S) (t : PairSpace) :
    tensor_operator q (merge_tensor s (insert_tensor s extra (pair_calculus p t))) =
    triple_multiply (triple_calculus
      (MvPolynomial.aeval (outer_variables s) q * MvPolynomial.aeval (inner_variables s) p)
      (insert_tensor s extra t)) := by
  rw [lemma_insert_calculus, tensor_operator, LinearMap.comp_apply, ← lemma_merge_calculus,
    map_mul, lemma_apply_endomorphism_product, ← lemma_triple_multiply s]
  rfl

theorem theorem_moyal_smooth_associativity : ansatz_matrix_associativity moyal_family := by
  intro n F G H
  let t := (F ⊗ₜ[ℂ] G) ⊗ₜ[ℂ] H
  let evaluate : TriplePolynomial →ₗ[ℂ] S :=
    triple_multiply.comp ((LinearMap.applyₗ (R := ℂ) t).comp triple_calculus.toLinearMap)
  have left (k l : ℕ) : moyal_family l (moyal_family k F G) H =
      evaluate (nested_polynomial .left k l) := by
    simpa [moyal_family, tensor_operator, merge_tensor, insert_tensor, evaluate, nested_polynomial,
      t, matrix_multiply] using
      lemma_nested_tensor .left (moyal_polynomial k) (moyal_polynomial l) H (F ⊗ₜ[ℂ] G)
  have right (k l : ℕ) : moyal_family l F (moyal_family k G H) =
      evaluate (nested_polynomial .right k l) := by
    simpa [moyal_family, tensor_operator, merge_tensor, insert_tensor, evaluate, nested_polynomial,
      t, matrix_multiply] using
      lemma_nested_tensor .right (moyal_polynomial k) (moyal_polynomial l) F (G ⊗ₜ[ℂ] H)
  simp only [left,right, ← map_sum, lemma_nested_polynomial_sum]

def constant_insert (s : Slot) (A : SpinMatrix) : S →ₗ[ℂ] PairSpace :=
  match s with
  | .left => TensorProduct.mk ℂ S S (constant_matrix A)
  | .right => (TensorProduct.mk ℂ S S).flip (constant_matrix A)

def surviving_variable (s : Slot) : Variable → MvPolynomial Axis ℂ
  | (j,i) => if j = s then 0 else MvPolynomial.X i

theorem lemma_constant_positive_order (s : Slot) (A : SpinMatrix) (F : S) (n : ℕ) :
    tensor_operator (moyal_polynomial (n+1)) (constant_insert s A F) = 0 := by
  let calcD := commuting_calculus (E := S) partial_map lemma_partials_commute
  have dconst (i : Axis) : partial_map i (constant_matrix A) = 0 := by
    apply Subtype.ext
    funext z r j
    simp [partial_map, directional, constant_matrix]
  have move := lemma_polynomial_intertwining
    (calcD.comp (MvPolynomial.aeval (surviving_variable s))) pair_calculus (constant_insert s A)
    (by rintro ⟨j,i⟩ U; cases s <;> cases j <;>
          simp [calcD, surviving_variable, pair_calculus, pair_partial, constant_insert, dconst])
    (moyal_polynomial (n+1)) F
  have zero_pair : MvPolynomial.aeval (surviving_variable s) canonical_symbol = 0 := by
    cases s <;> simp [canonical_symbol, contraction, surviving_variable]
  have vanished : MvPolynomial.aeval (surviving_variable s) (moyal_polynomial (n+1)) = 0 := by
    rw [moyal_polynomial, map_mul, map_pow, zero_pair, zero_pow (by omega), mul_zero]
  change constant_insert s A (calcD (MvPolynomial.aeval _ _) F) = _ at move
  rw [vanished, map_zero] at move
  change constant_insert s A 0 = _ at move
  rw [map_zero] at move
  change matrix_multiply (pair_calculus _ _) = 0
  rw [← move, map_zero]

theorem theorem_moyal_neutrality : ansatz_constant_matrix_neutrality moyal_family := by
  intro n A F
  cases n with
  | zero =>
    constructor <;> apply Subtype.ext <;>
      simp [lemma_family_agrees, moyal_coefficient, poisson_power, lemma_operator_one]
  | succ n =>
    simpa [moyal_family, constant_insert] using
      And.intro (lemma_constant_positive_order .left A F n)
        (lemma_constant_positive_order .right A F n)

/-- Existence with all the product assumptions used in the selection theorem. -/
theorem theorem_moyal_admissible :
    ansatz_scalar_locality moyal_family moyal_polynomial ∧
    (∀ n, ansatz_symplectic_covariance (moyal_polynomial n)) ∧
    (∀ n, ansatz_order_homogeneity n (moyal_polynomial n)) ∧
    ansatz_matrix_associativity moyal_family ∧ ansatz_constant_matrix_neutrality moyal_family ∧
    (∀ F G, moyal_family 0 F G = F * G) ∧
    (∀ F G, (moyal_family 1 F G : Symbol) - (moyal_family 1 G F : Symbol) =
      Complex.I • weyl_transport F G) := by
  refine ⟨?_, theorem_moyal_covariance, theorem_moyal_grading,
    theorem_moyal_smooth_associativity, theorem_moyal_neutrality, ?_, ?_⟩
  · intro n F G i k j z
    exact congrArg (fun f : Symbol => f z 0 0)
      (lemma_tensor_operator_value (moyal_polynomial n) (smooth_corner F i k) (smooth_corner G k j))
  · intro F G
    apply Subtype.ext
    rw [lemma_family_agrees, theorem_moyal_classical_limit F G F.property G.property]
    rfl
  · intro F G
    rw [lemma_family_agrees, lemma_family_agrees, lemma_first_moyal_commutator]

def admissible_smooth_composition (C : CoefficientFamily) : Prop :=
  ∃ p : ℕ → DifferentialSymbol, ansatz_scalar_locality C p ∧
    (∀ n, ansatz_symplectic_covariance (p n)) ∧ (∀ n, ansatz_order_homogeneity n (p n)) ∧
    ansatz_matrix_associativity C ∧ ansatz_constant_matrix_neutrality C ∧
    (∀ F G, C 0 F G = F * G) ∧
    (∀ F G, (C 1 F G : Symbol) - (C 1 G F : Symbol) = Complex.I • weyl_transport F G)

/-- Existence and uniqueness refer to the very same admissibility conditions. -/
theorem theorem_exists_unique_smooth_composition : ∃! C, admissible_smooth_composition C := by
  refine ⟨moyal_family, ⟨moyal_polynomial, theorem_moyal_admissible⟩, ?_⟩
  rintro C ⟨p, locality, covariance, grading, associativity, neutrality, classical_limit, matching⟩
  have selected := theorem_smooth_composition_is_moyal C p locality covariance grading
    associativity neutrality classical_limit matching
  funext n
  apply LinearMap.ext
  intro F
  apply LinearMap.ext
  intro G
  exact Subtype.ext ((selected n F G).trans (lemma_family_agrees n F G).symm)

/-- Apply the mass-shell argument with the constructed product. The state still
has to satisfy its leading-sector, preservation and continuation conditions. -/
theorem corollary_transport_for_the_constructed_product
    (factor : FourMomentum →ₗ[ℝ] SpinMatrix)
    (ansatz_square_identity : ansatz_reproduces_minkowski_square factor)
    (κ : PhasePoint → FourMomentum) (b : ℝ) (mass_positive : 0 < b)
    (z : PhasePoint) (on_shell : minkowski_pairing (κ z) (κ z) = b ^ 2)
    (Hₛ : SmoothMatrixSymbol) (ansatz_generator : ∀ y, (Hₛ : Symbol) y = factor (κ y) - b • 1)
    (Wₛ : ℕ → SmoothMatrixSymbol) (density : SpinMatrix) :
    let W := fun n => (Wₛ n : Symbol)
    let J := b⁻¹ • factor (κ z)
    let P := selected_projector J
    let H : Symbol := Hₛ
    let B := (Complex.I • weyl_transport H (W 0)) z
    ansatz_selected_leading_density (W 0 z) P density →
    ansatz_all_order_preservation moyal_family Hₛ Wₛ →
    ansatz_continues_left_zero_sector moyal_family Hₛ Wₛ →
      Module.finrank ℂ (LinearMap.range (Matrix.toLinAlgEquiv' P)) = 2 ∧
      (H z * W 0 z = 0 ∧ W 0 z * H z = 0) ∧
      (∀ n (F G : SmoothMatrixSymbol), (moyal_family n F G : Symbol) = moyal_coefficient n F G) ∧
      (J * B * J = -B ∧ b • (W 1 z - J * W 1 z * J) = -(J * B)) ∧
      (∀ n, (∑ r ∈ Finset.range (n+1), moyal_coefficient r H (W (n-r))) = 0 ∧
        (∑ r ∈ Finset.range (n+1), moyal_coefficient r (W (n-r)) H) = 0) := by
  obtain ⟨locality, covariance, grading, assoc, neutral, limit, matching⟩ := theorem_moyal_admissible
  exact theorem_from_mass_shell_to_transport_and_spectral_equations factor ansatz_square_identity
    κ b mass_positive z on_shell Hₛ ansatz_generator Wₛ density moyal_family moyal_polynomial
    locality covariance grading assoc neutral limit matching

end
end MassShell.CompositionAndTransport

/-! ## Distribution-valued ensembles -/

namespace MassShell.CompositionAndTransport
noncomputable section
open scoped Distributions ContDiff
abbrev PhaseTests := TestFunction (⊤ : TopologicalSpace.Opens PhasePoint) ℂ ⊤
/-- Complex-linear distributions on compactly supported smooth complex test functions. -/
abbrev ScalarDistribution := PhaseTests →L[ℂ] ℂ
abbrev EnsembleDistribution := Matrix (Fin 4) (Fin 4) ScalarDistribution

def smooth_directional (i : Axis) (F : SmoothMatrixSymbol) : SmoothMatrixSymbol :=
  ⟨directional i F, fun r s => (F.property r s).fderiv_right
    (m := ∞) (by simp) |>.clm_apply contDiff_const⟩

/-- Weak derivatives and smooth multipliers are transposes of continuous maps on tests. -/
@[expose] def weak_derivative (i : Axis) (T : ScalarDistribution) : ScalarDistribution :=
  - T.comp (TestFunction.lineDerivCLM ℂ (direction i))

def smooth_times_distribution {f : PhasePoint → ℂ} (hf : ContDiff ℝ ∞ f)
    (T : ScalarDistribution) : ScalarDistribution :=
  T.comp (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) hf)

theorem lemma_weak_derivative_on_test (i : Axis) (T : ScalarDistribution) (φ : PhaseTests) :
    weak_derivative i T φ = -T (TestFunction.lineDerivCLM ℂ (direction i) φ) := rfl

def distribution_directional (i : Axis) (W : EnsembleDistribution) : EnsembleDistribution :=
  Matrix.of fun r s => weak_derivative i (W r s)

inductive ProductSide | generator_left | generator_right

/-- At the end of a derivative word the smooth entry multiplies a distribution.
The intermediate index retains the order of the two spin matrices. -/
def mixed_multiplication (side : ProductSide) (F : SmoothMatrixSymbol)
    (W : EnsembleDistribution) : EnsembleDistribution := Matrix.of fun r s =>
  match side with
  | .generator_left => ∑ k, smooth_times_distribution (F.property r k) (W k s)
  | .generator_right => ∑ k, smooth_times_distribution (F.property k s) (W r k)

def mixed_word (side : ProductSide) :
    List Variable → SmoothMatrixSymbol → EnsembleDistribution → EnsembleDistribution
  | [], F, W => mixed_multiplication side F W
  | (slot,i) :: rest, F, W =>
    match side, slot with
    | .generator_left, .left | .generator_right, .right =>
      mixed_word side rest (smooth_directional i F) W
    | .generator_left, .right | .generator_right, .left =>
      mixed_word side rest F (distribution_directional i W)

/-- Each order is a finite sum of derivatives and smooth multipliers on the full dual. -/
def distribution_moyal_coefficient (side : ProductSide) (n : ℕ) (F : SmoothMatrixSymbol)
    (W : EnsembleDistribution) : EnsembleDistribution :=
  ((Complex.I / 2)^n / (n.factorial : ℂ)) •
    (canonical_symbol ^ n).coeff.sum (fun d c => c • mixed_word side (derivative_word d) F W)

def distribution_product_order (side : ProductSide) (n : ℕ) (H : SmoothMatrixSymbol)
    (W : ℕ → EnsembleDistribution) : EnsembleDistribution :=
  ∑ k ∈ Finset.range (n+1), distribution_moyal_coefficient side k H (W (n-k))

/-- Equality is in the continuous dual, hence these are weak spectral equations. -/
theorem corollary_weak_right_spectral_equation (H : SmoothMatrixSymbol)
    (W : ℕ → EnsembleDistribution)
    (ansatz_preservation : ∀ n, distribution_product_order .generator_left n H W -
      distribution_product_order .generator_right n H W = 0)
    (ansatz_left_sector : ∀ n, distribution_product_order .generator_left n H W = 0) :
    ∀ n, distribution_product_order .generator_right n H W = 0 := by
  intro n
  exact (sub_eq_zero.mp (ansatz_preservation n)).symm.trans (ansatz_left_sector n)

open MeasureTheory

abbrev phase_measure := ((Pi.basisFun ℝ (Fin 4)).prod (Pi.basisFun ℝ (Fin 4))).addHaar

def regular_distribution (f : PhasePoint → ℂ) : ScalarDistribution :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℂ ℂ) phase_measure f

theorem lemma_regular_evaluation {f : PhasePoint → ℂ} (hf : Continuous f) (φ : PhaseTests) :
    regular_distribution f φ = ∫ x, φ x * f x ∂phase_measure := by
  apply TestFunction.integralAgainstBilinCLM_eq_integral
  exact hf.continuousOn.locallyIntegrableOn (by simp)

theorem lemma_multiplier_on_regular {f g : PhasePoint → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : Continuous g) : smooth_times_distribution hf (regular_distribution g) =
      regular_distribution (f*g) := by
  ext φ
  change regular_distribution g _ = _
  rw [lemma_regular_evaluation hg, lemma_regular_evaluation (hf.continuous.mul hg)]
  apply integral_congr_ae
  filter_upwards with x
  change (φ x * f x) * g x = φ x * (f x * g x)
  exact mul_assoc ..

theorem lemma_weak_derivative_on_regular {f : PhasePoint → ℂ} (hf : ContDiff ℝ ∞ f) (i : Axis) :
    weak_derivative i (regular_distribution f) =
    regular_distribution (fun x => fderiv ℝ f x (direction i)) := by
  ext φ
  let v := direction i
  have df : Continuous (fun x => fderiv ℝ f x v) :=
    ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have dφ : Continuous (fun x => fderiv ℝ φ x v) :=
    ((φ.contDiff.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have parts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := phase_measure)
    (f := (φ : PhasePoint → ℂ)) (g := f) (v := v)
    ((dφ.mul hf.continuous).integrable_of_hasCompactSupport
      ((φ.hasCompactSupport.fderiv_apply ℝ v).mul_right))
    ((φ.contDiff.continuous.mul df).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right)
    ((φ.contDiff.continuous.mul hf.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_right)
    (fun x _ => φ.contDiff.differentiable (by simp) x)
    (fun x _ => hf.differentiable (by simp) x)
  rw [lemma_weak_derivative_on_test, lemma_regular_evaluation hf.continuous,
    lemma_regular_evaluation df]
  exact parts.symm


/-- Integration against a continuous density is linear in that density. -/
def integrate_density : C(PhasePoint, ℂ) →ₗ[ℂ] ScalarDistribution where
  toFun f := regular_distribution f
  map_add' f g := by
    ext φ
    change regular_distribution _ φ = regular_distribution f φ + regular_distribution g φ
    rw [lemma_regular_evaluation (f+g).continuous, lemma_regular_evaluation f.continuous,
      lemma_regular_evaluation g.continuous]
    simp only [ContinuousMap.add_apply, mul_add]
    apply integral_add
    · exact (φ.contDiff.continuous.mul f.continuous).integrable_of_hasCompactSupport
        φ.hasCompactSupport.mul_right
    · exact (φ.contDiff.continuous.mul g.continuous).integrable_of_hasCompactSupport
        φ.hasCompactSupport.mul_right
  map_smul' c f := by
    ext φ
    change regular_distribution _ φ = c * regular_distribution f φ
    rw [lemma_regular_evaluation (c • f).continuous, lemma_regular_evaluation f.continuous,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp [mul_left_comm]

def entry (F : SmoothMatrixSymbol) (r s : Fin 4) : C(PhasePoint, ℂ) :=
  ⟨fun z => F.val z r s, (F.property r s).continuous⟩

def regular_ensemble : SmoothMatrixSymbol →ₗ[ℂ] EnsembleDistribution where
  toFun F := Matrix.of fun r s => integrate_density (entry F r s)
  map_add' F G := by ext r s : 1; exact integrate_density.map_add (entry F r s) (entry G r s)
  map_smul' c F := by ext r s : 1; exact integrate_density.map_smul c (entry F r s)

theorem lemma_distribution_derivative_extends_smooth (i : Axis) (W : SmoothMatrixSymbol) :
    distribution_directional i (regular_ensemble W) = regular_ensemble (smooth_directional i W) := by
  apply Matrix.ext
  intro r s
  exact lemma_weak_derivative_on_regular (W.property r s) i

theorem lemma_mixed_multiplication_extends (side : ProductSide) (F W : SmoothMatrixSymbol) :
    mixed_multiplication side F (regular_ensemble W) = regular_ensemble
      (match side with | .generator_left => F*W | .generator_right => W*F) := by
  apply Matrix.ext
  intro r s
  have term (i j a b : Fin 4) : smooth_times_distribution (F.property i j)
      (regular_ensemble W a b) = integrate_density (entry F i j * entry W a b) :=
    lemma_multiplier_on_regular _ (W.property a b).continuous
  have prod_entry (U V : SmoothMatrixSymbol) :
      entry (U*V) r s = ∑ k, entry U r k * entry V k s := by
    ext x
    simp [entry, Matrix.mul_apply]
  cases side with
  | generator_left =>
    change (∑ k, smooth_times_distribution (F.property r k) (regular_ensemble W k s)) = integrate_density (entry (F*W) r s)
    rw [prod_entry, map_sum]
    exact Finset.sum_congr rfl (fun k _ => term r k k s)
  | generator_right =>
    change (∑ k, smooth_times_distribution (F.property k s) (regular_ensemble W r k)) = integrate_density (entry (W*F) r s)
    rw [prod_entry, map_sum]
    exact Finset.sum_congr rfl (fun k _ => (term k s r k).trans (by rw [mul_comm]))


def smooth_word : List Variable → SmoothMatrixSymbol → SmoothMatrixSymbol → SmoothMatrixSymbol
  | [], F, G => F*G
  | (.left,i)::tail, F, G => smooth_word tail (smooth_directional i F) G
  | (.right,i)::tail, F, G => smooth_word tail F (smooth_directional i G)

theorem lemma_smooth_word_value (word : List Variable) (F G : SmoothMatrixSymbol) :
    (smooth_word word F G : Symbol) = differentiated_product word F G := by
  induction word generalizing F G with
  | nil => rfl
  | cons j tail ih => obtain ⟨s,i⟩ := j; cases s <;> apply ih

theorem lemma_mixed_word_extends (word : List Variable) (side : ProductSide)
    (F W : SmoothMatrixSymbol) : mixed_word side word F (regular_ensemble W) =
    regular_ensemble (match side with
      | .generator_left => smooth_word word F W | .generator_right => smooth_word word W F) := by
  induction word generalizing F W with
  | nil => exact lemma_mixed_multiplication_extends side F W
  | cons j tail ih =>
    obtain ⟨s,i⟩ := j
    cases side <;> cases s <;> simp only [mixed_word, smooth_word,
      lemma_distribution_derivative_extends_smooth] <;> apply ih

def smooth_moyal_value (n : ℕ) (F G : SmoothMatrixSymbol) : SmoothMatrixSymbol :=
  ((Complex.I/2)^n / (n.factorial : ℂ)) • (canonical_symbol ^ n).coeff.sum
    (fun d c => c • smooth_word (derivative_word d) F G)

theorem lemma_smooth_moyal_value (n : ℕ) (F G : SmoothMatrixSymbol) :
    (smooth_moyal_value n F G : Symbol) = moyal_coefficient n F G := by
  unfold smooth_moyal_value moyal_coefficient poisson_power differential_operator
  simp only [Finsupp.sum, Subalgebra.coe_smul, lemma_smooth_sum, lemma_smooth_word_value,
    LinearMap.comp_apply, Finsupp.linearCombination_apply]
  rfl

/-- Both distribution actions agree exactly with the selected smooth coefficients
on every regular smooth ensemble, including the matrix order on the right. -/
theorem theorem_distribution_moyal_extends_smooth (n : ℕ) (side : ProductSide)
    (H W : SmoothMatrixSymbol) :
    distribution_moyal_coefficient side n H (regular_ensemble W) =
    regular_ensemble (match side with
      | .generator_left => smooth_moyal_value n H W
      | .generator_right => smooth_moyal_value n W H) := by
  cases side <;> simp [distribution_moyal_coefficient, smooth_moyal_value, Finsupp.sum,
    lemma_mixed_word_extends, map_sum]


/-- A point-supported matrix distribution can carry a spin density at a shell point. -/
def point_ensemble (z : PhasePoint) (ρ : SpinMatrix) : EnsembleDistribution :=
  Matrix.of fun r s => ρ r s • (show ScalarDistribution from
    { toFun := fun φ => φ z
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := continuous_eval_const _ })

theorem lemma_mixed_point_mass (side : ProductSide) (F : SmoothMatrixSymbol)
    (z : PhasePoint) (ρ : SpinMatrix) :
    mixed_multiplication side F (point_ensemble z ρ) =
    point_ensemble z (match side with
      | .generator_left => F.val z * ρ | .generator_right => ρ * F.val z) := by
  ext r s φ
  cases side <;>
    simp [mixed_multiplication, smooth_times_distribution, point_ensemble,
      Matrix.mul_apply, Finset.sum_mul] <;>
    apply Finset.sum_congr rfl <;> intro k _ <;> ring

/-- A leading density satisfying both algebraic shell equations yields both weak
zeroth-order equations even when concentrated at one phase point. -/
theorem corollary_point_ensemble_on_shell (H : SmoothMatrixSymbol) (z : PhasePoint) (ρ : SpinMatrix)
    (left_constraint : H.val z * ρ = 0) (right_constraint : ρ * H.val z = 0) :
    distribution_moyal_coefficient .generator_left 0 H (point_ensemble z ρ) = 0 ∧
    distribution_moyal_coefficient .generator_right 0 H (point_ensemble z ρ) = 0 := by
  have order_zero (side : ProductSide) (W : EnsembleDistribution) :
      distribution_moyal_coefficient side 0 H W = mixed_multiplication side H W := by
    unfold distribution_moyal_coefficient
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_smul]
    change (Finsupp.single 0 (1 : ℂ)).sum _ = _
    have empty_flat (xs : List Variable) : xs.flatMap (fun _ => ([] : List Variable)) = [] := by
      induction xs <;> simp_all
    rw [Finsupp.sum_single_index]
    · simp [derivative_word, empty_flat, mixed_word]
    · exact zero_smul ℂ (mixed_word side (derivative_word 0) H W)
  constructor <;> rw [order_zero, lemma_mixed_point_mass] <;>
    simp only [left_constraint, right_constraint] <;> ext r s φ <;> simp [point_ensemble]

/-- On a regular ensemble the weak actions recover the unique admissible product. -/
theorem corollary_distribution_action_of_selected_product (side : ProductSide) (n : ℕ)
    (H W : SmoothMatrixSymbol) :
    distribution_moyal_coefficient side n H (regular_ensemble W) =
      regular_ensemble (match side with
        | .generator_left => moyal_family n H W
        | .generator_right => moyal_family n W H) := by
  have same (F G : SmoothMatrixSymbol) : smooth_moyal_value n F G = moyal_family n F G :=
    Subtype.ext ((lemma_smooth_moyal_value n F G).trans (lemma_family_agrees n F G).symm)
  rw [theorem_distribution_moyal_extends_smooth]
  cases side <;> simp only [same]

/-- Concentrating a projected leading density at a massive shell point preserves
both classical shell equations as equalities of distributions. -/
theorem corollary_projected_point_mass_on_shell (factor : FourMomentum →ₗ[ℝ] SpinMatrix)
    (ansatz_square : ansatz_reproduces_minkowski_square factor) (p : FourMomentum) (b : ℝ)
    (mass_positive : 0 < b) (on_shell : minkowski_pairing p p = b^2)
    (H : SmoothMatrixSymbol) (z : PhasePoint) (density : SpinMatrix)
    (ansatz_generator : H.val z = factor p - b • 1) :
    let P := selected_projector (b⁻¹ • factor p)
    let W := point_ensemble z (P * density * P)
    distribution_moyal_coefficient .generator_left 0 H W = 0 ∧
      distribution_moyal_coefficient .generator_right 0 H W = 0 := by
  let J := b⁻¹ • factor p
  have square : J*J = 1 := lemma_on_shell_normalisation factor ansatz_square p b mass_positive.ne' on_shell
  have constraints := theorem_projected_distribution_satisfies_both_constraints J density square
  have generator : H.val z = b • (J - 1) := by
    rw [ansatz_generator, smul_sub, smul_smul, mul_inv_cancel₀ mass_positive.ne', one_smul]
  apply corollary_point_ensemble_on_shell
  · rw [generator, smul_mul_assoc, constraints.1, smul_zero]
  · rw [generator, mul_smul_comm, constraints.2, smul_zero]

end
end MassShell.CompositionAndTransport

namespace MassShell.CompositionAndTransport
noncomputable section
open scoped ContDiff ComplexConjugate TensorProduct
open TensorProduct
def hermitian_field (F : S) : S :=
  ⟨fun z => (F.val z).conjTranspose, fun i j =>
    Complex.conjCLE.contDiff.comp (F.property j i)⟩

def dirac_adjoint (metric : SpinMatrix) (F : S) : S :=
  constant_matrix metric * hermitian_field F * constant_matrix metric

/-- Adjoint compatibility for a real formal parameter, applied at each order. -/
def ansatz_dirac_adjoint_compatibility (metric : SpinMatrix) (C : CoefficientFamily) : Prop :=
  ∀ n F G, dirac_adjoint metric (C n F G) = C n (dirac_adjoint metric G) (dirac_adjoint metric F)

def coordinate_exponential_field (i : Axis) : S :=
  ⟨exponential_field (coordinate_covector i) 1, lemma_exponential_field_is_smooth _ _⟩

theorem lemma_coordinate_exponential_field_self_adjoint (metric : SpinMatrix) (square : metric*metric=1)
    (i : Axis) : dirac_adjoint metric (coordinate_exponential_field i) = coordinate_exponential_field i := by
  apply Subtype.ext
  funext z
  change metric * (Complex.exp (coordinate_covector i z) • (1 : SpinMatrix)).conjTranspose * metric = _
  have coordinate_value_is_real : conj (coordinate_covector i z) = coordinate_covector i z := by
    cases i <;> simp [coordinate_covector]
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  change metric * (conj (Complex.exp _) • 1) * metric = _
  rw [← Complex.exp_conj, coordinate_value_is_real, mul_smul_comm, mul_one, smul_mul_assoc, square]
  rfl

def oriented_response (C : CoefficientFamily) (n : ℕ) : ℂ :=
  (C n (coordinate_exponential_field (.inr 0)) (coordinate_exponential_field (.inl 0))).val 0 0 0

/-- The signed real scale is chosen after reality has fixed the phase. Eq. (72)
gives twice this imaginary component for the oriented first-order commutator. -/
def ansatz_oriented_weyl_scale (C : CoefficientFamily) : Prop := (oriented_response C 1).im = 1/2

theorem lemma_canonical_test_response (C : CoefficientFamily) (a : ℕ → ℂ)
    (reduction : ∀ n (F G : S), (C n F G : Symbol) = a n • poisson_power n F G)
    (n : ℕ) : oriented_response C n = a n := by
  unfold oriented_response
  rw [reduction]
  change (a n • poisson_power n (exponential_field _ 1) (exponential_field _ 1)) 0 0 0 = _
  rw [lemma_poisson_power_on_exponential_fields]
  simp [lemma_pairing_formula, Fin.sum_univ_four, coordinate_covector, direction, Pi.single_apply, exponential_field]

theorem theorem_adjoint_forces_coefficient_phase (C : CoefficientFamily) (a : ℕ → ℂ)
    (reduction : ∀ n (F G : S), (C n F G : Symbol) = a n • poisson_power n F G)
    (metric : SpinMatrix) (square : metric*metric=1)
    (adjoint : ansatz_dirac_adjoint_compatibility metric C) (n : ℕ) :
    conj (a n) = (-1 : ℂ)^n * a n := by
  let p := coordinate_exponential_field (.inr 0)
  let x := coordinate_exponential_field (.inl 0)
  have unit_pair : pairing (coordinate_covector (.inr 0)) (coordinate_covector (.inl 0)) = 1 := by
    simp [lemma_pairing_formula, Fin.sum_univ_four, coordinate_covector, direction, Pi.single_apply]
  have forward : (C n p x).val 0 = a n • (1 : SpinMatrix) := by
    rw [reduction]
    change (a n • poisson_power n (exponential_field _ 1) (exponential_field _ 1)) 0 = _
    simp [lemma_poisson_power_on_exponential_fields, unit_pair, exponential_field]
  have backward : (C n x p).val 0 = ((-1 : ℂ)^n * a n) • (1 : SpinMatrix) := by
    rw [reduction]
    change (a n • poisson_power n (exponential_field _ 1) (exponential_field _ 1)) 0 = _
    have neg_pair := (lemma_pairing_skew _ _).trans (congrArg Neg.neg unit_pair)
    simp [lemma_poisson_power_on_exponential_fields, neg_pair, exponential_field, smul_smul, mul_comm]
  have e := adjoint n p x
  rw [show dirac_adjoint metric p = p from lemma_coordinate_exponential_field_self_adjoint metric square _,
    show dirac_adjoint metric x = x from lemma_coordinate_exponential_field_self_adjoint metric square _] at e
  have h := congrArg (fun Y : S => Y.val 0) e
  change metric * ((C n p x).val 0).conjTranspose * metric = (C n x p).val 0 at h
  rw [forward, backward, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    mul_smul_comm, mul_one, smul_mul_assoc, square] at h
  simpa using congrArg (fun A : SpinMatrix => A 0 0) h

theorem theorem_selection_from_dirac_adjoint (C : CoefficientFamily) (p : ℕ → DifferentialSymbol)
    (locality : ansatz_scalar_locality C p) (covariance : ∀ n, ansatz_symplectic_covariance (p n))
    (grading : ∀ n, ansatz_order_homogeneity n (p n)) (assoc : ansatz_matrix_associativity C)
    (neutral : ansatz_constant_matrix_neutrality C) (classical_limit : ∀ F G, C 0 F G = F * G)
    (metric : SpinMatrix) (square : metric*metric=1)
    (adjoint : ansatz_dirac_adjoint_compatibility metric C) (scale : ansatz_oriented_weyl_scale C) :
    ∀ n (F G : S), (C n F G : Symbol) = moyal_coefficient n F G := by
  have reduction (n : ℕ) (F G : S) : (C n F G : Symbol) = scalar_coefficient p n • poisson_power n F G := by
    rw [theorem_neutral_extension C p locality assoc neutral,
      theorem_canonical_form_of_scalar_symbol n _ (covariance n) (grading n), map_smul]
    rfl
  have phase := theorem_adjoint_forces_coefficient_phase C _ reduction metric square adjoint 1
  have real_zero := congrArg Complex.re phase
  simp at real_zero
  have first : scalar_coefficient p 1 = Complex.I/2 := by
    apply Complex.ext
    · simp; linarith
    · rw [show (scalar_coefficient p 1).im = 1/2 from by
        rw [← lemma_canonical_test_response C _ reduction 1]; exact scale]
      norm_num [Complex.div_ofNat_im]
  apply theorem_smooth_composition_is_moyal C p locality covariance grading assoc neutral classical_limit
  intro F G
  rw [reduction, reduction, first, ← smul_sub, weyl_transport, smul_smul]
  congr 1
  ring
end
end MassShell.CompositionAndTransport

namespace MassShell.CompositionAndTransport
noncomputable section
open scoped ComplexConjugate ContDiff TensorProduct
open TensorProduct
set_option synthInstance.maxHeartbeats 300000
def reverse_slot : Slot → Slot | .left => .right | .right => .left
def adjoint_polynomial : DifferentialSymbol →+* DifferentialSymbol :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (starRingEnd ℂ))
    (fun v => MvPolynomial.X (reverse_slot v.1,v.2))

theorem lemma_adjoint_canonical : adjoint_polynomial canonical_symbol = -canonical_symbol := by
  simp only [canonical_symbol,contraction,map_sum,map_sub,map_mul,adjoint_polynomial,
    MvPolynomial.eval₂Hom_X',reverse_slot,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intros
  ring

theorem lemma_moyal_polynomial_adjoint (n : ℕ) : adjoint_polynomial (moyal_polynomial n) =
    moyal_polynomial n := by
  have scale : conj (moyal_weight n) = (-1 : ℂ)^n * moyal_weight n := by
    have two : conj (2:ℂ) = 2 := map_ofNat _ _
    simp only [moyal_weight,map_div₀,map_pow,Complex.conj_I,two,map_natCast]
    rw [neg_div, neg_eq_neg_one_mul (Complex.I/2), mul_pow]
    ring
  rw [moyal_polynomial, map_mul, map_pow, lemma_adjoint_canonical]
  change (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C _)) * _ = _
  rw [MvPolynomial.eval₂Hom_C]
  change MvPolynomial.C (conj (moyal_weight n)) * _ = _
  rw [scale, map_mul, map_pow, map_neg, map_one, neg_eq_neg_one_mul canonical_symbol, mul_pow]
  have sign : (-1 : DifferentialSymbol)^n * (-1)^n = 1 := by rw [← mul_pow]; simp
  linear_combination (MvPolynomial.C (moyal_weight n) * canonical_symbol^n) * sign

theorem lemma_hermitian_partial (i : Axis) (F : S) :
    hermitian_field (partial_map i F) = partial_map i (hermitian_field F) := by
  apply Subtype.ext
  funext z r s
  let f := fun y => F.val y s r
  change Complex.conjCLE (fderiv ℝ f z (direction i)) =
    fderiv ℝ (Complex.conjCLE ∘ f) z (direction i)
  rw [fderiv_comp _ Complex.conjCLE.differentiableAt ((F.property s r).differentiable (by simp) z)]
  rw [Complex.conjCLE.hasFDerivAt.fderiv]
  rfl

theorem lemma_adjoint_tensor_polynomial (p : DifferentialSymbol) (F G : S) :
    hermitian_field (tensor_operator p (F ⊗ₜ[ℂ] G)) =
    tensor_operator (adjoint_polynomial p) (hermitian_field G ⊗ₜ[ℂ] hermitian_field F) := by
  induction p using MvPolynomial.induction_on generalizing F G with
  | C c =>
    have const_rule (r : ℂ) (A B : S) :
        tensor_operator (MvPolynomial.C r) (A ⊗ₜ[ℂ] B) = r • (A*B) := by
      rw [MvPolynomial.C_eq_algebraMap, tensor_operator, LinearMap.comp_apply, pair_calculus.commutes]
      change matrix_multiply (r • (A ⊗ₜ[ℂ] B)) = _
      rw [map_smul]
      rfl
    rw [const_rule, adjoint_polynomial, MvPolynomial.eval₂Hom_C]
    change _ = tensor_operator (MvPolynomial.C (conj c)) _
    rw [const_rule]
    apply Subtype.ext
    funext z
    change (c • (F.val z * G.val z)).conjTranspose = _
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul]
    rfl
  | add p q hp hq =>
    have add_rule (u v : DifferentialSymbol) (t : PairSpace) :
        tensor_operator (u+v) t = tensor_operator u t + tensor_operator v t := by
      change matrix_multiply (pair_calculus (u+v) t) = _
      have add_coeff : pair_calculus (u+v) = pair_calculus u + pair_calculus v :=
        pair_calculus.toLinearMap.map_add u v
      rw [add_coeff]
      exact matrix_multiply.map_add _ _
    rw [map_add, add_rule,add_rule, ← hp,← hq]
    apply Subtype.ext
    funext z
    exact Matrix.conjTranspose_add _ _
  | mul_X p j ih =>
    obtain ⟨slot,i⟩ := j
    have left (u : DifferentialSymbol) (A B : S) : tensor_operator
        (u*MvPolynomial.X (.left,i)) (A ⊗ₜ[ℂ] B) =
        tensor_operator u ((partial_map i A) ⊗ₜ[ℂ] B) := by
      simp [tensor_operator,pair_calculus,pair_partial]
    have right (u : DifferentialSymbol) (A B : S) : tensor_operator
        (u*MvPolynomial.X (.right,i)) (A ⊗ₜ[ℂ] B) =
        tensor_operator u (A ⊗ₜ[ℂ] (partial_map i B)) := by
      simp [tensor_operator,pair_calculus,pair_partial]
    rw [map_mul]
    cases slot <;> simp only [adjoint_polynomial,MvPolynomial.eval₂Hom_X',reverse_slot,left,right] <;>
      rw [ih, lemma_hermitian_partial] <;> rfl

theorem theorem_constructed_dirac_adjoint (metric : SpinMatrix) (square : metric*metric=1) :
    ansatz_dirac_adjoint_compatibility metric moyal_family := by
  intro n F G
  let M := constant_matrix metric
  have mm : M*M = 1 := by apply Subtype.ext; funext z; exact square
  have h := lemma_adjoint_tensor_polynomial (moyal_polynomial n) F G
  rw [lemma_moyal_polynomial_adjoint] at h
  change hermitian_field (moyal_family n F G) = moyal_family n (hermitian_field G) (hermitian_field F) at h
  let B := moyal_family n
  have bal := lemma_balancing_from_associativity moyal_family theorem_moyal_smooth_associativity
    theorem_moyal_neutrality n metric
  change M*hermitian_field (moyal_family n F G)*M = B (M*hermitian_field G*M) (M*hermitian_field F*M)
  rw [h, (bal _ _).2.2, (bal _ _).2.1]
  change _ = B (M*hermitian_field G) (M*(M*hermitian_field F))*M
  rw [← mul_assoc M M, mm, one_mul, (bal _ _).1]
end
end MassShell.CompositionAndTransport

namespace MassShell
noncomputable section
open Matrix
set_option maxHeartbeats 3000000
abbrev PauliMatrix := Matrix (Fin 2) (Fin 2) ℂ

def pauli : Fin 3 → PauliMatrix := ![!![0,1;1,0], !![0,-Complex.I;Complex.I,0], !![1,0;0,-1]]
def gamma_axis (i : Fin 4) := four_component_factor (Pi.single i 1)
def rest_spin (j k : Fin 4) : FourByFour :=
  (Complex.I/2) • (gamma_axis j * gamma_axis k - gamma_axis k * gamma_axis j)

def cyclic_spin : Fin 3 → FourByFour := ![rest_spin 2 3, rest_spin 3 1, rest_spin 1 2]
def block_spin (A : PauliMatrix) : FourByFour :=
  !![A 0 0,A 0 1,0,0; A 1 0,A 1 1,0,0; 0,0,A 0 0,A 0 1; 0,0,A 1 0,A 1 1]

theorem theorem_clifford_generators_give_pauli (k : Fin 3) : cyclic_spin k = block_spin (pauli k) := by
  ext r s
  fin_cases k <;> fin_cases r <;> fin_cases s <;>
    norm_num [cyclic_spin, rest_spin, gamma_axis, four_component_factor, four_component_pencil,
      pauli, block_spin, Matrix.mul_apply, Fin.sum_univ_four, Pi.single_apply, Complex.I_mul_I] <;>
    ring_nf <;> simp

def sector_embedding (sign : ℂ) (v : Fin 2 → ℂ) : Fin 4 → ℂ :=
  ![v 0,v 1,sign*v 0,sign*v 1]

theorem lemma_sector_embedding_injective (sign : ℂ) : Function.Injective (sector_embedding sign) := by
  intro u v h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1

theorem theorem_pauli_on_rest_sector (sign : ℂ) (hs : sign*sign=1) (v : Fin 2 → ℂ) (k : Fin 3) :
    (gamma_axis 0).mulVec (sector_embedding sign v) = sign • sector_embedding sign v ∧
    (cyclic_spin k).mulVec (sector_embedding sign v) = sector_embedding sign ((pauli k).mulVec v) := by
  constructor
  · funext i
    fin_cases i <;> simp [gamma_axis, four_component_factor, four_component_pencil, sector_embedding,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four, ← mul_assoc, hs]
  · rw [theorem_clifford_generators_give_pauli]
    funext i
    fin_cases i <;> simp [sector_embedding, block_spin, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Fin.sum_univ_two] <;> ring

theorem theorem_pauli_algebra : (∀ k, pauli k * pauli k = 1) ∧
    pauli 0 * pauli 1 = Complex.I • pauli 2 ∧
    pauli 1 * pauli 2 = Complex.I • pauli 0 ∧ pauli 2 * pauli 0 = Complex.I • pauli 1 := by
  constructor
  · intro k
    ext i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      simp [pauli, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]
  · refine ⟨?_,?_,?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [pauli, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- For involutions representing two unit timelike momenta, the Clifford
anticommutator supplies an invertible intertwiner whenever 1 + u·v is nonzero. -/
theorem theorem_transport_between_timelike_sectors (J K : FourByFour) (j2 : J*J=1)
    (k2 : K*K=1) (t : ℂ) (inner : J*K+K*J=t • (1 : FourByFour)) (gap : 2+t ≠ 0) :
    ∃ U : FourByFourˣ, (U : FourByFour)*J = K*(U : FourByFour) := by
  let A := 1+K*J
  let B := 1+J*K
  have ab : A*B = (2+t) • (1 : FourByFour) := by
    have mid : K*J*(J*K)=1 := by rw [mul_assoc, ← mul_assoc J, j2, one_mul, k2]
    dsimp [A,B]
    rw [add_mul, one_mul, mul_add, mul_one, mid, add_smul]
    rw [← inner]
    module
  have ba : B*A = (2+t) • (1 : FourByFour) := by
    have mid : J*K*(K*J)=1 := by rw [mul_assoc, ← mul_assoc K, k2, one_mul, j2]
    dsimp [A,B]
    rw [add_mul, one_mul, mul_add, mul_one, mid, add_smul, ← inner]
    module
  refine ⟨⟨A, (2+t)⁻¹ • B, ?_, ?_⟩, ?_⟩
  · rw [mul_smul_comm, ab, smul_smul, inv_mul_cancel₀ gap, one_smul]
  · rw [smul_mul_assoc, ba, smul_smul, inv_mul_cancel₀ gap, one_smul]
  · change (1+K*J)*J = K*(1+K*J)
    rw [add_mul, mul_add, one_mul, mul_one, mul_assoc, j2, mul_one, ← mul_assoc, k2, one_mul]
    exact add_comm _ _
end
end MassShell

namespace MassShell
noncomputable section
open Matrix
local notation "η" => minkowski_pairing
local notation "K" => four_component_factor
def mass_pair : FourMomentum →ₗ[ℝ] FourMomentum →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ η (by intros; simp [minkowski_pairing]; ring)
    (by intros; simp [minkowski_pairing]; ring) (by intros; simp [minkowski_pairing]; ring)
    (by intros; simp [minkowski_pairing]; ring)
theorem lemma_mass_pair_symm (p q : FourMomentum) : η p q = η q p := by unfold minkowski_pairing; ring

def hyperplane_reflection (d : FourMomentum) : FourMomentum →ₗ[ℝ] FourMomentum :=
  LinearMap.id - (2 / η d d) • (mass_pair d).smulRight d

theorem lemma_reflection_formula (d x : FourMomentum) :
    hyperplane_reflection d x = x - (2 * η d x / η d d) • d := by
  simp [hyperplane_reflection,LinearMap.smulRight_apply,smul_smul, mass_pair,div_mul_eq_mul_div]

theorem lemma_reflection_preserves_pairing (d : FourMomentum) (positive_norm : η d d ≠ 0)
    (x y : FourMomentum) : η (hyperplane_reflection d x) (hyperplane_reflection d y) = η x y := by
  rw [lemma_reflection_formula,lemma_reflection_formula]
  change mass_pair _ _ = _
  simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
  change η x y - _ - _ = _
  change η x y - (2*η d x/η d d)*η d y -
    (2*η d y/η d d)*(η x d - (2*η d x/η d d)*η d d) = _
  rw [lemma_mass_pair_symm x d]
  field_simp
  ring

def chirality_matrix : FourByFour := Matrix.diagonal ![1,1,-1,-1]

theorem lemma_chirality (p : FourMomentum) : chirality_matrix * K p = -(K p * chirality_matrix) := by
  ext i j
  change (chirality_matrix * four_component_pencil p) i j = -((four_component_pencil p * chirality_matrix) i j)
  unfold chirality_matrix
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [four_component_pencil]

theorem lemma_reflection_has_spin_lift (d : FourMomentum) (hd : η d d ≠ 0) :
    ∃ U : FourByFourˣ, ∀ x, (U : FourByFour) * K x = K (hyperplane_reflection d x) * U := by
  have ss := theorem_four_components_are_sufficient d
  let G : FourByFourˣ := ⟨K d,(η d d)⁻¹ • K d, by rw [mul_smul_comm,ss,smul_smul,inv_mul_cancel₀ hd,one_smul],
    by rw [smul_mul_assoc,ss,smul_smul,inv_mul_cancel₀ hd,one_smul]⟩
  have ch2 : chirality_matrix * chirality_matrix = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [chirality_matrix]
  let ch : FourByFourˣ := ⟨chirality_matrix,chirality_matrix,ch2,ch2⟩
  refine ⟨ch*G,fun x => ?_⟩
  have mixed := theorem_factorisation_forces_clifford_relation K theorem_four_components_are_sufficient d x
  have scale : (2 * η d x / η d d) * η d d = 2*η d x := div_mul_cancel₀ _ hd
  have reflected : K (hyperplane_reflection d x) * K d = -(K d * K x) := by
    rw [lemma_reflection_formula,map_sub,map_smul,sub_mul,smul_mul_assoc,ss,smul_smul,scale,← mixed]
    abel
  change chirality_matrix*K d*K x = K (hyperplane_reflection d x)*(chirality_matrix*K d)
  rw [mul_assoc, ← neg_neg (K d*K x), ← reflected, mul_neg, ← mul_assoc,
    lemma_chirality, neg_mul, neg_neg,mul_assoc]

private def transform_has_lift (L : FourMomentum →ₗ[ℝ] FourMomentum) : Prop :=
  (∀ x y, η (L x) (L y) = η x y) ∧ ∃ U : FourByFourˣ, ∀ x, (U : FourByFour)*K x = K (L x)*U

private theorem lemma_lift_composition (M L : FourMomentum →ₗ[ℝ] FourMomentum)
    (hm : transform_has_lift M) (hl : transform_has_lift L) : transform_has_lift (M.comp L) := by
  obtain ⟨mp,U,mu⟩ := hm
  obtain ⟨lp,V,lv⟩ := hl
  refine ⟨fun x y => (mp _ _).trans (lp x y), U*V, fun x => ?_⟩
  change (U:FourByFour)*V*K x = K (M (L x))*((U:FourByFour)*V)
  rw [mul_assoc, lv, ← mul_assoc,mu,mul_assoc]

private theorem lemma_correct_vector (u v : FourMomentum) (same : η u u = η v v)
    (nonzero : η u u ≠ 0) :
    ∃ R : FourMomentum →ₗ[ℝ] FourMomentum, transform_has_lift R ∧ R u = v ∧
      ∀ w, η u w = 0 → η v w = 0 → R w = w := by
  have one (a b : FourMomentum) (eqnorm : η a a = η b b) (hd : η (a-b) (a-b) ≠ 0) :
      hyperplane_reflection (a-b) a = b := by
    have dbl : η (a-b) (a-b) = 2 * η (a-b) a := by
      change mass_pair (a-b) (a-b) = 2*mass_pair (a-b) a
      simp only [map_sub, LinearMap.sub_apply]
      change η a a - η b a - (η a b - η b b) = 2*(η a a - η b a)
      rw [lemma_mass_pair_symm a b,← eqnorm]; ring
    rw [lemma_reflection_formula,← dbl,div_self hd,one_smul]; abel
  have refl (d) (hd : η d d ≠ 0) : transform_has_lift (hyperplane_reflection d) :=
    ⟨lemma_reflection_preserves_pairing d hd,lemma_reflection_has_spin_lift d hd⟩
  have fix (a b w : FourMomentum) (ha : η a w = 0) (hb : η b w = 0) :
      hyperplane_reflection (a-b) w = w := by
    have h : η (a-b) w = 0 := (show mass_pair (a-b) w = 0 by
      rw [map_sub,LinearMap.sub_apply]; exact sub_eq_zero.mpr (ha.trans hb.symm))
    simp [lemma_reflection_formula,h]
  by_cases hd : η (u-v) (u-v) ≠ 0
  · exact ⟨_, refl _ hd, one _ _ same hd,fix u v⟩
  · have nn : η (-v) (-v) = η v v := by simp [minkowski_pairing]
    have plus : η (u- -v) (u- -v) ≠ 0 := by
      change ¬ mass_pair (u- -v) (u- -v) = 0
      change ¬ mass_pair (u-v) (u-v) ≠ 0 at hd
      simp only [map_sub,LinearMap.sub_apply,map_neg,LinearMap.neg_apply,not_not] at *
      rw [show mass_pair u v = mass_pair v u from lemma_mass_pair_symm u v] at *
      change mass_pair u u = mass_pair v v at same
      change mass_pair u u ≠ 0 at nonzero
      intro h; apply nonzero; linarith
    let R := hyperplane_reflection (u- -v)
    have nv : η v v ≠ 0 := same ▸ nonzero
    refine ⟨(hyperplane_reflection v).comp R, lemma_lift_composition _ _ (refl _ nv) (refl _ plus), ?_, ?_⟩
    · change hyperplane_reflection v (hyperplane_reflection _ u) = _
      rw [one _ _ (same.trans nn.symm) plus, map_neg,lemma_reflection_formula]
      rw [mul_div_cancel_right₀ _ nv,two_smul]; abel
    · intro w hu hv
      change hyperplane_reflection v (hyperplane_reflection _ w) = _
      rw [fix _ _ _ hu (show η (-v) w = 0 by change mass_pair (-v) w = 0; simp [hv,mass_pair] at *)]
      simp [lemma_reflection_formula,hv]

/-- Every Lorentz isometry of four-momentum is implemented by similarity on
the explicit minimal pencil. The lift may depend on the isometry. -/
theorem theorem_lorentz_covariance_of_minimal_factor (T : FourMomentum ≃ₗ[ℝ] FourMomentum)
    (preserves : ∀ u v, η (T u) (T v) = η u v) :
    ∃ U : FourByFourˣ, ∀ x, (U : FourByFour)*K x = K (T x)*U := by
  let e (i : Fin 4) : FourMomentum := Pi.single i 1
  have orth (i j : Fin 4) (ne : i ≠ j) : η (e i) (e j) = 0 := by
    fin_cases i <;> fin_cases j <;> simp_all [e,minkowski_pairing]
  have sq (i : Fin 4) : η (e i) (e i) ≠ 0 := by fin_cases i <;> norm_num [e,minkowski_pairing,Pi.single_apply]
  have align_axes (n : ℕ) (hn : n ≤ 4) :
      ∃ L : FourMomentum →ₗ[ℝ] FourMomentum, transform_has_lift L ∧ ∀ i : Fin 4, i.val<n → L (e i) = T (e i) := by
    induction n with
    | zero => exact ⟨LinearMap.id, ⟨fun _ _ => rfl,1,fun x => by simp⟩,fun i h => by omega⟩
    | succ n ih =>
      obtain ⟨L,lift,agree⟩ := ih (by omega)
      let j : Fin 4 := ⟨n,by omega⟩
      have lu := lift.1 (e j) (e j)
      obtain ⟨R,hr,hit,fix⟩ := lemma_correct_vector _ _ (lu.trans (preserves _ _).symm)
        (lu ▸ sq j)
      refine ⟨R.comp L, lemma_lift_composition _ _ hr lift, fun i hi => ?_⟩
      by_cases h : i = j
      · subst i; exact hit
      · have lt : i.val<n := by have := Fin.ext_iff.not.mp h; change i.val ≠ n at this; omega
        change R (L (e i)) = T (e i)
        rw [agree i lt]
        apply fix
        · rw [← agree i lt,lift.1,orth j i (Ne.symm h)]
        · rw [preserves,orth j i (Ne.symm h)]
  obtain ⟨L,⟨_,U,implements⟩,agrees⟩ := align_axes 4 le_rfl
  refine ⟨U,fun x => ?_⟩
  have eqn : L x = T x := by
    rw [pi_eq_sum_univ' x,map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change L (x i • e i) = T (x i • e i)
    rw [map_smul,map_smul,agrees i i.isLt]
  rw [← eqn,implements]
end
end MassShell

namespace MassShell.CompositionAndTransport
noncomputable section
open scoped ContDiff
set_option maxHeartbeats 2000000
def phase_coordinate (z : PhasePoint) : Axis → ℝ := Sum.elim z.1 z.2
def complex_covector_of_real (x : RealPhaseCovector) : ComplexPhaseCovector :=
  ∑ i, (x i : ℂ) • coordinate_covector i

theorem lemma_complex_covector_of_real_direction (x : RealPhaseCovector) (i : Axis) :
    complex_covector_of_real x (direction i) = (x i : ℂ) := by
  cases i <;> simp [complex_covector_of_real, coordinate_covector, direction, Fintype.sum_sum_type,
    Pi.single_apply, apply_ite]

def real_covector_exponential_field (x : RealPhaseCovector) : S :=
  ⟨exponential_field (complex_covector_of_real x) 1, lemma_exponential_field_is_smooth _ _⟩

def phase_pullback (T : RealPhaseCovector ≃ₗ[ℝ] RealPhaseCovector) (z : PhasePoint) : PhasePoint :=
  let component (j : Axis) := ∑ i, T (Pi.single j 1) i * phase_coordinate z i
  (fun j => component (.inl j), fun j => component (.inr j))

theorem lemma_phase_pullback_dual (T : RealPhaseCovector ≃ₗ[ℝ] RealPhaseCovector) (z : PhasePoint) (x : RealPhaseCovector) :
    complex_covector_of_real x (phase_pullback T z) = complex_covector_of_real (T x) z := by
  have formula (v : RealPhaseCovector) (y : PhasePoint) :
      complex_covector_of_real v y = ((∑ i, v i * phase_coordinate y i : ℝ) : ℂ) := by
    simp [complex_covector_of_real,phase_coordinate,coordinate_covector,Fintype.sum_sum_type]
  rw [formula, formula]
  congr 1
  have expand (i : Axis) : T x i = ∑ j, x j * T (Pi.single j 1) i := by
    calc
      T x i = T (∑ j, x j • Pi.single j 1) i := congrArg (fun v => T v i) (pi_eq_sum_univ' x)
      _ = _ := by simp [Finset.sum_apply]
  have coord (j : Axis) : phase_coordinate (phase_pullback T z) j =
      ∑ i, T (Pi.single j 1) i * phase_coordinate z i := by cases j <;> rfl
  simp only [coord,expand,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/-- Operator translation invariance, stated directly on translated input fields. -/
def ansatz_field_translation_invariance (C : CoefficientFamily) : Prop :=
  ∀ n t (F G Ft Gt : S), (∀ z, Ft.val z = F.val (z+t)) → (∀ z, Gt.val z = G.val (z+t)) →
    ∀ z, (C n Ft Gt).val z = (C n F G).val (z+t)

/-- The canonical transformation acts on phase-space arguments by its dual action. -/
def ansatz_field_symplectic_covariance (C : CoefficientFamily) : Prop :=
  ∀ n (T : RealPhaseCovector ≃ₗ[ℝ] RealPhaseCovector), (∀ x y, omega (T x) (T y) = omega x y) →
    ∀ (F G Ft Gt : S), (∀ z, Ft.val z = F.val (phase_pullback T z)) →
      (∀ z, Gt.val z = G.val (phase_pullback T z)) →
      ∀ z, (C n Ft Gt).val z = (C n F G).val (phase_pullback T z)

/-- Finite bidifferential order allows a local polynomial varying with the evaluation point.
Testing only the 00 scalar corner suffices. -/
def ansatz_local_differential_coordinates (C : CoefficientFamily)
    (p : ℕ → PhasePoint → DifferentialSymbol) : Prop :=
  ∀ n (F G : S) i k j z,
    (C n (smooth_corner F i k) (smooth_corner G k j)).val z 0 0 =
    differential_operator (corner F i k) (corner G k j) (p n z) z 0 0

def corner_exponential_field (x : RealPhaseCovector) : S := smooth_corner (real_covector_exponential_field x) 0 0

theorem lemma_corner_exponential_field_value (x : RealPhaseCovector) :
    (corner_exponential_field x : Symbol) = exponential_field (complex_covector_of_real x) (Matrix.single 0 0 1) := by
  funext z
  ext i j
  by_cases h : (0:Fin 4)=i ∧ (0:Fin 4)=j <;>
    simp [corner_exponential_field,smooth_corner,corner,real_covector_exponential_field,exponential_field,Matrix.single_apply,h]

theorem lemma_local_symbol_from_fields (C : CoefficientFamily) (p : ℕ → PhasePoint → DifferentialSymbol)
    (locality : ansatz_local_differential_coordinates C p) (n : ℕ) (z : PhasePoint) (x y : RealPhaseCovector) :
    (C n (corner_exponential_field x) (corner_exponential_field y)).val z 0 0 =
      Complex.exp ((complex_covector_of_real x + complex_covector_of_real y) z) * symbol_value (p n z) x y := by
  rw [show (C n (corner_exponential_field x) (corner_exponential_field y)).val z 0 0 = _ from
    locality n (real_covector_exponential_field x) (real_covector_exponential_field y) 0 0 0 z]
  change differential_operator (corner_exponential_field x) (corner_exponential_field y) (p n z) z 0 0 = _
  rw [lemma_corner_exponential_field_value,lemma_corner_exponential_field_value,lemma_operator_on_exponential_fields]
  have covector_coordinates : derivative_coordinates (complex_covector_of_real x) (complex_covector_of_real y) = real_variables x y := by
    funext j
    obtain ⟨s,i⟩ := j
    cases s <;> apply lemma_complex_covector_of_real_direction
  simp [covector_coordinates,symbol_value,exponential_field]

theorem theorem_translation_forces_constant_coefficients (C : CoefficientFamily)
    (p : ℕ → PhasePoint → DifferentialSymbol) (locality : ansatz_local_differential_coordinates C p)
    (translations : ansatz_field_translation_invariance C) (n : ℕ) (z : PhasePoint) :
    p n z = p n 0 := by
  apply lemma_real_symbol_ext
  intro x y
  have shift (v : RealPhaseCovector) (q : PhasePoint) :
      (Complex.exp (complex_covector_of_real v z) • corner_exponential_field v : S).val q = (corner_exponential_field v).val (q+z) := by
    change Complex.exp _ • (corner_exponential_field v).val q = _
    rw [lemma_corner_exponential_field_value]
    simp [exponential_field, Complex.exp_add,mul_comm]
  have eqn := congrArg (fun A : SpinMatrix => A 0 0)
    (translations n z (corner_exponential_field x) (corner_exponential_field y) _ _ (shift x) (shift y) 0)
  let ex (v : RealPhaseCovector) := Complex.exp (complex_covector_of_real v z)
  have lin : C n (ex x • corner_exponential_field x) (ex y • corner_exponential_field y) =
      ex x • ex y • C n (corner_exponential_field x) (corner_exponential_field y) := by
    rw [(C n).map_smul]
    change ex x • (C n (corner_exponential_field x) (ex y • corner_exponential_field y)) = _
    rw [(C n (corner_exponential_field x)).map_smul]
  change (C n (ex x • corner_exponential_field x) (ex y • corner_exponential_field y)).val 0 0 0 =
    (C n (corner_exponential_field x) (corner_exponential_field y)).val (0+z) 0 0 at eqn
  rw [lin, zero_add] at eqn
  change ex x * (ex y * (C n (corner_exponential_field x) (corner_exponential_field y)).val 0 0 0) = _ at eqn
  rw [lemma_local_symbol_from_fields C p locality, lemma_local_symbol_from_fields C p locality] at eqn
  simp only [map_zero,Complex.exp_zero,one_mul,add_apply,Complex.exp_add] at eqn
  exact mul_left_cancel₀ (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
    (eqn.symm.trans (mul_assoc _ _ _).symm)

theorem theorem_field_covariance_forces_symbol_covariance (C : CoefficientFamily)
    (p : ℕ → PhasePoint → DifferentialSymbol) (locality : ansatz_local_differential_coordinates C p)
    (covariance : ansatz_field_symplectic_covariance C) (n : ℕ) :
    ansatz_symplectic_covariance (p n 0) := by
  intro T preserves x y
  have trans (v : RealPhaseCovector) (z : PhasePoint) :
      (corner_exponential_field (T v)).val z = (corner_exponential_field v).val (phase_pullback T z) := by
    rw [lemma_corner_exponential_field_value,lemma_corner_exponential_field_value]
    simp [exponential_field, lemma_phase_pullback_dual]
  have e := congrArg (fun A : SpinMatrix => A 0 0)
    (covariance n T preserves _ _ _ _ (trans x) (trans y) 0)
  have zero : phase_pullback T 0 = 0 := by
    ext j <;> simp [phase_pullback, phase_coordinate]
  simpa only [zero,lemma_local_symbol_from_fields C p locality,map_zero,Complex.exp_zero,one_mul] using e

/-- Selection directly from translation and canonical covariance of the fields. -/
theorem theorem_selection_from_field_ansatze (C : CoefficientFamily)
    (p : ℕ → PhasePoint → DifferentialSymbol)
    (locality : ansatz_local_differential_coordinates C p)
    (translations : ansatz_field_translation_invariance C)
    (covariance : ansatz_field_symplectic_covariance C)
    (grading : ∀ n, ansatz_order_homogeneity n (p n 0))
    (assoc : ansatz_matrix_associativity C) (neutral : ansatz_constant_matrix_neutrality C)
    (classical_limit : ∀ F G, C 0 F G = F * G)
    (metric : SpinMatrix) (square : metric * metric = 1)
    (adjoint : ansatz_dirac_adjoint_compatibility metric C)
    (scale : ansatz_oriented_weyl_scale C) :
    ∀ n (F G : S), (C n F G : Symbol) = moyal_coefficient n F G := by
  apply theorem_selection_from_dirac_adjoint C (fun n => p n 0) _ _
    grading assoc neutral classical_limit metric square adjoint scale
  · intro n F G i k j z
    have local_value := locality n F G i k j z
    rw [theorem_translation_forces_constant_coefficients C p locality translations n z] at local_value
    exact local_value
  · exact theorem_field_covariance_forces_symbol_covariance C p locality covariance
end
end MassShell.CompositionAndTransport

namespace MassShell.CompositionAndTransport
noncomputable section
open MeasureTheory
set_option maxHeartbeats 2000000
open scoped ContDiff
abbrev TestMatrix := Matrix (Fin 4) (Fin 4) PhaseTests
def test_pairing : TestMatrix →ₗ[ℂ] (EnsembleDistribution → ℂ) where
  toFun t W := ∑ i, ∑ j, W i j (t i j)
  map_add' t u := by funext W; simp [Finset.sum_add_distrib]
  map_smul' c t := by funext W; simp [Finset.mul_sum]

def weak_action (A : EnsembleDistribution → EnsembleDistribution) : Prop :=
  ∀ i j φ, (fun W => A W i j φ) ∈ test_pairing.range

theorem lemma_single_test (i j : Fin 4) (φ : PhaseTests) :
    (fun W : EnsembleDistribution => W i j φ) ∈ test_pairing.range := by
  use Matrix.single i j φ
  funext W
  classical
  simp [test_pairing, Matrix.single_apply, apply_ite, ite_and]

theorem lemma_weak_action_comp {A B : EnsembleDistribution → EnsembleDistribution}
    (ha : weak_action A) (hb : weak_action B) : weak_action (fun W => A (B W)) := by
  intro i j φ
  obtain ⟨t, ht⟩ := ha i j φ
  have eqn : (fun W => A (B W) i j φ) = ∑ r, ∑ s, (fun W => B W r s (t r s)) := by
    funext W
    simpa [test_pairing,Finset.sum_apply] using (congrFun ht (B W)).symm
  rw [eqn]
  exact Submodule.sum_mem _ fun r _ => Submodule.sum_mem _ fun s _ => hb r s _

theorem lemma_weak_action_sum {ι : Type*} (t : Finset ι)
    (A : ι → EnsembleDistribution → EnsembleDistribution) (h : ∀ k ∈ t, weak_action (A k)) :
    weak_action (fun W => ∑ k ∈ t, A k W) := by
  intro i j φ
  have e : (fun W => (∑ k ∈ t, A k W) i j φ) = ∑ k ∈ t, (fun W => A k W i j φ) := by
    funext W
    simp [Matrix.sum_apply,Finset.sum_apply]
  rw [e]
  exact Submodule.sum_mem _ fun k hk => h k hk i j φ

theorem lemma_weak_action_smul (c : ℂ) {A : EnsembleDistribution → EnsembleDistribution}
    (h : weak_action A) : weak_action (fun W => c • A W) :=
  fun i j φ => test_pairing.range.smul_mem c (h i j φ)

theorem lemma_distribution_derivative_is_weak (d : Axis) : weak_action (distribution_directional d) := by
  intro i j φ
  exact test_pairing.range.neg_mem (lemma_single_test i j (TestFunction.lineDerivCLM ℂ (direction d) φ))

theorem lemma_mixed_word_is_weak (side : ProductSide) (word : List Variable) (F : S) :
    weak_action (mixed_word side word F) := by
  induction word generalizing F with
  | nil =>
    intro i j φ
    cases side <;> simp only [mixed_word, mixed_multiplication, Matrix.of_apply, sum_apply]
    · have e (k : Fin 4) := lemma_single_test k j
          (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (F.property i k) φ)
      convert Submodule.sum_mem test_pairing.range (t := Finset.univ) (fun k _ => e k) using 1
      ext W; simp [smooth_times_distribution, Finset.sum_apply]
    · have e (k : Fin 4) := lemma_single_test i k
          (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (F.property k j) φ)
      convert Submodule.sum_mem test_pairing.range (t := Finset.univ) (fun k _ => e k) using 1
      ext W; simp [smooth_times_distribution, Finset.sum_apply]
  | cons d w ih =>
    obtain ⟨s,i⟩ := d
    cases side <;> cases s <;> first | exact ih _ | exact (lemma_weak_action_comp (A := mixed_word _ w F) (B := distribution_directional i) (ih F) (lemma_distribution_derivative_is_weak i))

theorem lemma_moyal_action_is_weak (side : ProductSide) (n : ℕ) (H : S) :
    weak_action (distribution_moyal_coefficient side n H) :=
  lemma_weak_action_smul _ (lemma_weak_action_sum _ _ (fun _ _ =>
    lemma_weak_action_smul _ (lemma_mixed_word_is_weak side _ H)))

theorem lemma_regular_fields_separate_tests (t : TestMatrix)
    (vanishes : ∀ F : S, test_pairing t (regular_ensemble F) = 0) : t = 0 := by
  ext i j x
  have ae := ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := phase_measure) (t i j).contDiff.continuous.locallyIntegrable
    (by
      intro g hg _
      let field : S := ⟨fun z => Matrix.single i j (g z : ℂ), by
        intro r s
        by_cases e : i = r ∧ j = s
        · simpa [Matrix.single_apply,e,Function.comp_def] using Complex.ofRealCLM.contDiff.comp hg
        · simp only [Matrix.single_apply,ite_eq_right e]; exact contDiff_const⟩
      have h := vanishes field
      have reg (r s : Fin 4) : regular_ensemble field r s (t r s) =
          ∫ z, t r s z * (field.val z r s) ∂phase_measure := lemma_regular_evaluation
            (field.property r s).continuous _
      simp only [test_pairing, LinearMap.coe_mk, AddHom.coe_mk, reg] at h
      have isolate (r s : Fin 4) : (∫ z, t r s z * field.val z r s ∂phase_measure) =
          if i = r ∧ j = s then ∫ z, g z • t r s z ∂phase_measure else 0 := by
        split_ifs with e <;> simp [field,e, Complex.real_smul,mul_comm]
      simpa [isolate,ite_and] using h)
  exact congrFun (Measure.eq_of_ae_eq ae (t i j).contDiff.continuous continuous_zero) x

theorem lemma_weak_action_ext {A B : EnsembleDistribution → EnsembleDistribution}
    (ha : weak_action A) (hb : weak_action B)
    (h : ∀ F : S, A (regular_ensemble F) = B (regular_ensemble F)) : A = B := by
  funext W
  ext i j φ
  obtain ⟨u,hu⟩ := ha i j φ
  obtain ⟨v,hv⟩ := hb i j φ
  have same : u-v = 0 := by
    apply lemma_regular_fields_separate_tests
    intro F
    rw [map_sub,hu,hv]
    change A (regular_ensemble F) i j φ - B (regular_ensemble F) i j φ = 0
    rw [h,sub_self]
  rw [sub_eq_zero.mp same] at hu
  exact congrFun (hu.symm.trans hv) W

/-- The distribution can occupy any one of the three slots of the associator. -/
theorem theorem_distribution_bimodule_associativity (n : ℕ) (F G : S) (W : EnsembleDistribution) :
    let L := distribution_moyal_coefficient .generator_left
    let R := distribution_moyal_coefficient .generator_right
    let C := moyal_family
    (∑ k ∈ Finset.range (n+1), L (n-k) (C k F G) W) =
      (∑ k ∈ Finset.range (n+1), L (n-k) F (L k G W)) ∧
    (∑ k ∈ Finset.range (n+1), R (n-k) G (L k F W)) =
      (∑ k ∈ Finset.range (n+1), L (n-k) F (R k G W)) ∧
    (∑ k ∈ Finset.range (n+1), R (n-k) G (R k F W)) =
      (∑ k ∈ Finset.range (n+1), R (n-k) (C k F G) W) := by
  dsimp only
  have lift_eq (A B : ℕ → EnsembleDistribution → EnsembleDistribution)
      (ha : ∀ k, weak_action (A k)) (hb : ∀ k, weak_action (B k))
      (reg : ∀ X : S, (∑ k ∈ Finset.range (n+1), A k (regular_ensemble X)) =
        ∑ k ∈ Finset.range (n+1), B k (regular_ensemble X)) :
      (∑ k ∈ Finset.range (n+1), A k W) = ∑ k ∈ Finset.range (n+1), B k W :=
    congrFun (lemma_weak_action_ext (lemma_weak_action_sum _ A (fun k _ => ha k))
      (lemma_weak_action_sum _ B (fun k _ => hb k)) reg) W
  let L := distribution_moyal_coefficient .generator_left
  let R := distribution_moyal_coefficient .generator_right
  let C := moyal_family
  have lw (k : ℕ) (H : S) : weak_action (L k H) := lemma_moyal_action_is_weak _ _ _
  have rwk (k : ℕ) (H : S) : weak_action (R k H) := lemma_moyal_action_is_weak _ _ _
  have lr (k : ℕ) (H X : S) : L k H (regular_ensemble X) = regular_ensemble (C k H X) :=
    corollary_distribution_action_of_selected_product .generator_left .. 
  have rr (k : ℕ) (H X : S) : R k H (regular_ensemble X) = regular_ensemble (C k X H) :=
    corollary_distribution_action_of_selected_product .generator_right ..
  constructor
  · apply lift_eq (fun k => L (n-k) (C k F G)) (fun k w => L (n-k) F (L k G w))
      (fun k => lw _ _) (fun k => lemma_weak_action_comp (lw _ _) (lw _ _))
    intro X
    simpa only [lr,map_sum] using congrArg regular_ensemble (theorem_moyal_smooth_associativity n F G X)
  constructor
  · apply lift_eq (fun k w => R (n-k) G (L k F w)) (fun k w => L (n-k) F (R k G w))
      (fun k => lemma_weak_action_comp (rwk _ _) (lw _ _))
      (fun k => lemma_weak_action_comp (lw _ _) (rwk _ _))
    intro X
    simpa only [lr,rr,map_sum] using congrArg regular_ensemble (theorem_moyal_smooth_associativity n F X G)
  · apply lift_eq (fun k w => R (n-k) G (R k F w)) (fun k => R (n-k) (C k F G))
      (fun k => lemma_weak_action_comp (rwk _ _) (rwk _ _)) (fun k => rwk _ _)
    intro X
    simpa only [rr,map_sum] using congrArg regular_ensemble (theorem_moyal_smooth_associativity n X F G)
end
end MassShell.CompositionAndTransport

namespace MassShell.CompositionAndTransport
noncomputable section
open MeasureTheory
set_option maxHeartbeats 1000000
open scoped ContDiff
abbrev spacetime_measure := (Pi.basisFun ℝ (Fin 4)).addHaar
def monoenergetic_measure (p : Coordinates) : Measure PhasePoint :=
  spacetime_measure.prod (Measure.dirac p)

instance (p : Coordinates) : IsLocallyFiniteMeasure (monoenergetic_measure p) := by
  unfold monoenergetic_measure
  infer_instance

def plane_distribution (p : Coordinates) : ScalarDistribution :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℂ ℂ) (monoenergetic_measure p)
    (fun _ => 1)

theorem lemma_plane_test (p : Coordinates) (φ : PhaseTests) :
    plane_distribution p φ = ∫ x, φ (x,p) ∂spacetime_measure := by
  unfold plane_distribution
  rw [TestFunction.integralAgainstBilinCLM_eq_integral
    (continuous_const.continuousOn.locallyIntegrableOn (by simp))]
  change (∫ z, φ z * 1 ∂(spacetime_measure.prod (Measure.dirac p))) = _
  simp only [mul_one]
  rw [integral_prod _ (φ.contDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)]
  simp

theorem lemma_plane_weak_position_derivative (p : Coordinates) (j : Fin 4) :
    weak_derivative (.inl j) (plane_distribution p) = 0 := by
  ext φ
  rw [lemma_weak_derivative_on_test,lemma_plane_test]
  let f (x : Coordinates) := φ (x,p)
  have hf : ContDiff ℝ ∞ f := φ.contDiff.comp (contDiff_id.prodMk contDiff_const)
  have compact : HasCompactSupport f :=
    φ.hasCompactSupport.comp_isClosedEmbedding (.of_continuous_injective_isClosedMap (continuous_id.prodMk continuous_const)
      (fun _ _ h => congrArg Prod.fst h) (isClosedMap_prodMk_right p))
  let v : Coordinates := Pi.single j 1
  have chain (x : Coordinates) : fderiv ℝ f x v = fderiv ℝ φ (x,p) (direction (.inl j)) := by
    have d := (φ.contDiff.differentiable (by simp) (x,p)).hasFDerivAt.comp x
      ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (𝕜 := ℝ) p x))
    exact congrArg (fun L : Coordinates →L[ℝ] ℂ => L v) d.fderiv
  have ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := spacetime_measure)
    (f := fun _ : Coordinates => (1 : ℂ)) (g := f) (v := v)
    (by simp) (by
      simp only [one_mul]
      exact (((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
        ).integrable_of_hasCompactSupport (compact.fderiv_apply ℝ v))
    (by simpa using hf.continuous.integrable_of_hasCompactSupport compact)
    (fun _ _ => differentiableAt_const _) (fun x _ => hf.differentiable (by simp) x)
  simp only [one_mul,fderiv_const_apply,zero_apply,zero_mul,integral_zero,neg_zero] at ibp
  change - _ = 0
  rw [neg_eq_zero]
  convert ibp using 1
  apply integral_congr_ae
  filter_upwards with x
  exact (chain x).symm

def shell_ensemble (p : Coordinates) (ρ : SpinMatrix) : EnsembleDistribution :=
  Matrix.of fun r s => ρ r s • plane_distribution p

def spatially_constant (W : EnsembleDistribution) : Prop := ∀ j, distribution_directional (.inl j) W = 0

theorem lemma_weak_partials_commute (i j : Axis) (W : EnsembleDistribution) :
    distribution_directional i (distribution_directional j W) =
    distribution_directional j (distribution_directional i W) := by
  ext r s φ
  change -(-W r s _) = -(-W r s _)
  congr 3
  ext z
  let f := fun z => φ z
  have hf : ContDiff ℝ ∞ f := φ.contDiff
  have d := (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  change fderiv ℝ (fun y => fderiv ℝ f y (direction i)) z (direction j) =
    fderiv ℝ (fun y => fderiv ℝ f y (direction j)) z (direction i)
  simp only [fderiv_clm_apply d (differentiableAt_const _), fderiv_fun_const, Pi.zero_apply,
    ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply]
  exact hf.contDiffAt.isSymmSndFDerivAt (by simp) _ _

def momentum_only (F : S) : Prop := ∀ i, partial_map (.inl i) F = 0

theorem lemma_derivative_preserves_momentum_only {F : S} (h : momentum_only F) (i : Axis) :
    momentum_only (smooth_directional i F) := by
  intro j
  change partial_map (.inl j) (partial_map i F) = 0
  exact (DFunLike.congr_fun (lemma_partials_commute (.inl j) i).eq F).trans
    (by change partial_map i (partial_map (.inl j) F) = 0; rw [h,map_zero])

theorem lemma_weak_derivative_zero (i : Axis) : distribution_directional i 0 = 0 := by
  ext r s φ
  change -(0:ℂ) = 0
  simp

theorem lemma_derivative_preserves_spatial_constancy {W : EnsembleDistribution}
    (h : spatially_constant W) (i : Axis) : spatially_constant (distribution_directional i W) := by
  intro j
  rw [lemma_weak_partials_commute, h,lemma_weak_derivative_zero]

theorem lemma_mixed_word_zero (s : ProductSide) (w : List Variable) :
    (∀ W, mixed_word s w 0 W = 0) ∧ (∀ H, mixed_word s w H 0 = 0) := by
  induction w with
  | nil =>
    have z (i j : Fin 4) (φ : PhaseTests) : TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
        ((0:S).property i j) φ = (0:PhaseTests) := by ext x; change φ x * 0 = 0; simp
    constructor <;> intro F <;> ext i j φ <;> cases s <;>
      simp [mixed_word,mixed_multiplication,smooth_times_distribution,sum_apply]
    · apply Finset.sum_eq_zero; intro k _; exact (congrArg (F k j) (z i k φ)).trans (map_zero _)
    · apply Finset.sum_eq_zero; intro k _; exact (congrArg (F i k) (z k j φ)).trans (map_zero _)
  | cons v tail ih =>
    obtain ⟨slot,i⟩ := v
    have hz : smooth_directional i 0 = 0 := (partial_map i).map_zero
    cases s <;> cases slot <;> constructor <;> intro F <;>
      simp [mixed_word,hz,lemma_weak_derivative_zero,ih.1,ih.2]

theorem lemma_mixed_word_position_vanishes (s : ProductSide) (w : List Variable) (H : S)
    (W : EnsembleDistribution) (hH : momentum_only H) (hW : spatially_constant W)
    (slot : Slot) (j : Fin 4) (mem : (slot,Sum.inl j) ∈ w) : mixed_word s w H W = 0 := by
  induction w generalizing H W with
  | nil => simp at mem
  | cons v tail ih =>
    rcases List.mem_cons.mp mem with e | e
    · subst v
      have dz : smooth_directional (.inl j) H = 0 := hH j
      cases s <;> cases slot <;> simp [mixed_word,dz,hW j,(lemma_mixed_word_zero _ _).1,
        (lemma_mixed_word_zero _ _).2]
    · obtain ⟨a,i⟩ := v
      cases s <;> cases a <;> apply ih <;> first | exact hH | exact hW | exact e | exact lemma_derivative_preserves_momentum_only hH i | exact lemma_derivative_preserves_spatial_constancy hW i

def momentum_substitution : DifferentialSymbol →ₐ[ℂ] DifferentialSymbol :=
  MvPolynomial.aeval fun j => match j.2 with
    | .inl _ => 0 | .inr _ => MvPolynomial.X j

theorem lemma_positive_contraction_contains_position (n : ℕ) (d : Variable →₀ ℕ)
    (hd : d ∈ (canonical_symbol^(n+1)).coeff.support) :
    ∃ slot j, (slot,Sum.inl j) ∈ derivative_word d := by
  classical
  by_contra! absent
  have vanishes (slot : Slot) (j : Fin 4) : d (slot,Sum.inl j) = 0 := by
    by_contra ne
    apply absent slot j
    simp only [derivative_word,List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and]
    exact ⟨_, List.mem_replicate.mpr ⟨ne,rfl⟩⟩
  let proj := momentum_substitution
  have one_monomial (e : Variable →₀ ℕ) (c : ℂ) :
      (proj (MvPolynomial.monomial e c)).coeff d =
      (MvPolynomial.monomial e c : DifferentialSymbol).coeff d := by
    by_cases h : ∀ s j, e (s,Sum.inl j) = 0
    · have fixed : proj (MvPolynomial.monomial e c) = MvPolynomial.monomial e c := by
        rw [MvPolynomial.monomial_eq]
        simp only [proj,momentum_substitution,map_mul,MvPolynomial.aeval_C,Finsupp.prod,map_prod,map_pow,MvPolynomial.aeval_X]
        congr 1
        apply Finset.prod_congr rfl
        rintro ⟨s,i⟩ hi
        cases i with
        | inl j => simp [h s j]
        | inr j => rfl
      rw [fixed]
    · push Not at h
      obtain ⟨s,j,ne⟩ := h
      have diff : e ≠ d := fun eq => ne (eq ▸ vanishes s j)
      rw [MvPolynomial.coeff_monomial, ite_eq_right diff, MvPolynomial.monomial_eq]
      simp only [proj,momentum_substitution,map_mul,MvPolynomial.aeval_C,Finsupp.prod,map_prod,map_pow,MvPolynomial.aeval_X]
      rw [Finset.prod_eq_zero (i := (s,Sum.inl j)) (Finsupp.mem_support_iff.mpr ne)
        (show (0 : DifferentialSymbol) ^ e (s,Sum.inl j) = 0 from zero_pow ne), mul_zero,
        AddMonoidAlgebra.coeff_zero]
      rfl
  have same (P : DifferentialSymbol) : (proj P).coeff d = P.coeff d := by
    induction P using MvPolynomial.induction_on' with
    | monomial e c => exact one_monomial e c
    | add a b ha hb => simp [map_add,ha,hb]
  have erased : proj canonical_symbol = 0 := by simp [proj,momentum_substitution,canonical_symbol,contraction]
  have hz := same (canonical_symbol^(n+1))
  rw [map_pow,erased,zero_pow (by omega),AddMonoidAlgebra.coeff_zero] at hz
  exact Finsupp.mem_support_iff.mp hd hz.symm

theorem theorem_homogeneous_mixed_coefficients_vanish (side : ProductSide) (n : ℕ) (H : S)
    (W : EnsembleDistribution) (hH : momentum_only H) (hW : spatially_constant W) :
    distribution_moyal_coefficient side (n+1) H W = 0 := by
  unfold distribution_moyal_coefficient Finsupp.sum
  rw [Finset.sum_eq_zero,smul_zero]
  intro d hd
  obtain ⟨s,j,in_word⟩ := lemma_positive_contraction_contains_position n d hd
  dsimp only
  rw [lemma_mixed_word_position_vanishes side _ H W hH hW s j in_word]
  ext i j φ
  change _ * (0:ℂ) = 0
  exact mul_zero _
theorem lemma_distribution_order_zero (side : ProductSide) (H : S) (W : EnsembleDistribution) :
      distribution_moyal_coefficient side 0 H W = mixed_multiplication side H W := by
    unfold distribution_moyal_coefficient
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_smul]
    change (Finsupp.single 0 (1 : ℂ)).sum _ = _
    have empty_flat (xs : List Variable) : xs.flatMap (fun _ => ([] : List Variable)) = [] := by
      induction xs <;> simp_all
    rw [Finsupp.sum_single_index]
    · simp [derivative_word, empty_flat, mixed_word]
    · exact zero_smul ℂ (mixed_word side (derivative_word 0) H W)

def free_generator (b : ℝ) : S := by
  refine ⟨fun z => four_component_factor z.2 - b • 1, ?_⟩
  intro i j
  have component (k : Fin 4) : ContDiff ℝ ∞ (fun z : PhasePoint => (z.2 k : ℂ)) :=
    (coordinate_covector (.inr k)).contDiff
  fin_cases i <;> fin_cases j <;>
    simp [four_component_factor,four_component_pencil] <;> fun_prop (disch := exact component _)

theorem lemma_free_generator_momentum_only (b : ℝ) : momentum_only (free_generator b) := by
  intro j
  apply Subtype.ext
  funext z r s
  let f (p : Coordinates) := (four_component_factor p - b • 1) r s
  have hf : ContDiff ℝ ∞ f := by
    have component (k : Fin 4) : ContDiff ℝ ∞ (fun p : Coordinates => (p k : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) k)
    fin_cases r <;> fin_cases s <;> simp [f,four_component_factor,four_component_pencil] <;>
      fun_prop (disch := exact component _)
  change fderiv ℝ (f ∘ Prod.snd) z (direction (.inl j)) = 0
  rw [fderiv_comp _ (hf.differentiable (by simp) _) differentiableAt_snd, fderiv_snd]
  change (fderiv ℝ f z.2) 0 = 0
  exact map_zero _

theorem lemma_homogeneous_shell (p : Coordinates) (ρ : SpinMatrix) :
    spatially_constant (shell_ensemble p ρ) := by
  intro j
  ext r s φ
  have hz := DFunLike.congr_fun (lemma_plane_weak_position_derivative p j) φ
  change -(plane_distribution p) _ = 0 at hz
  change -(ρ r s * plane_distribution p _) = 0
  rw [neg_eq_zero.mp hz,mul_zero,neg_zero]

theorem lemma_generator_on_shell_ensemble (side : ProductSide) (b : ℝ) (p : Coordinates)
    (ρ : SpinMatrix) : mixed_multiplication side (free_generator b) (shell_ensemble p ρ) =
    shell_ensemble p (match side with
      | .generator_left => (four_component_factor p - b • 1) * ρ
      | .generator_right => ρ * (four_component_factor p - b • 1)) := by
  ext r s φ
  let h := four_component_factor p - b • 1
  have term (i j a c : Fin 4) :
      smooth_times_distribution ((free_generator b).property i j) (shell_ensemble p ρ a c) φ =
        (ρ a c * h i j) * plane_distribution p φ := by
    change ρ a c * plane_distribution p _ = _
    rw [lemma_plane_test,lemma_plane_test]
    change ρ a c * (∫ x, φ (x,p) * h i j ∂spacetime_measure) = _
    rw [integral_mul_const]
    ring
  cases side <;> simp only [mixed_multiplication, Matrix.of_apply,sum_apply,term] <;>
    change _ = (∑ k : Fin 4, _ * _) * plane_distribution p φ <;>
    rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem lemma_plane_distribution_nonzero (p : Coordinates) : plane_distribution p ≠ 0 := by
  let bump : ContDiffBump ((0:Coordinates),p) := ⟨1,2,by norm_num,by norm_num⟩
  let φ : PhaseTests := ⟨fun z => (bump z : ℂ), Complex.ofRealCLM.contDiff.comp bump.contDiff,
    bump.hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) rfl, Set.subset_univ _⟩
  have compact : HasCompactSupport (fun x : Coordinates => bump (x,p)) :=
    bump.hasCompactSupport.comp_isClosedEmbedding (.of_continuous_injective_isClosedMap
      (continuous_id.prodMk continuous_const) (fun _ _ e => congrArg Prod.fst e) (isClosedMap_prodMk_right p))
  have pos : 0 < ∫ x : Coordinates, bump (x,p) ∂spacetime_measure := by
    have cont : Continuous (fun x : Coordinates => bump (x,p)) :=
      bump.continuous.comp (continuous_id.prodMk continuous_const)
    have at_origin : bump ((0 : Coordinates),p) ≠ 0 := by
      rw [bump.eventuallyEq_one.eq_of_nhds]
      norm_num
    -- The support contains the origin and is open, so it has positive measure.
    apply (integral_pos_iff_support_of_nonneg (fun _ => bump.nonneg)
      (cont.integrable_of_hasCompactSupport compact)).2
    exact cont.isOpen_support.measure_pos spacetime_measure ⟨0, at_origin⟩
  intro hz
  have h := lemma_plane_test p φ
  rw [hz] at h
  change (0:ℂ) = ∫ x : Coordinates, (bump (x,p) : ℂ) ∂spacetime_measure at h
  rw [integral_complex_ofReal] at h
  exact pos.ne' (by exact_mod_cast h.symm)

theorem theorem_nonzero_free_shell_solution :
    ∃ W : EnsembleDistribution, W ≠ 0 ∧
      ∀ n side, distribution_moyal_coefficient side n (free_generator 1) W = 0 := by
  let p : Coordinates := Pi.single 0 1
  let ρ : SpinMatrix := 1 + four_component_factor p
  have nz : ρ 0 0 = 1 := by simp [ρ,p,four_component_factor,four_component_pencil]
  refine ⟨shell_ensemble p ρ, ?_, ?_⟩
  · intro hz
    have e := congrArg (fun M : EnsembleDistribution => M 0 0) hz
    change ρ 0 0 • plane_distribution p = 0 at e
    rw [nz,one_smul] at e
    exact lemma_plane_distribution_nonzero p e
  · intro n side
    cases n with
    | succ n =>
      exact theorem_homogeneous_mixed_coefficients_vanish side n _ _
        (lemma_free_generator_momentum_only 1) (lemma_homogeneous_shell p ρ)
    | zero =>
      have sq : four_component_factor p * four_component_factor p = 1 := by
        rw [theorem_four_components_are_sufficient]; norm_num [p,minkowski_pairing,Pi.single_apply]
      rw [lemma_distribution_order_zero,lemma_generator_on_shell_ensemble]
      have left_eq : (four_component_factor p - 1)*ρ = 0 := by
        simp [ρ,sub_mul,mul_add,sq]
      have right_eq : ρ*(four_component_factor p - 1) = 0 := by
        simp [ρ,mul_sub,add_mul,sq,add_comm]
      cases side <;> simp only [one_smul,left_eq,right_eq] <;> ext i j φ <;> simp [shell_ensemble]
end
end MassShell.CompositionAndTransport

namespace MassShell.Wigner
noncomputable section
open Real SchwartzMap LineDeriv
open scoped FourierTransform SchwartzMap
abbrev RelativeSpace := EuclideanSpace ℝ (Fin 4)
abbrev RelativeKernel := 𝓢(RelativeSpace, ℂ)

/-- Mathlib uses the positive Fourier kernel exp(2π i ⟨y,ξ⟩) for the inverse transform.
The paper's momentum coordinate is p = 2π ℏ ξ. -/
def relative_moment (v : RelativeSpace) (f : RelativeKernel) : RelativeKernel :=
  smulLeftCLM ℂ (inner ℝ · v) f

def momentum_derivative (v : RelativeSpace) (f : RelativeKernel) : RelativeKernel :=
  ((2 * (π : ℂ) * Complex.I)⁻¹) • ∂_{v} f

theorem lemma_relative_moment_transforms_to_derivative (v : RelativeSpace) (f : RelativeKernel) :
    𝓕⁻ (relative_moment v f) = momentum_derivative v (𝓕⁻ f) := by
  have nz : (2 * (π : ℂ) * Complex.I) ≠ 0 := by exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  unfold momentum_derivative relative_moment
  rw [lineDerivOp_fourierInv_eq, FourierTransform.fourierInv_smul, smul_smul, inv_mul_cancel₀ nz, one_smul]

/-- Directions may repeat and are kept in the order in which the factors act. -/
theorem theorem_relative_monomial_wigner_transform (directions : List RelativeSpace)
    (f : RelativeKernel) :
    𝓕⁻ (directions.foldr relative_moment f) =
      directions.foldr momentum_derivative (𝓕⁻ f) := by
  induction directions with
  | nil => rfl
  | cons v vs ih => simp only [List.foldr_cons, lemma_relative_moment_transforms_to_derivative, ih]

/-- Finite Taylor polynomials, including each individual coefficient of a formal
potential shift, transform exactly on Schwartz kernels. -/
theorem theorem_polynomial_potential_wigner_transform {N : ℕ} (coeff : Fin N → ℂ)
    (directions : Fin N → List RelativeSpace) (f : RelativeKernel) :
    𝓕⁻ (∑ k, coeff k • (directions k).foldr relative_moment f) =
      ∑ k, coeff k • (directions k).foldr momentum_derivative (𝓕⁻ f) := by
  simp [theorem_relative_monomial_wigner_transform]

theorem theorem_relative_derivative_wigner_transform (v : RelativeSpace) (f : RelativeKernel) :
    𝓕⁻ (∂_{v} f) = -(2 * (π : ℂ) * Complex.I) • relative_moment v (𝓕⁻ f) :=
  fourierInv_lineDerivOp_eq f v
end
end MassShell.Wigner

namespace MassShell.CompositionAndTransport
noncomputable section
open scoped TensorProduct ContDiff
open TensorProduct
set_option synthInstance.maxHeartbeats 350000
set_option maxHeartbeats 1500000

def dual_phase_map (T : RealPhaseCovector ≃ₗ[ℝ] RealPhaseCovector) : PhasePoint →L[ℝ] PhasePoint :=
  LinearMap.toContinuousLinearMap {
    toFun := phase_pullback T
    map_add' := by intro a b; ext i <;> simp [phase_pullback,phase_coordinate,mul_add,Finset.sum_add_distrib,Fintype.sum_sum_type] <;> abel
    map_smul' := by intro c a; ext i <;> simp [phase_pullback,phase_coordinate,Fintype.sum_sum_type,Finset.mul_sum,mul_left_comm,mul_add] }

def affine_field (L : PhasePoint →L[ℝ] PhasePoint) (t : PhasePoint) : S →ₗ[ℂ] S where
  toFun F := ⟨fun z => F.val (L z+t),fun i j => (F.property i j).comp (L.contDiff.add contDiff_const)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def transformed_variable (T : RealPhaseCovector ≃ₗ[ℝ] RealPhaseCovector) (v : Variable) : DifferentialSymbol :=
  ∑ j : Axis, MvPolynomial.C (T (Pi.single j 1) v.2 : ℂ) * MvPolynomial.X (v.1,j)

theorem lemma_transformed_moyal_polynomial (T : RealPhaseCovector ≃ₗ[ℝ] RealPhaseCovector)
    (preserves : ∀ u v, omega (T u) (T v) = omega u v) (n : ℕ) :
    MvPolynomial.aeval (transformed_variable T) (moyal_polynomial n) = moyal_polynomial n := by
  have ev (x y : RealPhaseCovector) (v : Variable) : MvPolynomial.eval (real_variables x y)
      (transformed_variable T v) = real_variables (T x) (T y) v := by
    have expansion (u : RealPhaseCovector) (i : Axis) : T u i = ∑ j, T (Pi.single j 1) i * u j := by
      calc
        T u i = T (∑ j, u j • Pi.single j 1) i := congrArg (fun w => T w i) (pi_eq_sum_univ' u)
        _ = _ := by simp [Finset.sum_apply,mul_comm]
    obtain ⟨s,i⟩ := v
    cases s <;> simp [transformed_variable, real_variables] <;> first | rw [expansion x i]; simp | rw [expansion y i]; simp
  apply lemma_real_symbol_ext
  intro x y
  change MvPolynomial.aeval (real_variables x y) _ = _
  rw [MvPolynomial.comp_aeval_apply]
  change MvPolynomial.eval (fun v => MvPolynomial.eval (real_variables x y) (transformed_variable T v)) _ = _
  simp only [ev]
  exact theorem_moyal_covariance n T preserves x y

theorem lemma_affine_chain_rule (T : RealPhaseCovector ≃ₗ[ℝ] RealPhaseCovector) (L : PhasePoint →L[ℝ] PhasePoint)
    (basis : ∀ i, L (direction i) = ∑ j, T (Pi.single j 1) i • direction j)
    (t : PhasePoint) (i : Axis) (F : S) :
    partial_map i (affine_field L t F) =
      affine_field L t (∑ j, (T (Pi.single j 1) i : ℂ) • partial_map j F) := by
  apply Subtype.ext
  funext z r s
  have h := ((F.property r s).differentiable (by simp) (L z+t)).hasFDerivAt.comp z
    (L.hasFDerivAt.add_const t)
  change fderiv ℝ (fun w => F.val (L w+t) r s) z (direction i) = _
  dsimp only [Function.comp_def] at h
  rw [h.fderiv]
  change fderiv ℝ (fun w => F.val w r s) (L z+t) (L (direction i)) = _
  rw [basis,map_sum]
  change _ = ((∑ j, (T (Pi.single j 1) i : ℂ) • partial_map j F : S) : Symbol) (L z+t) r s
  simp [partial_map,directional,Finset.sum_apply,Complex.real_smul,Matrix.sum_apply]

theorem lemma_affine_covariance (T : RealPhaseCovector ≃ₗ[ℝ] RealPhaseCovector)
    (preserves : ∀ u v, omega (T u) (T v) = omega u v) (L : PhasePoint →L[ℝ] PhasePoint)
    (basis : ∀ i, L (direction i) = ∑ j, T (Pi.single j 1) i • direction j)
    (t : PhasePoint) (n : ℕ) (F G : S) :
    moyal_family n (affine_field L t F) (affine_field L t G) = affine_field L t (moyal_family n F G) := by
  let P := affine_field L t
  let Q := TensorProduct.map P P
  let a := pair_calculus.comp (MvPolynomial.aeval (transformed_variable T))
  have step (v : Variable) (X : PairSpace) :
      Q (a (MvPolynomial.X v) X) = pair_calculus (MvPolynomial.X v) (Q X) := by
    obtain ⟨s,i⟩ := v
    induction X using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx,hy]
    | tmul f g =>
      cases s <;> simp [a,Q,P,transformed_variable,pair_calculus,pair_partial,
        lemma_affine_chain_rule T L basis,TensorProduct.add_tmul,TensorProduct.tmul_add,
        TensorProduct.sum_tmul,TensorProduct.tmul_sum, TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  have matched := lemma_polynomial_intertwining a pair_calculus Q step (moyal_polynomial n) (F ⊗ₜ[ℂ] G)
  simp only [a,AlgHom.comp_apply,lemma_transformed_moyal_polynomial T preserves] at matched
  have mult (X : PairSpace) : matrix_multiply (Q X) = P (matrix_multiply X) := by
    induction X using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx,hy]
    | tmul f g => rfl
  change matrix_multiply (pair_calculus _ (Q (F ⊗ₜ[ℂ] G))) = _
  rw [← matched,mult]
  rfl

theorem lemma_dual_phase_basis (T : RealPhaseCovector ≃ₗ[ℝ] RealPhaseCovector) (i : Axis) :
    dual_phase_map T (direction i) = ∑ j, T (Pi.single j 1) i • direction j := by
  change phase_pullback T (direction i) = _
  cases i <;> ext k <;>
    simp [phase_pullback,phase_coordinate,direction,Fintype.sum_sum_type,Finset.sum_apply,
      Pi.single_apply,apply_ite,Finset.sum_ite_eq',Prod.fst_sum,Prod.snd_sum]

theorem theorem_constructed_field_translation : ansatz_field_translation_invariance moyal_family := by
  intro n t F G Ft Gt hf hg z
  let I := LinearEquiv.refl ℝ RealPhaseCovector
  let L := ContinuousLinearMap.id ℝ PhasePoint
  have basis (i : Axis) : L (direction i) = ∑ j, I (Pi.single j 1) i • direction j := by
    simp [I,L,Pi.single_apply]
  have e := lemma_affine_covariance I (fun _ _ => rfl) L basis t n F G
  rw [show Ft = affine_field L t F from Subtype.ext (funext hf),
    show Gt = affine_field L t G from Subtype.ext (funext hg),e]
  rfl

theorem theorem_constructed_field_covariance : ansatz_field_symplectic_covariance moyal_family := by
  intro n T preserves F G Ft Gt hf hg z
  let L := dual_phase_map T
  have field_eq (H Ht : S) (h : ∀ z, Ht.val z = H.val (phase_pullback T z)) :
      Ht = affine_field L 0 H := by
    apply Subtype.ext
    funext p
    change Ht.val p = H.val (phase_pullback T p+0)
    rw [add_zero,h]
  rw [field_eq F Ft hf, field_eq G Gt hg,
    lemma_affine_covariance T preserves L (lemma_dual_phase_basis T) 0 n F G]
  change (moyal_family n F G).val (phase_pullback T z+0) = _
  rw [add_zero]

/-- One tensor contraction chooses the derivative slot attached to each end of P.
Repeated ends are permitted. Antisymmetry makes their contribution vanish. -/
def contraction_word : List (Slot × Slot) → DifferentialSymbol
  | [] => 1
  | (s,t) :: rest => contraction s t * contraction_word rest

/-- A17 in differential-symbol coordinates, with dimensionless complex weights.
The two ends of every available Poisson tensor must be attached to derivative
slots. A term at order n has action exponent n*d minus its number of tensors.
The first-order canonical response supplies the reference unit of action. -/
def ansatz_dimensionally_balanced_symbol (n : ℕ) (p : DifferentialSymbol) : Prop :=
  ∃ (d : ℤ) (count : ℕ) (weight : Fin count → ℂ) (word : Fin count → List (Slot × Slot)),
    1*d-1=0 ∧ (∀ j, (n : ℤ)*d - ((word j).length : ℤ)=0) ∧
      p = ∑ j, MvPolynomial.C (weight j) * contraction_word (word j)

/-- Each surviving contraction is linear in the second covector. This follows
by exchanging the antisymmetric tensor indices, even for same-slot contractions. -/
theorem lemma_single_contraction_scales (s t : Slot) (r : ℝ) (x y : RealPhaseCovector) :
    symbol_value (contraction s t) x (r • y) = (r : ℂ) * symbol_value (contraction s t) x y := by
  cases s <;> cases t <;>
    simp [symbol_value,contraction,real_variables,Finset.mul_sum,mul_sub,mul_left_comm,mul_comm,mul_assoc]

/-- Apply the single-tensor scaling law once for every tensor in a contraction diagram. -/
theorem lemma_contraction_word_scales (word : List (Slot × Slot)) (r : ℝ) (x y : RealPhaseCovector) :
    symbol_value (contraction_word word) x (r • y) =
      (r : ℂ)^word.length * symbol_value (contraction_word word) x y := by
  induction word with
  | nil => simp [contraction_word,symbol_value]
  | cons edge tail ih =>
    rcases edge with ⟨s,t⟩
    simp only [contraction_word,symbol_value,map_mul,List.length_cons,pow_succ]
    change symbol_value (contraction s t) x (r • y) * symbol_value (contraction_word tail) x (r • y) = _
    rw [lemma_single_contraction_scales,ih]
    unfold symbol_value
    ring

/-- A17 and dimensional balance imply A18 for the actual polynomial entering the
selection theorem. The integer count fixes each summand's degree; the sum then scales. -/
theorem theorem_dimensional_balance_implies_symbol_grading (n : ℕ) (p : DifferentialSymbol)
    (admissible : ansatz_dimensionally_balanced_symbol n p) : ansatz_order_homogeneity n p := by
  obtain ⟨d,N,w,word,first,balanced,rfl⟩ := admissible
  have hd : d=1 := by omega
  have degree (j : Fin N) : (word j).length = n := by
    have h := balanced j
    rw [hd,mul_one] at h
    omega
  intro r x y
  simp only [symbol_value,map_sum,map_mul,MvPolynomial.eval_C,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change w j * symbol_value (contraction_word (word j)) x (r • y) = _
  rw [lemma_contraction_word_scales,degree]
  unfold symbol_value
  ring

/-- The constructed product has one diagram with n canonical cross-contractions.
This provides a witness for A17 on the existence side as well as the selection side. -/
theorem theorem_moyal_symbol_dimensionally_balanced (n : ℕ) :
    ansatz_dimensionally_balanced_symbol n (moyal_polynomial n) := by
  let edge : Slot × Slot := (.left,.right)
  have repeated (k : ℕ) : contraction_word (List.replicate k edge) = canonical_symbol^k := by
    induction k with
    | zero => simp [contraction_word]
    | succ k ih => simp only [List.replicate_succ,edge,contraction_word,pow_succ']; exact congrArg _ ih
  refine ⟨1,1,fun _ => moyal_weight n,fun _ => List.replicate n edge,by decide,?_,?_⟩
  · intro j; simp
  · simp [repeated,moyal_polynomial]

/-- The field-product assumptions used in the existence and uniqueness theorem. -/
def ansatz_field_product_requirements (metric : SpinMatrix) (C : CoefficientFamily) : Prop :=
  (∃ p, ansatz_local_differential_coordinates C p ∧
    ∀ n, ansatz_dimensionally_balanced_symbol n (p n 0)) ∧ ansatz_field_translation_invariance C ∧
  ansatz_field_symplectic_covariance C ∧ ansatz_matrix_associativity C ∧
  ansatz_constant_matrix_neutrality C ∧ (∀ F G, C 0 F G = F*G) ∧
  ansatz_dirac_adjoint_compatibility metric C ∧ ansatz_oriented_weyl_scale C

theorem theorem_exists_unique_product_from_field_ansatze (metric : SpinMatrix) (sq : metric*metric=1) :
    ∃! C : CoefficientFamily, ansatz_field_product_requirements metric C := by
  have old := theorem_moyal_admissible
  refine ⟨moyal_family, ⟨⟨fun n _ => moyal_polynomial n,old.1,theorem_moyal_symbol_dimensionally_balanced⟩,
    theorem_constructed_field_translation,theorem_constructed_field_covariance,
    theorem_moyal_smooth_associativity,theorem_moyal_neutrality,old.2.2.2.2.2.1,
    theorem_constructed_dirac_adjoint metric sq,?_⟩,?_⟩
  · unfold ansatz_oriented_weyl_scale
    rw [lemma_canonical_test_response moyal_family moyal_weight (fun n F G => lemma_family_agrees n F G)]
    norm_num [moyal_weight,Complex.div_ofNat_im]
  · rintro C ⟨⟨p,loc,balanced⟩,trans,cov,assoc,neutral,cl,adj,scale⟩
    have selected := theorem_selection_from_field_ansatze C p loc trans cov
      (fun n => theorem_dimensional_balance_implies_symbol_grading n _ (balanced n)) assoc neutral cl metric sq adj scale
    funext n
    apply LinearMap.ext
    intro F
    apply LinearMap.ext
    intro G
    exact Subtype.ext ((selected n F G).trans (lemma_family_agrees n F G).symm)
end
end MassShell.CompositionAndTransport

namespace MassShell.Wigner
noncomputable section
open Real SchwartzMap LineDeriv
open scoped FourierTransform SchwartzMap ContDiff Topology

/-- The real sign distinguishes the left (+1) and right (−1) endpoints.
After the adjoint equation the relative derivative has the same sign on both sides. -/
def endpoint_kinetic (sign hbar speed : ℝ) (v : RelativeSpace)
    (density centreDerivative : RelativeKernel) : RelativeKernel :=
  (Complex.I * hbar * speed) • (∂_{v} density) +
    (sign * Complex.I * hbar * speed / 2) • centreDerivative

def wigner_kinetic (sign hbar speed : ℝ) (v : RelativeSpace)
    (density centreDerivative : RelativeKernel) : RelativeKernel :=
  (2 * (π : ℂ) * hbar * speed) • relative_moment v density +
    (sign * Complex.I * hbar * speed / 2) • centreDerivative

theorem lemma_kinetic_bopp_shift (sign hbar speed : ℝ) (v : RelativeSpace)
    (f d : RelativeKernel) : 𝓕⁻ (endpoint_kinetic sign hbar speed v f d) =
      wigner_kinetic sign hbar speed v (𝓕⁻ f) (𝓕⁻ d) := by
  simp only [endpoint_kinetic,wigner_kinetic,FourierTransform.fourierInv_add,
    FourierTransform.fourierInv_smul,theorem_relative_derivative_wigner_transform,smul_smul]
  congr 2
  ring_nf
  simp

def shifted_potential (A : RelativeSpace → ℂ) (X : RelativeSpace) (sign : ℝ) :
    RelativeSpace → ℂ := fun y => A (X + (sign / 2) • y)

/-- The exact fixed-gauge potential acts on a Wigner function by Fourier conjugation
of multiplication at the corresponding endpoint. -/
def fixed_gauge_potential (A : RelativeSpace → ℂ) (X : RelativeSpace) (sign : ℝ)
    (W : RelativeKernel) : RelativeKernel :=
  𝓕⁻ (smulLeftCLM ℂ (shifted_potential A X sign) (𝓕 W))

theorem lemma_fixed_gauge_potential_kernel (A : RelativeSpace → ℂ) (X : RelativeSpace)
    (sign : ℝ) (growth : (shifted_potential A X sign).HasTemperateGrowth)
    (W : RelativeKernel) (y : RelativeSpace) :
    (𝓕 (fixed_gauge_potential A X sign W)) y = A (X+(sign/2) • y) * (𝓕 W) y := by
  simp [fixed_gauge_potential,smulLeftCLM_apply_apply growth,shifted_potential]

/-- The centre derivative commutes with the transform for a differentiable
Schwartz-valued family. The relative and centre coordinates remain independent. -/
theorem lemma_centre_derivative_wigner (f : RelativeSpace → RelativeKernel) (X v : RelativeSpace)
    (smooth : DifferentiableAt ℝ f X) :
    fderiv ℝ (fun x => 𝓕⁻ (f x)) X v = 𝓕⁻ (fderiv ℝ f X v) := by
  let L : RelativeKernel →L[ℝ] RelativeKernel := FourierTransform.fourierInvCLM ℝ RelativeKernel
  have chain : HasFDerivAt (L ∘ f) (L.comp (fderiv ℝ f X)) X :=
    .of_isLittleOTVS <| by
      simpa [Function.comp_def] using L.isBigOTVS_comp.trans_isLittleOTVS smooth.hasFDerivAt.isLittleOTVS
  change (fderiv ℝ (L ∘ f) X) v = (L.comp (fderiv ℝ f X)) v
  rw [chain.fderiv]

/-- A row of the left Dirac density equation or a column of the right equation.
The index k can enumerate the Lorentz and contracted spin indices together.
The coefficients gamma carry the corresponding ordered matrix entries. -/
theorem theorem_fixed_gauge_dirac_density_equation {N : ℕ} (sign hbar speed charge massEnergy : ℝ)
    (X : RelativeSpace) (v : Fin N → RelativeSpace) (gamma : Fin N → ℂ)
    (A : Fin N → RelativeSpace → ℂ) (f : Fin N → RelativeSpace → RelativeKernel)
    (entry : RelativeKernel) (regular : ∀ k, DifferentiableAt ℝ (f k) X)
    (growth : ∀ k, (shifted_potential (A k) X sign).HasTemperateGrowth)
    (dirac_at_endpoints : ∀ y, (∑ k, gamma k *
      ((endpoint_kinetic sign hbar speed (v k) (f k X) (fderiv ℝ (f k) X (v k))) y -
        charge * A k (X+(sign/2) • y) * (f k X) y)) - massEnergy * entry y = 0) :
    (∑ k, gamma k • (wigner_kinetic sign hbar speed (v k) (𝓕⁻ (f k X))
      (fderiv ℝ (fun x => 𝓕⁻ (f k x)) X (v k)) -
      (charge : ℂ) • fixed_gauge_potential (A k) X sign (𝓕⁻ (f k X)))) -
      (massEnergy : ℂ) • (𝓕⁻ entry) = 0 := by
  have kernel : (∑ k, gamma k • (endpoint_kinetic sign hbar speed (v k) (f k X)
      (fderiv ℝ (f k) X (v k)) - (charge : ℂ) •
      smulLeftCLM ℂ (shifted_potential (A k) X sign) (f k X))) -
      (massEnergy : ℂ) • entry = 0 := by
    ext y
    simpa [smulLeftCLM_apply_apply (growth _),shifted_potential, mul_assoc] using dirac_at_endpoints y
  let inverseFourier := FourierTransform.fourierInvCLM ℂ RelativeKernel
  have transformed := congrArg inverseFourier kernel
  simp only [map_sub, map_sum, map_smul, map_zero] at transformed
  simp only [inverseFourier, FourierTransform.fourierInvCLM_apply] at transformed
  simpa [fixed_gauge_potential, lemma_centre_derivative_wigner _ _ _ (regular _),
    lemma_kinetic_bopp_shift] using transformed

/-- Smooth potentials with identical derivatives of all orders at the centre can differ
at an endpoint. A finite-ℏ potential therefore requires an exact Weyl action or a
separate convergence result for the chosen potential class. -/
theorem theorem_smooth_jet_does_not_determine_endpoint :
    ∃ f g : ℝ → ℝ, ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧
      (∀ n, iteratedFDeriv ℝ n f 0 = iteratedFDeriv ℝ n g 0) ∧ f 1 ≠ g 1 := by
  let bump : ContDiffBump (1 : ℝ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  have near : (bump : ℝ → ℝ) =ᶠ[𝓝 0] (fun _ => 0) := by
    filter_upwards [gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)] with x hx
    apply bump.zero_of_le_dist
    change 1/2 ≤ dist x 1
    rw [Real.dist_eq,abs_of_nonpos (by linarith : x-1 ≤ 0)]
    linarith
  refine ⟨bump,fun _ => 0,bump.contDiff,contDiff_const,fun n =>
    (near.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds,?_⟩
  rw [bump.eventuallyEq_one.eq_of_nhds]
  norm_num
end
end MassShell.Wigner

namespace MassShell
noncomputable section
open Matrix
/-- The entire rest eigenspace consists of the two-component vectors (u, sign u). -/
theorem theorem_rest_sector_exhausted (sign : ℂ) (w : Fin 4 → ℂ)
    (sector : (gamma_axis 0).mulVec w = sign • w) :
    ∃! u : Fin 2 → ℂ, sector_embedding sign u = w := by
  have row (i : Fin 4) := congrFun sector i
  have e₂ := row 0
  have e₃ := row 1
  simp [gamma_axis,four_component_factor,four_component_pencil,Matrix.mulVec,dotProduct,
    Fin.sum_univ_four] at e₂ e₃
  let u : Fin 2 → ℂ := ![w 0,w 1]
  have describes : sector_embedding sign u = w := by
    funext i
    fin_cases i <;> simp [u,sector_embedding,e₂,e₃]
  exact ⟨u,describes,fun other ho => lemma_sector_embedding_injective sign (ho.trans describes.symm)⟩

/-- The block action is multiplicative, so its restriction to SU(2) acts on both sectors. -/
def rest_block_representation : PauliMatrix →* FourByFour where
  toFun := block_spin
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp [block_spin]
  map_mul' A B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [block_spin, Matrix.mul_apply,Fin.sum_univ_four,Fin.sum_univ_two]

theorem theorem_rest_rotation_action (U : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (sign : ℂ) (u : Fin 2 → ℂ) :
    (rest_block_representation U.val).mulVec (sector_embedding sign u) =
      sector_embedding sign (U.val.mulVec u) := by
  funext i
  fin_cases i <;> simp [rest_block_representation, block_spin,sector_embedding, Matrix.mulVec,
    dotProduct, Fin.sum_univ_four,Fin.sum_univ_two] <;> ring
end
end MassShell

namespace MassShell.CompositionAndTransport
noncomputable section
open MeasureTheory
open scoped ContDiff

/-- An ambient distribution obtained by integrating a matrix density against a
locally finite shell measure. This also allows measures carried on one sheet. -/
def measured_ensemble (μ : Measure PhasePoint) (W : S) : EnsembleDistribution :=
  Matrix.of fun r s => TestFunction.integralAgainstBilinCLM
    (ContinuousLinearMap.mul ℂ ℂ) μ (fun z => W.val z r s)

theorem lemma_measured_evaluation (μ : Measure PhasePoint) [IsLocallyFiniteMeasure μ]
    (W : S) (r s : Fin 4) (φ : PhaseTests) :
    measured_ensemble μ W r s φ = ∫ z, φ z * W.val z r s ∂μ := by
  apply TestFunction.integralAgainstBilinCLM_eq_integral
  exact (W.property r s).continuous.continuousOn.locallyIntegrableOn (by simp)

theorem theorem_measured_shell_constraints (μ : Measure PhasePoint) [IsLocallyFiniteMeasure μ]
    (H W : S) (left : ∀ᵐ z ∂μ, H.val z * W.val z = 0)
    (right : ∀ᵐ z ∂μ, W.val z * H.val z = 0) (side : ProductSide) :
    distribution_moyal_coefficient side 0 H (measured_ensemble μ W) = 0 := by
  rw [lemma_distribution_order_zero]
  ext r s φ
  have term (i j a b : Fin 4) :
      smooth_times_distribution (H.property i j) (measured_ensemble μ W a b) φ =
      ∫ z, φ z * H.val z i j * W.val z a b ∂μ :=
    lemma_measured_evaluation μ W a b _
  have integ (i j a b : Fin 4) : Integrable (fun z => φ z * H.val z i j * W.val z a b) μ :=
    ((φ.contDiff.continuous.mul (H.property i j).continuous).mul (W.property a b).continuous
      ).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right.mul_right
  cases side <;> simp only [mixed_multiplication,Matrix.of_apply,sum_apply,term] <;>
    rw [← integral_finsetSum _ (fun _ _ => integ ..)] <;> apply integral_eq_zero_of_ae
  · filter_upwards [left] with z hz
    have e := congrArg (fun M : SpinMatrix => φ z * M r s) hz
    simpa [Matrix.mul_apply,Finset.mul_sum,mul_assoc] using e
  · filter_upwards [right] with z hz
    have e := congrArg (fun M : SpinMatrix => φ z * M r s) hz
    simpa [Matrix.mul_apply,Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm] using e

/-- Eq. (86) for any locally finite measure carried by the chosen mass shell.
Only the values of the smooth extensions on that shell enter the constraints. -/
theorem theorem_projected_density_on_measured_shell (μ : Measure PhasePoint) [IsLocallyFiniteMeasure μ]
    (factor : FourMomentum →ₗ[ℝ] SpinMatrix) (square : ansatz_reproduces_minkowski_square factor)
    (momentum : PhasePoint → FourMomentum) (b : ℝ) (hb : 0 < b) (density : PhasePoint → SpinMatrix)
    (H W : S) (shell : ∀ᵐ z ∂μ, minkowski_pairing (momentum z) (momentum z) = b^2)
    (generator : ∀ᵐ z ∂μ, H.val z = factor (momentum z) - b • 1)
    (selected : ∀ᵐ z ∂μ, W.val z = let P := selected_projector (b⁻¹ • factor (momentum z))
      P * density z * P) (side : ProductSide) :
    distribution_moyal_coefficient side 0 H (measured_ensemble μ W) = 0 := by
  have both : ∀ᵐ z ∂μ, H.val z * W.val z = 0 ∧ W.val z * H.val z = 0 := by
    filter_upwards [shell,generator,selected] with z on_shell h w
    let J := b⁻¹ • factor (momentum z)
    have invol := lemma_on_shell_normalisation factor square (momentum z) b hb.ne' on_shell
    have vanish := theorem_projected_distribution_satisfies_both_constraints J (density z) invol
    have gen : H.val z = b • (J-1) := by
      rw [h,smul_sub,smul_smul,mul_inv_cancel₀ hb.ne',one_smul]
    rw [gen,w]
    exact ⟨by rw [smul_mul_assoc,vanish.1,smul_zero],by rw [mul_smul_comm,vanish.2,smul_zero]⟩
  exact theorem_measured_shell_constraints μ H W (both.mono fun _ e => e.1)
    (both.mono fun _ e => e.2) side
end
end MassShell.CompositionAndTransport

namespace MassShell.Wigner
noncomputable section
open SchwartzMap LineDeriv
open scoped FourierTransform SchwartzMap

def endpoint_position (X y : RelativeSpace) (s : ℝ) := X + (s/2) • y

/-- Differentiating the spinor outer product at one endpoint cancels the derivative
of the spectator spinor. At the right endpoint a and b exchange roles entrywise. -/
theorem lemma_spinor_density_endpoint_derivative (a b : RelativeSpace → ℂ)
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) (s : ℝ) (X y v : RelativeSpace) :
    let density := fun x z => a (endpoint_position x z s) * b (endpoint_position x z (-s))
    fderiv ℝ (density X) y v + (s/2 : ℝ) • fderiv ℝ (fun x => density x y) X v =
      s • (fderiv ℝ a (endpoint_position X y s) v * b (endpoint_position X y (-s))) := by
  dsimp only
  have centre (g : RelativeSpace → ℂ) (hg : Differentiable ℝ g) (t : ℝ) :=
    (hg (endpoint_position X y t)).hasFDerivAt.comp X ((hasFDerivAt_id (𝕜 := ℝ) X).add_const ((t/2) • y))
  have relative (g : RelativeSpace → ℂ) (hg : Differentiable ℝ g) (t : ℝ) :=
    (hg (endpoint_position X y t)).hasFDerivAt.comp y (((hasFDerivAt_id (𝕜 := ℝ) y).const_smul (t/2)).const_add X)
  have cx := ((centre a ha s).mul (centre b hb (-s))).fderiv
  have ry := ((relative a ha s).mul (relative b hb (-s))).fderiv
  simp only [Function.comp_def,Pi.mul_def,Pi.smul_def,id_eq] at cx ry
  unfold endpoint_position
  rw [cx,ry]
  simp [Complex.real_smul,endpoint_position]
  ring

theorem lemma_centre_derivative_evaluation (f : RelativeSpace → RelativeKernel)
    (hf : DifferentiableAt ℝ f X) (y v : RelativeSpace) :
    (fderiv ℝ f X v) y = fderiv ℝ (fun x => f x y) X v := by
  let L : RelativeKernel →L[ℝ] ℂ := (BoundedContinuousFunction.evalCLM ℝ y).comp
    (toBoundedContinuousFunctionCLM ℝ RelativeSpace ℂ)
  have chain : HasFDerivAt (L ∘ f) (L.comp (fderiv ℝ f X)) X :=
    .of_isLittleOTVS <| by
      simpa [Function.comp_def] using L.isBigOTVS_comp.trans_isLittleOTVS hf.hasFDerivAt.isLittleOTVS
  exact (congrArg (fun h : RelativeSpace →L[ℝ] ℂ => h v) chain.fderiv).symm

theorem lemma_kinetic_on_spinor_density (a b : RelativeSpace → ℂ)
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) (s h c : ℝ) (X y v : RelativeSpace)
    (f : RelativeSpace → RelativeKernel) (hf : DifferentiableAt ℝ f X)
    (density : ∀ x z, f x z = a (endpoint_position x z s) * b (endpoint_position x z (-s))) :
    endpoint_kinetic s h c v (f X) (fderiv ℝ f X v) y =
      (s * Complex.I * h * c) * fderiv ℝ a (endpoint_position X y s) v * b (endpoint_position X y (-s)) := by
  have identity := lemma_spinor_density_endpoint_derivative a b ha hb s X y v
  have center := lemma_centre_derivative_evaluation f hf y v
  have ry : ((f X) : RelativeSpace → ℂ) = _ := funext (density X)
  simp only [endpoint_kinetic,add_apply,smul_apply,smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,center,ry]
  simp_rw [density]
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_ofNat] at identity
  linear_combination (Complex.I * (h : ℂ) * c) * identity

/-- Section 4 for each spinor-matrix entry. With s=1 the active spinor is ψ and
the spectator is an entry of its Dirac adjoint. With s=−1 the adjoint is active.
The input equation is the minimally coupled amplitude equation for that row or column. -/
theorem theorem_wigner_equation_from_spinor_amplitude {N : ℕ} (s h c q m : ℝ)
    (X : RelativeSpace) (v : Fin N → RelativeSpace) (gamma : Fin N → ℂ)
    (A a : Fin N → RelativeSpace → ℂ) (a₀ b : RelativeSpace → ℂ)
    (ha : ∀ k, Differentiable ℝ (a k)) (hb : Differentiable ℝ b)
    (f : Fin N → RelativeSpace → RelativeKernel) (entry : RelativeKernel)
    (regular : ∀ k, DifferentiableAt ℝ (f k) X)
    (density : ∀ k x z, f k x z = a k (endpoint_position x z s) * b (endpoint_position x z (-s)))
    (mass_entry : ∀ y, entry y = a₀ (endpoint_position X y s) * b (endpoint_position X y (-s)))
    (growth : ∀ k, (shifted_potential (A k) X s).HasTemperateGrowth)
    (amplitude_equation : ∀ x, (∑ k, gamma k * ((s * Complex.I * h * c) * fderiv ℝ (a k) x (v k)
      - q * A k x * a k x)) - m * a₀ x = 0) :
    (∑ k, gamma k • (wigner_kinetic s h c (v k) (𝓕⁻ (f k X))
      (fderiv ℝ (fun x => 𝓕⁻ (f k x)) X (v k)) -
      (q : ℂ) • fixed_gauge_potential (A k) X s (𝓕⁻ (f k X)))) -
      (m : ℂ) • (𝓕⁻ entry) = 0 := by
  apply theorem_fixed_gauge_dirac_density_equation s h c q m X v gamma A f entry regular growth
  intro y
  have term (k : Fin N) := lemma_kinetic_on_spinor_density (a k) b (ha k) hb s h c X y
    (v k) (f k) (regular k) (density k)
  simp only [term,density,mass_entry]
  change (∑ k, gamma k * (_ - q * A k (endpoint_position X y s) * _)) - _ = _
  have zero := congrArg (fun z : ℂ => z * b (endpoint_position X y (-s)))
    (amplitude_equation (endpoint_position X y s))
  simpa [sub_mul,Finset.sum_mul,mul_assoc,mul_sub] using zero
end
end MassShell.Wigner

namespace MassShell.Wigner
noncomputable section
open SchwartzMap Real
open scoped FourierTransform SchwartzMap

def coordinate_monomial (directions : List RelativeSpace) (y : RelativeSpace) : ℂ :=
  (directions.map fun v => (inner ℝ y v : ℂ)).prod

theorem lemma_relative_monomial_value (directions : List RelativeSpace)
    (f : RelativeKernel) (y : RelativeSpace) :
    directions.foldr relative_moment f y = coordinate_monomial directions y * f y := by
  induction directions with
  | nil => simp [coordinate_monomial]
  | cons v vs ih =>
    have growth : (inner ℝ · v).HasTemperateGrowth := ((innerSL ℝ).flip v).hasTemperateGrowth
    simp [relative_moment,smulLeftCLM_apply_apply growth,coordinate_monomial,ih,Complex.real_smul,mul_assoc]

/-- If the shifted potential has a finite polynomial expansion in the relative
coordinate, the exact fixed-gauge operator equals the finite differential operator. -/
theorem theorem_fixed_potential_equals_finite_derivative_expansion {N : ℕ}
    (A : RelativeSpace → ℂ) (X : RelativeSpace) (s : ℝ) (coeff : Fin N → ℂ)
    (terms : Fin N → List RelativeSpace) (growth : (shifted_potential A X s).HasTemperateGrowth)
    (expansion : ∀ y, shifted_potential A X s y = ∑ k, coeff k * coordinate_monomial (terms k) y)
    (W : RelativeKernel) :
    fixed_gauge_potential A X s W = ∑ k, coeff k • (terms k).foldr momentum_derivative W := by
  have polynomial : smulLeftCLM ℂ (shifted_potential A X s) (𝓕 W) =
      ∑ k, coeff k • (terms k).foldr relative_moment (𝓕 W) := by
    ext y
    simp [smulLeftCLM_apply_apply growth,expansion,lemma_relative_monomial_value,Finset.sum_mul,mul_assoc]
  unfold fixed_gauge_potential
  rw [polynomial,theorem_polynomial_potential_wigner_transform]
  simp
end
end MassShell.Wigner

namespace MassShell.CompositionAndTransport
noncomputable section
/-- The Section 5 chain, with field symmetries and the Dirac adjoint among the
product hypotheses. The first-order complex matching identity is derived. -/
theorem theorem_minimal_argument_from_field_ansatze
    (factor : FourMomentum →ₗ[ℝ] SpinMatrix)
    (ansatz_square_identity : ansatz_reproduces_minkowski_square factor)
    (κ : PhasePoint → FourMomentum) (b : ℝ) (mass_positive : 0 < b)
    (z : PhasePoint) (on_shell : minkowski_pairing (κ z) (κ z) = b ^ 2)
    (Hₛ : SmoothMatrixSymbol) (ansatz_generator : ∀ y, (Hₛ : Symbol) y = factor (κ y) - b • 1)
    (Wₛ : ℕ → SmoothMatrixSymbol) (density : SpinMatrix)
    (metric : SpinMatrix) (metric_square : metric * metric = 1)
    (C : CoefficientFamily) (product_assumptions : ansatz_field_product_requirements metric C) :
    let W := fun n => (Wₛ n : Symbol)
    let J := b⁻¹ • factor (κ z)
    let P := selected_projector J
    let H : Symbol := Hₛ
    let B := (Complex.I • weyl_transport H (W 0)) z
    ansatz_selected_leading_density (W 0 z) P density →
    ansatz_all_order_preservation C Hₛ Wₛ →
    ansatz_continues_left_zero_sector C Hₛ Wₛ →
      Module.finrank ℂ (LinearMap.range (Matrix.toLinAlgEquiv' P)) = 2 ∧
      (H z * W 0 z = 0 ∧ W 0 z * H z = 0) ∧
      (∀ n (F G : SmoothMatrixSymbol), (C n F G : Symbol) = moyal_coefficient n F G) ∧
      (J * B * J = -B ∧ b • (W 1 z - J * W 1 z * J) = -(J * B)) ∧
      (∀ n, (∑ r ∈ Finset.range (n+1), moyal_coefficient r H (W (n-r))) = 0 ∧
        (∑ r ∈ Finset.range (n+1), moyal_coefficient r (W (n-r)) H) = 0) := by
  obtain ⟨⟨p,locality,balanced⟩,translations,covariance,assoc,neutral,cl,adjoint,scale⟩ :=
    product_assumptions
  have selected := theorem_selection_from_field_ansatze C p locality translations covariance
    (fun n => theorem_dimensional_balance_implies_symbol_grading n _ (balanced n))
    assoc neutral cl metric metric_square adjoint scale
  have family_eq : C = moyal_family := by
    funext n
    ext F G : 2
    exact Subtype.ext ((selected n F G).trans (lemma_family_agrees n F G).symm)
  subst C
  exact corollary_transport_for_the_constructed_product factor ansatz_square_identity κ b
    mass_positive z on_shell Hₛ ansatz_generator Wₛ density
end
end MassShell.CompositionAndTransport

namespace MassShell.CompositionAndTransport
noncomputable section
/-- Use the time generator of the actual four-component pencil as the Dirac metric. -/
theorem lemma_time_gamma_is_dirac_metric : (gamma_axis 0).conjTranspose = gamma_axis 0 ∧
    gamma_axis 0 * gamma_axis 0 = 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [gamma_axis,four_component_factor,four_component_pencil]
  · exact (show four_component_factor (Pi.single 0 1) * four_component_factor (Pi.single 0 1) = 1 by
      rw [theorem_four_components_are_sufficient]
      norm_num [minkowski_pairing, Pi.single_apply])

theorem corollary_unique_product_for_dirac_metric :
    ∃! C : CoefficientFamily, ansatz_field_product_requirements (gamma_axis 0) C :=
  theorem_exists_unique_product_from_field_ansatze _ lemma_time_gamma_is_dirac_metric.2

/-- In Eq. (66) each Poisson contraction removes one power of action. With
dimensionless coefficients the net power in λⁿPᵏ is n*d−k, where d is the
action exponent of λ. First-order matching includes one contraction. -/
def ansatz_dimensional_balance (action_exponent : ℤ) (order contractions : ℕ) : Prop :=
  (order : ℤ) * action_exponent - (contractions : ℤ) = 0

theorem theorem_dimension_of_parameter_and_contraction_count (action_exponent : ℤ)
    (first_order : ansatz_dimensional_balance action_exponent 1 1) :
    action_exponent = 1 ∧ ∀ n k, ansatz_dimensional_balance action_exponent n k → k = n := by
  have units : action_exponent = 1 := by simpa [ansatz_dimensional_balance,sub_eq_zero] using first_order
  refine ⟨units,?_⟩
  intro n k balance
  simp [ansatz_dimensional_balance,units,sub_eq_zero] at balance
  omega
end
end MassShell.CompositionAndTransport

namespace MassShell.CompositionAndTransport
noncomputable section

def position_covector (a : Coordinates) : RealPhaseCovector := Sum.elim a (fun _ => 0)
def momentum_contraction (a : Coordinates) (v : RealPhaseCovector) : ℝ := ∑ j, a j * v (.inr j)

/-- The nth coefficient of the potential shift A(X ± y/2) after the positive
Fourier transform, in physical momentum coordinates. The two signs correspond
to the two endpoint equations. Here λ is the external formal parameter. -/
def potential_shift_symbol (sign : ℝ) (n : ℕ) (a : Coordinates) (v : RealPhaseCovector) : ℂ :=
  ((-(sign : ℂ) * Complex.I / 2) * momentum_contraction a v)^n / (n.factorial : ℂ)

/-- All differential symbols of the potential terms agree with the selected
matrix Moyal coefficients in both orders, including the sign at odd orders. -/
theorem theorem_wigner_potential_symbols_match_moyal (n : ℕ) (a : Coordinates) (v : RealPhaseCovector) :
    symbol_value (moyal_polynomial n) (position_covector a) v = potential_shift_symbol 1 n a v ∧
    symbol_value (moyal_polynomial n) v (position_covector a) = potential_shift_symbol (-1) n a v := by
  have plus : omega v (position_covector a) = momentum_contraction a v := by
    simp [omega,position_covector,momentum_contraction,mul_comm]
  have minus := (lemma_omega_skew (position_covector a) v).trans (congrArg Neg.neg plus)
  constructor <;> rw [lemma_moyal_symbol_value] <;>
    simp only [plus,minus,potential_shift_symbol,moyal_weight,Complex.ofReal_neg,
      Complex.ofReal_one,div_mul_eq_mul_div,← mul_pow] <;> congr 2 <;> ring
end
end MassShell.CompositionAndTransport

namespace MassShell.CompositionAndTransport
noncomputable section
open MeasureTheory
abbrev ShellCoordinates := Coordinates × (Fin 3 → ℝ)

/-- Independent coordinates on a graph patch. The transverse coordinate is the
covariant energy coordinate p₀ in the original Cartesian phase-space volume. -/
def shell_chart_point (y : ShellCoordinates) (t : ℝ) : PhasePoint := (y.1, Fin.cons t y.2)

def delta_chart_weight (g : PhasePoint → ℝ) (root : ShellCoordinates → ℝ) (y : ShellCoordinates) :
    ENNReal := ENNReal.ofReal |deriv (fun t => g (shell_chart_point y t)) (root y)|⁻¹

/-- The local formula for δ(g) on a simple-root graph, with transverse Jacobian
1/|∂g/∂p₀|. The base measure may be restricted to a single coordinate patch. -/
def delta_chart_measure (base : Measure ShellCoordinates) (g : PhasePoint → ℝ)
    (root : ShellCoordinates → ℝ) : Measure PhasePoint :=
  (base.withDensity (delta_chart_weight g root)).map (fun y => shell_chart_point y (root y))

theorem theorem_delta_chart_is_carried_on_shell (base : Measure ShellCoordinates)
    (g : PhasePoint → ℝ) (root : ShellCoordinates → ℝ) (hg : Continuous g)
    (chart : Measurable (fun y => shell_chart_point y (root y)))
    (on_graph : ∀ y, g (shell_chart_point y (root y)) = 0) :
    ∀ᵐ z ∂(delta_chart_measure base g root), g z = 0 := by
  apply (ae_map_iff chart.aemeasurable (measurableSet_eq_fun hg.measurable measurable_const)).2
  exact Filter.Eventually.of_forall on_graph

def free_shell_function (b : ℝ) (z : PhasePoint) := minkowski_pairing z.2 z.2 - b^2
def free_energy_root (b sign : ℝ) (y : ShellCoordinates) :=
  sign * Real.sqrt (b^2 + (y.2 0)^2 + (y.2 1)^2 + (y.2 2)^2)

theorem theorem_free_delta_chart (b sign : ℝ) (hb : 0 < b) (hs : sign^2=1) (y : ShellCoordinates) :
    free_shell_function b (shell_chart_point y (free_energy_root b sign y)) = 0 ∧
    0 < |free_energy_root b sign y| ∧
    delta_chart_weight (free_shell_function b) (free_energy_root b sign) y =
      ENNReal.ofReal (2 * |free_energy_root b sign y|)⁻¹ := by
  let E := b^2 + (y.2 0)^2 + (y.2 1)^2 + (y.2 2)^2
  have pos : 0 < E := by dsimp [E]; positivity
  have sq := Real.sq_sqrt pos.le
  have root_sq : (free_energy_root b sign y)^2 = E := by
    change (sign*Real.sqrt E)^2 = E
    rw [mul_pow,hs,one_mul,sq]
  have norm : free_energy_root b sign y ≠ 0 := by intro h; rw [h] at root_sq; simp at root_sq; linarith
  have scalar (t : ℝ) : free_shell_function b (shell_chart_point y t) =
      t^2 - (y.2 0)^2 - (y.2 1)^2 - (y.2 2)^2 - b^2 := by
    change t*t - y.2 0*y.2 0 - y.2 1*y.2 1 - y.2 2*y.2 2 - b^2 = _
    ring
  refine ⟨?_,abs_pos.mpr norm,?_⟩
  · rw [scalar,root_sq]
    dsimp [E]; ring
  · unfold delta_chart_weight
    simp_rw [scalar]
    have derivative (t : ℝ) : HasDerivAt (fun w : ℝ => w^2 - (y.2 0)^2 -
        (y.2 1)^2 - (y.2 2)^2 - b^2) (2*t) t := by
      convert (((((hasDerivAt_pow 2 t).sub_const _).sub_const _).sub_const _).sub_const _) using 1; simp
    rw [(derivative _).deriv,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
end
end MassShell.CompositionAndTransport

namespace MassShell.CompositionAndTransport
noncomputable section
set_option maxHeartbeats 1000000
abbrev left_multiply := mixed_multiplication .generator_left
abbrev right_multiply := mixed_multiplication .generator_right
def weak_block (P Q : S) (W : EnsembleDistribution) := right_multiply Q (left_multiply P W)

theorem lemma_smooth_multiplier_is_weak (side : ProductSide) (H : S) :
    weak_action (mixed_multiplication side H) := lemma_mixed_word_is_weak side [] H

theorem lemma_block_is_weak (P Q : S) : weak_action (weak_block P Q) :=
  lemma_weak_action_comp (A := right_multiply Q) (B := left_multiply P)
    (lemma_smooth_multiplier_is_weak .generator_right Q)
    (lemma_smooth_multiplier_is_weak .generator_left P)

theorem lemma_weak_map_sub {A : EnsembleDistribution → EnsembleDistribution} (ha : weak_action A)
    (W V : EnsembleDistribution) : A (W-V) = A W - A V := by
  ext i j φ
  obtain ⟨t,ht⟩ := ha i j φ
  have ev (U : EnsembleDistribution) : A U i j φ = ∑ r, ∑ s, U r s (t r s) :=
    (congrFun ht U).symm
  change A (W-V) i j φ = A W i j φ - A V i j φ
  simp only [ev,Matrix.sub_apply,sub_apply,Finset.sum_sub_distrib]

/-- The distributional block of the commutator is the spectral-gap multiplier
times that block of the distribution. Scalar eigenvalue fields may vary in space. -/
theorem theorem_weak_spectral_gap (H P Q e₁ e₂ : S)
    (left_eigen : P*H = e₁*P) (right_eigen : H*Q = Q*e₂)
    (central : ∀ F : S, F*e₂ = e₂*F) (W : EnsembleDistribution) :
    weak_block P Q (left_multiply H W - right_multiply H W) =
      left_multiply e₁ (weak_block P Q W) - left_multiply e₂ (weak_block P Q W) := by
  let B := weak_block P Q
  have equiv (A D : EnsembleDistribution → EnsembleDistribution) (aw : weak_action A)
      (dw : weak_action D) (agree : ∀ F : S, A (regular_ensemble F) = D (regular_ensemble F)) :
      A W = D W := congrFun (lemma_weak_action_ext aw dw agree) W
  have l (E F : S) : left_multiply E (regular_ensemble F) = regular_ensemble (E*F) :=
    lemma_mixed_multiplication_extends .generator_left E F
  have r (E F : S) : right_multiply E (regular_ensemble F) = regular_ensemble (F*E) :=
    lemma_mixed_multiplication_extends .generator_right E F
  have block (F : S) : B (regular_ensemble F) = regular_ensemble (P*F*Q) := by
    change right_multiply Q (left_multiply P (regular_ensemble F)) = _
    rw [l,r]
  have pair (side : ProductSide) (e : S)
      (algebra : ∀ F : S, P*(match side with | .generator_left => H*F | .generator_right => F*H)*Q =
        e*(P*F*Q)) : B (mixed_multiplication side H W) = left_multiply e (B W) := by
    apply equiv (fun V => B (mixed_multiplication side H V)) (fun V => left_multiply e (B V))
      (lemma_weak_action_comp (lemma_block_is_weak P Q) (lemma_smooth_multiplier_is_weak side H))
      (lemma_weak_action_comp (lemma_smooth_multiplier_is_weak .generator_left e) (lemma_block_is_weak P Q))
    intro F
    rw [lemma_mixed_multiplication_extends,block,block,l]
    exact congrArg regular_ensemble (algebra F)
  rw [lemma_weak_map_sub (lemma_block_is_weak P Q)]
  change B _ - B _ = _
  rw [pair .generator_left e₁ (fun F => by dsimp; rw [← mul_assoc P H,left_eigen]; simp [mul_assoc])]
  apply congrArg (fun Z => left_multiply e₁ (B W) - Z)
  apply pair .generator_right e₂
  intro F
  change P*(F*H)*Q = _
  calc
    P*(F*H)*Q = (P*F)*(H*Q) := by simp [mul_assoc]
    _ = (P*F*Q)*e₂ := by rw [right_eigen]; simp only [mul_assoc]
    _ = _ := central _

theorem theorem_distribution_first_order_transport (H P e : S)
    (left_eigen : P*H = e*P) (right_eigen : H*P = P*e) (central : ∀ F : S, F*e = e*F)
    (W : ℕ → EnsembleDistribution)
    (preserved : distribution_product_order .generator_left 1 H W =
      distribution_product_order .generator_right 1 H W) :
    weak_block P P (distribution_moyal_coefficient .generator_left 1 H (W 0) -
      distribution_moyal_coefficient .generator_right 1 H (W 0)) = 0 := by
  simp [distribution_product_order,Finset.sum_range_succ,lemma_distribution_order_zero] at preserved
  have reaction : distribution_moyal_coefficient .generator_left 1 H (W 0) -
      distribution_moyal_coefficient .generator_right 1 H (W 0) =
      -(left_multiply H (W 1) - right_multiply H (W 1)) := by
    change left_multiply H (W 1) + _ = right_multiply H (W 1) + _ at preserved
    rw [neg_sub,sub_eq_sub_iff_add_eq_add]
    simpa only [add_comm,add_left_comm,add_assoc] using preserved
  have gap := theorem_weak_spectral_gap H P P e e left_eigen right_eigen central (W 1)
  have swap : distribution_moyal_coefficient .generator_left 1 H (W 0) -
      distribution_moyal_coefficient .generator_right 1 H (W 0) =
      right_multiply H (W 1) - left_multiply H (W 1) := by rw [reaction,neg_sub]
  rw [swap,lemma_weak_map_sub (lemma_block_is_weak P P)]
  rw [lemma_weak_map_sub (lemma_block_is_weak P P),sub_self,sub_eq_zero] at gap
  rw [gap,sub_self]
end
end MassShell.CompositionAndTransport

namespace MassShell
noncomputable section
open Matrix
open scoped ComplexConjugate
theorem lemma_gamma_dirac_hermiticity (μ : Fin 4) :
    (gamma_axis μ).conjTranspose * gamma_axis 0 = gamma_axis 0 * gamma_axis μ := by
  ext i j
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    norm_num [gamma_axis,four_component_factor,four_component_pencil,Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.conjTranspose_apply, Pi.single_apply, Complex.conj_I]

/-- Columns may encode spinor amplitudes. For real potentials, taking the ordinary
Hermitian transpose of the minimally coupled equation and multiplying on the right
by γ⁰ gives the adjoint amplitude equation. The matrices D contain the four
directional derivatives at the spacetime point under consideration. -/
theorem theorem_adjoint_dirac_equation (ψ : FourByFour) (D : Fin 4 → FourByFour)
    (h c q m : ℝ) (A : Fin 4 → ℝ)
    (equation : (∑ μ, gamma_axis μ * ((Complex.I * h * c) • D μ - ((q*A μ : ℝ) : ℂ) • ψ)) -
      (m : ℂ) • ψ = 0) :
    (∑ μ, ((-Complex.I * h * c) • ((D μ).conjTranspose * gamma_axis 0) -
      ((q*A μ : ℝ) : ℂ) • (ψ.conjTranspose * gamma_axis 0)) * gamma_axis μ) -
      (m : ℂ) • (ψ.conjTranspose * gamma_axis 0) = 0 := by
  have e := congrArg (fun M : FourByFour => M.conjTranspose * gamma_axis 0) equation
  have slide (μ : Fin 4) (B : FourByFour) : B * (gamma_axis μ).conjTranspose * gamma_axis 0 =
      B * gamma_axis 0 * gamma_axis μ := by rw [mul_assoc,lemma_gamma_dirac_hermiticity,← mul_assoc]
  rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_sum,sub_mul,Finset.sum_mul,
    Matrix.conjTranspose_smul,smul_mul_assoc,Matrix.conjTranspose_zero,zero_mul] at e
  convert e using 2
  · apply Finset.sum_congr rfl
    intro μ _
    rw [Matrix.conjTranspose_mul,slide,Matrix.conjTranspose_sub,sub_mul]
    simp [Matrix.conjTranspose_smul,sub_mul,neg_mul]
  · simp
end
end MassShell

namespace MassShell
noncomputable section
open scoped Matrix.Norms.Elementwise
/-- Constant matrices act continuously on the spacetime density. Differentiation
at fixed momentum therefore preserves the two-sided support of the free projector. -/
theorem lemma_free_derivative_has_sector_support (P : FourByFour) (W : FourMomentum → FourByFour)
    (supported : ∀ x, P*W x=W x ∧ W x*P=W x) (x v : FourMomentum)
    (smooth : DifferentiableAt ℝ W x) :
    let D := fderiv ℝ W x v
    P*D=D ∧ D*P=D := by
  let L : FourByFour →L[ℝ] FourByFour := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ P)
  let R : FourByFour →L[ℝ] FourByFour := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ P)
  have fixed (T : FourByFour →L[ℝ] FourByFour) (h : ∀ y, T (W y) = W y) :
      T (fderiv ℝ W x v) = fderiv ℝ W x v := by
    have eqn : T ∘ W = W := funext h
    have d := (T.hasFDerivAt.comp x smooth.hasFDerivAt).fderiv
    exact (congrArg (fun M : FourMomentum →L[ℝ] FourByFour => M v) d).symm.trans
      (congrArg (fun f : FourMomentum → FourByFour => fderiv ℝ f x v) eqn)
  exact ⟨fixed L (fun y => (supported y).1),fixed R (fun y => (supported y).2)⟩

/-- Eqs. (22) and (23), at either massive momentum and in any fixed linear spin
coordinates. The observation may in particular extract the entire 2×2 block.
No constancy of the ensemble along x is assumed. The vanishing premise is the
diagonal projection of the free Weyl operator in canonical coordinates. -/
theorem theorem_free_projected_transport_equation (factor : FourMomentum →ₗ[ℝ] FourByFour)
    (square : ansatz_reproduces_minkowski_square factor) (p : FourMomentum) (m : ℝ)
    (hm : m ≠ 0) (shell : minkowski_pairing p p = m^2) (W : FourMomentum → FourByFour)
    (x : FourMomentum) (smooth : DifferentiableAt ℝ W x)
    (observe : FourByFour →L[ℝ] PauliMatrix) :
    let P := selected_projector (m⁻¹ • factor p)
    let axis := fun i : Fin 4 => (Pi.single i 1 : FourMomentum)
    let D := fun i => fderiv ℝ W x (axis i)
    (∀ y, P*W y=W y ∧ W y*P=W y) →
    P*(∑ i, (1/2 : ℝ) • (factor (axis i)*D i + D i*factor (axis i)))*P = 0 →
    (∑ i, (m⁻¹*minkowski_pairing p (axis i)) • D i) = 0 ∧
    (∑ i, minkowski_pairing p (axis i) • fderiv ℝ (observe ∘ W) x (axis i)) = 0 := by
  intro P axis D support projected
  have component (i : Fin 4) := corollary_free_transport_in_direction factor square p (axis i) m hm shell (D i)
  have hw : (∑ i, (m⁻¹*minkowski_pairing p (axis i)) • D i) = 0 := by
    rw [Finset.mul_sum,Finset.sum_mul] at projected
    refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) projected
    have d := lemma_free_derivative_has_sector_support P W support x (axis i) smooth
    exact (component i d.1 d.2).symm
  refine ⟨hw,?_⟩
  have full := congrArg (fun a : FourByFour => m • a) hw
  simp only [Finset.smul_sum,smul_zero,smul_smul,← mul_assoc,mul_inv_cancel₀ hm,one_mul] at full
  have block := congrArg observe full
  have obs (i : Fin 4) : fderiv ℝ (observe ∘ W) x (axis i) = observe (D i) :=
    congrArg (fun M : FourMomentum →L[ℝ] PauliMatrix => M (axis i)) ((observe.hasFDerivAt.comp x smooth.hasFDerivAt).fderiv)
  simpa only [obs,map_sum,map_smul,map_zero] using block
end
end MassShell

namespace MassShell.CompositionAndTransport
noncomputable section
open TensorProduct
open scoped TensorProduct Matrix.Norms.Elementwise ContDiff
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

/-- Expand the single canonical contraction in the smooth tensor calculus.
The order of the two matrix factors is preserved in both terms. -/
theorem lemma_canonical_poisson_on_fields (F G : S) :
    poisson_power 1 F G = ((∑ i : Fin 4, (partial_map (.inr i) F * partial_map (.inl i) G -
      partial_map (.inl i) F * partial_map (.inr i) G) : S) : Symbol) := by
  have cross (i j : Axis) : differential_operator F G
      (MvPolynomial.X (.left,i) * MvPolynomial.X (.right,j)) =
      ((partial_map i F * partial_map j G : S) : Symbol) := by
    rw [← lemma_tensor_operator_value]
    unfold tensor_operator
    rw [LinearMap.comp_apply,map_mul,lemma_apply_endomorphism_product]
    simp [pair_calculus,pair_partial,matrix_multiply]
  unfold poisson_power canonical_symbol contraction
  simp only [pow_one,map_sum,map_sub,cross,lemma_smooth_sum,Subalgebra.coe_sub]

/-- Differentiate the linear free momentum pencil. Its momentum derivative is
the corresponding gamma matrix everywhere, on either energy sheet. -/
theorem lemma_free_momentum_derivative (m : ℝ) (i : Fin 4) :
    partial_map (.inr i) (free_generator m) = constant_matrix (gamma_axis i) := by
  apply Subtype.ext
  funext z a b
  let entry : FourByFour →L[ℝ] ℂ := (Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap
  let K := four_component_factor.toContinuousLinearMap
  let L := entry.comp (K.comp (ContinuousLinearMap.snd ℝ Coordinates Coordinates))
  have d := (L.hasFDerivAt (x := z)).sub_const ((m • (1 : FourByFour)) a b)
  change fderiv ℝ (fun w => L w - _) z (direction (.inr i)) = _
  rw [d.fderiv]
  rfl

/-- On the free pencil the Weyl Liouvillian is the symmetrised contraction of
the four spacetime derivatives. No momentum-independence of W is required. -/
theorem theorem_free_weyl_is_spacetime_transport (m : ℝ) (W : S) (z : PhasePoint) :
    weyl_transport (free_generator m) W z =
      ∑ i : Fin 4, (1/2 : ℝ) • (gamma_axis i * (partial_map (.inl i) W).val z +
        (partial_map (.inl i) W).val z * gamma_axis i) := by
  have left := lemma_canonical_poisson_on_fields (free_generator m) W
  have right := lemma_canonical_poisson_on_fields W (free_generator m)
  unfold weyl_transport
  rw [left,right]
  simp only [lemma_free_momentum_derivative,(show ∀ i, partial_map (.inl i) (free_generator m) = 0 from lemma_free_generator_momentum_only m),zero_mul,mul_zero,
    sub_zero,zero_sub,lemma_smooth_sum,Subalgebra.coe_mul,Subalgebra.coe_neg,
    Pi.smul_apply,Finset.sum_neg_distrib,sub_neg_eq_add]
  rw [← Finset.sum_add_distrib, Finset.sum_apply,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (1/2 : ℂ) • _ = (1/2 : ℝ) • _
  exact congrArg (fun c : ℂ => c • (gamma_axis i * (partial_map (.inl i) W).val z +
    (partial_map (.inl i) W).val z * gamma_axis i)) (by norm_num : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ))

/-- At fixed momentum, differentiating the matrix field entrywise along its
spacetime slice gives precisely the derivatives used by the bidifferential product. -/
theorem lemma_free_slice_derivative (W : S) (x p : Coordinates) (i : Fin 4)
    (hs : DifferentiableAt ℝ (fun y => W.val (y,p)) x) :
    fderiv ℝ (fun y => W.val (y,p)) x (Pi.single i 1) = (partial_map (.inl i) W).val (x,p) := by
  ext a b
  let E : FourByFour →L[ℝ] ℂ := (Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap
  let v : Coordinates := Pi.single i 1
  have lhs := E.hasFDerivAt.comp x hs.hasFDerivAt
  have rhs := ((W.property a b).differentiable (by simp) (x,p)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (𝕜 := ℝ) p x))
  have eqn := lhs.unique rhs
  exact congrArg (fun L : Coordinates →L[ℝ] ℂ => L v) eqn

/-- From projected free Weyl preservation to Eq. (23) for all entries of
the arbitrary internal density. Choosing a basis of the rank-two image
makes observe the corresponding constant 2×2 compression at fixed p. -/
theorem theorem_free_sector_pde_from_projected_weyl (m : ℝ) (hm : m ≠ 0)
    (x p : Coordinates) (shell : minkowski_pairing p p=m^2) (W : S)
    (observe : FourByFour →L[ℝ] PauliMatrix) :
    let P := selected_projector (m⁻¹ • four_component_factor p)
    let slice := fun y : Coordinates => W.val (y,p)
    (∀ y, P*slice y=slice y ∧ slice y*P=slice y) →
    P*weyl_transport (free_generator m) W (x,p)*P=0 →
      (∑ i : Fin 4, minkowski_pairing p (Pi.single i 1) •
        fderiv ℝ (observe ∘ slice) x (Pi.single i 1)) = 0 := by
  intro P slice support projected
  have hs : DifferentiableAt ℝ slice x := by
    apply differentiableAt_pi.mpr
    intro r
    apply differentiableAt_pi.mpr
    intro s
    have component := (W.property r s).comp (contDiff_id.prodMk contDiff_const :
      ContDiff ℝ ∞ (fun y : Coordinates => (y,p)))
    exact component.differentiable (by simp) x
  apply (theorem_free_projected_transport_equation four_component_factor
    theorem_four_components_are_sufficient p m hm shell slice x hs observe support ?_).2
  rw [theorem_free_weyl_is_spacetime_transport] at projected
  simpa only [lemma_free_slice_derivative W x p _ hs, slice,gamma_axis] using projected
end
end MassShell.CompositionAndTransport

namespace MassShell.CompositionAndTransport
noncomputable section
/-- The known source at order N collects only positive product orders. Its state
indices are strictly below N whenever the sum is nonempty. -/
def lower_order_source (N : ℕ) (H : S) (W : ℕ → EnsembleDistribution) :=
  ∑ j ∈ Finset.range N, (distribution_moyal_coefficient .generator_left (j+1) H (W (N-(j+1))) -
    distribution_moyal_coefficient .generator_right (j+1) H (W (N-(j+1))))

/-- Split Eq. (78) at product order zero. A20 identifies the lower-order source
with the negative ordinary commutator of H and the unknown coefficient W_N. -/
theorem theorem_isolate_hierarchy_source (N : ℕ) (H : S) (W : ℕ → EnsembleDistribution)
    (preserved : distribution_product_order .generator_left N H W =
      distribution_product_order .generator_right N H W) :
    lower_order_source N H W = right_multiply H (W N) - left_multiply H (W N) := by
  have h := sub_eq_zero.mpr preserved
  unfold distribution_product_order at h
  rw [← Finset.sum_sub_distrib,Finset.sum_range_succ',Nat.sub_zero,
    lemma_distribution_order_zero,lemma_distribution_order_zero] at h
  change lower_order_source N H W + (left_multiply H (W N) - right_multiply H (W N)) = 0 at h
  simpa only [neg_sub] using eq_neg_of_add_eq_zero_left h

/-- Diagonal compatibility at every order. Within an eigensector the spectral
gap vanishes, so W_N cannot cancel a diagonal lower-order source. -/
theorem theorem_diagonal_compatibility_at_every_order (N : ℕ) (H P e : S)
    (left : P*H=e*P) (right : H*P=P*e) (central : ∀ F : S, F*e=e*F)
    (W : ℕ → EnsembleDistribution) (preserved : distribution_product_order .generator_left N H W =
      distribution_product_order .generator_right N H W) :
    weak_block P P (lower_order_source N H W) = 0 := by
  rw [theorem_isolate_hierarchy_source N H W preserved,lemma_weak_map_sub (lemma_block_is_weak P P)]
  have gap := theorem_weak_spectral_gap H P P e e left right central (W N)
  rw [lemma_weak_map_sub (lemma_block_is_weak P P),sub_self,sub_eq_zero] at gap
  rw [gap,sub_self]

/-- In opposite eigensectors multiply by the smooth inverse gap on the region
under consideration. This gives the actual off-diagonal coefficient in terms
of H and lower state orders, conditional only on preservation and the gap. -/
theorem theorem_intersector_reaction_at_every_order (N : ℕ) (H P Q e₁ e₂ inverseGap : S)
    (left : P*H=e₁*P) (right : H*Q=Q*e₂) (central : ∀ F : S, F*e₂=e₂*F)
    (inverse : inverseGap*(e₂-e₁)=1)
    (W : ℕ → EnsembleDistribution) (preserved : distribution_product_order .generator_left N H W =
      distribution_product_order .generator_right N H W) :
    weak_block P Q (W N) = left_multiply inverseGap (weak_block P Q (lower_order_source N H W)) := by
  let B := weak_block P Q
  have gap := theorem_weak_spectral_gap H P Q e₁ e₂ left right central (W N)
  rw [lemma_weak_map_sub (lemma_block_is_weak P Q)] at gap
  rw [theorem_isolate_hierarchy_source N H W preserved,lemma_weak_map_sub (lemma_block_is_weak P Q)]
  have reverse := congrArg Neg.neg gap
  simp only [neg_sub] at reverse
  rw [reverse]
  let A := fun U : EnsembleDistribution => left_multiply inverseGap (left_multiply e₂ U - left_multiply e₁ U)
  have aw : weak_action A := by
    apply lemma_weak_action_comp (A := left_multiply inverseGap)
      (B := fun U => left_multiply e₂ U - left_multiply e₁ U) (lemma_smooth_multiplier_is_weak _ _)
    intro i j φ
    exact test_pairing.range.sub_mem (lemma_smooth_multiplier_is_weak .generator_left e₂ i j φ)
      (lemma_smooth_multiplier_is_weak .generator_left e₁ i j φ)
  have l (e f : S) : left_multiply e (regular_ensemble f) = regular_ensemble (e*f) :=
    lemma_mixed_multiplication_extends .generator_left e f
  have eqn : A = id := by
    apply lemma_weak_action_ext aw (fun i j φ => lemma_single_test i j φ)
    intro F
    change left_multiply inverseGap (left_multiply e₂ (regular_ensemble F) -
      left_multiply e₁ (regular_ensemble F)) = regular_ensemble F
    rw [l,l,← map_sub,l,← sub_mul,← mul_assoc,inverse,one_mul]
  exact (congrFun eqn (B (W N))).symm
end
end MassShell.CompositionAndTransport

namespace MassShell.CompositionAndTransport
noncomputable section
open scoped Topology ContDiff
abbrev CartesianPhase := Fin 8 → ℝ
abbrev ChartBase := Fin 7 → ℝ

/-- Insert the graph's transverse coordinate into any one of the eight Cartesian slots. -/
def chart_frame (i : Fin 8) : ChartBase × ℝ →L[ℝ] CartesianPhase :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p => i.insertNth p.2 p.1
    map_add' := by intro u v; funext j; cases j using i.succAboveCases <;> simp
    map_smul' := by intro c u; funext j; cases j using i.succAboveCases <;> simp }

/-- Any regular point has a transverse Cartesian direction because the coordinate
vectors span phase space. The implicit function theorem constructs its local graph
and proves that it contains every nearby point of the level set. -/
theorem theorem_regular_shell_has_graph (g : CartesianPhase → ℝ) (z : CartesianPhase)
    (smooth : ContDiffAt ℝ ∞ g z) (on_shell : g z=0) (regular : fderiv ℝ g z ≠ 0) :
    ∃ (i : Fin 8) (root : ChartBase → ℝ),
      fderiv ℝ g z (Pi.single i 1) ≠ 0 ∧
      root (i.removeNth z) = z i ∧ ContDiffAt ℝ ∞ root (i.removeNth z) ∧
      (∀ᶠ y in 𝓝 (i.removeNth z), g (chart_frame i (y,root y)) = 0) ∧
      (∀ᶠ p in 𝓝 (i.removeNth z,z i), g (chart_frame i p) = 0 ↔ root p.1=p.2) := by
  obtain ⟨i,hi⟩ : ∃ i : Fin 8, fderiv ℝ g z (Pi.single i 1) ≠ 0 := by
    by_contra! all_zero
    apply regular
    ext1 w
    rw [pi_eq_sum_univ' w,map_sum]
    simp [all_zero]
  let p : ChartBase × ℝ := (i.removeNth z,z i)
  let L := chart_frame i
  have at_z : L p=z := by
    change i.insertNth (z i) (i.removeNth z)=z
    simp
  have axis : L (0,1) = Pi.single i 1 := by
    funext j
    change i.insertNth (α := fun _ => ℝ) 1 0 j = _
    cases j using i.succAboveCases <;> simp [Fin.succAbove_ne]
  let f := g ∘ L
  have hs : ContDiffAt ℝ ∞ f p := (at_z ▸ smooth : ContDiffAt ℝ ∞ g (L p)).comp p L.contDiff.contDiffAt
  let D := (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ ChartBase ℝ)
  have slope : D 1 ≠ 0 := by
    have deriv := (smooth.differentiableAt (by simp)).hasFDerivAt
    rw [← at_z] at deriv
    have e := (deriv.comp p L.hasFDerivAt).fderiv
    change fderiv ℝ (g ∘ L) p (0,1) ≠ 0
    rw [e]
    simpa [axis,at_z] using hi
  have inv : D.IsInvertible := by
    have formula (a : ℝ) : D a = a * D 1 := by simpa using D.map_smul a 1
    have bij : Function.Bijective D := ⟨fun a b eqn => mul_right_cancel₀ slope
      ((formula a).symm.trans (eqn.trans (formula b))), fun y => ⟨y / D 1,(formula _).trans (div_mul_cancel₀ _ slope)⟩⟩
    exact ⟨(LinearEquiv.ofBijective D.toLinearMap bij).toContinuousLinearEquiv,rfl⟩
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨i,hs.implicitFunction hn inv,hi,hs.implicitFunction_apply_self hn inv,
    hs.contDiffAt_implicitFunction hn inv,?_,?_⟩
  · simpa only [f,Function.comp_apply,at_z,on_shell] using hs.eventually_apply_implicitFunction hn inv
  · simpa only [f,Function.comp_apply,at_z,on_shell] using hs.eventually_apply_eq_iff_implicitFunction hn inv
end
end MassShell.CompositionAndTransport

namespace MassShell.CompositionAndTransport
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
/-- On an overlap, hold the six common coordinates fixed. If s=φ(r) solves
g(r,s)=0, differentiating that identity gives g_r + g_s φ'=0. Taking absolute
values yields the change of transverse delta weight, including orientation reversal. -/
theorem lemma_transverse_jacobian_ratio (g : ℝ × ℝ → ℝ) (φ : ℝ → ℝ) (r : ℝ)
    (dg : DifferentiableAt ℝ g (r,φ r)) (dφ : DifferentiableAt ℝ φ r)
    (on_shell : ∀ᶠ t in 𝓝 r, g (t,φ t) = 0)
    (gr : fderiv ℝ g (r,φ r) (1,0) ≠ 0) (gs : fderiv ℝ g (r,φ r) (0,1) ≠ 0) :
    |deriv φ r| / |fderiv ℝ g (r,φ r) (1,0)| = 1 / |fderiv ℝ g (r,φ r) (0,1)| := by
  let D := fderiv ℝ g (r,φ r)
  have curve := dg.hasFDerivAt.comp r ((hasFDerivAt_id (𝕜 := ℝ) r).prodMk dφ.hasFDerivAt)
  have zero : fderiv ℝ (fun t => g (t,φ t)) r = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq (show (fun t => g (t,φ t)) =ᶠ[𝓝 r] (fun _ => 0) from on_shell)]
    simp
  have tangent : D (1,deriv φ r) = 0 := by
    have eqn := curve.fderiv
    change fderiv ℝ (fun t => g (t,φ t)) r = _ at eqn
    rw [zero] at eqn
    exact (congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) eqn).symm
  have split : (1,deriv φ r) = (1,0) + deriv φ r • ((0,1) : ℝ × ℝ) := by ext <;> simp
  rw [split,map_add,map_smul,smul_eq_mul] at tangent
  have ratio : deriv φ r = -(D (1,0)) / D (0,1) := (eq_div_iff gs).2 (by linarith)
  rw [ratio,abs_div,abs_neg]
  change |D (1,0)| / |D (0,1)| / |D (1,0)| = 1 / |D (0,1)|
  field_simp [abs_ne_zero.mpr (show D (1,0) ≠ 0 from gr), abs_ne_zero.mpr (show D (0,1) ≠ 0 from gs)]

/-- The two graph formulas give identical integrals of every complex test on
their overlap. The transition derivative is proved from the shell equation.
The inverse-graph hypothesis identifies the common points of the two patches. -/
theorem theorem_delta_graph_overlap_on_fibre (g : ℝ × ℝ → ℝ) (φ ψ : ℝ → ℝ)
    (U : Set ℝ) (openU : IsOpen U) (smooth : ∀ r ∈ U, DifferentiableAt ℝ g (r,φ r))
    (graph : ∀ r ∈ U, g (r,φ r)=0) (inverse : ∀ r ∈ U, ψ (φ r)=r)
    (regular : ∀ r ∈ U, fderiv ℝ g (r,φ r) (1,0) ≠ 0 ∧ fderiv ℝ g (r,φ r) (0,1) ≠ 0)
    (dφ : ∀ r ∈ U, DifferentiableAt ℝ φ r) (test : ℝ × ℝ → ℂ) :
    (∫ s in φ '' U, (1 / |fderiv ℝ g (ψ s,s) (1,0)|) • test (ψ s,s)) =
      ∫ r in U, (1 / |fderiv ℝ g (r,φ r) (0,1)|) • test (r,φ r) := by
  have inj : InjOn φ U := fun a ha b hb eqn => (inverse a ha).symm.trans ((congrArg ψ eqn).trans (inverse b hb))
  rw [integral_image_eq_integral_abs_deriv_smul openU.measurableSet
    (fun r hr => (dφ r hr).hasDerivAt.hasDerivWithinAt) inj]
  apply setIntegral_congr_fun openU.measurableSet
  intro r hr
  have near : ∀ᶠ t in 𝓝 r, g (t,φ t) = 0 := by
    filter_upwards [openU.mem_nhds hr] with t ht using graph t ht
  have jac := lemma_transverse_jacobian_ratio g φ r (smooth r hr) (dφ r hr) near
    (regular r hr).1 (regular r hr).2
  simp only [inverse r hr,smul_smul,one_div]
  exact congrArg (fun c : ℝ => c • test (r,φ r)) (by simpa only [div_eq_mul_inv,one_mul] using jac)

/-- Fubini in coordinate order (six shared coordinates, then the remaining
chart parameter). Equality for each fibre proves agreement of the local
distribution pairings for arbitrary test fields on eight-dimensional phase space. -/
theorem theorem_shell_chart_distributions_agree {Y : Type*} [MeasurableSpace Y]
    (base : Measure Y) (point : Y → ℝ × ℝ → PhasePoint) (g : PhasePoint → ℝ)
    (φ ψ : Y → ℝ → ℝ) (U : Y → Set ℝ) (openU : ∀ y, IsOpen (U y))
    (smooth : ∀ y r, r ∈ U y → DifferentiableAt ℝ (g ∘ point y) (r,φ y r))
    (graph : ∀ y r, r ∈ U y → g (point y (r,φ y r))=0)
    (inverse : ∀ y r, r ∈ U y → ψ y (φ y r)=r)
    (regular : ∀ y r, r ∈ U y → fderiv ℝ (g ∘ point y) (r,φ y r) (1,0) ≠ 0 ∧
      fderiv ℝ (g ∘ point y) (r,φ y r) (0,1) ≠ 0)
    (dφ : ∀ y r, r ∈ U y → DifferentiableAt ℝ (φ y) r) (test : PhasePoint → ℂ) :
    (∫ y, (∫ s in (φ y) '' U y, (1 / |fderiv ℝ (g ∘ point y) (ψ y s,s) (1,0)|) •
      test (point y (ψ y s,s))) ∂base) =
    ∫ y, (∫ r in U y, (1 / |fderiv ℝ (g ∘ point y) (r,φ y r) (0,1)|) •
      test (point y (r,φ y r))) ∂base := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => theorem_delta_graph_overlap_on_fibre
    (g ∘ point y) (φ y) (ψ y) (U y) (openU y) (smooth y) (graph y) (inverse y)
    (regular y) (dφ y) (test ∘ point y)
end
end MassShell.CompositionAndTransport

namespace MassShell.CompositionAndTransport
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
variable {Y : Type*} [MeasurableSpace Y]

/-- A graph patch over seven coordinates, displayed as six shared coordinates and
one variable of integration. Restriction to the patch is included in the weight. -/
def graph_patch_measure (base : Measure Y) (domain : Set (Y × ℝ))
    (weight : Y × ℝ → ENNReal) (graph : Y × ℝ → PhasePoint) : Measure PhasePoint :=
  ((base.prod volume).withDensity (domain.indicator weight)).map graph

/-- Evaluate the graph measure on a Borel set by integrating over its fibres.
This nonnegative formula applies before any local-finiteness or integrability argument. -/
theorem lemma_graph_patch_measure_apply (base : Measure Y) [SFinite base]
    (domain : Set (Y × ℝ)) (weight : Y × ℝ → ENNReal) (graph : Y × ℝ → PhasePoint)
    (hd : MeasurableSet domain) (hw : Measurable weight) (hg : Measurable graph)
    (B : Set PhasePoint) (hB : MeasurableSet B) :
    graph_patch_measure base domain weight graph B =
      ∫⁻ y, (∫⁻ r in {r : ℝ | (y,r) ∈ domain},
        (graph ⁻¹' B).indicator weight (y,r)) ∂base := by
  rw [graph_patch_measure,Measure.map_apply hg hB,withDensity_apply _ (hg hB),
    ← lintegral_indicator (hg hB),lintegral_prod]
  · apply lintegral_congr
    intro y
    have fibre : MeasurableSet {r : ℝ | (y,r) ∈ domain} := hd.preimage
      (measurable_const.prodMk measurable_id : Measurable (fun r : ℝ => (y,r)))
    rw [← lintegral_indicator fibre]
    apply lintegral_congr
    intro r
    by_cases h : (y,r) ∈ domain <;> by_cases k : graph (y,r) ∈ B <;>
      simp [Set.mem_preimage,h,k]
  · exact ((hw.indicator hd).indicator (hg hB)).aemeasurable

/-- Equality of the actual pushforward measures on a common regular patch.
Only the usual graph conditions and Borel measurability are required. The
Jacobian ratio is derived, so equality of chart measures is a conclusion. -/
theorem theorem_delta_measures_agree_on_overlap (base : Measure Y) [SFinite base]
    (point : Y → ℝ × ℝ → PhasePoint) (g : PhasePoint → ℝ) (φ ψ : Y → ℝ → ℝ)
    (U V : Set (Y × ℝ)) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (openU : ∀ y, IsOpen {r : ℝ | (y,r) ∈ U})
    (image : ∀ y, {s : ℝ | (y,s) ∈ V} = φ y '' {r : ℝ | (y,r) ∈ U})
    (smooth : ∀ y r, (y,r) ∈ U → DifferentiableAt ℝ (g ∘ point y) (r,φ y r))
    (shell : ∀ y r, (y,r) ∈ U → g (point y (r,φ y r))=0)
    (inverse : ∀ y r, (y,r) ∈ U → ψ y (φ y r)=r)
    (regular : ∀ y r, (y,r) ∈ U → fderiv ℝ (g ∘ point y) (r,φ y r) (1,0) ≠ 0 ∧
      fderiv ℝ (g ∘ point y) (r,φ y r) (0,1) ≠ 0)
    (dφ : ∀ y r, (y,r) ∈ U → DifferentiableAt ℝ (φ y) r) :
    let first := fun p : Y × ℝ => point p.1 (p.2,φ p.1 p.2)
    let second := fun p : Y × ℝ => point p.1 (ψ p.1 p.2,p.2)
    let w := fun p : Y × ℝ => ENNReal.ofReal (1/|fderiv ℝ (g ∘ point p.1) (p.2,φ p.1 p.2) (0,1)|)
    let v := fun p : Y × ℝ => ENNReal.ofReal (1/|fderiv ℝ (g ∘ point p.1) (ψ p.1 p.2,p.2) (1,0)|)
    Measurable first → Measurable second → Measurable w → Measurable v →
      graph_patch_measure base U w first = graph_patch_measure base V v second := by
  intro first second w v hf hs hw hv
  ext B hB
  rw [lemma_graph_patch_measure_apply base U w first hU hw hf B hB,
    lemma_graph_patch_measure_apply base V v second hV hv hs B hB]
  apply lintegral_congr
  intro y
  let fibre := {r : ℝ | (y,r) ∈ U}
  have inj : InjOn (φ y) fibre := fun a ha b hb eqn =>
    (inverse y a ha).symm.trans ((congrArg (ψ y) eqn).trans (inverse y b hb))
  rw [image,lintegral_image_eq_lintegral_abs_deriv_mul (openU y).measurableSet
    (fun r hr => (dφ y r hr).hasDerivAt.hasDerivWithinAt) inj]
  apply setLIntegral_congr_fun (openU y).measurableSet
  intro r hr
  have near : ∀ᶠ t in 𝓝 r, (g ∘ point y) (t,φ y t)=0 := by
    filter_upwards [(openU y).mem_nhds hr] with t ht using shell y t ht
  have jac := lemma_transverse_jacobian_ratio _ _ _ (smooth y r hr) (dφ y r hr) near
    (regular y r hr).1 (regular y r hr).2
  by_cases h : first (y,r) ∈ B
  · have same : second (y,φ y r) = first (y,r) := by simp [first,second,inverse y r hr]
    simp only [Set.indicator_of_mem (show (y,r) ∈ first ⁻¹' B from h),
      Set.indicator_of_mem (show (y,φ y r) ∈ second ⁻¹' B from (show second (y,φ y r) ∈ B by rw [same]; exact h))]
    dsimp only [w,v]
    rw [inverse y r hr,← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    simpa only [div_eq_mul_inv,one_mul] using jac.symm
  · have h' : second (y,φ y r) ∉ B := by simpa [first,second,inverse y r hr] using h
    simp only [Set.indicator_of_notMem (show (y,r) ∉ first ⁻¹' B from h),
      Set.indicator_of_notMem (show (y,φ y r) ∉ second ⁻¹' B from h'),mul_zero]
end
end MassShell.CompositionAndTransport

namespace MassShell.CompositionAndTransport
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology

/-- Identify the eight Cartesian coordinates with the original position–momentum pair. -/
def phase_from_cartesian : CartesianPhase ≃L[ℝ] PhasePoint :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Axis => ℝ) finSumFinEquiv.symm).trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 4) (Fin 4) (fun _ => ℝ))

/-- A regular point of the paper's defining function κ²−b² has a local
simple-root graph in the original phase space, whichever Cartesian derivative
is nonzero. The equivalence in the final clause gives local uniqueness. -/
theorem theorem_phase_shell_regular_atlas (g : PhasePoint → ℝ) (z : PhasePoint)
    (smooth : ContDiffAt ℝ ∞ g z) (shell : g z=0) (regular : fderiv ℝ g z ≠ 0) :
    let a := phase_from_cartesian.symm z
    ∃ (i : Fin 8) (root : ChartBase → ℝ),
      fderiv ℝ (g ∘ phase_from_cartesian) a (Pi.single i 1) ≠ 0 ∧
      root (i.removeNth a)=a i ∧ ContDiffAt ℝ ∞ root (i.removeNth a) ∧
      (∀ᶠ y in 𝓝 (i.removeNth a), g (phase_from_cartesian (chart_frame i (y,root y)))=0) ∧
      (∀ᶠ u in 𝓝 (i.removeNth a,a i), g (phase_from_cartesian (chart_frame i u))=0 ↔ root u.1=u.2) := by
  intro a
  let T := phase_from_cartesian
  have at_z : T a=z := T.apply_symm_apply z
  have hs : ContDiffAt ℝ ∞ (g ∘ T) a := (at_z ▸ smooth : ContDiffAt ℝ ∞ g (T a)).comp a T.contDiff.contDiffAt
  apply theorem_regular_shell_has_graph (g ∘ T) a hs (by change g (T a)=0; rw [at_z,shell])
  intro zero
  apply regular
  have d := ((at_z ▸ smooth : ContDiffAt ℝ ∞ g (T a)).differentiableAt (by simp)).hasFDerivAt.comp a T.hasFDerivAt
  have eqn := d.fderiv
  rw [zero] at eqn
  apply ContinuousLinearMap.ext
  intro w
  have h := congrArg (fun L : CartesianPhase →L[ℝ] ℝ => L (T.symm w)) eqn
  simpa [at_z] using h.symm

/-- Splitting off any transverse slot uses the usual Cartesian Lebesgue measure.
Thus the choice of omitted index introduces no extra volume factor. -/
theorem lemma_cartesian_split_preserves_volume {n : ℕ} (i : Fin (n+1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i) :=
  volume_preserving_piFinSuccAbove _ i

/-- Two distinct transverse axes leave six common coordinates. The second
index is enumerated among the seven slots remaining after removing the first. -/
def two_axis_phase_point (i : Fin 8) (j : Fin 7) (y : Fin 6 → ℝ) (t : ℝ × ℝ) : PhasePoint :=
  phase_from_cartesian (i.insertNth t.2 (j.insertNth t.1 y))

/-- On a graph patch the pushed-forward measure is carried on g=0. Combined
with the measured-shell constraint theorem this gives Eq. (86) on that patch. -/
theorem lemma_graph_patch_carried_on_shell {Y : Type*} [MeasurableSpace Y] (base : Measure Y)
    (U : Set (Y × ℝ)) (w : Y × ℝ → ENNReal) (graph : Y × ℝ → PhasePoint)
    (g : PhasePoint → ℝ) (g_meas : Measurable g) (chart_meas : Measurable graph)
    (weight_meas : Measurable (U.indicator w))
    (root : ∀ y ∈ U, g (graph y)=0) : ∀ᵐ z ∂(graph_patch_measure base U w graph), g z=0 := by
  apply (ae_map_iff chart_meas.aemeasurable (measurableSet_eq_fun g_meas measurable_const)).2
  rw [ae_withDensity_iff' _]
  · filter_upwards with y hy
    by_cases h : y ∈ U
    · exact root y h
    · simp [Set.indicator_of_notMem h] at hy
  · exact weight_meas.aemeasurable
end
end MassShell.CompositionAndTransport

namespace MassShell
noncomputable section
open scoped Matrix.Norms.Elementwise
/-- An idempotent of rank two admits coordinates for all internal matrices.
Extend each endomorphism of its image by first projecting into that image.
Restriction back to the image recovers the original endomorphism. -/
theorem theorem_arbitrary_internal_matrix_lift (P : FourByFour) (idem : P*P=P)
    (rank : Module.finrank ℂ (LinearMap.range (Matrix.toLinAlgEquiv' P))=2) :
    ∃ encode : PauliMatrix → FourByFour, Function.Injective encode ∧
      (∀ F, P*encode F=encode F ∧ encode F*P=encode F) ∧
      (∀ F G, encode (F+G)=encode F+encode G) ∧
      (∀ (c : ℂ) F, encode (c • F)=c • encode F) := by
  let J := Matrix.toLinAlgEquiv' P
  let V := LinearMap.range J
  let basis : V ≃ₗ[ℂ] (Fin 2 → ℂ) := LinearEquiv.ofFinrankEq _ _ (by simpa [V,J] using rank)
  let insert := V.subtype.comp basis.symm.toLinearMap
  let read := basis.toLinearMap.comp J.rangeRestrict
  have jj : J*J=J := by simpa [J] using congrArg Matrix.toLinAlgEquiv' idem
  have fixed (v : V) : J v.val = v.val := by
    obtain ⟨w,hw⟩ := v.property
    rw [← hw]
    exact DFunLike.congr_fun jj w
  have retract (v) : read (insert v)=v := by
    change basis (J.rangeRestrict (basis.symm v).val) = v
    rw [show J.rangeRestrict (basis.symm v).val = basis.symm v from Subtype.ext (fixed _)]
    exact basis.apply_symm_apply v
  let encode (A : PauliMatrix) : FourByFour :=
    Matrix.toLinAlgEquiv'.symm (insert.comp ((Matrix.toLinAlgEquiv' A).comp read))
  refine ⟨encode,?_,?_,?_,?_⟩
  · intro A B eqn
    apply Matrix.toLinAlgEquiv'.injective
    apply LinearMap.ext
    intro v
    have h := congrArg (fun M : FourByFour => read ((Matrix.toLinAlgEquiv' M) (insert v))) eqn
    simpa [encode,retract] using h
  · intro A
    constructor <;> apply Matrix.toLinAlgEquiv'.injective <;> apply LinearMap.ext <;> intro w
    · simpa [encode,J,insert] using fixed (basis.symm ((Matrix.toLinAlgEquiv' A) (read w)))
    · have supported : read (J w)=read w := by
        apply congrArg basis
        exact Subtype.ext (DFunLike.congr_fun jj w)
      simpa [encode,← show Matrix.toLinAlgEquiv' P=J from rfl,supported,J] using
        (congrArg (fun v => insert ((Matrix.toLinAlgEquiv' A) v)) supported)
  · intro F G
    apply Matrix.toLinAlgEquiv'.injective
    apply LinearMap.ext
    intro v
    simp only [encode, map_add, AlgEquiv.apply_symm_apply, LinearMap.comp_apply, LinearMap.add_apply]
  · intro c F
    apply Matrix.toLinAlgEquiv'.injective
    apply LinearMap.ext
    intro v
    simp only [encode, map_smul, AlgEquiv.apply_symm_apply, LinearMap.comp_apply, LinearMap.smul_apply]

/-- Eq. (23) for arbitrary distribution-valued internal data on either sheet.
Weak differentiation acts on the compactly supported spacetime test. Testing
commutes with the constant spin embedding, whose injectivity reflects zero. -/
theorem theorem_free_transport_for_internal_distributions (p : FourMomentum) (m : ℝ) (positive_mass : 0 < m)
    (shell : minkowski_pairing p p=m^2) :
    let P := selected_projector (m⁻¹ • four_component_factor p)
    ∃ encode : PauliMatrix →ₗ[ℂ] FourByFour, Function.Injective encode ∧
    ∀ (F : TestFunction (⊤ : TopologicalSpace.Opens FourMomentum) ℂ ⊤ →L[ℂ] PauliMatrix),
      let D := fun (i : Fin 4) (φ : TestFunction (⊤ : TopologicalSpace.Opens FourMomentum) ℂ ⊤) => -F (TestFunction.lineDerivCLM ℂ (Pi.single i 1 : FourMomentum) φ)
      (∀ φ, P*(∑ i, (1/2 : ℝ) • (gamma_axis i * encode (D i φ) + encode (D i φ)*gamma_axis i))*P=0) →
      ∀ φ, (∑ i : Fin 4, minkowski_pairing p (Pi.single i 1) • D i φ)=0 := by
  intro P
  have hm := positive_mass.ne'
  have square := lemma_on_shell_normalisation four_component_factor theorem_four_components_are_sufficient
    p m hm shell
  have positive_scale := CompositionAndTransport.lemma_rank_of_matrix_sector four_component_factor
    theorem_four_components_are_sufficient p m positive_mass shell
  obtain ⟨f,inj,support,add,smul⟩ := theorem_arbitrary_internal_matrix_lift P
    (lemma_selected_projector_is_idempotent _ square) positive_scale
  let E : PauliMatrix →ₗ[ℂ] FourByFour := ⟨⟨f,add⟩,smul⟩
  refine ⟨E,inj,?_⟩
  intro F D projected φ
  let v (i : Fin 4) := minkowski_pairing p (Pi.single i 1)
  have eqn := projected φ
  rw [Finset.mul_sum,Finset.sum_mul] at eqn
  have single (i : Fin 4) := corollary_free_transport_in_direction four_component_factor
    theorem_four_components_are_sufficient p (Pi.single i 1) m hm shell (E (D i φ))
    (support _).1 (support _).2
  have weighted : ∑ i, (m⁻¹*v i) • E (D i φ) = 0 :=
    (Finset.sum_congr rfl fun i _ => (single i).symm).trans eqn
  have full := congrArg (fun a : FourByFour => m • a) weighted
  simp only [Finset.smul_sum,smul_zero,smul_smul,← mul_assoc,mul_inv_cancel₀ hm,one_mul] at full
  apply inj
  change (E.restrictScalars ℝ) _ = (E.restrictScalars ℝ) 0
  rw [map_zero,map_sum]
  simp only [map_smul]
  exact full
end
end MassShell

namespace MassShell.CompositionAndTransport
noncomputable section
/-- Equations (20)–(23) for the free generator. The order-one commutator contains
the unknown first correction to the density. Both occurrences of the generator
annihilate the selected sector, so projection removes this correction and leaves
the free streaming equation for the leading internal density. -/
theorem theorem_free_sector_transport_from_preservation (m : ℝ) (hm : m ≠ 0)
    (x p : Coordinates) (shell : minkowski_pairing p p=m^2) (W : ℕ → S)
    (observe : FourByFour →L[ℝ] PauliMatrix)
    (preservation : ∀ n, commutator_coefficient moyal_coefficient (free_generator m)
      (fun k => (W k).val) n = 0) :
    let P := selected_projector (m⁻¹ • four_component_factor p)
    let slice := fun y : Coordinates => (W 0).val (y,p)
    (∀ y, P*slice y=slice y ∧ slice y*P=slice y) →
      (∑ i : Fin 4, minkowski_pairing p (Pi.single i 1) •
        fderiv ℝ (observe ∘ slice) x (Pi.single i 1)) = 0 := by
  intro P slice support
  let J := m⁻¹ • four_component_factor p
  let H := (free_generator m).val (x,p)
  have sq := lemma_on_shell_normalisation four_component_factor
    theorem_four_components_are_sufficient p m hm shell
  have form : H = m • J - m • 1 := by simp [H,free_generator,J,smul_smul,hm]
  have fixed := lemma_involution_fixes_projector J sq
  have left : P*H=0 := by
    rw [form,mul_sub,mul_smul_comm m P J,mul_smul_comm m P (1 : FourByFour),mul_one,fixed.2,sub_self]
  have right : H*P=0 := by
    rw [form,sub_mul,smul_mul_assoc m J P,smul_mul_assoc m (1 : FourByFour) P,one_mul,fixed.1,sub_self]
  have eqn := (theorem_preservation_implies_projected_transport _ rfl _ _ (x,p) J m m hm sq
    form preservation).1
  let D := weyl_transport (free_generator m) (W 0) (x,p)
  change H * _ - _ * H + Complex.I • D = 0 at eqn
  have sandwich := congrArg (fun A : FourByFour => P*A*P) eqn
  simp only [mul_add,add_mul,mul_sub,sub_mul,← mul_assoc P H,left,zero_mul,
    mul_assoc (P * _ : FourByFour) H P, ← mul_assoc P _ H,right,mul_zero,
    mul_smul_comm,smul_mul_assoc] at sandwich
  apply theorem_free_sector_pde_from_projected_weyl m hm x p shell (W 0) observe support
  exact (smul_eq_zero.mp (by simpa [mul_assoc,right] using sandwich :
    Complex.I • (P*D*P) = 0)).resolve_left Complex.I_ne_zero
end
end MassShell.CompositionAndTransport
