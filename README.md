# Mass-shell factorisation in Lean

This repository formalises selected arguments from Mark Everitt's *Quantum Mechanics as a Relativistic Statistical Theory* in Lean 4, using Mathlib. The equation and ansatz numbers in the source refer to the manuscript dated 14 October 2026. [Read the public preprint on arXiv](https://arxiv.org/abs/2608.29353).

Note: most of this material in this repo is AI generated from the paper. The first step was to re-express using ChatGPT the paper in a theorem proof (see [mass_shell_argument.pdf](mass_shell_argument.pdf)) format and check this structure with a flow diagram (see [mass_shell_flow.pdf](mass_shell_flow.pdf)). Then numerous iterations of generating Lean code, inspecting it for obvious missing martial or other issues were then used until this version, deemed good enough to share, was created.

As this stage it is an intellectual curiosity and I do not yet claim it substantiated the claims made in my original manuscript.

## Reading the argument

Start with `theorem_minimal_argument_from_field_ansatze` in [MassShell.lean](MassShell.lean). It is a conditional implication: the leading state is assumed to lie in the selected sector, the commutator hierarchy is assumed at every order, and the left zero-sector equation is assumed at every order. The theorem identifies the product and derives a first-order compatibility condition and the right equation under those premises. It does not construct a state satisfying them. Definitions beginning with `ansatz_` identify modelling assumptions.

1. The linear factor must reproduce the Minkowski square off shell. Polarisation gives the Clifford relations. `theorem_four_is_minimal` proves that four is the least positive dimension of a complex matrix representation satisfying the square condition.
2. With this matrix structure in place, the paper asks how two matrix-valued phase-space fields compose. `theorem_exists_unique_product_from_field_ansatze` shows that the formal Moyal product satisfies the stated composition assumptions and is unique under them. These premises include finite local differential form, dimensional balance, canonical covariance, associativity, matrix neutrality, adjoint compatibility, and a signed Weyl response of $1/2$ for a unit canonical pair. The final scale is therefore supplied by an explicit normalisation assumption.
3. Preservation of the mass-shell constraint restricts the allowed ensembles. For the free case, `theorem_free_sector_transport_from_preservation` derives a necessary transport equation for the projected internal density. For singular ensembles, `theorem_distribution_bimodule_associativity` establishes associativity of the left and right actions with one distributional argument. `theorem_homogeneous_free_all_order_continuation` constructs an all-order continuation for any spacetime-homogeneous distribution satisfying both ordinary free-shell equations. `theorem_free_shell_solution_family` supplies such distributions for every massive on-shell momentum and every internal matrix after sector projection.

## Existence for general massive free data

Let `F` be a matrix of distributions on full phase space, let `H = K(p) − mI` be the free generator, and take nonzero mass `m`. Then `F` occurs as the leading term of a formal solution of **both** Moyal equations exactly when

1. `H F = 0` and `F H = 0` under ordinary distributional multiplication, and
2. `p^μ ∂F/∂x^μ = 0` entrywise, in the sense of distributions.

The datum may vary in spacetime and may occupy either or both massive sheets. It is specified on full phase space. Given compatible data, the proof constructs the even coefficients of an auxiliary distribution by a recurrence involving the momentum Euler operator and the spacetime wave operator. Applying the two shifted Dirac factors produces a formal solution with the prescribed leading term. Conversely, subtracting the squared left and right equations gives free transport. Each coefficient requires finitely many derivatives. For nonzero leading data, multiplying a solution by `1 + cℏ` gives different continuations as `c` varies.

The Lean statement is `MassShell.CompositionAndTransport.free_continuation_iff` in [FreeShellExistence.lean](FreeShellExistence.lean). The [mathematical proof](FreeShellExistence.pdf) gives the explicit recurrence and its derivation. The theorem concerns the free generator and a formal deformation parameter.

The smooth-state theorem should not be read as a nonzero smooth free-shell existence result. For the free generator, the exact zeroth-order shell equation makes a smooth leading state vanish off the shell, where the generator is invertible. Continuity then makes it vanish on the shell. Nonzero free-shell states require the distributional setting used by the solution family.

## Checking the proof

With [Elan](https://lean-lang.org/install/) installed, open a terminal in the directory containing `lakefile.toml` and run:

```sh
lake exe cache get
lake build
```

The project pins Lean and Mathlib to version 4.36.0. To inspect the hypotheses and proof steps interactively, open this directory in VS Code with the Lean 4 extension and select `MassShell.lean`.

## Citation

If you use this formalisation in research, please cite the accompanying paper:

Mark Everitt (2026), *Quantum Mechanics as a Relativistic Statistical Theory: A Mass-Shell Factorisation Approach*. [arXiv:2608.29353](https://arxiv.org/abs/2608.29353).

GitHub's **Cite this repository** uses the preferred citation in [CITATION.cff](CITATION.cff).

## Licence

The Lean source and accompanying project files are available under the [Apache License 2.0](LICENSE). The linked manuscript retains its own publication terms.
