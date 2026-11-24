# Mass-shell factorisation in Lean

This repository formalises selected arguments from Mark Everitt's *Quantum Mechanics as a Relativistic Statistical Theory* in Lean 4, using Mathlib. The equation and ansatz numbers in the source refer to the manuscript dated 14 October 2026. [Read the public preprint on arXiv](https://arxiv.org/abs/2608.29353).

## Reading the argument

Start with `theorem_minimal_argument_from_field_ansatze` in [MassShell.lean](MassShell.lean). Its hypotheses state the physical assumptions, and its proof shows where each enters. Definitions beginning with `ansatz_` identify modelling assumptions.

1. The linear factor must reproduce the Minkowski square off shell. Polarisation gives the Clifford relations. `theorem_four_is_minimal` proves that four is the least positive dimension of a complex matrix representation satisfying the square condition.
2. With this matrix structure in place, the paper asks how two matrix-valued phase-space fields compose. `theorem_exists_unique_product_from_field_ansatze` shows that the formal Moyal product satisfies the stated composition assumptions and is unique under them. Compatibility with the Dirac adjoint makes the first coefficient purely imaginary. The signed Weyl normalisation fixes it at $i/2$.
3. Preservation of the mass-shell constraint then restricts the allowed ensembles. For the free case, `theorem_free_sector_transport_from_preservation` derives the transport equation for the projected internal density. For singular ensembles, `theorem_distribution_bimodule_associativity` establishes associativity of the left and right actions with one distributional argument.

The product is formal in the deformation parameter. The distributional results include an explicit nonzero free solution. Existence of an all-orders continuation for arbitrary initial data remains open in this formalisation.

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
