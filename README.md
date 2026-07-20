[![Logo for Axiom Math](logo.svg)](https://axiommath.ai/)

# Parity of the Partition Function in Quadratic Progressions

These files accompany the paper **[TODO]**.

The formal proofs provided in this work were developed and verified using **Lean 4.28.0 + mathlib 4.28.0**. Compatibility with earlier or later versions is not guaranteed due to the evolving nature of the Lean 4 compiler and mathlib.

## Input files

- [`KeyFormulasPartitionFunction.tex`](PartitionParity/Input/KeyFormulasPartitionFunction.tex): auxiliary key formulas
- [`PofNParity.tex`](PartitionParity/Input/PofNParity.tex): an early draft of the paper
- [`task.md`](PartitionParity/Input/task.md): natural language instructions for AxiomProver

## Output files

- [`problem.lean`](PartitionParity/Output/problem.lean): translation of the problem statement into formal language (Lean)
- [`solution.lean`](PartitionParity/Output/solution.lean): solution in formal language (Lean)

## Verification

One can verify that each `problem.lean` and `solution.lean` are compatible
using `verify.py`, which calls [Axle's `verify_proof`](https://axle.axiommath.ai/):

```bash
python3 verify.py
okay=True (passed)
```

This is expected to complete very quickly, as the results are cached by Axle.
To bypass this, pass `--no-cache` to the call, which will force Axle to recompute everything,
at the cost of a slower time:

```bash
python3 verify.py --no-cache
okay=True (passed)
```

The files have been verified locally via the [Comparator](https://github.com/leanprover/comparator).

## License

This repository uses the MIT License. See [LICENSE](LICENSE) for details.
