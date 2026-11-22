# Companion code: commuting finite quasi-orders

Code and Lean files for the paper *The probability that two random finite topologies commute is $2^{-\Theta(n)}$*.
The repository computes the exact numbers of commuting pairs of quasi-orders and of Alexandrov interior operators for $n\le 6$, checks them independently, tests the equal-layers family behind the lower bound, and formalises the structural statements in Lean 4 without Mathlib.

## Reproducing the paper

Commands are run from the repository root after the setup below. Times are wall-clock on a 28-core machine.

| Paper | Command | Expected output | Time |
|---|---|---|---|
| Section 4, exact counts, $n\le5$ | `python -m counts.orbit_count --n-max 5` | rows for $n=1..5$, e.g. `n=5: T=6942 io=9053 t=9545484 cio=14681479`; no file is written | 1 s |
| Section 4, Table 1, $n\le6$ | `python -m counts.orbit_count --n-max 6 --out results/counts.csv` | adds `n=6: T=209527 io=257151 t=3898813457 cio=5478474381` and writes `results/counts.csv`; $c=4,41,1179,86342,14681479,5478474381$ and $t=1,16,577,49871,9545484,3898813457$ are asserted | about 3 min (about 40 CPU-minutes on one core, `--workers 1`) |
| Section 4, independent check, $n\le5$ | `python -m counts.brute_force` | same $\mathrm{io},T,\mathrm{cio},t$ for $n\le5$ from the definition $A(B(S))=B(A(S))$, and $t$ again from $R\circ S=S\circ R$; last line `brute force agrees ...` | 30 s |
| Section 3, Proposition on the criterion | same two commands | the fixed-point test (orbit method) and the relational test (brute force) give identical counts | |
| Section 7 and Section 8, equal layers, $F(n)$ | `python -m lower_bound.equal_layers` | `F(n)` = 242, 9300, 1032602 for $n=4,5,6$, equal to the direct count with 0 non-commuting pairs; 0 failures in the exhaustive $n=5$ and random layered-poset checks; writes `results/equal_layers.csv` | 3 s |
| Appendix B, parameter choice and class thresholds | `python -m linear_kr.check_appendix_b` and `python -m linear_kr.class_thresholds` | all class rates at least `3e-11` and conditions (P1)-(P4) true (`all rates >= 3e-11 and all conditions hold`); largest class threshold `1.75e+27`, asserted in (1e27, 1e28) | under 1 s each |
| Section 2 and Section 3, Lean statements | `cd lean && lake build` | `Build completed successfully`; no `sorry` | under 1 min |

In the tables, `T` is the number of quasi-orders, `io` the number of interior operators, `t` and `cio` the numbers of ordered commuting pairs of quasi-orders and of interior operators, `rho = t/T^2` and `rho_io = cio/io^2`.

## Setup

```
python -m venv .venv && . .venv/bin/activate
pip install -r requirements.txt     # numpy, mpmath
```

Python 3.10 or later. The orbit count uses `fork` multiprocessing (Linux, macOS); `--workers` sets the number of processes (default: all cores). The programs are limited to $n\le6$.
For Lean install [elan](https://github.com/leanprover/elan); `lean/lean-toolchain` pins `leanprover/lean4:v4.34.0` and the project needs no other dependency.

## Method

An operator is stored by the sets $N(x)$ (smallest open set containing $x$, empty outside the domain); quasi-orders on subsets and operators correspond as in the paper. `counts/quasi_orders.py` enumerates them and tests commutation through fixed points. Simultaneous relabelling preserves commutation, so `counts/orbit_count.py` tests one representative per isomorphism class (904 classes at $n=6$) against all operators and weights it by the orbit size. `counts/brute_force.py` shares no enumeration code with it and works from the definitions. `lower_bound/equal_layers.py` counts ordered pairs of three-layer posets with the same layers by the closed formula and by direct search, and checks the lemma that posets with a common layering commute.

## Lean

`lean/CommutingPreorders/` is a self-contained Lake project (no Mathlib, no `sorry`). Subsets are predicates on a type, and a relation `le` defines the interior operator `intr le S`, the set of `x` with `le x x` whose neighbourhood `{y | le x y}` lies in `S`.

| File | Theorems |
|---|---|
| `Witness.lean` | `witness_noncommute`: a witness forces `A(B(S)) != B(A(S))` for some `S` (any relations, no transitivity) |
| `Representation.lean` | `interior_is_intr`: a contracting, meet-preserving, idempotent operator equals `intr` of its quasi-order; `intr_is_interior`: the converse for transitive relations |
| `Commutation.lean` | `commute_iff_relcomp`: commutation of `intr` operators iff condition C holds in both directions; `commute_iff_relcomp_refl`: the case of reflexive relations; `commute_iff_preorder`: the criterion for two interior operators and their quasi-orders |

The bijection between operators and quasi-orders is not formalised as a bijection.

## Licence and citation

Code: MIT, see `LICENSE`. The data in `results/*.csv`: CC BY 4.0. Citation metadata: `CITATION.cff`.
