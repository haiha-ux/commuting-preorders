"""Exact numbers of commuting pairs, n <= 6, by orbits of the symmetric group.

Simultaneous relabelling of A and B preserves commutation, hence
    cio(n) = sum over isomorphism classes [A] of |orbit(A)| * #{B : AB = BA},
so only one representative per class is tested against all B.  The same is done on the
strict operators (quasi-orders on all n points) to get t(n).

The table is written as CSV only when --out is given.

Usage:  python -m counts.orbit_count [--n-max 6] [--workers K] [--out FILE.csv]
"""

from __future__ import annotations

import argparse
import csv
import multiprocessing as mp
import time
from fractions import Fraction
from itertools import permutations
from pathlib import Path

import numpy as np

from counts import reference
from counts.quasi_orders import (MAX_N, commute_fixed_points, operators, strict,
                                 tables)

BLOCK = 20_000  # operators B tested per vectorised step
_shared: dict = {}  # tables shared with forked workers


def canonical_keys(N: np.ndarray, n: int) -> np.ndarray:
    """Canonical key of each operator: minimum over all permutations p of the packed code
    of the relabelled neighbourhoods, (pN)[p(x)] = p(N[x]), at n bits per point."""
    best = np.full(len(N), np.iinfo(np.uint64).max, dtype=np.uint64)
    masks = np.arange(1 << n)
    for p in permutations(range(n)):
        relabel = np.zeros(1 << n, dtype=np.uint8)
        for i in range(n):
            relabel |= (((masks >> i) & 1) << p[i]).astype(np.uint8)
        key = np.zeros(len(N), dtype=np.uint64)
        for x in range(n):
            key |= relabel[N[:, x]].astype(np.uint64) << np.uint64(n * p[x])
        np.minimum(best, key, out=best)
    return best


def _count_for_representative(i: int) -> int:
    apply, fixed, n, count = _shared["apply"], _shared["fixed"], _shared["n"], _shared["count"]
    total = 0
    for start in range(0, count, BLOCK):
        b = np.arange(start, min(start + BLOCK, count))
        total += int(commute_fixed_points(apply, fixed, np.full(len(b), i), b, n).sum())
    return total


def count_commuting_pairs(N: np.ndarray, n: int, workers: int = 1) -> tuple[int, int]:
    """(number of ordered commuting pairs in N x N, number of isomorphism classes)."""
    apply, fixed = tables(N, n)
    _, first, size = np.unique(canonical_keys(N, n), return_index=True, return_counts=True)
    _shared.update(apply=apply, fixed=fixed, n=n, count=len(N))
    if workers > 1:
        with mp.get_context("fork").Pool(workers) as pool:
            per_rep = pool.map(_count_for_representative, [int(i) for i in first], chunksize=1)
    else:
        per_rep = [_count_for_representative(int(i)) for i in first]
    return sum(int(k) * b for k, b in zip(size, per_rep)), len(first)


def counts_for(n: int, workers: int = 1) -> dict[str, int]:
    """T(n), io(n), cio(n), t(n) for one n."""
    N = operators(n)
    top = strict(N)
    cio, _ = count_commuting_pairs(N, n, workers)
    t, _ = count_commuting_pairs(top, n, workers)
    return {"n": n, "T": len(top), "io": len(N), "cio": cio, "t": t}


def check_against_reference(row: dict[str, int]) -> None:
    n = row["n"]
    for key, table in (("T", reference.T), ("io", reference.IO),
                       ("cio", reference.CIO), ("t", reference.T_COMM)):
        assert row[key] == table[n], f"{key}({n}) = {row[key]}, expected {table[n]}"


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--n-max", type=int, default=6)
    ap.add_argument("--workers", type=int, default=mp.cpu_count())
    ap.add_argument("--out", type=Path, default=None, help="write the table as CSV")
    args = ap.parse_args()
    assert 1 <= args.n_max <= MAX_N

    print(f"workers: {args.workers}")
    rows = []
    for n in range(1, args.n_max + 1):
        start = time.time()
        row = counts_for(n, args.workers)
        check_against_reference(row)
        row["rho"] = row["t"] / row["T"] ** 2
        row["rho_io"] = row["cio"] / row["io"] ** 2
        rows.append(row)
        f = Fraction(row["cio"], row["io"] ** 2)
        print(f"n={n}: T={row['T']} io={row['io']} t={row['t']} cio={row['cio']} "
              f"rho={row['rho']:.4f} rho_io={f.numerator}/{f.denominator}={float(f):.4f} "
              f"({time.time() - start:.1f}s)")

    if args.out is None:
        return
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="") as fh:
        w = csv.writer(fh, lineterminator="\n")
        w.writerow(["n", "T", "io", "t", "cio", "rho", "rho_io"])
        for r in rows:
            w.writerow([r["n"], r["T"], r["io"], r["t"], r["cio"],
                        f"{r['rho']:.6f}", f"{r['rho_io']:.6f}"])
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
