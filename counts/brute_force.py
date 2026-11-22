"""Independent check of the counts for n <= 5 straight from the definitions.

Quasi-orders on subsets are enumerated as relations (reflexive and transitive on their
domain, nothing outside it) by testing every relation on n points, not through the
neighbourhood search of counts.quasi_orders.  Two operators A, B are declared to commute
when A(B(S)) = B(A(S)) for every subset S.  For quasi-orders on the whole set the
relational test R o S = S o R is compared with it as well.

Usage:  python -m counts.brute_force [--n-max 5]
"""

from __future__ import annotations

import argparse
from itertools import combinations

import numpy as np

from counts import reference
from counts.quasi_orders import commute_relational


def quasi_orders(k: int) -> np.ndarray:
    """All reflexive transitive relations on k points: boolean array (T(k), k, k)."""
    if k == 0:
        return np.zeros((1, 0, 0), dtype=bool)
    off = [(i, j) for i in range(k) for j in range(k) if i != j]
    out = []
    step = 1 << 20
    for start in range(0, 1 << len(off), step):
        code = np.arange(start, min(start + step, 1 << len(off)), dtype=np.int64)
        R = np.zeros((len(code), k, k), dtype=bool)
        for bit, (i, j) in enumerate(off):
            R[:, i, j] = (code >> bit) & 1
        for i in range(k):
            R[:, i, i] = True
        square = np.einsum("nij,njk->nik", R.astype(np.int8), R.astype(np.int8)) > 0
        out.append(R[~np.any(square & ~R, axis=(1, 2))])
    return np.concatenate(out)


def relations_on_subsets(n: int) -> np.ndarray:
    """Every quasi-order on every subset U, as a relation on n points (no loop outside U)."""
    out = []
    for k in range(n + 1):
        local = quasi_orders(k)
        for U in combinations(range(n), k):
            full = np.zeros((len(local), n, n), dtype=bool)
            idx = np.array(U, dtype=int)
            full[:, idx[:, None], idx[None, :]] = local
            out.append(full)
    return np.concatenate(out)


def interior_table(R: np.ndarray, n: int) -> np.ndarray:
    """table[i, S] = {x : x R x and every y with x R y lies in S}, subsets as bitmasks."""
    table = np.zeros((len(R), 1 << n), dtype=np.int64)
    for S in range(1 << n):
        outside = np.array([(S >> y) & 1 == 0 for y in range(n)])
        for x in range(n):
            ok = R[:, x, x] & ~np.any(R[:, x, :] & outside, axis=1)
            table[:, S] |= ok.astype(np.int64) << x
    return table


def count_commuting(table: np.ndarray) -> int:
    total = 0
    for a in range(len(table)):
        ab = table[a][table]  # A(B(S)) for every B
        ba = table[:, table[a]]  # B(A(S)) for every B
        total += int(np.all(ab == ba, axis=1).sum())
    return total


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--n-max", type=int, default=5)
    n_max = ap.parse_args().n_max
    for n in range(1, n_max + 1):
        R = relations_on_subsets(n)
        cio = count_commuting(interior_table(R, n))
        whole = R[np.all(R.diagonal(axis1=1, axis2=2), axis=1)]
        t = count_commuting(interior_table(whole, n))
        # relational criterion on all pairs of quasi-orders on the whole set
        t_rel = sum(int(commute_relational(np.broadcast_to(r, whole.shape), whole).sum())
                    for r in whole)
        print(f"n={n}: io={len(R)} T={len(whole)} cio={cio} t={t} t(relational)={t_rel}")
        assert (len(R), len(whole), cio, t) == (
            reference.IO[n], reference.T[n], reference.CIO[n], reference.T_COMM[n])
        assert t_rel == t
    print("brute force agrees with the published values and with the relational criterion")


if __name__ == "__main__":
    main()
