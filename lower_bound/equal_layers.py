"""Pairs of posets with the same layers (the family behind the lower bound).

(1) F(n), the number of ordered pairs of standard three-layer posets with the same layers,
    from the closed formula; for n <= 6 it is also counted directly in the list of all
    operators, and every such pair is tested for commutation (non-commuting pairs: 0).
(2) The lemma "posets with a common layering commute" is tested on random layered posets
    with 2 to 5 layers, and exhaustively for all layerings on n = 5 points.

A layering of a poset is a map l with (L1) x < y implies l(x) < l(y), and
(L2) l(x) + 2 <= l(y) implies x < y.  Given l, the posets with layering l are exactly
the relations "equal, or l-gap >= 2, or any chosen subset of the gap-1 pairs".

Usage:  python -m lower_bound.equal_layers [--out results/equal_layers.csv]
"""

from __future__ import annotations

import argparse
import csv
from itertools import product
from math import factorial
from pathlib import Path

import numpy as np

from counts import reference
from counts.quasi_orders import (commute_fixed_points, commute_relational,
                                 operators, tables)


def equal_layer_pairs(n: int) -> int:
    """F(n) = sum over k1,k3 >= 1, k2 >= 0 of n!/(k1! k2! k3!) * ((2^k1-1)(2^k3-1))^(2 k2)."""
    total = 0
    for k1 in range(1, n):
        for k3 in range(1, n - k1 + 1):
            k2 = n - k1 - k3
            g = ((1 << k1) - 1) * ((1 << k3) - 1)
            total += factorial(n) // (factorial(k1) * factorial(k2) * factorial(k3)) * g ** (2 * k2)
    return total


def three_layer_signature(N: np.ndarray, n: int) -> np.ndarray:
    """Layer partition (Min | Max << n) of the standard three-layer posets among the rows
    of N, and -1 for the other rows.

    Standard three-layer poset: a partial order on all points with L1 = Min and L3 = Max
    non-empty and disjoint, L2 the remaining points forming an antichain between them, and
    every point of L1 below every point of L3.  The partition is determined by the poset.
    """
    N = N.astype(np.int64)
    m = len(N)
    everything = (1 << n) - 1
    above = np.stack([N[:, x] & ~(1 << x) for x in range(n)], 1)  # y > x
    below = np.zeros((m, n), np.int64)
    for y in range(n):
        for x in range(n):
            if x != y:
                below[:, x] |= ((N[:, y] >> x) & 1) << y  # y < x
    ok = np.all(((N >> np.arange(n)) & 1) == 1, axis=1)  # reflexive everywhere
    ok &= np.all((below & above) == 0, axis=1)  # antisymmetric
    low = ((below == 0).astype(np.int64) << np.arange(n)).sum(1)
    high = ((above == 0).astype(np.int64) << np.arange(n)).sum(1)
    mid = everything & ~low & ~high
    ok &= (low & high) == 0
    for x in range(n):
        in_mid, in_low = (mid >> x) & 1 == 1, (low >> x) & 1 == 1
        ok &= ~in_mid | (((above[:, x] & ~high) == 0) & ((below[:, x] & ~low) == 0))
        ok &= ~in_low | ((above[:, x] & high) == high)
    return np.where(ok, low | (high << n), -1)


def same_layer_pairs_direct(n: int) -> tuple[int, int, int]:
    """(ordered pairs with the same layers, how many do not commute, cio(n))."""
    N = operators(n)
    apply, fixed = tables(N, n)
    sig = three_layer_signature(N, n)
    pairs = failures = 0
    for s in np.unique(sig[sig >= 0]):
        members = np.flatnonzero(sig == s)
        for a in members:
            ok = commute_fixed_points(apply, fixed, np.full(len(members), a), members, n)
            pairs += len(members)
            failures += int((~ok).sum())
    return pairs, failures, reference.CIO[n]


def layered_posets(layer: np.ndarray) -> np.ndarray:
    """All posets (boolean matrices R[x, y] = x <= y) having the layering `layer`."""
    n = len(layer)
    gap = layer[None, :] - layer[:, None]
    adjacent = np.argwhere(gap == 1)
    code = np.arange(1 << len(adjacent))
    R = np.broadcast_to((gap >= 2) | np.eye(n, dtype=bool), (len(code), n, n)).copy()
    for bit, (i, j) in enumerate(adjacent):
        R[:, i, j] = (code >> bit) & 1
    return R


def check_exhaustive(n: int) -> tuple[int, int]:
    """Every layering l: Omega -> {0..n-1} (up to translation) and every ordered pair of
    posets with that layering; returns (pairs tested, pairs not commuting)."""
    tested = bad = 0
    for layer in product(range(n), repeat=n):
        if min(layer) != 0:
            continue
        P = layered_posets(np.array(layer))
        m = len(P)
        ok = commute_relational(np.repeat(P, m, axis=0), np.tile(P, (m, 1, 1)))
        tested += m * m
        bad += int((~ok).sum())
    return tested, bad


def check_random(trials: int, seed: int = 1) -> tuple[int, int]:
    """Random layerings with 2 to 5 layers on 6..12 points and random posets on them."""
    rng = np.random.default_rng(seed)
    bad = 0
    for _ in range(trials):
        n, k = int(rng.integers(6, 13)), int(rng.integers(2, 6))
        layer = rng.integers(0, k, size=n)
        gap = layer[None, :] - layer[:, None]
        pair = []
        for _ in range(2):
            R = (gap >= 2) | np.eye(n, dtype=bool) | ((gap == 1) & (rng.random((n, n)) < 0.5))
            pair.append(R[None])
        bad += int(not commute_relational(*pair)[0])
    return trials, bad


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--out", type=Path, default=Path("results/equal_layers.csv"))
    args = ap.parse_args()

    rows = []
    print("n | F(n) | direct count | non-commuting | cio(n)")
    for n in range(2, 13):
        f = equal_layer_pairs(n)
        if n <= 6:
            direct, bad, cio = same_layer_pairs_direct(n)
            assert direct == f and bad == 0, (n, f, direct, bad)
            rows.append([n, f, direct, bad, cio])
            print(f"{n} | {f} | {direct} | {bad} | {cio}")
        else:
            rows.append([n, f, "", "", ""])
            print(f"{n} | {f} | - | - | -")
    tested, bad = check_exhaustive(5)
    print(f"exhaustive n=5: {tested} pairs with a common layering, {bad} not commuting")
    assert bad == 0
    tested, bad = check_random(2000)
    print(f"random layered posets (6..12 points, 2..5 layers): {tested} pairs, {bad} not commuting")
    assert bad == 0

    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="") as fh:
        w = csv.writer(fh, lineterminator="\n")
        w.writerow(["n", "F", "same_layer_pairs_direct", "non_commuting", "cio"])
        w.writerows(rows)
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
