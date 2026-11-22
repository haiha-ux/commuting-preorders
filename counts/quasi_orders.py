"""Alexandrov interior operators on {0, ..., n-1} as quasi-orders on subsets.

An operator A is stored as an array N of n bitmasks: N[x] is the smallest A-open set
containing x, and N[x] = 0 when x is outside the domain U.  The quasi-order is
x <= y iff y in N[x], and A(S) is the union of the sets N[x] contained in S (N[x] != 0).
Operators with N[x] != 0 for all x ("strict") are the quasi-orders on the whole set.
Everything here is limited to n <= 6 (masks fit in uint8, fixed-point sets in uint64).
"""

from __future__ import annotations

from itertools import combinations

import numpy as np

MAX_N = 6


def topologies(k: int) -> np.ndarray:
    """All quasi-orders on k points as an array (T(k), k) of local neighbourhood masks."""
    found: list[tuple[int, ...]] = []
    chosen: list[int] = []

    def extend(x: int) -> None:
        if x == k:
            found.append(tuple(chosen))
            return
        for m in range(1 << k):
            if not (m >> x) & 1:
                continue
            # y in N(x) implies N(y) <= N(x), checked in both directions against earlier points
            if all(
                (not (m >> y) & 1 or chosen[y] & ~m == 0)
                and (not (chosen[y] >> x) & 1 or m & ~chosen[y] == 0)
                for y in range(x)
            ):
                chosen.append(m)
                extend(x + 1)
                chosen.pop()

    extend(0)
    return np.array(found, dtype=np.uint8).reshape(len(found), k)


def operators(n: int) -> np.ndarray:
    """All interior operators on n points: an array (io(n), n) of neighbourhood masks.

    Choose the domain U (k points), then a quasi-order on U.
    """
    assert 0 <= n <= MAX_N
    blocks = []
    for k in range(n + 1):
        local = topologies(k)
        for domain in combinations(range(n), k):
            to_global = np.zeros(1 << k, dtype=np.uint8)
            for mask in range(1 << k):
                to_global[mask] = sum(1 << domain[i] for i in range(k) if (mask >> i) & 1)
            block = np.zeros((len(local), n), dtype=np.uint8)
            for i, x in enumerate(domain):
                block[:, x] = to_global[local[:, i]]
            blocks.append(block)
    return np.concatenate(blocks)


def strict(N: np.ndarray) -> np.ndarray:
    """Rows of N whose domain is the whole set (quasi-orders on all n points)."""
    return N[np.all(N != 0, axis=1)]


def tables(N: np.ndarray, n: int) -> tuple[np.ndarray, np.ndarray]:
    """apply[f, S] = A_f(S) and fixed[f] = bitmask over S of the sets with A_f(S) = S."""
    apply = np.zeros((len(N), 1 << n), dtype=np.uint8)
    for S in range(1 << n):
        for x in range(n):
            nx = N[:, x]
            apply[:, S] |= np.where(nx & ~np.uint8(S) == 0, nx, 0).astype(np.uint8)
    fixed = np.zeros(len(N), dtype=np.uint64)
    for S in range(1 << n):
        fixed |= (apply[:, S] == S).astype(np.uint64) << np.uint64(S)
    return apply, fixed


def commute_fixed_points(apply, fixed, a: np.ndarray, b: np.ndarray, n: int) -> np.ndarray:
    """Boolean array: operators a[i], b[i] commute iff A(Fix B) <= Fix B and B(Fix A) <= Fix A."""
    sets = np.arange(1 << n, dtype=np.uint64)

    def one_way(a, b):
        fb = fixed[b][:, None]
        in_fb = (fb >> sets) & np.uint64(1)
        image_in_fb = (fb >> apply[a].astype(np.uint64)) & np.uint64(1)
        return np.all((in_fb == 0) | (image_in_fb == 1), axis=1)

    return one_way(a, b) & one_way(b, a)


def commute_relational(R: np.ndarray, S: np.ndarray) -> np.ndarray:
    """Whether the relations R[i] and S[i] commute as relations: R o S = S o R.

    (x, z) is in R o S iff x R y and y S z for some y.  R and S are boolean arrays of
    shape (m, n, n); for quasi-orders on the whole set this is the commutation of the
    corresponding interior operators.
    """
    r, s = R.astype(np.int16), S.astype(np.int16)
    return np.all((r @ s > 0) == (s @ r > 0), axis=(1, 2))
