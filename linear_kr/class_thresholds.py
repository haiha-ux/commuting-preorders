"""Size thresholds of the counting classes at the exponent c' = 2.9e-11.

For each class with rate r (rounded down from the output of check_appendix_b), the
threshold is the first n, on the grid 2, 3, 4.5, ... (factor 1.5), with
    (r - c') n > overhead(class, n) + 4,
where the overhead collects the lower-order terms of the class count.  The largest
threshold must lie between 1e27 and 1e28.

Usage:  python -m linear_kr.class_thresholds
"""

from math import log2

C_PRIME = 2.9e-11
K = 5.1e10
GAMMA1 = 1e4
GAMMA2 = 2e12
D = K + 1
LG3 = log2(3)

RATES = {"B": 3e-11, "D": 0.03, "F": 3.018e-11, "G": 0.5392, "H": 3.5864e-11,
         "L": 1.7e-6, "J": 0.207, "K": 0.0155, "I2": 1.086e-4, "M": 0.498}


def overhead(cls: str, n: float) -> float:
    ln = log2(n)
    if cls in ("B", "F"):
        return (K + 4) * ln + GAMMA1 * (ln + LG3) + 1e3
    if cls in ("D", "G"):
        return D * D * GAMMA1 * LG3 + D * GAMMA1 * ln + D * D / 4 + (K + 4) * ln
    if cls == "H":
        return GAMMA2 * (ln + 2 * LG3) + 2 * GAMMA2 + 65 + 1e3 * ln
    return 1e6 * ln


def threshold(cls: str, rate: float) -> float:
    n = 2.0
    while (rate - C_PRIME) * n <= overhead(cls, n) + 4:
        n *= 1.5
    return n


def main() -> None:
    thresholds = {cls: threshold(cls, rate) for cls, rate in RATES.items()}
    for cls, n in thresholds.items():
        print(f"{cls:3s} {n:.2e}")
    largest = max(thresholds.values())
    print(f"largest threshold {largest:.2e}")
    assert 1e27 < largest < 1e28, "largest threshold outside (1e27, 1e28)"


if __name__ == "__main__":
    main()
