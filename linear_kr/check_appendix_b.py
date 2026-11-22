"""Rates of the counting classes and conditions (P1)-(P6) for the parameter choice of Appendix B.

The parameters are fixed below and the exponential rate of each class A, B, D, E, F, G, H,
I2, J, K, L, M is evaluated at 50 digits.  (P1)-(P4) are inequalities between the
parameters, (P5) says gap := varsigma (1/300 - theta) - xi log2(3) > 0, and (P6) says that
every class rate is at least 3e-11.  All six must hold.

Names follow the appendix; the only differences are
    lam      for lambda (a Python keyword)
    varsigma for the symbol written as a final sigma
    I2       for the class written with a double prime
    g1, g2   for the two constants of the appendix
    LG3      for log2(3), C3 for 2 - log2(3), t0 for 2 phi + 2 sigma + psi

Usage:  python -m linear_kr.check_appendix_b
"""

from mpmath import log, mp, mpf, nstr

mp.dps = 50
MIN_RATE = mpf("3e-11")


def log2(x):
    return log(x, 2)


def h(x):
    """Binary entropy."""
    x = mpf(x)
    return -x * log2(x) - (1 - x) * log2(1 - x)


LG3 = log2(3)
C3 = 2 - LG3
delta = mpf("6e-11")
phi = mpf("1.45e-10")
sigma = mpf("1.45e-10")
psi = mpf("3e-11")
nu = mpf("5.2e-8")
lam = mpf("6.2e-5")
varsigma = mpf("1.35e-3")
k = mpf("5.1e10")
g1 = mpf(10) ** 4
g2 = mpf("2e12")

t0 = 2 * phi + 2 * sigma + psi
xi = t0 + 54 * nu
theta = delta / 2 + t0 + xi
w = mpf(1) / 2 + theta

rates = {
    "A": mpf(1) / 4,
    "B": delta / 2,
    "D": k * delta / 2 - mpf(3) / 2,
    "E": mpf(6),
    "F": C3 * phi - delta / 2,
    "G": k * (C3 * sigma - delta / 2) - 1 - delta / 2,
    "H": C3 * nu - delta - 2 * t0 * LG3 - h(t0),
    "I2": mpf(1) / 64 - mpf(1) / 300 - 2 * theta - xi - xi * LG3 - h(xi) + varsigma - w * h(varsigma / w),
    "J": 1 - w * LG3 - 2 * xi * LG3 - h(xi),
    "K": mpf(1) / 64 - xi - h(xi) - 2 * xi * LG3,
    "L": lam - h(xi) - xi * LG3,
    "M": mpf(1) / 2 - h(2 * lam) - 2 * lam,
}

conditions = {
    "P1": [
        ("g1 > 29", g1 > 29),
        ("1/128 - 29/g1 > 0", mpf(1) / 128 - 29 / g1 > 0),
        ("g2 >= 56/psi", g2 >= 56 / psi),
    ],
    "P2": [
        ("theta < 1/300", theta < mpf(1) / 300),
        ("(1/2 - theta)/3 >= nu", (mpf(1) / 2 - theta) / 3 >= nu),
        ("(1/2 - delta/2 - t0 - 52 nu)/3 >= nu",
         (mpf(1) / 2 - delta / 2 - t0 - 52 * nu) / 3 >= nu),
    ],
    "P3": [
        ("theta <= lam", theta <= lam),
        ("lam <= 1/4 - theta/2", lam <= mpf(1) / 4 - theta / 2),
    ],
    "P4": [
        ("varsigma <= (1/64 - xi)/2", varsigma <= (mpf(1) / 64 - xi) / 2),
        ("1/64 - t0 > 1/65", mpf(1) / 64 - t0 > mpf(1) / 65),
    ],
}


def main() -> None:
    print("t0", nstr(t0, 8), "xi", nstr(xi, 8), "theta", nstr(theta, 8))
    print("class rates")
    for name, rate in rates.items():
        print(f"  {name:3s} {nstr(rate, 8)}")
    print("conditions")
    for name, items in conditions.items():
        for text, ok in items:
            print(f"  {name}: {text}: {ok}")
    gap = varsigma * (mpf(1) / 300 - theta) - xi * LG3
    print("(P5) gap = varsigma (1/300 - theta) - xi log2(3) =", nstr(gap, 8))
    smallest = min(rates.values())
    print("(P6) smallest class rate =", nstr(smallest, 8))
    assert all(ok for items in conditions.values() for _, ok in items), "(P1)-(P4) fail"
    assert gap > 0, "(P5) fails"
    assert smallest >= MIN_RATE, "(P6) fails"
    print("(P1)-(P6) hold")


if __name__ == "__main__":
    main()
