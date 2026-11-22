"""Rates of the counting classes and conditions (P1)-(P4) for the parameter choice of Appendix B.

The parameters (delta, rho, sigma, psi, eta, lam, s, k, gamma1, gamma2) are fixed below.
For each class A, B, D, E, F, G, H, I2, J, K, L, M the exponential rate is evaluated at
50 digits; every rate must be at least 3e-11 and every listed inequality must hold.

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
rho = mpf("1.45e-10")
sigma = mpf("1.45e-10")
psi = mpf("3e-11")
eta = mpf("5.2e-8")
lam = mpf("6.2e-5")
s = mpf("1.35e-3")
k = mpf("5.1e10")
gamma1 = mpf(10) ** 4
gamma2 = mpf("2e12")

t0 = 2 * rho + 2 * sigma + psi
tau = t0 + 54 * eta
theta = delta / 2 + t0 + tau
w = mpf(1) / 2 + theta

rates = {
    "A": mpf(1) / 4,
    "B": delta / 2,
    "D": k * delta / 2 - mpf(3) / 2,
    "E": mpf(6),
    "F": C3 * rho - delta / 2,
    "G": k * (C3 * sigma - delta / 2) - 1 - delta / 2,
    "H": C3 * eta - delta - 2 * t0 * LG3 - h(t0),
    "I2": mpf(1) / 64 - mpf(1) / 300 - 2 * theta - tau - tau * LG3 - h(tau) + s - w * h(s / w),
    "J": 1 - w * LG3 - 2 * tau * LG3 - h(tau),
    "K": mpf(1) / 64 - tau - h(tau) - 2 * tau * LG3,
    "L": lam - h(tau) - tau * LG3,
    "M": mpf(1) / 2 - h(2 * lam) - 2 * lam,
}

conditions = {
    "P1": [
        ("gamma1 > 29", gamma1 > 29),
        ("1/128 - 29/gamma1 > 0", mpf(1) / 128 - 29 / gamma1 > 0),
        ("gamma2 >= 56/psi", gamma2 >= 56 / psi),
    ],
    "P2": [
        ("theta < 1/300", theta < mpf(1) / 300),
        ("(1/2 - theta)/3 >= eta", (mpf(1) / 2 - theta) / 3 >= eta),
        ("(1/2 - delta/2 - t0 - 52 eta)/3 >= eta",
         (mpf(1) / 2 - delta / 2 - t0 - 52 * eta) / 3 >= eta),
    ],
    "P3": [
        ("theta <= lam", theta <= lam),
        ("lam <= 1/4 - theta/2", lam <= mpf(1) / 4 - theta / 2),
    ],
    "P4": [
        ("s <= (1/64 - tau)/2", s <= (mpf(1) / 64 - tau) / 2),
        ("1/64 - t0 > 1/65", mpf(1) / 64 - t0 > mpf(1) / 65),
    ],
}


def main() -> None:
    print("t0", nstr(t0, 8), "tau", nstr(tau, 8), "theta", nstr(theta, 8))
    print("class rates")
    for name, rate in rates.items():
        print(f"  {name:3s} {nstr(rate, 8)}")
    print("conditions")
    for name, items in conditions.items():
        for text, ok in items:
            print(f"  {name}: {text}: {ok}")
    slack = s * (mpf(1) / 300 - theta) - tau * LG3
    print("s (1/300 - theta) - tau log2(3):", nstr(slack, 8))
    smallest = min(rates.values())
    print("smallest rate", nstr(smallest, 8))
    assert smallest >= MIN_RATE, "a class rate is below 3e-11"
    assert all(ok for items in conditions.values() for _, ok in items), "a condition fails"
    print("all rates >= 3e-11 and all conditions hold")


if __name__ == "__main__":
    main()
