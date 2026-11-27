"""Readable cross-check of the finite arithmetic encoded in SmallChunk*.lean."""
from fractions import Fraction
from math import isqrt

S = 100_000


def lo(k):
    return Fraction(isqrt(k * S * S), S)


def hi(k):
    return lo(k) + Fraction(1, S)


checks = []
for n in range(3, 91):
    for p in range(1 if n == 3 else n // 2 + 1):
        d = n - p if p else n - 1
        low = (n-p)*lo(2*d)/(d+2) + p*(1-hi(2)/(d+2))/hi(d)
        high = 1 + Fraction(3, 2)*(hi(n)-lo(2))
        assert low > high, (n, p)
        checks.append((low-high, n, p))

assert len(checks) == 2111
gap, n, p = min(checks)
print(f"{len(checks)} cases; minimum certified gap {gap} at n={n}, p={p}.")
