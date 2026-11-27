from fractions import Fraction as Q
from math import isqrt

S = 100_000

def lo(k):
    return Q(isqrt(k*S*S), S)

def hi(k):
    return lo(k) + Q(1, S)

s, t = lo(2), hi(2)
target = lambda n: 1 + Q(3, 2)*(hi(n)-s)

assert (4*Q(17, 12)**3)**2 <= 130
assert Q(256, 27)**2 <= 90 and 129 < 12**2
assert Q(3, 2)*s-1 > Q(3, 4)
assert Q(3, 2) > target(3)

a_hi = Q(3, 2) - s
b_hi = (Q(5, 2)*t-1) * hi(10) / 3
for n, a in [(10, Q(1117, 1000)), (90, Q(1097, 1000))]:
    assert a_hi * hi(n) + b_hi / lo(n) < a < Q(3, 2)*s - 1

for n in range(4, 10):
    d = n-1
    p_low = d*lo(2*d)/(d+2) + (1-t/(d+2))/hi(d)
    assert p_low > target(n)
