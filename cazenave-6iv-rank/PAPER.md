# A Randić lower bound in terms of adjacency rank

Let \(G\) be a finite simple connected graph on \(n\ge2\) vertices, with degree function \(d_G\) and real adjacency matrix \(A\). Set \(r=\operatorname{rank}_{\mathbb R}(A)\), let
\[
R(G)=\sum_{uv\in E(G)}\frac{1}{\sqrt{d_G(u)d_G(v)}},
\qquad
F(t)=1+\frac32(\sqrt t-\sqrt2).
\]
We give a proof of \(R(G)\ge F(r)\), the second inequality in [Cazenave's Conjecture 6(iv)](https://arxiv.org/abs/2611.03879v1). Equality holds exactly for \(K_2\).

## Large order: the rank witness

A real symmetric rank-\(r\) matrix has a nonsingular principal \(r\times r\) submatrix. For instance, factor it as \(X\Lambda X^{\mathsf T}\) by choosing the nonzero eigenspaces and select \(r\) independent rows of \(X\). On the corresponding set \(S\), a nonzero term of the determinant expansion of \(A[S,S]\) supplies a permutation \(\pi\) with \(v\sim\pi(v)\) for every \(v\in S\).

Put \(x_v=\sqrt{d_G(v)}\) and \(B=\sqrt{n-1}\). In the oriented-edge sum \(2R(G)\), at each \(v\in S\) separately keep the term \(1/(x_vx_{\pi(v)})\); every other term at \(v\) is at least \(1/(Bx_v)\). Outside \(S\), the sum at \(v\) is at least \(x_v/B\ge1/B\). Consequently,
\[
2R(G)\ge
\sum_{v\in S}\left(\frac1{x_vx_{\pi(v)}}+\frac{x_v-1/x_v}{B}\right)
+\frac{n-r}{B}.
\]
Since \(\pi\) is a permutation, split the positive \(x_v/B\) sum evenly between \(x_v/(2B)\) and \(x_{\pi(v)}/(2B)\). Their product with \(1/(x_vx_{\pi(v)})\) is \(1/(4B^2)\). By AM–GM and \(x_v\ge1\),
\[
R(G)\ge \frac B2+\frac1{2B}+\frac rB\left(\frac32(B/4)^{1/3}-1\right).
\]
For \(n\ge131\), \(B\ge4(17/12)^3\), so the bracket is at least \(9/8\). By completing a square,
\[
B/2+9r/(8B)-\tfrac32\sqrt r
=\frac{(B-\tfrac32\sqrt r)^2}{2B}\ge0.
\]
For \(91\le n\le130\), \(B\ge256/27\) and \(B<12\); the bracket is at least \(1\), and
\[
B/2+r/B-\tfrac32\sqrt r+B/16
=\frac{(\sqrt r-3B/4)^2}{B}\ge0.
\]
Thus this range gives \(R(G)>\tfrac32\sqrt r-3/4>F(r)\). The range \(n\ge131\) is strict as well, since \(\tfrac32\sqrt r>F(r)\).

## Small order: distinct leaf supports

If two leaves share a neighbour, delete one. The graph stays connected, and subtracting the other leaf's identical row and column shows that adjacency rank is unchanged. At their common neighbour of degree \(k\), the deleted edge has weight \(1/\sqrt k\), while each of the remaining \(k-1\) incident edges gains at most \(1/\sqrt{k-1}-1/\sqrt k\). Hence \(R\) decreases by at least \(\sqrt k-\sqrt{k-1}>0\).

After exhausting these deletions, \(K_2\) gives \(r=2,R=1\). Every remaining leaf has a distinct nonleaf neighbour. Writing \(p\) for the number of leaves, \(2p\le n\); every vertex is adjacent to at most one leaf, so \(\Delta\le n-p\). Let \(d=n-p\) when \(p>0\), and \(d=n-1\) when \(p=0\). Put
\[
c=\frac{\sqrt{2d}}{d+2},\qquad b=\frac{1}{\sqrt d}-\frac{c}{d}.
\]
For an edge between nonleaves, charge \(c/d_G(v)\) to each endpoint \(v\). This does not exceed the weight of the edge: the ratio of the larger degree root to the smaller is at most \(\sqrt{d/2}\), and \(z+1/z\) increases for \(z\ge1\). For a leaf edge, charge \(b\) to the leaf and \(c/d_G(v)\) to its support \(v\). To check feasibility, put \(x=\sqrt{d_G(v)}\) and \(T=\sqrt d\). The slack is
\[
(1/x-c/x^2)-(1/T-c/T^2)
=\frac{(T-x)[xT-c(x+T)]}{x^2T^2}\ge0,
\]
since \(c\le1/2\) and \(xT\ge\max(x,T)\). Summing gives
\[
R(G)\ge(n-p)c+pb.
\]

## Checking the small-order inequality without a table

For real \(d\ge2\), write \(f(d)=\sqrt2 d^{3/2}/(d+2)\) and \(g(d)=(1-\sqrt2/(d+2))/\sqrt d\). For \(p\ge1\) the charge is \(f(d)+(n-d)g(d)\). It decreases in \(d\) on \([2,n-1]\): \(g'(d)<0\), as \((d+2)^2>\sqrt2(3d+2)\), and \(f'(d)-g(d)+g'(d)<0\). The latter sign is equivalent to positivity of
\[
(2d+1)(d+2)^2-\sqrt2(d^3+8d^2+7d+2).
\]
Writing \(d=2+y\) and using \(\sqrt2<17/12\) bounds this polynomial below by \(y^2-y/4+2/3>0\). Since \(n-d\ge1\), the derivative is indeed negative. Thus the smallest charge for positive \(p\) occurs at \(p=1\). For \(p=0\) the bound is no smaller: using the same \(d=n-1\), its extra \(c-b\) is nonnegative because \(\sqrt2(d+1)\ge d+2\) for \(d\ge3\).

For \(p=1\), \(d=n-1\), the bound simplifies to
\[
P(n)=\sqrt{2d}-\frac{2\sqrt2-1-3\sqrt2/(d+2)}{\sqrt d}
 \ge\sqrt{2n}-\frac{5\sqrt2/2-1}{\sqrt{n-1}}.
\]
In \(10\le n\le90\), put \(x=\sqrt n\), \(\alpha=3/2-\sqrt2\), and
\(\beta=(5\sqrt2/2-1)\sqrt{10}/3\).
Because \(\sqrt{n-1}\ge3\sqrt n/\sqrt{10}\), it suffices that
\(\alpha x+\beta/x<3\sqrt2/2-1\).
The left side is convex in \(x>0\), so only the endpoints \(\sqrt{10}\) and \(\sqrt{90}\) need checking. The bounds are respectively below \(1.117\) and \(1.097\), whereas the right-hand side exceeds \(1.121\). For \(4\le n\le9\) check the six values of \(P(n)\) directly by the exact enclosures below. In the remaining case \(n=3\) the reduced graph is \(K_3\), for which \(R=3/2>F(3)\). Since \(r\le n\), this proves the desired strict inequality for all reduced graphs of order at least three, and the deletion argument gives equality only at \(K_2\).

## Exact reproducibility

The following uses integer square root and rational arithmetic only. Copy it into Python 3 and run. The bracket thresholds and the rational comparisons for \(K_3\) are included for convenience.

~~~python
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
~~~

## Relation to prior methods

The degree-end charging inequality is the standard Randić bound in terms of the minimum and maximum degrees; see [O and Shi, arXiv:1705.05963](https://arxiv.org/abs/1705.05963). The AM–GM step is related to the nearly-perfect matching argument of [Akbari et al., arXiv:2402.12884v2, Theorem 8](https://arxiv.org/html/2402.12884v2). Here a rank witness supplies an adjacent permutation instead of a matching, and the outside-vertex term is retained. The written symbolic small-order reduction is an alternative to the direct 2,111 exact charging-inequality cases in the parallel Lean development.
