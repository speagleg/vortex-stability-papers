"""Lattice sums over the N-th roots of unity and their closed forms.

    T_a(n) = sum_{j=1}^{N-1} zeta^(j n) / (1 - zeta^j)^a ,   zeta = exp(2 pi i / N),  a >= 0, n in Z.

Facts used (proved in the paper, Lemma 3.1, and in Lean, module Heptagon.LatticeSums):
  (i)   T_a(n) depends only on n mod N, and is real (rational, in fact).
  (ii)  T_0(n) = N - 1 if N | n, and -1 otherwise.
  (iii) T_a(n) - T_a(n+1) = T_{a-1}(n)              (a >= 1)
  (iv)  sum_{n=0}^{N-1} T_a(n) = 0                    (a >= 0)
Hence for a >= 1 and 1 <= n <= N, T_a(n) = P_a(N, n) with P_a the unique polynomial with
  P_1(n) = n - (N+1)/2,  P_a(n) - P_a(n+1) = P_{a-1}(n),  sum_{n=1}^N P_a(n) = 0.

This module builds P_a symbolically, evaluates T_a exactly (Fraction) for given N, and checks against
direct floating-point (mpmath, 50 digits) summation.
"""
from fractions import Fraction
import sympy as sp

Nsym, nsym = sp.symbols('N n')
_P = {}


def P(a):
    """Closed form P_a(N, n) (sympy polynomial in N, n), valid for 1 <= n <= N, a >= 1."""
    if a in _P:
        return _P[a]
    i = sp.Symbol('i')
    if a == 1:
        prev_sum = -(nsym - 1)            # sum_{i=1}^{n-1} P_0(i), P_0 = -1 on [1, N-1]
    else:
        prev_sum = sp.summation(P(a - 1).subs(nsym, i), (i, 1, nsym - 1))
    c = sp.Symbol('c')                    # c = P_a(1)
    cand = c - prev_sum                   # P_a(n) = P_a(1) - sum_{i=1}^{n-1} P_{a-1}(i)
    tot = sp.summation(cand.subs(nsym, i), (i, 1, Nsym))
    csol = sp.solve(sp.Eq(tot, 0), c)[0]
    _P[a] = sp.factor(sp.expand(cand.subs(c, csol)))
    return _P[a]


def T_exact(a, n, N):
    """Exact T_a(n) for the given integer N (Fraction)."""
    if a == 0:
        return Fraction(N - 1) if n % N == 0 else Fraction(-1)
    r = n % N
    if r == 0:
        r = N
    v = P(a).subs({Nsym: N, nsym: r})
    v = sp.Rational(v)
    return Fraction(int(v.p), int(v.q))


def T_float(a, n, N, dps=50):
    import mpmath as mp
    mp.mp.dps = dps
    z = mp.expjpi(mp.mpf(2) / N)
    return mp.fsum(z**(j * n) / (1 - z**j)**a for j in range(1, N))


if __name__ == '__main__':
    import mpmath as mp
    print("Closed forms P_a(N, n), valid for 1 <= n <= N:")
    for a in range(1, 7):
        print(f"  P_{a} =", P(a))
    print("T_a(0) = P_a(N, N):")
    for a in range(1, 7):
        print(f"  T_{a}(0) =", sp.factor(P(a).subs(nsym, Nsym)))
    worst = 0
    for N in range(2, 16):
        for a in range(0, 7):
            for n in range(-8, 2 * N + 3):
                e = T_exact(a, n, N)
                f = T_float(a, n, N)
                err = abs(mp.mpf(e.numerator) / e.denominator - f)
                worst = max(worst, err)
    print("max |closed form - direct sum| over N = 2..15, a = 0..6, n = -8..2N+2:", mp.nstr(worst, 3))
