# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# Changes: none
"""conjugate geometry of f_N, tanh/sinh threshold radii, Krein-window structure.

Blocks from tanh_common.py (the derivation
written for check A).  Three numerical statements whose reproducers check A did not cover:
 (1) Conjugate geometry.  f_N = the irreducible factor of check aperp_crit vanishing at xi_*.  f_N is
     palindromic of degree 2k, so f_N(x) = x^k h_N(x + 1/x) with h_N the trace polynomial.  Roots of f_N on |x| = 1
     correspond to real roots of h_N in (-2, 2) (two each), real roots of f_N to real roots of h_N with |C| > 2 (two
     each).  Counts are exact (sympy real-root isolation of integer polynomials), so this part is in fact certified.
 (2) tanh/sinh threshold radii.  r_*^tanh = 2 artanh sqrt(xi_*), xi_* the zero of aperp_crit (bisection, 60 digits);
     r_*^sinh = arcosh sqrt(Theta_N), Theta_N = floor(N^2/4)/(N-1) - 1 (the sinh threshold cosh^2 r_* of wave 2).
 (3) Krein-window structure and constant (data).  For odd N, xi_EM^crit = the
     zero of det_crit = aperp apar - varpi^2 above xi_*; at 9 interior points of (xi_*, xi_EM^crit) the critical block
     is indefinite and all blocks 1 <= m <= (N-3)/2 are positive definite; just above xi_EM^crit (xi_EM^crit + gap/10,
     + gap, + 10 gap) every block is definite, so xi_EM = xi_EM^crit.  Prints N^3 (xi_EM - xi_*).  NUMERICAL.
Run: python tanh_extras.py   (deterministic)
"""
import os
import sys
import sympy as sp
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tanh_common import x, cleared, blocks_mp  # noqa: E402

mp.mp.dps = 60
C = sp.Symbol('C')


def trace_poly(f):
    """h with f(x) = x^k h(x + 1/x), f palindromic of degree 2k."""
    c = f.all_coeffs()[::-1]  # c[i] = coefficient of x^i
    d = len(c) - 1
    assert d % 2 == 0 and all(c[i] == c[d - i] for i in range(d + 1))
    k = d // 2
    P = [sp.Integer(2), C]
    for j in range(2, k + 1):
        P.append(sp.expand(C * P[-1] - P[-2]))
    h = c[k] + sum(c[k + j] * P[j] for j in range(1, k + 1))
    h = sp.Poly(sp.expand(h), C)
    assert sp.cancel(x**k * h.as_expr().subs(C, x + 1 / x) - f.as_expr()) == 0
    return h


def f_N(N):
    A = cleared(N, N // 2)[0]
    _, facs = sp.factor_list(A.as_expr())
    cands = [sp.Poly(g, x) for g, e in facs if sp.Poly(g, x).degree() > 1 and sp.Poly(g, x).count_roots(0, 1) > 0]
    assert len(cands) == 1
    f = cands[0]
    if f.LC() < 0:
        f = -f
    return f


def bisect(fun, lo, hi, it=230):
    flo = fun(lo)
    assert flo * fun(hi) < 0
    for _ in range(it):
        mid = (lo + hi) / 2
        fm = fun(mid)
        if fm * flo > 0:
            lo, flo = mid, fm
        else:
            hi = mid
    return (lo + hi) / 2


def xi_star(N):
    m = N // 2
    g = lambda t: blocks_mp(N, m, t)[0]
    grid = [mp.mpf(i) / 2000 for i in range(1, 2000)]
    vals = [g(t) for t in grid]
    ch = [i for i in range(len(grid) - 1) if vals[i] * vals[i + 1] < 0]
    assert len(ch) == 1, (N, ch)
    i = ch[0]
    return bisect(g, grid[i], grid[i + 1])


def xi_star_tau(N):
    """Large N: bisect in tau = -(N/2) log xi on [4, 12] (unique sign change there)."""
    m = N // 2
    g = lambda tau: blocks_mp(N, m, mp.exp(-2 * tau / N))[0]
    tau = bisect(g, mp.mpf(4), mp.mpf(12))
    return mp.exp(-2 * tau / N)


def part1():
    print("(1) conjugate geometry of f_N (exact real-root counts)")
    off_claim = {8: 6, 9: 12, 10: 8, 11: 16, 12: 10, 13: 20, 14: 12, 15: 24, 16: 14}
    for N in range(8, 17):
        f = f_N(N)
        h = trace_poly(f)
        d = int(f.degree())
        assert h.eval(2) != 0 and h.eval(-2) != 0
        on = 2 * int(h.count_roots(-2, 2))
        nreal_h = int(h.count_roots())
        real_f = 2 * (nreal_h - int(h.count_roots(-2, 2)))
        assert f.count_roots() == real_f
        off = d - on
        line = f"  N={N:2d}: deg {d:2d}; roots on |x|=1: {on:2d}; off: {off:2d} (claim {off_claim[N]}); real roots of f_N: {real_f}"
        assert off == off_claim[N]
        if N == 8:
            rr = sorted(sp.Poly(f, x).real_roots())
            vals = [mp.mpf(sp.N(r, 30)) for r in rr]
            line += f" = {[mp.nstr(v, 12) for v in vals]}; xi_*(8)^-1 = {mp.nstr(1 / vals[0], 15)}"
            assert real_f == 2 and on == 4 and off == 6
            line += "; not Pisot (conjugates on |x|=1), not Salem (more than 2 conjugates off |x|=1)"
        print(line)


def part2():
    print("(2) tanh vs sinh threshold radii")
    claim_s = {8: 0.5119, 9: 0.6585, 10: 0.7954, 11: 0.8814, 12: 0.9692, 13: 1.0317, 14: 1.0967, 15: 1.1462, 16: 1.1978}
    claim_t = {8: 0.5312, 9: 0.6991, 10: 0.8654, 11: 0.9752, 12: 1.0917, 13: 1.1776, 14: 1.2691, 15: 1.3407, 16: 1.4168}
    for N in list(range(8, 17)) + [50, 100, 200, 400, 800]:
        xs = xi_star(N) if N <= 16 else xi_star_tau(N)
        rt = 2 * mp.atanh(mp.sqrt(xs))
        Th = mp.mpf((N * N) // 4) / (N - 1) - 1
        rs = mp.acosh(mp.sqrt(Th))
        line = f"  N={N:3d}: r_*^tanh = {mp.nstr(rt, 10):>12}  r_*^sinh = {mp.nstr(rs, 10):>12}  ratio = {mp.nstr(rt / rs, 8)}"
        assert rt > rs
        if N <= 16:
            ok = abs(rt - claim_t[N]) < 5e-5 and abs(rs - claim_s[N]) < 5e-5
            assert ok
            line += f"  (claim {claim_t[N]}, {claim_s[N]}: {ok})"
        print(line)


def part3():
    print("(3) Krein window structure, odd N (NUMERICAL)")
    for N in [9, 15, 17, 21, 31, 61, 121, 241]:
        c = (N - 1) // 2
        xs = xi_star(N) if N <= 61 else xi_star_tau(N)
        det = lambda t: (lambda b: b[0] * b[1] - b[2]**2)(blocks_mp(N, c, t))
        assert det(xs) < 0
        d = mp.mpf(10)**-14
        while det(xs + d) < 0:
            d *= 2
        xem = bisect(det, xs, xs + d)
        gap = xem - xs
        inner = True
        for k in range(1, 10):
            t = xs + gap * k / 10
            a, b, v, _ = blocks_mp(N, c, t)
            inner &= (a > 0 and a * b - v * v < 0 and b > 0)
            for m in range(1, c):
                a, b, v, _ = blocks_mp(N, m, t)
                inner &= (a > 0 and a * b - v * v > 0)
        above = True
        for t in (xem + gap / 10, xem + gap, xem + 10 * gap):
            for m in range(1, c + 1):
                a, b, v, _ = blocks_mp(N, m, t)
                above &= (a > 0 and a * b - v * v > 0)
        assert inner and above
        print(f"  N={N:3d}: xi_* = {mp.nstr(xs, 20)}  xi_EM = {mp.nstr(xem, 20)}  gap = {mp.nstr(gap, 6)}"
              f"  N^3 gap = {mp.nstr(N**3 * gap, 6)}  interior: crit indefinite, others definite: {inner}; definite above: {above}")


def main():
    print(__doc__.split('\n')[0])
    part1()
    part2()
    part3()
    print("\nDONE (all assertions passed)")


if __name__ == '__main__':
    main()
