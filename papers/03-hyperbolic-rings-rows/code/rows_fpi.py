# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# Changes: none
"""F(pi) of G_1 hypercycle rows by four independent evaluations.

Independent recomputation (no archive code).  F(pi) = sum_{j>=1} [a(c_j) - (-1)^{j+1} b(c_j)], c_j = cosh(j ell_u).
 (L) lattice: the sympy-derived rational pair functions a, b (rows_common.tanh_pair_symbolic) summed over j;
 (S) Lambert series sum_n [(sin2a sin2na - 2n s^2 sin^2 na) r_n/(1-r_n) - 2n s^2 cos^2 na r_n/(1+r_n)], r_n = e^{-n ell_u}
     (from the generating functions b = 2 s^2 sum n cos^2(na) z^n, a = d + sin2a sum sin(2na) z^n checked in item 1);
 (T) theta form F = sin2a S(a; r) - 2 s^2 [E(r) - E(r^2)] + 2 s^2 C(a; r^2) with mpmath's jtheta:
     S = (theta_1'/theta_1(a | e^{-ell_u/2}) - cot a)/4,  C = ((theta_1'/theta_1)'(a | e^{-ell_u}) + csc^2 a)/8,
     E(r) = sum n r^n/(1-r^n) = (theta_1'''(0)/theta_1'(0) + 1)/24 at nome r^{1/2};
 (M) modular dual F = F0 - R1 - R2 (derived here from theta_1(v|tau) = i(-i tau)^{-1/2} e^{-i v^2/(pi tau)}
     theta_1(v/tau|-1/tau) and E_2(-1/tau) = tau^2 E_2(tau) - 6 i tau/pi):
     F0 = (pi sin2a/(2 ell_u)) coth(2 pi a/ell_u) - a sin2a/ell_u - cos2a/4 - (pi^2 s^2/(4 ell_u^2)) coth^2(pi a/ell_u),
     R1 = (2 pi/ell_u) sum Q1^n/(1-Q1^n)[sin2a sinh(4 pi n a/ell_u) - 4 pi n s^2/ell_u],   Q1 = e^{-4 pi^2/ell_u},
     R2 = (2 pi^2 s^2/ell_u^2) sum n Q2^n/(1-Q2^n)[1 + cosh(2 pi n a/ell_u)],              Q2 = e^{-2 pi^2/ell_u}.
Also: R1, R2 > 0 for kappa >= 1/sqrt2 on a grid (F < F0); the alpha -> 0 limit of F0 at fixed arc spacing
ell = ell_u/sin a (eta = pi/ell) is eta coth 2eta - 1/4 - eta^2 coth^2(eta)/4 (sympy), and F(pi) tends to it.
Run: python rows_fpi.py   (deterministic; dps 50, 30 digits printed)
"""
import os
import sys
import mpmath as mp
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rows_common import tanh_pair_symbolic, F_lambert, F0, F_dual_corrections, F_dual, nmax_for  # noqa: E402

mp.mp.dps = 50


def F_lattice_closed(fa, fb, alpha, lu):
    kap = mp.cos(alpha)
    J = nmax_for(lu, 20)
    return mp.fsum(fa(mp.cosh(j * lu), kap) + (-1)**j * fb(mp.cosh(j * lu), kap) for j in range(1, J + 1))


def logder(v, q):
    return mp.jtheta(1, v, q, 1) / mp.jtheta(1, v, q)


def logder_prime(v, q):
    t0, t1, t2 = mp.jtheta(1, v, q), mp.jtheta(1, v, q, 1), mp.jtheta(1, v, q, 2)
    return t2 / t0 - (t1 / t0)**2


def E_eis(r):
    q = mp.sqrt(r)
    return (mp.jtheta(1, 0, q, 3) / mp.jtheta(1, 0, q, 1) + 1) / 24


def F_theta(alpha, lu):
    # mpmath's jtheta loses accuracy as the nome approaches 1 (small ell_u): give it 60 guard digits
    with mp.extradps(60):
        alpha, lu = +alpha, +lu
        return +_F_theta(alpha, lu)


def _F_theta(alpha, lu):
    s2 = mp.sin(alpha)**2
    r = mp.exp(-lu)
    S = (logder(alpha, mp.exp(-lu / 2)) - mp.cot(alpha)) / 4
    C = (logder_prime(alpha, mp.exp(-lu)) + 1 / mp.sin(alpha)**2) / 8
    return mp.sin(2 * alpha) * S - 2 * s2 * (E_eis(r) - E_eis(r * r)) + 2 * s2 * C


POINTS = [('0.72', '3.3'), ('0.75', '2.2'), ('0.8', '1.35'), ('0.9', '0.62'), ('0.999', '0.04'),
          ('0.7071067811865475244', '2.0'), ('0.5', '0.1'), ('0.3', '5'), ('0', '1'), ('-0.6', '0.8')]


def main():
    print(__doc__.split('\n')[0])
    sym, c, k = tanh_pair_symbolic()
    fa = sp.lambdify((c, k), sym['a'], 'mpmath')
    fb = sp.lambdify((c, k), sym['b'], 'mpmath')
    print('(1) F(pi) at (kappa, ell_u); value from the lattice sum (L), and |X - L| for X = S, T, M:')
    worst = 0
    for kap, lu in POINTS:
        al = mp.acos(mp.mpf(kap))
        lu_ = mp.mpf(lu)
        L = F_lattice_closed(fa, fb, al, lu_)
        S = F_lambert(al, lu_)
        T = F_theta(al, lu_)
        M = F_dual(al, lu_)
        R1, R2 = F_dual_corrections(al, lu_)
        e = [abs(S - L), abs(T - L), abs(M - L)]
        worst = max(worst, max(e))
        print(f'  kappa={mp.nstr(mp.mpf(kap), 8):>10} ell_u={lu:>5}: F(pi) = {mp.nstr(L, 30)}')
        print(f'      |S-L| {mp.nstr(e[0], 2)}  |T-L| {mp.nstr(e[1], 2)}  |M-L| {mp.nstr(e[2], 2)}'
              f'   F0 = {mp.nstr(F0(al, lu_), 12)}  R1 = {mp.nstr(R1, 3)}  R2 = {mp.nstr(R2, 3)}')
    print(f'  max discrepancy over all points and methods: {mp.nstr(worst, 2)}  (30-digit agreement: {worst < 1e-30})')

    print('(2) dual corrections positive for kappa >= 1/sqrt2 (alpha <= pi/4), grid alpha = (pi/4) i/40, '
          'ell_u in {0.02, 0.05, 0.1, 0.3, 1, 3, 10}:')
    mp.mp.dps = 30
    ok = True
    minr = None
    for i in range(1, 41):
        al = mp.pi / 4 * i / 40
        for lu in ('0.02', '0.05', '0.1', '0.3', '1', '3', '10'):
            R1, R2 = F_dual_corrections(al, mp.mpf(lu))
            ok = ok and R1 > 0 and R2 > 0
    print('  R1 > 0 and R2 > 0 at all 280 points:', ok,
          ' (termwise: sin2a sinh(4 pi n a/l) >= 4 pi n s^2/l iff tan a <= 2a for a <= pi/4 once sinh x >= x)')
    mp.mp.dps = 50

    print('(3) alpha -> 0 at fixed arc spacing ell (ell_u = ell sin alpha):')
    a_, l_ = sp.symbols('alpha ell', positive=True)
    lu_s = l_ * sp.sin(a_)
    F0s = (sp.pi * sp.sin(2 * a_) / (2 * lu_s)) * sp.coth(2 * sp.pi * a_ / lu_s) - a_ * sp.sin(2 * a_) / lu_s \
        - sp.cos(2 * a_) / 4 - (sp.pi**2 * sp.sin(a_)**2 / (4 * lu_s**2)) * sp.coth(sp.pi * a_ / lu_s)**2
    lim = sp.limit(F0s, a_, 0)
    eta = sp.Symbol('eta', positive=True)
    target = eta * sp.coth(2 * eta) - sp.Rational(1, 4) - eta**2 * sp.coth(eta)**2 / 4
    print('  lim F0 =', lim, ';  minus horocycle function at eta = pi/ell:',
          sp.simplify((lim - target.subs(eta, sp.pi / l_)).rewrite(sp.exp)))
    ell = mp.mpf('0.9')
    hfun = lambda e: e * mp.coth(2 * e) - mp.mpf(1) / 4 - e**2 * mp.coth(e)**2 / 4
    print(f'  numeric, ell = 0.9: horocycle function {mp.nstr(hfun(mp.pi / ell), 20)}')
    for al in ('0.2', '0.05', '0.01', '0.001', '0.0001'):
        al_ = mp.mpf(al)
        Fv = F_dual(al_, ell * mp.sin(al_))
        print(f'    alpha = {al:>6}: F(pi) = {mp.nstr(Fv, 20)},  (F(pi) - limit)/alpha = {mp.nstr((Fv - hfun(mp.pi / ell)) / al_, 10)}')


if __name__ == '__main__':
    main()
