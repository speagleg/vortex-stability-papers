# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# Changes: none
"""screened rows W_nu = Q_nu, nu = 0, 1, 2 -- two independent evaluations of F_nu.

Independent recomputation (no archive code).  Conventions in rows_common.py.
 (L) direct lattice sum of the pair functions a, b of the kernel W(X) = Q_nu(X) (chain rule through X; Q_nu, Q_nu',
     Q_nu'' from closed forms, themselves checked against mpmath's legenq and its numerical derivatives);
 (P) Poschl-Teller mode sum: W_nu = 2 pi sum_n e^{-n|u|} psi_n(phi) psi_n(phi0)/(2 n N_n), psi_n = sin^m phi
     C^{(m)}_{n-m}(cos phi), m = nu + 1, N_n = pi 2^{1-2m} Gamma(n+m)/((n-m)! n Gamma(m)^2), giving
     F_nu(pi) = sum_n (pi/(n N_n)) [(2 s kappa psi psi' + (Lambda - n^2 s^2) psi^2) r_n/(1-r_n) - s^2 psi'^2 r_n/(1+r_n)].
Parts:
 (a) the mode sum reproduces Q_nu(X) at sample points; N_n vs quadrature; Q_derivs vs legenq;
 (b) |L - P| over the sign grid below;
 (c) sign of F_nu(pi) for kappa <= 1/sqrt2 (and the mirror kappa < 0) on 10 kappa x 14 ell_u, nu = 0, 1, 2;
 (d) F_nu(q) decreasing in q on (0, pi] at sample points (critical mode q = pi);
 (e) lowest mode: bracket at n = m equals m s^{2m} cos 2a (sympy), leading coefficients (pi/(m N_m)) m s^{2m} cos 2a =
     2 s^2 cos2a, (8/3) s^4 cos2a, (16/5) s^6 cos2a; the r^3 coefficient of F_1 vs (16/3) s^4 (6 s^4 - 9 s^2 + 2) and its
     max over alpha in [pi/4, pi/2] (<= -4/3 claimed); max of the r^4 coefficient c4 of F_2 over alpha in [pi/4, pi/2];
 (f) Q_1 and Q_2 thresholds ell^*(kappa) (arc spacing) at kappa = 0.72 .. 0.9999 with sign-change counts, vs the
     archive's Q_1 values 5.7296, 4.0856, 3.0055, 1.9820, 1.6859, 1.4949 (kappa = 0.72, 0.75, 0.8, 0.9, 0.95, 0.99)
     and 1.4496 (kappa = 0.9999).
Run: python rows_screened.py   (deterministic; a few minutes)
"""
import os
import sys
import mpmath as mp
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rows_common import Q_derivs, Q_legenq, pt_modes, pt_norm, F_lattice, F_modes, nmax_for  # noqa: E402

mp.mp.dps = 30


def W_modes(nu, u, phi, phi0):
    nmax = nmax_for(abs(u), 60)
    m1 = dict((n, p) for n, p, _ in pt_modes(nu, phi, nmax))
    m2 = dict((n, p) for n, p, _ in pt_modes(nu, phi0, nmax))
    return mp.fsum(2 * mp.pi * mp.exp(-n * abs(u)) * m1[n] * m2[n] / (2 * n * pt_norm(nu, n)) for n in m1)


def part_a():
    print('(a) mode expansion and kernel checks:')
    for nu in (0, 1, 2):
        worst = 0
        for u, p, p0 in (('0.3', '1.0', '1.4'), ('1.2', '0.4', '2.5'), ('2.5', '2.9', '0.2'), ('0.05', '1.5', '1.55')):
            u, p, p0 = mp.mpf(u), mp.mpf(p), mp.mpf(p0)
            X = (mp.cosh(u) - mp.cos(p) * mp.cos(p0)) / (mp.sin(p) * mp.sin(p0))
            worst = max(worst, abs(W_modes(nu, u, p, p0) - Q_derivs(nu, X)[0]) / abs(Q_derivs(nu, X)[0]))
        nq = max(abs(mp.quad(lambda t: pt_modes(nu, t, n)[-1][1]**2, [0, mp.pi / 2, mp.pi]) - pt_norm(nu, n))
                 for n in range(nu + 1, nu + 7))
        dq = 0
        for X in ('1.01', '1.7', '6', '40'):
            X = mp.mpf(X)
            v, d1, d2 = Q_derivs(nu, X)
            dq = max(dq, abs(v - Q_legenq(nu, X)) / abs(v), abs(d1 - mp.diff(lambda x: Q_legenq(nu, x), X)) / abs(d1),
                     abs(d2 - mp.diff(lambda x: Q_legenq(nu, x), X, 2)) / abs(d2))
        print(f'  nu={nu}: mode sum vs Q_nu(X) max rel. err {mp.nstr(worst, 2)};  N_n vs quadrature (n = m..m+5) '
              f'{mp.nstr(nq, 2)};  closed-form Q, Q\', Q\'\' vs legenq (+ numerical derivatives) {mp.nstr(dq, 2)}')


KAPS = ['0', '0.3', '0.5', '0.6', '0.65', '0.7', '0.705', 'kc', '-0.5', '-kc']
LUS = ['0.05', '0.1', '0.2', '0.35', '0.5', '0.75', '1', '1.5', '2', '3', '5', '8', '12', '20']


def kval(k):
    if k == 'kc':
        return 1 / mp.sqrt(2)
    if k == '-kc':
        return -1 / mp.sqrt(2)
    return mp.mpf(k)


def part_bc():
    print('(b)+(c) F_nu(pi) on the grid kappa in', KAPS, '(kc = 1/sqrt2), ell_u in', LUS)
    for nu in (0, 1, 2):
        worst_rel = 0
        maxF = None
        npos = 0
        for k in KAPS:
            al = mp.acos(kval(k))
            for lu in LUS:
                lu_ = mp.mpf(lu)
                L = F_lattice(nu, al, lu_)
                P = F_modes(nu, al, lu_)
                worst_rel = max(worst_rel, abs(L - P) / abs(P))
                scaled = P * mp.exp((nu + 2) * lu_)       # F_nu(pi) e^{(nu+2) ell_u}: O(1) at kappa_c and large spacing
                if maxF is None or scaled > maxF[0]:
                    maxF = (scaled, k, lu)
                npos += (L >= 0) or (P >= 0)
        print(f'  nu={nu}: max |L-P|/|P| = {mp.nstr(worst_rel, 2)};  points with F >= 0 (either method): {npos} of '
              f'{len(KAPS) * len(LUS)};  max of F e^{{(nu+2) ell_u}} = {mp.nstr(maxF[0], 6)} at kappa={maxF[1]}, '
              f'ell_u={maxF[2]}')
    for nu in (0, 1, 2):
        row = []
        al = mp.acos(1 / mp.sqrt(2))
        for lu in ('0.05', '1', '5', '20'):
            row.append(f'{lu}: {mp.nstr(F_modes(nu, al, mp.mpf(lu)), 8)}')
        print(f'  kappa = 1/sqrt2, nu={nu}: F_nu(pi) at ell_u ' + ', '.join(row))


def part_d():
    print('(d) F_nu(q) strictly decreasing on q = pi i/60, i = 1..60 (mode form):')
    for nu in (0, 1, 2):
        res = []
        for k, lu in (('0.3', '0.7'), ('0.72', '2'), ('0.9', '1'), ('0.99', '0.3'), ('-0.6', '1.5')):
            al = mp.acos(mp.mpf(k))
            v = [F_modes(nu, al, mp.mpf(lu), q=mp.pi * i / 60) for i in range(1, 61)]
            res.append(all(v[i + 1] < v[i] for i in range(59)))
        print(f'  nu={nu}: {res}')


def part_e():
    print('(e) lowest mode and leading coefficients:')
    phi, kk = sp.symbols('phi kappa')
    for nu in (0, 1, 2):
        m = nu + 1
        psi = sp.sin(phi)**m
        dpsi = sp.diff(psi, phi)
        br = 2 * sp.sin(phi) * sp.cos(phi) * psi * dpsi + (nu * (nu + 1) - m**2 * sp.sin(phi)**2) * psi**2 \
            - sp.sin(phi)**2 * dpsi**2
        print(f'  nu={nu}: bracket - m s^(2m) cos 2a = {sp.simplify(sp.expand_trig(br - m * sp.sin(phi)**(2 * m) * sp.cos(2 * phi)))};'
              f'  pi/(m N_m) * m = {sp.nsimplify(float(mp.pi / pt_norm(nu, m)))}')

    def coef(nu, n, al):
        s, k = mp.sin(al), mp.cos(al)
        for nn, psi, dpsi in pt_modes(nu, al, n):
            if nn == n:
                A = 2 * s * k * psi * dpsi + (nu * (nu + 1) - n * n * s * s) * psi * psi
                return mp.pi / (n * pt_norm(nu, n)) * (A - s * s * dpsi * dpsi)

    err = max(abs(coef(1, 3, mp.mpf(a)) - mp.mpf(16) / 3 * mp.sin(mp.mpf(a))**4 *
                  (6 * mp.sin(mp.mpf(a))**4 - 9 * mp.sin(mp.mpf(a))**2 + 2)) for a in ('0.3', '0.8', '1.2', '1.5'))
    print(f'  nu=1: r^3 coefficient vs (16/3) s^4 (6s^4 - 9s^2 + 2): max diff {mp.nstr(err, 2)}')
    grid = [mp.pi / 4 + (mp.pi / 4) * i / 2000 for i in range(2001)]
    c3 = max(coef(1, 3, a) for a in grid)
    c4 = max(coef(2, 4, a) for a in grid)
    print(f'  max over alpha in [pi/4, pi/2] (2001 points): c3 (nu=1) = {mp.nstr(c3, 10)} (claim <= -4/3);'
          f'  c4 (nu=2) = {mp.nstr(c4, 10)} (archive c4max = -0.7602)')
    # the r^4 coefficient of F_2 has contributions from n = 4 only (n = 3 gives r^3, r^6, ...)


def part_f():
    print('(f) screened thresholds (arc spacing ell* = ell_u*/sin a):')
    arch1 = {'0.72': '5.7296', '0.75': '4.0856', '0.8': '3.0055', '0.9': '1.9820', '0.95': '1.6859', '0.99': '1.4949',
             '0.9999': '1.4496'}
    for nu in (1, 2):
        for k in ('0.72', '0.75', '0.8', '0.9', '0.95', '0.99', '0.9999'):
            al = mp.acos(mp.mpf(k))
            f = lambda lu: F_modes(nu, al, lu)
            xs = [mp.mpf('0.01') * (mp.mpf(2000))**(mp.mpf(i) / 39) for i in range(40)]
            vs = [f(x) for x in xs]
            br = [(xs[i], xs[i + 1]) for i in range(39) if (vs[i] < 0) != (vs[i + 1] < 0)]
            r = mp.findroot(f, br[0], solver='anderson')
            arc = r / mp.sin(al)
            extra = f'  archive {arch1[k]}' if nu == 1 else ''
            print(f'  nu={nu} kappa={k:>6}: sign changes on 40 points ell_u in [0.01, 20]: {len(br)};  ell_u* = {mp.nstr(r, 12)};'
                  f'  ell* = {mp.nstr(arc, 12)}{extra}')


def main():
    print(__doc__.split('\n')[0])
    part_a()
    part_e()
    part_d()
    part_f()
    part_bc()


if __name__ == '__main__':
    main()
