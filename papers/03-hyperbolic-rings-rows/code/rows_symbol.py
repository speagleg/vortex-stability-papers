# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# Changes: none
"""exact Bloch symbol of G_1 hypercycle rows from a direct lattice-sum Hessian.

Independent recomputation (no archive code).  Conventions: see rows_common.py (strip chart, u' = s^2 H_phi,
phi' = -s^2 H_u, W = G_1 = Q_0, kappa = cos alpha, K2 := kappa^2, c = cosh(j ell_u), D = c - cos 2 alpha).
 (a) sympy derivation of the pair functions a, b, d as rational functions of (c, kappa) from X and the equations of
     motion; exact checks of the archive's closed forms: a - b = s^2((2K2-1)c-1)/((c-1)D), a + b =
     s^2((4K2-1)c-(4K2^2-2K2+1))/D^2, b numerator in t = c-1 with coefficients K2, 1-K2, 2(1-K2)^2, b - d = s^2/(c-1),
     a - d = sin^2(2a)/(2(c - cos 2a)), and the sign of d.
 (b) Chebyshev/Lambert generating functions b = 2 s^2 sum n cos^2(n a) z^n, d = -2 s^2 sum n sin^2(n a) z^n
     (z = e^{-x}, c = cosh x) at sample points, 40 digits.
 (c) direct Hessian: every second partial of the pair energy W(X(u0-uj, phi0, phij)) by numerical differentiation
     (mpmath diff, dps 40) for j = +-1, +-2, +-3 at five (kappa, ell_u), assembled into the velocity Jacobian, vs (a);
     parity checks (u-partials odd in j, the rest even).
 (d) full Bloch symbol at q = 0.7, 2, pi from the lattice sum of the numerical entries: A_uphi = B, A_phiu = C,
     A_uu = A_phiphi = i varpi, vs closed forms; varpi vs -2 kappa s^3 sum sinh(j l) sin(qj)/D_j^2.
 (e) 6-site supercell (periodic images) velocity Jacobian eigenvalues vs i varpi(q) +- sqrt(B(q) C(q)), q = 2 pi m/6.
 (f) F(q) decreasing in q on (0, pi) (grid) at the sample points.
Run: python rows_symbol.py   (deterministic)
"""
import os
import sys
import mpmath as mp
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rows_common import tanh_pair_symbolic, fmt  # noqa: E402

mp.mp.dps = 40


def part_a(sym, c, k):
    print('(a) pair functions derived by sympy (K2 = kappa^2):')
    for nm in 'abd':
        print(f'  {nm}(c) =', sym[nm])
    a, b, d = sym['a'], sym['b'], sym['d']
    K2 = sp.Symbol('K2', positive=True)
    s2 = 1 - k**2
    D = c + 1 - 2 * k**2
    checks = {
        'a - b = s^2((2K2-1)c-1)/((c-1)D)': a - b - s2 * ((2 * k**2 - 1) * c - 1) / ((c - 1) * D),
        'a + b = s^2((4K2-1)c-(4K2^2-2K2+1))/D^2': a + b - s2 * ((4 * k**2 - 1) * c - (4 * k**4 - 2 * k**2 + 1)) / D**2,
        'b - d = s^2/(c-1)': b - d - s2 / (c - 1),
        'a - d = sin^2(2a)/(2(c - cos2a))': a - d - 4 * k**2 * s2 / (2 * D),
    }
    for nm, e in checks.items():
        print(f'  {nm}: exact difference = {sp.simplify(e)}')
    t = sp.Symbol('t')
    num_b = sp.factor(b * (c - 1) * D**2 / s2)
    poly = sp.Poly(sp.expand(num_b.subs(c, t + 1).subs(k**2, K2)), t)
    print('  b = s^2 Nb(t)/((c-1) D^2), Nb(t) coefficients (t^2, t, 1):',
          [sp.factor(cf) for cf in poly.all_coeffs()])
    num_d = sp.factor(-d * (c - 1)**2 * D**2 / s2**2)
    print('  d = -s^4 Nd(c)/((c-1)^2 D^2) with Nd =', sp.factor(sp.expand(num_d)),
          '; Nd(c) in t = c-1:', sp.Poly(sp.expand(num_d.subs(c, t + 1).subs(k**2, K2)), t).all_coeffs())
    return {nm: sp.lambdify((c, k), sym[nm], 'mpmath') for nm in 'abd'}


def part_b(f):
    print('(b) generating functions, z = e^{-x}, c = cosh x (max abs difference over samples):')
    worst = {'b': 0, 'd': 0}
    for kap in ('0.1', '0.5', '0.7071', '0.9', '-0.6'):
        for x in ('0.3', '1', '4'):
            kap_, x_ = mp.mpf(kap), mp.mpf(x)
            al = mp.acos(kap_)
            s2 = mp.sin(al)**2
            z = mp.exp(-x_)
            c = mp.cosh(x_)
            nN = int(mp.ceil((mp.mp.dps * mp.log(10) + 20) / x_)) + 10      # explicit truncation, tail < 10^-dps
            gb = 2 * s2 * mp.fsum(n * mp.cos(n * al)**2 * z**n for n in range(1, nN))
            gd = -2 * s2 * mp.fsum(n * mp.sin(n * al)**2 * z**n for n in range(1, nN))
            worst['b'] = max(worst['b'], abs(gb - f['b'](c, kap_)))
            worst['d'] = max(worst['d'], abs(gd - f['d'](c, kap_)))
    print('  b:', mp.nstr(worst['b'], 3), '  d:', mp.nstr(worst['d'], 3))


def pair_partials(al, lu, j):
    """All second partials of W(X(u0 - uj, phi0, phij)) at the row, plus first partials, numerically."""
    def W(u0, p0, uj, pj):
        X = (mp.cosh(u0 - uj) - mp.cos(p0) * mp.cos(pj)) / (mp.sin(p0) * mp.sin(pj))
        return mp.log((X + 1) / (X - 1)) / 2
    pt = (mp.mpf(0), al, j * lu, al)
    D = {}
    names = ['u0', 'p0', 'uj', 'pj']
    for i in range(4):
        o = [0] * 4
        o[i] = 1
        D[names[i]] = mp.diff(W, pt, tuple(o))
        for k2 in range(i, 4):
            o2 = [0] * 4
            o2[i] += 1
            o2[k2] += 1
            D[names[i] + names[k2]] = mp.diff(W, pt, tuple(o2))
    return D


def jac_entries(al, lu, j):
    """Velocity-Jacobian entries of vortex 0 from pair (0, j): derivatives of u'_0, phi'_0 w.r.t. (u0, p0, uj, pj)."""
    D = pair_partials(al, lu, j)
    s, k = mp.sin(al), mp.cos(al)
    s2 = s * s
    return {
        'du/du0': s2 * D['u0p0'], 'du/dp0': s2 * D['p0p0'] + 2 * s * k * D['p0'],
        'du/duj': s2 * D['p0uj'], 'du/dpj': s2 * D['p0pj'],
        'dp/du0': -s2 * D['u0u0'], 'dp/dp0': -s2 * D['u0p0'] - 2 * s * k * D['u0'],
        'dp/duj': -s2 * D['u0uj'], 'dp/dpj': -s2 * D['u0pj'],
    }


SAMPLES = [('0.3', '0.7'), ('0.72', '2.0'), ('0.9', '1.1'), ('0.999', '0.6'), ('-0.6', '1.5')]


def part_c(f):
    print('(c) direct numerical Hessian (mpmath diff) vs closed forms, pairs j = +-1, +-2, +-3:')
    for kap, lu in SAMPLES:
        kap_, lu_ = mp.mpf(kap), mp.mpf(lu)
        al = mp.acos(kap_)
        errs = {'a': 0, 'b': 0, 'd': 0, 'dp/duj=-d': 0, 'parity': 0}
        for j in (1, 2, 3):
            c = mp.cosh(j * lu_)
            Ep, Em = jac_entries(al, lu_, j), jac_entries(al, lu_, -j)
            for E in (Ep, Em):
                errs['a'] = max(errs['a'], abs(E['du/dp0'] - f['a'](c, kap_)))
                errs['b'] = max(errs['b'], abs(E['du/dpj'] - f['b'](c, kap_)))
                errs['d'] = max(errs['d'], abs(E['dp/du0'] - f['d'](c, kap_)))
                errs['dp/duj=-d'] = max(errs['dp/duj=-d'], abs(E['dp/duj'] + E['dp/du0']))
            odd = ['du/du0', 'du/duj', 'dp/dp0', 'dp/dpj']
            even = ['du/dp0', 'du/dpj', 'dp/du0', 'dp/duj']
            for nm in odd:
                errs['parity'] = max(errs['parity'], abs(Ep[nm] + Em[nm]))
            for nm in even:
                errs['parity'] = max(errs['parity'], abs(Ep[nm] - Em[nm]))
        print(f'  kappa={kap:>6} ell_u={lu}: ' + ', '.join(f'{k_}: {mp.nstr(v, 2)}' for k_, v in errs.items()),
              ' d(j=1) =', fmt(f['d'](mp.cosh(lu_), kap_), 8))


def symbol_numeric(al, lu, qs, J):
    ent = {j: jac_entries(al, lu, j) for j in list(range(-J, 0)) + list(range(1, J + 1))}
    out = {}
    for q in qs:
        S = {'uu': 0, 'up': 0, 'pu': 0, 'pp': 0}
        for j, E in ent.items():
            e = mp.expjpi(q * j / mp.pi)
            S['uu'] += E['du/du0'] + E['du/duj'] * e
            S['up'] += E['du/dp0'] + E['du/dpj'] * e
            S['pu'] += E['dp/du0'] + E['dp/duj'] * e
            S['pp'] += E['dp/dp0'] + E['dp/dpj'] * e
        out[q] = S
    return out, ent


def closed_symbol(f, kap, lu, q, J):
    al = mp.acos(kap)
    s = mp.sin(al)
    B = C = varpi = mp.mpf(0)
    for j in range(1, J + 1):
        c = mp.cosh(j * lu)
        B += 2 * (f['a'](c, kap) + f['b'](c, kap) * mp.cos(q * j))
        C += 2 * f['d'](c, kap) * (1 - mp.cos(q * j))
        varpi += -2 * kap * s**3 * mp.sinh(j * lu) * mp.sin(q * j) / (c - mp.cos(2 * al))**2
    return B, C, varpi


def part_d_e_f(f):
    mp.mp.dps = 30
    print('(d) lattice-sum symbol from the numerical Hessian vs closed forms (Bloch convention e^{+iqk}):')
    store = {}
    for kap, lu in SAMPLES:
        kap_, lu_ = mp.mpf(kap), mp.mpf(lu)
        al = mp.acos(kap_)
        J = int(mp.ceil(80 / lu_))
        qs = [mp.mpf('0.7'), mp.mpf(2), mp.pi]
        num, ent = symbol_numeric(al, lu_, qs, J)
        store[(kap, lu)] = (al, ent, J)
        worst = 0
        for q in qs:
            B, C, vp = closed_symbol(f, kap_, lu_, q, J)
            S = num[q]
            worst = max(worst, abs(S['up'] - B), abs(S['pu'] - C), abs(S['uu'] - 1j * vp), abs(S['pp'] - 1j * vp))
        Bpi, Cpi, _ = closed_symbol(f, kap_, lu_, mp.pi, J)
        print(f'  kappa={kap:>6} ell_u={lu}: max|numeric - closed| over q, entries = {mp.nstr(worst, 2)};'
              f'  F(pi) = B(pi)/2 = {fmt(Bpi / 2, 12)},  C(pi) = {fmt(Cpi, 12)}')
    print('(e) 6-site supercell velocity Jacobian eigenvalues vs i varpi(q) +- sqrt(B C), q = 2 pi m/6:')
    M = 6
    for kap, lu in SAMPLES:
        al, ent, J = store[(kap, lu)]
        kap_, lu_ = mp.mpf(kap), mp.mpf(lu)
        Jm = mp.zeros(2 * M, 2 * M)
        for i in range(M):
            for j, E in ent.items():
                k_ = (i + j) % M
                Jm[i, i] += E['du/du0']
                Jm[i, M + i] += E['du/dp0']
                Jm[M + i, i] += E['dp/du0']
                Jm[M + i, M + i] += E['dp/dp0']
                Jm[i, k_] += E['du/duj']
                Jm[i, M + k_] += E['du/dpj']
                Jm[M + i, k_] += E['dp/duj']
                Jm[M + i, M + k_] += E['dp/dpj']
        ev = mp.eig(Jm, left=False, right=False)
        pred = []
        for m in range(M):
            q = 2 * mp.pi * m / M
            B, C, vp = closed_symbol(_F, kap_, lu_, q, J)
            r = mp.sqrt(mp.mpc(B * C))
            pred += [1j * vp + r, 1j * vp - r]
        # q = 0 carries a 2x2 Jordan block at 0 (translation and drift), so its numerical eigenvalues are only
        # sqrt(eps)-accurate; it is compared separately.
        jor = [e for e in ev if abs(e) < mp.mpf(10)**-8]
        ev = [e for e in ev if abs(e) >= mp.mpf(10)**-8]
        pred = pred[2:]
        used = [False] * len(pred)
        worst = 0
        for e in ev:
            best, bi = None, None
            for i, p in enumerate(pred):
                if not used[i] and (best is None or abs(e - p) < best):
                    best, bi = abs(e - p), i
            used[bi] = True
            worst = max(worst, best)
        gmax = max(mp.re(e) for e in ev)
        print(f'  kappa={kap:>6} ell_u={lu}: q != 0 max eigenvalue mismatch = {mp.nstr(worst, 2)};'
              f' q = 0 pair |lambda| <= {mp.nstr(max(abs(e) for e in jor), 2)} ({len(jor)} eigenvalues);'
              f'  max Re(lambda) = {fmt(gmax, 10)}')
    print('(f) F(q) = sum_j [a_j + b_j cos qj] strictly decreasing on a 200-point grid of (0, pi):')
    for kap, lu in SAMPLES:
        kap_, lu_ = mp.mpf(kap), mp.mpf(lu)
        J = int(mp.ceil(80 / lu_))
        vals = [closed_symbol(_F, kap_, lu_, mp.pi * i / 200, J)[0] / 2 for i in range(1, 201)]
        dec = all(vals[i + 1] < vals[i] for i in range(len(vals) - 1))
        print(f'  kappa={kap:>6} ell_u={lu}: decreasing {dec};  F(pi) {"<" if vals[-1] < 0 else ">="} 0')


_F = None


def main():
    global _F
    print(__doc__.split('\n')[0])
    sym, c, k = tanh_pair_symbolic()
    _F = part_a(sym, c, k)
    part_b(_F)
    part_c(_F)
    part_d_e_f(_F)


if __name__ == '__main__':
    main()
