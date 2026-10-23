# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# Changes: none
"""hypercycle-row thresholds ell^*(kappa) of the G_1 model and related numbers.

Independent recomputation (no archive code).  F(pi)(alpha, ell_u) is evaluated by the Lambert series (ell_u >= 1) or the
modular dual F0 - R1 - R2 (ell_u < 1); both were checked against direct lattice sums in rows_fpi.py.  Arc spacing
ell = ell_u/sin alpha, kappa = cos alpha.
 (1) for kappa in a list: the sign changes of F(pi) on a geometric grid of 400 points ell_u in [0.005, 60] (count),
     the root ell_u^* (bisection-refined findroot, 25 digits), ell^* = ell_u^*/sin alpha, and the archive's quoted values
     (task text / note table); monotonicity of ell_u^* in kappa.
 (2) the elementary closed form F0 = 0: its root and the error |ell^*_{F0} - ell^*|.
 (3) the explicit bound ell_A = arccosh(1/(2kappa^2-1))/sqrt(1-kappa^2): F(pi) > 0 on ell_u >= ell_A sin alpha (grid),
     the ratio ell_A/ell^* on a kappa grid, and ell_A - ell^* vs ln2/sqrt(1-kappa^2) near kappa_c.
 (4) near kappa_c: ell^* vs -ln(2kappa^2-1)/sqrt(1-kappa^2) (relative error).
 (5) the epsilon series F(pi)/(2 s^2) = sum_N e_N(kappa) e^{-N ell_u}: exact coefficients N = 1..4 from the Lambert series
     (sympy), vs the archive's (2K-1), (8K^2-3), 4(8K^3-8K^2+2K-1), K = kappa^2.
 (6) alpha -> 0: the horocycle criterion (coth eta - 1/eta)^2 = 2 tanh(eta)/eta, ell_* = pi/eta, to 30 digits, vs
     0.8439085312925335 (the horocycle-row critical spacing), and ell^*(kappa) as kappa -> 1.
 (7) Bolza collar (cylinder model): L_sys = 2 arccosh(1+sqrt2), sinh h_col sinh(L_sys/2) = 1, tanh h_col = sqrt2 - 1
     (exact); necklace thresholds h^*(N), N = 2..12, from F(2 pi floor(N/2)/N) = 0 at ell_u = L_sys/N, kappa = tanh h;
     the bound h_A(N): tanh^2 h_A = (1 + 1/cosh(L_sys/N))/2; the infinite-row boundary at the same ell_u.
Run: python rows_thresholds.py   (deterministic)
"""
import os
import sys
import mpmath as mp
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rows_common import F_lambert, F0, F_dual, tanh_pair_symbolic  # noqa: E402

mp.mp.dps = 35


def Fpi(alpha, lu):
    return F_lambert(alpha, lu) if lu >= 1 else F_dual(alpha, lu)


def grid_roots(f, lo, hi, n=400):
    xs = [lo * (hi / lo)**(mp.mpf(i) / (n - 1)) for i in range(n)]
    vals = [f(x) for x in xs]
    brackets = [(xs[i], xs[i + 1]) for i in range(n - 1) if (vals[i] < 0) != (vals[i + 1] < 0)]
    return brackets, vals


def refine(f, br):
    return mp.findroot(f, br, solver='anderson')


ARCHIVE = {'0.72': '4.7635102682', '0.75': '3.1863292497', '0.8': '2.2554766253', '0.9': '1.4365846813',
           '0.95': '1.1694721423', '0.99': '0.9537651073', '0.999': '0.8740556005', '0.9999': '0.8530342205'}


def main():
    print(__doc__.split('\n')[0])
    print('(1)+(2) thresholds (ell_u^*, arc ell^*), archive value, F0-root error:')
    kaps = ['0.708', '0.71', '0.72', '0.75', '0.8', '0.85', '0.9', '0.95', '0.99', '0.999', '0.9999']
    lus = {}
    for kap in kaps:
        al = mp.acos(mp.mpf(kap))
        s = mp.sin(al)
        f = lambda lu: Fpi(al, lu)
        br, _ = grid_roots(f, mp.mpf('0.005'), mp.mpf(60))
        root = refine(f, br[0]) if len(br) == 1 else None
        lus[kap] = root
        arc = root / s
        g = lambda lu: F0(al, lu)
        br0, _ = grid_roots(g, mp.mpf('0.005'), mp.mpf(60))
        r0 = refine(g, br0[-1]) / s if br0 else None
        arch = ARCHIVE.get(kap)
        cmp_ = f'archive {arch}, diff {mp.nstr(arc - mp.mpf(arch), 2)}' if arch else ''
        print(f'  kappa={kap:>7}: sign changes {len(br)};  ell_u* = {mp.nstr(root, 20)};  ell* = {mp.nstr(arc, 20)}  {cmp_}')
        print(f'      F0 roots {len(br0)}; ell*_F0 = {mp.nstr(r0, 15)}, |ell*_F0 - ell*| = {mp.nstr(abs(r0 - arc), 3)}')
    vals = [lus[k] for k in kaps]
    print('  ell_u^* strictly decreasing in kappa on this list:', all(vals[i + 1] < vals[i] for i in range(len(vals) - 1)))

    print('(3) bound ell_A and ratio ell_A/ell^*:')
    for kap in ('0.7072', '0.72', '0.75', '0.8', '0.9', '0.99', '0.999', '0.99999'):
        k_ = mp.mpf(kap)
        al = mp.acos(k_)
        s = mp.sin(al)
        luA = mp.acosh(1 / (2 * k_**2 - 1))
        ok = all(Fpi(al, luA * (1 + mp.mpf(i) / 10)) > 0 for i in range(0, 31))
        f = lambda lu: Fpi(al, lu)
        br, _ = grid_roots(f, mp.mpf('0.0001'), luA * 1.0001, 300)
        root = refine(f, br[-1])
        print(f'  kappa={kap:>8}: ell_A = {mp.nstr(luA / s, 12)}, F(pi) > 0 on ell_u in [1, 4] x ell_A sin a: {ok}; '
              f'ell_A/ell* = {mp.nstr(luA / root, 8)};  (ell_A - ell*) sqrt(1-k^2)/ln2 = {mp.nstr((luA - root) / mp.log(2), 8)}')
    print('  ratio ell_A/ell^* on kappa = 1/sqrt2 + (1 - 1/sqrt2) i/60, i = 1..59 (min, max, monotone):')
    rs = []
    for i in range(1, 60):
        k_ = 1 / mp.sqrt(2) + (1 - 1 / mp.sqrt(2)) * mp.mpf(i) / 60
        al = mp.acos(k_)
        luA = mp.acosh(1 / (2 * k_**2 - 1))
        f = lambda lu: Fpi(al, lu)
        br, _ = grid_roots(f, mp.mpf('0.005'), luA * 1.0001, 150)
        rs.append(luA / refine(f, br[-1]))
    print(f'    min {mp.nstr(min(rs), 8)} (i=1), max {mp.nstr(max(rs), 8)} (i=59), increasing: '
          f'{all(rs[i + 1] > rs[i] for i in range(len(rs) - 1))};  limit kappa->1: 2/ell_* = '
          f'{mp.nstr(2 / (mp.pi / mp.findroot(lambda e: (mp.coth(e) - 1 / e)**2 - 2 * mp.tanh(e) / e, 3.7)), 8)}')

    print('(4) near kappa_c: ell^* vs ell_as = -ln(2k^2-1)/sqrt(1-k^2):')
    for kap in ('0.708', '0.71', '0.72', '0.75', '0.8'):
        k_ = mp.mpf(kap)
        arc = lus[kap] / mp.sqrt(1 - k_**2)
        las = -mp.log(2 * k_**2 - 1) / mp.sqrt(1 - k_**2)
        print(f'  kappa={kap}: ell* = {mp.nstr(arc, 10)}, ell_as = {mp.nstr(las, 10)}, rel. error {mp.nstr((arc - las) / arc, 3)}')

    print('(5) epsilon series of F(pi)/(2 s^2) in e = exp(-ell_u):')
    al, kk, K = sp.symbols('alpha kappa K')
    s2 = sp.sin(al)**2
    coeffs = []
    for N in range(1, 5):
        tot = 0
        for n in sp.divisors(N):
            A = sp.sin(2 * al) * sp.sin(2 * n * al) - 2 * n * s2 * sp.sin(n * al)**2
            Bn = 2 * n * s2 * sp.cos(n * al)**2
            tot += A - Bn * (-1)**(N // n + 1)
        e = sp.expand(sp.expand_trig(tot / (2 * s2)))
        e = sp.simplify(e.subs(sp.sin(al)**2, 1 - sp.cos(al)**2))
        e = sp.expand(sp.simplify(sp.expand_trig(e).subs(sp.sin(al), sp.sqrt(1 - kk**2)).subs(sp.cos(al), kk)))
        coeffs.append(sp.factor(e.subs(kk**2, K)) if e.has(kk) else e)
        print(f'  e^{N}: {sp.expand(e.subs(kk, sp.sqrt(K)))}')
    claims = [2 * K - 1, 8 * K**2 - 3, 4 * (8 * K**3 - 8 * K**2 + 2 * K - 1)]
    for N, cl in enumerate(claims, 1):
        print(f'  e^{N} minus archive coefficient: {sp.simplify(sp.expand(coeffs[N - 1].subs(kk, sp.sqrt(K))) - cl)}')
    al0 = mp.acos(mp.mpf('0.8'))
    lu = mp.mpf(6)
    ee = mp.exp(-lu)
    ser = sum(float(sp.expand(coeffs[N].subs(kk, sp.sqrt(K))).subs(K, sp.Rational(16, 25))) * ee**(N + 1)
              for N in range(4))
    print(f'  numeric check kappa=0.8, ell_u=6: F/(2s^2) = {mp.nstr(Fpi(al0, lu) / (2 * mp.sin(al0)**2), 15)}, '
          f'4-term series = {mp.nstr(ser, 15)}, diff/e^5 = {mp.nstr((Fpi(al0, lu) / (2 * mp.sin(al0)**2) - ser) / ee**5, 6)}')

    print('(6) horocycle limit:')
    mp.mp.dps = 50
    eta = mp.findroot(lambda e: (mp.coth(e) - 1 / e)**2 - 2 * mp.tanh(e) / e, mp.mpf('3.72'))
    lstar = mp.pi / eta
    print(f'  eta_inf = {mp.nstr(eta, 32)};  ell_* = pi/eta = {mp.nstr(lstar, 32)};  '
          f'diff vs 0.8439085312925335: {mp.nstr(lstar - mp.mpf("0.8439085312925335"), 3)}')
    hfun = lambda e: e * mp.coth(2 * e) - mp.mpf(1) / 4 - e**2 * mp.coth(e)**2 / 4
    print(f'  horocycle function eta coth 2eta - 1/4 - eta^2 coth^2(eta)/4 at eta_inf: {mp.nstr(hfun(eta), 3)}')
    mp.mp.dps = 35
    for kap in ('0.9999', '0.999999', '0.99999999', '0.9999999999'):
        al = mp.acos(mp.mpf(kap))
        f = lambda lu: Fpi(al, lu)
        guess = lstar * mp.sin(al)
        root = mp.findroot(f, (guess * 0.9, guess * 1.2), solver='anderson')
        arc = root / mp.sin(al)
        print(f'  kappa={kap:>13}: alpha = {mp.nstr(al, 6)}, ell* = {mp.nstr(arc, 16)}, (ell* - ell_*)/alpha = '
              f'{mp.nstr((arc - lstar) / al, 8)}')

    print('(7) Bolza collar and necklaces (cylinder model):')
    Lsys = 2 * sp.acosh(1 + sp.sqrt(2))
    sh2 = sp.simplify(sp.sinh(Lsys / 2)**2)
    print('  sinh^2(L_sys/2) =', sp.nsimplify(sp.expand(sp.simplify(sh2))), ';  tanh^2 h_col = 1/(1 + sinh^2(L_sys/2)) =',
          sp.radsimp(1 / (1 + sp.expand(sh2))), '; (sqrt2-1)^2 =', sp.expand((sp.sqrt(2) - 1)**2))
    Ls = mp.mpf(2) * mp.acosh(1 + mp.sqrt(2))
    hcol = mp.asinh(1 / mp.sinh(Ls / 2))
    print(f'  L_sys = {mp.nstr(Ls, 15)}, h_col = {mp.nstr(hcol, 15)}, tanh h_col = {mp.nstr(mp.tanh(hcol), 15)}, '
          f'sqrt2-1 = {mp.nstr(mp.sqrt(2) - 1, 15)}')
    sym, c, k = tanh_pair_symbolic()
    fa = sp.lambdify((c, k), sym['a'], 'mpmath')
    fb = sp.lambdify((c, k), sym['b'], 'mpmath')

    def Fq(kap, lu, q):
        J = int(mp.ceil((mp.mp.dps * mp.log(10) + 20) / lu)) + 5
        return mp.fsum(fa(mp.cosh(j * lu), kap) + fb(mp.cosh(j * lu), kap) * mp.cos(q * j) for j in range(1, J + 1))
    mp.mp.dps = 25
    for N in range(2, 13):
        lu = Ls / N
        q = 2 * mp.pi * (N // 2) / N
        f = lambda h: Fq(mp.tanh(h), lu, q)
        hs = [mp.mpf(i) / 50 for i in range(1, 251)]
        vs = [f(h) for h in hs]
        br = [(hs[i], hs[i + 1]) for i in range(len(hs) - 1) if (vs[i] < 0) != (vs[i + 1] < 0)]
        hstar = mp.findroot(f, br[0], solver='anderson')
        hA = mp.atanh(mp.sqrt((1 + 1 / mp.cosh(lu)) / 2))
        frow = lambda h: Fq(mp.tanh(h), lu, mp.pi)
        hrow = mp.findroot(frow, (hstar - mp.mpf('0.3'), hstar + mp.mpf('0.3')), solver='anderson') if N % 2 else hstar
        print(f'  N={N:>2}: sign changes in h on (0.02, 5]: {len(br)};  h* = {mp.nstr(hstar, 10)};  h_A = {mp.nstr(hA, 6)};'
              f'  row (q = pi) boundary h = {mp.nstr(hrow, 10)};  h* < h_col: {hstar < hcol}')


if __name__ == '__main__':
    main()
