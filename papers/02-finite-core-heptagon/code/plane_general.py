"""General-N closed forms of the planar ring blocks (Theorem 3.3 of the paper).

For 1 <= m <= N-1 (ring radius 1, Gamma = 1, eps = r^4):
  point vortices:  a_perp^0 = N - 1 - m(N-m)/2,  a_par^0 = m(N-m)/2,  varpi^0 = 0
  r^4 terms:       a_perp^1 = (Lp^2 + Lm^2)/4 + mu*kap - 2*Om1
                   a_par^1  = (Lp^2 + Lm^2)/4 - mu*kap
                   varpi^1  = (Lp^2 - Lm^2)/4
  with mu = T_2(0), Om1 = -mu^2, Lp = -2(T_3(0) - T_3(m+1)), Lm = -2(T_3(0) - T_3(1-m)),
       kap = -T_2(0) + 3(T_4(0) - T_4(1-m) - T_4(1+m) + T_4(2)).
These are the formulas derived by hand in Section 3; here we (1) substitute the closed forms P_a,
(2) compare with the exact per-(N, m) output of blocks.py (which does not use these hand formulas),
(3) specialise m = floor(N/2) (the critical mode) and print the closed forms of Corollary 4.4.
"""
import sympy as sp
import tsums
from fractions import Fraction

N, m = sp.symbols('N m')


def T(a, arg):
    """closed form, arg must lie in [1, N] (a >= 1)."""
    return tsums.P(a).subs({tsums.Nsym: N, tsums.nsym: arg})


def formulas():
    mu = T(2, N)                        # T_2(0) = T_2(N)
    T30 = T(3, N); T40 = T(4, N)
    Lp = -2 * (T30 - T(3, m + 1))       # m + 1 in [2, N]
    Lm = -2 * (T30 - T(3, N + 1 - m))   # 1 - m = N + 1 - m mod N, in [2, N]
    kap = -mu + 3 * (T40 - T(4, N + 1 - m) - T(4, m + 1) + T(4, 2))
    Om1 = -mu**2
    a0p = N - 1 - m * (N - m) / sp.Integer(2)
    a0q = m * (N - m) / sp.Integer(2)
    # point-vortex blocks from the sums as well (check of the classical formula)
    g = lambda arg: T(2, arg) - T(1, arg)          # sum_j zeta^{j n} zeta_j p_j^2
    a0p_sum = N - 1 + (T(2, N) - T(1, N)) - g(m)
    a0q_sum = -((T(2, N) - T(1, N)) - g(m))
    d = dict(
        mu=sp.factor(mu), Om1=sp.factor(Om1), Lp=sp.factor(Lp), Lm=sp.factor(Lm), kap=sp.factor(kap),
        aperp1=sp.factor((Lp**2 + Lm**2) / 4 + mu * kap - 2 * Om1),
        apar1=sp.factor((Lp**2 + Lm**2) / 4 - mu * kap),
        varpi1=sp.factor((Lp**2 - Lm**2) / 4),
        a0p=a0p, a0q=a0q,
        a0p_check=sp.simplify(a0p_sum - a0p), a0q_check=sp.simplify(a0q_sum - a0q))
    return d


if __name__ == '__main__':
    d = formulas()
    print("mu = T_2(0) =", d['mu'])
    print("Omega_1 = -mu^2 =", d['Om1'])
    print("Lambda(m) =", d['Lp'])
    print("Lambda(-m) =", d['Lm'])
    print("kappa(m) =", d['kap'])
    print("point-vortex blocks from the lattice sums minus classical formula:", d['a0p_check'], d['a0q_check'])
    print("d_perp(N, m) =", d['aperp1'])
    print("d_par(N, m)  =", d['apar1'])
    print("d_varpi(N,m) =", d['varpi1'])
    # Compare with blocks.py exact output (independent bookkeeping) for N = 2..12, 1 <= m <= N/2
    import blocks
    bad = 0
    for NN in range(2, 13):
        for mm in range(1, NN // 2 + 1):
            b = blocks.block('plane', NN, mm)
            got = tuple(sp.nsimplify(x) for x in (b['ss'][1], b['tt'][1], b['varpi'][1]))
            f = tuple(sp.nsimplify(d[k].subs({N: NN, m: mm})) for k in ('aperp1', 'apar1', 'varpi1'))
            if got != f:
                bad += 1
                print("MISMATCH", NN, mm, got, f)
    print("formula vs blocks.py, N = 2..12, 1 <= m <= N/2: mismatches =", bad)
    # critical mode
    k = sp.Symbol('k', integer=True, positive=True)
    Aeven = sp.factor(d['aperp1'].subs({N: 2 * k, m: k}).subs(k, N / 2))
    Aodd = sp.factor(d['aperp1'].subs({N: 2 * k + 1, m: k}).subs(k, (N - 1) / 2))
    print("A_N(1) = d_perp(N, floor(N/2)):  even N:", Aeven, "   odd N:", Aodd)
    print("A_N(1), N = 2..14 (N = 2, 3: critical mode m = 1 is the m = floor(N/2) value only for N = 2, 3):")
    for NN in range(2, 15):
        mc = NN // 2
        print("  N=%d m=%d  d=(%s, %s, %s)" % (NN, mc, d['aperp1'].subs({N: NN, m: mc}), d['apar1'].subs({N: NN, m: mc}),
                                             d['varpi1'].subs({N: NN, m: mc})))
    print("Heptagon N = 7, m = 3:", [d[k].subs({N: 7, m: 3}) for k in ('a0p', 'a0q', 'aperp1', 'apar1', 'varpi1', 'Om1')])
    # sign of A_N(1): positive for N <= 7, negative for N >= 8
    rs_e = sp.Poly(-(N**6 - 6*N**5 - 65*N**4 + 576*N**3 - 1632*N**2 + 1920*N - 800), N).nroots()
    rs_o = sp.Poly(-(3*N**4 - 12*N**3 - 230*N**2 + 1316*N - 1925), N).nroots()
    print("real roots of the even numerator:", [sp.N(r, 8) for r in rs_e if abs(sp.im(r)) < 1e-12])
    print("real roots of the odd quartic factor:", [sp.N(r, 8) for r in rs_o if abs(sp.im(r)) < 1e-12])
