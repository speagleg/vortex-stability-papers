# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# Changes: renamed; internal labels replaced by references to this paper
"""One curve across kappa = 1?  Threshold rings versus the hypercycle threshold branch.

Uses the ring blocks and exact symbol (paper Thms 3.1, 3.3), the certified xi_* (Table 1), the second-order formula
(Prop 5.3), the hypercycle-row symbol and the dual series (Prop 6.1, Thm 6.7), and the horocycle limit (Thm 6.6(c)).

Notation: ring threshold r_*(N) (critical mode m = floor(N/2)), kappa_N = coth r_*(N), l_N = 2 pi sinh r_*(N)/N,
X_{0*} = cosh r_*, tau = N artanh(1/X0).  Hypercycle row: kappa = cos alpha, l = l_u/sin alpha, threshold l^*(kappa).

Objects introduced here (local names, not conventions symbols):
  E(kappa, l) = (pi kappa/l) coth(2 pi rho/l) - (pi^2/(4 l^2)) coth^2(pi rho/l) - (2 kappa^2 - 1)/4,
     rho = arccos(kappa)/sqrt(1-kappa^2) (kappa<1), arcosh(kappa)/sqrt(kappa^2-1) (kappa>1), 1 (kappa=1);
  so calF^mod (dual series, Thm 6.7) at l_u = l sin alpha is E(cos alpha, l) - 2 alpha cos(alpha)/l.
  E is real-analytic in kappa through kappa = 1 (rho is analytic in kappa); the term -2 alpha kappa/l is odd in alpha
  and has a square-root branch point at kappa = 1.  l^E(kappa) := root of E(kappa, l) = 0 near l_*.
"""
import mpmath as mp

mp.mp.dps = 50

XI_CERT = {  # Table 1 (certified digits as printed)
    8: '0.0673562230040812622684374', 9: '0.1128710632366027404396940', 10: '0.1661142415262391180817586',
    11: '0.2046011768826692906355358', 12: '0.2474177768040677091739650', 13: '0.2798613886439066870299965',
    14: '0.3149389631155066233935054', 15: '0.3424585835121702566010226', 16: '0.3716818139060454566367287'}


def lan(x):
    return mp.coth(x) - 1 / x


def ahat_inf(t):
    return ((4 / t) * mp.tanh(t / 2) - lan(t / 2) ** 2) / 8


def Psi(mh, t):
    ch = mp.cosh(t) * mp.cosh(mh * t) - mh * mp.sinh(t) * mp.sinh(mh * t)
    return (1 - mh ** 2) / 8 + ch / (4 * mp.sinh(t) ** 2)


def aperp_symbol(N, m, t):
    """a_perp_m/N^2 from the exact symbol (Thm 3.3), X0 = coth(tau/N)."""
    X0 = mp.coth(t / N)
    EN = X0 / N * mp.coth(t) - X0 ** 2 / (2 * N ** 2) - mp.mpf(1) / (2 * N ** 2)
    mh = 1 - mp.mpf(2 * m) / N
    return EN - 1 / (4 * mp.sinh(t) ** 2) - Psi(mh, t)


def aperp_blocks(N, m, xi):
    """a_perp_m from the Fourier blocks (Thm 3.1; rational in xi)."""
    X0 = (1 + xi) / (1 - xi)
    xN = xi ** N
    return ((N - 1) * X0 - (X0 - 1) ** 2 / 2 - mp.mpf(m * (N - m)) / 2 + 2 * N * X0 * xN / (1 - xN)
            - N ** 2 * xN / (1 - xN) ** 2
            - mp.mpf(N) / 2 * (m * xi ** m + (N - m) * xi ** (N - m) + (N - m) * xi ** (N + m) + m * xi ** (2 * N - m)) / (1 - xN) ** 2)


def rho_of(k):
    if k < 1:
        return mp.acos(k) / mp.sqrt(1 - k ** 2)
    if k > 1:
        return mp.acosh(k) / mp.sqrt(k ** 2 - 1)
    return mp.mpf(1)


def Efun(k, l):
    rho = rho_of(k)
    return (mp.pi * k / l * mp.coth(2 * mp.pi * rho / l) - mp.pi ** 2 / (4 * l ** 2) * mp.coth(mp.pi * rho / l) ** 2
            - (2 * k ** 2 - 1) / 4)


def F_pi_modular(al, lu, nmax=60):
    """calF(pi) of the G_1 hypercycle row via the dual series (Thm 6.7; complex-safe)."""
    qt = mp.exp(-2 * mp.pi ** 2 / lu)
    Fm = (mp.pi * mp.sin(2 * al) / (2 * lu) * mp.coth(2 * mp.pi * al / lu)
          - mp.pi ** 2 * mp.sin(al) ** 2 / (4 * lu ** 2) * mp.coth(mp.pi * al / lu) ** 2
          - al * mp.sin(2 * al) / lu - mp.cos(2 * al) / 4)
    s1 = mp.fsum(qt ** (2 * n) / (1 - qt ** (2 * n)) * (mp.sin(2 * al) * mp.sinh(4 * mp.pi * n * al / lu)
                                                       - 4 * mp.pi * n * mp.sin(al) ** 2 / lu) for n in range(1, nmax))
    s2 = mp.fsum(n * qt ** n / (1 - qt ** n) * (1 + mp.cosh(2 * mp.pi * n * al / lu)) for n in range(1, nmax))
    return Fm - 2 * mp.pi / lu * s1 - 2 * mp.pi ** 2 * mp.sin(al) ** 2 / lu ** 2 * s2


def F_pi_direct(al, lu, J=None):
    K = mp.cos(al) ** 2
    s2 = mp.sin(al) ** 2
    if J is None:
        J = int(160 / lu) + 20
    tot = mp.mpf(0)
    for j in range(1, J):
        c = mp.cosh(j * lu)
        D = c + 1 - 2 * K
        den = (c - 1) * D ** 2
        B0 = s2 * ((3 * K - 1) * c ** 2 - (4 * K ** 2 - K + 1) * c + 2 * K ** 2) / den
        B1 = s2 * (K * c ** 2 + (1 - 3 * K) * c + 2 * K ** 2 - 2 * K + 1) / den
        tot += B0 + (-1) ** j * B1
    return tot


def main():
    print("threshold rings vs the hypercycle branch; mp.dps =", mp.mp.dps)
    tinf = mp.findroot(ahat_inf, mp.mpf('7.445'))
    lstar = 2 * mp.pi / tinf
    print("tau_inf =", mp.nstr(tinf, 30), " l_* = 2 pi/tau_inf =", mp.nstr(lstar, 30))
    ok_l = abs(lstar - mp.mpf('0.8439085312925')) < 1e-13
    print(f"  {'PASS' if ok_l else 'FAIL'}  l_* agrees with conventions 0.8439085312925")
    # varsigma from the second-order formula (Prop 5.3)
    dA = abs(mp.diff(ahat_inf, tinf))
    Pmm = -mp.mpf(1) / 4 + (tinf ** 2 * mp.cosh(tinf) - 2 * tinf * mp.sinh(tinf)) / (4 * mp.sinh(tinf) ** 2)
    base = (tinf * mp.coth(tinf) - 1) / 3 - mp.mpf(1) / 2
    se = tinf / 3 - base / (dA * tinf ** 2)
    so = tinf / 3 - (base - Pmm / 2) / (dA * tinf ** 2)
    print("varsigma formula: even", mp.nstr(se, 25), " odd", mp.nstr(so, 25))

    # ---------------- thresholds ----------------
    def threshold(N):
        m = N // 2
        f = lambda t: aperp_symbol(N, m, t)
        t0 = N * mp.atanh(1 / (N / tinf + (se if N % 2 == 0 else so) / N)) if N >= 12 else None
        if t0 is None:
            xi0 = mp.mpf(XI_CERT.get(N, '0.3'))
            t0 = -N * mp.log(xi0) / 2
        return mp.findroot(f, t0, tol=mp.mpf(10) ** -45)

    res = {}
    worst_cert = mp.mpf(0)
    worst_blk = mp.mpf(0)
    for N in range(8, 129):
        t = threshold(N)
        xi = mp.exp(-2 * t / N)
        X0 = mp.coth(t / N)
        r = mp.acosh(X0)
        res[N] = dict(tau=t, xi=xi, X0=X0, r=r, kap=mp.coth(r), l=2 * mp.pi * mp.sinh(r) / N)
        if N in XI_CERT:
            worst_cert = max(worst_cert, abs(xi - mp.mpf(XI_CERT[N])))
        if N <= 40:
            worst_blk = max(worst_blk, abs(aperp_blocks(N, N // 2, xi)) / N ** 2)
    ok1 = worst_cert < mp.mpf(10) ** -24
    ok2 = worst_blk < mp.mpf(10) ** -40
    print(f"  {'PASS' if ok1 else 'FAIL'}  new roots reproduce certified xi_*(N), N=8..16 (25 printed digits): max dev {mp.nstr(worst_cert, 3)}")
    print(f"  {'PASS' if ok2 else 'FAIL'}  roots of the exact symbol are roots of the rational block a_perp_floor(N/2) (N<=40): {mp.nstr(worst_blk, 3)}")

    # varsigma extraction (Richardson in 1/N^2 on each parity)
    def richardson(Ns):
        # fit s_N = c0 + c1/N^2 + ... + c_{k}/N^{2k} through len(Ns) points
        n = len(Ns)
        A = mp.matrix(n, n)
        b = mp.matrix(n, 1)
        for i, N in enumerate(Ns):
            for k in range(n):
                A[i, k] = mp.mpf(N) ** (-2 * k)
            b[i] = (res[N]['X0'] - N / tinf) * N
        return mp.lu_solve(A, b)[0]
    ext = {}
    for par, Ns_sets in (("even", [list(range(108, 129, 4)), list(range(118, 129, 2))]),
                         ("odd", [list(range(107, 128, 4)), list(range(117, 128, 2))])):
        vals = [richardson(Ns) for Ns in Ns_sets]
        ext[par] = vals
        tgt = se if par == "even" else so
        print(f"  varsigma_{par[0]}: Richardson {mp.nstr(vals[0], 20)} / {mp.nstr(vals[1], 20)}, formula {mp.nstr(tgt, 20)},"
              f" |diff| {mp.nstr(abs(vals[1] - tgt), 3)}")
    ok3 = abs(ext["even"][1] - se) < 1e-12 and abs(ext["odd"][1] - so) < 1e-12
    print(f"  {'PASS' if ok3 else 'FAIL'}  second-order constants (Prop 5.3) confirmed to 1e-12 (numerically)")

    # ---------------- E-curve ----------------
    def lE(k, l0=None):
        return mp.findroot(lambda l: Efun(k, l), l0 if l0 is not None else lstar, tol=mp.mpf(10) ** -45)
    ok4 = abs(lE(mp.mpf(1)) - lstar) < mp.mpf(10) ** -40
    print(f"  {'PASS' if ok4 else 'FAIL'}  E(1, l) = I(l) of eq. (8): l^E(1) = l_*")
    dI = mp.diff(lambda l: Efun(mp.mpf(1), l), lstar)
    c1 = 2 / (lstar * dI)
    print("\nTable: N, parity, kappa_N - 1, l_N, N^2 (l_N - l_*), N^2 (l_N - l^E(kappa_N)), N^2 (Re l_c - l_N)")
    print("  (l_c: complex root of calF^mod(alpha = i a, l_u = i l sinh a) = 0 continuing the hypercycle root, the literal")
    print("   alpha-continuation of the modular-part threshold; shown for N >= 16, where Newton from l_N + i c1 a tracks that branch)")
    worst_even = mp.mpf(0)
    odd_res = {}
    for N in range(8, 129):
        d = res[N]
        k = d['kap']
        le = lE(k, d['l'])
        a = mp.acosh(k)
        fc = lambda l: (lambda al, lu: (mp.pi * mp.sin(2 * al) / (2 * lu) * mp.coth(2 * mp.pi * al / lu)
                                        - mp.pi ** 2 * mp.sin(al) ** 2 / (4 * lu ** 2) * mp.coth(mp.pi * al / lu) ** 2
                                        - al * mp.sin(2 * al) / lu - mp.cos(2 * al) / 4))(1j * a, 1j * l * mp.sinh(a))
        try:
            lc = mp.findroot(fc, mp.mpc(d['l'], c1 * a), tol=mp.mpf(10) ** -40)
        except Exception:
            lc = mp.mpc(mp.nan)
        if N % 2 == 0:
            worst_even = max(worst_even, abs(le - d['l']))
        else:
            odd_res[N] = N ** 2 * (d['l'] - le)
        if N <= 16 or N in (24, 32, 33, 48, 63, 64, 65, 96, 97, 127, 128):
            print(f"  {N:4d} {'e' if N % 2 == 0 else 'o'} {mp.nstr(k - 1, 12):>20} {mp.nstr(d['l'], 20):>24}"
                  f" {mp.nstr(N ** 2 * (d['l'] - lstar), 12):>16} {mp.nstr(N ** 2 * (d['l'] - le), 12):>18}"
                  f" {(mp.nstr(N ** 2 * (lc.real - d['l']), 10) if N >= 16 else 'n/a'):>14}{'  (certified xi_*)' if N <= 16 else ''}")
    ok5 = worst_even < mp.mpf(10) ** -40
    print(f"  {'PASS' if ok5 else 'FAIL'}  even N = 8..128: l_N = l^E(kappa_N) exactly (max |diff| {mp.nstr(worst_even, 3)})")
    lim_odd = 2 * mp.pi * (so - se)
    last = [odd_res[N] for N in (125, 127)]
    print(f"  odd N: N^2 (l_N - l^E(kappa_N)) -> {mp.nstr(last[-1], 12)} at N=127; 2 pi (varsigma_o - varsigma_e) = {mp.nstr(lim_odd, 12)}")
    ok6 = abs(last[-1] - lim_odd) < 1e-2
    print(f"  {'PASS' if ok6 else 'FAIL'}  odd N deviate at O(N^-2) (not O(N^-4)): the parity split of varsigma")

    # ---------------- hypercycle branch near kappa = 1 ----------------
    print("\nHypercycle branch l^*(kappa), kappa = cos alpha < 1, from calF(pi) = 0 (modular-dual form, checked against the direct sum):")
    chk = abs(F_pi_modular(mp.mpf('0.3'), mp.mpf('0.5')) - F_pi_direct(mp.mpf('0.3'), mp.mpf('0.5')))
    chk2 = abs(F_pi_modular(mp.mpf('1.1'), mp.mpf('1.3')) - F_pi_direct(mp.mpf('1.1'), mp.mpf('1.3')))
    ok7 = max(chk, chk2) < mp.mpf(10) ** -40
    print(f"  {'PASS' if ok7 else 'FAIL'}  modular-dual form = direct lattice sum at (alpha,l_u) = (0.3,0.5), (1.1,1.3): {mp.nstr(max(chk, chk2), 3)}")
    print("  prediction: l^*(cos alpha) - l^E(cos alpha) = c1 alpha + O(alpha^2), c1 = 2/(l_* I'(l_*)) =", mp.nstr(c1, 15))
    print("   alpha        kappa              l^*(kappa)              l^E(kappa)             (l^* - l^E)/alpha")
    prev = lstar
    ratios = []
    for al in ['0.4', '0.2', '0.1', '0.05', '0.025', '0.0125']:
        al = mp.mpf(al)
        k = mp.cos(al)
        le = lE(k)
        ls = mp.findroot(lambda l: F_pi_modular(al, l * mp.sin(al)), le + c1 * al, tol=mp.mpf(10) ** -40)
        ratios.append((ls - le) / al)
        print(f"   {mp.nstr(al, 6):8} {mp.nstr(k, 16):>18} {mp.nstr(ls, 20):>24} {mp.nstr(le, 20):>24} {mp.nstr((ls - le) / al, 15):>20}")
    als = [mp.mpf('0.05'), mp.mpf('0.025'), mp.mpf('0.0125')]
    A3 = mp.matrix([[1, x, x ** 2] for x in als])
    ext1 = mp.lu_solve(A3, mp.matrix(ratios[-3:]))[0]
    print(f"  Richardson (quadratic in alpha, last 3 points): lim (l^* - l^E)/alpha = {mp.nstr(ext1, 12)}  vs c1 = {mp.nstr(c1, 12)}")
    ok8 = abs(ext1 - c1) < mp.mpf('1e-3') * abs(c1)
    print(f"  {'PASS' if ok8 else 'FAIL'}  (l^* - l^E)/alpha -> c1 (nonzero): l^*(kappa) = l^E(kappa) + c1 sqrt(2(1-kappa)) + O(1-kappa):")
    print("        square-root branch point at kappa = 1 in kappa (and in kappa^2 - 1); analytic in alpha up to the")
    print("        beyond-all-orders dual-nome terms O(alpha^-1 exp(-2 pi^2/(l sin alpha))).")
    print("Summary: (i) the alpha-odd term -alpha sin(2 alpha)/l_u of calF^mod obstructs an analytic continuation of l^* in kappa;")
    print("         (ii) the alpha-even part l^E(kappa) continues analytically through (1, l_*) and passes EXACTLY through every")
    print("              even-N threshold ring (to 40 digits, N = 8..128);")
    print("         (iii) odd-N threshold rings miss l^E by 2 pi (varsigma_o - varsigma_e)/N^2 + O(N^-4) (critical mode q = pi - pi/N);")
    print("         (iv) hence l_N = l*_cont(kappa_N) + O(N^-4) holds (exactly) for even N with l*_cont = l^E and fails at O(N^-2) for odd N.")
    allok = all([ok_l, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8])
    print("OVERALL", "PASS" if allok else "FAIL")


if __name__ == "__main__":
    main()
