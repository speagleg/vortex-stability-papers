"""General-N closed forms on S^2 and H^2 (G model): the r^4 coefficient A_N(y) of the critical stiffness
and the threshold shift D_N, from the lattice-sum reduction with N symbolic (blocks.block_symbolic).

Validity: the closed forms of the lattice sums are used at arguments n + e m with |n| <= 2, e in {-1,0,1};
they apply for N >= 4 and 2 <= m <= N - 2, which contains the critical mode m = floor(N/2) for every N >= 4.
We compare with the closed forms as stated in the paper (eq. (3)), and evaluate them at N = 4..12 against the
per-N exact values computed independently by curved.py (outputs/curved.out).
"""
import sympy as sp
import blocks

N = blocks.Nsym_b
y, X, r2 = sp.symbols('y X r2', positive=True)


def crit_general(model, parity):
    msub = N / 2 if parity == 'even' else (N - 1) / 2
    b = blocks.block_symbolic(model, msub=msub)
    rho = blocks.rho
    conv = lambda ex: sp.factor(sp.cancel(sp.expand(ex.subs(rho, sp.sqrt(r2)))))
    a0 = conv(b['ss'][0]); d = conv(b['ss'][1])
    r2X = (1 - X) / (1 + X) if model == 'S2' else (X - 1) / (X + 1)
    a0X = sp.factor(sp.cancel(a0.subs(r2, r2X)))
    dX = sp.factor(sp.cancel(d.subs(r2, r2X)))
    return a0X, dX, b['shifts']


def paper_forms(parity):
    if parity == 'even':
        A = (-(N - 1) * (3 * N**2 - 12 * N + 10) / 32 * y**2
             + (N - 2) * (9 * N**4 + 179 * N**3 - 938 * N**2 + 1492 * N - 760) / 2304 * y
             - (N - 2)**2 * (N - 1) * (3 * N**3 + 6 * N**2 - 28 * N + 40) / 2304)
        D = (N - 2)**2 * (N - 1) * (3 * N**4 - 104 * N**3 + 612 * N**2 - 1088 * N + 640) / (288 * (N**2 - 8 * N + 8)**2)
        Th = sp.Rational(1, 4) * N**2 / (N - 1) - 1
    else:
        A = (-3 * (N - 3) * (N - 1)**2 / 32 * y**2
             + (N - 1)**2 * (9 * N**3 + 179 * N**2 - 965 * N + 1169) / 2304 * y
             - (N - 3) * (N - 1)**2 * (N**3 + 2 * N**2 - 11 * N + 12) / 768)
        D = (N - 3) * (N - 1) * (3 * N**3 - 101 * N**2 + 509 * N - 539) / (288 * (N - 7)**2)
        Th = sp.Rational(1, 4) * (N**2 - 1) / (N - 1) - 1
    return sp.expand(A), D, Th


if __name__ == '__main__':
    for model in ('S2', 'H2'):
        for parity in ('even', 'odd'):
            a0X, dX, shifts = crit_general(model, parity)
            mN = N / 2 if parity == 'even' else (N - 1) / 2
            target = sp.Rational(1, 2) * ((N - 1) * (1 + X**2) - sp.expand(N * N / 4 if parity == 'even' else (N * N - 1) / 4))
            c = sp.factor(sp.cancel(a0X / target))
            A = sp.factor(sp.cancel(dX / c * (1 - X**2)**2))
            Ay = sp.expand(sp.expand(A).subs(X, sp.sqrt(y)))
            Avt, Dvt, Th = paper_forms(parity)
            print(f"{model}, {parity} N (m = {mN}): normalisation c = {c}")
            print(f"   A_N(y) = {sp.collect(Ay, y, sp.factor)}")
            print(f"   A_N(y) - (form stated in the paper) = {sp.simplify(Ay - Avt)}")
            # D_N = -2 A_N(Theta)/((N-1)(1-Theta)^2) given a_perp^0 = (1/2)[(N-1)(1+y) - floor(N^2/4)]
            D = sp.factor(sp.simplify(-2 * Ay.subs(y, Th) / ((N - 1) * (1 - Th)**2)))
            print(f"   D_N = {D}")
            print(f"   D_N - (form stated in the paper) = {sp.simplify(D - Dvt)}")

    # per-N exact values from curved.py (outputs/curved.out), N = 4..12
    PER_N = {4: (-sp.Rational(15, 16), sp.Rational(55, 16), -sp.Rational(9, 8), sp.Rational(1, 8)),
             5: (-3, sp.Rational(27, 2), -sp.Rational(11, 2), -1),
             6: (-sp.Rational(115, 16), sp.Rational(1547, 36), -sp.Rational(230, 9), -sp.Rational(380, 9)),
             7: (-sp.Rational(27, 2), 98, -sp.Rational(141, 2), None),
             8: (-sp.Rational(371, 16), sp.Rational(3319, 16), -sp.Rational(1519, 8), -sp.Rational(539, 4)),
             9: (-36, sp.Rational(3386, 9), -402, -sp.Rational(244, 3)),
             10: (-sp.Rational(855, 16), sp.Rational(1315, 2), -840, -sp.Rational(2880, 49)),
             11: (-75, 1050, -1525, -55),
             12: (-sp.Rational(1639, 16), sp.Rational(236255, 144), -sp.Rational(197725, 72), -sp.Rational(179575, 3528))}
    bad = 0
    for n, (c2, c1, c0, Dn) in PER_N.items():
        A, Dg, Th = paper_forms('even' if n % 2 == 0 else 'odd')
        if sp.expand(A.subs(N, n) - (c2 * y**2 + c1 * y + c0)) != 0:
            bad += 1
        if Dn is not None and sp.simplify(Dg.subs(N, n) - Dn) != 0:
            bad += 1
    print("general-N forms evaluated at N = 4..12 versus the per-N exact results of curved.py: mismatches =", bad)
