# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# Changes: none
"""tanh threshold polynomials f_N (N = 8..16), irreducibility, palindromy,
degrees, Arb roots, the N = 8 unit and non-integrality for N = 9..16; exact sign structure of the blocks, N = 2..16.

Independent recomputation (no archive code).  The blocks are the closed forms derived in tanh_common.py.
Steps:
 (a) symbolic identity of the derived blocks with the havelock note's Theorem 2 (typed from the claim text), N = 2..16,
     all m; the weights W_k: (1-x^N)^2 sum_{n<=k+PN, n=k mod N} n x^n agrees with k x^k (1-x^N) + N x^{k+N} up to
     degree k+PN (P = 6), N = 2..16, k = 1..N;
 (b) cleared numerators (conventions: check aperp = 2(1-xi)^2(1-xi^N)^2 aperp etc.) are integer polynomials; the
     self-reciprocity check aperp(1/xi) = xi^{-2N-2} check aperp(xi) (L5) and the analogues for apar, varpi;
 (c) exact real-root counts on (0,1) of every check aperp_m, check apar_m (flint isolation, cross-checked by sympy's
     exact Sturm count): N <= 7 no zeros; 8 <= N <= 16: apar_m > 0, aperp_1, aperp_2 > 0, aperp_m (3 <= m <
     floor(N/2)) one simple zero below xi_*, aperp_crit exactly one zero xi_*, sign - to +;
 (d) factorisation over Z of check aperp_crit (python-flint), the factor f_N carrying xi_*: irreducible, primitive,
     palindromic, degree and leading coefficient; a mod-p irreducibility witness; trace polynomial g with
     f_N(x) = x^{n/2} g(x + 1/x) and its irreducibility;
 (e) xi_* from Arb (prec 400) to 50 digits, exact rational sign change, comparison with the archive certified values
     (certify_v2.out, typed below as constants), cosh r_* = (1+xi_*)/(1-xi_*);
 (f) N = 8: f_8 monic with constant term 1 (unit), degree 10, equal to the stated polynomial; N = 9..16: lead != +-1.
Run: python tanh_threshold_polys.py   (deterministic)
"""
import os
import sys
import sympy as sp
import mpmath as mp
import flint
from flint import fmpz_poly, fmpq, nmod_poly, arb

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tanh_common import x, blocks_sym, blocks_T2_literal, cleared, to_flint  # noqa: E402

flint.ctx.prec = 400
mp.mp.dps = 60

ARCHIVE_XI = {  # havelock-vortex-rings@2cc1ee5:tanh/certify_v2.out (55 printed digits), comparison only
    8: '0.06735622300408126226843747656623557439402511756974286746',
    9: '0.1128710632366027404396940190565054155465126211997598489',
    10: '0.1661142415262391180817586997848971841127721310135217286',
    11: '0.2046011768826692906355358331548029981500666180946277148',
    12: '0.2474177768040677091739650887199179457129297666808108510',
    13: '0.2798613886439066870299965646856616022348139775529566969',
    14: '0.3149389631155066233935054633810836766939603932829221397',
    15: '0.3424585835121702566010226386713207317144169141137213274',
    16: '0.3716818139060454566367287813218700082934780664483868026',
}
CLAIM_DEG = {8: 10, 9: 16, 10: 12, 11: 20, 12: 16, 13: 24, 14: 18, 15: 28, 16: 22}
CLAIM_LEAD = {8: 1, 9: 4, 10: 7, 11: 10, 12: 7, 13: 18, 14: 23, 15: 28, 16: 17}
F8_CLAIM = [1, -12, -37, -72, -84, -88, -84, -72, -37, -12, 1]  # x^10 ... 1
G8_CLAIM = [1, -12, -42, -24, 32, 32]  # C^5 ... 1

XF = fmpz_poly([0, 1])
ONE_MINUS_X = fmpz_poly([1, -1])


def strip_one(p):
    """Remove factors (x-1) and x; return (p', mult at 1, mult at 0)."""
    k1 = k0 = 0
    while p(1) == 0:
        p = p // fmpz_poly([-1, 1]); k1 += 1
    while p(0) == 0:
        p = p // XF; k0 += 1
    return p, k1, k0


def roots01(p):
    """Rigorously isolated real roots of p in (0,1) (with multiplicity), via flint complex_roots on the squarefree
    factorisation.  Fails loudly on an ambiguous ball."""
    out = []
    c, fac = p.factor_squarefree()
    for q, e in fac:
        for r, _ in q.complex_roots():
            if r.imag != 0:
                assert not (r.imag.contains(0)), "ambiguous imaginary part"
                continue
            re = r.real
            if re > 0 and re < 1:
                out.append((re, e))
            else:
                assert (re < 0 or re > 1 or re == 0 or re == 1) or not (re.contains(0) or re.contains(1)), "ambiguous"
    return sorted(out, key=lambda t: float(t[0].mid()))


def sturm01(P):
    """sympy exact count of roots of P (Poly in x, roots at 0 and 1 removed) in the closed interval [0,1]."""
    return P.count_roots(0, 1)


def to_sym(p):
    return sp.Poly(list(reversed([int(c) for c in p.coeffs()])), x)


def eval_q(p, q):
    """Exact evaluation of an fmpz_poly at a rational fmpq."""
    acc = fmpq(0)
    for c in reversed(p.coeffs()):
        acc = acc * q + c
    return acc


def rat_bracket(ball):
    """Rational lo < root < hi: the 90-digit decimal midpoint -+ 1e-80 (requires Arb radius < 1e-85)."""
    assert ball.rad() < arb('1e-85')
    s = ball.mid().str(90, radius=False)
    mant, _, ex = s.partition('e')
    ip, _, fp = mant.partition('.')
    q = fmpq(int(ip + fp), 10 ** len(fp))
    if ex:
        q = q * fmpq(10) ** int(ex) if int(ex) >= 0 else q / fmpq(10) ** (-int(ex))
    eps = fmpq(1, 10 ** 80)
    return q - eps, q + eps


def reciprocal(p, deg):
    """x^deg p(1/x)."""
    c = list(p.coeffs()) + [0] * (deg + 1 - len(p.coeffs()))
    return fmpz_poly(list(reversed(c[:deg + 1])))


def trace_poly(f):
    """g with f(x) = x^d g(x + 1/x), deg f = 2d, f palindromic (Dickson recursion)."""
    a = [int(c) for c in f.coeffs()]
    d = (len(a) - 1) // 2
    C = sp.Symbol('C')
    D = [sp.Integer(2), C]
    for i in range(2, d + 1):
        D.append(sp.expand(C * D[-1] - D[-2]))
    g = a[d] + sum(a[d + i] * D[i] for i in range(1, d + 1))
    return sp.Poly(sp.expand(g), C)


def main():
    print(__doc__.split('\n')[0])
    # (a)
    bad = 0
    for N in range(2, 17):
        for m in range(1, N):
            d = blocks_sym(N, m)[:3]
            t = blocks_T2_literal(N, m)
            for u, v in zip(d, t):
                if sp.cancel(u - v) != 0:
                    bad += 1
    print(f"(a) derived blocks - note Thm 2 literal: nonzero differences over N=2..16, m=1..N-1 (aperp, apar, varpi): {bad}")
    badW = 0
    P = 6
    for N in range(2, 17):
        for k in range(1, N + 1):
            ser = sum((k + p * N) * x**(k + p * N) for p in range(P + 1))
            lhs = sp.Poly(sp.expand((1 - x**N)**2 * ser), x)
            rhs = sp.Poly(k * x**k * (1 - x**N) + N * x**(k + N), x)
            diff = (lhs - rhs).all_coeffs()[::-1]
            if any(diff[i] != 0 for i in range(min(len(diff), k + P * N + 1))):
                badW += 1
    print(f"    W_k closed form vs series (N=2..16, k=1..N, through degree k+{P}N): mismatches {badW}")

    # (b), (c)
    print("\n(b,c) cleared numerators: reciprocity and exact zero structure on (0,1)")
    xi_star = {}
    recip_bad = 0
    for N in range(2, 17):
        crit = N // 2
        zeros = {}
        for m in range(1, N):
            A, B, V, det = cleared(N, m)
            fA, fB, fV = to_flint(A), to_flint(B), to_flint(V)
            # reciprocity: check aperp of degree 2N+2 palindromic-type (x^{2N+2} A(1/x) = A), apar: x^{2N} B(1/x) = B,
            # varpi: x^{2N} V(1/x) = -V
            if reciprocal(fA, 2 * N + 2) != fA or reciprocal(fB, 2 * N) != fB or reciprocal(fV, 2 * N) != -fV:
                recip_bad += 1
            rA = roots01(strip_one(fA)[0]); rB = roots01(strip_one(fB)[0])
            sA = sturm01(to_sym(strip_one(fA)[0])); sB = sturm01(to_sym(strip_one(fB)[0]))
            assert sA == sum(e for _, e in rA) and sB == sum(e for _, e in rB), "flint/sympy root count mismatch"
            zeros[m] = (rA, rB, fA, fB)
        nB = sum(len(zeros[m][1]) for m in zeros)
        signB = all(eval_q(zeros[m][3], fmpq(1, 2)) > 0 for m in zeros)
        if N <= 7:
            nA = sum(len(zeros[m][0]) for m in zeros)
            signA = all(eval_q(zeros[m][2], fmpq(1, 2)) > 0 for m in zeros)
            print(f"  N={N:2d}: zeros of check aperp_m in (0,1): {nA}; of check apar_m: {nB}; all positive at 1/2: {signA and signB}")
            continue
        rc = zeros[crit][0]
        assert len(rc) == 1 and rc[0][1] == 1, f"N={N}: crit mode zero count {rc}"
        xs = rc[0][0]
        xi_star[N] = (xs, zeros[crit][2])
        others = []
        for m in range(1, crit):
            r = zeros[m][0]
            others.append((m, len(r), all(z < xs for z, _ in r), all(e == 1 for _, e in r)))
        ok12 = others[0][1] == 0 and others[1][1] == 0 and eval_q(zeros[1][2], fmpq(1, 2)) > 0 and eval_q(zeros[2][2], fmpq(1, 2)) > 0
        ok3 = all(n == 1 and below and simple for (m, n, below, simple) in others[2:])
        print(f"  N={N:2d}: apar_m zeros {nB}, positive at 1/2 {signB}; crit m={crit}: one simple zero; aperp_1, aperp_2 zero-free"
              f" and positive: {ok12}; m=3..{crit - 1}: one simple zero each, below xi_*: {ok3}  "
              f"[counts {[(m, n) for (m, n, _, _) in others]}]")
    print(f"  reciprocity failures (x^(2N+2) A(1/x)=A, x^(2N) B(1/x)=B, x^(2N) V(1/x)=-V): {recip_bad}")

    # (d), (e), (f)
    print("\n(d,e,f) critical numerator factorisation, f_N, roots")
    for N in range(8, 17):
        xs, A = xi_star[N]
        crit = N // 2
        cont, fac = A.factor()
        f = None
        desc = []
        for q, e in fac:
            r = roots01(q)
            desc.append(f"({q.degree()}:{q.leading_coefficient()})^{e}" + (" [xi_*]" if r else ""))
            if r:
                assert f is None and e == 1
                f = q
        if f.leading_coefficient() < 0:
            f = -f
        pal = reciprocal(f, f.degree()) == f
        prim = f.content() == 1
        deg = f.degree(); lead = int(f.leading_coefficient())
        pat = 2 * N - 2 if N % 2 else (3 * N // 2 - 2 if N % 4 == 0 else 3 * N // 2 - 3)
        # mod-p irreducibility witness
        wit = None
        for p in sp.primerange(3, 2000):
            if lead % p == 0:
                continue
            fp = nmod_poly([int(c) % p for c in f.coeffs()], int(p))
            fl = fp.factor()[1]
            if len(fl) == 1 and fl[0][1] == 1 and fl[0][0].degree() == deg:
                wit = int(p); break
        # other factors, symbolic description for even N
        shape = ''
        if N % 2 == 0:
            expect = fmpz_poly([1, -1]) ** 4 * (fmpz_poly([1] + [0] * (N // 2 - 1) + [1]))
            if N % 4 == 2:
                expect = expect * fmpz_poly([1, 1])
            q, r = divmod(A, expect * f)
            shape = f"A_crit = ({q}) (x-1)^4 (x^{N // 2}+1){' (x+1)' if N % 4 == 2 else ''} f_N exactly: {r == 0 and q.degree() == 0}"
        g = trace_poly(f)
        gf = to_flint(g)
        g_irred = len(gf.factor()[1]) == 1 and gf.factor()[1][0][1] == 1
        # root and rational sign change
        lo, hi = rat_bracket(xs)
        sgn = (eval_q(A, lo) < 0) and (eval_q(A, hi) > 0) and (eval_q(f, lo) * eval_q(f, hi) < 0)
        xs_mp = mp.mpf(xs.mid().str(60, radius=False))
        arch = mp.mpf(ARCHIVE_XI[N])
        X0 = (1 + xs_mp) / (1 - xs_mp)
        print(f"  N={N:2d}: factors (deg:lead)^mult {' '.join(desc)}; content {cont}")
        if shape:
            print(f"        {shape}")
        print(f"        f_N: degree {deg} (claim {CLAIM_DEG[N]}, pattern {pat}), lead {lead} (claim {CLAIM_LEAD[N]}),"
              f" primitive {prim}, palindromic {pal}, irreducible over Z (flint) True, irreducible mod {wit}")
        print(f"        trace poly g (deg {g.degree()}) irreducible {g_irred}: {g.as_expr()}")
        print(f"        xi_* = {xs.mid().str(50, radius=False)}  (Arb radius {mp.nstr(mp.mpf(xs.rad().str(5, radius=False)), 3)})")
        print(f"        rational sign change A_crit(lo)<0<A_crit(hi), width {hi - lo}: {sgn}")
        print(f"        |xi_* - archive| = {mp.nstr(abs(xs_mp - arch), 3)}   cosh r_* = {mp.nstr(X0, 12)}  sqrt xi_* = {mp.nstr(mp.sqrt(xs_mp), 12)}")
        assert deg == CLAIM_DEG[N] == pat and lead == CLAIM_LEAD[N] and pal and prim and sgn and abs(xs_mp - arch) < mp.mpf('1e-50')
        if N == 8:
            coeffs = [int(c) for c in reversed(f.coeffs())]
            print(f"        N=8: f_8 = stated polynomial: {coeffs == F8_CLAIM}; monic {lead == 1}, constant {int(f.coeffs()[0])}"
                  f" -> xi_*(8) algebraic integer with algebraic-integer inverse: unit of degree {deg}")
            print(f"        N=8: g = stated C^5-12C^4-42C^3-24C^2+32C+32: {[int(c) for c in g.all_coeffs()] == G8_CLAIM};"
                  f" C = xi+1/xi = {mp.nstr(xs_mp + 1 / xs_mp, 15)} = 2+4/sinh^2 r_* = {mp.nstr(2 + 4 / (X0**2 - 1), 15)}")
        else:
            print(f"        N={N}: primitive irreducible with lead {lead} != +-1 -> xi_*(N) is not an algebraic integer")
    print("\nDONE (all assertions passed)")


if __name__ == '__main__':
    main()
