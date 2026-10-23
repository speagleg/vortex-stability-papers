# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# Changes: none
"""definiteness threshold xi_EM and Krein windows from the exact determinant.

Independent recomputation (no archive code).  Blocks: closed forms derived in tanh_common.py.  d^2F is positive definite
on V_{>=1} iff, for every 1 <= m <= N-1, aperp_m > 0 and det_m = aperp_m apar_m - varpi_m^2 > 0 (2x2 Hermitian
blocks M_m).  With the cleared numerators (conventions) check aperp_m and
  check det_m = check aperp_m check apar_m - (1-xi)^2 check varpi_m^2 = 4(1-xi)^2(1-xi^N)^4 det_m,
xi_EM(N) = the largest zero in (0,1) over m of check aperp_m and check det_m (positivity above it is verified by
exact evaluation at a rational point), and xi_* = the zero of check aperp_crit.  All zeros are isolated rigorously
(python-flint), and the gap is certified by disjoint rational brackets.
Checks: N = 2..7 no zero of check det_m in (0,1) (definite at every radius); even N = 8..16: xi_EM = xi_* (the
critical det_m = aperp apar since varpi_{N/2} = 0); odd N = 9..15: xi_EM > xi_*, the zero belongs to det_crit, gap vs the
claim (3.220e-8, 1.244e-7, 1.777e-7, 1.886e-7); inside the window (rational midpoint): spectrally stable (all
aperp_m apar_m > 0), critical block indefinite (det_crit < 0 < aperp_crit), all other blocks definite; critical
eigenvalues A_0 lambda = -i varpi +- i sqrt(aperp apar) purely imaginary and distinct.
Whole window (odd N, referee 3): every root in (0,1) of check aperp_m, check det_m, m not in {crit, N-crit}, is < xi_* (arb); det_crit has one root; det_1, det_2 none.
Run: python tanh_krein.py   (deterministic)
"""
import os
import sys
import mpmath as mp
import flint
from flint import fmpq

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tanh_common import cleared, to_flint, blocks_mp  # noqa: E402
from tanh_threshold_polys import strip_one, roots01, eval_q, rat_bracket  # noqa: E402

flint.ctx.prec = 400
mp.mp.dps = 50
CLAIM_GAP = {9: 3.220e-8, 11: 1.244e-7, 13: 1.777e-7, 15: 1.886e-7}


def fq_to_mp(q):
    return mp.mpf(int(q.p)) / int(q.q)


def main():
    print(__doc__.split('\n')[0])
    for N in range(2, 17):
        crit = N // 2
        polys = {}
        for m in range(1, N):
            A, B, V, D = cleared(N, m)
            fA, fB, fD = to_flint(A), to_flint(B), to_flint(D)
            polys[m] = (fA, fB, fD)

        if N <= 7:
            nd = sum(len(roots01(strip_one(polys[m][2])[0])) for m in polys)
            pos = all(eval_q(polys[m][2], fmpq(1, 2)) > 0 and eval_q(polys[m][0], fmpq(1, 2)) > 0 for m in polys)
            print(f"N={N:2d}: zeros of check det_m in (0,1): {nd}; all aperp_m, det_m > 0 at 1/2: {pos} -> definite at every radius")
            continue
        xs = roots01(strip_one(polys[crit][0])[0]); assert len(xs) == 1
        xs = xs[0][0]
        # all zeros of det_m and aperp_m, largest
        allz = []
        for m in polys:
            for name, p in (('aperp', polys[m][0]), ('det', polys[m][2])):
                for r, e in roots01(strip_one(p)[0]):
                    allz.append((r, name, m, e))
        allz.sort(key=lambda t: float(t[0].mid()))
        rEM = allz[-1][0]
        holders = sorted({(n, m) for (r, n, m, e) in allz if r.overlaps(rEM)})
        lo, hi = rat_bracket(rEM)
        above = (hi + 1) / 2
        defin = all(eval_q(polys[m][0], above) > 0 and eval_q(polys[m][2], above) > 0 for m in polys)
        xs_mp = mp.mpf(xs.mid().str(60, radius=False)); xe_mp = mp.mpf(rEM.mid().str(60, radius=False))
        if N % 2 == 0:
            same = rEM.overlaps(xs) and (rEM - xs).rad() < flint.arb('1e-100')
            g = polys[crit][2].gcd(polys[crit][0])
            shared = len(roots01(strip_one(g)[0])) == 1
            print(f"N={N:2d}: xi_* = {mp.nstr(xs_mp, 30)}; xi_EM = {mp.nstr(xe_mp, 30)}; zero carriers {holders};"
                  f" |xi_EM - xi_*| < 1e-100: {same}; det_crit and aperp_crit share the factor of xi_*: {shared};"
                  f" definite above: {defin}")
            continue
        xlo, xhi = rat_bracket(xs)
        disjoint = xhi < lo
        gap = xe_mp - xs_mp
        mid = (xhi + lo) / 2
        spec = all(eval_q(polys[m][0], mid) * eval_q(polys[m][1], mid) > 0 for m in polys)
        crit_indef = eval_q(polys[crit][2], mid) < 0 and eval_q(polys[crit][0], mid) > 0
        others = all(eval_q(polys[m][2], mid) > 0 and eval_q(polys[m][0], mid) > 0
                     for m in polys if m not in (crit, N - crit))
        xm = fq_to_mp(mid)
        ap, bp, vp, _ = blocks_mp(N, crit, xm)
        A0 = 4 * xm / (1 - xm)**2
        lam = sorted([(-vp + s * mp.sqrt(ap * bp)) / A0 for s in (1, -1)] + [(vp + s * mp.sqrt(ap * bp)) / A0 for s in (1, -1)])
        dist = min(abs(lam[i + 1] - lam[i]) for i in range(3))
        print(f"N={N:2d}: xi_* = {mp.nstr(xs_mp, 30)}  xi_EM = {mp.nstr(xe_mp, 30)}  zero carriers {holders}")
        print(f"        gap xi_EM - xi_* = {mp.nstr(gap, 6)} (claim {CLAIM_GAP[N]:.3e}); rational brackets disjoint: {disjoint};"
              f" definite above xi_EM: {defin}")
        print(f"        window midpoint: spectrally stable {spec}; critical block indefinite {crit_indef}; all other blocks"
              f" definite {others}; critical frequencies Im(lambda) (modes m, N-m) = {[mp.nstr(l, 8) for l in lam]},"
              f" min separation {mp.nstr(dist, 3)}")
        assert disjoint and defin and spec and crit_indef and others and abs(gap / CLAIM_GAP[N] - 1) < 2e-3
        # whole-window exact check (referee 3): every root in (0,1) of check aperp_m, check det_m, m not in {crit, N-crit},
        # lies strictly below xi_* (arb comparison), so those blocks are positive definite on the whole window
        # (xi_*, 1) minus the critical gap; det_crit has exactly one root in (0,1); det_1, det_2 have none.
        max_other = None
        for m in polys:
            if m in (crit, N - crit):
                continue
            for p_ in (polys[m][0], polys[m][2]):
                for r, e in roots01(strip_one(p_)[0]):
                    assert r < xs, f"N={N} m={m}: root {r} not below xi_*"
                    if max_other is None or r > max_other:
                        max_other = r
        assert max_other is not None and max_other < xs
        assert len(roots01(strip_one(polys[crit][2])[0])) == 1
        assert not roots01(strip_one(polys[1][2])[0]) and not roots01(strip_one(polys[2][2])[0])
        print(f"N={N:2d}: non-critical blocks positive definite on whole window (max other root {mp.nstr(mp.mpf(max_other.mid().str(40, radius=False)), 12)}"
              f" < xi_* {mp.nstr(xs_mp, 12)}); det_crit has exactly one root in (0,1); det_1, det_2 have none: PASS")
    print("\nDONE (all assertions passed)")


if __name__ == '__main__':
    main()
