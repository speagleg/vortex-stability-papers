"""Contour dynamics versus the r^4 block formulas (Theorem 3.3), N = 4..8, every Bloch mode m = 1..floor(N/2).

For each (N, m) the two slow eigenvalues lambda_1, lambda_2 of the Bloch block (normalised units, ring radius 1,
centroid pinned at radius 1) give
    s     = ((lambda_1 - lambda_2)/2)^2  = -a_perp a_par
    varpi = i (lambda_1 + lambda_2)/2
(Section 2: the block [[a_perp, i varpi], [-i varpi, a_par]] has eigenvalues -i varpi +- sqrt(-a_perp a_par)).
With a_perp = a0 + d eps, a_par = b0 + e eps, varpi = w eps (eps = a^4), the theory predicts
    (s + a0 b0)/eps -> -(a0 e + b0 d),     varpi/eps -> w      as a -> 0,
and for N = 7, m = 3 (a0 = 0): s/eps -> -84.  We fit f(a) = c0 + c1 a^2 + c2 a^4 on a = 0.03..0.08 and
compare c0 with the exact values.
"""
import sys
import numpy as np
import cd
from fractions import Fraction

EXACT = {}   # (N, m) -> (a0, b0, d, e, w), from plane_general.py / blocks.py (exact rationals)


def exact_blocks(N, m):
    a0 = Fraction(2 * (N - 1) - m * (N - m), 2)
    b0 = Fraction(m * (N - m), 2)
    # closed forms of Theorem 3.3 (valid for 1 <= m <= N-1)
    d = Fraction(-N**4*m**2 + 6*N**4 - 6*N**3*m**3 + 18*N**3*m**2 + 24*N**3*m - 72*N**3 + 23*N**2*m**4
                 - 36*N**2*m**3 - 21*N**2*m**2 - 144*N**2*m + 276*N**2 - 24*N*m**5 + 18*N*m**4 - 6*N*m**3
                 + 144*N*m**2 + 120*N*m - 360*N + 8*m**6 + 3*m**4 - 120*m**2 + 150, 144)
    e = Fraction(m**2 * (N - m)**2 * (5*N**2 - 8*N*m - 18*N + 8*m**2 + 33), 144)
    w = Fraction(-m * (m - N) * (2*m - N) * (-N**2 - 3*N*m + 6*N + 3*m**2 - 5), 36)
    return a0, b0, d, e, w


def slow_pair(ev):
    i = np.argsort(abs(ev))[:2]
    l1, l2 = ev[i]
    if l1.imag < l2.imag:
        l1, l2 = l2, l1
    return l1, l2


if __name__ == '__main__':
    fast = '--fast' in sys.argv
    avals = [0.03, 0.04, 0.05, 0.06, 0.08] if not fast else [0.04, 0.06, 0.08]
    Ns = [4, 5, 6, 7, 8] if not fast else [6, 7, 8]
    M = 33
    print("Contour dynamics (M = %d nodes per patch) versus the exact r^4 block coefficients." % M)
    print("Columns: a, slow pair (normalised units), s = ((l1-l2)/2)^2, varpi = i(l1+l2)/2, max Re over all blocks")
    for N in Ns:
        data = {m: [] for m in range(1, N // 2 + 1)}
        guess = None
        for a in avals:
            S = cd.spectrum(N, a, M)
            mxre = max(max(b['ev'].real) for b in S['blocks'])
            print(f"N={N} a={a:.3f} Omega={S['Om']:.12f} (Omega-Omega0)/a^4={(S['Om']-(N-1)/2)/a**4:+.5f} "
                  f"[exact {(N-1)**2*(N-5)**2/144:.5f}] newton_res={S['res']:.1e} maxRe={mxre:.2e}")
            for m in data:
                l1, l2 = slow_pair(S['blocks'][m]['ev'])
                s = (((l1 - l2) / 2)**2).real
                vp = (1j * (l1 + l2) / 2).real
                data[m].append((a, s, vp))
                print(f"      m={m}: l1={l1.real:+.1e}{l1.imag:+.12f}i  l2={l2.real:+.1e}{l2.imag:+.12f}i  s={s:+.12e}  varpi={vp:+.6e}")
        for m, rows in data.items():
            a0, b0, d, e, w = exact_blocks(N, m)
            A = np.array([r[0] for r in rows]); s = np.array([r[1] for r in rows]); vp = np.array([r[2] for r in rows])
            eps = A**4
            ys = (s + float(a0 * b0)) / eps
            yv = vp / eps
            X = np.column_stack([np.ones_like(A), A**2, A**4])
            cs = np.linalg.lstsq(X, ys, rcond=None)[0]
            cv = np.linalg.lstsq(X, yv, rcond=None)[0]
            pred_s = -(a0 * e + b0 * d)
            print(f"  N={N} m={m}: (s + a0 b0)/a^4 -> {cs[0]:+.5f}  exact {float(pred_s):+.5f} ({pred_s});   "
                  f"varpi/a^4 -> {cv[0]:+.5f}  exact {float(w):+.5f} ({w});   (a^2 coefficients {cs[1]:+.2f}, {cv[1]:+.2f})")
        sys.stdout.flush()
