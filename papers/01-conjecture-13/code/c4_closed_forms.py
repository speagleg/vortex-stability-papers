# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# No code changes. 'c4_MT' = this paper's c4; 'c4_new' = c4/2, the value for the alternative normalisation H' = H/2.
"""Quartic coefficient c4 from the two closed forms, n = 4..25.

Paper (MT) normalisation, H_MT = -sum log(|z_i-z_j|^2/(sigma_i sigma_j)), ring at r0 = 1, kernel vector
Euclidean-unit in the chart (to leading order = unit in log-polar s, sum_k s_k^2 = 1):
  even n, m = n-2:  c4 = (n-2)(m^4+40m^2+48m+16)/(192 n (n-1))
  odd n:            c4 = (n-1)(n-3)(n^2-9n+38)/(128 n)

Conversion to the new normalisation (H = sum_{i<j} G(X_ij), G = -1/2 log|1-X|):
  H_new = H_MT/2 + const  (since |1-X_ij| = 2|lambda||z_i-z_j|^2/(sigma_i sigma_j) on S^2/H^2, and
  G_plane = -log|x-y| on the contraction), and the level set J^{-1}(mu) is the same set because
  J_new is an invertible affine function of J_MT.  The kernel coordinate eps is the log-polar amplitude
  (scale invariant, so independent of which conformal chart is used).  The eps^2 and eps^3 coefficients
  vanish, so an O(eps^2) reparametrisation eps_cart = eps_s + O(eps_s^2) does not change c4.  Hence
      c4_new = c4_MT / 2     (factor 1/2, from H only).
Other normalisations printed for reference (they are NOT the recommended one):
  * Euclidean-unit in the unit-curvature chart zeta = sqrt|b| z:     c4_MT/(2 b^2)  (n != 7)
  * Riemannian-unit kernel vector (dA_K metric, K = +-1):            c4_new/(1-q)^2 (n != 7),
    since a log-polar amplitude eps moves each vortex a geodesic distance eps*sqrt|1-X0^2|.
Run: python c4_closed_forms.py   (deterministic, exact over Q)
"""
from fractions import Fraction as Fr

table_MT = {4: Fr(1, 4), 5: Fr(9, 40), 6: Fr(23, 30), 7: Fr(9, 14), 8: Fr(95, 56), 9: Fr(19, 12), 10: Fr(49, 15),
            11: Fr(75, 22), 12: Fr(755, 132), 13: Fr(675, 104), 14: Fr(1693, 182), 15: Fr(56, 5),
            16: Fr(1141, 80), 17: Fr(609, 34), 18: Fr(3190, 153), 19: Fr(27), 20: Fr(11139, 380),
            21: Fr(2175, 56), 22: Fr(6145, 154), 23: Fr(2475, 46), 24: Fr(29183, 552), 25: Fr(7227, 100)}


def c4_MT(n):
    if n % 2 == 0:
        m = n - 2
        return Fr((n - 2) * (m**4 + 40 * m**2 + 48 * m + 16), 192 * n * (n - 1))
    return Fr((n - 1) * (n - 3) * (n * n - 9 * n + 38), 128 * n)


def q_of(n):
    return Fr(n * n // 4, n - 1) - 1


print("conversion: c4_new = c4_MT/2 (H halved; eps = log-polar unit amplitude; level set unchanged)")
print("cols: n | parity | geometry | c4_MT (closed form) | = paper table | c4_new | c4_new (15 d) | c4_new*256n (odd) or *384n(n-1) (even) | Riemannian-unit c4")
ok = True
for n in range(4, 26):
    c = c4_MT(n)
    t = (c == table_MT[n])
    ok &= t
    cn = c / 2
    q = q_of(n)
    geom = "sphere" if q < 1 else ("plane" if q == 1 else "H^2")
    if n % 2 == 0:
        m = n - 2
        chk = cn * 384 * n * (n - 1) == (n - 2) * (m**4 + 40 * m**2 + 48 * m + 16)
    else:
        chk = cn * 256 * n == (n - 1) * (n - 3) * (n * n - 9 * n + 38)
    ok &= chk
    riem = str(cn / (1 - q)**2) if q != 1 else "undefined (plane: scale-free)"
    print(f"n={n:2d} | {'even' if n % 2 == 0 else 'odd '} | {geom:6s} | {str(c):>10s} | {t} | {str(cn):>10s} | "
          f"{float(cn):.15g} | new closed form {chk} | {riem}")
print("ALL CHECKS PASS:", ok)
# extra: the odd formula at n = 3 and the even formula's positivity
print("odd formula at n=3:", Fr((3 - 1) * (3 - 3) * (9 - 27 + 38), 128 * 3), "; disc(n^2-9n+38) =", 81 - 4 * 38)
