# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# Only printed labels changed. Uses the alternative normalisation H' = H/2: prints C4_lin/2; this paper's values are twice those printed.
"""Quartic of F = H - Omega J_3 on the LINEAR slice at the G_0 ring threshold.

Normalisation H' = H/2: H' = sum_{i<j} G(X_ij), G(X) = -(1/2) ln|1 - X|, on S^2 (Theta_N < 1) or H^2 (Theta_N > 1) with X the
embedding inner product (S^2: x.y; H^2: -<x, y>_Minkowski), J = sum of embedding coordinates, ring at X_0^2 = Theta_N =
floor(N^2/4)/(N - 1) - 1.  Chart: Cartesian coordinates z of the stereographic (S^2) / Poincare (H^2)
chart rescaled by rho_0 = sqrt(|1 - X_0|/(1 + X_0)), so the ring sits at |z| = 1 (the MT chart).  Slice: z - z_0 = eta e + P xi
with dJ_a(z_0)(z - z_0) = 0 (a = 1, 2, 3), <z - z_0, t_rot> = 0, <z - z_0, e> = eta, <z - z_0, e'> = 0 (N odd), Euclidean
<.,.> in the chart; e_k = (-1)^k r_k/sqrt N (N even), e_k = sqrt(2/N) cos(l phi_k) r_k, e'_k = sqrt(2/N) sin(l phi_k) r_k,
l = (N - 1)/2 (N odd), r_k the radial unit vector at site k.  Omega = <grad H, grad J_3>/|grad J_3|^2 at z_0 (exact multiplier).
F is minimised over xi by Newton's method (exact sympy derivatives, mp.dps = 60); C_4^lin from a polynomial fit of
(F - F_0)/eta^4 at eta = j 10^-3, j = 1..5 (degree 3 in eta).
"""
from fractions import Fraction as Fr

import mpmath as mp
import sympy as sp

mp.mp.dps = 60
x1, y1, x2, y2, r0 = sp.symbols('x1 y1 x2 y2 r0', real=True)


def emb(x, y, geom):
    w2 = r0**2 * (x**2 + y**2)
    if geom == 'S2':
        return [2 * r0 * x / (1 + w2), 2 * r0 * y / (1 + w2), (1 - w2) / (1 + w2)]
    return [2 * r0 * x / (1 - w2), 2 * r0 * y / (1 - w2), (1 + w2) / (1 - w2)]


def compile_geom(geom):
    a, b = emb(x1, y1, geom), emb(x2, y2, geom)
    X = a[0] * b[0] + a[1] * b[1] + a[2] * b[2] if geom == 'S2' else a[2] * b[2] - a[0] * b[0] - a[1] * b[1]
    G = -sp.log(1 - X) / 2 if geom == 'S2' else -sp.log(X - 1) / 2
    v4 = [x1, y1, x2, y2]
    pf = sp.lambdify(v4 + [r0], G, 'mpmath')
    pg = sp.lambdify(v4 + [r0], [sp.diff(G, v) for v in v4], 'mpmath')
    ph = sp.lambdify(v4 + [r0], [[sp.diff(G, u, v) for v in v4] for u in v4], 'mpmath')
    js = []
    for J in a:
        js.append((sp.lambdify([x1, y1, r0], J, 'mpmath'),
                   sp.lambdify([x1, y1, r0], [sp.diff(J, v) for v in (x1, y1)], 'mpmath'),
                   sp.lambdify([x1, y1, r0], [[sp.diff(J, u, v) for v in (x1, y1)] for u in (x1, y1)], 'mpmath')))
    return pf, pg, ph, js


def F_all(z, n, rho, C, Om):
    pf, pg, ph, js = C
    dim = 2 * n
    val = mp.mpf(0)
    g = [mp.mpf(0)] * dim
    Hm = mp.matrix(dim, dim)
    for i in range(n):
        for j in range(i + 1, n):
            args = (z[2 * i], z[2 * i + 1], z[2 * j], z[2 * j + 1], rho)
            val += pf(*args)
            gl = pg(*args)
            hl = ph(*args)
            idx = [2 * i, 2 * i + 1, 2 * j, 2 * j + 1]
            for p in range(4):
                g[idx[p]] += gl[p]
                for q in range(4):
                    Hm[idx[p], idx[q]] += hl[p][q]
    f3, g3, h3 = js[2]
    for k in range(n):
        args = (z[2 * k], z[2 * k + 1], rho)
        val -= Om * f3(*args)
        gg = g3(*args)
        hh = h3(*args)
        for p in range(2):
            g[2 * k + p] -= Om * gg[p]
            for q in range(2):
                Hm[2 * k + p, 2 * k + q] -= Om * hh[p][q]
    return val, g, Hm


def nullspace_basis(Cm, dim):
    """orthonormal basis of {v : Cm v = 0} (Gram-Schmidt in mpmath)"""
    rows = [list(r) for r in Cm]
    Q = []
    for r in rows:  # orthonormalise the constraint normals
        v = [mp.mpf(x) for x in r]
        for qv in Q:
            c = mp.fsum(a * b for a, b in zip(v, qv))
            v = [a - c * b for a, b in zip(v, qv)]
        nv = mp.sqrt(mp.fsum(a * a for a in v))
        Q.append([a / nv for a in v])
    basis = []
    for kk in range(dim):
        v = [mp.mpf(1) if t == kk else mp.mpf(0) for t in range(dim)]
        for qv in Q + basis:
            c = mp.fsum(a * b for a, b in zip(v, qv))
            v = [a - c * b for a, b in zip(v, qv)]
        nv = mp.sqrt(mp.fsum(a * a for a in v))
        if nv > mp.mpf('1e-20'):
            basis.append([a / nv for a in v])
    return Q, basis


def c4_lin(n):
    q = Fr(n * n // 4, n - 1) - 1
    geom = 'S2' if q < 1 else 'H2'
    X0 = mp.sqrt(mp.mpf(q.numerator) / q.denominator)
    rho = mp.sqrt(abs(1 - X0) / (1 + X0))
    C = compile_geom(geom)
    phis = [2 * mp.pi * k / n for k in range(n)]
    z0 = []
    for p in phis:
        z0 += [mp.cos(p), mp.sin(p)]
    dim = 2 * n
    # J gradients and multiplier at the ring
    gJ = []
    for a in range(3):
        g = []
        for k in range(n):
            g += list(C[3][a][1](z0[2 * k], z0[2 * k + 1], rho))
        gJ.append(g)
    _, gH, _ = F_all(z0, n, rho, C, mp.mpf(0))
    Om = mp.fsum(a * b for a, b in zip(gH, gJ[2])) / mp.fsum(b * b for b in gJ[2])
    t = []
    for p in phis:
        t += [-mp.sin(p), mp.cos(p)]
    if n % 2 == 0:
        e = []
        for k, p in enumerate(phis):
            e += [(-1)**k * mp.cos(p) / mp.sqrt(n), (-1)**k * mp.sin(p) / mp.sqrt(n)]
        ep = None
    else:
        l = (n - 1) // 2
        e, ep = [], []
        for p in phis:
            c, s_ = mp.sqrt(mp.mpf(2) / n) * mp.cos(l * p), mp.sqrt(mp.mpf(2) / n) * mp.sin(l * p)
            e += [c * mp.cos(p), c * mp.sin(p)]
            ep += [s_ * mp.cos(p), s_ * mp.sin(p)]
    cons = gJ + [t] + ([ep] if ep else [])
    # e must be orthogonal to the other constraint normals for z0 + eta e to be on the slice
    orth = max(abs(mp.fsum(a * b for a, b in zip(e, c))) for c in cons)
    _, P = nullspace_basis(cons + [e], dim)
    F0 = F_all(z0, n, rho, C, Om)[0]
    xs, ys = [], []
    xi = [mp.mpf(0)] * len(P)
    for j in range(1, 6):
        eta = mp.mpf(j) / 1000
        for it in range(40):
            z = [z0[a] + eta * e[a] + mp.fsum(P[b][a] * xi[b] for b in range(len(P))) for a in range(dim)]
            val, g, Hm = F_all(z, n, rho, C, Om)
            gr = mp.matrix([mp.fsum(P[b][a] * g[a] for a in range(dim)) for b in range(len(P))])
            Hr = mp.matrix(len(P), len(P))
            for b in range(len(P)):
                Pb = P[b]
                HPb = [mp.fsum(Hm[a, c] * Pb[c] for c in range(dim)) for a in range(dim)]
                for d in range(len(P)):
                    Hr[d, b] = mp.fsum(P[d][a] * HPb[a] for a in range(dim))
            step = mp.lu_solve(Hr, -gr)
            xi = [xi[b] + step[b] for b in range(len(P))]
            if max(abs(s) for s in step) < mp.mpf(10)**-50:
                break
        z = [z0[a] + eta * e[a] + mp.fsum(P[b][a] * xi[b] for b in range(len(P))) for a in range(dim)]
        xs.append(eta)
        ys.append((F_all(z, n, rho, C, Om)[0] - F0) / eta**4)
    A = mp.matrix([[x**k for k in range(4)] for x in xs[:4]] + [[xs[4]**k for k in range(4)]])
    # least squares on 5 points, degree 3
    At = A.T
    sol = mp.lu_solve(At * A, At * mp.matrix(ys))
    return geom, q, sol[0], orth, ys


def closed_level_set(n):  # level-set c4 in the H/2 normalisation (= paper closed form / 2)
    if n % 2 == 0:
        m = n - 2
        return Fr((n - 2) * (m**4 + 40 * m**2 + 48 * m + 16), 384 * n * (n - 1))
    return Fr((n - 1) * (n - 3) * (n * n - 9 * n + 38), 256 * n)


print(" N  geom  Theta_N   C4_lin (H/2)        (F-F0)/eta^4 at eta = 1e-3 .. 5e-3           level-set c4/2 (Table 1)   e . constraints")
for n in (4, 8, 9, 13):
    geom, q, c4, orth, ys = c4_lin(n)
    cl = closed_level_set(n)
    print(f"{n:2d}  {geom}   {str(q):6s}  {mp.nstr(c4, 10):18s}  " + " ".join(mp.nstr(y, 8) for y in ys)
          + f"   {cl} = {float(cl):.6f}   {mp.nstr(orth, 2)}")
