# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# No code changes. Uses the alternative normalisation H' = H/2: it prints c4/2 and compares with closed/2.
"""Independent numerical c4 in the alternative normalisation H' = H/2.

Direct level-set minimisation (Def 5, new conventions); it starts from the symmetric guess, so it confirms the symmetric point is a full KKT point:
  f(eps) = min { H(v) - H(ring) : J(v) = J(ring), e.s = eps, e'.s = 0 (n odd), sum theta = 0 },
with v = (s, theta) log-polar coordinates of the n vortices, H = sum G(X_ij),
G = -1/2 log|1-X| on S^2 / H^2 (quadric model) and G = -1/2 log|x-y|^2 on the plane, J = sum of embedding
coordinates (S^2, H^2) or sum (x, y, |x|^2/2) (plane).  e_k = n^{-1/2} (-1)^k (even n),
e_k = (2/n)^{1/2} cos(l phi_k), e'_k = (2/n)^{1/2} sin(l phi_k), l = (n-1)/2 (odd n): unit in sum s_k^2.
The KKT system is solved by Newton's method with exact (sympy-generated) derivatives at mp.dps = 80;
c4 (and c5..c9) are fitted by exact interpolation over eps = j*2e-4, j = 1..6.
A second fit uses the chart-Cartesian amplitude eps_c = sum_k e_k (e^{s_k} - 1) (the paper's Def 5
displacement at r0 = 1): the two c4 agree, confirming that the O(eps^2) reparametrisation is irrelevant.
Expected: c4_new = c4_MT/2 = closed form /2.
Run: python c4_levelset.py   (deterministic)
"""
from fractions import Fraction as Fr
import mpmath as mp
import sympy as sp

mp.mp.dps = 80

si, sj, d, sk, ak, rho0 = sp.symbols('si sj d sk ak rho0', real=True)


def pair_expr(geom):
    if geom == 'S2':
        gi, gj = 2 * sp.atan(rho0 * sp.exp(si)), 2 * sp.atan(rho0 * sp.exp(sj))
        X = sp.sin(gi) * sp.sin(gj) * sp.cos(d) + sp.cos(gi) * sp.cos(gj)
        return -sp.log(1 - X) / 2
    if geom == 'H2':
        ri, rj = 2 * sp.atanh(rho0 * sp.exp(si)), 2 * sp.atanh(rho0 * sp.exp(sj))
        X = sp.cosh(ri) * sp.cosh(rj) - sp.sinh(ri) * sp.sinh(rj) * sp.cos(d)
        return -sp.log(X - 1) / 2
    return -sp.log(sp.exp(2 * si) + sp.exp(2 * sj) - 2 * sp.exp(si + sj) * sp.cos(d)) / 2


def one_body(geom):
    if geom == 'S2':
        g = 2 * sp.atan(rho0 * sp.exp(sk)); return [sp.sin(g) * sp.cos(ak), sp.sin(g) * sp.sin(ak), sp.cos(g)]
    if geom == 'H2':
        r = 2 * sp.atanh(rho0 * sp.exp(sk)); return [sp.sinh(r) * sp.cos(ak), sp.sinh(r) * sp.sin(ak), sp.cosh(r)]
    R = sp.exp(sk); return [R * sp.cos(ak), R * sp.sin(ak), R**2 / 2]


def compile_geom(geom):
    P = pair_expr(geom)
    pv = [si, sj, d]
    pf = sp.lambdify(pv + [rho0], P, 'mpmath')
    pg = [sp.lambdify(pv + [rho0], sp.diff(P, x), 'mpmath') for x in pv]
    ph = [[sp.lambdify(pv + [rho0], sp.diff(P, x, y), 'mpmath') for y in pv] for x in pv]
    obs = []
    for J in one_body(geom):
        ov = [sk, ak]
        obs.append((sp.lambdify(ov + [rho0], J, 'mpmath'),
                    [sp.lambdify(ov + [rho0], sp.diff(J, x), 'mpmath') for x in ov],
                    [[sp.lambdify(ov + [rho0], sp.diff(J, x, y), 'mpmath') for y in ov] for x in ov]))
    return pf, pg, ph, obs


class Problem:
    def __init__(self, geom, n, X0):
        self.geom, self.n = geom, n
        self.r0 = mp.sqrt(abs(1 - X0) / (1 + X0)) if geom != 'P' else mp.mpf(1)
        self.pf, self.pg, self.ph, self.obs = compile_geom(geom)
        self.phi = [2 * mp.pi * k / n for k in range(n)]
        if n % 2 == 0:
            self.e = [(-1)**k / mp.sqrt(n) for k in range(n)]; self.ep = None
        else:
            l = (n - 1) // 2
            self.e = [mp.sqrt(mp.mpf(2) / n) * mp.cos(l * p) for p in self.phi]
            self.ep = [mp.sqrt(mp.mpf(2) / n) * mp.sin(l * p) for p in self.phi]

    def H_grad_hess(self, v):
        n = self.n; dim = 2 * n
        Hv = mp.mpf(0); g = [mp.mpf(0)] * dim; Hm = mp.matrix(dim, dim)
        for i in range(n):
            for j in range(i + 1, n):
                args = (v[i], v[j], self.phi[i] + v[n + i] - self.phi[j] - v[n + j], self.r0)
                Hv += self.pf(*args)
                idx = [i, j, n + i, n + j]
                # chain: (si, sj, d) -> (s_i, s_j, th_i, th_j) with d = th_i - th_j
                Jac = [[1, 0, 0], [0, 1, 0], [0, 0, 1], [0, 0, -1]]
                gl = [self.pg[a](*args) for a in range(3)]
                hl = [[self.ph[a][b](*args) for b in range(3)] for a in range(3)]
                for p in range(4):
                    g[idx[p]] += sum(Jac[p][a] * gl[a] for a in range(3))
                    for q in range(4):
                        Hm[idx[p], idx[q]] += sum(Jac[p][a] * Jac[q][b] * hl[a][b] for a in range(3) for b in range(3))
        return Hv, g, Hm

    def J_all(self, v):
        n = self.n; dim = 2 * n
        out = []
        for (f, fg, fh) in self.obs:
            val = mp.mpf(0); g = [mp.mpf(0)] * dim; Hm = mp.matrix(dim, dim)
            for k in range(n):
                args = (v[k], self.phi[k] + v[n + k], self.r0)
                val += f(*args)
                idx = [k, n + k]
                for p in range(2):
                    g[idx[p]] += fg[p](*args)
                    for q in range(2):
                        Hm[idx[p], idx[q]] += fh[p][q](*args)
            out.append((val, g, Hm))
        return out

    def solve(self, eps, v0, J0, Om):
        n = self.n; dim = 2 * n
        lin = [self.e + [0] * n]
        rhs_lin = [eps]
        if self.ep is not None:
            lin.append(self.ep + [0] * n); rhs_lin.append(0)
        lin.append([0] * n + [1] * n); rhs_lin.append(0)
        nc = 3 + len(lin)
        v = list(v0); mu = [mp.mpf(0), mp.mpf(0), Om]   # start from the ring's angular velocity
        for it in range(60):
            Hv, gH, HH = self.H_grad_hess(v)
            Js = self.J_all(v)
            # Lagrangian L = H - sum mu_c (J_c - J0_c) - sum nu (lin)
            L = HH.copy()
            for c in range(3):
                L -= mu[c] * Js[c][2]
            K = mp.matrix(dim + nc, dim + nc)
            R = mp.matrix(dim + nc, 1)
            Cm = [Js[c][1] for c in range(3)] + lin
            for a in range(dim):
                for b in range(dim):
                    K[a, b] = L[a, b]
                for c in range(nc):
                    K[a, dim + c] = -Cm[c][a]; K[dim + c, a] = Cm[c][a]
            # residuals: stationarity uses multipliers for linear constraints solved jointly
            for c in range(3):
                R[dim + c] = -(Js[c][0] - J0[c])
            for c in range(len(lin)):
                R[dim + 3 + c] = -(mp.fsum(lin[c][a] * v[a] for a in range(dim)) - rhs_lin[c])
            # stationarity residual with current mu (linear-constraint multipliers re-solved each step)
            for a in range(dim):
                R[a] = -(gH[a] - mp.fsum(mu[c] * Js[c][1][a] for c in range(3)))
            sol = mp.lu_solve(K, R)
            v = [v[a] + sol[a] for a in range(dim)]
            mu = [mu[c] + sol[dim + c] for c in range(3)]
            step = max(abs(sol[a]) for a in range(dim))
            if step < mp.mpf(10)**(-70):
                break
        Hv, _, _ = self.H_grad_hess(v)
        return Hv, v, step


def fit(xs, ys, kmin=4, kmax=9):
    m = len(xs)
    A = mp.matrix(m, kmax - kmin + 1)
    for i, x in enumerate(xs):
        for k in range(kmin, kmax + 1):
            A[i, k - kmin] = x**k
    return mp.lu_solve(A, mp.matrix(ys))


def closed_new(n):
    if n % 2 == 0:
        m = n - 2
        return Fr((n - 2) * (m**4 + 40 * m**2 + 48 * m + 16), 384 * n * (n - 1))
    return Fr((n - 1) * (n - 3) * (n * n - 9 * n + 38), 256 * n)


cache = {}
for n in range(4, 12):
    q = Fr(n * n // 4, n - 1) - 1
    geom = 'S2' if q < 1 else ('P' if q == 1 else 'H2')
    X0 = mp.sqrt(mp.mpf(q.numerator) / q.denominator)
    P = Problem(geom, n, X0)
    z = [mp.mpf(0)] * (2 * n)
    H0 = P.H_grad_hess(z)[0]
    Jz = P.J_all(z)
    J0 = [J[0] for J in Jz]
    Om = P.H_grad_hess(z)[1][0] / Jz[2][1][0]
    xs, xc, ys = [], [], []
    v = z
    for j in range(1, 7):
        eps = mp.mpf(j) * mp.mpf('2e-4')
        guess = [eps * P.e[k] for k in range(n)] + [mp.mpf(0)] * n
        Hv, v, step = P.solve(eps, guess, J0, Om)
        xs.append(eps); ys.append(Hv - H0)
        xc.append(mp.fsum(P.e[k] * (mp.e**v[k] - 1) for k in range(n)))
    c = fit(xs, ys)
    cc = fit(xc, ys)
    ex = closed_new(n)
    exm = mp.mpf(ex.numerator) / ex.denominator
    print(f"n={n:2d} {geom:2s} X0^2={str(q):5s}: c4(log-polar)={mp.nstr(c[0], 25)}  c4(chart-Cartesian)={mp.nstr(cc[0], 25)}  "
          f"closed/2={ex} ={mp.nstr(exm, 25)}  |diff|={mp.nstr(abs(c[0]-exm), 3)}  c4_num/c4_MT={mp.nstr(c[0]/(2*exm), 20)}"
          f"  c5={mp.nstr(c[1], 8)}  last Newton step={mp.nstr(step, 3)}")
