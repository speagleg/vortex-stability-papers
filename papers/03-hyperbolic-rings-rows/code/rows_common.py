# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# Changes: none
"""Shared helpers for the hypercycle-row scripts.

Conventions: strip z = u + i phi, g = (du^2 + dphi^2)/sin^2 phi,
X = (cosh(u-u') - cos phi cos phi')/(sin phi sin phi'), H = sum_{i<j} W(X_ij), Gamma = 1, mobility sin^2 phi:
  u' = sin^2 phi H_phi,   phi' = -sin^2 phi H_u.
Row: u_k = k ell_u, phi_k = alpha, kappa = cos alpha, s = sin alpha, c_j = cosh(j ell_u), D_j = c_j - cos 2 alpha.
Bloch ansatz (du_k, dphi_k) = (U, P) e^{i q k}; symbol entries A_xy(q) = sum_k d(x'_0)/d(y_k) e^{i q k}.
Jacobian form on (du, dphi): [[i varpi, B], [C, i varpi]].  Pair functions (j >= 1):
  B(q) = 2 sum_j [a_j + b_j cos(q j)],  C(q) = 2 sum_j d_j (1 - cos(q j)),  F(q) = B(q)/2,
  a_j = s^2 W_{phi0 phi0} + 2 s kappa W_{phi0},  b_j = s^2 W_{phi0 phij},  d_j = -s^2 W_{u0 u0}
(all at the equilibrium, pair (0, j)).  Kernels: W_nu = Q_nu(X); W_0 = G_1 = (1/2) log((X+1)/(X-1)) (tanh model).
"""
import mpmath as mp
import sympy as sp

# ---------------------------------------------------------------- symbolic pair functions (derived here, not quoted)
_u, _p0, _pj, _al = sp.symbols('u phi0 phij alpha', real=True)
_c, _k = sp.symbols('c kappa', real=True)
_Xexpr = (sp.cosh(_u) - sp.cos(_p0) * sp.cos(_pj)) / (sp.sin(_p0) * sp.sin(_pj))


def _to_ck(e):
    """Rewrite an expression at phi0 = phij = alpha in c = cosh u and kappa = cos alpha."""
    e = e.subs({_p0: _al, _pj: _al})
    e = e.subs(sp.sinh(_u)**2, _c**2 - 1).subs(sp.cosh(_u), _c)
    e = sp.expand_trig(e)
    e = e.subs(sp.cos(_al), _k).subs(sp.sin(_al), sp.sqrt(1 - _k**2))
    e = sp.factor(sp.simplify(e))
    e = sp.expand_trig(e).subs(sp.cos(_al), _k).subs(sp.sin(_al), sp.sqrt(1 - _k**2))
    return sp.factor(sp.simplify(e))


def tanh_pair_symbolic():
    """a, b, d of the G_1 row as rational functions of (c, kappa), derived by sympy from X and u' = s^2 H_phi etc."""
    W = sp.log((_Xexpr + 1) / (_Xexpr - 1)) / 2
    s = sp.sin(_p0)
    udot = s**2 * sp.diff(W, _p0)
    pdot = -s**2 * sp.diff(W, _u)
    a = sp.diff(udot, _p0)
    b = sp.diff(udot, _pj)
    d = sp.diff(pdot, _u)          # d phi'_0 / d u_0 (pair j); sinh^2 u appears and is replaced by c^2 - 1
    out = {}
    for nm, e in (('a', a), ('b', b), ('d', d)):
        e = e.subs({_p0: _al, _pj: _al})
        e = sp.expand(sp.simplify(e))
        e = e.subs(sp.sinh(_u)**2, _c**2 - 1)
        out[nm] = _to_ck(e)
    return out, _c, _k


def X_derivatives_symbolic():
    """X and its partials at phi0 = phij = alpha as functions of (c, kappa) [X_u carries sinh u = sqrt(c^2-1)]."""
    sh = sp.Symbol('sh', positive=True)
    res = {}
    for nm, e in (('X', _Xexpr), ('Xp0', sp.diff(_Xexpr, _p0)), ('Xp0p0', sp.diff(_Xexpr, _p0, 2)),
                  ('Xp0pj', sp.diff(_Xexpr, _p0, _pj)), ('Xu', sp.diff(_Xexpr, _u)), ('Xuu', sp.diff(_Xexpr, _u, 2))):
        e = e.subs({_p0: _al, _pj: _al}).subs(sp.sinh(_u), sh).subs(sp.cosh(_u), _c)
        e = e.subs(sp.cos(_al), _k).subs(sp.sin(_al), sp.sqrt(1 - _k**2))
        res[nm] = sp.simplify(e)
    return res, _c, _k, sh


_XD = None


def generic_pair(W1, W2, c, kappa):
    """a, b, d for a kernel W(X) given W1 = W'(X), W2 = W''(X) at X(c) (mpmath numbers)."""
    global _XD
    if _XD is None:
        res, c_, k_, sh_ = X_derivatives_symbolic()
        _XD = {nm: sp.lambdify((c_, k_, sh_), e, 'mpmath') for nm, e in res.items()}
    sh = mp.sqrt(c * c - 1)
    s = mp.sqrt(1 - kappa**2)
    D = {nm: f(c, kappa, sh) for nm, f in _XD.items()}
    a = s**2 * (W2 * D['Xp0']**2 + W1 * D['Xp0p0']) + 2 * s * kappa * W1 * D['Xp0']
    b = s**2 * (W2 * D['Xp0'] * D['Xp0'] + W1 * D['Xp0pj'])     # X_phij = X_phi0 at the symmetric point
    d = -s**2 * (W2 * D['Xu']**2 + W1 * D['Xuu'])
    return a, b, d


def X_of_c(c, kappa):
    return (c - kappa**2) / (1 - kappa**2)


# ---------------------------------------------------------------- kernels Q_nu (closed forms for nu = 0, 1, 2)
def Q_derivs(nu, X):
    """(Q_nu, Q_nu', Q_nu'') at X > 1, from Q_0 = (1/2) log((X+1)/(X-1)), Q_1 = X Q_0 - 1, Q_2 = P_2 Q_0 - 3X/2.
    The closed forms cancel ~ (2 nu + 2) log10 X digits at large X; the working precision is raised accordingly."""
    extra = int((2 * nu + 4) * mp.log10(abs(X) + 2)) + 15
    with mp.extradps(extra):
        X = +X
        return tuple(+v for v in _Q_derivs(nu, X))


def _Q_derivs(nu, X):
    L = mp.log((X + 1) / (X - 1)) / 2
    L1 = -1 / (X * X - 1)
    L2 = 2 * X / (X * X - 1)**2
    if nu == 0:
        return L, L1, L2
    if nu == 1:
        return X * L - 1, L + X * L1, 2 * L1 + X * L2
    if nu == 2:
        P, P1, P2 = (3 * X * X - 1) / 2, 3 * X, mp.mpf(3)
        return P * L - 3 * X / 2, P1 * L + P * L1 - mp.mpf(3) / 2, P2 * L + 2 * P1 * L1 + P * L2
    raise ValueError(nu)


def Q_legenq(nu, X):
    """Independent value of Q_nu(X), X > 1, from mpmath's Legendre function of the second kind (type 3)."""
    return mp.legenq(nu, 0, X, type=3).real


# ---------------------------------------------------------------- lattice sums
def jmax_for(lu, gamma=1, extra=30):
    return int(mp.ceil((mp.mp.dps * mp.log(10) + extra) / (gamma * lu))) + 5


def F_lattice(nu, alpha, lu, q=mp.pi, J=None):
    """F_nu(q) = sum_{j>=1} [a_j + b_j cos(q j)] by direct lattice summation of the Legendre-Q pair functions."""
    kappa = mp.cos(alpha)
    J = J or jmax_for(lu, nu + 1)
    tot = mp.mpf(0)
    for j in range(1, J + 1):
        c = mp.cosh(j * lu)
        _, W1, W2 = Q_derivs(nu, X_of_c(c, kappa))
        a, b, _d = generic_pair(W1, W2, c, kappa)
        tot += a + b * mp.cos(q * j)
    return tot


# ---------------------------------------------------------------- Poschl-Teller modes
def gegen_table(lam, x, kmax):
    """C^{(lam)}_k(x), k = 0..kmax, by the three-term recurrence (exact polynomials in x)."""
    C = [mp.mpf(1), 2 * lam * x]
    for k in range(2, kmax + 1):
        C.append((2 * x * (k + lam - 1) * C[k - 1] - (k + 2 * lam - 2) * C[k - 2]) / k)
    return C[:kmax + 1]


def pt_norm(nu, n):
    """N_n = int_0^pi psi_n^2 dphi = pi 2^{1-2m} Gamma(n+m)/((n-m)! n Gamma(m)^2), m = nu+1."""
    m = nu + 1
    return mp.pi * mp.mpf(2)**(1 - 2 * m) * mp.gamma(n + m) / (mp.factorial(n - m) * n * mp.gamma(m)**2)


def pt_modes(nu, phi, nmax):
    """[(n, psi_n(phi), psi_n'(phi))] for n = m..nmax, psi_n = sin^m phi C^{(m)}_{n-m}(cos phi)."""
    m = nu + 1
    s, c = mp.sin(phi), mp.cos(phi)
    C = gegen_table(m, c, nmax - m)
    Cp = [mp.mpf(0)] + [2 * m * v for v in gegen_table(m + 1, c, max(nmax - m - 1, 0))]
    out = []
    for n in range(m, nmax + 1):
        k = n - m
        psi = s**m * C[k]
        dpsi = m * s**(m - 1) * c * C[k] - s**(m + 1) * Cp[k]
        out.append((n, psi, dpsi))
    return out


def nmax_for(lu, extra=80):
    return int(mp.ceil((mp.mp.dps * mp.log(10) + extra) / lu)) + 10


def F_modes(nu, alpha, lu, q=mp.pi, nmax=None):
    """F_nu(q) from the Poschl-Teller expansion W_nu = 2 pi sum_n e^{-n|u|} psi_n psi_n(phi0)/(2 n N_n):
    a = sum w_n [2 s kappa psi psi' + (Lambda - n^2 s^2) psi^2], b = s^2 sum w_n psi'^2, summed over the lattice."""
    s, kappa = mp.sin(alpha), mp.cos(alpha)
    Lam = nu * (nu + 1)
    nmax = nmax or nmax_for(lu)
    tot = mp.mpf(0)
    cq = mp.cos(q)
    for n, psi, dpsi in pt_modes(nu, alpha, nmax):
        r = mp.exp(-n * lu)
        pref = mp.pi / (n * pt_norm(nu, n))       # 2 pi/(2 n N_n)
        A = 2 * s * kappa * psi * dpsi + (Lam - n * n * s * s) * psi * psi
        Bc = s * s * dpsi * dpsi
        sum0 = r / (1 - r)                          # sum_{j>=1} r^j
        sumq = (r * cq - r * r) / (1 - 2 * r * cq + r * r)   # sum_{j>=1} cos(qj) r^j
        tot += pref * (A * sum0 + Bc * sumq)
    return tot


# ---------------------------------------------------------------- tanh (nu = 0) series forms
def F_lambert(alpha, lu, N=None):
    """F(pi) = sum_n [(sin2a sin2na - 2n s^2 sin^2 na) r_n/(1-r_n) - 2n s^2 cos^2 na r_n/(1+r_n)], r_n = e^{-n lu}."""
    s2 = mp.sin(alpha)**2
    s2a = mp.sin(2 * alpha)
    N = N or nmax_for(lu, 20)
    tot = mp.mpf(0)
    for n in range(1, N + 1):
        r = mp.exp(-n * lu)
        tot += (s2a * mp.sin(2 * n * alpha) - 2 * n * s2 * mp.sin(n * alpha)**2) * r / (1 - r) \
            - 2 * n * s2 * mp.cos(n * alpha)**2 * r / (1 + r)
    return tot


def F0(alpha, lu):
    """Elementary modular term (derived in rows_fpi.py):
    F0 = (pi sin2a/(2 lu)) coth(2 pi a/lu) - a sin2a/lu - cos2a/4 - (pi^2 s^2/(4 lu^2)) coth^2(pi a/lu)."""
    s2 = mp.sin(alpha)**2
    e = mp.pi * alpha / lu
    return (mp.pi * mp.sin(2 * alpha) / (2 * lu)) * mp.coth(2 * e) - alpha * mp.sin(2 * alpha) / lu \
        - mp.cos(2 * alpha) / 4 - (mp.pi**2 * s2 / (4 * lu**2)) * mp.coth(e)**2


def F_dual_corrections(alpha, lu, N=None):
    """(R1, R2): F(pi) = F0 - R1 - R2 with Q1 = e^{-4 pi^2/lu}, Q2 = e^{-2 pi^2/lu},
    R1 = (2pi/lu) sum Q1^n/(1-Q1^n)[sin2a sinh(4 pi n a/lu) - 4 pi n s^2/lu],
    R2 = (2 pi^2 s^2/lu^2) sum n Q2^n/(1-Q2^n)[1 + cosh(2 pi n a/lu)]."""
    s2 = mp.sin(alpha)**2
    Q1 = mp.exp(-4 * mp.pi**2 / lu)
    Q2 = mp.exp(-2 * mp.pi**2 / lu)
    R1 = R2 = mp.mpf(0)
    n = 1
    while True:
        t1 = Q1**n / (1 - Q1**n) * (mp.sin(2 * alpha) * mp.sinh(4 * mp.pi * n * alpha / lu) - 4 * mp.pi * n * s2 / lu)
        t2 = n * Q2**n / (1 - Q2**n) * (1 + mp.cosh(2 * mp.pi * n * alpha / lu))
        R1 += t1
        R2 += t2
        if (abs(t1) + abs(t2)) < mp.mpf(10)**(-mp.mp.dps - 10) * (1 + abs(R1) + abs(R2)) and n > 3:
            break
        n += 1
        if N and n > N:
            break
    return (2 * mp.pi / lu) * R1, (2 * mp.pi**2 * s2 / lu**2) * R2


def F_dual(alpha, lu):
    R1, R2 = F_dual_corrections(alpha, lu)
    return F0(alpha, lu) - R1 - R2


def fmt(x, n=15):
    return mp.nstr(x, n)
