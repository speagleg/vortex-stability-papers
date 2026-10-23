"""Fourier (Bloch) blocks of the effective ring Hamiltonian, reduced to the lattice sums T_a(n).

Written for this paper.  Model (normalised units, circulation Gamma = 1 per patch), stereographic / planar
coordinate z, ring |z| = rho, log-polar coordinates z_k = rho zeta^k exp(s_k + i t_k):

  F = H + eps * Q - Omega * J,     eps = r^4  (r = patch radius),
  H = sum_{k<l} W(z_k, z_l),   W(z, w) = -log|z - w| + (1/2) log(1 + K|z|^2) + (1/2) log(1 + K|w|^2),
  Q = sum_k e^{-4 Phi(z_k)} |G_k|^2,   G_k = (1/2) sum_{l != k} ( 1/(z_k - z_l) - K conj(z_k)/(1 + K|z_k|^2) )^2,
  e^{2 Phi} = 4/(1 + K|z|^2)^2 (K = +-1),  Phi = 0 (K = 0, the plane),
  J = |z|^2/2 (plane) or (1 - K|z|^2)/(1 + K|z|^2) (K = +-1; any function of |z| works: Omega is solved for).
K = 0: plane, K = 1: sphere S^2 with the Green function G, K = -1: H^2 with G (the "G model" with background).
For K = 0, Q = (1/4) sum_k |M_k|^2 with M_k = sum_l (z_k - z_l)^{-2}: the plane effective Hamiltonian.

Method (paper, Section 3): every term of F is a sum over k of a local term at k; translation invariance of
the ring lets us evaluate the complexified Bloch form on the local term at k = 0.  Each sum over the other
vortices j becomes, after Taylor expansion to second order, a polynomial in p_j = 1/(1 - zeta^j),
zeta^{+-j}, zeta^{+-mj}; we replace each monomial p^a zeta^{n j} zeta^{e m j} by the lattice sum T_a(n + e m).
The block entries are then exact rationals (given N, m) or polynomials in (N, m) (symbolic, middle range of m).
"""
import sympy as sp
from fractions import Fraction
from functools import lru_cache
import tsums

h, tau, sig = sp.symbols('h tau sigma')
Pj, Wj, Xp, Xm = sp.symbols('p w Xp Xm')        # p_j, zeta^j, zeta^{mj}, zeta^{-mj}
rho, K = sp.symbols('rho K')
I = sp.I


def bloch_vars(alpha, beta):
    """complexified Bloch substitution: returns (u0, ut0, uj, utj) as expressions in tau, sigma, Xp, Xm.
    alpha: type ('s' or 't') of the conjugated vector (coefficient tau), beta: of the plain vector (sigma)."""
    def st(phase_conj, phase):
        s = (tau * phase_conj if alpha == 's' else 0) + (sig * phase if beta == 's' else 0)
        t = (tau * phase_conj if alpha == 't' else 0) + (sig * phase if beta == 't' else 0)
        return s + I * t, s - I * t
    u0, ut0 = st(1, 1)
    uj, utj = st(Xm, Xp)
    return u0, ut0, uj, utj


def series2(expr):
    """Taylor polynomial of expr in h to order 2 (expr analytic at h = 0)."""
    return sp.expand(sp.series(expr, h, 0, 3).removeO())


def tsum_symbol(a, n, e):
    return sp.Symbol(f'T_{a}_{n}_{e}')


def sum_over_j(summand):
    """summand: polynomial in tau, sigma (already truncated) with coefficients polynomial in p, w, 1/w, Xp, Xm.
    Return the same polynomial with sum_j applied: monomials p^a w^n Xp^e1 Xm^e2 -> T_a(n + (e1-e2) m)."""
    summand = sp.expand(summand)
    out = 0
    poly = sp.Poly(summand, tau, sig)
    for (dt, ds), coeff in poly.terms():
        coeff = sp.expand(coeff)
        acc = 0
        for term in sp.Add.make_args(coeff):
            c, mon = term.as_coeff_Mul()
            powers = mon.as_powers_dict() if mon != 1 else {}
            a = n = e = 0
            rest = c
            for base, ex in powers.items():
                if base == Pj:
                    a += int(ex)
                elif base == Wj:
                    n += int(ex)
                elif base == Xp:
                    e += int(ex)
                elif base == Xm:
                    e -= int(ex)
                else:
                    rest = rest * base**ex
            acc += rest * tsum_symbol(a, n, e)
        out += acc * tau**dt * sig**ds
    return sp.expand(out)


def trunc(expr):
    """keep only monomials tau^a sigma^b with a <= 1, b <= 1 (we need the tau*sigma coefficient)."""
    expr = sp.expand(expr)
    poly = sp.Poly(expr, tau, sig)
    return sp.expand(sum(c * tau**a * sig**b for (a, b), c in poly.terms() if a <= 1 and b <= 1))


@lru_cache(maxsize=None)
def local_terms(alpha, beta, model):
    """Bilinear Bloch form (coefficient of tau*sigma) of the local terms of H, Q, J, in terms of T symbols."""
    u0, ut0, uj, utj = bloch_vars(alpha, beta)
    Kv = {'plane': 0, 'S2': 1, 'H2': -1}[model]
    r = 1 if model == 'plane' else rho
    E = lambda x: sp.exp(h * x)
    pbar = 1 - Pj
    d = (E(u0) - 1) - Wj * (E(uj) - 1)
    dt = (E(ut0) - 1) - (E(utj) - 1) / Wj
    z0 = r * E(u0); zt0 = r * E(ut0)
    # H local: -(1/4) sum_j [log(1 + p d) + log(1 + pbar dt)] + (N-1)/2 log(1 + K z0 zt0)
    Hj = -sp.Rational(1, 4) * (sp.log(1 + Pj * d) + sp.log(1 + pbar * dt))
    Hj = trunc(series2(Hj).subs(h, 1))
    H_sum = sum_over_j(Hj)
    Nn = sp.Symbol('N')
    Hsite = (Nn - 1) / 2 * sp.log(1 + Kv * z0 * zt0)
    Hsite = trunc(series2(Hsite).subs(h, 1))
    Hloc = sp.expand(H_sum + Hsite)
    # J local
    if Kv == 0:
        Jloc = z0 * zt0 / 2
    else:
        Jloc = (1 - Kv * z0 * zt0) / (1 + Kv * z0 * zt0)
    Jloc = trunc(series2(Jloc).subs(h, 1))
    # Q local
    S1 = sum_over_j(trunc(series2(Pj / (1 + Pj * d) / r).subs(h, 1)))
    S2 = sum_over_j(trunc(series2(Pj**2 / (1 + Pj * d)**2 / r**2).subs(h, 1)))
    S1t = sum_over_j(trunc(series2(pbar / (1 + pbar * dt) / r).subs(h, 1)))
    S2t = sum_over_j(trunc(series2(pbar**2 / (1 + pbar * dt)**2 / r**2).subs(h, 1)))
    # single-site pieces are exact functions of tau, sigma; expand them in h then set h = 1
    S0 = trunc(series2(Kv * zt0 / (1 + Kv * z0 * zt0)).subs(h, 1))
    S0t = trunc(series2(Kv * z0 / (1 + Kv * z0 * zt0)).subs(h, 1))
    conf = trunc(series2(((1 + Kv * z0 * zt0) / 2)**4).subs(h, 1)) if Kv != 0 else 1
    G = trunc(sp.Rational(1, 2) * (S2 - 2 * S0 * S1 + (Nn - 1) * S0**2))
    Gt = trunc(sp.Rational(1, 2) * (S2t - 2 * S0t * S1t + (Nn - 1) * S0t**2))
    Qloc = trunc(conf * G * Gt)
    res = {}
    for name, ex in (('H', Hloc), ('Q', Qloc), ('J', Jloc)):
        res[name] = (sp.Poly(ex, tau, sig).coeff_monomial(tau * sig), sp.Poly(ex, tau, sig).coeff_monomial(sig))
    return res


def evaluate(expr, N, m, extra=None):
    """Replace T symbols by exact values for integer N, m (and N symbol)."""
    subs = {sp.Symbol('N'): N}
    for s in expr.free_symbols:
        if s.name.startswith('T_'):
            _, a, n, e = s.name.split('_')
            subs[s] = sp.Rational(*tsums.T_exact(int(a), int(n) + int(e) * m, N).as_integer_ratio())
    if extra:
        subs.update(extra)
    return sp.cancel(sp.expand(expr.subs(subs)))


def evaluate_symbolic(expr, m_sym, Nsym):
    """Replace T symbols by the polynomial closed forms, assuming the arguments n + e m lie in [1, N]
    after adding N when e < 0 or n + e m <= 0 (valid for m in a middle range, checked by the caller)."""
    subs = {}
    for s in expr.free_symbols:
        if s.name.startswith('T_'):
            _, a, n, e = s.name.split('_')
            a, n, e = int(a), int(n), int(e)
            arg = n + e * m_sym
            if e < 0 or (e == 0 and n <= 0):
                arg = arg + Nsym
            if a == 0:
                # T_0 at an argument in [1, N]: -1 unless the argument is N (e = 0 only)
                if e == 0:
                    subs[s] = Nsym - 1 if (n % 1 == 0 and (n == 0)) else -1
                else:
                    subs[s] = -1          # 1 <= arg <= N-1 in the middle range
            else:
                subs[s] = tsums.P(a).subs({tsums.Nsym: Nsym, tsums.nsym: arg})
    return sp.expand(expr.subs(subs))


def ranges_needed(expr):
    """list of (n, e) shifts appearing, to determine the valid range of m for the symbolic formula."""
    out = set()
    for s in expr.free_symbols:
        if s.name.startswith('T_'):
            _, a, n, e = s.name.split('_')
            out.add((int(a), int(n), int(e)))
    return sorted(out)


def block(model, N, m, rho_val=None, eps_order=True):
    """Exact block (a_perp, a_par, varpi) at eps^0 and eps^1 for integer N, m.  Returns dict."""
    extra = {} if rho_val is None else {rho: rho_val}
    loc = {ab: local_terms(ab[0], ab[1], model) for ab in ('ss', 'tt', 'st')}
    # Omega0, Omega1 from the first-order condition with the uniform radial perturbation (m = 0, beta = s):
    l0 = local_terms('s', 's', model)
    dH = evaluate(l0['H'][1], N, 0, extra)
    dQ = evaluate(l0['Q'][1], N, 0, extra)
    dJ = evaluate(l0['J'][1], N, 0, extra)
    Om0 = sp.cancel(dH / dJ); Om1 = sp.cancel(dQ / dJ)
    out = {'Omega0': Om0, 'Omega1': Om1}
    for ab in ('ss', 'tt', 'st'):
        H2 = evaluate(loc[ab]['H'][0], N, m, extra)
        Q2 = evaluate(loc[ab]['Q'][0], N, m, extra)
        J2 = evaluate(loc[ab]['J'][0], N, m, extra)
        out[ab] = (sp.cancel(sp.expand(H2 - Om0 * J2)), sp.cancel(sp.expand(Q2 - Om1 * J2)))
    # B_st = i varpi
    out['varpi'] = tuple(sp.cancel(sp.expand(x / I)) for x in out['st'])
    return out


if __name__ == '__main__':
    import sys
    for N in range(2, 13):
        b = {m: block('plane', N, m) for m in range(N // 2 + 1)}
        print(f"N={N} Omega=({b[0]['Omega0']}) + ({b[0]['Omega1']}) eps")
        for m in range(N // 2 + 1):
            x = b[m]
            print(f"   m={m}: pv ({x['ss'][0]}, {x['tt'][0]}, {x['varpi'][0]})  eps ({x['ss'][1]}, {x['tt'][1]}, {x['varpi'][1]})")
        sys.stdout.flush()


# ---------------------------------------------------------------------------------------------
# Faster variant for given integer N, m: the lattice sums are replaced by their exact values right after
# the sum over j, so that the products (|G|^2, conformal factor) are taken between small polynomials.
# Used for the sphere and the hyperbolic plane (curved.py); it reproduces block() on the plane.

@lru_cache(maxsize=None)
def _summands(alpha, beta, model):
    u0, ut0, uj, utj = bloch_vars(alpha, beta)
    Kv = {'plane': 0, 'S2': 1, 'H2': -1}[model]
    r = 1 if model == 'plane' else rho
    E = lambda x: sp.exp(h * x)
    pbar = 1 - Pj
    d = (E(u0) - 1) - Wj * (E(uj) - 1)
    dt = (E(ut0) - 1) - (E(utj) - 1) / Wj
    z0 = r * E(u0); zt0 = r * E(ut0)
    T2 = lambda ex: trunc(series2(ex).subs(h, 1))
    out = dict(
        Hj=T2(-sp.Rational(1, 4) * (sp.log(1 + Pj * d) + sp.log(1 + pbar * dt))),
        Hsite=T2(sp.log(1 + Kv * z0 * zt0) / 2),          # times (N - 1)
        J=T2(z0 * zt0 / 2 if Kv == 0 else (1 - Kv * z0 * zt0) / (1 + Kv * z0 * zt0)),
        S1=T2(Pj / (1 + Pj * d) / r), S2=T2(Pj**2 / (1 + Pj * d)**2 / r**2),
        S1t=T2(pbar / (1 + pbar * dt) / r), S2t=T2(pbar**2 / (1 + pbar * dt)**2 / r**2),
        S0=T2(Kv * zt0 / (1 + Kv * z0 * zt0)), S0t=T2(Kv * z0 / (1 + Kv * z0 * zt0)),
        conf=T2(((1 + Kv * z0 * zt0) / 2)**4) if Kv != 0 else sp.Integer(1))
    return out


def _sum_numeric(summand, N, m):
    ex = sum_over_j(summand)
    subs = {}
    for s in ex.free_symbols:
        if s.name.startswith('T_'):
            _, a, n, e = s.name.split('_')
            v = tsums.T_exact(int(a), int(n) + int(e) * m, N)
            subs[s] = sp.Rational(v.numerator, v.denominator)
    return sp.expand(ex.subs(subs))


def _tr(ex):
    return trunc(sp.expand(ex))


def local_numeric(alpha, beta, model, N, m):
    S = _summands(alpha, beta, model)
    Hloc = _sum_numeric(S['Hj'], N, m) + (N - 1) * S['Hsite']
    S1 = _sum_numeric(S['S1'], N, m); S2 = _sum_numeric(S['S2'], N, m)
    S1t = _sum_numeric(S['S1t'], N, m); S2t = _sum_numeric(S['S2t'], N, m)
    G = _tr(sp.Rational(1, 2) * (S2 - 2 * _tr(S['S0'] * S1) + (N - 1) * _tr(S['S0']**2)))
    Gt = _tr(sp.Rational(1, 2) * (S2t - 2 * _tr(S['S0t'] * S1t) + (N - 1) * _tr(S['S0t']**2)))
    Qloc = _tr(S['conf'] * _tr(G * Gt))
    res = {}
    for name, ex in (('H', Hloc), ('Q', Qloc), ('J', S['J'])):
        P_ = sp.Poly(sp.expand(ex), tau, sig)
        res[name] = (P_.coeff_monomial(tau * sig), P_.coeff_monomial(sig))
    return res


def block_numeric(model, N, m):
    """Same output as block(), computed with the lattice sums substituted early (N, m integers)."""
    l0 = local_numeric('s', 's', model, N, 0)
    Om0 = sp.cancel(l0['H'][1] / l0['J'][1]); Om1 = sp.cancel(l0['Q'][1] / l0['J'][1])
    out = {'Omega0': Om0, 'Omega1': Om1}
    for ab in ('ss', 'tt', 'st'):
        loc = local_numeric(ab[0], ab[1], model, N, m)
        out[ab] = (sp.cancel(sp.expand(loc['H'][0] - Om0 * loc['J'][0])),
                   sp.cancel(sp.expand(loc['Q'][0] - Om1 * loc['J'][0])))
    out['varpi'] = tuple(sp.cancel(sp.expand(x / I)) for x in out['st'])
    return out


# ---------------------------------------------------------------------------------------------
# Symbolic N and m: the lattice sums are replaced by their closed forms P_a(N, n) (tsums.py), assuming the
# arguments n + e m (e in {-1, 0, 1}) lie in the range where the closed form applies.  The shifts that occur
# are recorded so that the caller can state the range of m for which the result is valid.

Nsym_b, msym_b = sp.symbols('N m')
_shifts = set()


def T_symbolic(a, n, e):
    _shifts.add((a, n, e))
    N, m = Nsym_b, msym_b
    if e == 0:
        r = n % 10**6  # n is a small integer
        if n == 0:
            return N - 1 if a == 0 else tsums.P(a).subs({tsums.Nsym: N, tsums.nsym: N})
        arg = n if n > 0 else N + n
        return -1 if a == 0 else tsums.P(a).subs({tsums.Nsym: N, tsums.nsym: arg})
    arg = n + m if e == 1 else N + n - m
    if a == 0:
        return sp.Integer(-1)
    return tsums.P(a).subs({tsums.Nsym: N, tsums.nsym: arg})


def _sum_symbolic(summand, m_is_zero=False):
    """m_is_zero: the Bloch mode m = 0 (used for Omega); then T_a(n + e m) = T_a(n) exactly."""
    ex = sum_over_j(summand)
    subs = {}
    for s in ex.free_symbols:
        if s.name.startswith('T_'):
            _, a, n, e = s.name.split('_')
            subs[s] = T_symbolic(int(a), int(n), 0 if m_is_zero else int(e))
    return sp.expand(ex.subs(subs))


def local_symbolic(alpha, beta, model, msub=None):
    """as local_numeric, with N and m symbolic (msub: substitute m by an expression, e.g. N/2)."""
    S = _summands(alpha, beta, model)
    N = Nsym_b
    f = (lambda ex: sp.expand(ex.subs(msym_b, msub))) if msub is not None else (lambda ex: ex)
    z = (msub == 0)
    Hloc = f(_sum_symbolic(S['Hj'], z)) + (N - 1) * S['Hsite']
    S1 = f(_sum_symbolic(S['S1'], z)); S2 = f(_sum_symbolic(S['S2'], z))
    S1t = f(_sum_symbolic(S['S1t'], z)); S2t = f(_sum_symbolic(S['S2t'], z))
    G = _tr(sp.Rational(1, 2) * (S2 - 2 * _tr(S['S0'] * S1) + (N - 1) * _tr(S['S0']**2)))
    Gt = _tr(sp.Rational(1, 2) * (S2t - 2 * _tr(S['S0t'] * S1t) + (N - 1) * _tr(S['S0t']**2)))
    Qloc = _tr(S['conf'] * _tr(G * Gt))
    res = {}
    for name, ex in (('H', Hloc), ('Q', Qloc), ('J', S['J'])):
        P_ = sp.Poly(sp.expand(ex), tau, sig)
        res[name] = (P_.coeff_monomial(tau * sig), P_.coeff_monomial(sig))
    return res


def block_symbolic(model, msub=None):
    """Blocks with N symbolic and m symbolic (or m = msub).  Omega is computed with m = 0 terms only
    (first-order condition), which involve T(n, e = 0) only and are valid for all N >= 2."""
    l0 = local_symbolic('s', 's', model, msub=0)
    Om0 = sp.cancel(l0['H'][1] / l0['J'][1]); Om1 = sp.cancel(l0['Q'][1] / l0['J'][1])
    out = {'Omega0': Om0, 'Omega1': Om1}
    _shifts.clear()
    for ab in ('ss', 'tt', 'st'):
        loc = local_symbolic(ab[0], ab[1], model, msub=msub)
        out[ab] = (sp.factor(sp.cancel(sp.expand(loc['H'][0] - Om0 * loc['J'][0]))),
                   sp.factor(sp.cancel(sp.expand(loc['Q'][0] - Om1 * loc['J'][0]))))
    out['varpi'] = tuple(sp.factor(sp.cancel(sp.expand(x / I))) for x in out['st'])
    out['shifts'] = sorted(_shifts)
    return out
