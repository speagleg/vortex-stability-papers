"""The G_1 (tanh-kernel) threshold shifts on H^2, D^tanh_N, N = 8..12.

Model (Section 6 of the paper): on the Poincare disc, metric e^{2 Phi}|dz|^2, e^{2 Phi} = 4/(1-|z|^2)^2,
  H = sum_{k<l} W1(z_k, z_l),  W1(z, w) = -log|z - w| + log|1 - conj(w) z|   (W1 = -log tanh(d/2)),
  Q = sum_k e^{-4 Phi(z_k)} |f_zz - 2 Phi_z f_z|^2,  f = sum_{l != k} W1(., z_l),
  F = H + r^4 Q - Omega J,  J = (1 + |z|^2)/(1 - |z|^2).
Ring |z_k| = rho, xi = rho^2 = tanh^2(ring radius/2).  The threshold xi_* is the zero of the point-vortex critical
stiffness a_perp^0(xi) (m = floor(N/2)) and D^tanh = d xi_*/d(r^4) = -d_perp/(d a_perp^0/d xi).

Method: the second-order Taylor expansion of the local terms is done symbolically (as in blocks.py) with the Bloch
substitution; the sums over the other vortices are then evaluated directly at 50 digits.  The threshold is found by a
secant iteration started from the rough guesses XI0, and its derivative by central differences (double precision).
"""
import sympy as sp
import mpmath as mp
from functools import lru_cache
from blocks import bloch_vars, series2, trunc, tau, sig, Pj, Wj, Xp, Xm, h

mp.mp.dps = 50
R1, R2, q = sp.symbols('R1 R2 q')   # R1 = 1/(1 - q/w), R2 = 1/(1 - q w), q = rho^2
rho = sp.Symbol('rho', positive=True)


@lru_cache(maxsize=None)
def summands(alpha, beta):
    u0, ut0, uj, utj = bloch_vars(alpha, beta)
    E = lambda x: sp.exp(h * x)
    pbar = 1 - Pj
    d = (E(u0) - 1) - Wj * (E(uj) - 1)
    dt = (E(ut0) - 1) - (E(utj) - 1) / Wj
    z0 = rho * E(u0); zt0 = rho * E(ut0)
    # 1 - conj(z_j) z_0 = (1 - q/w) (1 - R1 (q/w) (e^{ut_j + u_0} - 1));  1 - z_j conj(z_0) similarly with R2, q w
    A1 = 1 - R1 * (q / Wj) * (E(utj + u0) - 1)
    A2 = 1 - R2 * (q * Wj) * (E(uj + ut0) - 1)
    T2 = lambda ex: trunc(series2(ex).subs(h, 1))
    s = {}
    s['Hp'] = T2(-sp.Rational(1, 4) * (sp.log(1 + Pj * d) + sp.log(1 + pbar * dt)))
    s['Hr'] = T2(sp.Rational(1, 4) * (sp.log(A1) + sp.log(A2)))
    s['J'] = T2((1 + z0 * zt0) / (1 - z0 * zt0))
    # holomorphic derivatives at z_0 of the pair term, and their "conjugates" (tilde variables)
    # 1/(z0 - zj) = p/(rho (1 + p d));  conj(z_j)/(1 - conj(z_j) z0) = (q/(rho w)) e^{ut_j} R1 / A1 / rho * rho ...
    zj_t = rho / Wj * E(utj)          # conj(z_j)
    zj = rho * Wj * E(uj)             # z_j
    s['a1'] = T2(Pj / (1 + Pj * d) / rho)                      # 1/(z0 - zj)
    s['a2'] = T2(Pj**2 / (1 + Pj * d)**2 / rho**2)             # 1/(z0 - zj)^2
    s['b1'] = T2(zj_t * R1 / A1)                               # conj(zj)/(1 - conj(zj) z0)
    s['b2'] = T2((zj_t * R1 / A1)**2)
    s['a1t'] = T2(pbar / (1 + pbar * dt) / rho)                # conjugate quantities
    s['a2t'] = T2(pbar**2 / (1 + pbar * dt)**2 / rho**2)
    s['b1t'] = T2(zj * R2 / A2)
    s['b2t'] = T2((zj * R2 / A2)**2)
    s['Phz'] = T2(zt0 / (1 - z0 * zt0))                        # Phi_z = conj(z)/(1 - |z|^2)
    s['Phzt'] = T2(z0 / (1 - z0 * zt0))
    s['conf'] = T2(((1 - z0 * zt0) / 2)**4)
    return s


def jsum(expr, N, m, qv):
    """sum over j = 1..N-1 of a polynomial in tau, sigma whose coefficients involve p, w, Xp, Xm, R1, R2."""
    expr = sp.expand(expr)
    poly = sp.Poly(expr, tau, sig)
    out = 0
    z = mp.expjpi(mp.mpf(2) / N)
    for (dt_, ds_), coeff in poly.terms():
        f = sp.lambdify((Pj, Wj, Xp, Xm, R1, R2, q, rho), coeff, 'mpmath')
        tot = mp.mpf(0)
        for j in range(1, N):
            w = z**j
            tot += f(1 / (1 - w), w, w**m, w**(-m), 1 / (1 - qv / w), 1 / (1 - qv * w), qv, mp.sqrt(qv))
        out += sp.Float(mp.re(tot), 50) * tau**dt_ * sig**ds_ + sp.I * sp.Float(mp.im(tot), 50) * tau**dt_ * sig**ds_
    return out


def site(expr, qv):
    return sp.expand(expr.subs({rho: sp.sqrt(sp.Float(qv, 50)), q: sp.Float(qv, 50)}))


def local(alpha, beta, N, m, qv):
    s = summands(alpha, beta)
    tr = lambda ex: trunc(sp.expand(ex))
    H = jsum(s['Hp'], N, m, qv) + jsum(s['Hr'], N, m, qv)
    A1 = jsum(s['a1'], N, m, qv); A2 = jsum(s['a2'], N, m, qv)
    B1 = jsum(s['b1'], N, m, qv); B2 = jsum(s['b2'], N, m, qv)
    A1t = jsum(s['a1t'], N, m, qv); A2t = jsum(s['a2t'], N, m, qv)
    B1t = jsum(s['b1t'], N, m, qv); B2t = jsum(s['b2t'], N, m, qv)
    Phz = site(s['Phz'], qv); Phzt = site(s['Phzt'], qv); conf = site(s['conf'], qv)
    # f_z = sum[-1/(2(z-zj)) - conj(zj)/(2(1-conj(zj) z))],  f_zz = sum[1/(2(z-zj)^2) - conj(zj)^2/(2(1-conj(zj)z)^2)]
    fz = -(A1 + B1) / 2; fzz = (A2 - B2) / 2
    fzt = -(A1t + B1t) / 2; fzzt = (A2t - B2t) / 2
    G = tr(fzz - 2 * tr(Phz * fz)); Gt = tr(fzzt - 2 * tr(Phzt * fzt))
    Q = tr(conf * tr(G * Gt))
    J = site(s['J'], qv)
    res = {}
    for name, ex in (('H', H), ('Q', Q), ('J', J)):
        P_ = sp.Poly(sp.expand(ex), tau, sig)
        res[name] = (complex(P_.coeff_monomial(tau * sig)), complex(P_.coeff_monomial(sig)))
    return res


def aperp(N, xi):
    m = N // 2
    l0 = local('s', 's', N, 0, xi)
    Om0 = l0['H'][1] / l0['J'][1]; Om1 = l0['Q'][1] / l0['J'][1]
    l = local('s', 's', N, m, xi)
    return (l['H'][0] - Om0 * l['J'][0]).real, (l['Q'][0] - Om1 * l['J'][0]).real


XI0 = {8: 0.067, 9: 0.113, 10: 0.166, 11: 0.205, 12: 0.247}   # rough starting guesses

if __name__ == '__main__':
    import sys
    Ns = [8, 9, 10, 11, 12] if '--fast' not in sys.argv else [8]
    print("H^2, G_1 kernel: threshold xi_* and D^tanh = d xi_*/d(r^4) (Taylor + direct 50-digit sums)")
    for N in Ns:
        f0 = lambda x: aperp(N, float(x))[0]
        x0 = XI0[N]
        # secant iteration in double precision (the sums are in 50 digits, the polynomial algebra in sympy floats)
        xa, xb = x0 * (1 - 1e-6), x0 * (1 + 1e-6)
        fa, fb = f0(xa), f0(xb)
        for it in range(12):
            xc = xb - fb * (xb - xa) / (fb - fa)
            xa, fa, xb, fb = xb, fb, xc, f0(xc)
            if abs(fb) < 1e-13:
                break
        xs = xb
        hstep = 1e-6
        dA = (f0(xs + hstep) - f0(xs - hstep)) / (2 * hstep)
        d1 = aperp(N, xs)[1]
        D = -d1 / dA
        print(f"N={N}: xi_*={xs:.15f}  a_perp^0(xi_*)={f0(xs):.1e}  d_perp={d1:.10f}  D^tanh={D:.10f}")
        sys.stdout.flush()
