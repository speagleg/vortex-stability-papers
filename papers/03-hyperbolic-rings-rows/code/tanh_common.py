# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# Changes: none
"""shared closed forms for the tanh (G_1) ring, derived independently (no archive code).

Model: H = sum_{j<k} G_1(X_jk), G_1(X) = 1/2 log((X+1)/(X-1)) on H^2, omega = sum dA_{-1},
J_3 = sum (cosh r_k - 1) (generates -d/dtheta), F = H - Omega J_3.  Disk chart z = z_D:
  X - 1 = 2|z-w|^2/((1-|z|^2)(1-|w|^2)),  X + 1 = 2|1 - z conj w|^2/((1-|z|^2)(1-|w|^2)),
so G_1 = -log|z-w| + log|1 - z conj w|.  Ring z_j = sqrt(xi) e(j/N) e^{s_j + i theta_j}, xi = tanh^2(r/2) = -b,
X0 = (1+xi)/(1-xi), A_0 = 4xi/(1-xi)^2 = X0^2 - 1.

Derivation (written for this check).  Since log|1-u| = -Re sum_n u^n/n,
  sum_{j<k} log|1 - z_j conj z_k| = -1/2 sum_{n>=1} |s_n|^2/n - 1/2 sum_j log(1-|z_j|^2),   s_n = sum_j z_j^n.
With u_j = s_j + i theta_j, z_j^n = xi^{n/2} e(nj/N) e^{n u_j}; to second order
  |s_n|^2 = xi^n [ N^2 [N|n] + 2 N n [N|n] sum_j s_j + n^2 |U_{n mod N}|^2 + N n^2 [N|n] sum_j (s_j^2 - theta_j^2) ],
  U_k = sum_j e(kj/N) u_j.  Hence, with W_k = sum_{n>=1, n = k mod N} n xi^n,
  H_img linear  = -N xi^N/(1-xi^N) sum_j s_j,
  H_img quadratic = -1/2 [ sum_{k=1}^N W_k |U_k|^2 + N W_N sum_j (s_j^2 - theta_j^2) ].
Fourier symbol with v_m = (e(mj/N))_j, block (1/N) v_m^* Hess v_m, order (s, theta):
  image:     ss  -(N/2)(W_m + W_{N-m}) - N W_N,   tt  -(N/2)(W_m + W_{N-m}) + N W_N,   st  i (N/2)(W_m - W_{N-m});
  planar -log|z_j - z_k|:  ss -m(N-m)/2,  tt +m(N-m)/2,  st 0     (Fejer: sum_d sin^2(pi m d/N)/sin^2(pi d/N) = m(N-m));
  one-body -1/2 log(1 - xi e^{2s}):  ss 2xi/(1-xi)^2;
  -Omega J_3, J_3 = (1 + xi e^{2s})/(1 - xi e^{2s}) - 1:  d_s J_3 = A_0, d_s^2 J_3 = 2 X0 A_0  ->  ss -2 X0 (A_0 Omega).
Relative equilibrium: d_{s_j} H = A_0 Omega with
  A_0 Omega = -(N-1)/2 + xi/(1-xi) - N xi^N/(1-xi^N)          (theta-gradient vanishes by symmetry).
So M_m = [[aperp, i varpi], [-i varpi, apar]] with
  aperp = -m(N-m)/2 + 2xi/(1-xi)^2 - 2 X0 (A_0 Omega) - (N/2)(W_m + W_{N-m}) - N W_N,
  apar  =  m(N-m)/2 + N W_N - (N/2)(W_m + W_{N-m}),
  varpi = (N/2)(W_m - W_{N-m}),
  W_k = k xi^k/(1-xi^N) + N xi^{k+N}/(1-xi^N)^2  (1 <= k <= N; sum over n = k + pN).
"""
import sympy as sp
import mpmath as mp

x = sp.Symbol('x')  # xi


def W_sym(N, k):
    return k * x**k / (1 - x**N) + N * x**(k + N) / (1 - x**N)**2


def blocks_sym(N, m):
    """Own derivation: (aperp, apar, varpi, A0*Omega) as sympy rational functions of x = xi."""
    X0 = (1 + x) / (1 - x)
    AOm = -sp.Rational(N - 1, 2) + x / (1 - x) - N * x**N / (1 - x**N)
    Wm, Wn, WN = W_sym(N, m), W_sym(N, N - m), W_sym(N, N)
    mm = sp.Rational(m * (N - m), 2)
    aperp = -mm + 2 * x / (1 - x)**2 - 2 * X0 * AOm - sp.Rational(N, 2) * (Wm + Wn) - N * WN
    apar = mm + N * WN - sp.Rational(N, 2) * (Wm + Wn)
    varpi = sp.Rational(N, 2) * (Wm - Wn)
    return aperp, apar, varpi, AOm


def blocks_T2_literal(N, m):
    """The havelock note's Theorem 2 typed from the claim text (for the symbolic comparison only)."""
    X0 = (1 + x) / (1 - x)
    D = 1 - x**N
    aperp = ((N - 1) * X0 - (X0 - 1)**2 / 2 - sp.Rational(m * (N - m), 2) + 2 * N * X0 * x**N / D
             - N**2 * x**N / D**2
             - sp.Rational(N, 2) * (m * x**m + (N - m) * x**(N - m) + (N - m) * x**(N + m) + m * x**(2 * N - m)) / D**2)
    WN = W_sym(N, N)
    apar = sp.Rational(m * (N - m), 2) + N * WN - sp.Rational(N, 2) * (W_sym(N, m) + W_sym(N, N - m))
    varpi = sp.Rational(N, 2) * (W_sym(N, m) - W_sym(N, N - m))
    return aperp, apar, varpi


def as_int_poly(expr):
    """Cancel a rational function that must be a polynomial in x with integer coefficients; return a sympy Poly."""
    e = sp.cancel(sp.together(expr))
    num, den = sp.fraction(e)
    q, r = sp.div(sp.Poly(num, x), sp.Poly(den, x))
    assert r.is_zero, "not a polynomial"
    assert all(c.is_integer for c in q.all_coeffs()), "non-integer coefficient"
    return q


def cleared(N, m):
    """Cleared numerators (conventions): check aperp = 2(1-x)^2(1-x^N)^2 aperp, check apar = 2(1-x^N)^2 apar,
    check varpi = 2(1-x^N)^2 varpi, check det = check aperp check apar - (1-x)^2 check varpi^2."""
    ap, bp, vp, _ = blocks_sym(N, m)
    D = 1 - x**N
    A = as_int_poly(2 * (1 - x)**2 * D**2 * ap)
    B = as_int_poly(2 * D**2 * bp)
    V = as_int_poly(2 * D**2 * vp)
    det = A * B - sp.Poly((1 - x)**2, x) * V * V
    return A, B, V, det


def blocks_mp(N, m, xi):
    """mpmath evaluation of the derived closed forms."""
    xi = mp.mpf(xi)
    D = 1 - xi**N
    W = lambda k: k * xi**k / D + N * xi**(k + N) / D**2
    X0 = (1 + xi) / (1 - xi)
    AOm = -mp.mpf(N - 1) / 2 + xi / (1 - xi) - N * xi**N / D
    mm = mp.mpf(m * (N - m)) / 2
    aperp = -mm + 2 * xi / (1 - xi)**2 - 2 * X0 * AOm - mp.mpf(N) / 2 * (W(m) + W(N - m)) - N * W(N)
    apar = mm + N * W(N) - mp.mpf(N) / 2 * (W(m) + W(N - m))
    varpi = mp.mpf(N) / 2 * (W(m) - W(N - m))
    return aperp, apar, varpi, AOm


def to_flint(p):
    import flint
    return flint.fmpz_poly([int(c) for c in reversed(p.all_coeffs())])
