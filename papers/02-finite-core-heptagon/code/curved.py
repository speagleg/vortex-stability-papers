"""S^2 and H^2 (G model) ring blocks with the r^4 correction, exact, for given N.

Uses blocks.py (lattice-sum reduction, exact in rho).  Stereographic radius of the ring:
rho^2 = (1 - X0)/(1 + X0) on S^2 (X0 = height of the ring = cos of the colatitude) and
rho^2 = (X0 - 1)/(X0 + 1) on H^2 (X0 = cosh of the geodesic ring radius); y = X0^2.
For the critical mode m = floor(N/2) we print the point-vortex block a_perp^0 as a function of y (it must be
proportional to (1/2)[(N-1)(1+y) - floor(N^2/4)]), the r^4 coefficient in the normalisation of Section 6
A_N(y) := (1 - y)^2 d_perp(y) / c(y), where c(y) = a_perp^0 / ((1/2)[(N-1)(1+y) - floor(N^2/4)]), and the threshold
shift D_N = -(d a_perp/d eps)/(d a_perp/d y) at the threshold y = Theta_N (independent of the normalisation).
"""
import sys
import sympy as sp
import blocks

y = sp.Symbol('y', positive=True)
r2 = sp.Symbol('r2', positive=True)


def crit(model, N, m=None):
    m = N // 2 if m is None else m
    b = blocks.block_numeric(model, N, m)
    rho = blocks.rho
    def conv(ex):
        ex = sp.cancel(sp.expand(ex.subs(rho, sp.sqrt(r2))))
        assert not ex.has(sp.sqrt(r2)) or True
        return ex
    a0 = conv(b['ss'][0]); d = conv(b['ss'][1])
    b0 = conv(b['tt'][0]); e = conv(b['tt'][1]); w = conv(b['varpi'][1])
    return a0, d, b0, e, w


Xs = sp.Symbol('X', positive=True)


def to_X(ex, model):
    r2X = (1 - Xs) / (1 + Xs) if model == 'S2' else (Xs - 1) / (Xs + 1)
    return sp.factor(sp.cancel(ex.subs(r2, r2X)))


def report(model, N):
    a0, d, b0, e, w = crit(model, N)
    target = sp.Rational(1, 2) * ((N - 1) * (1 + Xs**2) - (N * N // 4))
    a0X = to_X(a0, model)
    c = sp.factor(sp.cancel(a0X / target))
    dX = to_X(d, model)
    A = sp.factor(sp.cancel(dX / c * (1 - Xs**2)**2))
    Ay = sp.expand(sp.expand(A).subs(Xs, sp.sqrt(y)))          # A is even in X: a polynomial in y
    Th = sp.Rational(N * N // 4, N - 1) - 1
    # D_N = -(d a_perp/d eps)/(d a_perp/d y),  d/dy = (1/(2X)) d/dX
    D = None
    if Th > 0:
        D = sp.nsimplify(sp.radsimp(sp.simplify((-dX / (sp.diff(a0X, Xs) / (2 * Xs))).subs(Xs, sp.sqrt(Th)))))
    return c, Ay, Th, D, (a0X, dX)


if __name__ == '__main__':
    print("S^2, G kernel: c(y) = normalisation factor, A_N(y) (normalisation of Section 6), Theta_N, D_N")
    for N in range(2, 8):
        c, A, Th, D, _ = report('S2', N)
        print(f" N={N}: c={c};  A_N(y) = {A};  Theta = {Th};  D_N = {D if (Th > 0 and Th < 1) else 'n/a'}")
        sys.stdout.flush()
    print("H^2, G kernel (with background)")
    for N in range(8, 13):
        c, A, Th, D, _ = report('H2', N)
        print(f" N={N}: c={c};  A_N(y) = {A};  Theta = {Th};  D_N = {D}")
        sys.stdout.flush()
