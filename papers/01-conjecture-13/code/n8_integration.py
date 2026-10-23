# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# One change: the worker pool is capped at 2 processes (shared machine); results are unchanged. Run with argument 'sinh' (the MT family); 'tanh' is outside this paper.
"""Direct N = 8 integrations on H^2 near the ring threshold.

Poincare disk z (curvature -1), omega = sum_k 4 (1-|z_k|^2)^{-2} dx_k ^ dy_k = sum_k dA_{-1}(x_k), present normalisation:
  G   (sinh): H = sum_{i<j} G(X_ij)   = -sum_{i<j} log|z_i - z_j| + (N-1)/2 sum_k log(1-|z_k|^2) + const,
  K_1 (tanh): H = sum_{i<j} K_1(X_ij) = -sum_{i<j} [log|z_i - z_j| - log|1 - z_i conj z_j|] + const,
using X_ij - 1 = 2|z_i-z_j|^2/((1-|z_i|^2)(1-|z_j|^2)) and X_ij + 1 = 2|1-z_i conj z_j|^2/((1-|z_i|^2)(1-|z_j|^2)).
Equations xdot = H_y/rho, ydot = -H_x/rho, rho = 4/(1-|z|^2)^2 (DOP853, rtol 1e-12, atol 1e-14, T = 2000).
Initial data: ring |z_k|^2 = xi*(1+rel) (rel > 0 is the linearly stable side, X0^2 > threshold) plus the critical
mode |z_k| -> |z_k|(1 + delta (-1)^k), delta = 1e-3.  Thresholds: G: xi* = -b_8 = 8 - 3 sqrt 7 (X0^2 = 9/7);
K_1: xi* = 0.0673562230040813 (root of h_2 for the tanh kernel).
Diagnostic D(t) = max_{i<j} |d_ij(t) - d_ij(ring)| (hyperbolic distances, group invariant), sampled at 40001 times.
Conserved quantities monitored: H and J = sum_k x_k (J_3 = sum (1+|z|^2)/(1-|z|^2), J_+ = sum 2 z/(1-|z|^2)).
Usage: python n8_integration.py sinh|tanh   (runs its parameter set in parallel, prints in a fixed order; about 10 minutes)
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1"); os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import sys
from multiprocessing import Pool
import numpy as np
from scipy.integrate import solve_ivp

N = 8
T = 2000.0
DELTA = 1e-3
XI = {"sinh": 8 - 3 * np.sqrt(7.0), "tanh": 0.0673562230040813}
RELS = (-1e-2, -1e-3, 0.0, 1e-2)


def make(model):
    iu, ju = np.triu_indices(N, 1)

    def grad(x, y):
        dx = x[:, None] - x[None, :]; dy = y[:, None] - y[None, :]
        r2 = dx * dx + dy * dy; np.fill_diagonal(r2, 1.0)
        gx = -(dx / r2).sum(1); gy = -(dy / r2).sum(1)
        if model == "sinh":
            s = 1 - x * x - y * y
            gx += -(N - 1) * x / s; gy += -(N - 1) * y / s
        else:
            z = x + 1j * y
            w = 1 - z[:, None] * np.conj(z)[None, :]          # w_kj = 1 - z_k conj z_j
            cw = np.conj(w); aw = (w * cw).real
            np.fill_diagonal(aw, 1.0)
            tx = (-np.conj(z)[None, :] * cw).real / aw        # d/dx_k log|w_kj|
            ty = (-1j * np.conj(z)[None, :] * cw).real / aw   # d/dy_k log|w_kj|
            np.fill_diagonal(tx, 0.0); np.fill_diagonal(ty, 0.0)
            gx += tx.sum(1); gy += ty.sum(1)
        return gx, gy

    def rhs(t, u):
        x, y = u[:N], u[N:]
        gx, gy = grad(x, y)
        rho = 4 / (1 - x * x - y * y) ** 2
        return np.concatenate([gy / rho, -gx / rho])

    def H(x, y):
        z = x + 1j * y
        h = -np.log(np.abs(z[iu] - z[ju])).sum()
        if model == "sinh":
            h += (N - 1) / 2 * np.log(1 - np.abs(z) ** 2).sum()
        else:
            h += np.log(np.abs(1 - z[iu] * np.conj(z[ju]))).sum()
        return h

    def J(x, y):
        s = 1 - x * x - y * y
        return np.array([((2 - s) / s).sum(), (2 * x / s).sum(), (2 * y / s).sum()])

    def dist(x, y):
        s = 1 - x * x - y * y
        return np.arccosh(1 + 2 * ((x[iu] - x[ju]) ** 2 + (y[iu] - y[ju]) ** 2) / (s[iu] * s[ju]))

    return rhs, H, J, dist


def run(args):
    model, rel = args
    rhs, H, J, dist = make(model)
    k = np.arange(N); ph = 2 * np.pi * k / N
    R = np.sqrt(XI[model] * (1 + rel))
    dref = dist(R * np.cos(ph), R * np.sin(ph))
    r = R * (1 + DELTA * (-1.0) ** k)
    u0 = np.concatenate([r * np.cos(ph), r * np.sin(ph)])
    D0 = np.max(np.abs(dist(u0[:N], u0[N:]) - dref))
    te = np.linspace(0, T, 40001)
    sol = solve_ivp(rhs, (0, T), u0, method="DOP853", rtol=1e-12, atol=1e-14, t_eval=te)
    D = np.array([np.max(np.abs(dist(sol.y[:N, m], sol.y[N:, m]) - dref)) for m in range(len(te))])
    dH = max(abs(H(sol.y[:N, m], sol.y[N:, m]) - H(u0[:N], u0[N:])) for m in range(0, len(te), 400))
    J0 = J(u0[:N], u0[N:])
    dJ = max(np.max(np.abs(J(sol.y[:N, m], sol.y[N:, m]) - J0)) for m in range(0, len(te), 400))
    return (f"{model} rel={rel:+.0e} delta={DELTA:.0e}: D0={D0:.4e}  max D/D0={D.max() / D0:.3f}  max D={D.max():.3g}  "
            f"frac(D<D0/2)={np.mean(D < D0 / 2):.2f}  |dH|<1e-7: {dH < 1e-7}  |dJ|<1e-8: {dJ < 1e-8}")


if __name__ == "__main__":
    model = sys.argv[1]
    assert model in XI
    with Pool(min(2, len(RELS))) as pool:  # changed: at most 2 workers (shared machine)
        lines = pool.map(run, [(model, rel) for rel in RELS])
    print(f"N={N} {model}: xi*={XI[model]:.15g}, T={T:g}, delta={DELTA:g}, rel in {RELS}")
    for line in lines:
        print(line)
    print("expected: rel < 0 saturates (max D roughly proportional to sqrt|rel|); rel >= 0 stays within D0 (max D/D0 = 1.000)")
