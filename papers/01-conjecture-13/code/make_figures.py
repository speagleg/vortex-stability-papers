"""Figures for paper 01-conjecture-13.  New code (no provenance).

Fig. 1 (paper/figures/mt_line.pdf): n = 4 at b_4 = 2 - sqrt 3, on the D_2-invariant family rho_pm = 1 + u +- v.
  (a) contours of F - F0 (F = H - omega0 J3, H as in paper eq. (2.1)) in the (v, u) plane, with MT's straight
      line u = 0, the momentum level set J3 = J3(ring), and the curve of minima of F in u at fixed v;
  (b) (F - F0)/v^4 along these three curves, tending to D = 6 - 4 sqrt3/3 (line), 4 = n^2 c4 (level set),
      and D - B^2/(4A) (free minimum).
Fig. 2 (paper/figures/n8_traces.pdf): recorded n = 8 integrations (outputs/recorded/D_sinh8_*.npy, produced by
  havelock-vortex-rings@2cc1ee5:conj13/integrate.py; recorded, not rerun): D(t)/D(0) for delta = 1e-3.
Run: python make_figures.py
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy.optimize import brentq, minimize_scalar

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..")
FIG = os.path.join(ROOT, "paper", "figures")
os.makedirs(FIG, exist_ok=True)
plt.rcParams.update({"font.size": 9, "font.family": "serif"})

M = 2
b = 2 - np.sqrt(3)
om0 = (2 * M - 1) * (b * b - 1) / 2


def H(rp, rm):
    up, um = rp * rp, rm * rm
    return (-(M * (M - 1) / 2) * (np.log(up) + np.log(um)) - 2 * M * np.log(rp**M + rm**M)
            + (2 * M - 1) * M * (np.log(1 + b * up) + np.log(1 + b * um)))


def J3(rp, rm):
    return M * (rp * rp / (1 + b * rp * rp) + rm * rm / (1 + b * rm * rm))


def F(u, v):
    return H(1 + u + v, 1 + u - v) - om0 * J3(1 + u + v, 1 + u - v)


F0 = F(0.0, 0.0)
J0 = J3(1.0, 1.0)


def u_level(v):
    return brentq(lambda u: J3(1 + u + v, 1 + u - v) - J0, -0.2, 0.2, xtol=1e-15)


def u_free(v):
    return minimize_scalar(lambda u: F(u, v), bracket=(-0.05, 0.0, 0.05), tol=1e-14).x


fig, ax = plt.subplots(1, 2, figsize=(7.0, 3.0))
V, U = np.meshgrid(np.linspace(-0.25, 0.25, 301), np.linspace(-0.012, 0.012, 301))
Z = F(U, V) - F0
lev = np.quantile(Z[Z > 0], np.linspace(0.02, 0.98, 18))
ax[0].contour(V, U, Z, levels=lev, colors="0.75", linewidths=0.5)
vs = np.linspace(-0.25, 0.25, 201)
ax[0].plot(vs, 0 * vs, color="C1", lw=1.4, label="MT line $u=0$")
ax[0].plot(vs, [u_level(v) for v in vs], color="C0", lw=1.4, label=r"level set $J_3=\mu_3$")
ax[0].plot(vs, [u_free(v) for v in vs], color="C2", lw=1.0, ls="--", label=r"min of $F$ in $u$")
ax[0].set_xlabel(r"$v=(\rho_+-\rho_-)/2$")
ax[0].set_ylabel(r"$u=(\rho_++\rho_-)/2-1$")
ax[0].set_title(r"(a) $F-F_0$ on the $D_2$-family, $n=4$", fontsize=9)
ax[0].legend(fontsize=7, loc="lower center")
vv = np.linspace(0.01, 0.12, 60)
ax[1].plot(vv, [(F(0, v) - F0) / v**4 for v in vv], color="C1", label="MT line")
ax[1].plot(vv, [(F(u_level(v), v) - F0) / v**4 for v in vv], color="C0", label="level set")
ax[1].plot(vv, [(F(u_free(v), v) - F0) / v**4 for v in vv], color="C2", ls="--", label="free min")
D = 6 - 4 * np.sqrt(3) / 3
ax[1].axhline(D, color="C1", lw=0.6, ls=":")
ax[1].axhline(4.0, color="C0", lw=0.6, ls=":")
ax[1].set_xlabel(r"$v$")
ax[1].set_ylabel(r"$(F-F_0)/v^4$")
ax[1].set_title(r"(b) limits $6-4\sqrt{3}/3\approx3.69$ vs $4=n^2c_4$", fontsize=9)
ax[1].legend(fontsize=7)
fig.tight_layout()
fig.savefig(os.path.join(FIG, "mt_line.pdf"))
print("fig1: (F-F0)/v^4 at v=0.01: line %.6f level %.6f free %.6f; D=%.6f" % (
    (F(0, 0.01) - F0) / 1e-8, (F(u_level(0.01), 0.01) - F0) / 1e-8, (F(u_free(0.01), 0.01) - F0) / 1e-8, D))

fig, ax = plt.subplots(1, 2, figsize=(7.0, 2.6))
rec = os.path.join(ROOT, "outputs", "recorded")
LAB = {"+0e+00": r"threshold $b_8$", "-1e-02": r"rel $=-10^{-2}$", "-1e-03": r"rel $=-10^{-3}$",
       "+1e-02": r"rel $=+10^{-2}$"}
for k, rels in enumerate((("-1e-02", "-1e-03"), ("+1e-02", "+0e+00"))):
    for rel, col in zip(rels, ("C3", "C1") if k == 0 else ("0.6", "C0")):
        t, d = np.load(os.path.join(rec, "D_sinh8_%s_1e-03.npy" % rel))
        m = t <= 400
        ax[k].plot(t[m], d[m], color=col, lw=0.7, label=LAB[rel])
        print("fig2: rel=%s max_t D/D0 over [0,2000] = %.4f" % (rel, d.max()))
    ax[k].set_xlabel("$t$")
    ax[k].legend(fontsize=7, loc="upper right")
ax[0].set_ylabel(r"$\mathcal{D}(t)/\mathcal{D}(0)$")
ax[0].set_title("(a) linearly unstable side", fontsize=9)
ax[1].set_title("(b) threshold and stable side", fontsize=9)
ax[1].set_ylim(0, 1.25)
fig.tight_layout()
fig.savefig(os.path.join(FIG, "n8_traces.pdf"))
