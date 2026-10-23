"""Figures for paper 3 (new code). Output: paper/figures/boundary.pdf, paper/figures/large_n.pdf.

Fig. 1: the stability boundary in the (kappa, ell) plane: hypercycle branch (zero of the pairing series
F(pi), exact formula of Thm 6.2), the explicit sufficient bound ell_A, the horocycle point (1, ell_*), and
the ring threshold points (coth r_*(N), ell_N), N = 8..64, from the closed-form blocks (floating point).
Fig. 2: ring threshold spacing ell_N against N, with the limit ell_* and the second-order curves.
All values plotted are floating point (NUMERICAL); the certified values are in the other outputs.
"""
import os
import numpy as np
import mpmath as mp
from scipy.optimize import brentq
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
FIG = os.path.join(HERE, "..", "paper", "figures")
os.makedirs(FIG, exist_ok=True)

TAU_INF = 7.4453392449490186872
ELL_STAR = 2 * np.pi / TAU_INF


def F_pi(alpha, lu, nmax=4000):
    """Pairing series F(pi) (Thm 6.2 / eq. (6.4)) at kappa = cos(alpha), strip spacing lu."""
    q = np.exp(-lu)
    n = np.arange(1, nmax + 1)
    qn = q ** n
    s2 = np.sin(alpha) ** 2
    t1 = (np.sin(2 * alpha) * np.sin(2 * n * alpha) - 2 * n * s2 * np.sin(n * alpha) ** 2) * qn / (1 - qn)
    t2 = -2 * n * s2 * np.cos(n * alpha) ** 2 * qn / (1 + qn)
    return float(np.sum(t1 + t2))


def hyper_threshold(kappa):
    a = np.arccos(kappa)
    f = lambda lu: F_pi(a, lu, nmax=int(min(200000, 60 / lu + 50)))
    lo, hi = 1e-3, 60.0
    lu = brentq(f, lo, hi, xtol=1e-13)
    return lu / np.sin(a)


def ring_a_crit(N, xi):
    m = N // 2
    X = xi ** N
    W = lambda k: k * xi ** k / (1 - X) + N * xi ** (k + N) / (1 - X) ** 2
    W0 = N * X / (1 - X) ** 2
    E = -(N - 1) / 2 + xi / (1 - xi) - N * X / (1 - X)
    Vpp = 2 * xi / (1 - xi) ** 2 - 2 * E * (1 + xi) / (1 - xi)
    return Vpp - m * (N - m) / 2 - N * W0 - N / 2 * (W(m) + W(N - m))


def ring_threshold(N):
    mp.mp.dps = 30
    f = lambda x: ring_a_crit(N, x)
    xi = mp.findroot(f, (mp.mpf("1e-6"), mp.mpf(1) - mp.mpf("1e-9")), solver="anderson")
    xi = mp.mpf(xi)
    c = (1 + xi) / (1 - xi)
    s = mp.sqrt(c * c - 1)
    return float(c / s), float(2 * mp.pi * s / N)


def main():
    kc = 1 / np.sqrt(2)
    ks = kc + (1 - kc) * np.linspace(0.004, 0.9995, 120) ** 1.0
    ells = np.array([hyper_threshold(k) for k in ks])
    ellA = np.arccosh(1 / (2 * ks ** 2 - 1)) / np.sqrt(1 - ks ** 2)
    rings = {N: ring_threshold(N) for N in range(8, 65)}
    print("hypercycle branch: kappa, ell_hyp(kappa) at selected points")
    for k in [0.72, 0.75, 0.8, 0.9, 0.95, 0.99, 0.999]:
        print(f"  {k:7.4f}  {hyper_threshold(k):.10f}")
    print("ring points (coth r_*, ell_N):")
    for N in [8, 9, 10, 12, 16, 24, 32, 48, 64]:
        print(f"  N={N:3d}  {rings[N][0]:.6f}  {rings[N][1]:.6f}")

    fig, ax = plt.subplots(figsize=(6.4, 4.2))
    ax.axvspan(0, kc, color="0.88")
    ax.text(0.36, 3.6, "unstable at every spacing\n" r"($|\kappa|\leq 1/\sqrt{2}$)", ha="center", fontsize=9)
    ax.plot(ks, ells, color="C0", lw=2, label=r"hypercycle rows: $\ell_{\rm hyp}(\kappa)$")
    ax.plot(ks, ellA, color="C0", lw=1, ls="--", label=r"sufficient bound $\ell_A(\kappa)$")
    kr = [rings[N][0] for N in rings]
    lr = [rings[N][1] for N in rings]
    ax.plot(kr, lr, "o", color="C3", ms=3, label=r"rings $(\coth r_*(N),\ell_N)$, $N=8..64$")
    ax.plot([1], [ELL_STAR], "k*", ms=11, label=r"horocycle row $(1,\ell_*)$")
    ax.axvline(1, color="k", lw=0.5)
    ax.set_xlim(0, 2.1)
    ax.set_ylim(0, 5)
    ax.set_xlabel(r"geodesic curvature $\kappa$ of the carrying curve")
    ax.set_ylabel(r"arc spacing $\ell$")
    ax.text(0.55, 4.6, "geodesic\n+ hypercycles", fontsize=8, ha="center")
    ax.text(1.55, 4.6, "circles (rings)", fontsize=8, ha="center")
    ax.legend(loc="center right", fontsize=8)
    fig.tight_layout()
    fig.savefig(os.path.join(FIG, "boundary.pdf"))

    # Fig 2: ell_N vs N
    Ns = np.arange(8, 65)
    fig, ax = plt.subplots(figsize=(6.0, 3.6))
    ev = [N for N in Ns if N % 2 == 0]
    od = [N for N in Ns if N % 2 == 1]
    ax.plot(ev, [rings[N][1] for N in ev], "o", ms=3, color="C0", label="even $N$")
    ax.plot(od, [rings[N][1] for N in od], "s", ms=3, color="C1", label="odd $N$")
    NN = np.linspace(8, 64, 200)
    ax.plot(NN, ELL_STAR - 19.98964481 / NN ** 2, color="C0", lw=0.8, label=r"$\ell_*-19.990\,N^{-2}$")
    ax.plot(NN, ELL_STAR - 20.87042550 / NN ** 2, color="C1", lw=0.8, ls="--", label=r"$\ell_*-20.870\,N^{-2}$")
    ax.axhline(ELL_STAR, color="k", lw=0.6)
    ax.text(10, ELL_STAR + 0.005, r"$\ell_*=2\pi/\tau_\infty=0.84391$", fontsize=9)
    ax.set_xlabel("$N$")
    ax.set_ylabel(r"threshold arc spacing $\ell_N$")
    ax.set_ylim(0.4, 0.88)
    ax.legend(loc="lower right", fontsize=8)
    fig.tight_layout()
    fig.savefig(os.path.join(FIG, "large_n.pdf"))
    print("wrote boundary.pdf, large_n.pdf")


if __name__ == "__main__":
    main()
