"""Figures of the paper (with --fast: written to outputs/fast/figures/ instead of paper/figures/), from the recorded outputs (outputs/*.out) and a few steady-state solves.

fig_shapes.pdf     steady patch heptagons (ring radius 1) at a = 0.10, 0.20 and at the onset a = 0.2614
fig_slowpair.pdf   the slow m = 3 pair from contour dynamics: s_3/a^4 and varpi_3/a^4 versus a^2,
                   with the asymptotic values -84 and 16 (Corollary 3.6)
fig_onset.pdf      largest real part over all Bloch blocks versus a, and the collision in block m = 2
"""
import os
import re
import sys
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, '..', 'outputs')
FIG = os.path.join(HERE, '..', 'paper', 'figures')
if '--fast' in sys.argv:          # never overwrite the paper's figures in fast mode
    FIG = os.path.join(HERE, '..', 'outputs', 'fast', 'figures')
os.makedirs(FIG, exist_ok=True)
plt.rcParams.update({'font.size': 9, 'figure.dpi': 150})
cnum = r'([+-]?[0-9.]+e[+-][0-9]+)([+-][0-9.]+)i'


def parse_scan():
    rows = []
    for line in open(os.path.join(OUT, 'cd_heptagon_scan.out')):
        if not line.startswith('a='):
            continue
        a = float(re.search(r'a=([0-9.]+)', line).group(1))
        mx = float(re.search(r'maxRe=([+-][0-9.e+-]+)', line).group(1))
        m = re.search(r'slow3=\(' + cnum + ', ' + cnum + r'\)', line)
        l1 = complex(float(m.group(1)), float(m.group(2)))
        l2 = complex(float(m.group(3)), float(m.group(4)))
        rows.append((a, mx, l1, l2))
    return rows


def fig_slowpair(rows):
    A = np.array([r[0] for r in rows if r[0] <= 0.2])
    L1 = np.array([r[2] for r in rows if r[0] <= 0.2]); L2 = np.array([r[3] for r in rows if r[0] <= 0.2])
    s = (((L1 - L2) / 2)**2).real
    vp = (1j * (L1 + L2) / 2).real
    fig, ax = plt.subplots(1, 2, figsize=(6.4, 2.5))
    ax[0].plot(A**2, s / A**4, 'o', ms=3, label='contour dynamics')
    ax[0].axhline(-84, color='k', lw=0.8, ls='--', label=r'$-84$ (asymptotics)')
    ax[0].set_xlabel(r'$(r/R)^2$'); ax[0].set_ylabel(r'$s_3/(r/R)^4$')
    ax[0].legend(frameon=False)
    ax[1].plot(A**2, vp / A**4, 'o', ms=3)
    ax[1].axhline(16, color='k', lw=0.8, ls='--', label=r'$16$ (asymptotics)')
    ax[1].set_xlabel(r'$(r/R)^2$'); ax[1].set_ylabel(r'$\varpi_3/(r/R)^4$')
    ax[1].legend(frameon=False)
    fig.tight_layout()
    fig.savefig(os.path.join(FIG, 'fig_slowpair.pdf'))


def parse_onset_modes():
    data = {}
    for line in open(os.path.join(OUT, 'cd_onset_modes.out')):
        m = re.match(r'a=([0-9.]+) m=2: (.*)', line)
        if not m:
            continue
        a = float(m.group(1))
        for z in re.finditer(cnum + r' \(frac1=([0-9.]+), kdom=([0-9]+)\)', m.group(2)):
            data.setdefault(a, []).append((float(z.group(1)), float(z.group(2)), float(z.group(3)), int(z.group(4))))
    return data


def fig_onset(rows):
    A = np.array([r[0] for r in rows]); MX = np.array([r[1] for r in rows])
    fig, ax = plt.subplots(1, 2, figsize=(6.4, 2.6))
    ax[0].semilogy(A, np.maximum(MX, 1e-14), 'o-', ms=3)
    ax[0].axvline(0.261378, color='k', lw=0.8, ls=':')
    ax[0].set_xlabel(r'$r/R$'); ax[0].set_ylabel(r'$\max\,\mathrm{Re}\,\lambda$ (all blocks)')
    ax[0].text(0.03, 1e-3, r'$a_c=0.26138$', fontsize=8)
    data = parse_onset_modes()
    for a, lst in sorted(data.items()):
        for re_, im, f1, kd in lst:
            if im < 0:
                ax[1].plot(a, im, 'o' if kd == 1 else 's', color='C0' if kd == 1 else 'C3', ms=3)
    ax[1].plot([], [], 'o', color='C0', ms=3, label='displacement mode ($k=1$)')
    ax[1].plot([], [], 's', color='C3', ms=3, label='elliptical mode ($k=2$)')
    ax[1].axvline(0.261378, color='k', lw=0.8, ls=':')
    ax[1].set_xlabel(r'$r/R$'); ax[1].set_ylabel(r'$\mathrm{Im}\,\lambda$, block $m=2$')
    ax[1].legend(frameon=False, fontsize=7)
    fig.tight_layout()
    fig.savefig(os.path.join(FIG, 'fig_onset.pdf'))


def fig_shapes():
    import cd
    fig, ax = plt.subplots(1, 3, figsize=(6.4, 2.3))
    for axi, a in zip(ax, (0.10, 0.20, 0.2614)):
        ring = cd.Ring(7, a, 65 if a < 0.25 else 129)
        r0, Om, res, smin = ring.solve_steady()
        th = np.linspace(0, 2 * np.pi, 400)
        # trigonometric interpolation of the boundary
        c = np.fft.fft(r0) / len(r0); k = np.fft.fftfreq(len(r0), 1.0 / len(r0))
        rr = np.real(sum(c[i] * np.exp(1j * k[i] * th) for i in range(len(r0))))
        for p in range(7):
            ph = 2 * np.pi * p / 7
            x = np.cos(ph) + rr * np.cos(th + ph); y = np.sin(ph) + rr * np.sin(th + ph)
            axi.fill(x, y, color='C0', alpha=0.6, lw=0.5)
        axi.plot(np.cos(th), np.sin(th), 'k:', lw=0.5)
        axi.set_aspect('equal'); axi.axis('off')
        axi.set_title(f'$r/R = {a:g}$', fontsize=9)
    fig.tight_layout()
    fig.savefig(os.path.join(FIG, 'fig_shapes.pdf'))


if __name__ == '__main__':
    rows = parse_scan()
    fig_slowpair(rows)
    fig_onset(rows)
    if '--fast' not in sys.argv:
        fig_shapes()
    print("figures written to", os.path.normpath(FIG))
