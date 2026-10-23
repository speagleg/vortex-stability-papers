"""Which modes collide at the onset of instability of the patch heptagon, and where the steady branch ends.

(1) In the Bloch blocks m = 2 and m = 1 we follow the eigenvalues with 3 < |Im| < 7 as a increases to the
    onset a_c ~ 0.26138, and classify each eigenvector by the Fourier content of the boundary perturbation
    delta rho(theta) = sum_k c_k e^{i k theta}: k = 1 is a displacement of the patch (a "centre" mode),
    k >= 2 a deformation (a "shape" mode).  We print the fraction of the norm in k = +-1 and the dominant |k|.
    We also print the Krein signature sign(Im(lambda) * <v, H v>)-type quantity in the simplest available
    form: the sign of d(Im lambda)/da is shown instead (the colliding pair moves towards each other).
(2) The steady branch is continued beyond a = 0.278 in small steps (M = 257) until Newton fails, recording
    the smallest singular value of the Newton matrix and the gap between neighbouring boundaries.
"""
import sys
import numpy as np
import cd
from cd_heptagon_scan import gap, resample

FAST = '--fast' in sys.argv


def classify(ring, r0, Q, y):
    v = Q @ y
    c = np.fft.fft(v) / len(v)
    k = np.fft.fftfreq(len(v), 1.0 / len(v)).astype(int)
    w = abs(c)**2
    frac1 = w[abs(k) == 1].sum() / w.sum()
    kd = abs(k[np.argmax(w * (k != 0))])
    return frac1, kd


def block_modes(a, M, blocks=(1, 2), window=(2.5, 8.0)):
    ring = cd.Ring(7, a, M)
    r0, Om, res, smin = ring.solve_steady()
    Jc = ring.jacobian_columns(r0, Om)
    Bs = ring.bloch_blocks(Jc)
    Q, l = ring.area_projector(r0)
    out = {}
    for m in blocks:
        ev, V = np.linalg.eig(Q.T @ Bs[m] @ Q)
        sel = [(ev[i], *classify(ring, r0, Q, V[:, i])) for i in range(len(ev))
               if window[0] < abs(ev[i].imag) < window[1]]
        out[m] = sorted(sel, key=lambda t: t[0].imag)
    return out, r0, Om


if __name__ == '__main__':
    M = 129 if FAST else 193
    alist = [0.20, 0.24, 0.26, 0.2613] if FAST else [0.20, 0.22, 0.24, 0.25, 0.255, 0.258, 0.26, 0.261, 0.2613, 0.26137, 0.2614, 0.262]
    print("Eigenvalues of Bloch blocks m = 1, 2 with 2.5 < |Im| < 8 (normalised units); frac1 = share of the boundary")
    print("perturbation norm in Fourier modes k = +-1 (patch displacement), kdom = dominant |k| (k != 0).")
    for a in alist:
        out, r0, Om = block_modes(a, M)
        for m, sel in out.items():
            print(f"a={a:.5f} m={m}: " + "; ".join(f"{z.real:+.2e}{z.imag:+.5f}i (frac1={f:.2f}, kdom={k})" for z, f, k in sel))
        sys.stdout.flush()
    # branch continuation
    print("Continuation of the steady branch beyond a = 0.278 (M = 257):")
    a = 0.278; step = 0.0005 if not FAST else 0.001
    Mb = 257 if not FAST else 129
    ring = cd.Ring(7, a, Mb); r0, Om, res, smin = ring.solve_steady()
    print(f"  a={a:.5f} res={res:.1e} smin={smin:.2e} gap/a={gap(ring, r0):.4f} Omega={Om:.8f}")
    for it in range(60 if not FAST else 6):
        a_new = a + step
        ring = cd.Ring(7, a_new, Mb)
        r, O, res, smin = ring.solve_steady(rho_guess=r0 * a_new / a, Om_guess=Om)
        ok = res < 1e-8 and np.all(r > 0)
        if ok:
            g = gap(ring, r)
            ok = g > 0
        if not ok:
            if step > 1e-5:
                step /= 4; continue
            print(f"  Newton fails beyond a={a:.6f} (res={res:.1e})"); break
        a, r0, Om = a_new, r, O
        print(f"  a={a:.5f} res={res:.1e} smin={smin:.2e} gap/a={g:.4f} Omega={Om:.8f} min(rho)/a={r0.min()/a:.4f} max(rho)/a={r0.max()/a:.4f}")
        sys.stdout.flush()
