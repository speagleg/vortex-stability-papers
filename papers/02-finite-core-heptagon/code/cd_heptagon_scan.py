"""The steady heptagon of uniform patches followed in the patch radius a (ring radius 1, normalised units):
spectrum of every Bloch block, onset of instability, the unstable eigenvalues, and the end of the branch.

Uses cd.py (complex-step Jacobian, Bloch blocks, area and rotation-Jordan quotients).  For each a we
report: Omega, Newton residual, the smallest singular value of the Newton matrix, the gap between
neighbouring patch boundaries in units of a, the largest real part over all blocks (and its block), the
slow m = 3 pair, and the size of the split rotation Jordan pair (diagnostic only).  Selected values of a
are repeated at a second resolution M.  Then the onset of instability is bisected at two resolutions.
"""
import sys
import numpy as np
import cd

FAST = '--fast' in sys.argv


def M_for(a):
    if a <= 0.205:
        return 65
    if a <= 0.255:
        return 129
    return 193


def gap(ring, r0):
    """min distance between the boundaries of patch 0 and patch 1, over a."""
    X0, _ = ring.geom(r0, 0)
    X1, _ = ring.geom(r0, 1)
    d = np.hypot(X0[0][:, None] - X1[0][None, :], X0[1][:, None] - X1[1][None, :])
    return d.min() / ring.a


def analyse(a, M, guess=None):
    S = cd.spectrum(7, a, M, rho_guess=guess[0] if guess else None, Om_guess=guess[1] if guess else None)
    worst = max(((b['ev'].real.max(), b['m']) for b in S['blocks']))
    ev3 = S['blocks'][3]['ev']
    i = np.argsort(abs(ev3))[:2]
    l1, l2 = sorted(ev3[i], key=lambda z: -z.imag)
    return S, worst, (l1, l2)


def line(a, M, S, worst, pair):
    l1, l2 = pair
    return (f"a={a:.5f} M={M:3d} Omega={S['Om']:.10f} res={S['res']:.1e} smin={S['smin']:.1e} "
            f"gap/a={gap(S['ring'], S['r0']):.4f} maxRe={worst[0]:+.3e} (m={worst[1]}) "
            f"slow3=({l1.real:+.1e}{l1.imag:+.8f}i, {l2.real:+.1e}{l2.imag:+.8f}i) "
            f"jordan={abs(S['blocks'][0]['jordan']).max():.1e}")


def resample(r0, Mnew):
    """trigonometric interpolation of r0 (odd length) onto Mnew (odd) nodes."""
    M = len(r0)
    c = np.fft.fft(r0) / M
    n = (M - 1) // 2
    cn = np.zeros(Mnew, complex)
    cn[:n + 1] = c[:n + 1]
    cn[-n:] = c[-n:]
    return np.real(np.fft.ifft(cn * Mnew))


if __name__ == '__main__':
    if FAST:
        grid = [0.05, 0.10, 0.15, 0.20, 0.25, 0.26, 0.262, 0.27]
    else:
        grid = ([0.02, 0.04, 0.06, 0.08, 0.10, 0.12, 0.14, 0.16, 0.18, 0.20, 0.21, 0.22, 0.23, 0.24, 0.25,
                 0.255, 0.258, 0.26, 0.2605, 0.261, 0.2615, 0.262, 0.265, 0.27, 0.272, 0.274, 0.276, 0.277, 0.278])
    check = {0.10: 129, 0.20: 129, 0.21: 129, 0.22: 129, 0.25: 193, 0.26: 257, 0.262: 257, 0.27: 257}
    print("Planar heptagon of uniform patches, ring radius 1, normalised units (Gamma = 1).")
    prev = None
    results = {}
    for a in grid:
        M = M_for(a)
        guess = None
        if prev is not None:
            r0p, Omp, ap = prev
            guess = (resample(r0p, M) * a / ap, Omp)
        try:
            S, worst, pair = analyse(a, M, guess)
        except Exception as ex:          # noqa
            print(f"a={a:.5f} M={M}: failed ({ex})"); break
        if S['res'] > 1e-8:
            print(f"a={a:.5f} M={M}: Newton did not converge (res={S['res']:.1e}); branch end reached"); break
        print(line(a, M, S, worst, pair)); sys.stdout.flush()
        results[a] = (S, worst)
        prev = (S['r0'], S['Om'], a)
        if a in check and not FAST:
            M2 = check[a]
            S2, worst2, pair2 = analyse(a, M2, (resample(S['r0'], M2), S['Om']))
            print("   resolution check: " + line(a, M2, S2, worst2, pair2)); sys.stdout.flush()

    # Onset of instability: bisection on maxRe > tol
    tol = 1e-7

    def unstable(a, M):
        S, worst, _ = analyse(a, M)
        return worst[0] > tol, S, worst

    for M in ([193, 257] if not FAST else [129]):
        lo, hi = 0.255, 0.265
        u, _, _ = unstable(lo, M); assert not u, "expected stable at lower bracket"
        u, _, _ = unstable(hi, M); assert u, "expected unstable at upper bracket"
        for _ in range(12 if not FAST else 6):
            mid = 0.5 * (lo + hi)
            u, S, worst = unstable(mid, M)
            if u:
                hi = mid
            else:
                lo = mid
        print(f"onset of instability (M={M}): a in [{lo:.6f}, {hi:.6f}]  (core radius over side "
              f"[{lo/(2*np.sin(np.pi/7)):.5f}, {hi/(2*np.sin(np.pi/7)):.5f}])")
        sys.stdout.flush()
        # unstable eigenvalues just above the onset, and the colliding pair just below
        for aa in (hi + 2e-4, lo - 2e-4, 0.27):
            S, worst, _ = analyse(aa, M)
            for b in S['blocks']:
                ev = b['ev']
                bad = ev[ev.real > tol]
                if len(bad):
                    print(f"   a={aa:.5f}: block m={b['m']}: eigenvalues with Re > {tol:g}: " +
                          ", ".join(f"{z.real:+.4e}{z.imag:+.6f}i" for z in bad))
            if aa == lo - 2e-4:
                # closest pair of eigenvalues on the imaginary axis within any block (the collision partners)
                best = None
                for b in S['blocks']:
                    im = np.sort(b['ev'].imag)
                    dd = np.diff(im)
                    k = np.argmin(dd)
                    if best is None or dd[k] < best[0]:
                        best = (dd[k], b['m'], im[k], im[k + 1])
                print(f"   a={aa:.5f} (stable side): closest pair on the imaginary axis: block m={best[1]}, "
                      f"Im = {best[2]:+.6f}, {best[3]:+.6f} (separation {best[0]:.2e})")
            sys.stdout.flush()
