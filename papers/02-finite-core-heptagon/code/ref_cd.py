# Provenance: independent referee code, unmodified (session scratchpad referee2/ref_cd.py, 2026-10-23). Only this header was added.
"""Referee's independent contour dynamics for N uniform patches on a ring.
Velocity: conj(u+iv)(z) = (w/4pi) sum_l oint_l (conj z' - conj z)/(z' - z) dz'   (Cauchy form; trapezoid, diagonal filled
with conj(z_a)/z_a).  Units: each patch circulation 2*pi (book Gamma=1), vorticity w = 2/r^2.
Patch k: z = zeta^k (1 + rho_k(th) e^{i th}) ... i.e. centre c_k = zeta^k, local angle rotated with the patch.
Rotating frame angular velocity W (counterclockwise).  rho_t = u_r - u_th rho'/rho.
Jacobian by central finite differences (not complex step), Bloch blocks by hand.
"""
import numpy as np, sys
from numpy.fft import fft, ifft, fftfreq

N = 7

def deriv(f):
    M = f.shape[-1]
    k = fftfreq(M, 1.0 / M)
    return np.real(ifft(1j * k * fft(f, axis=-1), axis=-1))

def geometry(rho):  # rho: (N, M)
    Np, M = rho.shape
    th = 2 * np.pi * np.arange(M) / M
    zeta = np.exp(2j * np.pi * np.arange(Np) / Np)[:, None]
    e = np.exp(1j * th)[None, :]
    rp = deriv(rho)
    z = zeta * (1 + rho * e)
    za = zeta * (rp + 1j * rho) * e
    return z, za, th

def velocity(rho, r):
    Np, M = rho.shape
    w = 2.0 / r**2
    z, za, th = geometry(rho)
    zf, zaf = z.ravel(), za.ravel()
    dz = zf[None, :] - zf[:, None]  # source - target
    with np.errstate(divide='ignore', invalid='ignore'):
        K = np.conj(dz) / dz
    idx = np.arange(Np * M)
    K[idx, idx] = np.conj(zaf) / zaf
    wbar = (w / (4 * np.pi)) * (K @ zaf) * (2 * np.pi / M)
    return np.conj(wbar).reshape(Np, M), z

def rhs(rho, r, W):
    Np, M = rho.shape
    u, z = velocity(rho, r)
    zeta = np.exp(2j * np.pi * np.arange(Np) / Np)[:, None]
    V = u - 1j * W * z
    th = 2 * np.pi * np.arange(M) / M
    loc = V * np.conj(zeta) * np.exp(-1j * th)[None, :]
    ur, ut = loc.real, loc.imag
    return ur - ut * deriv(rho) / rho

def area_centroid(rho):
    M = rho.shape[-1]
    th = 2 * np.pi * np.arange(M) / M
    A = 0.5 * np.mean(rho**2, axis=-1) * 2 * np.pi
    # centroid offset relative to centre: (1/A) * int rho^3/3 e^{i th} dth
    cx = (np.mean(rho**3 * np.exp(1j * th), axis=-1) * 2 * np.pi / 3) / A
    return A, cx

def steady(r, M, guess=None, W0=3.0, tol=1e-13, verbose=False):
    K = (M - 1) // 2
    th = 2 * np.pi * np.arange(M) / M
    C = np.cos(np.outer(th, np.arange(K + 1)))  # M x (K+1)
    if guess is None:
        x = np.zeros(K + 2); x[0] = r; x[-1] = W0
    else:
        x = guess.copy()
    def F(x):
        rho0 = C @ x[:-1]
        rho = np.tile(rho0, (N, 1))
        f = rhs(rho[:, :], r, x[-1])[0]
        A, cx = area_centroid(rho0[None, :])
        # f is odd (reflection reverses time); project onto sines
        S = np.sin(np.outer(th, np.arange(1, K + 1)))
        fc = S.T @ f / M
        # centroid of patch 0 at distance 1 from origin: 1 + Re cx = 1
        return np.concatenate([fc / r, [A[0] / (np.pi * r**2) - 1, cx[0].real / r]])
    for it in range(40):
        f = F(x)
        nf = np.linalg.norm(f)
        if verbose: print(it, nf)
        h = 1e-7 * r
        Jm = np.empty((len(f), len(x)))
        for j in range(len(x)):
            e = np.zeros_like(x); e[j] = h if j < len(x) - 1 else 1e-7
            Jm[:, j] = (F(x + e) - F(x - e)) / (2 * e[j])
        dx = np.linalg.lstsq(Jm, -f, rcond=None)[0]
        x = x + dx
        if nf < tol: break
    sv = np.linalg.svd(Jm, compute_uv=False)
    return x, np.linalg.norm(F(x)), sv[-1], C

def bloch_blocks(rho0, r, W, h=None):
    M = rho0.size
    rho = np.tile(rho0, (N, 1))
    if h is None: h = 1e-4 * r
    cols = np.empty((N, M, M))
    for j in range(M):
        fs = []
        for c in (2, 1, -1, -2):
            p = rho.copy(); p[0, j] += c * h
            fs.append(rhs(p, r, W))
        cols[:, :, j] = (-fs[0] + 8 * fs[1] - 8 * fs[2] + fs[3]) / (12 * h)
    zeta = np.exp(2j * np.pi / N)
    l = rho0 / np.linalg.norm(rho0)
    Q = np.linalg.svd(np.eye(M) - np.outer(l, l))[0][:, :M - 1]
    return [Q.T @ sum(cols[d] * zeta**(-m * d) for d in range(N)) @ Q for m in range(N)]

if __name__ == "__main__":
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 65
    alist = [float(a) for a in sys.argv[2:]] or [0.05, 0.1, 0.15, 0.2, 0.25]
    x = None
    for a in alist:
        x, res, smin, C = steady(a, M, guess=None if x is None else x * np.r_[np.full(len(x) - 1, a / prev), 1])
        prev = a
        rho0 = C @ x[:-1]
        W = x[-1]
        Bs = bloch_blocks(rho0, a, W, h=float(__import__('os').environ.get('HREL','1e-4'))*a)
        maxre = []
        for m, B in enumerate(Bs):
            ev = np.linalg.eigvals(B)
            nz = ev[np.abs(ev) > 1e-4] if m == 0 else ev
            maxre.append(np.max(nz.real))
        ev3 = np.linalg.eigvals(Bs[3])
        # slow pair: the two eigenvalues with smallest |lam| apart from the area zero
        srt = ev3[np.argsort(np.abs(ev3))]
        cand = list(srt[:2])
        l1, l2 = cand
        s3 = ((l1 - l2) / 2)**2
        vp = (1j / 2 * (l1 + l2))
        print(f"a={a:.4f} M={M} W={W:.10f} (W-3)/a^4={(W-3)/a**4:.4f} res={res:.1e} smin={smin:.1e} "
              f"maxRe per block={['%.1e' % v for v in maxre]} slow3={l1:.6e},{l2:.6e} "
              f"s3/a^4={s3.real/a**4:.4f} varpi/a^4={abs(vp.real)/a**4:.4f}", flush=True)
