# Provenance: independent referee code, unmodified (session scratchpad referee2/ref_lagr.py, 2026-10-23). Only this header was added.
"""Nonlinear Lagrangian contour dynamics (referee), rotating frame W.  Start from the steady heptagon (ref_cd.steady),
displace patch centroids radially by delta*cos(2 pi m k/7) (m=3 slow mode), integrate with RK4, record m=3 Fourier
component of centroid radial / angular displacement."""
import numpy as np, sys, time
import ref_cd as R
from numpy.fft import fft, ifft, fftfreq

a = float(sys.argv[1]); M = int(sys.argv[2]); T = float(sys.argv[3]); dt = float(sys.argv[4]); delta = float(sys.argv[5])
N = 7
x, res, smin, C = R.steady(a, 65)
th65 = 2 * np.pi * np.arange(65) / 65
coef = x[:-1]; W = x[-1]
th = 2 * np.pi * np.arange(M) / M
rho = np.cos(np.outer(th, np.arange(len(coef)))) @ coef
zeta = np.exp(2j * np.pi * np.arange(N) / N)[:, None]
m = 3
Z = zeta * (1 + rho[None, :] * np.exp(1j * th)[None, :])
Z = Z + delta * zeta * np.cos(2 * np.pi * m * np.arange(N) / N)[:, None]
k = fftfreq(M, 1.0 / M)
w = 2.0 / a**2

def vel(Z):
    Za = ifft(1j * k * fft(Z, axis=-1), axis=-1)
    zf, zaf = Z.ravel(), Za.ravel()
    dz = zf[None, :] - zf[:, None]
    with np.errstate(divide='ignore', invalid='ignore'):
        K = np.conj(dz) / dz
    i = np.arange(zf.size); K[i, i] = np.conj(zaf) / zaf
    u = np.conj((w / (4 * np.pi)) * (K @ zaf) * (2 * np.pi / M)).reshape(Z.shape)
    return u - 1j * W * Z

def centroid(Z):
    Za = ifft(1j * k * fft(Z, axis=-1), axis=-1)
    # area = 1/2 Im oint conj z dz ; first moment: int z dA = (1/(4i)) oint ... use (1/2i)oint z conj z dz /... simpler:
    A = 0.5 * np.imag(np.sum(np.conj(Z) * Za, axis=-1)) * 2 * np.pi / M
    # int z dA = (1/(2i)) oint z * conj(z) dz /... Green: int f(z) dA = (1/2i) oint f(z) conj(z) dz for holomorphic f... use f=z: (1/(4i))*...
    mom = (1 / (2j)) * np.sum(Z * np.conj(Z) * Za, axis=-1) * 2 * np.pi / M / 2 * 2  # see check below
    return A, mom / A

A0, c0 = centroid(Z)
t0 = time.time()
nsteps = int(round(T / dt)); out = max(1, nsteps // 400)
print(f"a={a} M={M} W={W:.10f} dt={dt} delta={delta} area/pi a^2={A0/(np.pi*a**2)}", flush=True)
for n in range(nsteps + 1):
    if n % out == 0:
        A, c = centroid(Z)
        d = c / zeta[:, 0] - 1  # complex displacement in local frame: real=radial, imag=angular
        dr = np.sum(d.real * np.exp(-2j * np.pi * m * np.arange(N) / N)) / N
        dth = np.sum(d.imag * np.exp(-2j * np.pi * m * np.arange(N) / N)) / N
        # other modes
        allm = np.abs(fft(d.real))
        print(f"t={n*dt:9.3f} |dr3|={abs(dr):.4e} |dth3|={abs(dth):.4e} dr3={dr.real:+.4e}{dr.imag:+.4e}i "
              f"maxareaerr={np.max(np.abs(A/A0-1)):.1e} modes|dr|={' '.join('%.1e'%v for v in allm)}", flush=True)
    k1 = vel(Z); k2 = vel(Z + 0.5 * dt * k1); k3 = vel(Z + 0.5 * dt * k2); k4 = vel(Z + dt * k3)
    Z = Z + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
print("wall", time.time() - t0)
