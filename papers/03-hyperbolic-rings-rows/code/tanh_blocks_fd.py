# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# Changes: none
"""tanh Fourier blocks from a direct finite-difference Hessian of H (kernel G_1).

Independent recomputation (no archive code).  Points in the Poincare disk, z_j = sqrt(xi) e^{s_j} e^{i(2 pi j/N + theta_j)};
the two-point invariant is computed from the disk formula X = 1 + 2|z-w|^2/((1-|z|^2)(1-|w|^2)) and the kernel as
G_1(X) = 1/2 log((X+1)/(X-1)) (no chart identities used), J_3 = sum (X(z_j, 0) - 1).  Omega is fixed numerically by
d_{s_0} H = Omega d_{s_0} J_3 at the ring, then the 2N x 2N Hessian of F = H - Omega J_3 in (s, theta) is taken by
central differences.  Fourier blocks: (1/N) v_m^* Hess v_{m'}, v_m = (e^{2 pi i m j/N})_j, order (s, theta), so
M_m = [[aperp, i varpi], [-i varpi, apar]].
Predictions: the derived closed forms of tanh_common.py (equal to the havelock note's Theorem 2, checked symbolically in
tanh_threshold_polys.py) and A_0 Omega = -(N-1)/2 + xi/(1-xi) - N xi^N/(1-xi^N) (L1).
Also: theta-gradient and s-gradient of F vanish (L1), cross-mode blocks vanish, symmetries m <-> N-m, varpi_{N/2} = 0,
mode-0 tangential and s-theta entries vanish.
Precision: mp.dps = 90, Hessian step 1e-22 (truncation ~1e-44), gradient step 1e-30; target agreement < 1e-40.
Run: python tanh_blocks_fd.py   (deterministic)
"""
import os
import sys
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tanh_common import blocks_mp  # noqa: E402

mp.mp.dps = 90
H2 = mp.mpf('1e-22')
H1 = mp.mpf('1e-30')
NS = range(4, 13)
XIS = [mp.mpf(1) / 50, mp.mpf(1) / 7, mp.mpf(2) / 5, mp.mpf(3) / 4]


def X_pair(z, w):
    return 1 + 2 * abs(z - w)**2 / ((1 - abs(z)**2) * (1 - abs(w)**2))


def G1(X):
    return mp.log((X + 1) / (X - 1)) / 2


def pts(N, rho0, v):
    return [rho0 * mp.e**v[k] * mp.expjpi(2 * mp.mpf(k) / N + v[N + k] / mp.pi) for k in range(N)]


def H(N, rho0, v):
    p = pts(N, rho0, v)
    return mp.fsum(G1(X_pair(p[j], p[k])) for j in range(N) for k in range(j + 1, N))


def J3(N, rho0, v):
    return mp.fsum(X_pair(z, mp.mpc(0)) - 1 for z in pts(N, rho0, v))


def d1(f, dim, i):
    vp = [mp.mpf(0)] * dim; vm = [mp.mpf(0)] * dim
    vp[i] = H1; vm[i] = -H1
    return (f(vp) - f(vm)) / (2 * H1)


def hessian(f, dim):
    z = [mp.mpf(0)] * dim
    f0 = f(z)
    M = mp.matrix(dim, dim)
    for i in range(dim):
        vp = list(z); vm = list(z); vp[i] = H2; vm[i] = -H2
        M[i, i] = (f(vp) - 2 * f0 + f(vm)) / H2**2
        for j in range(i + 1, dim):
            s = []
            for (a, b) in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
                w = list(z); w[i] = a * H2; w[j] = b * H2
                s.append(a * b * f(w))
            M[i, j] = M[j, i] = mp.fsum(s) / (4 * H2**2)
    return M


def block(M, N, m, m2, off_r, off_c):
    tot = mp.mpc(0)
    for a in range(N):
        ca = mp.expjpi(-2 * mp.mpf(m * a) / N)
        for b in range(N):
            tot += ca * M[off_r + a, off_c + b] * mp.expjpi(2 * mp.mpf(m2 * b) / N)
    return tot / N


def main():
    print(__doc__.split('\n')[0])
    worst = dict(Omega=0, grad=0, aperp=0, apar=0, varpi=0, cross=0, sym=0)
    for N in NS:
        for xi in XIS:
            rho0 = mp.sqrt(xi)
            dim = 2 * N
            fH = lambda v: H(N, rho0, v)
            fJ = lambda v: J3(N, rho0, v)
            A0 = 4 * xi / (1 - xi)**2
            Om = d1(fH, dim, 0) / d1(fJ, dim, 0)
            _, _, _, AOm = blocks_mp(N, 1, xi)
            Om_pred = AOm / A0
            F = lambda v: fH(v) - Om * fJ(v)
            gres = max(abs(d1(F, dim, i)) for i in range(dim))
            M = hessian(F, dim)
            dA = dB = dV = dC = mp.mpf(0)
            rows = {}
            for m in range(N):
                for m2 in range(N):
                    Bss = block(M, N, m, m2, 0, 0)
                    Btt = block(M, N, m, m2, N, N)
                    Bst = block(M, N, m, m2, 0, N)
                    Bts = block(M, N, m, m2, N, 0)
                    if m != m2:
                        dC = max(dC, abs(Bss), abs(Btt), abs(Bst), abs(Bts))
                        continue
                    if m == 0:
                        # mode 0: aperp_0 is not part of note Thm 2; apar_0 = varpi_0 = 0
                        dB = max(dB, abs(Btt)); dV = max(dV, abs(Bst))
                        rows[0] = (Bss.real, None, Btt.real, 0, Bst, 0)
                        continue
                    ap, bp, vp, _ = blocks_mp(N, m, xi)
                    dA = max(dA, abs(Bss - ap)); dB = max(dB, abs(Btt - bp))
                    dV = max(dV, abs(Bst - 1j * vp), abs(Bts + 1j * vp))
                    rows[m] = (Bss.real, ap, Btt.real, bp, Bst, vp)
            dsym = max(max(abs(rows[m][0] - rows[N - m][0]), abs(rows[m][2] - rows[N - m][2]),
                           abs(rows[m][4] + rows[N - m][4])) for m in range(1, N))
            dOm = abs(Om - Om_pred)
            for k, v in (('Omega', dOm), ('grad', gres), ('aperp', dA), ('apar', dB), ('varpi', dV),
                         ('cross', dC), ('sym', dsym)):
                worst[k] = max(worst[k], v)
            X0 = (1 + xi) / (1 - xi)
            print(f"\nN={N}  xi={mp.nstr(xi, 8)}  X0=cosh r={mp.nstr(X0, 20)}  A0=X0^2-1={mp.nstr(A0, 20)}")
            print(f"  Omega_fd={mp.nstr(Om, 40)}  Omega_L1={mp.nstr(Om_pred, 40)}  |diff|={mp.nstr(dOm, 3)}  max|grad F|={mp.nstr(gres, 3)}")
            print(f"  mode 0: s-s entry (aperp_0, not in note Thm 2) = {mp.nstr(rows[0][0], 30)}  t-t = {mp.nstr(rows[0][2], 3)}  s-t = {mp.nstr(abs(rows[0][4]), 3)}")
            for m in range(1, N):
                a_fd, ap, b_fd, bp, st, vp = rows[m]
                print(f"  m={m:2d} aperp_fd={mp.nstr(a_fd, 42):>46s} aperp_T2={mp.nstr(ap, 22):>24s}"
                      f"  apar_fd={mp.nstr(b_fd, 30):>32s}  st_fd={mp.nstr(st.real, 3)}{'+' if st.imag >= 0 else '-'}{mp.nstr(abs(st.imag), 30)}i"
                      f"  varpi_T2={mp.nstr(vp, 22)}")
            print(f"  max|aperp-Thm2|={mp.nstr(dA, 3)} max|apar-Thm2|={mp.nstr(dB, 3)} max|st-i varpi|={mp.nstr(dV, 3)}"
                  f" max|cross-mode|={mp.nstr(dC, 3)} symmetry m<->N-m={mp.nstr(dsym, 3)}")
    print("\nWorst over N=4..12, xi in {1/50, 1/7, 2/5, 3/4}:")
    for k, v in worst.items():
        print(f"  {k:6s} {mp.nstr(v, 3)}")
    ok = all(v < mp.mpf('1e-40') for v in worst.values())
    print("PASS" if ok else "FAIL", "(all < 1e-40)")


if __name__ == '__main__':
    main()
