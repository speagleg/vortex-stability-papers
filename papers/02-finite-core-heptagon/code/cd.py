"""Contour dynamics for a ring of N equal uniform vortex patches in the plane: steady states and the
linear spectrum, by Bloch (Fourier-in-patch-index) blocks and a complex-step Jacobian.

Written for this paper.  It follows the design of the reviewer's code ngon.py (polar-graph boundaries,
spectral differentiation, Kress quadrature for the logarithmic self-interaction, Newton solve for the
steady ring, Jacobian eigenvalues), with three changes that remove the round-off problems of a
finite-difference Jacobian:
  * the Jacobian is computed by the complex-step method (exact to round-off: no subtractive cancellation);
  * the ring's cyclic symmetry is used: only the M columns belonging to patch 0 are computed, and the
    spectrum is that of the N Bloch blocks B_m = sum_d J_{d,0} zeta^{-m d} (M x M each);
  * the conserved patch area is projected out: in each block the area functional l(x) = int rho_0 x dtheta
    is a left null vector of the exact linearisation, and we restrict B_m to its kernel by an
    orthogonal projection; the discarded eigenvalue is the (neutral) area mode.

Units: normalised units.  Each patch has circulation Gamma = 1 in the point-vortex normalisation
H = -sum log|z_j - z_k|, i.e. physical circulation 2 pi, so the vorticity is q = 2/a^2 (a = patch radius).
Ring radius R = 1.  The point-vortex ring rotates at Omega = (N-1)/2.
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "4"); os.environ.setdefault("OPENBLAS_NUM_THREADS", "4")
import numpy as np

TWO_PI = 2 * np.pi


class Ring:
    def __init__(self, N, a, M, R=1.0):
        self.N, self.a, self.M, self.R = N, a, M, R
        self.q = 2.0 / a**2                        # vorticity, circulation 1
        th = TWO_PI * np.arange(M) / M
        self.th = th
        k = np.fft.fftfreq(M, 1.0 / M)
        # real spectral differentiation matrix (Nyquist mode dropped)
        Dm = np.zeros((M, M))
        I = np.eye(M)
        assert M % 2 == 1, "use an odd number of nodes (no Nyquist mode)"
        for j in range(M):
            fh = np.fft.fft(I[:, j])
            Dm[:, j] = np.real(np.fft.ifft(1j * k * fh))
        self.D = Dm
        d = th[:, None] - th[None, :]
        n = (M - 1) // 2
        # Kress-type weights for odd M (exact for trigonometric polynomials of degree <= n):
        # int_0^{2pi} log(4 sin^2((t_i - s)/2)) f(s) ds ~ sum_j Wk[i, j] f_j
        self.Wk = -(2 * TWO_PI / M) * sum(np.cos(mm * d) / mm for mm in range(1, n + 1))
        self.s2 = 4 * np.sin(d / 2)**2
        np.fill_diagonal(self.s2, 1.0)
        self.phis = TWO_PI * np.arange(N) / N
        self.cent = np.array([[R * np.cos(p), R * np.sin(p)] for p in self.phis])
        self.cosang = [np.cos(th + p) for p in self.phis]
        self.sinang = [np.sin(th + p) for p in self.phis]

    def geom(self, rho, p):
        """rho: (..., M) boundary radius of patch p; returns X (..., 2, M), dX/dtheta (..., 2, M)."""
        c, s = self.cosang[p], self.sinang[p]
        rp = rho @ self.D.T
        X = np.stack([self.cent[p][0] + rho * c, self.cent[p][1] + rho * s], axis=-2)
        DX = np.stack([rp * c - rho * s, rp * s + rho * c], axis=-2)
        return X, DX

    def vel_pair(self, Xt, Xs, DXs):
        """velocity at targets Xt (..., 2, M) induced by a different patch with boundary Xs, DXs."""
        dx = Xt[..., 0, :, None] - Xs[..., 0, None, :]
        dy = Xt[..., 1, :, None] - Xs[..., 1, None, :]
        L = 0.5 * np.log(dx * dx + dy * dy) * (TWO_PI / self.M)
        u = np.einsum('...ij,...j->...i', L, DXs[..., 0, :])
        v = np.einsum('...ij,...j->...i', L, DXs[..., 1, :])
        return -self.q / TWO_PI * np.stack([u, v], axis=-2)

    def vel_self(self, X, DX):
        dx = X[..., 0, :, None] - X[..., 0, None, :]
        dy = X[..., 1, :, None] - X[..., 1, None, :]
        sm = 0.5 * np.log((dx * dx + dy * dy + np.eye(self.M)) / self.s2)   # diagonal replaced below
        sp_ = np.sqrt(DX[..., 0, :]**2 + DX[..., 1, :]**2)
        idx = np.arange(self.M)
        sm[..., idx, idx] = np.log(sp_)
        Ls = sm * (TWO_PI / self.M) + 0.5 * self.Wk
        u = np.einsum('...ij,...j->...i', Ls, DX[..., 0, :])
        v = np.einsum('...ij,...j->...i', Ls, DX[..., 1, :])
        return -self.q / TWO_PI * np.stack([u, v], axis=-2)

    def normal_rate(self, rho_p, U, X, p, Om):
        """d rho_p/dt in the frame rotating at Omega (counter-clockwise rotation rate Om)."""
        ux = U[..., 0, :] + Om * X[..., 1, :]
        uy = U[..., 1, :] - Om * X[..., 0, :]
        c, s = self.cosang[p], self.sinang[p]
        ur = ux * c + uy * s
        ut = -ux * s + uy * c
        return ur - ut / rho_p * (rho_p @ self.D.T)

    def rhs_all(self, rhos, Om):
        """rhos: (N, M) -> d rho/dt (N, M)."""
        G = [self.geom(rhos[p], p) for p in range(self.N)]
        out = []
        for p in range(self.N):
            U = self.vel_self(*G[p])
            for l in range(self.N):
                if l != p:
                    U = U + self.vel_pair(G[p][0], G[l][0], G[l][1])
            out.append(self.normal_rate(rhos[p], U, G[p][0], p, Om))
        return np.array(out)

    # ---------- steady state ----------
    def solve_steady(self, rho_guess=None, Om_guess=None, tol=1e-14, maxit=40, verbose=False):
        """Newton for an even (reflection-symmetric) identical-patch ring: unknowns cos-coefficients of
        rho_0 and Omega; equations: d rho_0/dt = 0 (patch 0), area = pi a^2, and the centroid of patch 0
        at distance R from the ring centre (this fixes the scale of the one-parameter family of rings)."""
        M = self.M
        nc = (M + 1) // 2
        C = np.array([np.cos(m * self.th) for m in range(nc)]).T      # M x nc
        if rho_guess is None:
            cs = np.zeros(nc); cs[0] = self.a
        else:
            cs = np.linalg.lstsq(C, rho_guess, rcond=None)[0]
        Om = (self.N - 1) / 2 / self.R**2 if Om_guess is None else Om_guess
        v = np.concatenate([cs, [Om]])

        def res(v):
            """v: (..., nc+1) -> residual (..., M+2); works with complex v for the complex step."""
            r = v[..., :-1] @ C.T
            rhos = np.stack([r] * self.N, axis=-2)
            o = self.rhs_patch0(rhos, v[..., -1:])
            area = 0.5 * np.mean(r**2, axis=-1) * TWO_PI
            # pin the vorticity centroid of patch 0 at distance R from the ring centre
            cx = np.mean(r**3 / 3 * np.cos(self.th), axis=-1) * TWO_PI
            return np.concatenate([o, (area - np.pi * self.a**2)[..., None], cx[..., None]], axis=-1)

        hh = 1e-30
        prev = np.inf
        for it in range(maxit):
            f = res(v)
            nf = np.linalg.norm(f)
            if verbose:
                print('   newton', it, nf)
            Vb = np.tile(v.astype(complex), (len(v), 1)) + 1j * hh * np.eye(len(v))
            Jn = (np.imag(res(Vb)) / hh).T
            if nf < tol or (nf < 1e-9 and nf > 0.3 * prev):
                break
            prev = nf
            dv, *_ = np.linalg.lstsq(Jn, -f, rcond=1e-14)
            v = v + dv
        r = C @ v[:-1]
        sv = np.linalg.svd(Jn, compute_uv=False)
        return r, v[-1], np.linalg.norm(res(v)), sv[-1]

    def rhs_patch0(self, rhos, Om):
        """rhos: (..., N, M); returns d rho_0/dt (..., M)."""
        G = [self.geom(rhos[..., p, :], p) for p in range(self.N)]
        U = self.vel_self(*G[0])
        for l in range(1, self.N):
            U = U + self.vel_pair(G[0][0], G[l][0], G[l][1])
        return self.normal_rate(rhos[..., 0, :], U, G[0][0], 0, Om)

    # ---------- linearisation ----------
    def jacobian_columns(self, r0, Om, batch=32):
        """J_{l,0} (N x M x M): derivative of d rho_l/dt with respect to rho_0, by complex step."""
        N, M = self.N, self.M
        hh = 1e-30
        Jc = np.zeros((N, M, M))
        G0 = [self.geom(r0, p) for p in range(N)]
        # velocity contributions not involving patch 0 (unchanged by the perturbation)
        Ubase = []
        for p in range(N):
            U = np.zeros((2, M))
            if p != 0:
                U = self.vel_self(*G0[p])
                for l in range(1, N):
                    if l != p:
                        U = U + self.vel_pair(G0[p][0], G0[l][0], G0[l][1])
            Ubase.append(U)
        for j0 in range(0, M, batch):
            js = np.arange(j0, min(M, j0 + batch))
            B = len(js)
            rp = np.tile(r0.astype(complex), (B, 1))
            rp[np.arange(B), js] += 1j * hh
            X0, DX0 = self.geom(rp, 0)
            # patch 0: self + all others
            U0 = self.vel_self(X0, DX0)
            for l in range(1, N):
                U0 = U0 + self.vel_pair(X0, G0[l][0][None], G0[l][1][None])
            Jc[0][:, js] = (np.imag(self.normal_rate(rp, U0, X0, 0, Om)) / hh).T
            for p in range(1, N):
                Up = Ubase[p][None] + self.vel_pair(np.broadcast_to(G0[p][0], (B, 2, M)), X0, DX0)
                rr = np.broadcast_to(r0, (B, M))
                Jc[p][:, js] = (np.imag(self.normal_rate(rr, Up, G0[p][0][None], p, Om)) / hh).T
        return Jc

    def bloch_blocks(self, Jc):
        N = self.N
        z = np.exp(2j * np.pi / N)
        return [sum(Jc[d] * z**(-m * d) for d in range(N)) for m in range(N)]

    def centroid_radius(self, r0):
        """distance from the ring centre to the vorticity centroid of patch 0 (spectral quadrature)."""
        th = self.th
        # centroid relative to the nominal centre: (1/A) int (rho^3/3) (cos, sin) dtheta
        A = 0.5 * np.mean(r0**2) * TWO_PI
        cx = np.mean(r0**3 / 3 * np.cos(th)) * TWO_PI / A
        return self.R + cx

    def area_projector(self, r0):
        """orthonormal basis Q (M x (M-1)) of the kernel of the area functional l = rho_0 (trapezoid)."""
        l = r0 / np.linalg.norm(r0)
        Qf, _ = np.linalg.qr(np.column_stack([l, np.eye(self.M)[:, :-1]]))
        return Qf[:, 1:], l


def rotation_vector(ring, r0):
    """Bloch m = 0 vector of an infinitesimal rigid rotation of the whole ring (per unit angle):
    each patch is translated tangentially by R and its shape rotated about its centre."""
    rp = r0 @ ring.D.T
    th = ring.th
    return ring.R * np.sin(th) - ring.R * np.cos(th) * rp / r0 - rp


def spectrum(N, a, M, project=True, steady=None, verbose=False, rho_guess=None, Om_guess=None):
    """Steady ring and the eigenvalues of every Bloch block.
    With project=True: blocks restricted to the area-preserving subspace (exactly invariant: the area
    functional is a left null vector), and in block m = 0 the 2-dimensional invariant Jordan subspace of the
    rotation symmetry (rotation and its partner, a change of ring size) is also factored out.
    Also returned: 'leak' = |l B|/|B| (should be round-off), 'rot_res' = |B v_rot|/|B||v_rot| (m = 0),
    and 'jordan' = the two smallest eigenvalues of the m = 0 block before factoring out (the split
    Jordan pair: its size measures the floating-point perturbation of a 2x2 nilpotent block)."""
    ring = Ring(N, a, M)
    if steady is None:
        r0, Om, res, smin = ring.solve_steady(verbose=verbose, rho_guess=rho_guess, Om_guess=Om_guess)
    else:
        r0, Om = steady
        res = smin = np.nan
    Jc = ring.jacobian_columns(r0, Om)
    Bs = ring.bloch_blocks(Jc)
    Q, l = ring.area_projector(r0)
    out = []
    for m, B in enumerate(Bs):
        nB = np.linalg.norm(B)
        leak = np.linalg.norm(l @ B) / nB
        info = dict(m=m, leak=leak)
        if not project:
            info['ev'] = np.linalg.eigvals(B)
        else:
            Br = Q.T @ B @ Q
            if m == 0:
                ev0 = np.linalg.eigvals(Br)
                info['jordan'] = ev0[np.argsort(abs(ev0))[:2]]
                vr = Q.T @ rotation_vector(ring, r0)
                info['rot_res'] = np.linalg.norm(Br @ vr) / (np.linalg.norm(Br) * np.linalg.norm(vr))
                w = np.linalg.lstsq(Br, vr, rcond=1e-12)[0]
                V, _ = np.linalg.qr(np.column_stack([vr, w]))
                full, _ = np.linalg.qr(np.column_stack([V, np.eye(Br.shape[0])]))
                P = full[:, 2:]                     # orthonormal complement of the Jordan subspace
                info['ev'] = np.linalg.eigvals(P.T @ Br @ P)
            else:
                info['ev'] = np.linalg.eigvals(Br)
        out.append(info)
    return dict(r0=r0, Om=Om, res=res, smin=smin, blocks=out, ring=ring)
