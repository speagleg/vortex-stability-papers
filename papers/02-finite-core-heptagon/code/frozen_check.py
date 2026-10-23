"""Section 7, item (ii): the decomposition of d_perp for the heptagon (N = 7, m = 3), and what a model that
does not slave the ellipses would give.

Slaved (adiabatic) ellipses:  H_eff = H + (r^4/4) sum_k |M_k|^2           -> d_perp = (L+^2 + L-^2)/4 + mu kappa + 2 mu^2
Frozen ellipses (shape fixed at its equilibrium value eps_k = r^2 conj(M_k^0), not responding to the perturbation):
                              H_fr  = H + (r^4/2) sum_k Re(M_k conj(M_k^0)) -> the |L|^2 term is absent: d_perp = mu kappa + 2 mu^2
Both models have the same first variation, hence the same Omega_1.  We evaluate both by direct 40-digit finite
differences of the Hamiltonians (no lattice sums), and print the lattice-sum pieces from tsums.py.
"""
import mpmath as mp
import tsums

mp.mp.dps = 40
N, m = 7, 3
zeta = mp.exp(2j * mp.pi / N)


def zs(x):
    return [zeta**k * mp.exp(x[2 * k] + 1j * x[2 * k + 1]) for k in range(N)]


def Mk(z, k):
    return sum(1 / (z[k] - z[l])**2 for l in range(N) if l != k)


M0 = [Mk(zs([mp.mpf(0)] * (2 * N)), k) for k in range(N)]


def H(x):
    z = zs(x)
    return -sum(mp.log(abs(z[j] - z[k])) for j in range(N) for k in range(j + 1, N))


def Phi_slaved(x):
    z = zs(x)
    return sum(abs(Mk(z, k))**2 for k in range(N)) / 4


def Phi_frozen(x):
    z = zs(x)
    return sum(mp.re(Mk(z, k) * mp.conj(M0[k])) for k in range(N)) / 2


def J(x):
    return sum(abs(w)**2 for w in zs(x)) / 2


h = mp.mpf('1e-12')


def d2(f, i, j):
    def ev(a, b):
        x = [mp.mpf(0)] * (2 * N); x[i] += a; x[j] += b; return f(x)
    return (ev(h, h) - ev(h, -h) - ev(-h, h) + ev(-h, -h)) / (4 * h * h)


def d1(f, i):
    x = [mp.mpf(0)] * (2 * N); xp = list(x); xm = list(x); xp[i] += h; xm[i] -= h
    return (f(xp) - f(xm)) / (2 * h)


def aperp_eps(Phi):
    Om1 = d1(Phi, 0) / d1(J, 0)
    G = lambda x: Phi(x) - Om1 * J(x)
    ss = sum(d2(G, 0, 2 * j) * zeta**(m * j) for j in range(N))
    tt = sum(d2(G, 1, 2 * j + 1) * zeta**(m * j) for j in range(N))
    return Om1, mp.re(ss), mp.re(tt)


if __name__ == '__main__':
    T = lambda a, n: float(tsums.T_exact(a, n, N))
    mu = T(2, 0)
    Lp = -2 * (T(3, 0) - T(3, m + 1)); Lm = -2 * (T(3, 0) - T(3, 1 - m))
    kap = -T(2, 0) + 3 * (T(4, 0) - T(4, 1 - m) - T(4, 1 + m) + T(4, 2))
    print(f"lattice sums (N=7, m=3): mu = {mu}, Lambda+ = {Lp}, Lambda- = {Lm}, kappa = {kap}")
    print(f"  slaved: d_perp = (L+^2+L-^2)/4 + mu*kappa + 2 mu^2 = {(Lp**2+Lm**2)/4} + {mu*kap} + {2*mu**2} = {(Lp**2+Lm**2)/4 + mu*kap + 2*mu**2}")
    print(f"          d_par  = (L+^2+L-^2)/4 - mu*kappa = {(Lp**2+Lm**2)/4 - mu*kap}")
    print(f"  frozen: d_perp = mu*kappa + 2 mu^2 = {mu*kap + 2*mu**2},  d_par = -mu*kappa = {-mu*kap}")
    for name, Phi in (('slaved', Phi_slaved), ('frozen', Phi_frozen)):
        Om1, dp, dq = aperp_eps(Phi)
        print(f"direct finite differences, {name}: Omega_1 = {mp.nstr(Om1, 15)}, d_perp = {mp.nstr(dp, 15)}, d_par = {mp.nstr(dq, 15)}")
    print("Heptagon slow block with frozen ellipses: a_perp a_par = (-20 eps)(6 + 22 eps) < 0 -> unstable (Lemma 2.1).")
