# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# Changes: none
"""large-N constants of the tanh ring and the horocycle-row critical spacing.

Notation: tau = -(N/2) log xi, Lan(x) = coth x - 1/x,
8 ahat_inf(tau) = (4/tau) tanh(tau/2) - Lan(tau/2)^2.  With eta = tau/2 the zero condition is
  (coth eta - 1/eta)^2 = 2 tanh(eta)/eta,
and eta_inf = tau_inf/2, kappa_inf := tau_inf^{-1} (the limit of cosh r_*/N; the letter kappa is geodesic curvature in the
conventions, so this is tau_inf^{-1} there), ell_* = pi/eta_inf = 2 pi/tau_inf.
Steps:
 (a) eta_inf to 40 digits (mpmath findroot, dps 60), tau_inf, tau_inf^{-1}, ell_*, d ahat_inf/dtau at tau_inf;
     limits ahat_inf(0+) = 1/4, ahat_inf(inf) = -1/8, strict decrease and a single sign change on a grid (numerical);
 (b) the algebraic approximation eta ~ 2+sqrt3 (eta^2 - 4 eta + 1 = 0) and its errors;
 (c) the limit is the limit of the derived closed form: aperp_{floor(N/2)}(xi = e^{-2tau/N})/N^2 at N = 20000, 20001;
 (d) thresholds from the derived closed form for N = 100..801: cosh r_*/N -> tau_inf^{-1}, N (cosh r_* - N/tau_inf),
     ell_N = 2 pi sinh r_*/N -> ell_*, N^2 (ell_N - ell_*), N(1 - xi_*) -> 2 tau_inf, neighbour distance
     2 arsinh(sinh r_* sin(pi/N)) -> 2 arsinh(ell_*/2).
Run: python tanh_large_n.py   (deterministic)
"""
import os
import sys
import mpmath as mp
import flint

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tanh_common import blocks_mp  # noqa: E402

mp.mp.dps = 60


def Lan(t):
    return mp.coth(t) - 1 / t


def a_inf(tau):
    return ((4 / tau) * mp.tanh(tau / 2) - Lan(tau / 2)**2) / 8


def main():
    print(__doc__.split('\n')[0])
    # (a)
    eq = lambda e: Lan(e)**2 - 2 * mp.tanh(e) / e
    eta = mp.findroot(eq, mp.mpf('3.72'))
    tau = 2 * eta
    ell = mp.pi / eta
    der = mp.diff(a_inf, tau)
    print("(a) eta_inf      =", mp.nstr(eta, 40), "  residual", mp.nstr(eq(eta), 3))
    print("    tau_inf      =", mp.nstr(tau, 40), "  (claim 7.44533924494901868...)")
    print("    1/tau_inf    =", mp.nstr(1 / tau, 40), "  (claim 0.134312214272628139056...)")
    print("    ell_*        =", mp.nstr(ell, 40), "  (claim 0.8439085312925335 / 0.843908531292533...)")
    print("    d ahat_inf/dtau at tau_inf =", mp.nstr(der, 15), "  (claim -0.0153242426449);  d(8 ahat_inf)/dtau =", mp.nstr(8 * der, 15))
    print("    ahat_inf(1e-8) =", mp.nstr(a_inf(mp.mpf('1e-8')), 15), "(-> 1/4);  ahat_inf(200) =", mp.nstr(a_inf(mp.mpf(200)), 15), "(-> -1/8)")
    grid = [mp.mpf(k) / 100 for k in range(1, 20001)]  # tau in (0, 200]
    vals = [a_inf(t) for t in grid]
    dec = all(vals[i + 1] < vals[i] for i in range(len(vals) - 1))
    changes = sum(1 for i in range(len(vals) - 1) if vals[i] > 0 >= vals[i + 1])
    print(f"    grid tau = 0.01..200 (step 0.01): strictly decreasing {dec}; sign changes {changes}")
    assert abs(tau - mp.mpf('7.44533924494901868')) < mp.mpf('1e-17') and abs(1 / tau - mp.mpf('0.134312214272628139056')) < mp.mpf('1e-21')
    assert abs(ell - mp.mpf('0.8439085312925335')) < mp.mpf('1e-16') and abs(der - mp.mpf('-0.0153242426449')) < mp.mpf('1e-13')
    # (a') rigorous Arb certification (python-flint, 300 bits).  8 a_perp_inf(tau) at eta = tau/2 is 2 tanh(eta)/eta - Lan(eta)^2.
    flint.ctx.prec = 300
    def f8(e):
        e = flint.arb(e)
        return 2 * e.tanh() / e - (e.coth() - 1 / e)**2
    lo_s, hi_s = '3.72266962247450934355', '3.72266962247450934365'
    flo, fhi = f8(lo_s), f8(hi_s)
    assert flo > 0 and fhi < 0
    print(f"(a') Arb sign bracket for 8 a_perp_inf at eta = tau_inf/2 (prec 300): f({lo_s}) > 0: {flo > 0}; f({hi_s}) < 0: {fhi < 0}"
          f" -> tau_inf/2 in ({lo_s}, {hi_s}) (unique zero by strict decrease), tau_inf in (7.4453392449490186871, 7.4453392449490186873)")
    # archive P21: Phi(5) and Phi(10) (P21's Phi = a_perp_inf in tau, so Phi = f/8) and a rigorous bound on -Phi' on [5, 10]
    def Phi(t):
        t = flint.arb(t)
        return (4 / t * (t / 2).tanh() - ((t / 2).coth() - 2 / t)**2) / 8
    P5, P10 = Phi(5), Phi(10)
    assert P5 > 0 > P10
    print(f"    Arb: Phi(5) = {P5.mid().str(5, radius=False)} (> 0: {P5 > 0}), Phi(10) = {P10.mid().str(5, radius=False)} (< 0: {P10 < 0})")
    # -Phi'(t) on [5,10]: Arb enclosure of the derivative over the interval ball (interval arithmetic, rigorous)
    def dPhi(t):
        h = t / 2
        th, ch = h.tanh(), h.coth()
        d_tanh_term = -4 / (t * t) * th + 2 / t * (1 - th * th) / 1  # d/dt[(4/t) tanh(t/2)]
        L = ch - 2 / t
        dL = -(ch * ch - 1) / 2 + 2 / (t * t)                       # d/dt[coth(t/2) - 2/t]
        return (d_tanh_term - 2 * L * dL) / 8
    K = 1000  # K sub-intervals of [5,10], each an Arb ball; lower bound = min over subintervals of the lower end of -Phi'
    dmin = None
    for k in range(K):
        sub = flint.arb(5 + (2 * k + 1) * 5.0 / (2 * K), 5.0 / (2 * K))
        lb = (-dPhi(sub)).lower()
        dmin = lb if dmin is None or lb < dmin else dmin
    assert dmin > flint.arb('0.0089')
    print(f"    Arb interval enclosure, {K} sub-intervals of [5,10]: min(-Phi') > 0.0089 certified (computed lower bound {dmin.str(3, radius=False)}; archive 0.00898)")
    # (b)
    e0 = 2 + mp.sqrt(3)
    print(f"(b) 2+sqrt3 = {mp.nstr(e0, 12)}: eta_inf - (2+sqrt3) = {mp.nstr(eta - e0, 4)};"
          f" 1-sqrt3/2 - 1/tau_inf = {mp.nstr(1 - mp.sqrt(3) / 2 - 1 / tau, 4)}; pi(2-sqrt3) = {mp.nstr(mp.pi * (2 - mp.sqrt(3)), 6)}")
    # (c)
    print("(c) limit of the derived closed form, aperp_crit(xi = e^{-2tau/N})/N^2 - ahat_inf(tau):")
    for N in (20000, 20001):
        for t in (mp.mpf(1), mp.mpf(5), tau, mp.mpf(12)):
            ap = blocks_mp(N, N // 2, mp.e**(-2 * t / N))[0] / N**2
            print(f"    N={N} tau={mp.nstr(t, 8)}: {mp.nstr(ap, 15)} - {mp.nstr(a_inf(t), 15)} = {mp.nstr(ap - a_inf(t), 4)}")
    # (d)
    print("(d) thresholds from the closed form:")
    print("      N   xi_*                      cosh r_*/N        N(cosh r_* - N/tau_inf)  N^2(ell_N - ell_*)  N(1-xi_*)   neighbour d")
    for N in (100, 101, 200, 201, 400, 401, 800, 801):
        f = lambda t: blocks_mp(N, N // 2, mp.e**(-2 * t / N))[0]
        assert f(mp.mpf(5)) > 0 > f(mp.mpf(10))
        ts = mp.findroot(f, (mp.mpf(5), mp.mpf(10)), solver='anderson')
        xi = mp.e**(-2 * ts / N)
        X0 = (1 + xi) / (1 - xi)
        sh = mp.sqrt(X0**2 - 1)
        ellN = 2 * mp.pi * sh / N
        dnb = 2 * mp.asinh(sh * mp.sin(mp.pi / N))
        print(f"    {N:4d}  {mp.nstr(xi, 20):24s}  {mp.nstr(X0 / N, 12):16s}  {mp.nstr(N * (X0 - N / tau), 10):22s}"
              f"  {mp.nstr(N**2 * (ellN - ell), 8):18s}  {mp.nstr(N * (1 - xi), 8):10s}  {mp.nstr(dnb, 8)}")
    print(f"    limits: tau_inf^-1 = {mp.nstr(1 / tau, 12)}, 2 tau_inf = {mp.nstr(2 * tau, 8)}, 2 arsinh(ell_*/2) = {mp.nstr(2 * mp.asinh(ell / 2), 8)}")
    print("\nDONE (all assertions passed)")


if __name__ == '__main__':
    main()
