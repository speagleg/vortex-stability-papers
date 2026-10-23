"""Region C of the single-threshold certificate (paper, Appendix E), with every estimate proved in the paper.
New code (replaces region C of single_root_cert.py, whose R-derivative bound was only described in its docstring).

Setting: hypercycle row, 0 < alpha <= pi/4, strip spacing l < 0.25, eta = pi*alpha/l. By the dual series
(Appendix D), F(pi) = F0 - R with R = R1 + R2 >= 0, where in the variables (alpha, eta), lam = 2*pi*eta/alpha,
  F0 = eta sinc(2a) coth(2 eta) - (eta^2/4) sinc(a)^2 coth(eta)^2 - (eta/pi) sin(2a) - cos(2a)/4,
  R1 = (2 eta/a) sum_n e^{-2n lam}/(1 - e^{-2n lam}) [sin 2a sinh(4 n eta) - 4 n eta sin^2 a / a],
  R2 = (2 eta^2 sin^2 a / a^2) sum_n n e^{-n lam}/(1 - e^{-n lam}) [1 + cosh(2 n eta)].
Bounds used (Appendix E, Lemma E.1), with s1 = e^{-2 lam + 4 eta}, s2 = e^{-lam + 2 eta}:
  (i)  R  <= 16 eta^2 s1/((1-s1)^2 (1-e^{-2 lam})) + 4 eta^2 s2/((1-s2)^2 (1-e^{-lam}))           (real eta > 0)
  (ii) |R(z)| <= 4|z|(1+2|z|) s1(x)/((1-s1(x))^2 (1-e^{-2 lam(x)})) + 4|z|^2 s2(x)/((1-s2(x))^2 (1-e^{-lam(x)}))
       for complex z, x = Re z > 0; hence |dR/deta| <= max of (ii) on the circle |z - eta| = 1 (Cauchy).
Regions: C1 eta >= 7 (analytic, Lemma E.2); C2 eta <= 2.5 (Lemma E.3, plus an Arb mean-value enclosure of h/eta^2);
C3 2.5 <= eta <= 7 (adaptive boxes; on each F0 - Rmax > 0, or F0 < 0, or dF0/deta + |dR/deta|max < 0).
Arb ball arithmetic (python-flint); no floating-point comparison decides a box.
Run: python region_C_cert.py
"""
import math
from flint import arb, ctx
ctx.prec = 120
PI = arb.pi()


def S_enc(x0, x1):
    """Enclosure of sinc on [x0, x1] within [0, pi] (sinc is decreasing there)."""
    v1 = arb(x1).sinc() if x1 > 0 else arb(1)
    v0 = arb(x0).sinc() if x0 > 0 else arb(1)
    return v1.union(v0)


def F0_dF0(A0, A1, E0, E1):
    al, eta = arb(A0).union(arb(A1)), arb(E0).union(arb(E1))
    S2, S1 = S_enc(2 * A0, 2 * A1), S_enc(A0, A1)
    c2, c1 = (2 * eta).coth(), eta.coth()
    F0 = eta * S2 * c2 - eta ** 2 / 4 * S1 ** 2 * c1 ** 2 - eta / PI * (2 * al).sin() - (2 * al).cos() / 4
    dF0 = (S2 * (c2 - 2 * eta / (2 * eta).sinh() ** 2) - S1 ** 2 / 4 * (2 * eta * c1 ** 2 - 2 * eta ** 2 * c1 / eta.sinh() ** 2)
           - (2 * al).sin() / PI)
    return F0, dF0


def R_real_bound(eta_hi, eta_lo, a_hi):
    """Bound (i) for all eta in [eta_lo, eta_hi], alpha in (0, a_hi]: prefactors at eta_hi, decay at eta_lo, a_hi."""
    eh, el, ah = arb(eta_hi), arb(eta_lo), arb(a_hi)
    lam = 2 * PI * el / ah
    s1 = (-2 * lam + 4 * el).exp(); s2 = (-lam + 2 * el).exp()
    assert s1 < 1 and s2 < 1
    return 16 * eh ** 2 * s1 / ((1 - s1) ** 2 * (1 - (-2 * lam).exp())) + 4 * eh ** 2 * s2 / ((1 - s2) ** 2 * (1 - (-lam).exp()))


def R_complex_bound(absz, x, a_hi):
    absz, x, ah = arb(absz), arb(x), arb(a_hi)
    lam = 2 * PI * x / ah
    s1 = (-2 * lam + 4 * x).exp(); s2 = (-lam + 2 * x).exp()
    assert s1 < 1 and s2 < 1
    return (4 * absz * (1 + 2 * absz) * s1 / ((1 - s1) ** 2 * (1 - (-2 * lam).exp()))
            + 4 * absz ** 2 * s2 / ((1 - s2) ** 2 * (1 - (-lam).exp())))


def region_C1():
    # eta >= 7, alpha <= pi/4: F <= F0 <= (pi sin a / l) coth(eta)^2 (1 - eta/(2 pi)) < 0 since 7 > 2 pi
    return arb(7) > 2 * PI and (2 * math.sqrt(2) / math.pi) / 4 >= 1 / (2 * math.pi)


def region_C2(lc=0.25, e1=2.5, d0=0.05):
    t = arb(lc) / PI

    def g(e):  # h(eta)/eta^2
        return -e.coth() ** 2 / 4 + (2 * e).coth() / e - 1 / (4 * e ** 2)

    def gp(e):
        return e.coth() / (2 * e.sinh() ** 2) - 2 / ((2 * e).sinh() ** 2 * e) - (2 * e).coth() / e ** 2 + 1 / (2 * e ** 3)

    def need(x1):
        return (2 * t * t / 3) * (arb(0.5) + x1) + 2 * t / PI

    # (0, d0]: h/eta^2 >= 1/2 - (37/180) eta^2 (Lemma E.3(b))
    worst = arb(0.5) - arb(37) / 180 * arb(d0) ** 2 - need(d0)
    stack = [(d0, e1)]; nbox = 0
    while stack:
        x0, x1 = stack.pop(); nbox += 1
        e = arb(x0).union(arb(x1)); m = arb((x0 + x1) / 2)
        lower = g(m) + gp(e) * (e - m) - need(x1)       # mean-value enclosure
        if lower > 0.02 or x1 - x0 < 1e-4:
            if lower.lower() < worst.lower():
                worst = lower
            continue
        stack += [(x0, (x0 + x1) / 2), ((x0 + x1) / 2, x1)]
    # R/eta^2 on the whole region: lam = 2 pi^2 / l >= 2 pi^2/lc, eta <= e1
    lam = 2 * PI ** 2 / arb(lc)
    s1 = (-2 * lam + 4 * arb(e1)).exp(); s2 = (-lam + 2 * arb(e1)).exp()
    Rc = 16 * s1 / ((1 - s1) ** 2 * (1 - (-2 * lam).exp())) + 4 * s2 / ((1 - s2) ** 2 * (1 - (-lam).exp()))
    return worst, Rc, nbox


def region_C3(lc=0.25, e0=2.5, e1=7.0, maxdepth=40):
    amax = 7 * lc / math.pi                        # eta <= 7 and l < 0.25 give alpha = eta l/pi < 7 lc/pi
    Rmax = R_real_bound(e1, e0, amax)
    dRmax = R_complex_bound(e1 + 1, e0 - 1, amax)   # Cauchy radius 1: |z| <= eta+1, Re z >= eta-1
    stack = [(0.0, amax, e0, e1, 0)]; nbox = nder = nneg = npos = 0
    while stack:
        A0, A1, E0, E1, d = stack.pop(); nbox += 1
        assert d < maxdepth
        F0, dF0 = F0_dF0(A0, A1, E0, E1)
        if F0 - Rmax > 0: npos += 1; continue
        if F0 < 0: nneg += 1; continue
        if dF0 + dRmax < 0: nder += 1; continue
        if (A1 - A0) * 8 > (E1 - E0):
            m = (A0 + A1) / 2; stack += [(A0, m, E0, E1, d + 1), (m, A1, E0, E1, d + 1)]
        else:
            m = (E0 + E1) / 2; stack += [(A0, A1, E0, m, d + 1), (A0, A1, m, E1, d + 1)]
    return nbox, npos, nneg, nder, Rmax, dRmax, amax


if __name__ == '__main__':
    print('C1 (eta >= 7, alpha <= pi/4): 7 > 2 pi and (2 sqrt2/pi)/4 >= 1/(2 pi):', region_C1())
    w, Rc, nb = region_C2()
    print(f'C2 (eta <= 2.5, l < 0.25): min of h/eta^2 - [(2t^2/3)(1/2+eta) + 2t/pi] >= {float(w.lower()):.4f} ({nb} intervals);'
          f' R/eta^2 <= {float(Rc.upper()):.2e}; margin positive: {bool(w - Rc > 0)}')
    nbox, npos, nneg, nder, Rmax, dRmax, amax = region_C3()
    print(f'C3 (2.5 <= eta <= 7, l < 0.25, alpha <= {amax:.4f}): {nbox} boxes: {npos} with F > 0, {nneg} with F < 0,'
          f' {nder} with dF/deta < 0;  R <= {float(Rmax.upper()):.2e}, |dR/deta| <= {float(dRmax.upper()):.2e}')
    print('all regions decided')
