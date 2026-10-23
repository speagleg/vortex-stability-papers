"""Numerical checks of each step of the proof of the dual series (paper, Appendix D). New code.
(1) Lemma D.1: int_R e^{-i w x}/(cosh x - cos th) dx = 2 pi sinh((pi - th) w)/(sin th sinh(pi w)), 0 < th < 2 pi.
(2) Lemma D.2: S_th(l) = sum_{k>=1} 1/(cosh kl - cos th) = (pi coth(pi th/l) - th + E_th(l))/(l sin th) - 1/(2(1 - cos th)),
    E_th(l) = -4 pi sum_m Q^m sinh(2 pi th m/l)/(1 - Q^m), Q = e^{-4 pi^2/l}.
(3) Lemma D.3: F(pi) = (sin^2 2a/2) S_{2a}(l) - s [S_0(l) - S_0(2l)] + s [cos 2a S_{2a}(2l) + sin 2a dS_th(2l)/dth at th = 2a],
    s = sin^2 a, against the pair-function lattice sum.
(4) Theorem D.4: F(pi) = F^mod + R with the explicit R, against the lattice sum.
mpmath, 30 digits.
"""
from mpmath import mp, mpf, quad, cos, sin, sinh, cosh, coth, exp, pi, inf, diff, nstr

mp.dps = 30


def S_direct(th, l):
    tot = mpf(0); k = 1
    while True:
        t = 1 / (cosh(k * l) - cos(th)); tot += t; k += 1
        if t < mpf(10) ** -35: return tot


def E(th, l):
    Q = exp(-4 * pi ** 2 / l); tot = mpf(0); m = 1
    while True:
        t = Q ** m * sinh(2 * pi * th * m / l) / (1 - Q ** m); tot += t; m += 1
        if abs(t) < mpf(10) ** -40: return -4 * pi * tot


def S_dual(th, l):
    return (pi * coth(pi * th / l) - th + E(th, l)) / (l * sin(th)) - 1 / (2 * (1 - cos(th)))


def F_lattice(a, l):
    K = cos(a) ** 2; s = 1 - K; tot = mpf(0); j = 1
    while True:
        c = cosh(j * l); D = c + 1 - 2 * K
        b0 = s * ((3 * K - 1) * c ** 2 - (4 * K ** 2 - K + 1) * c + 2 * K ** 2) / ((c - 1) * D ** 2)
        b1 = s * (K * c ** 2 + (1 - 3 * K) * c + 2 * K ** 2 - 2 * K + 1) / ((c - 1) * D ** 2)
        t = b0 + (-1) ** j * b1; tot += t; j += 1
        if abs(t) < mpf(10) ** -40: return tot


def F_viaS(a, l):
    s = sin(a) ** 2
    S0 = lambda L: S_direct(0, L)
    dS = diff(lambda th: S_direct(th, 2 * l), 2 * a)
    return (sin(2 * a) ** 2 / 2) * S_direct(2 * a, l) - s * (S0(l) - S0(2 * l)) + s * (cos(2 * a) * S_direct(2 * a, 2 * l) + sin(2 * a) * dS)


def F_dual(a, l):
    s = sin(a) ** 2; qt = exp(-2 * pi ** 2 / l)
    Fmod = pi * sin(2 * a) / (2 * l) * coth(2 * pi * a / l) - pi ** 2 * s / (4 * l ** 2) * coth(pi * a / l) ** 2 - a * sin(2 * a) / l - cos(2 * a) / 4
    R1 = sum(qt ** (2 * n) / (1 - qt ** (2 * n)) * (sin(2 * a) * sinh(4 * pi * n * a / l) - 4 * pi * n * s / l) for n in range(1, 60))
    R2 = sum(n * qt ** n / (1 - qt ** n) * (1 + cosh(2 * pi * n * a / l)) for n in range(1, 60))
    return Fmod - 2 * pi / l * R1 - 2 * pi ** 2 * s / l ** 2 * R2


print('(1) Fourier transform of 1/(cosh x - cos th):')
for th, w in [(0.7, 0.3), (2.0, 1.5), (4.0, 0.9)]:
    th, w = mpf(th), mpf(w)
    num = 2 * quad(lambda x: cos(w * x) / (cosh(x) - cos(th)), [0, 5, 20, 60])
    cl = 2 * pi * sinh((pi - th) * w) / (sin(th) * sinh(pi * w))
    print(f'  th={float(th)}, w={float(w)}: quadrature {nstr(num, 20)}, closed form {nstr(cl, 20)}, diff {nstr(abs(num - cl), 3)}')
print('(2) S_th(l): direct sum vs dual form')
for th, l in [(0.4, 0.3), (1.2, 0.8), (2.5, 2.0), (0.9, 5.0)]:
    th, l = mpf(th), mpf(l)
    print(f'  th={float(th)}, l={float(l)}: diff {nstr(abs(S_direct(th, l) - S_dual(th, l)), 3)}')
print('    theta -> 0: S_0(l) - S_0(2l) vs pi^2/(4l^2) - 1/(2l) + E\'_0(l)/l - E\'_0(2l)/(2l)')
for l in [mpf('0.3'), mpf('1.1')]:
    lhs = S_direct(0, l) - S_direct(0, 2 * l)
    dE = lambda L: -8 * pi ** 2 / L * sum(m * exp(-4 * pi ** 2 * m / L) / (1 - exp(-4 * pi ** 2 * m / L)) for m in range(1, 80))
    rhs = pi ** 2 / (4 * l ** 2) - 1 / (2 * l) + dE(l) / l - dE(2 * l) / (2 * l)
    print(f'  l={float(l)}: diff {nstr(abs(lhs - rhs), 3)}')
print('(3) F(pi) via S functions vs pair-function lattice sum; (4) dual series vs lattice sum')
for a, l in [(0.3, 0.2), (0.6, 0.9), (0.785, 1.4), (1.2, 0.5), (0.1, 0.05)]:
    a, l = mpf(a), mpf(l)
    FL = F_lattice(a, l)
    print(f'  alpha={float(a)}, l={float(l)}: F={nstr(FL, 15)}  |viaS - F| {nstr(abs(F_viaS(a, l) - FL), 3)}  |dual - F| {nstr(abs(F_dual(a, l) - FL), 3)}')
