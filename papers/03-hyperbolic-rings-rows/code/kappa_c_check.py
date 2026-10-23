"""Checks for the hypercycle-row statements formalised in lean/HyperbolicRings/Rows (new code).

(1) sympy: the pair-function identities B0 - B1 = s*g_o, B0 + B1 = s*g_e (s = 1 - K), the positivity form
    of the numerator of B1, and the two comparison identities with K = 1/2 used for the pairing bound.
(2) the pair-function sum F(q) = sum_j [B0(c_j) + B1(c_j) cos qj] agrees with the one-variable series
    F(pi) of the paper (eq. (6.4)) at sample points (mpmath, 30 digits).
(3) the elementary bound chain behind `pairing_instability`:
    F(pi)/s <= -1/((c1-1)c1) + 2 e^{-2l}/(1 - e^{-l}) < 0 for K <= 1/2, on a grid (floating point check of
    a statement proved in the paper and in Lean).
"""
import sympy as sp
import mpmath as mp

K, c, t = sp.symbols('K c t', real=True)
s = 1 - K
D = c + 1 - 2 * K
B0 = s * ((3 * K - 1) * c**2 - (4 * K**2 - K + 1) * c + 2 * K**2) / ((c - 1) * D**2)
B1 = s * (K * c**2 + (1 - 3 * K) * c + 2 * K**2 - 2 * K + 1) / ((c - 1) * D**2)
go = ((2 * K - 1) * c - 1) / ((c - 1) * D)
ge = ((4 * K - 1) * c - (4 * K**2 - 2 * K + 1)) / D**2
print('(1) B0 - B1 - s*g_o =', sp.simplify(B0 - B1 - s * go))
print('    B0 + B1 - s*g_e =', sp.simplify(B0 + B1 - s * ge))
num1 = K * c**2 + (1 - 3 * K) * c + 2 * K**2 - 2 * K + 1
print('    numerator(B1) - [K t^2 + (1-K) t + 2(1-K)^2] at c = 1 + t:',
      sp.expand(num1.subs(c, 1 + t) - (K * t**2 + (1 - K) * t + 2 * (1 - K)**2)))
T = sp.symbols('T', real=True)  # T = 1 - 2K
geT = sp.simplify(ge.subs(K, (1 - T) / 2))
diff = sp.factor(sp.simplify((c - 1) / c**2 - geT))
print('    (c-1)/c^2 - g_e  =', diff)
goT = sp.simplify(go.subs(K, (1 - T) / 2))
print('    -1/((c-1)c) - g_o =', sp.factor(sp.simplify(-1 / ((c - 1) * c) - goT)))

mp.mp.dps = 30


def F_pairs(Kv, lu, q, jmax=4000):
    tot = mp.mpf(0)
    for j in range(1, jmax):
        cj = mp.cosh(j * lu)
        b0 = B0.subs({K: Kv}) if False else None
        sv = 1 - Kv
        Dv = cj + 1 - 2 * Kv
        b0 = sv * ((3 * Kv - 1) * cj**2 - (4 * Kv**2 - Kv + 1) * cj + 2 * Kv**2) / ((cj - 1) * Dv**2)
        b1 = sv * (Kv * cj**2 + (1 - 3 * Kv) * cj + 2 * Kv**2 - 2 * Kv + 1) / ((cj - 1) * Dv**2)
        term = b0 + b1 * mp.cos(q * j)
        tot += term
        if abs(term) < mp.mpf(10)**-32 and j > 5:
            break
    return tot


def F_series(alpha, lu, nmax=20000):
    qq = mp.e**(-lu)
    tot = mp.mpf(0)
    for n in range(1, nmax):
        qn = qq**n
        a = (mp.sin(2 * alpha) * mp.sin(2 * n * alpha) - 2 * n * mp.sin(alpha)**2 * mp.sin(n * alpha)**2) * qn / (1 - qn)
        b = -2 * n * mp.sin(alpha)**2 * mp.cos(n * alpha)**2 * qn / (1 + qn)
        tot += a + b
        if abs(qn) * n < mp.mpf(10)**-34:
            break
    return tot


print('(2) F(pi) from pair functions vs one-variable series:')
for kap, lu in [(0.3, 1.0), (0.6, 0.5), (0.75, 2.0), (0.9, 0.7), (0.99, 0.2)]:
    kap = mp.mpf(kap); lu = mp.mpf(lu)
    a = F_pairs(kap**2, lu, mp.pi)
    b = F_series(mp.acos(kap), lu)
    print(f'    kappa={float(kap):5.2f} l_u={float(lu):4.2f}: pairs {mp.nstr(a, 15)}  series {mp.nstr(b, 15)}  |diff| {mp.nstr(abs(a - b), 3)}')

print('(3) pairing bound chain for K <= 1/2:')
ok = True
worst = -mp.inf
for Kv in [0, 0.1, 0.25, 0.4, 0.5]:
    for lu in [0.05, 0.2, 0.5, 0.75, 1.0, 1.5, 2.5, 5.0, 10.0]:
        Kv = mp.mpf(Kv); lu = mp.mpf(lu)
        F = F_pairs(Kv, lu, mp.pi, jmax=20000)
        c1 = mp.cosh(lu)
        bound = -1 / ((c1 - 1) * c1) + 2 * mp.e**(-2 * lu) / (1 - mp.e**(-lu))
        good = F / (1 - Kv) <= bound < 0
        ok = ok and good
        worst = max(worst, bound)
print('    all grid points satisfy F(pi)/s <= bound < 0:', ok, '; largest bound', mp.nstr(worst, 6))

# (4) exact generating functions (used for the critical mode q = pi):
#   B1(cosh x) = 2 sin^2(a) sum_n n cos^2(n a) z^n,  C1(cosh x) = -2 sin^2(a) sum_n n sin^2(n a) z^n,  z = e^{-x}.
# With e = e^{i a}: sum_n n cos^2(n a) z^n = (1/2) z/(1-z)^2 + (1/4)[w/(1-w)^2 + v/(1-v)^2], w = z e^2, v = z/e^2,
# and sum_n n sin^2(n a) z^n = (1/2) z/(1-z)^2 - (1/4)[w/(1-w)^2 + v/(1-v)^2]. Checked as rational identities in (z, e).
z, e = sp.symbols('z e', positive=True)
cosa = (e + 1 / e) / 2
sin2 = 1 - cosa**2
Kz = cosa**2
cz = (z + 1 / z) / 2
lam = lambda y: y / (1 - y)**2
S_cos = sp.Rational(1, 2) * lam(z) + sp.Rational(1, 4) * (lam(z * e**2) + lam(z / e**2))
S_sin = sp.Rational(1, 2) * lam(z) - sp.Rational(1, 4) * (lam(z * e**2) + lam(z / e**2))
B1z = B1.subs({K: Kz, c: cz})
C1 = -s**2 * (c**2 + c - 2 * K) / ((c - 1) * D**2)
C1z = C1.subs({K: Kz, c: cz})
print('(4) B1 - 2 sin^2(a) sum n cos^2(na) z^n  =', sp.simplify(sp.together(B1z - 2 * sin2 * S_cos)))
print('    C1 + 2 sin^2(a) sum n sin^2(na) z^n  =', sp.simplify(sp.together(C1z + 2 * sin2 * S_sin)))
