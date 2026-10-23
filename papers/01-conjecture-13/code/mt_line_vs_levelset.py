"""Even n = 2M: Montaldi--Tokieda's straight-line quartic versus the quartic on the momentum level set.

New code written for this paper (no provenance).  Exact (sympy), symbolic in M and b = lambda r0^2 (r0 = 1).

Setting (paper eq. (2.1)): H = -sum_{i<j} log(|z_i-z_j|^2/(sigma_i sigma_j)) + const, sigma = 1 + b|z|^2,
J3 = sum |z|^2/sigma, F = H - omega0 J3 with dF(ring) = 0.  H is 4 pi times MT's Hamiltonian (kappa = 1).
On the D_M-invariant family of two staggered regular M-gons of radii rho_+ (even j) and rho_- (odd j), write
rho_pm = 1 + u +- v.  By the swap symmetry v -> -v,
    F - F0 = v2 v^2 + A u^2 + B u v^2 + D v^4 + (order >= 5 when u = O(v^2)).
* MT (section 3.5.1) expand F along the straight line z_j = (1 + (-1)^j t) e^{2 pi i j/n}: u = 0, v = t.
  Their t^4 coefficient is D.
* On the level set J3 = J3(ring): u = u2 v^2 + O(v^4), so the reduced quartic is D + B u2 + A u2^2.
The unit kernel vector e_k = n^{-1/2}(-1)^k zhat_k gives <q - x0, e> = sqrt(n) v + O(v^2), so c4 = (v^4 coeff)/n^2.
Also evaluated: MT's printed bracket T (p. 21; the t^4 coefficient is n T/(768 pi r0^4 sigma^4), i.e.
n T/(192 sigma^4) for H = 4 pi f) and MT's printed closed forms for T1 + T2 and T1 T2.
Run: python mt_line_vs_levelset.py   (about 1-2 minutes)
"""
import sympy as sp
import mpmath as mp

mp.mp.dps = 30
M, b, u, v = sp.symbols('M b u v', positive=True)
rp, rm = 1 + u + v, 1 + u - v
up, um = rp**2, rm**2
sgp, sgm = 1 + b * up, 1 + b * um
H = (-(M * (M - 1) / 2) * (sp.log(up) + sp.log(um)) - 2 * M * sp.log(up**(M / 2) + um**(M / 2))
     + (2 * M - 1) * M * (sp.log(sgp) + sp.log(sgm)))
J3 = M * (up / sgp + um / sgm)
Z = {u: 0, v: 0}


def d(e, *a):
    return sp.factor(sp.cancel(sp.simplify(sp.diff(e, *a).subs(Z))))


om = sp.factor(d(H, u) / d(J3, u))
F = H - om * J3
assert d(F, u) == 0 and d(F, v) == 0 and d(F, u, v) == 0 and d(F, v, 3) == 0 and d(F, u, v, v, v) == 0
A = sp.factor(d(F, u, 2) / 2)
B = sp.factor(d(F, u, 1, v, 2) / 2)
D = sp.factor(d(F, v, 4) / 24)
v2 = sp.factor(d(F, v, 2) / 2)
u2 = sp.factor(-(d(J3, v, 2) / 2) / d(J3, u))
bend = sp.factor(B * u2 + A * u2**2)
print("General even n = 2M (exact in M, b):")
print("  omega0 =", om)
print("  v^2 coefficient v2 =", v2)
print("  A (u^2, radial V_0 weight) =", A)
print("  B (u v^2 coupling)        =", B)
print("  D (v^4 = MT's line)       =", D)
print("  u2 (level-set bending, u = u2 v^2) =", u2)
print("  bending contribution B u2 + A u2^2 =", bend)

thr = sp.expand(M**2 * (1 + b)**2 - (4 * M - 2) * (1 + b**2))   # = 0  <=>  MT (3.7) for n = 2M
print("  threshold polynomial (MT (3.7)):", sp.factor(thr), "; v2 * (1+b)^2 / (-M) =", sp.factor(sp.expand(-v2 * (1 + b)**2 / M)))

# closed form of n^2 c4 = level-set quartic, reduced modulo the threshold (as a polynomial identity in Q(M)[b])
nn = 2 * M
mm = nn - 2
c4cl = (nn - 2) * (mm**4 + 40 * mm**2 + 48 * mm + 16) / (192 * nn * (nn - 1))
L = sp.together(D + bend - nn**2 * c4cl)
rr = sp.rem(sp.expand(sp.numer(L)), thr, b)
print("  remainder of numerator(D + B u2 + A u2^2 - n^2 c4_closed) modulo the threshold polynomial:", sp.simplify(rr))
LD = sp.together(D - nn**2 * c4cl)
print("  for contrast, remainder of numerator(D - n^2 c4_closed):", sp.factor(sp.simplify(sp.rem(sp.expand(sp.numer(LD)), thr, b))))


def bn(nv):
    bb = sp.symbols('bb')
    rts = sp.solve(sp.expand(thr.subs(M, sp.Rational(nv, 2)).subs(b, bb)), bb)
    return rts


print()
print("Numerical values at the threshold b_n in (-1,1] (MT normalisation of H times 4 pi; coefficients of t^4):")
print(" n |      b_n      |  A        |  B        |  u2       | D (MT line) | bending  | level set | n^2 c4 closed | MT printed n T/(192 s^4)")
for nv in (4, 6, 8, 10, 12, 16, 20):
    rts = bn(nv)
    bv = [x for x in rts if -1 < float(x) <= 1][0]
    sub = {M: sp.Rational(nv, 2), b: bv}
    vals = {k: mp.mpf(sp.N(e.subs(sub), 40)) for k, e in (('A', A), ('B', B), ('u2', u2), ('D', D), ('bend', bend))}
    lam = mp.mpf(sp.N(bv, 40))
    T = ((nv - 2) * (nv**3 + 2 * nv**2 - 12 * nv + 24) * (1 + lam)**4
         + 24 * (nv - 1) * lam * (19 * lam**3 - 54 * lam**2 + 43 * lam - 4))
    printed = nv * T / (192 * (1 + lam)**4)
    cl = sp.Rational(nv - 2, 1) * ((nv - 2)**4 + 40 * (nv - 2)**2 + 48 * (nv - 2) + 16) / (192 * nv * (nv - 1)) * nv**2
    print(f"{nv:2d} | {mp.nstr(lam, 12):>13s} | {mp.nstr(vals['A'], 8):>9s} | {mp.nstr(vals['B'], 8):>9s} | "
          f"{mp.nstr(vals['u2'], 8):>9s} | {mp.nstr(vals['D'], 10):>11s} | {mp.nstr(vals['bend'], 8):>8s} | "
          f"{mp.nstr(vals['D'] + vals['bend'], 10):>9s} | {str(cl):>8s} = {mp.nstr(mp.mpf(cl.p) / cl.q, 10)} | {mp.nstr(printed, 10)}")

print()
print("MT's printed bracket T against the direct bracket T_direct = 192 (1+b)^4 D / n, at both roots of (3.7):")
for nv in (4, 6, 8, 10):
    m = nv - 2
    Ts = []
    for bv in bn(nv):
        lam = mp.mpf(sp.N(bv, 40))
        Dd = mp.mpf(sp.N(D.subs({M: sp.Rational(nv, 2), b: bv}), 40))
        Tdir = 192 * (1 + lam)**4 * Dd / nv
        Tpr = ((nv - 2) * (nv**3 + 2 * nv**2 - 12 * nv + 24) * (1 + lam)**4
               + 24 * (nv - 1) * lam * (19 * lam**3 - 54 * lam**2 + 43 * lam - 4))
        Ts.append((Tdir, Tpr))
        print(f"  n={nv:2d} b={mp.nstr(lam, 12):>14s}: T_direct={mp.nstr(Tdir, 12):>14s}  T_printed={mp.nstr(Tpr, 12):>14s}")
    s_mt = mp.mpf(128 * (m + 1)) / (m**2 - 4 * m - 4)**4 * (384 + 2560 * m + 4 * m**9 + 4832 * m**2 + 5024 * m**3
                                                          + 10616 * m**4 + 15888 * m**5 + 10778 * m**6 + 3266 * m**7 + 177 * m**8)
    p_mt = mp.mpf(4096 * (m + 1)**2) / (m**2 - 4 * m - 4)**4 * (16 * m**10 + 648 * m**9 + 7409 * m**8 + 1044 * m**7
                                                              + 39960 * m**6 + 85512 * m**5 + 57332 * m**4 + 25824 * m**3
                                                              + 15136 * m**2 + 5376 * m + 576)
    print(f"        T1+T2: direct {mp.nstr(Ts[0][0] + Ts[1][0], 12)}, printed-T {mp.nstr(Ts[0][1] + Ts[1][1], 12)}, "
          f"MT closed form {mp.nstr(s_mt, 12)};  T1*T2: direct {mp.nstr(Ts[0][0] * Ts[1][0], 12)}, "
          f"printed-T {mp.nstr(Ts[0][1] * Ts[1][1], 12)}, MT closed form {mp.nstr(p_mt, 12)}")

print()
print("Independent check of D from the vortex positions (no product formula): t^4 Taylor coefficient of")
print("F(t) = H - omega0 J3 at z_j = (1 + (-1)^j t) e^{2 pi i j/n}, b = b_n, by mpmath.taylor at 50 digits:")
mp.mp.dps = 50


def F_line(nv, lam, tt):
    z = [(1 + (-1)**j * tt) * mp.expjpi(2 * mp.mpf(j) / nv) for j in range(nv)]
    sg = [1 + lam * abs(w)**2 for w in z]
    Hh = -sum(mp.log(abs(z[i] - z[j])**2 / (sg[i] * sg[j])) for i in range(nv) for j in range(i + 1, nv))
    Jj = sum(abs(w)**2 / s for w, s in zip(z, sg))
    return Hh + (nv - 1) * (1 - lam**2) / 2 * Jj


for nv in (4, 6, 8, 10):
    bv = [x for x in bn(nv) if -1 < float(x) <= 1][0]
    lam = mp.mpf(sp.N(bv, 60))
    cs = mp.taylor(lambda tt: F_line(nv, lam, tt), 0, 4)
    Dd = mp.mpf(sp.N(D.subs({M: sp.Rational(nv, 2), b: bv}), 60))
    print(f"  n={nv:2d}: t^2 coeff {mp.nstr(cs[2], 5)}, t^3 coeff {mp.nstr(cs[3], 5)}, t^4 coeff {mp.nstr(cs[4], 20)}; "
          f"D (closed form) {mp.nstr(Dd, 20)}; |diff| {mp.nstr(abs(cs[4] - Dd), 3)}")

print()
print("MT's printed bracket versus the bracket of the direct expansion, symbolically (n = 2M, lam = b):")
nn_, lam_ = sp.symbols('n lam')
Tdir = sp.expand(sp.simplify((192 * (1 + b)**4 * D / (2 * M)).subs({M: nn_ / 2, b: lam_})))
Tpr = sp.expand((nn_ - 2) * (nn_**3 + 2 * nn_**2 - 12 * nn_ + 24) * (1 + lam_)**4
                + 24 * (nn_ - 1) * lam_ * (19 * lam_**3 - 54 * lam_**2 + 43 * lam_ - 4))
print("  T_direct =", sp.factor(Tdir))
print("  T_printed - T_direct =", sp.factor(Tpr - Tdir))

print()
print("Free minimum over u (no momentum constraint): quartic D - B^2/(4A), a lower bound for D and for the level set:")
for nv in (4, 6, 8, 10, 12):
    bv = [x for x in bn(nv) if -1 < float(x) <= 1][0]
    sub = {M: sp.Rational(nv, 2), b: bv}
    fm = sp.nsimplify(sp.radsimp(sp.simplify((D - B**2 / (4 * A)).subs(sub))))
    print(f"  n={nv:2d}: D - B^2/(4A) = {fm} = {sp.N(fm, 12)};  D = {sp.N(D.subs(sub), 12)};  level set = {sp.N((D + bend).subs(sub), 12)}")
