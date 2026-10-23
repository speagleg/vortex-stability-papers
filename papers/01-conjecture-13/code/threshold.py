# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# No code changes.
"""Ring threshold X0^2 = q(n) and MT's b_n.

New conventions: X0 = (1-b)/(1+b) is the two-point invariant of a ring vortex with the ring centre
(cos of polar angle on S^2, cosh r on H^2, X0 -> 1 contraction for the plane).
Threshold (new form): X0^2 = q(n) := floor(n^2/4)/(n-1) - 1.

Checks, exactly (sympy, quadratic surds):
  * q(n) equals (n-2)^2/(4(n-1)) (n even), (n-3)/4 (n odd);
  * the two branches X0 = +sqrt(q), -sqrt(q) give b_+ = (1-sqrt q)/(1+sqrt q), b_- = 1/b_+;
    both solve MT (3.6) (1+b^2)/(1+b)^2 = floor(n^2/4)/(2(n-1)); only b_+ lies in (-1,1];
  * b_+ equals the paper's closed form (even/odd, b_7 = 0);
  * the identities 1+b = 2/(1+X0), 1-b = 2X0/(1+X0), (1+b^2)/(1+b)^2 = (1+X0^2)/2 hold identically;
  * the geometry: q<1 sphere, q=1 plane, q>1 H^2.
Run: python threshold.py   (deterministic)
"""
import sympy as sp

n_ = sp.Symbol('n', positive=True)
X = sp.Symbol('X0')
bsym = (1 - X) / (1 + X)
ids = [sp.simplify(1 + bsym - 2 / (1 + X)), sp.simplify(1 - bsym - 2 * X / (1 + X)),
       sp.simplify((1 + bsym**2) / (1 + bsym)**2 - (1 + X**2) / 2)]
print("identities (1+b)-2/(1+X0), (1-b)-2X0/(1+X0), (1+b^2)/(1+b)^2-(1+X0^2)/2:", ids)


def q_of(n):
    return sp.Rational(n * n // 4, n - 1) - 1


def paper_b(n):
    if n % 2 == 0:
        return (4 * (n - 2) * sp.sqrt(n - 1) - n**2) / sp.Integer(n**2 - 8 * n + 8)
    if n == 7:
        return sp.Integer(0)
    return (4 * sp.sqrt(n - 3) - (n + 1)) / sp.Integer(n - 7)


def is_zero(e):
    e = sp.nsimplify(sp.radsimp(sp.expand(e)))
    return sp.simplify(e) == 0


print("n=3: q =", q_of(3), " b_+ =", (1 - sp.sqrt(q_of(3))) / (1 + sp.sqrt(q_of(3))), "(equator)")
print("cols: n | q(n) | closed-form q ok | X0=sqrt q | X0 (20 d) | b_+ exact | b_+ (12 d) | MT(3.6) b_+ | "
      "= paper b_n | b_- = 1/b_+ | MT(3.6) b_- | geometry")
allok = True
for n in range(4, 26):
    q = q_of(n)
    qcf = sp.Rational((n - 2)**2, 4 * (n - 1)) if n % 2 == 0 else sp.Rational(n - 3, 4)
    ok_q = (q == qcf)
    X0 = sp.sqrt(q)
    bp = sp.radsimp((1 - X0) / (1 + X0)) if q != 1 else sp.Integer(0)
    rhs = sp.Rational(n * n // 4, 2 * (n - 1))
    ok36p = is_zero((1 + bp**2) - rhs * (1 + bp)**2)
    ok_paper = is_zero(bp - paper_b(n))
    if q != 1:
        bm = sp.radsimp(1 / bp) if bp != 0 else sp.oo
        ok36m = is_zero((1 + bm**2) - rhs * (1 + bm)**2)
        bm_s = f"{sp.N(bm, 12)}"
    else:
        bm_s, ok36m = "inf (X0=-1: point at infinity / antipodal ring)", True
    in_range = (-1 < bp <= 1)
    geom = "sphere" if q < 1 else ("plane" if q == 1 else "H^2")
    sign = "b>0" if bp > 0 else ("b=0" if bp == 0 else "b<0")
    allok &= ok_q and ok36p and ok_paper and ok36m and in_range
    print(f"n={n:2d} | q={str(q):>8s} | {ok_q} | X0={str(X0):>14s} | {sp.N(X0, 20)} | b_+={str(bp):>22s} | "
          f"{sp.N(bp, 12)} | {ok36p} | {ok_paper} | b_-={bm_s} | {ok36m} | {geom} ({sign}, b_+ in (-1,1]: {in_range})")
print("ALL CHECKS PASS:", allok)
print("note: b_- = 1/b_+ is the second root of MT (3.6) (invariant under b -> 1/b); it is the same ring seen from the")
print("      antipodal pole (sphere) / the other sheet (H^2), i.e. X0 -> -X0, outside MT's range (-1,1].")
