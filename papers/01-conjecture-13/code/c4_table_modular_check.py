# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# No code changes (vendored code in code/archive_kkt/). Prints this paper's c4 ('c4_MT').
"""Re-run of the GF(p) check of the c4 table.

This re-runs vendored code (code/archive_kkt/, verbatim copies of havelock-vortex-rings@2cc1ee5:
conj13/paper/table_check.py and conj13/review3/kkt_exact.py); further agreement comes from c4_closed_forms.py
(exact over Q) and c4_levelset.py (N = 4..11).
For each N = 4..25 it runs the archive's Cartesian order-by-order KKT engine (MT normalisation, c4_MT = 2 c4) in
40-digit floats at the threshold b_N in (-1,1], and exactly over GF(p) for three primes p ~ 2^61, p = 1 mod 4N, at both
conjugates of the threshold, checking: kernel multiplier nu_e[1] = 0 (threshold), nu_e[2] = 0 (no cubic), c4 = table value.
Added here (not in the archive script): a negative control, the same GF(p) data compared with the perturbed target
c4_MT + 1/(4N), which must be rejected.  Timings are omitted so that the output is deterministic.
Run: python c4_table_modular_check.py   (about 7 minutes)
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "archive_kkt", "paper"))
import mpmath as mp  # noqa: E402
from fractions import Fraction  # noqa: E402
import table_check as tc  # noqa: E402  (vendored; also puts archive_kkt/review3 on the path)

for n in range(4, 26):
    F = tc.formula(n)
    for lam, r in tc.float_run(n):
        print('n=%d b_n=%s c4(float)=%s formula=%s=%s diff<1e-35: %s nu1<1e-35: %s' % (
            n, mp.nstr(lam, 12), mp.nstr(r['c4'], 25), F, mp.nstr(mp.mpf(F.numerator) / F.denominator, 25),
            abs(r['c4'] - mp.mpf(F.numerator) / F.denominator) < mp.mpf(10) ** -35, abs(r['nue1']) < mp.mpf(10) ** -35))
    ok, neg = True, True
    Fbad = F + Fraction(1, 4 * n)
    for p in tc.primes_for(n, 3):
        for sign in ((1,) if n == 7 else (1, -1)):
            r = tc.modp_run(n, p, sign)
            Ffp = tc.Fp(F.numerator) / F.denominator
            ok &= r['nue1'].iszero() and r['nue2'].iszero() and (r['c4'] - Ffp).iszero()
            neg &= not (r['c4'] - tc.Fp(Fbad.numerator) / Fbad.denominator).iszero()
    print('n=%d EXACT GF(p) (3 primes x conjugates): threshold, no cubic, c4_MT == %s : %s; perturbed target %s rejected: %s'
          % (n, F, ok, Fbad, neg), flush=True)
