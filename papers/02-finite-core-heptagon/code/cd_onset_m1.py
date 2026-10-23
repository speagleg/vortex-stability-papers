"""Onset of instability in the Bloch blocks m = 1, 6 of the patch heptagon (the second instability of
Result 5.2), by bisection on max Re over block m = 1, at two resolutions."""
import sys
import numpy as np
import cd

tol = 1e-7


def re1(a, M):
    S = cd.spectrum(7, a, M)
    return max(S['blocks'][1]['ev'].real), max(S['blocks'][6]['ev'].real)


if __name__ == '__main__':
    for M in ([129] if '--fast' in sys.argv else [129, 193]):
        lo, hi = 0.2615, 0.265
        print(f"M={M}: max Re block 1, 6 at a={lo}: {re1(lo, M)}; at a={hi}: {re1(hi, M)}")
        for _ in range(10 if '--fast' not in sys.argv else 5):
            mid = 0.5 * (lo + hi)
            r = re1(mid, M)[0]
            if r > tol:
                hi = mid
            else:
                lo = mid
        print(f"M={M}: onset in blocks m = 1, 6 at a in [{lo:.6f}, {hi:.6f}]; max Re at a={hi + 2e-4:.5f}: {re1(hi + 2e-4, M)}")
        sys.stdout.flush()
