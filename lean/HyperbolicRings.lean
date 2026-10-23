-- Root of the HyperbolicRings library (paper 3: vortex rings and rows on the hyperbolic plane).
-- Fourier blocks of the tanh ring derived from the Hamiltonian:
import HyperbolicRings.TanhBlocks
-- Exact symbol, critical mode, thresholds (all N), large N, Krein window, horocycle row,
-- certificates N = 2..16 (imported through LargeN.AllN), and the linear flow:
import HyperbolicRings.TanhLargeN
-- Irreducibility of the threshold polynomials f_8, ..., f_16 (imports CertN8..CertN16):
import HyperbolicRings.TanhIrred
-- New in this paper: Krein signatures in the odd-N window.
import HyperbolicRings.Krein
-- New in this paper: hypercycle rows (pair functions, stability bound, all-mode and pairing instability).
import HyperbolicRings.Rows.Pair
import HyperbolicRings.Rows.Criterion
-- New: the strip-chart pair term, its second derivatives, the Bloch symbol and the spectral criterion,
-- the generating functions and the critical mode, the curvature monotonicity, the combined statements.
import HyperbolicRings.Rows.PairTerm
import HyperbolicRings.Rows.Bloch
import HyperbolicRings.Rows.CriticalMode
import HyperbolicRings.Rows.Main
import HyperbolicRings.Rows.Monotone
-- New: dense hypercycle rows are unstable (small-spacing limit).
import HyperbolicRings.Rows.SmallSpacing
-- New in this paper: the parity term that separates the even/odd ring germs at the horocycle point.
import HyperbolicRings.Horocycle.ParitySplit
-- New: hypercycle rows converge to the horocycle row (dominated convergence), threshold convergence.
import HyperbolicRings.Horocycle.HyperLimit
