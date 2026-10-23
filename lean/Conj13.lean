-- Root of the Conj13 library (paper 1: Montaldi–Tokieda Conjecture 13).
-- Exact-algebra layer (threshold, spectral arithmetic, closed forms of c₄, table entries):
import Conj13.Algebra
-- Series layer: the coefficients used by `Conj13.Algebra`, derived from the Hamiltonian.
import Conj13.Series
import Conj13.EvenCurve
import Conj13.EvenConfig
import Conj13.EvenQuartic
import Conj13.OddSums
import Conj13.OddQuadratic
import Conj13.OddConstraint
import Conj13.Odd4Fejer
import Conj13.Odd4Jets
import Conj13.Odd4Pair
import Conj13.Odd4Trig
import Conj13.Odd4Inner
import Conj13.Odd4PairSums
import Conj13.Odd4Hamiltonian
-- Montaldi–Tokieda straight line versus the level set (new for this paper):
import Conj13.MTLine
import Conj13.Symmetry
import Conj13.MTFamily
import Conj13.MTBlocks
import Conj13.Bracket
-- Abstract Lyapunov layer (Lemmas B1–B4 and the stability theorem, abstract setting):
import Conj13.LyapunovAbstract
import Conj13.LyapunovAnalytic
