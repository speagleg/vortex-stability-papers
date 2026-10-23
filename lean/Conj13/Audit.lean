/- Axiom audit for paper 01-conjecture-13 (not imported by the root `Conj13.lean`).
Run: `lake env lean Conj13/Audit.lean`. -/
import Conj13

open Conj13

-- §2 threshold and spectral arithmetic
#print axioms Conj13.bn_spec
#print axioms Conj13.bn_unique
#print axioms Conj13.bn_sign
#print axioms Conj13.phi_crit_and_C1
#print axioms Conj13.C1_eq_iff
#print axioms Conj13.am_nonneg_and_kernel
#print axioms Conj13.am_next
#print axioms Conj13.V1'_n4
#print axioms Conj13.V1'_n5
#print axioms Conj13.bracket_value
#print axioms Conj13.fejer
-- §3 symmetry
#print axioms Conj13.Symmetry.invariant_monomial
#print axioms Conj13.Symmetry.crit_mode_coprime
-- §4 even n
#print axioms Conj13.EvenQuartic.J3_curve
#print axioms Conj13.EvenQuartic.Jp_stag
#print axioms Conj13.EvenQuartic.Ham_curve_jet
#print axioms Conj13.EvenQuartic.c4even_limit_at_bn
#print axioms Conj13.c4even_reduction
#print axioms Conj13.c4_even_at_bn
-- §5 odd n
#print axioms Conj13.Odd4.Ham_oddAnsatz_jet
#print axioms Conj13.Odd4.fejer1
#print axioms Conj13.Odd4.fejer2
#print axioms Conj13.Odd.J1_oddAnsatz_jet
#print axioms Conj13.Q_values
#print axioms Conj13.a2_pos
#print axioms Conj13.c4odd_reduction
#print axioms Conj13.c4_odd_at_bn
#print axioms Conj13.sum_cos_sq_mul_cos
-- positivity and table
#print axioms Conj13.c4_at_bn
#print axioms Conj13.c4even_pos
#print axioms Conj13.c4odd_pos
#print axioms Conj13.table_values
#print axioms Conj13.Symmetry.c4odd_three
-- §6 MT's line versus the level set
#print axioms Conj13.MTLine.Fline_jet
#print axioms Conj13.MTLine.Fline_limit
#print axioms Conj13.MTLine.v2_eq_h2
#print axioms Conj13.MTLine.bending_identity
#print axioms Conj13.MTLine.bending_at_bn
#print axioms Conj13.MTLine.n4_line_value
#print axioms Conj13.MTLine.n4_line_ne
#print axioms Conj13.MTLine.n4_line_limit
-- §7 abstract Lyapunov argument
#print axioms Conj13.Lyapunov.lemma_B1
#print axioms Conj13.Lyapunov.lemma_B2
#print axioms Conj13.Lyapunov.lemma_B3
#print axioms Conj13.Lyapunov.lyapunov_on_section
#print axioms Conj13.Lyapunov.stable_modulo_orbit
#print axioms Conj13.Lyapunov.stable_modulo_orbit_global
-- added: Fourier blocks from the Hamiltonian (Prop 2.3), the bracket (§2.4), the two-parameter family (Prop 6.1)
#print axioms Conj13.MTBlocks.mt_ring_critical
#print axioms Conj13.MTBlocks.mt_ring_critical_iff
#print axioms Conj13.MTBlocks.mtD_omega
#print axioms Conj13.MTBlocks.mtHessQ_eq
#print axioms Conj13.MTBlocks.mt_blocks_eigen
#print axioms Conj13.MTBlocks.mt_blocks_hermitian
#print axioms Conj13.Bracket.hasDerivAt_J1_x
#print axioms Conj13.Bracket.hasDerivAt_J2_y
#print axioms Conj13.Bracket.bracket_one
#print axioms Conj13.Bracket.bracket_sum
#print axioms Conj13.MTFamily.Ffam_closed
#print axioms Conj13.MTFamily.Ffam_jet
#print axioms Conj13.MTFamily.c2fam_eq
#print axioms Conj13.MTFamily.c4fam_eq
#print axioms Conj13.MTFamily.J3fam_jet
#print axioms Conj13.MTFamily.gc2_eq_zero_iff
#print axioms Conj13.MTFamily.level_quartic_at_bn
