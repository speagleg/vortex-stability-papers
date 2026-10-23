# Paper 1: The regular n-gon is stable at its bifurcation point (Montaldi–Tokieda Conjecture 13)

`paper/main.tex` (built: `paper/main.pdf`). Build: `pdflatex main; bibtex main; pdflatex main; pdflatex main` in `paper/`.

Lean library: `lean/Conj13/` (root `lean/Conj13.lean`), namespace `Conj13`. Build: `cd lean && lake build Conj13`.
Axiom audit: `lake env lean Conj13/Audit.lean` → `outputs/lean_axioms.out` (64 theorems; only `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`).

Scripts: `code/`, outputs: `outputs/`. `sh run_all.sh [--fast]` regenerates them (`PY` selects the interpreter).

## Normalisation

The paper uses `H = -Σ_{i<j} log(|z_i-z_j|²/(σ_iσ_j))` (Montaldi–Tokieda's Hamiltonian without κ²/4π), so
`c4 = (n-2)(m⁴+40m²+48m+16)/(192 n(n-1))` (even, m = n-2) and `(n-1)(n-3)(n²-9n+38)/(128 n)` (odd).
Two scripts (`c4_levelset.py`, `c4_slice.py`) use the alternative normalisation `H' = H/2` (pair term
`−log d_ij` instead of `−log d_ij²`) and print `c4/2` (denominators 384 n(n-1), 256 n); they say so in their
output ("closed/2", "C4_lin (H/2)").
`c4_closed_forms.py` prints both (`c4_MT` = this paper's `c4`, `c4_new` = `c4/2`).

## Claims → status → check

Lean names are full names in `lean/Conj13/`.

| Claim (paper) | Status | Proof / Lean / script | Output |
|---|---|---|---|
| Thm 1.1 (main theorem) | Proved (instantiation of Thm 7.1 by hand) | §7; inputs below | — |
| Prop 2.2 threshold `b_n`: unique root in (-1,1], closed forms, signs | Lean; Certified | `Conj13.bn_spec`, `bn_unique`, `bn_even_paper`, `bn_odd_paper`, `bn_seven`, `bn_four`..`bn_ten`, `bn_sign`; `code/threshold.py` | `outputs/threshold.out` |
| Prop 2.3 Fourier blocks: ring critical exactly at ω₀; Hessian block-diagonal over Fourier modes with blocks diag(a_m, b_m), a_m = C₁ − m(n−m), b_m = m(n−m); all b > −1 | Lean (from H); Numerical | `Conj13.MTBlocks.mt_grad_formula`, `mt_ring_critical`, `mt_ring_critical_iff`, `mtD_omega`, `mtHessQ_eq`, `mtHessSS_eq`, `mtHessTT_eq`, `mtHessST_eq`, `mtHessTS_eq`, `mt_blocks_eigen`, `mt_blocks_hermitian`; pair calculus and Fourier sums in `Conj13.Ring.*` (copied); `Conj13.fejer`, `phi_crit_and_C1`, `C1_eq_iff`; `code/spectral_check.py` (40 digits, n = 4..15) | `outputs/spectral_check.out` |
| Prop 2.3: polarised directional second derivatives = Hessian matrix | Proved | standard fact for C² functions — not restated in Lean (the Lean Hessian is defined by polarising t ↦ d²F(x₀+tξ)/dt²) | — |
| Prop 2.4 spectral picture (kernel, positivity on E) | Proved; arithmetic Lean | `Conj13.am_factor`, `am_nonneg_and_kernel`, `am_next`, `V1'_form`, `V1'_kappa_rho`, `V1'_n4`, `V1'_n5`, `bracket_value` (algebra of {J1,J2}(x0)) | `outputs/spectral_check.out` |
| §2.4 {J1,J2} = n/2 − λJ3 and its value at the ring | Lean (given the Poisson structure) | `Conj13.Bracket.hasDerivAt_J1_x`, `hasDerivAt_J1_y`, `hasDerivAt_J2_x`, `hasDerivAt_J2_y`, `bracket_one`, `bracket_sum`; `Conj13.bracket_value`. The one-vortex bracket {f,g} = (σ²/2)(f_x g_y − f_y g_x) of Ω = 2σ⁻²dx∧dy is taken as the definition — not derived in Lean (Mathlib has no symplectic forms/Poisson brackets on manifolds) | — |
| §2.4 reduced space, momentum differentials on Fourier modes, V₁' | Proved | by hand — not in Lean (symplectic reduction J⁻¹(μ)/K is not formalised in Mathlib) | — |
| Def 3.1 / Lemma 3.2 chart independence | Proved | by hand — not in Lean (needs charts of the reduced manifold) | — |
| Lemma 3.3 symmetry (no cubic, quartic ∝ abs(a)⁴) | Proved; arithmetic Lean | `Conj13.Symmetry.invariant_monomial`, `Conj13.Symmetry.crit_mode_coprime` | — |
| Thm 4.1 (even n) closed form, positivity | Lean (series + algebra); Proved (symmetric criticality) | `Conj13.Config.Ham_stag_sub`, `Conj13.EvenQuartic.J3_curve`, `Jp_stag`, `epsK_stag`, `Ham_curve_jet`, `c4even_limit`, `c4even_limit_at_bn`; `Conj13.h2_eq_zero_iff`, `c4even_diff`, `c4even_reduction`, `c4_even_at_bn`, `c4even_pos`, `even_quartic_pos`. Symmetric criticality (minimiser is D_M-invariant): by hand — not in Lean (uniqueness of a constrained minimiser on a manifold). Cross-checks: `code/even_exact.py` (sympy, symbolic in M, b) | `outputs/even_exact.out` |
| Thm 5.1 (odd n) closed form, positivity | Lean (series + algebra); Proved (ansatz completeness) | `Conj13.Odd4.Ham_oddAnsatz_jet`, `Ham_oddAnsatz_jet4`, `fejer1`, `fejer2`; `Conj13.Odd.J1_oddAnsatz_jet`, `Ham_oddLine_jet`, `epsOdd_hasDerivAt`, `oddNorm_pow4`; `Conj13.Q_values`, `sum_cos_sq_mul_cos`, `f2_eq_zero_iff`, `odd_rel_iff`, `J1con_iff`, `E_vertex`, `a2_pos`, `odd_min_value`, `c4odd_reduction`, `c4_odd_at_bn`, `c4odd_pos`, `odd_quadratic_disc`. Ansatz completeness (only modes 0, 1 slaved at O(A²); O(A³) irrelevant): by hand — not in Lean (implicit-function/slaving argument on the reduced manifold) | — |
| Remark 5.2 (n = 3: odd formula gives 0) | Lean | `Conj13.Symmetry.c4odd_three` | `outputs/c4_closed_forms.out` |
| Table 1 (c4, n = 4..25) | Lean; Numerical (exact modular); Numerical | `Conj13.table_values`, `c4_at_bn`, `table_n7`, `table_n8`; `code/c4_table_modular_check.py` (Numerical, exact modular: GF(p) Cartesian KKT; strong evidence, not a proof over Q; the proof does not use it, no ansatz, + negative control; vendored `code/archive_kkt/`); `code/c4_levelset.py` (80-digit level-set minimisation, n = 4..11; prints c4/2); `code/c4_closed_forms.py` | `outputs/c4_table_modular_check.out`, `outputs/c4_levelset.out`, `outputs/c4_closed_forms.out` |
| Prop 6.1(1) jet of F along MT's line (v2, D), from H | Lean | `Conj13.MTLine.Fline_closed`, `Fline_jet`, `v2_eq`, `v2_eq_h2`, `Dline_eq`, `epsK_line`, `Fline_limit` | `outputs/mt_line_vs_levelset.out` |
| Prop 6.1(2) A, B, D, u2 as Taylor coefficients on the 2-parameter family | Lean (from H); Certified | `Conj13.MTFamily.Ffam_closed`, `Ffam_jet` (on every curve u = κv²: F − F₀ = v₂v² + (Aκ² + Bκ + D)v⁴ + O(v⁶)), `c2fam_eq`, `c4fam_eq`, `J3fam_jet`, `gc2_eq_zero_iff` (level set u = u₂v² + O(v⁴)), `level_quartic_at_bn`; generic jets `log_sextic_jet`, `rat_jet`, `ath_w_jet`; cross-check `code/mt_line_vs_levelset.py` | `outputs/mt_line_vs_levelset.out` |
| Prop 6.1(3) bending identity D + B u2 + A u2² = n² c4 at b_n | Lean (algebra, given A, B, u2); Certified | `Conj13.MTLine.bending_identity`, `bending_at_bn`; script (exact remainder 0) | `outputs/mt_line_vs_levelset.out` |
| Cor 6.2 n = 4: D = 6 − 4√3/3 ≈ 3.69 vs 4; limits 0.2307 vs 1/4 | Lean | `Conj13.MTLine.thr_four`, `n4_line_value`, `n4_line_ne`, `n4_line_limit`; `Conj13.EvenQuartic.c4even_limit_at_bn` (M = 2) | `outputs/mt_line_vs_levelset.out` |
| Table 2 (D, bending, level set, n = 4..20) | Certified | `code/mt_line_vs_levelset.py` (D also recomputed from vortex positions at 50 digits) | `outputs/mt_line_vs_levelset.out` |
| §6 MT's printed T vs direct: difference 72(n−1)λ²(λ²−6λ+1) | Certified | `code/mt_line_vs_levelset.py` | `outputs/mt_line_vs_levelset.out` |
| §6 linear-slice minima (n = 4, 8, 9, 13) | Numerical | `code/c4_slice.py` (prints values/2) | `outputs/c4_slice.out` |
| Remark 7.2 (penalty needed on S² for j > 0 and on H² for j < 0; not in the plane) | Proved | §7, from Prop 2.3 (C₁ decreasing in b) | — |
| Remark 7.3 free minimum D − B²/(4A) = 10/3 (n = 4), 751/7 (n = 8) | Certified | `code/mt_line_vs_levelset.py` | `outputs/mt_line_vs_levelset.out` |
| Appendix B (expansions behind h₄ and E_ij) | Lean | `Conj13.Even.Phi_jet`, `Conj13.Odd4.jet_logPw`, `jet_pair`, `fejer1`, `fejer2` | — |
| Fig 1 | Numerical | `code/make_figures.py` | `paper/figures/mt_line.pdf`, `outputs/make_figures.out` |
| Thm 7.1 (degenerate energy–momentum) — Lemmas B1–B4 and the conclusion | Lean (abstract core); Proved | `Conj13.Lyapunov.lemma_B1`, `lemma_B2`, `lemma_B3`, `quartic_form_coercive`, `lyapunov_on_section` and `stable_modulo_orbit` (trajectories on time intervals `I x`, matching the a priori local vortex flow); `stable_modulo_orbit_global` also available. Global existence (the last step of B4: solutions stay in a compact collision-free set) is by hand | `outputs/lean_axioms.out` |
| Thm 7.1 Lemma A (cross-section), chart on S/K, slaving map β | Proved | by hand — not in Lean (implicit function theorem on a symplectic manifold, Lie group actions; hypotheses of the Lean lemmas) | — |
| §7 verification of (A1)–(A4) for the ring; existence of the vortex flow, conservation of H, J | Proved | by hand — not in Lean (ODE flow on configuration space, conservation laws; Mathlib has no point-vortex dynamics) | — |
| §8, Fig 2 (n = 8 integration) | Numerical | `code/n8_integration.py sinh` (rerun; prints maxima); Fig 2 plots recorded traces `outputs/recorded/D_sinh8_*.npy` (recorded, not rerun; produced by `code/integrate_recorded.py` = havelock-vortex-rings@2cc1ee5:conj13/integrate.py) | `outputs/n8_integration_sinh.out`, `paper/figures/n8_traces.pdf` |

## Lean modules

Copied from `havelock-vortex-rings@2cc1ee5`, `lean/Havelock/` (namespaces renamed, a few
documented fixes; provenance header in each file):
`Algebra` (= `Conj13Algebra`), `Series`, `EvenCurve`, `EvenConfig`, `EvenQuartic`, `OddSums`, `OddQuadratic`,
`OddConstraint`, `Odd4Fejer`, `Odd4Jets`, `Odd4Pair`, `Odd4Trig`, `Odd4Inner`, `Odd4PairSums`, `Odd4Hamiltonian`,
`LyapunovAbstract`, `LyapunovAnalytic`. Not copied: `TaylorCoeffs` (restates the jets as iterated derivatives; not used).

Copied from `havelock-vortex-rings@2cc1ee5:lean/Havelock/Tanh/` into `Conj13/Ring/` (namespace `Conj13.Ring`): `General`, `BlocksSums`,
`BlocksCalc`, `Blocks`, `BlocksHess`, `BlocksFourier` (pair-term calculus, Fejér sums, circulant Hessian, Fourier eigenvectors; the
same code is also in `lean/HyperbolicRings/Tanh/`, kept separate so the libraries stay independent).

New for this paper: `MTLine` (MT's straight line versus the level set), `MTFamily` (the two-parameter family, A, B, D, u₂),
`MTBlocks` (Fourier blocks of MT's family for all b > −1, adapted from `havelock-vortex-rings@2cc1ee5:lean/Havelock/Sinh/Hessian.lean`),
`Bracket` ({J₁, J₂}) and `Symmetry` (invariant monomials, n = 3).

## Scripts

| Script | Provenance | Runtime | Output |
|---|---|---|---|
| `threshold.py` | the author's earlier research code (unpublished), adapted | 2 s | `threshold.out` |
| `c4_closed_forms.py` | the author's earlier research code (unpublished), adapted | <1 s | `c4_closed_forms.out` |
| `mt_line_vs_levelset.py` | new | ~2 min | `mt_line_vs_levelset.out` |
| `even_exact.py` | havelock-vortex-rings@2cc1ee5:conj13/even_exact.py | 36 s | `even_exact.out` |
| `spectral_check.py` | havelock-vortex-rings@2cc1ee5:conj13/gaps/spectral_check.py | 11 min (not in `--fast`) | `spectral_check.out` |
| `c4_levelset.py` | the author's earlier research code (unpublished), adapted | 6 min (not in `--fast`) | `c4_levelset.out` |
| `make_figures.py` | new | 10 s | `make_figures.out`, figures |
| `c4_table_modular_check.py` (+ `archive_kkt/`) | the author's earlier research code (unpublished), adapted; `archive_kkt/` = havelock-vortex-rings@2cc1ee5:conj13/paper/table_check.py, conj13/review3/kkt_exact.py (verbatim) | 7 min (not in `--fast`) | `c4_table_modular_check.out` |
| `c4_slice.py` | the author's earlier research code (unpublished), adapted (printed labels changed) | 3 min (not in `--fast`) | `c4_slice.out` |
| `n8_integration.py` | the author's earlier research code (unpublished), adapted (pool capped at 2) | 10 min (not in `--fast`) | `n8_integration_sinh.out` |
| `integrate_recorded.py` | havelock-vortex-rings@2cc1ee5:conj13/integrate.py | not rerun | `recorded/D_sinh8_*.npy` (recorded) |
