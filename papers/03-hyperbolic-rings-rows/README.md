# Paper 3: Vortex rings and rows on the hyperbolic plane

`paper/main.pdf` (source `paper/main.tex`, `paper/refs.bib`, figures in `paper/figures/`).

Model: point vortices of equal strength on H² with the Green function −log tanh(d/2) (Kimura's model, no
background). Results: Fourier blocks and one threshold for every ring size; the odd-N Krein window; the large-N limit
and the horocycle row; the critical curvature 1/√2 and the threshold curve of hypercycle rows; and the structure of
the stability boundary at the horocycle point.

## Reproducing

```sh
sh run_all.sh --fast    # about 5 minutes on an idle machine (15 on a loaded one); skips the four slow scripts
sh run_all.sh           # everything (adds about 25 minutes)
cd ../../lean && lake build HyperbolicRings            # about 21 minutes from a Mathlib-only cache
cd ../../lean && lake env lean HyperbolicRings/Audit.lean > ../papers/03-hyperbolic-rings-rows/outputs/lean_axioms.out
```

Python: `PY` defaults to `python3` (numpy, scipy, sympy,
mpmath, python-flint, matplotlib). All scripts are self-contained in `code/`; copied scripts carry a
`# Provenance:` header. Every output was regenerated here by running the script; `boatto_map_and_verify.out` is
byte-identical to `havelock-vortex-rings@2cc1ee5:tanh/boatto_check/map_and_verify.out`. Nothing is "recorded, not rerun".
Two slow outputs, `tanh_blocks_fd.out` and `rows_screened.out`, had only their header/label text edited after the run
(internal labels removed; label text edited, numbers unchanged).

| Script | Output | Time | What it does |
|---|---|---|---|
| `tanh_threshold_polys.py` (+ `tanh_common.py`) | `outputs/tanh_threshold_polys.out` | 40 s–5 min | exact numerators of the ring blocks, root isolation on (0,1), certified ξ*(N), N ≤ 16, factorisation, irreducibility, palindromy, Arb balls |
| `tanh_krein.py` | `outputs/tanh_krein.out` | 20 s–3.5 min | definiteness thresholds ξ_EM(N), Krein windows N = 9, 11, 13, 15, inertia of every block on the window |
| `tanh_large_n.py` | `outputs/tanh_large_n.out` | 15 s | τ∞, ℓ*, Arb bracket of τ∞, thresholds to N = 801 |
| `blocks.py` | `outputs/blocks.out` | 2 s | floating-point ξ*(8), ξ*(9), ξ*(10) from the block formulas |
| `boatto_map_and_verify.py` (+ `boatto_hessian.py`) | `outputs/boatto_map_and_verify.out` | ~2 min | Boatto's (2008) Hessian implemented from her equations, mapped to ξ |
| `ring_row_germs.py`, `b4_varsigma.py`, `b7_curves.py`, `b8_flat.py` | same names `.out` | < 30 s | second-order constants, slopes, modular germ, ring curves, flat remainder |
| `rows_symbol.py` (+ `rows_common.py`) | `outputs/rows_symbol.out` | ~4 min | hypercycle-row pair functions by sympy; numerical Hessian, lattice-sum symbol, 6-site supercell |
| `rows_fpi.py` | `outputs/rows_fpi.out` | 30 s | F(π) by four methods (lattice, Lambert, theta, dual series); horocycle limit |
| `single_root_cert.py` | `outputs/single_root_cert.out` | 10 s | Arb certificate, regions ℓ_u ≥ 6 and 0.25 ≤ ℓ_u ≤ 6 (its region-C part is superseded by `region_C_cert.py`) |
| `region_C_cert.py` (new) | `outputs/region_C_cert.out` | 1 s | Arb certificate for ℓ_u < 0.25 with the bounds of Appendix E (Lemmas E.1–E.3) |
| `dual_series_check.py` (new) | `outputs/dual_series_check.out` | 2 s | numerical check of each step of the proof of the dual series (Appendix D) |
| `kappa_c_check.py` | `outputs/kappa_c_check.out` | 5 s | exact identities used in Lemma 6.2, Prop 6.3 and Thm 6.4; bound chain of Thm 6.4(b) on a grid |
| `make_figures.py` | `outputs/make_figures.out`, `paper/figures/*.pdf` | 10 s | Figures 1 and 2 (floating point) |
| `tanh_blocks_fd.py` (slow) | `outputs/tanh_blocks_fd.out` | ~7 min | blocks vs finite differences of the Cartesian Hessian |
| `tanh_extras.py` (slow-ish) | `outputs/tanh_extras.out` | 30 s | Krein-window structure for N up to 241, Krein constant |
| `rows_thresholds.py` (slow) | `outputs/rows_thresholds.out` | ~4 min | ℓ_hyp(κ) table, ℓ_A ratio, near-κ_c law, q-series, horocycle approach |
| `rows_screened.py` (slow) | `outputs/rows_screened.out` | ~10 min | screened kernels W_ν, ν = 0, 1, 2 (Remark 6.5 only) |

## Lean

Library `HyperbolicRings` in `../../lean/` (namespace `HyperbolicRings`). It contains

* `Tanh/**`, `TanhBlocks.lean`, `TanhLargeN.lean`, `TanhIrred.lean`: copied from
  `havelock-vortex-rings@2cc1ee5:lean/Havelock/**` with namespaces renamed (provenance header
  in each file). All of
  them are included and built, including every certificate module (`StableN2to7`, `CertN8`–`CertN16c`,
  `IrredN8`–`IrredN16`).
* New for this paper:
  * `Krein.lean`: Krein signatures in the odd-N window.
  * `Rows/PairTerm.lean`: the tanh pair term in the strip chart z = e^{u+iφ}, proved equal to the upper-half-plane pair
    term `pairG` (`stripW_eq_pairG`); the eight per-pair second derivatives at the row, in closed form, identified with
    the pair functions B⁽⁰⁾, B⁽¹⁾, C⁽¹⁾.
  * `Rows/Pair.lean`, `Rows/Criterion.lean`: pair identities, absolute convergence, stability bound, all-mode and pairing
    instability for the series F(q).
  * `Rows/Bloch.lean`: the Bloch lattice sums of the per-pair coefficients converge to [[iϖ, 2F], [C, iϖ]] with C < 0;
    spectral criterion (`bloch_stable_iff`).
  * `Rows/CriticalMode.lean`: generating functions, B⁽¹⁾ = 2 sin²α ∑ n cos²(nα) e^{-nx}, F strictly decreasing on [0, π],
    F(q) ≥ F(π), row stable iff F(π) ≥ 0.
  * `Rows/Main.lean`: the critical-curvature theorem for the Bloch matrices. `Rows/Monotone.lean`: at fixed strip
    spacing, F(π)/sin²α increases with κ², so stability is monotone in the curvature.
  * `Horocycle/HyperLimit.lean`: at fixed arc spacing, F(π) → (τ²/2)Φ(τ) as κ → 1 (dominated convergence; the limit is
    identified with the horocycle-row yy-entry at the pairing mode), and the threshold-convergence statement.
  * `Horocycle/ParitySplit.lean`: second x-derivative of ψ and its sign at τ∞.
  * `Rows/SmallSpacing.lean`: ℓ_u² F(π) → −π² sin²α/4 as ℓ_u → 0 (dominated convergence), so dense rows are unstable
    (Lemma E.4).
  * `Krein.lean` also contains `xiEM_lt_one` and `krein_window_bounds` (0 < ξ* < ξ_EM < 1).
* `Audit.lean` (not imported by the root): `#print axioms` for 120 theorems (every theorem named in the paper or this README, plus dependencies); output `outputs/lean_axioms.out`. Every one
  depends only on `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no new axioms, no `native_decide`.

Build: the first `lake build HyperbolicRings` (copied modules only, from a Mathlib-only cache) completed successfully in
20 min 39 s wall clock (`outputs/lean_build.out`; slowest modules `CertN16a` 747 s and `CertN15a/b`, `CertN14a/b`
270–680 s). After the new modules were added, `lake build HyperbolicRings` again completed successfully
(`outputs/lean_build_final.out`, 8990 jobs; the new modules take a few minutes in total).

Screened kernels W_ν appear only in Remark 6.5, for orientation; the paper does not rely on them.

## Claims

Status labels: **Lean**, **Proved** (by hand in the paper), **Certified** (exact/interval arithmetic), **Derived**,
**Numerical**. Where a Lean statement rests on a modelling input that is not formalised, the input is named in the
status column.

| Claim | Status | Proof / Lean theorem | Script → output |
|---|---|---|---|
| Lemma 2.2 (ring is a relative equilibrium, Ω) | Lean | `HyperbolicRings.Tanh.ring_critical`, `ring_critical_iff`; hand computation App. A | — |
| Thm 3.1 (Fourier blocks) | Lean | `blocks_eigen`, `blocks_hermitian` (Hessian from H in `Tanh.BlocksHess`); hand proof App. A | `tanh_blocks_fd` (finite differences), `tanh_threshold_polys` (a) |
| Prop 3.2 (linearisation, criteria) | Lean | `linFlow_spectral_iff`, `hessQ_posDef_compl_iff` (`Tanh.LinearFlow`), `flowBlock_hasEigenvalue_iff`, `specStable_iff_spectral` | — |
| Thm 3.3 (exact symbol) | Lean | `aBlock_xiOf`, `bBlock_xiOf`, `gBlock_xiOf` | `tanh_large_n` (c) |
| Lemma 3.4 (b_m > 0) | Lean | `beta_pos`, `bBlock_pos` | — |
| Lemma 3.5 (critical mode ⌊N/2⌋) | Lean | `psi_strictAntiOn`, `aBlock_half_le`, `aBlock_half_lt`, `specStable_iff`; hand proof App. B | — |
| Thm 3.6(a) (N ≤ 7 stable and definite at every radius) | Lean | `stable_N2` … `stable_N7`, `stable_all_radii_of_le_seven` (polynomial positivity certificates) | `tanh_threshold_polys`, `tanh_krein` (exact root isolation, independent) |
| Thm 3.6(b) (one threshold, every N ≥ 8) | Lean | `unique_threshold_of_ge_eight` (even: `aBlock_half_threshold`; odd ≥ 17: `aBlock_half_threshold_of_ge_17`; odd 9–15: `cert_N9/11/13/15`) | `tanh_threshold_polys` |
| Thm 3.6(c) (algebraic) | Proved | immediate from Thm 3.1 | — |
| Table 1, ξ*(N) digits | Certified (Lean to 10⁻²⁰) | `cert_N8` … `cert_N16` | `tanh_threshold_polys.out` |
| Table 1 / Remark 3.7, degrees, irreducibility, unit ξ*(8) | Lean (irreducibility) + Certified (degree, palindromy, leading coeff.) | `Irred.f8_irreducible` … `f16_irreducible`; minimal-polynomial consequences by Gauss's lemma (paper) | `tanh_threshold_polys.out` |
| Table 1, Krein window widths | Certified | — | `tanh_krein.out` |
| Remark 3.8 and §8 (Boatto's equations reproduce ξ*; her Fig. 5a and quotes, journal and preprint mp_arc 06-311 both read) | Numerical | — | `boatto_map_and_verify.out` |
| Lemma 4.1 (definiteness excess) | Lean | `beta_mul_G`, `K_pos`, `G_nonneg`, `det_xiOf` | — |
| Thm 4.2(a) (even N: no window) | Lean | `emDefinite_iff_even`, `xiEM_eq_xiStar_even` | `tanh_krein.out` (N ≤ 16) |
| Thm 4.2(b) (odd N ≥ 9: 0 < ξ* < ξ_EM < 1, window non-empty, O(N⁻³)) | Lean | `krein_window_odd`, `Krein.krein_window_bounds`, `Krein.xiEM_lt_one`, `xiEM_sub_xiStar_le` | — |
| Thm 4.2(c) (opposite Krein signatures) | Lean | `HyperbolicRings.Krein.ring_window_hypotheses`, `opposite_signatures`, `eigenvalues_imaginary_distinct` | — |
| Thm 4.2(d) (windows N = 9..15, block structure) | Certified; N ≤ 241 Numerical | — | `tanh_krein.out`; `tanh_extras.out` |
| Krein constant 0.003709 | Derived | — | `tanh_extras.out` |
| Lemma 5.1 (Φ decreasing, τ∞) | Lean; digits Certified | `Phi_strictAntiOn`, `existsUnique_Phi_zero`, `tauInf_bracket` | `tanh_large_n.out` (a′) |
| Thm 5.2 (cosh r* = N/τ∞ + O(1/N), ℓ_N → ℓ*) | Lean | `cR_xiStar_rate`, `tendsto_cR_xiStar`, `spacing_rate`, `cR_xiEM_rate` | `tanh_large_n.out` (d) |
| Prop 5.3 (second order) | Proved (analytic IFT, not in Mathlib in the needed form); constants Numerical; sign of parity term Lean | `HyperbolicRings.Horocycle.second_deriv_psi`, `psiXX_tauInf_neg` | `b4_varsigma.out`, `tanh_large_n.out`, `ring_row_germs.out` |
| Thm 5.4(a) (horocycle-row symbol = limit of ring blocks) | Lean | `row_bloch_symbol`, `pair_hessian_row`, lattice sums in `Tanh.LargeN.RowFourier` | — |
| Thm 5.4(b) (row stable iff ℓ ≥ ℓ*, no Krein window) | Lean | `row_stable_iff`, `row_definite_iff`, `row_spectral_iff` | — |
| Eq. (5) (strip-chart pair term) | Lean | `Rows.stripW_eq_pairG` | — |
| Prop 6.1 (hypercycle Bloch symbol) | Lean (modelling inputs: Hamilton's equations in the strip chart; linearisation of the infinite row = lattice sum of per-pair second derivatives, as for the horocycle row) | `onB_val` … `cpP_val`, `onB_eq_B0`, `cpB_eq_B1`, `onC_eq_C1`, `cpC_eq_C1`, `hasSum_symB`, `hasSum_symC`, `hasSum_symU`, `hasSum_symP`, `Cser_neg`, `rowFlow_re_iff`, `bloch_stable_iff`; hand derivation App. C | `rows_symbol.out` (a)–(e) |
| Lemma 6.2 (pair identities) | Lean | `Rows.B0_sub_B1`, `B0_add_B1`, `B1_pos`, `C1_neg`, `go_le_half`, `ge_le_half` | `kappa_c_check.out` (1) |
| Prop 6.3 (critical mode q = π) | Lean | `hasSum_n_cos`, `hasSum_cos_geom`, `B1_gen`, `F_strictAntiOn`, `F_ge_F_pi`, `row_stable_iff_F_pi` | `kappa_c_check.out` (4); `rows_symbol.out` (b), (f) |
| Eq. (7) (one-variable series for F(π)) | Proved (generating functions) | not in Lean: the C⁽¹⁾ and B⁽⁰⁾ generating functions are not formalised (the same technique as `B1_gen` would apply; not needed by any Lean theorem) | `kappa_c_check.out` (2), (4); `rows_fpi.out` |
| Thm 6.4(a) (|κ| ≤ 1/2: all modes unstable) | Lean | `Rows.every_mode_unstable` (from `all_mode_instability`, `F_summable`) | — |
| Thm 6.4(b) (|κ| ≤ 1/√2: unstable at every spacing) | Lean | `Rows.row_unstable_of_le_kappa_c` (from `pairing_instability`) | `kappa_c_check.out` (3) |
| Thm 6.4(c) (stability bound ℓ_A) | Lean | `Rows.row_stable_of_bound` (from `stability_bound`) | `rows_thresholds.out` (3) |
| Remark 6.5 (45°, other kernels) | Derived (leading order); screened-kernel thresholds Numerical, for orientation only | — | `rows_screened.out` |
| Thm 6.6(a) (single transversal threshold) | Certified (regions ℓ_u ≥ 0.25: `single_root_cert.py`; ℓ_u < 0.25: `region_C_cert.py` with Lemmas E.1–E.3 proved in Appendix E and the dual series, Thm 6.7, proved in Appendix D); negativity at small spacing: Lemma E.4 (Lean) and Lemma E.2 | not in Lean: Arb certificates (~15 000 and 113 boxes) | `single_root_cert.out`, `region_C_cert.out` |
| Thm 6.6(b), monotonicity in κ | Lean for ℓ_u,hyp (strict decrease then follows from (a)); decrease of ℓ_hyp itself: Numerical | `Rows.Fpi_div_strictMono`, `stable_mono` | `rows_thresholds.out` (1) |
| Thm 6.6(b), analyticity and the law near κ_c | Proved given (a) | not in Lean: analytic implicit function theorem (Mathlib has the C¹ version only) and a uniform q-series remainder; feasible in part, not done | `rows_thresholds.out` (4), (5) |
| Thm 6.6(c) (F(π) → τ²Φ/2 at fixed arc spacing; ℓ_hyp(κ) → ℓ*) | Lean, except the final step "the unique zero converges", which uses (a) | `Horocycle.tendsto_F_pi`, `hasSum_gL`, `hyper_threshold_tendsto` | `rows_thresholds.out` (6), `rows_fpi.out` (3) |
| Eq. (8) (I(ℓ) := τ²Φ(τ)/2 and its closed form) | Proved (elementary); the integral form mentioned after it is Numerical (15-digit quadrature) and not used | — | `rows_fpi.out` (3) |
| Table 2 (ℓ_hyp(κ)) | Numerical | — | `rows_thresholds.out` (1), `make_figures.out` |
| Thm 6.7 (dual series) | Proved (Appendix D: Lambert series → lattice sums, Fourier transform of 1/(cosh x − cos θ) by residues, Poisson summation, assembly); every step checked numerically | not in Lean: needs the residue computation of the Fourier transform (Mathlib has Poisson summation but not this transform) | `dual_series_check.out`, `rows_fpi.out` (1), (2) |
| Lemma E.1 (bounds on R and ∂_η R) | Proved | — | used in `region_C_cert.out` |
| Lemma E.2 (η ≥ 7: F(π) < 0) | Proved | — | `region_C_cert.out` (C1) |
| Lemma E.3 (region C2 bounds) | Proved | — | `region_C_cert.out` (C2) |
| Lemma E.4 (dense rows unstable: ℓ_u² F(π) → −π² sin²α/4) | Lean | `Rows.tendsto_F_small`, `Rows.F_neg_small`, `Rows.hasSum_odd_sq` | — |
| Thm 7.1(a) (rings accumulate only at (1, ℓ*)) | Proved; rates Lean | `cR_xiStar_rate`, `spacing_rate` | `tanh_large_n.out` |
| Thm 7.1(b) (square-root branch point, flat remainder, α ↦ ℓ_hyp(cos α) not real-analytic at 0) | Proved given Thm 6.6(a) and Thm 6.7 | not in Lean: real-analytic germs and the dual series; λ₁ > 0 reduces to Φ′(τ∞) < 0, which is Lean (`Phi_strictAntiOn`) | `b7_curves.out`, `b8_flat.out` |
| Thm 7.1(c) (different ring slopes) | Proved (via Prop 5.3); sign Lean; decimals Numerical | `psiXX_tauInf_neg`, `Phi_strictAntiOn` | `b4_varsigma.out`, `ring_row_germs.out` |
| Remark 7.2 (rings lie on two analytic curves) | Numerical | — | `b7_curves.out` |
| Fig. 1, Fig. 2 | Numerical | — | `make_figures.out` |

## Lean coverage summary

In Lean: everything about rings and the horocycle row (blocks from the Hamiltonian, linearisation, thresholds for all
N, certificates N ≤ 16, irreducibility, Krein window and Krein signatures, large-N rates, row symbol and critical
spacing); for hypercycle rows, the strip-chart pair term, the Bloch symbol from its second derivatives, the spectral
criterion, the critical mode q = π, the critical curvature 1/√2 (all three parts), monotonicity in the curvature, and
the convergence to the horocycle row, and the instability of dense rows; at the horocycle point, the sign that separates
the parities.

Not in Lean, with reasons: Hamilton's equations in the strip chart (the conformal factor, taken as the model); the
single hypercycle threshold (Arb certificate, ~15 000 boxes); statements resting on the analytic implicit function
theorem (Prop 5.3, analyticity in Thm 6.6(b), Thm 7.1(b)); the q-series law near κ_c; the dual series (Thm 6.7, proved by hand
in Appendix D; the Fourier transform needs a residue computation not available in Mathlib); the estimates of Lemmas E.1–E.3;
eq. (7); and all floating-point decimals.
