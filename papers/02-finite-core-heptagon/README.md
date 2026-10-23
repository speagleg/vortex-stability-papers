# Paper 2: Finite cores stabilise Thomson's heptagon

`paper/main.tex` builds to `paper/main.pdf` (pdflatex + bibtex). The code is in `code/` and the recorded outputs are in `outputs/`. `sh run_all.sh` regenerates the outputs; `sh run_all.sh --fast` runs a reduced set into `outputs/fast/`; its figures go to `outputs/fast/figures/`, never to `paper/figures/`. The full run rebuilds `paper/main.pdf` after the figures. The Lean library is `Heptagon` (`../../lean/Heptagon/`); build it with `lake build Heptagon`. The axiom audit is `outputs/lean_axioms.out`: only `propext`, `Classical.choice` and `Quot.sound` appear, and there is no `sorry`.

Status labels: **Proved** (by hand in the paper), **Lean**, **Certified** (exact computer arithmetic), **Derived** (formal asymptotics), **Numerical** (floating point).

## Claims

| Paper | Claim | Status | Proof / Lean theorem / script | Output |
|---|---|---|---|---|
| Lemma 2.1 | Spectrum of a Fourier block: det(λ − J B) = (λ + iϖ)² + a⊥a∥; imaginary iff a⊥a∥ > 0; unstable if a⊥a∥ < 0 | Proved; Lean | `Heptagon.BlockSpectrum`: `J_mul_block`, `charpoly_block`, `block_eigs_imaginary`, `block_unstable`, `block_eigs_explicit` | `lean_axioms.out` |
| Prop. 2.2 | Point-vortex blocks a⊥ = N−1−m(N−m)/2, a∥ = m(N−m)/2; heptagon (0, 6) | Proved; Lean | `Heptagon.RingBlocks.pv_blocks`, `heptagon_blocks`; `heptagon_pv_degenerate` | `lean_axioms.out` |
| Lemma 3.1 | Newton's theorem for log on circles: rigid discs act as points, so there is no r² term from centres | Lean (circles); the integration over radii is by hand | `Heptagon.Newton`: `circleAverage_log_far`, `circleAverage_log_two_circles` | `lean_axioms.out` |
| Lemma 3.2 | Energy of the m=2 shape mode: −Γ²\|ε\|²/4 + (Γr²/2)Re(Mε) | Proved (classical Kirchhoff–Love computation) | paper | — |
| Prop. 3.3 | Effective Hamiltonian H + (r⁴/4)Σ\|M_k\|² + O(r⁶); no r² term | **Derived** (adiabatic elimination, remainder order-counted). Its algebra is Lean | `Heptagon.Elimination`: `complete_square`, `elim_max`, `elim_at_max`, `patch_elimination`, `aspect_ratio`, `schur_elimination`. Not formalisable here: the Euler patch PDE and the slow-manifold reduction | — |
| Lemma 4.1 | Lattice sums T_a(n): periodicity, difference relation, zero sum, T_0, closed forms of T_1..T_4 for all N | Proved; Lean; also checked numerically to 50 digits | `Heptagon.LatticeSums`: `T_add_N`, `T_sub_succ`, `sum_T`, `T_zero`, `T_eq_of`, `T1_closed`…`T4_closed`, `sum_inv_one_sub`, `sum_inv_one_sub_sq`; `code/tsums.py` | `tsums.out` |
| Prop. 4.2 | Blocks of H_eff as lattice-sum expressions (Λ±, κ, μ, Ω₁ = −μ²) | Proved by hand (App. A); cross-checked by independent computer algebra | `code/blocks.py` (mechanical Taylor + Bloch reduction, exact), `code/plane_general.py` (symbolic N, m: identical) | `blocks.out`, `plane_general.out` |
| Thm 4.3 | Closed forms d⊥, d∥, dϖ(N, m), μ, Ω₁ for all N ≥ 2, 1 ≤ m ≤ N−1 | Lean (from the lattice-sum expressions) | `Heptagon.RingBlocks.r4_blocks` | `lean_axioms.out`, `plane_general.out` |
| Cor. 4.4 | Critical coefficient 𝔄_N(1) (even/odd closed forms); values; positive for N ≤ 7, negative for N ≥ 8 | Lean | `A_even`, `A_odd`, `A_values`, `A_even_neg`, `A_odd_neg` | `plane_general.out` |
| Cor. 4.5 | Heptagon: (a⊥, a∥, ϖ) = (14ε, 6+56ε, 16ε), Ω = −3−ε; truncated block has imaginary spectrum | Lean (algebra); **Derived** (conclusion "small-patch heptagon linearly stable") | `heptagon_blocks`, `heptagon_blocks_exp` (ζ = e^{2πi/7}), `heptagon_truncated_stable` | `blocks.out` |
| Rem. 3.4 | Existence of the steady patch heptagon: García (2021) Thm 1.1 covers every N ≥ 2, including N = 7. Her ansatz is N-fold symmetric, so the m = 3 degeneracy does not enter. Boundaries are at least C¹ | Checked against the arXiv text (literature) | paper | — |
| Rem. 4.6 | Only s₃ = −84r⁴ and ϖ₃ = 16r⁴ are determined; the individual r⁴ terms of λ± are not | Proved (order counting) | paper | `cd_asymptotics.out` |
| Result 5.1 / Table 1 | Contour dynamics reproduces the r⁴ coefficients for N = 4..8, all m (rel. error ≤ 8e−5) | Numerical | `code/cd.py`, `code/cd_asymptotics.py` | `cd_asymptotics.out` |
| Fig. 1 | Slow m=3 pair: s₃/a⁴ → −84, ϖ₃/a⁴ → 16 | Numerical | `code/figures.py` (from `cd_heptagon_scan.out`) | `paper/figures/fig_slowpair.pdf` |
| Result 5.2 | Steady heptagon is linearly stable for 0.02 ≤ r/R ≤ 0.26137 (Numerical); stability as r → 0 rests on Cor. 4.5 (Derived). Onset a_c ∈ [0.261377, 0.261379] (M = 193 and 257); complex quartet in blocks 2, 5 with Re λ ≈ 22.7√(a−a_c); second quartet in blocks 1, 6 from a ∈ [0.262194, 0.262197] (M = 129 and 193) | Numerical | `code/cd_heptagon_scan.py`, `code/cd_onset_m1.py` | `cd_heptagon_scan.out`, `cd_onset_m1.out` |
| §5.3 mechanism, Fig. 3 | Collision of a displacement mode (k = ±1) with an elliptical mode (k = ±2) in block m = 2 at Im λ ≈ −4.88 | Numerical | `code/cd_onset_modes.py`, `code/figures.py` | `cd_onset_modes.out`, `paper/figures/fig_onset.pdf` |
| §5.3 branch | Steady branch continued to r/R = 0.28019, where the smallest Newton singular value falls toward 0 (apparent fold; gap 0.41 r) | Numerical | `code/cd_onset_modes.py` | `cd_onset_modes.out` |
| Fig. 2 | Steady shapes at r/R = 0.1, 0.2, 0.2614 | Numerical | `code/figures.py` | `paper/figures/fig_shapes.pdf` |
| §7 (ii) | N = 7, m = 3 decomposition μ = −1, Λ₊ = 10, Λ₋ = 6, κ = 22, so d⊥ = 34 − 22 + 2 = 14. With frozen ellipses (or without the \|L\|² term): d⊥ = −20, d∥ = 22, i.e. unstable | Numerical (40-digit finite differences) + exact lattice sums | `code/frozen_check.py` | `frozen_check.out` |
| §5.4 | Spurious real eigenvalues explained: even-M Nyquist modes, split rotation Jordan pair (FD Jacobian), area modes | Numerical | `code/ngon_reviewer.py` (reviewer's code, unchanged), `code/cd.py` | `ngon_reviewer_a020.out`, `cd_heptagon_scan.out` (column `jordan`) |
| §5.4 referee (a) | Second linear code (Cauchy kernel, 4th-order FD Jacobian): same slow pair; onset in (0.2613, 0.2615); blocks 1, 6 Re λ = 1.07 at 0.265 | Numerical; independent referee code, **recorded, not rerun** | `code/ref_cd.py` | `ref_scan65.out`, `ref_scan97.out`, `ref_scan129.out` |
| §5.4 referee (b) | Nonlinear Lagrangian CD: the m = 3 perturbation stays bounded to t = 160 (about 9 slow periods) at r/R = 0.20, 0.15; spectral peaks match the eigenvalues | Numerical; referee code, **recorded, not rerun** (`fitfreq.py` rerun on the recorded series) | `code/ref_lagr.py`, `code/fitfreq.py` | `ref_lagr020.out`, `ref_lagr015.out`, `ref_fitfreq.out` |
| §5.4 referee (c) | Direct 40-digit differentiation of H_eff (no lattice sums): (14, 56, 16), Ω₁ = −1 for N = 7 | Numerical; referee code (rerun, < 1 s) | `code/heff_check.py` | `heff_check.out` |
| Prop. 6.1 | S² and H² (G model): 𝔄_N(y), 𝔇_N for N = 4..12 (𝔇₄ = 1/8, 𝔇₅ = −1, 𝔇₆ = −380/9; H²: −539/4, −244/3, −2880/49, −55, −179575/3528) | **Derived** (curved effective Hamiltonian); Certified (exact rational algebra given the model) | `code/curved.py` (uses `blocks.block_numeric`) | `curved.out` |
| (6.1) general N | Closed forms of 𝔄_N(y) and 𝔇_N for all N ≥ 4 (even/odd); evaluated at N = 4..12 they reproduce the per-N results of `curved.py` | Certified (exact symbolic algebra) given the **Derived** model; not Lean | `code/curved_general.py` (symbolic N) | `curved_general.out` |
| §6 signs | 𝔇_N from 𝔄_N; tabulated values; 𝔇_N < 0 for 5 ≤ N ≤ 27, N ≠ 7; 𝔇₄ > 0; 𝔇_N > 0 for N ≥ 28 | Lean (given the closed forms of 𝔄_N) | `Heptagon.Curved`: `D_from_A_even`, `D_from_A_odd`, `D_values`, `A_at_one_even`, `A_at_one_odd`, `D_neg_small`, `D4_pos`, `DEven_pos`, `DOdd_pos` | `lean_axioms.out` |
| §6 tanh | G₁ on H²: threshold ξ_* and shift 𝔇^tanh_N, N = 8..12 (all negative) | Numerical, given the **Derived** model | `code/tanh_check.py` | `tanh_check.out` |

## What Lean does not cover, and why

- **The effective Hamiltonian (Prop. 3.3) and the shape energy (Lemma 3.2).** These concern the Euler equations for patches, an infinite-dimensional free-boundary problem. The adiabatic elimination is a formal asymptotic argument with order-counted remainders. There is no theorem to formalise; Lean checks only its algebra.
- **The reduction of H_eff to lattice sums (Prop. 4.2).** It is a multivariable Taylor expansion followed by a Bloch evaluation. It is proved by hand and cross-checked by independent computer algebra (`blocks.py`). Formalising multivariate Taylor coefficients of this function in Mathlib would be a large project, so Lean starts from the lattice-sum expressions.
- **The curved closed forms of 𝔄_N(y).** These come from exact computer algebra; Lean checks only what follows from them.
- **Contour dynamics.** These are floating-point numerics and are not formalisable.

## Code provenance

All Python in `code/` was written for this paper, with these exceptions, each copied unmodified apart from a provenance header:

- `ngon_reviewer.py`: the independent reviewer's code.
- `ref_cd.py`, `ref_lagr.py`, `heff_check.py`, `fitfreq.py`: the independent referee's code. Their long runs are recorded, not rerun (`outputs/ref_*.out`).

 `cd.py` follows its design (polar-graph boundaries, Kress quadrature, Newton solve) and adds odd M, a complex-step Jacobian, Bloch blocks, and the area and rotation-Jordan quotients. Some of the models build on the author's earlier research code, which is unpublished; nothing is imported from it.

## Recorded, not rerun

The referee outputs `outputs/ref_scan*.out` and `outputs/ref_lagr*.out` are recorded, not rerun; they are copied from the referee's run. Every other output in `outputs/` was produced by the scripts here.

In `outputs/cd_asymptotics.out`, `cd_heptagon_scan.out`, `cd_onset_modes.out` and `curved.out` (and their `fast/` copies), the header text naming the unit convention was renamed to "normalised units" after the run. Only the label text was edited; the numbers are unchanged. The full `run_all.sh` takes a few hours, dominated by `cd_heptagon_scan.py`, `cd_onset_modes.py`, `curved_general.py` and `tanh_check.py`.
