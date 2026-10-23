# Vortex stability papers

Three short papers on one classical question: **when is a symmetric arrangement of vortices stable?** Each paper settles one case that was open, or wrongly settled, in the literature. This repository contains everything needed to check them:

- the papers;
- the Lean 4 proofs;
- the exact and interval-arithmetic certificates;
- the numerical experiments.

| # | Paper | Result | PDF |
|---|---|---|---|
| 1 | *The regular n-gon of point vortices is stable at its bifurcation point* | Proves Montaldi–Tokieda's Conjecture 13 for every n ≥ 4, and corrects their published even-n argument. | [`papers/01-conjecture-13/paper/main.pdf`](papers/01-conjecture-13/paper/main.pdf) |
| 2 | *Finite cores stabilise Thomson's heptagon* | Seven small vortex patches in a ring are linearly stable. This contradicts Dhanak (1992) and a reported result of Dritschel (1985). | [`papers/02-finite-core-heptagon/paper/main.pdf`](papers/02-finite-core-heptagon/paper/main.pdf) |
| 3 | *Vortex rings and rows on the hyperbolic plane* | Exact stability theory for Kimura's model, a problem Montaldi–Tokieda called "no longer tractable analytically". Ring and row stability boundaries meet at one point. | [`papers/03-hyperbolic-rings-rows/paper/main.pdf`](papers/03-hyperbolic-rings-rows/paper/main.pdf) |

---

## 1. Background in five minutes

**Point vortices.** In an ideal two-dimensional fluid, swirl can be concentrated at points. Each such *point vortex* moves with the velocity that the others induce at its position. The motion is a Hamiltonian system:

- the energy is a sum of pairwise interactions, given by the Green function of the surface;
- rotation symmetry gives a conserved *momentum*.

**Rings.** Place N identical vortices at the corners of a regular N-gon. The ring rotates rigidly, which makes it a *relative equilibrium*. The question is whether a small nudge stays small or grows.

**The classical answer.** On the flat plane, Thomson (1883) and Havelock (1931) found:

- N ≤ 6: stable;
- N = 7: exactly on the stability boundary (degenerate);
- N ≥ 8: unstable.

Curvature moves the boundary. On a sphere it shifts to smaller rings. On the hyperbolic plane, large rings become stable.

**What "stable" means.** The papers keep three notions separate:

| Notion | Meaning | Used in |
|---|---|---|
| Spectral (linear) stability | The linearised dynamics has no growing modes. | Papers 2 and 3 |
| Energy–momentum stability | The energy at fixed momentum has a strict minimum, so it serves as a Lyapunov function. This implies nonlinear stability, but it can miss stable cases (see the Krein windows in paper 3). | Papers 1 and 3 |
| Lyapunov stability modulo rotation | Solutions that start near the ring stay near the rotating ring for all time. This is the strongest of the three. | Paper 1 proves this |

**Why these cases are hard.** At a stability boundary the quadratic (linear) test gives zero, so higher-order terms decide stability. All three papers work at or near such boundaries.

---

## 2. The three results, and how each was established

### Paper 1: Conjecture 13 (rings exactly at their bifurcation point)

**Question.** Montaldi and Tokieda put the sphere, the plane and the hyperbolic plane into one family, with a curvature parameter b. A ring of n vortices changes stability at an explicit value b_n. Is the ring still stable *at* b_n?

They conjectured that it is (Conjecture 13, arXiv:1210.5662). They had argued the even case and checked a few small odd n numerically.

**Answer.** Yes, for every n ≥ 4. The ring is Lyapunov stable modulo rotations, for perturbations of any momentum.

**How it is argued.**

1. **Reduction.** Remove the rotation symmetry and fix the momentum. At b_n the reduced energy has a degenerate minimum: its Hessian is positive semidefinite, with a one- or two-dimensional kernel.
2. **The quartic decides.** Stability is governed by a fourth-order coefficient c₄, computed on the momentum level set. Its closed form is:
   - c₄ = (n−2)(m⁴+40m²+48m+16)/(192n(n−1)) for even n, with m = n−2;
   - c₄ = (n−1)(n−3)(n²−9n+38)/(128n) for odd n.

   Both are positive.
3. **Degenerate energy–momentum argument.** A strict quartic minimum, plus a quadratic penalty in the momentum, gives a Lyapunov function. This standard argument (Patrick 1992; Ortega–Ratiu) is written out in abstract form.
4. **Correction to the original argument.** For even n, Montaldi–Tokieda expand along a straight line that leaves the momentum level set. The level set bends at second order into a direction where the Hessian is not zero, and that bending contributes at fourth order. Their quartic has the right sign but the wrong value: at n = 4 it is 6 − 4√3/3 ≈ 3.69, while the true value is 4.

**What is checked how.**

| Part | Status |
|---|---|
| Threshold b_n; Fourier blocks of the Hessian, derived from the Hamiltonian | **Lean** |
| Fourth-order expansions along the even and odd curves; closed forms and positivity of c₄ for all n; all table entries | **Lean** |
| Comparison with Montaldi–Tokieda's line, including the n = 4 values | **Lean** |
| The abstract Lyapunov lemmas | **Lean** |
| Symplectic reduction, chart independence, symmetric criticality, the slicing lemma, and existence of the vortex flow | **Proved** by hand. Mathlib has no symplectic reduction or point-vortex dynamics. |
| The c₄ table, independently recomputed | **Numerical**: an 80-digit level-set minimisation, and an exact computation modulo three primes with no symmetry assumptions. This is strong evidence; the proof does not rely on it. |
| A long nonlinear integration at n = 8 | **Numerical** illustration |

64 Lean theorems are cited and audited.

### Paper 2: Finite cores stabilise Thomson's heptagon

**Question.** Thomson's heptagon of *point* vortices sits exactly on the stability boundary. Real vortices have cores. Replace each point by a small uniform patch of radius r on a ring of radius R. Which way does the degeneracy break?

**Answer.** Towards stability. The deciding coefficient is a⊥ = +14(r/R)⁴ > 0.

Contour dynamics finds the steady heptagon of patches linearly stable for 0.02 ≤ r/R < 0.26138 (0.02 is the smallest value computed). At about 0.26138 an elliptical shape mode collides with a displacement mode, and the ring becomes unstable.

**How it is argued.**

1. **Effective Hamiltonian.** The strain from the other patches deforms each patch into an ellipse. Eliminating these fast shape modes adiabatically gives H + (r⁴/4)Σ|M_k|². There is no (r/R)² term. This step is formal asymptotics, so it is labelled **Derived**, not proved.
2. **Lattice sums.** For every N and every mode, the order-(r/R)⁴ stability blocks reduce to sums over roots of unity, which have explicit closed forms. For N = 7 the critical coefficient comes from a cancellation: 34 − 22 + 2 = 14.
3. **Independent numerical confirmation.**
   - The paper's contour-dynamics code reproduces every (r/R)⁴ coefficient for N = 4–8 to about four significant figures.
   - An independent referee's code, written from scratch, reproduces stability and brackets the onset in (0.2613, 0.2615).
   - The referee's nonlinear simulations show an m = 3 perturbation staying bounded for about nine slow periods.

**What is checked how.**

| Part | Status |
|---|---|
| Newton's theorem for averages on circles; the algebra of the elimination and Schur complement | **Lean** |
| Closed forms of the lattice sums; the block polynomials for all N; the heptagon values (14, 56, 16); the reduction of stability to the sign of a⊥ | **Lean** |
| Reduction to the lattice-sum form, which the Lean algebra starts from | By hand plus computer algebra |
| The effective Hamiltonian | **Derived** (formal asymptotics) |
| Stability of the patch heptagon | **Derived** at small r; **Numerical** at finite r |

**The conflict with the literature.** Dhanak (JFM 1992) states that small finite cores make N ≥ 7 unstable. Polvani–Dritschel (1993) and Llewellyn Smith–Crowdy (2012) report the same of Dritschel's 1985 computations.

We could not obtain Dhanak's full text, so the paper does not claim to locate his error. It does give a concrete candidate. If the ellipses are frozen instead of following the strain, the critical coefficient changes from +14 to −20 and the heptagon comes out unstable. This was checked by direct 40-digit differentiation of both models.

The paper also gives the corresponding (r/R)⁴ threshold shifts on the sphere and the hyperbolic plane.

38 Lean theorems are cited and audited.

### Paper 3: Vortex rings and rows on the hyperbolic plane

**Question.** On the hyperbolic plane, with its true Green function −log tanh(d/2) (Kimura's model), which rings are stable?

- Boatto (2008) set up the problem and computed stability ranges numerically.
- Montaldi–Tokieda (2012) called it no longer tractable analytically.

The paper also asks the same question for infinite rows of vortices along horocycles and hypercycles, the hyperbolic analogues of straight lines.

**Answer.**

- **Rings.**
  - N ≤ 7 is stable at every radius.
  - Every N ≥ 8 has exactly one threshold radius. It is an algebraic number, certified to 45 digits for N = 8–16.
  - For odd N there is a tiny window, about 10⁻⁸ to 10⁻⁷ wide, where the ring is spectrally stable but the energy test fails. The two critical frequencies carry opposite Krein signatures. A definiteness criterion such as Boatto's cannot detect this.
- **Large rings.** The threshold spacing tends to ℓ* = 2π/τ∞ ≈ 0.843908, which is exactly the critical spacing of an infinite vortex row on a horocycle.
- **Hypercycle rows.**
  - A row is unstable at every spacing iff its curvature satisfies |κ| ≤ 1/√2.
  - Above that, it is stable beyond a single threshold. The threshold curve runs from infinity at κ = 1/√2 to the horocycle point.
  - At that point the curve has a square-root branch point, and rings of even and odd N arrive with different slopes. So a single stability boundary passes through the horocycle and does not continue analytically.

**How it is argued.**

1. **Rings.** The Hessian splits into 2×2 Fourier blocks that are rational in ξ = tanh²(r/2). The critical mode is ⌊N/2⌋. Positivity certificates handle N ≤ 7, and monotonicity in ξ gives uniqueness of the threshold for N ≥ 8.
2. **Large N.** The ring's blocks converge to the Bloch symbol of the horocycle row.
3. **Rows.** The row's Bloch symbol is derived from the pair interaction. The pairing mode q = π is shown to be the most dangerous. The 1/√2 criterion then follows from a one-line bound.
4. **Single threshold.** Interval arithmetic (Arb) certifies that the hypercycle threshold is unique. For dense rows it uses analytic bounds proved in Appendix E, together with a dual-series identity proved by Fourier analysis and Poisson summation in Appendix D.

**What is checked how.**

| Part | Status |
|---|---|
| Rings: blocks derived from the Hamiltonian, linearisation, N ≤ 7, a unique threshold for every N ≥ 8, intervals of width 10⁻²⁰ around each threshold for N = 8–16, irreducibility, the Krein window and its signatures | **Lean** |
| Horocycle row: large-N rates, the symbol, the critical spacing | **Lean** |
| Hypercycle rows: the Bloch symbol, the critical mode, the 1/√2 theorem, monotonicity in curvature, the limit to the horocycle row, instability of dense rows | **Lean** |
| Uniqueness of the hypercycle threshold | **Certified** (about 15,000 interval boxes) |
| Analyticity results that need the analytic implicit function theorem (Mathlib has only the C¹ version), and the dual series (which needs a residue computation Mathlib lacks) | **Proved** by hand |
| Decimal values | **Numerical** |

120 Lean theorems are cited and audited.

---

## 3. Status labels

Every claim in every paper carries one label. Each paper's README has a table mapping every theorem, table and figure to its label, its proof, Lean theorem or script, and its output file.

| Label | Meaning | How to check |
|---|---|---|
| **Lean** | Machine-checked in Lean 4 with Mathlib. | Build the library and read the axiom audit (§6). |
| **Proved** | A complete proof by hand in the paper. | Read the proof. |
| **Certified** | Computer-assisted with exact or interval arithmetic; the computation is itself a proof. | Rerun the script and compare with the recorded output. |
| **Derived** | Formal asymptotics: a careful calculation, but not a proof. | Read the derivation and compare with the numerics. |
| **Numerical** | Floating-point evidence. | Rerun the script. |

A weaker label is never presented as a stronger one. Where a Lean theorem takes something as a hypothesis or modelling input, the paper and the README name it. Examples are the Poisson structure of the vortex system, Hamilton's equations in a given chart, and existence of the flow.

**What is not in Lean, and why.** The README tables give a reason for every claim that is not in Lean. The main gaps are:

- **Tools Mathlib lacks:** symplectic reduction, point-vortex flows, PDE asymptotics for vortex patches, the analytic implicit function theorem, and certain residue computations.
- **Interval certificates:** about 15,000 boxes, which would need verified interval arithmetic inside Lean.
- **Floating-point numerics:** inherently outside Lean.

---

## 4. Review

Before being committed, each paper went through two independent reviews:

1. A novelty check against the literature, reading full texts where they could be obtained.
2. An adversarial referee, who rebuilt the Lean, reran the scripts and recomputed the key numbers independently.

| Paper | Referee's independent recomputation | Verdict |
|---|---|---|
| 1 | c₄ by a symmetry-free Cartesian optimisation; the n = 4 discrepancy with Montaldi–Tokieda | Minor revision; fixes applied |
| 2 | The heptagon with a second contour-dynamics code and nonlinear simulation; the coefficients 14, 56, 16 and −84 by direct differentiation | Minor revision; fixes applied |
| 3 | Every step of the new appendices checked by hand; certificates rerun | Minor revision; re-reviewed after fixes, minor again; fixes applied |

**No human specialist has refereed these papers yet.** The reviews above were carried out by AI agents, and the papers say so.

---

## 5. Repository map

```
README.md                          this file
lean/                              one Lake project: Lean v4.34.1, Mathlib v4.34.1
  Conj13.lean, Conj13/             paper 1
  Heptagon.lean, Heptagon/         paper 2
  HyperbolicRings.lean, HyperbolicRings/   paper 3
  */Audit.lean                     #print axioms for every theorem a paper cites (not imported by the library roots)
papers/NN-name/
  paper/                           main.tex, refs.bib, figures/, main.pdf
  code/                            self-contained Python; copied files carry a "# Provenance:" header
  outputs/                         recorded output of every script, lean_axioms.out, build logs
  run_all.sh                       regenerates the outputs (--fast skips the slow jobs)
  README.md                        claim → status → proof / Lean theorem / script → output
```

---

## 6. Reproducing

### Lean

```sh
cd lean
lake exe cache get                # on a fresh machine only: fetch Mathlib build artefacts
lake build Conj13 Heptagon HyperbolicRings
lake env lean Conj13/Audit.lean   # likewise Heptagon/Audit.lean and HyperbolicRings/Audit.lean
```

- Each audit lists the axioms behind every cited theorem. Only Lean's standard axioms appear: `propext`, `Classical.choice` and `Quot.sound`.
- There is no `sorry`, no new `axiom` and no `native_decide`.
- The first build of `HyperbolicRings` takes about 20 minutes, because of its certificate modules.
- On the author's machine, `lean/.lake/packages` is symlinked to a prebuilt Mathlib. Git does not track it.

### Python

Python 3 with numpy, scipy, sympy, mpmath, python-flint and matplotlib. Set `PY` to choose the interpreter.

```sh
cd papers/01-conjecture-13
sh run_all.sh --fast    # a few minutes per paper
sh run_all.sh           # everything, including the slow jobs
```

Each paper's README lists:

- every script and its runtime;
- which outputs are recorded rather than rerun (only a few long jobs).

Almost every output was regenerated here.

### LaTeX

In each `paper/` directory:

```sh
pdflatex main && bibtex main && pdflatex main && pdflatex main
```

---

## 7. Provenance and disclosure

- Papers 1 and 3 grew out of the author's earlier work in [`havelock-vortex-rings`](https://github.com/speagleg/havelock-vortex-rings). Code and Lean files copied from there name their source file and commit.
- The remaining code comes from the author's earlier unpublished research and was adapted here.
- Everything the papers rely on is in this repository.
- The research, papers, proofs and code were developed with substantial AI assistance (Anthropic's Claude), under the direction of Gordon Speagle. Each paper has a disclosure section.

**Author:** Gordon Speagle, independent researcher, Boise, Idaho.
