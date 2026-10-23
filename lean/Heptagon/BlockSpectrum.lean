/-
Paper 2 (finite-core heptagon), Lemma 2.1 and Corollary 4.5: the spectrum of a Hermitian Fourier block
B = [[a, iϖ], [-iϖ, b]] under the canonical symplectic matrix J = [[0, 1], [-1, 0]].

The linearised flow on a Bloch block is d/dt (ŝ, ϑ̂) = J B (ŝ, ϑ̂); we prove that
det(λ - J B) = (λ + iϖ)^2 + a b, so the eigenvalues are λ = -iϖ ± sqrt(-ab); all eigenvalues are purely
imaginary when ab > 0, and one has positive real part when ab < 0.  Applied to the truncated heptagon
block (a, b, ϖ) = (14ε, 6 + 56ε, 16ε), ε = r⁴ > 0, this gives spectral stability of the truncated block.
What is not proved here: that the true patch dynamics is governed by this truncated block up to O(r⁶)
(formal asymptotics, Proposition 3.3), and nonlinear stability.  Written for this paper (no source module).
-/
import Mathlib

namespace Heptagon

open Complex Matrix

/-- The Hermitian Fourier block. -/
def blockB (a b w : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(a : ℂ), I * w; -I * w, (b : ℂ)]
/-- The canonical symplectic matrix. -/
def Jstd : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- The generator of the linearised flow on the block. -/
theorem J_mul_block (a b w : ℝ) :
    Jstd * blockB a b w = !![-I * w, (b : ℂ); -(a : ℂ), -I * w] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jstd, blockB, Matrix.mul_apply, Fin.sum_univ_two]

/-- Characteristic polynomial of the block generator. -/
theorem charpoly_block (a b w : ℝ) (lam : ℂ) :
    (lam • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Jstd * blockB a b w).det = (lam + I * w) ^ 2 + a * b := by
  rw [J_mul_block, Matrix.det_fin_two]
  simp [Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- If `μ² = -c` with `c > 0` then `Re μ = 0`. -/
lemma re_eq_zero_of_sq_neg {μ : ℂ} {c : ℝ} (hc : 0 < c) (h : μ ^ 2 = -(c : ℂ)) : μ.re = 0 := by
  have hre : (μ ^ 2).re = -c := by rw [h]; simp
  have him : (μ ^ 2).im = 0 := by rw [h]; simp
  rw [pow_two, mul_re] at hre
  rw [pow_two, mul_im] at him
  by_contra hne
  have him' : μ.im = 0 := by
    have : 2 * μ.re * μ.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd (by linarith : μ.re = 0) hne
    · exact h1
  rw [him'] at hre
  nlinarith [sq_nonneg μ.re]

/-- Stability criterion of a block: if `a b > 0`, every eigenvalue of `J B` is purely imaginary. -/
theorem block_eigs_imaginary (a b w : ℝ) (hab : 0 < a * b) (lam : ℂ)
    (hl : (lam • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Jstd * blockB a b w).det = 0) : lam.re = 0 := by
  rw [charpoly_block] at hl
  have h : (lam + I * w) ^ 2 = -((a * b : ℝ) : ℂ) := by
    push_cast; linear_combination hl
  have := re_eq_zero_of_sq_neg hab h
  simpa using this

/-- Instability criterion: if `a b < 0`, `J B` has an eigenvalue with positive real part. -/
theorem block_unstable (a b w : ℝ) (hab : a * b < 0) :
    ∃ lam : ℂ, (lam • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Jstd * blockB a b w).det = 0 ∧ 0 < lam.re := by
  refine ⟨(Real.sqrt (-(a * b)) : ℂ) - I * w, ?_, ?_⟩
  · rw [charpoly_block]
    have hs : (Real.sqrt (-(a * b)) : ℂ) ^ 2 = -((a : ℂ) * b) := by
      rw [← ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
    linear_combination hs
  · simp only [sub_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
    have : 0 < Real.sqrt (-(a * b)) := Real.sqrt_pos.mpr (by linarith)
    linarith

/-- The two eigenvalues are `-iϖ ± i sqrt(ab)` when `ab ≥ 0`. -/
theorem block_eigs_explicit (a b w : ℝ) (hab : 0 ≤ a * b) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    let lam : ℂ := I * (-(w : ℂ) + s * Real.sqrt (a * b))
    (lam • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Jstd * blockB a b w).det = 0 := by
  intro lam
  rw [charpoly_block]
  have hq : (Real.sqrt (a * b) : ℂ) ^ 2 = (a : ℂ) * b := by
    rw [← ofReal_pow, Real.sq_sqrt hab]; push_cast; ring
  have hs2 : (s : ℂ) ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  simp only [lam]
  linear_combination (-(s : ℂ) ^ 2) * hq + (-(a : ℂ) * b) * hs2 + I_sq * ((s:ℂ) ^ 2 * (Real.sqrt (a * b) : ℂ) ^ 2)

/-- Corollary 4.5 (truncated heptagon block): for `ε = r⁴ > 0` the block
`(a_⊥, a_∥, ϖ) = (14 ε, 6 + 56 ε, 16 ε)` has only purely imaginary eigenvalues, namely
`i (-16 ε ± sqrt(14 ε (6 + 56 ε)))`. -/
theorem heptagon_truncated_stable (ε : ℝ) (hε : 0 < ε) (lam : ℂ)
    (hl : (lam • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Jstd * blockB (14 * ε) (6 + 56 * ε) (16 * ε)).det = 0) :
    lam.re = 0 :=
  block_eigs_imaginary _ _ _ (by positivity) lam hl

/-- Without the core correction (`ε = 0`) the heptagon block is degenerate: `λ = 0` is a double root. -/
theorem heptagon_pv_degenerate :
    ((0 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Jstd * blockB 0 6 0).det = 0 := by
  rw [charpoly_block]; simp

end Heptagon
