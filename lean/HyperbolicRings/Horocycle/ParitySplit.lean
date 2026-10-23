/-
New in this paper (vortex-stability-papers, paper 3). Not copied from the source repositories.

The ingredient that separates the even-N and odd-N ring threshold germs at the horocycle point
(paper, Theorem "three germs", part (c)).

The second-order constants of the large-N threshold differ by parity only through the term
`-(1/2) ∂²ψ/∂x²(0, τ∞)` (paper, Proposition "second order"). Here we prove:

* `hasDerivAt_psi_x`: `∂²ψ/∂x²(0,τ) = -1/4 + (τ² cosh τ - 2τ sinh τ)/(4 sinh² τ)` (as the derivative at
  `0` of the `x`-derivative of `ψ` given by `hasDerivAt_psi`);
* `psiXX_tauInf_neg`: this value is negative at `τ = τ∞`, so `-(1/2) ψ_xx(0,τ∞) > 0`.

The second-order expansion itself (implicit function theorem for a real-analytic function) is by
hand in the paper and is not formalised here.
-/
import HyperbolicRings.Tanh.LargeN.CritMode
import HyperbolicRings.Tanh.LargeN.PhiLimit

noncomputable section

namespace HyperbolicRings.Horocycle

open Real HyperbolicRings.Tanh.LargeN

/-- The `x`-derivative of `ψ(·,τ)` (from `hasDerivAt_psi`). -/
def psiX (τ x : ℝ) : ℝ :=
  -(x / 4) + (τ * cosh τ * sinh (x * τ) - sinh τ * sinh (x * τ)
    - x * τ * sinh τ * cosh (x * τ)) / (4 * sinh τ ^ 2)

/-- `ψ_xx(0,τ)`. -/
def psiXX0 (τ : ℝ) : ℝ := -1 / 4 + (τ ^ 2 * cosh τ - 2 * τ * sinh τ) / (4 * sinh τ ^ 2)

theorem deriv_psi_eq (τ : ℝ) : deriv (fun y => psi y τ) = psiX τ := by
  funext x; exact (hasDerivAt_psi x τ).deriv

/-- `∂²ψ/∂x²(0,τ) = psiXX0 τ`. -/
theorem hasDerivAt_psi_x (τ : ℝ) : HasDerivAt (psiX τ) (psiXX0 τ) 0 := by
  have h1 : HasDerivAt (fun y : ℝ => y * τ) τ 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const τ
  have hc := (hasDerivAt_cosh ((0 : ℝ) * τ)).comp (0 : ℝ) h1
  have hs := (hasDerivAt_sinh ((0 : ℝ) * τ)).comp (0 : ℝ) h1
  have hA := (hs.const_mul (τ * cosh τ)).sub (hs.const_mul (sinh τ))
  have hB := (((hasDerivAt_id (0 : ℝ)).mul_const (τ * sinh τ)).mul hc)
  have hT := ((hA.sub hB).div_const (4 * sinh τ ^ 2))
  have hL := ((hasDerivAt_id (0 : ℝ)).div_const 4).neg
  have := hL.add hT
  convert this using 1
  · funext y
    simp only [psiX, Function.comp, id, Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  · simp [psiXX0]; ring

theorem second_deriv_psi (τ : ℝ) :
    deriv (deriv (fun y => psi y τ)) 0 = psiXX0 τ := by
  rw [deriv_psi_eq]; exact (hasDerivAt_psi_x τ).deriv

/-- `sinh τ ≥ 2 τ²` on the bracket of `τ∞`. -/
theorem sinh_ge_two_sq {τ : ℝ} (h1 : 74453 / 10000 < τ) (h2 : τ < 74454 / 10000) :
    2 * τ ^ 2 ≤ sinh τ := by
  have hτ : 0 ≤ τ := by linarith
  have he := Real.pow_div_factorial_le_exp τ hτ 6
  have hne : exp (-τ) ≤ 1 := by
    have := Real.exp_le_exp.mpr (show -τ ≤ 0 by linarith); simpa using this
  rw [Real.sinh_eq]
  have h6 : (74453 / 10000 : ℝ) ^ 6 ≤ τ ^ 6 := pow_le_pow_left₀ (by norm_num) h1.le 6
  have hf : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [hf] at he
  nlinarith

/-- `ψ_xx(0,τ∞) < 0`: the parity term `-(1/2)ψ_xx(0,τ∞)` is positive. -/
theorem psiXX_tauInf_neg : psiXX0 tauInf < 0 := by
  obtain ⟨h1, h2⟩ := tauInf_bracket
  set τ := tauInf
  have hτ : 1 ≤ τ := by linarith
  have hS := sinh_ge_two_sq h1 h2
  have hSpos : 0 < sinh τ := by nlinarith
  have hcs : cosh τ ≤ sinh τ + 1 := by
    rw [Real.cosh_eq, Real.sinh_eq]
    have : exp (-τ) ≤ 1 := by
      have := Real.exp_le_exp.mpr (show -τ ≤ 0 by linarith); simpa using this
    linarith
  unfold psiXX0
  have hden : 0 < 4 * sinh τ ^ 2 := by positivity
  rw [show -1 / 4 + (τ ^ 2 * cosh τ - 2 * τ * sinh τ) / (4 * sinh τ ^ 2)
      = (τ ^ 2 * cosh τ - 2 * τ * sinh τ - sinh τ ^ 2) / (4 * sinh τ ^ 2) by field_simp; ring]
  apply div_neg_of_neg_of_pos _ hden
  have hτ2 : 0 < τ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcs hτ2.le, mul_nonneg (by linarith : (0:ℝ) ≤ τ) hSpos.le]

end HyperbolicRings.Horocycle
