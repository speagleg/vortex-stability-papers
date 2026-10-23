/-
New module for paper 01-conjecture-13 (not copied).

The bracket `{J₁, J₂}` of paper §2.4. For one vortex with area form `Ω = 2σ⁻² dx∧dy`, `σ = 1 + λ(x²+y²)`, the
Poisson bracket of two functions is `{f, g} = (σ²/2)(f_x g_y − f_y g_x)` (the definition of the Poisson
structure of `Ω`; stated here, not derived). With `J₁ = x/σ`, `J₂ = y/σ` we compute the four partial
derivatives (genuine derivatives) and the bracket: `{J₁, J₂} = 1/2 − λ(x²+y²)/σ`. Summing over the vortices gives
`{J₁, J₂} = n/2 − λJ₃` (`bracket_sum`), whose value at the ring is `Conj13.bracket_value`.
-/
import Conj13.Algebra

namespace Conj13.Bracket

noncomputable section

/-- `σ = 1 + λ(x² + y²)`. -/
def sig (l x y : ℝ) : ℝ := 1 + l * (x ^ 2 + y ^ 2)

theorem hasDerivAt_J1_x (l x y : ℝ) (h : sig l x y ≠ 0) :
    HasDerivAt (fun x' => x' / sig l x' y) ((sig l x y - 2 * l * x ^ 2) / sig l x y ^ 2) x := by
  have hd : HasDerivAt (fun x' => sig l x' y) (l * (2 * x)) x := by
    unfold sig
    have := (((hasDerivAt_pow 2 x).add_const (y ^ 2)).const_mul l).const_add 1
    simpa using this
  have := (hasDerivAt_id' x).div hd h
  convert this using 1
  ring

theorem hasDerivAt_J1_y (l x y : ℝ) (h : sig l x y ≠ 0) :
    HasDerivAt (fun y' => x / sig l x y') (-(2 * l * x * y) / sig l x y ^ 2) y := by
  have hd : HasDerivAt (fun y' => sig l x y') (l * (2 * y)) y := by
    unfold sig
    have := ((((hasDerivAt_pow 2 y).const_add (x ^ 2))).const_mul l).const_add 1
    simpa using this
  have := (hasDerivAt_const y x).div hd h
  convert this using 1
  field_simp
  ring

theorem hasDerivAt_J2_x (l x y : ℝ) (h : sig l x y ≠ 0) :
    HasDerivAt (fun x' => y / sig l x' y) (-(2 * l * x * y) / sig l x y ^ 2) x := by
  have hd : HasDerivAt (fun x' => sig l x' y) (l * (2 * x)) x := by
    unfold sig
    have := (((hasDerivAt_pow 2 x).add_const (y ^ 2)).const_mul l).const_add 1
    simpa using this
  have := (hasDerivAt_const x y).div hd h
  convert this using 1
  field_simp
  ring

theorem hasDerivAt_J2_y (l x y : ℝ) (h : sig l x y ≠ 0) :
    HasDerivAt (fun y' => y' / sig l x y') ((sig l x y - 2 * l * y ^ 2) / sig l x y ^ 2) y := by
  have hd : HasDerivAt (fun y' => sig l x y') (l * (2 * y)) y := by
    unfold sig
    have := ((((hasDerivAt_pow 2 y).const_add (x ^ 2))).const_mul l).const_add 1
    simpa using this
  have := (hasDerivAt_id' y).div hd h
  convert this using 1
  ring

/-- **One vortex**: `(σ²/2)(∂ₓJ₁ ∂ᵧJ₂ − ∂ᵧJ₁ ∂ₓJ₂) = 1/2 − λ(x²+y²)/σ`, with the partial derivatives of
`hasDerivAt_J1_x` … `hasDerivAt_J2_y`. -/
theorem bracket_one (l x y : ℝ) (h : sig l x y ≠ 0) :
    sig l x y ^ 2 / 2 * ((sig l x y - 2 * l * x ^ 2) / sig l x y ^ 2
        * ((sig l x y - 2 * l * y ^ 2) / sig l x y ^ 2)
      - (-(2 * l * x * y) / sig l x y ^ 2) * (-(2 * l * x * y) / sig l x y ^ 2))
      = 1 / 2 - l * (x ^ 2 + y ^ 2) / sig l x y := by
  have h' := h
  unfold sig at h' ⊢
  field_simp
  ring

/-- **All vortices**: `{J₁, J₂} = Σ_k (1/2 − λ|z_k|²/σ_k) = n/2 − λJ₃`. -/
theorem bracket_sum {n : ℕ} (l : ℝ) (x y : Fin n → ℝ) :
    ∑ k, (1 / 2 - l * (x k ^ 2 + y k ^ 2) / sig l (x k) (y k))
      = n / 2 - l * ∑ k, (x k ^ 2 + y k ^ 2) / sig l (x k) (y k) := by
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun k _ => ?_; ring

end

end Conj13.Bracket
