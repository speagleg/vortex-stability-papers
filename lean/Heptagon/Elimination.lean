/-
Paper 2 (finite-core heptagon), Lemma 3.2 and Proposition 3.3: the algebra of the adiabatic
elimination of the elliptical (m = 2) shape mode.

(1) Scalar/complex elimination.  The energy of a patch of circulation Γ and radius r whose boundary is
r(1 + Re(ε e^{-2iθ})), in an external stream function with complex trace-free Hessian M, is, to second
order in ε, E(ε) = -(Γ²/4)|ε|² + (Γ r²/2) Re(M ε) (Lemma 3.2, by hand).  Its stationary point is
ε* = r² conj(M)/Γ and E(ε*) = r⁴ |M|²/4, independent of Γ; this is the r⁴ term of the effective Hamiltonian.
The aspect ratio of the stationary ellipse is (1 + |ε*|)/(1 - |ε*|) = 1 + 2 r²|M|/Γ + O(r⁴).

(2) Schur complement.  For a quadratic form Q(x, y) = xᵀAx + 2xᵀBy + yᵀCy with C invertible and symmetric,
the stationary point in y is y* = -C⁻¹Bᵀx and Q(x, y*) = xᵀ(A - B C⁻¹ Bᵀ)x.

What is not proved here: the energy formula E(ε) (a classical Kirchhoff–Love computation, by hand in the
paper) and the claim that the slow dynamics follows the stationary shape (formal adiabatic elimination).
Written for this paper (no source module).
-/
import Mathlib

set_option autoImplicit false

namespace Heptagon

open Complex ComplexConjugate

/-- Completing the square: `-α|ε|² + Re(conj c · ε) = |c|²/(4α) - α|ε - c/(2α)|²`. -/
theorem complete_square (α : ℝ) (hα : α ≠ 0) (c ε : ℂ) :
    -α * normSq ε + (conj c * ε).re = normSq c / (4 * α) - α * normSq (ε - c / (2 * α)) := by
  simp only [normSq_apply, mul_re, conj_re, conj_im, sub_re, sub_im, div_re, div_im]
  have h2 : ((2 : ℂ) * α).re = 2 * α := by simp
  have h3 : ((2 : ℂ) * α).im = 0 := by simp
  simp only [h2, h3, normSq_apply, mul_re, mul_im, re_ofNat, im_ofNat, ofReal_re, ofReal_im]
  field_simp
  ring

/-- The maximum of `E(ε) = -α|ε|² + Re(conj c · ε)` (α > 0) is `|c|²/(4α)`, attained at `ε = c/(2α)`. -/
theorem elim_max (α : ℝ) (hα : 0 < α) (c ε : ℂ) :
    -α * normSq ε + (conj c * ε).re ≤ normSq c / (4 * α) := by
  rw [complete_square α hα.ne' c ε]
  have := normSq_nonneg (ε - c / (2 * α))
  nlinarith

theorem elim_at_max (α : ℝ) (hα : 0 < α) (c : ℂ) :
    -α * normSq (c / (2 * α)) + (conj c * (c / (2 * α))).re = normSq c / (4 * α) := by
  rw [complete_square α hα.ne' c]; simp

/-- Proposition 3.3 (algebra): with `α = Γ²/4` and `c = Γ r² M̄/2` (stated for any `M`, apply it to `M̄`), the eliminated energy is `r⁴|M|²/4`
and the stationary amplitude is `r² M/Γ`. -/
theorem patch_elimination (Γ r : ℝ) (hΓ : Γ ≠ 0) (M : ℂ) :
    normSq ((Γ * r ^ 2 / 2 : ℝ) * M) / (4 * (Γ ^ 2 / 4)) = r ^ 4 * normSq M / 4 ∧
    ((Γ * r ^ 2 / 2 : ℝ) * M) / (2 * ((Γ ^ 2 / 4 : ℝ) : ℂ)) = ((r ^ 2 / Γ : ℝ) : ℂ) * M := by
  constructor
  · rw [normSq_mul, normSq_ofReal]; field_simp; ring
  · have : (Γ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hΓ
    push_cast; field_simp; ring

/-- Aspect ratio of the stationary ellipse: `(1 + e)/(1 - e) = 1 + 2e + 2e²/(1 - e)`. -/
theorem aspect_ratio (e : ℝ) (he : e ≠ 1) : (1 + e) / (1 - e) = 1 + 2 * e + 2 * e ^ 2 / (1 - e) := by
  have : 1 - e ≠ 0 := sub_ne_zero.mpr (Ne.symm he)
  field_simp; ring

/-! ### Schur complement (elimination of the fast block in the linearisation) -/

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- `Q(x, y) = xᵀ A x + 2 xᵀ B y + yᵀ C y`. -/
def quadQ (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n n ℝ) (x : m → ℝ) (y : n → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x) + 2 * (x ⬝ᵥ (B *ᵥ y)) + y ⬝ᵥ (C *ᵥ y)

/-- At `y* = -C⁻¹ Bᵀ x` (the stationary point of `Q(x, ·)` when `C` is symmetric and invertible),
`Q(x, y*) = xᵀ (A - B C⁻¹ Bᵀ) x`. -/
theorem schur_elimination (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hC : IsUnit C.det) (x : m → ℝ) :
    quadQ A B C x (-(C⁻¹ *ᵥ (Bᵀ *ᵥ x))) = x ⬝ᵥ ((A - B * C⁻¹ * Bᵀ) *ᵥ x) := by
  have hCi : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hC
  have h1 : ∀ w : n → ℝ, x ⬝ᵥ (B *ᵥ w) = (Bᵀ *ᵥ x) ⬝ᵥ w := by
    intro w; rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have h2 : ∀ w : n → ℝ, (C⁻¹ *ᵥ w) ⬝ᵥ (C *ᵥ (C⁻¹ *ᵥ w)) = w ⬝ᵥ (C⁻¹ *ᵥ w) := by
    intro w; rw [Matrix.mulVec_mulVec, hCi, Matrix.one_mulVec, dotProduct_comm]
  have h3 : x ⬝ᵥ ((B * C⁻¹ * Bᵀ) *ᵥ x) = (Bᵀ *ᵥ x) ⬝ᵥ (C⁻¹ *ᵥ (Bᵀ *ᵥ x)) := by
    have : (B * C⁻¹ * Bᵀ) *ᵥ x = B *ᵥ (C⁻¹ *ᵥ (Bᵀ *ᵥ x)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [this, h1]
  have e1 := h1 (C⁻¹ *ᵥ (Bᵀ *ᵥ x))
  have e2 := h2 (Bᵀ *ᵥ x)
  simp only [quadQ, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, Matrix.sub_mulVec,
    dotProduct_sub, neg_neg, e1, e2, h3]
  ring

end Heptagon
