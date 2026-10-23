/-
New in this paper (vortex-stability-papers, paper 3). Not copied from the source repositories.

Hypercycle rows of the tanh kernel: the pair functions of the Bloch symbol and their algebra
(paper, Section "Rows on hypercycles", Proposition "pair functions" and Lemma "pair identities").

The pair functions are taken here as *definitions* (rational functions of `c = cosh(j ℓ_u)` and
`K = κ²`); their derivation from the Hamiltonian is by hand in the paper, checked by sympy
(`code/rows_symbol.py`). With `s = 1 - K = sin²α` and `D = c + 1 - 2K`:

  B0(c) = s((3K-1)c² - (4K²-K+1)c + 2K²) / ((c-1) D²)
  B1(c) = s(K c² + (1-3K)c + 2K² - 2K + 1) / ((c-1) D²)
  C1(c) = -s²(c² + c - 2K) / ((c-1) D²)
-/
import Mathlib

noncomputable section

namespace HyperbolicRings.Rows

/-- `D = c + 1 - 2K`. -/
def Dd (K c : ℝ) : ℝ := c + 1 - 2 * K

/-- The pair function `B⁽⁰⁾`. -/
def B0 (K c : ℝ) : ℝ :=
  (1 - K) * ((3 * K - 1) * c ^ 2 - (4 * K ^ 2 - K + 1) * c + 2 * K ^ 2) / ((c - 1) * Dd K c ^ 2)

/-- The pair function `B⁽¹⁾`. -/
def B1 (K c : ℝ) : ℝ :=
  (1 - K) * (K * c ^ 2 + (1 - 3 * K) * c + 2 * K ^ 2 - 2 * K + 1) / ((c - 1) * Dd K c ^ 2)

/-- The pair function `C⁽¹⁾`. -/
def C1 (K c : ℝ) : ℝ := -(1 - K) ^ 2 * (c ^ 2 + c - 2 * K) / ((c - 1) * Dd K c ^ 2)

/-- Odd-`j` pairing term `𝔤_o = (2K-1)c - 1) / ((c-1) D)`. -/
def go (K c : ℝ) : ℝ := ((2 * K - 1) * c - 1) / ((c - 1) * Dd K c)

/-- Even-`j` pairing term `𝔤_e = ((4K-1)c - (4K²-2K+1)) / D²`. -/
def ge (K c : ℝ) : ℝ := ((4 * K - 1) * c - (4 * K ^ 2 - 2 * K + 1)) / Dd K c ^ 2

variable {K c : ℝ}

theorem Dd_pos (hK : K < 1) (hc : 1 < c) : 0 < Dd K c := by unfold Dd; linarith

theorem Dd_ge (hK : K ≤ 1) : c - 1 ≤ Dd K c := by unfold Dd; linarith

/-- `B⁽⁰⁾ - B⁽¹⁾ = s 𝔤_o`. -/
theorem B0_sub_B1 (hK : K < 1) (hc : 1 < c) : B0 K c - B1 K c = (1 - K) * go K c := by
  have h1 : c - 1 ≠ 0 := by linarith
  have h2 : Dd K c ≠ 0 := (Dd_pos hK hc).ne'
  unfold B0 B1 go
  rw [div_sub_div _ _ (by positivity) (by positivity), div_eq_iff (by positivity)]
  field_simp
  simp only [Dd]; ring

/-- `B⁽⁰⁾ + B⁽¹⁾ = s 𝔤_e`. -/
theorem B0_add_B1 (hK : K < 1) (hc : 1 < c) : B0 K c + B1 K c = (1 - K) * ge K c := by
  have h1 : c - 1 ≠ 0 := by linarith
  have h2 : Dd K c ≠ 0 := (Dd_pos hK hc).ne'
  unfold B0 B1 ge
  rw [div_add_div _ _ (by positivity) (by positivity), div_eq_iff (by positivity)]
  field_simp
  ring

/-- `B⁽¹⁾ > 0` for `0 ≤ K < 1`, `c > 1`: with `t = c - 1` its numerator is
`K t² + (1-K) t + 2(1-K)²`. -/
theorem B1_pos (hK0 : 0 ≤ K) (hK : K < 1) (hc : 1 < c) : 0 < B1 K c := by
  unfold B1
  apply div_pos
  · apply mul_pos (by linarith)
    have : K * c ^ 2 + (1 - 3 * K) * c + 2 * K ^ 2 - 2 * K + 1
        = K * (c - 1) ^ 2 + (1 - K) * (c - 1) + 2 * (1 - K) ^ 2 := by ring
    rw [this]
    have : 0 < (1 - K) * (c - 1) := mul_pos (by linarith) (by linarith)
    have : 0 ≤ K * (c - 1) ^ 2 := by positivity
    have : 0 < 2 * (1 - K) ^ 2 := by have : 0 < 1 - K := by linarith
                                     positivity
    linarith
  · have := Dd_pos hK hc
    have : 0 < c - 1 := by linarith
    positivity

/-- `C⁽¹⁾ < 0` for `0 ≤ K < 1`, `c > 1`. -/
theorem C1_neg (_hK0 : 0 ≤ K) (hK : K < 1) (hc : 1 < c) : C1 K c < 0 := by
  unfold C1
  have hD := Dd_pos hK hc
  have : 0 < c - 1 := by linarith
  have hs : 0 < (1 - K) ^ 2 := by have : 0 < 1 - K := by linarith
                                  positivity
  have hn : 0 < c ^ 2 + c - 2 * K := by nlinarith
  apply div_neg_of_neg_of_pos _ (by positivity)
  have := mul_pos hs hn
  linarith

/-- Stability-bound lemma: if `(2K-1)c ≥ 1` then `𝔤_o ≥ 0`. -/
theorem go_nonneg (hK : K < 1) (hc : 1 < c) (h : 1 ≤ (2 * K - 1) * c) : 0 ≤ go K c := by
  unfold go
  have := Dd_pos hK hc
  have : 0 < c - 1 := by linarith
  apply div_nonneg (by linarith) (by positivity)

theorem go_pos (hK : K < 1) (hc : 1 < c) (h : 1 < (2 * K - 1) * c) : 0 < go K c := by
  unfold go
  have := Dd_pos hK hc
  have : 0 < c - 1 := by linarith
  apply div_pos (by linarith) (by positivity)

/-- All-mode lemma: if `K ≤ 1/4` then `𝔤_e < 0`. -/
theorem ge_neg (_hK0 : 0 ≤ K) (hK : K ≤ 1 / 4) (hc : 1 < c) : ge K c < 0 := by
  unfold ge
  have hD := Dd_pos (by linarith : K < 1) hc
  apply div_neg_of_neg_of_pos _ (by positivity)
  nlinarith

/-- Comparison with `K = 1/2` for the odd terms: `𝔤_o(K) ≤ -1/((c-1)c)` for `K ≤ 1/2`. -/
theorem go_le_half (hK : K ≤ 1 / 2) (hc : 1 < c) : go K c ≤ -1 / ((c - 1) * c) := by
  unfold go Dd
  set t := 1 - 2 * K with ht
  have ht0 : 0 ≤ t := by linarith
  have hc1 : 0 < c - 1 := by linarith
  have hc0 : 0 < c := by linarith
  have e1 : (2 * K - 1) * c - 1 = -(t * c + 1) := by rw [ht]; ring
  have e2 : c + 1 - 2 * K = c + t := by rw [ht]; ring
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg ht0 (mul_nonneg hc1.le hc0.le), mul_nonneg ht0 hc1.le]

/-- Comparison with `K = 1/2` for the even terms: `𝔤_e(K) ≤ (c-1)/c²` for `0 ≤ K ≤ 1/2`. -/
theorem ge_le_half (hK0 : 0 ≤ K) (hK : K ≤ 1 / 2) (hc : 1 < c) : ge K c ≤ (c - 1) / c ^ 2 := by
  unfold ge Dd
  set t := 1 - 2 * K with ht
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t ≤ 1 := by linarith
  have hc0 : 0 < c := by linarith
  have e1 : (4 * K - 1) * c - (4 * K ^ 2 - 2 * K + 1) = (1 - 2 * t) * c - (t ^ 2 - t + 1) := by
    rw [ht]; ring
  have e2 : c + 1 - 2 * K = c + t := by rw [ht]; ring
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
  -- RHS - LHS = t (2c³ + c² + t c² + t c - 2c - t) ≥ 0
  have key : 0 ≤ t * (2 * c ^ 3 + c ^ 2 + t * c ^ 2 + t * c - 2 * c - t) := by
    apply mul_nonneg ht0
    have : 0 ≤ 2 * c ^ 3 - 2 * c := by
      have : 2 * c ^ 3 - 2 * c = 2 * c * ((c - 1) * (c + 1)) := by ring
      rw [this]; have : 0 ≤ (c - 1) * (c + 1) := mul_nonneg (by linarith) (by linarith)
      positivity
    have : 0 ≤ c ^ 2 - t := by nlinarith
    have : 0 ≤ t * c ^ 2 + t * c := by positivity
    linarith
  nlinarith [key]

end HyperbolicRings.Rows
