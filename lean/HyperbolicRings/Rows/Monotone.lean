/-
New in this paper (vortex-stability-papers, paper 3). Not copied from the source repositories.

Monotonicity in the curvature (paper, Theorem "hypercycle threshold", part (b)): at fixed strip spacing,
`F(π)/sin²α` is strictly increasing in `K = κ²`. Hence, at a fixed strip spacing, if the row of curvature `κ₁`
is spectrally stable, so is every row with `κ₁² < κ₂² < 1` (`stable_mono`); with the (certified) uniqueness of the
threshold this is the strict decrease of `ℓ_u^*(κ)`.
-/
import HyperbolicRings.Rows.Main

noncomputable section

namespace HyperbolicRings.Rows

open Real

theorem go_strictMono {K₁ K₂ c : ℝ} (hK : K₁ < K₂) (hK2 : K₂ < 1) (hc : 1 < c) : go K₁ c < go K₂ c := by
  unfold go Dd
  have hD1 : 0 < c + 1 - 2 * K₁ := by linarith
  have hD2 : 0 < c + 1 - 2 * K₂ := by linarith
  have hc1 : 0 < c - 1 := by linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have : 0 < (c - 1) * (2 * (K₂ - K₁) * (c ^ 2 - 1)) := by
    apply mul_pos hc1; apply mul_pos (by linarith); nlinarith
  nlinarith

theorem ge_strictMono {K₁ K₂ c : ℝ} (hK0 : 0 ≤ K₁) (hK : K₁ < K₂) (hK2 : K₂ < 1) (hc : 1 < c) :
    ge K₁ c < ge K₂ c := by
  unfold ge Dd
  have hD1 : 0 < c + 1 - 2 * K₁ := by linarith
  have hD2 : 0 < c + 1 - 2 * K₂ := by linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  -- N₂ D₁² - N₁ D₂² = 2 (K₂ - K₁) [ (2c² + c - 1)(D₁ + D₂) / ... ]: verified by nlinarith with hints
  have hd : 0 < K₂ - K₁ := by linarith
  have h1 : 0 < 2 * c ^ 2 + c - 1 - 2 * K₂ := by nlinarith
  have h2 : 0 < 2 * c ^ 2 + c - 1 - 2 * K₁ := by nlinarith
  nlinarith [mul_pos hd (mul_pos h1 hD1), mul_pos hd (mul_pos h2 hD2), mul_pos hd (mul_pos h1 hD2),
    mul_pos hd (mul_pos h2 hD1), mul_pos (mul_pos hd hd) (mul_pos hD1 hD2), mul_pos hd hD1, mul_pos hd hD2]

/-- At fixed strip spacing, `F(π)/(1-K)` is strictly increasing in `K ∈ [0,1)`. -/
theorem Fpi_div_strictMono {K₁ K₂ ℓ : ℝ} (hK0 : 0 ≤ K₁) (hK : K₁ < K₂) (hK2 : K₂ < 1) (hℓ : 0 < ℓ) :
    F K₁ ℓ π / (1 - K₁) < F K₂ ℓ π / (1 - K₂) := by
  have hK1 : K₁ < 1 := by linarith
  have hK20 : 0 ≤ K₂ := by linarith
  have e : ∀ {K : ℝ}, 0 ≤ K → K < 1 → F K ℓ π / (1 - K) = ∑' n, term K ℓ π n / (1 - K) := by
    intro K _ _; unfold F; rw [tsum_div_const]
  rw [e hK0 hK1, e hK20 hK2]
  have hval : ∀ {K : ℝ}, K < 1 → ∀ n, term K ℓ π n / (1 - K) =
      if Even n then go K (cj ℓ n) else ge K (cj ℓ n) := by
    intro K hK n
    have hs : (1 - K) ≠ 0 := by linarith
    have h1 := B0_sub_B1 hK (one_lt_cj hℓ n)
    have h2 := B0_add_B1 hK (one_lt_cj hℓ n)
    unfold term; rw [cos_pi_mul]
    rcases Nat.even_or_odd n with he | ho
    · rw [if_pos he, (he.add_one).neg_one_pow]
      rw [show B0 K (cj ℓ n) + B1 K (cj ℓ n) * -1 = (1 - K) * go K (cj ℓ n) by linarith]
      field_simp
    · rw [if_neg (Nat.not_even_iff_odd.mpr ho), (ho.add_one).neg_one_pow]
      rw [show B0 K (cj ℓ n) + B1 K (cj ℓ n) * 1 = (1 - K) * ge K (cj ℓ n) by linarith]
      field_simp
  have hs1 : Summable (fun n => term K₁ ℓ π n / (1 - K₁)) := (F_summable hK0 hK1 hℓ π).div_const _
  have hs2 : Summable (fun n => term K₂ ℓ π n / (1 - K₂)) := (F_summable hK20 hK2 hℓ π).div_const _
  refine hs1.tsum_lt_tsum (i := 0) (fun n => ?_) ?_ hs2
  · rw [hval hK1, hval hK2]
    split_ifs
    · exact (go_strictMono hK hK2 (one_lt_cj hℓ n)).le
    · exact (ge_strictMono hK0 hK hK2 (one_lt_cj hℓ n)).le
  · rw [hval hK1, hval hK2, if_pos (by decide)]
    exact go_strictMono hK hK2 (one_lt_cj hℓ 0)

/-- At fixed strip spacing `ℓ`, spectral stability is monotone in the curvature: if the row with
`cos²α₁ = K₁` is stable, so is every row with `K₁ < cos²α₂ < 1`. -/
theorem stable_mono {α₁ α₂ ℓ : ℝ} (h₁0 : 0 < α₁) (h₁π : α₁ < π) (h₂0 : 0 < α₂) (h₂π : α₂ < π) (hℓ : 0 < ℓ)
    (hK : cos α₁ ^ 2 < cos α₂ ^ 2) (hst : RowStable α₁ ℓ) : RowStable α₂ ℓ := by
  have hK1 := K_lt_one h₁0 h₁π hℓ
  have hK2 := K_lt_one h₂0 h₂π hℓ
  rw [rowStable_iff h₁0 h₁π hℓ] at hst
  rw [rowStable_iff h₂0 h₂π hℓ]
  have hm := Fpi_div_strictMono (sq_nonneg _) hK hK2 hℓ
  have hs1 : 0 < 1 - cos α₁ ^ 2 := by linarith
  have hs2 : 0 < 1 - cos α₂ ^ 2 := by linarith
  have : 0 ≤ F (cos α₁ ^ 2) ℓ π / (1 - cos α₁ ^ 2) := div_nonneg hst hs1.le
  have : 0 < F (cos α₂ ^ 2) ℓ π / (1 - cos α₂ ^ 2) := by linarith
  have := (div_pos_iff_of_pos_right hs2).mp this
  exact this.le

end HyperbolicRings.Rows
