/-
New in this paper (vortex-stability-papers, paper 3). Not copied from the source repositories.

The hypercycle rows approach the horocycle row (paper, Theorem "hypercycle threshold", part (c)).

At fixed arc spacing `ℓ` (strip spacing `ℓ sin α`), as `α → 0⁺` (`κ = cos α → 1`):
* `tendsto_F_pi`: `F(π) → (τ²/2) Φ(τ)`, `τ = 2π/ℓ`, where `Φ` is the limit function of the rings (`Tanh.LargeN.Phi`).
  The limit is computed by dominated convergence (Tannery's theorem) termwise, and the limiting lattice sum is
  identified with the yy-entry of the horocycle-row Bloch symbol at the pairing mode (`rowMyy_eq`, θ = 1/2).
* `hyper_threshold_tendsto`: for every `ε > 0`, for all small `α > 0`, the hypercycle row with arc spacing
  `ℓ_* - ε` is spectrally unstable and the one with arc spacing `ℓ_* + ε` is spectrally stable
  (`ℓ_* = 2π/τ∞`). With the (certified, not formalised) uniqueness of the threshold this is `ℓ*(κ) → ℓ_*`.
-/
import HyperbolicRings.Rows.Main
import HyperbolicRings.Tanh.LargeN.RowStability

noncomputable section

namespace HyperbolicRings.Horocycle

open Real Filter Topology HyperbolicRings.Rows HyperbolicRings.Tanh.LargeN
open Complex (I)

/-- The limiting lattice summand at `j = m + 1`, `d = jℓ`. -/
def gL (ℓ : ℝ) (m : ℕ) : ℝ :=
  if Even m then -2 / (((m : ℝ) + 1) * ℓ) ^ 2 + 4 / ((((m : ℝ) + 1) * ℓ) ^ 2 + 4)
  else 2 * ((((m : ℝ) + 1) * ℓ) ^ 2 - 4) / ((((m : ℝ) + 1) * ℓ) ^ 2 + 4) ^ 2
    + 4 / ((((m : ℝ) + 1) * ℓ) ^ 2 + 4)

/-! ## The limiting lattice sum is the horocycle yy-entry at the pairing mode -/

theorem blochPhase_half (k : ℤ) : blochPhase (1 / 2) k = ((-1 : ℝ) ^ k.natAbs : ℝ) := by
  unfold blochPhase
  push_cast
  rw [show (2 : ℂ) * π * I * k * (1 / 2) = k * (π * I) by ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rcases Int.even_or_odd k with h | h
  · rw [h.neg_one_zpow, (Int.natAbs_even.mpr h).neg_one_pow]
  · rw [h.neg_one_zpow, (Int.natAbs_odd.mpr h).neg_one_pow]

theorem hasSum_gL {ℓ : ℝ} (hℓ : 0 < ℓ) :
    HasSum (gL ℓ) ((2 * π / ℓ) ^ 2 * Phi (2 * π / ℓ) / 2) := by
  have hθ : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hY := hasSum_termYY hℓ hθ
  have hv := hasSum_rowVel hℓ
  have hrv : rowVel ℓ = ((2 * π / ℓ) * coth (2 * π / ℓ) - 1) / 2 := hv.tsum_eq
  -- termYY + 2·(v-summand) over ℤ
  set vk : ℤ → ℝ := fun k => if k = 0 then 0 else 2 / (((k : ℝ) * ℓ) ^ 2 + 4)
  have hY' : HasSum (fun k => termYY ℓ (1 / 2) k) (((2 * π / ℓ) ^ 2 * (Einf (2 * π / ℓ)
      - 1 / (4 * sinh (2 * π / ℓ) ^ 2) - psi (1 - 2 * (1 / 2)) (2 * π / ℓ)) : ℝ) - 2 * (rowVel ℓ : ℂ)) := by
    have := hY.sub (hasSum_ite_eq (0 : ℤ) (2 * (rowVel ℓ : ℂ)))
    simpa using this
  have hV : HasSum (fun k => 2 * ((vk k : ℝ) : ℂ)) (2 * (rowVel ℓ : ℂ)) := by
    rw [hrv]; exact (Complex.hasSum_ofReal.mpr hv).mul_left 2
  have hT := hY'.add hV
  simp only [sub_add_cancel] at hT
  -- the full summand is real: define it
  set h : ℤ → ℝ := fun k => if k = 0 then 0 else
    (onYY ℓ k + (-1 : ℝ) ^ k.natAbs * cpYY ℓ k) + 2 * (2 / (((k : ℝ) * ℓ) ^ 2 + 4)) with hh
  have hT' : HasSum h ((2 * π / ℓ) ^ 2 * (Einf (2 * π / ℓ) - 1 / (4 * sinh (2 * π / ℓ) ^ 2)
      - psi (1 - 2 * (1 / 2)) (2 * π / ℓ))) := by
    rw [← Complex.hasSum_ofReal]
    convert hT using 1
    funext k
    by_cases hk : k = 0
    · simp [hh, hk, termYY, vk]
    · simp only [hh, hk, termYY, vk, if_false, blochPhase_half]; push_cast; ring
  -- pair k and -k
  have hN := hT'.nat_add_neg
  have h0 : h 0 = 0 := by simp [hh]
  rw [h0, add_zero] at hN
  have hshift := (hasSum_nat_add_iff' 1).mpr hN
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, neg_zero, h0, add_zero, sub_zero] at hshift
  have hfin : (fun n : ℕ => h ((n + 1 : ℕ) : ℤ) + h (-((n + 1 : ℕ) : ℤ))) = fun n => 2 * gL ℓ n := by
    funext n
    have hk1 : ((n + 1 : ℕ) : ℤ) ≠ 0 := by omega
    have hk2 : -((n + 1 : ℕ) : ℤ) ≠ 0 := by omega
    simp only [hh, hk1, hk2, if_false, Int.natAbs_neg, Int.natAbs_natCast, onYY, cpYY, rowS, rowP_re, gL]
    push_cast
    rcases Nat.even_or_odd n with he | ho
    · have : Odd (n + 1) := he.add_one
      rw [if_pos he, this.neg_one_pow]; ring
    · have : Even (n + 1) := ho.add_one
      rw [if_neg (Nat.not_even_iff_odd.mpr ho), this.neg_one_pow]; ring
  rw [hfin] at hshift
  have := hshift.div_const 2
  simp only [mul_div_cancel_left₀ _ (two_ne_zero' ℝ)] at this
  convert this using 1
  simp only [Phi]; norm_num

/-! ## Termwise limit as `α → 0⁺` -/

theorem tendsto_sin_nhdsGT : Tendsto Real.sin (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have := (Real.continuous_sin.tendsto 0); simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π from Real.pi_pos)] with x hx
    exact Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2

/-- `(cosh(dσ) - 1)/σ² → d²/2` as `σ → 0⁺`. -/
theorem tendsto_w {d : ℝ} (hd : 0 < d) :
    Tendsto (fun σ => (cosh (d * σ) - 1) / σ ^ 2) (𝓝[>] 0) (𝓝 (d ^ 2 / 2)) := by
  have hslope := (hasDerivAt_iff_tendsto_slope_zero.mp (Real.hasDerivAt_sinh 0))
  simp only [zero_add, Real.sinh_zero, sub_zero, Real.cosh_zero, smul_eq_mul] at hslope
  have hy : Tendsto (fun σ : ℝ => d * σ / 2) (𝓝[>] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun σ : ℝ => d * σ / 2) (𝓝 0) (𝓝 (d * 0 / 2)) :=
        ((continuous_const.mul continuous_id).div_const 2).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      have : 0 < d * σ / 2 := by have := Set.mem_Ioi.mp hσ; positivity
      exact this.ne'
  have h1 := (hslope.comp hy)
  have h2 := (h1.pow 2).const_mul (d ^ 2 / 2)
  simp only [one_pow, mul_one] at h2
  apply h2.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ0 : σ ≠ 0 := (Set.mem_Ioi.mp hσ).ne'
  simp only [Function.comp]
  have hc : cosh (d * σ) - 1 = 2 * sinh (d * σ / 2) ^ 2 := by
    have := Real.cosh_two_mul (d * σ / 2)
    rw [show 2 * (d * σ / 2) = d * σ by ring, Real.cosh_sq] at this
    linarith
  rw [hc]
  field_simp
  try ring

/-- `s·𝔤_o` and `s·𝔤_e` in the variables `w = (c-1)/s`, `s = sin²α`. -/
theorem go_w {s w : ℝ} (hs : 0 < s) (hw : 0 < w) :
    s * go (1 - s) (1 + s * w) = (w - 2 * (1 + s * w)) / (w * (w + 2)) := by
  unfold go Dd
  rw [show (1 + s * w) - 1 = s * w by ring, show 1 + s * w + 1 - 2 * (1 - s) = s * (w + 2) by ring]
  have : w + 2 ≠ 0 := by positivity
  field_simp
  ring

theorem ge_w {s w : ℝ} (hs : 0 < s) (hw : 0 < w) :
    s * ge (1 - s) (1 + s * w) = (3 * w - 4 * (1 + s * w) + 6 - 4 * s) / (w + 2) ^ 2 := by
  unfold ge Dd
  rw [show 1 + s * w + 1 - 2 * (1 - s) = s * (w + 2) by ring]
  have : w + 2 ≠ 0 := by positivity
  field_simp
  ring

section limit
variable {ℓ : ℝ} (hℓ : 0 < ℓ)
include hℓ

/-- The summand of `F(π)` at strip spacing `ℓ sin α`, written in `w = (c-1)/s` and `c`. -/
theorem term_w {α : ℝ} (hα0 : 0 < α) (hα : α < π / 2) (n : ℕ) :
    term (cos α ^ 2) (ℓ * sin α) π n =
      if Even n then
        ((cosh ((((n : ℝ) + 1) * ℓ) * sin α) - 1) / sin α ^ 2 - 2 * cosh ((((n : ℝ) + 1) * ℓ) * sin α)) /
          ((cosh ((((n : ℝ) + 1) * ℓ) * sin α) - 1) / sin α ^ 2 *
            ((cosh ((((n : ℝ) + 1) * ℓ) * sin α) - 1) / sin α ^ 2 + 2))
      else
        (3 * ((cosh ((((n : ℝ) + 1) * ℓ) * sin α) - 1) / sin α ^ 2)
            - 4 * cosh ((((n : ℝ) + 1) * ℓ) * sin α) + 6 - 4 * sin α ^ 2) /
          ((cosh ((((n : ℝ) + 1) * ℓ) * sin α) - 1) / sin α ^ 2 + 2) ^ 2 := by
  have hs : 0 < sin α := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
  have hK : cos α ^ 2 < 1 := by nlinarith [sin_sq_add_cos_sq α]
  have hcK : cos α ^ 2 = 1 - sin α ^ 2 := by rw [← sin_sq_add_cos_sq α]; ring
  have hlu : 0 < ℓ * sin α := mul_pos hℓ hs
  have hc := one_lt_cj hlu n
  have hcj : cj (ℓ * sin α) n = cosh ((((n : ℝ) + 1) * ℓ) * sin α) := by unfold cj; ring_nf
  set c := cosh ((((n : ℝ) + 1) * ℓ) * sin α) with hcdef
  rw [hcj] at hc
  have hc1 : 0 < c - 1 := by linarith
  have h1 := B0_sub_B1 hK (one_lt_cj hlu n)
  have h2 := B0_add_B1 hK (one_lt_cj hlu n)
  rw [hcj] at h1 h2
  unfold term
  rw [cos_pi_mul, hcj]
  have hs2 : 0 < sin α ^ 2 := by positivity
  have hw0 : 0 < (c - 1) / sin α ^ 2 := div_pos hc1 hs2
  have hcw : c = 1 + sin α ^ 2 * ((c - 1) / sin α ^ 2) := by field_simp; ring
  have hsK : 1 - cos α ^ 2 = sin α ^ 2 := by rw [hcK]; ring
  rcases Nat.even_or_odd n with he | ho
  · rw [if_pos he, (he.add_one).neg_one_pow, mul_neg_one]
    have : B0 (cos α ^ 2) c + -B1 (cos α ^ 2) c = (1 - cos α ^ 2) * go (cos α ^ 2) c := by linarith
    rw [this, hsK, hcK]
    conv_lhs => rw [hcw]
    rw [go_w hs2 hw0, ← hcw]
  · rw [if_neg (Nat.not_even_iff_odd.mpr ho), (ho.add_one).neg_one_pow, mul_one, h2, hsK, hcK]
    conv_lhs => rw [hcw]
    rw [ge_w hs2 hw0, ← hcw]

theorem tendsto_term (n : ℕ) :
    Tendsto (fun α => term (cos α ^ 2) (ℓ * sin α) π n) (𝓝[>] 0) (𝓝 (gL ℓ n)) := by
  set d := ((n : ℝ) + 1) * ℓ with hd
  have hd0 : 0 < d := by positivity
  have hw := (tendsto_w hd0).comp tendsto_sin_nhdsGT
  have hcos : Tendsto (fun α => cosh (d * sin α)) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun α => cosh (d * sin α)) (𝓝 0) (𝓝 (cosh (d * sin 0))) :=
      ((Real.continuous_cosh.comp (continuous_const.mul Real.continuous_sin))).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hsin2 : Tendsto (fun α => sin α ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun α => sin α ^ 2) (𝓝 0) (𝓝 (sin 0 ^ 2)) :=
      (Real.continuous_sin.pow 2).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ α in 𝓝[>] (0 : ℝ), α ∈ Set.Ioo 0 (π / 2) :=
    Ioo_mem_nhdsGT (by linarith [Real.pi_pos])
  have hd2 : d ^ 2 / 2 ≠ 0 := by positivity
  have hd22 : d ^ 2 / 2 + 2 ≠ 0 := by positivity
  rcases Nat.even_or_odd n with he | ho
  · have hlim := ((hw.sub (hcos.const_mul 2)).div (hw.mul (hw.add_const 2))
      (mul_ne_zero hd2 hd22))
    have hval : (d ^ 2 / 2 - 2 * 1) / (d ^ 2 / 2 * (d ^ 2 / 2 + 2)) = gL ℓ n := by
      rw [gL, if_pos he, ← hd]; field_simp; ring
    rw [hval] at hlim
    apply hlim.congr'
    filter_upwards [hev] with α hα
    rw [term_w hℓ hα.1 hα.2, if_pos he]
    simp only [Pi.div_apply, Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Function.comp, ← hd]
  · have hlim := ((((hw.const_mul 3).sub (hcos.const_mul 4)).add_const 6).sub (hsin2.const_mul 4)).div
      ((hw.add_const 2).pow 2) (pow_ne_zero 2 hd22)
    have hval : (3 * (d ^ 2 / 2) - 4 * 1 + 6 - 4 * 0) / (d ^ 2 / 2 + 2) ^ 2 = gL ℓ n := by
      rw [gL, if_neg (Nat.not_even_iff_odd.mpr ho), ← hd]; field_simp; ring
    rw [hval] at hlim
    apply hlim.congr'
    filter_upwards [hev] with α hα
    rw [term_w hℓ hα.1 hα.2, if_neg (Nat.not_even_iff_odd.mpr ho)]
    simp only [Pi.div_apply, Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Function.comp, Pi.pow_apply, ← hd]

/-- Domination: `|term_n| ≤ 14/((n+1)ℓ)²` for `0 < α < π/2`. -/
theorem term_bound {α : ℝ} (hα0 : 0 < α) (hα : α < π / 2) (n : ℕ) :
    ‖term (cos α ^ 2) (ℓ * sin α) π n‖ ≤ 14 * (1 / ((n : ℝ) + 1) ^ 2) / ℓ ^ 2 := by
  have hs : 0 < sin α := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
  have hs1 : sin α ^ 2 ≤ 1 := by nlinarith [sin_sq_add_cos_sq α]
  set d := ((n : ℝ) + 1) * ℓ with hd
  have hd0 : 0 < d := by positivity
  set c := cosh (d * sin α) with hc
  set w := (c - 1) / sin α ^ 2 with hw
  have hs2 : 0 < sin α ^ 2 := by positivity
  have hwge : d ^ 2 / 2 ≤ w := by
    rw [hw, le_div_iff₀ hs2]
    have := one_add_sq_half_le_cosh (mul_pos hd0 hs).le
    rw [hc]; nlinarith
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hwge
  have hcw : c = 1 + sin α ^ 2 * w := by rw [hw]; field_simp; ring
  have hcle : c ≤ 1 + w := by rw [hcw]; nlinarith
  have hc1 : 1 ≤ c := by rw [hcw]; nlinarith
  have key : 14 * (1 / ((n : ℝ) + 1) ^ 2) / ℓ ^ 2 = 7 / (d ^ 2 / 2) := by rw [hd]; field_simp; ring
  rw [key, Real.norm_eq_abs, term_w hℓ hα0 hα n]
  have hrw : cosh ((((n : ℝ) + 1) * ℓ) * sin α) = c := by rw [hc, hd]
  rw [hrw, ← hw]
  have h7 : 7 / w ≤ 7 / (d ^ 2 / 2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hwge
  split_ifs
  · rw [abs_div, abs_of_pos (by positivity : 0 < w * (w + 2))]
    have : |w - 2 * c| ≤ 3 * (w + 2) := by rw [abs_le]; constructor <;> nlinarith
    calc |w - 2 * c| / (w * (w + 2)) ≤ 3 * (w + 2) / (w * (w + 2)) :=
          div_le_div_of_nonneg_right this (by positivity)
      _ = 3 / w := by field_simp
      _ ≤ 7 / w := div_le_div_of_nonneg_right (by norm_num) hw0.le
      _ ≤ _ := h7
  · rw [abs_div, abs_of_pos (by positivity : 0 < (w + 2) ^ 2)]
    have : |3 * w - 4 * c + 6 - 4 * sin α ^ 2| ≤ 7 * (w + 2) := by
      rw [abs_le]; constructor <;> nlinarith
    calc |3 * w - 4 * c + 6 - 4 * sin α ^ 2| / (w + 2) ^ 2 ≤ 7 * (w + 2) / (w + 2) ^ 2 :=
          div_le_div_of_nonneg_right this (by positivity)
      _ = 7 / (w + 2) := by field_simp; try ring
      _ ≤ 7 / w := div_le_div_of_nonneg_left (by norm_num) hw0 (by linarith)
      _ ≤ _ := h7

/-- **Hypercycle → horocycle.** At fixed arc spacing `ℓ`, `F(π) → (τ²/2) Φ(τ)`, `τ = 2π/ℓ`, as `α → 0⁺`. -/
theorem tendsto_F_pi :
    Tendsto (fun α => F (cos α ^ 2) (ℓ * sin α) π) (𝓝[>] 0)
      (𝓝 ((2 * π / ℓ) ^ 2 * Phi (2 * π / ℓ) / 2)) := by
  rw [← (hasSum_gL hℓ).tsum_eq]
  show Tendsto (fun α => ∑' n, term (cos α ^ 2) (ℓ * sin α) π n) _ _
  refine tendsto_tsum_of_dominated_convergence (f := fun α n => term (cos α ^ 2) (ℓ * sin α) π n)
    (g := gL ℓ) (bound := fun n => 14 * (1 / ((n : ℝ) + 1) ^ 2) / ℓ ^ 2) ?_ ?_ ?_
  · have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [Nat.cast_add, Nat.cast_one] using (this.mul_left 14).div_const (ℓ ^ 2)
  · exact tendsto_term hℓ
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by linarith [Real.pi_pos])] with α hα
    exact term_bound hℓ hα.1 hα.2

end limit

/-- **Threshold convergence.** For every `ε ∈ (0, ℓ_*)` there is `δ > 0` such that for `0 < α < δ` the
hypercycle row of curvature `cos α` is spectrally unstable at arc spacing `ℓ_* - ε` and spectrally stable at
arc spacing `ℓ_* + ε`, where `ℓ_* = 2π/τ∞`. -/
theorem hyper_threshold_tendsto {ε : ℝ} (hε : 0 < ε) (hε' : ε < 2 * π / tauInf) :
    ∃ δ > 0, ∀ α ∈ Set.Ioo 0 δ,
      ¬ RowStable α ((2 * π / tauInf - ε) * sin α) ∧ RowStable α ((2 * π / tauInf + ε) * sin α) := by
  have hτ := tauInf_pos
  set ℓm := 2 * π / tauInf - ε with hℓm
  set ℓp := 2 * π / tauInf + ε with hℓp
  have hℓm0 : 0 < ℓm := by linarith
  have hℓp0 : 0 < ℓp := by
    have h : 0 < 2 * π / tauInf := (by positivity)
    linarith
  -- signs of the limits
  have hτm : tauInf < 2 * π / ℓm := by
    rw [lt_div_iff₀ hℓm0]
    have e : tauInf * ℓm = 2 * π - tauInf * ε := by rw [hℓm]; field_simp
    nlinarith
  have hτp : 2 * π / ℓp < tauInf := by
    rw [div_lt_iff₀ hℓp0]
    have e : tauInf * ℓp = 2 * π + tauInf * ε := by rw [hℓp]; field_simp
    nlinarith
  have hneg : (2 * π / ℓm) ^ 2 * Phi (2 * π / ℓm) / 2 < 0 := by
    have : Phi (2 * π / ℓm) < 0 := by
      by_contra h; push_neg at h
      have := (Phi_nonneg_iff (by positivity)).mp h; linarith
    have : 0 < (2 * π / ℓm) ^ 2 := by positivity
    nlinarith
  have hpos : 0 < (2 * π / ℓp) ^ 2 * Phi (2 * π / ℓp) / 2 := by
    have : 0 < Phi (2 * π / ℓp) := (Phi_pos_iff (by positivity)).mpr hτp
    have : 0 < (2 * π / ℓp) ^ 2 := by positivity
    positivity
  have em := (tendsto_F_pi hℓm0).eventually (gt_mem_nhds hneg)
  have ep := (tendsto_F_pi hℓp0).eventually (lt_mem_nhds hpos)
  have e3 : ∀ᶠ α in 𝓝[>] (0 : ℝ), α ∈ Set.Ioo 0 (π / 2) := Ioo_mem_nhdsGT (by linarith [Real.pi_pos])
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp (em.and (ep.and e3))
  refine ⟨δ, hδ, fun α hα => ?_⟩
  have hmem : α ∈ Metric.ball 0 δ ∩ Set.Ioi 0 :=
    ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hα.1]; exact hα.2, hα.1⟩
  obtain ⟨h1, h2, h3⟩ := hball hmem
  have hαπ : α < π := by linarith [h3.2, Real.pi_pos]
  have hs : 0 < sin α := Real.sin_pos_of_pos_of_lt_pi hα.1 hαπ
  refine ⟨fun hst => ?_, ?_⟩
  · have := (rowStable_iff hα.1 hαπ (mul_pos hℓm0 hs)).mp hst; linarith
  · exact (rowStable_iff hα.1 hαπ (mul_pos hℓp0 hs)).mpr h2.le

end HyperbolicRings.Horocycle
