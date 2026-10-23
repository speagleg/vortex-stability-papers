/-
New in this paper (vortex-stability-papers, paper 3). Not copied from the source repositories.

Small spacing (paper, Appendix E, Lemma E.4): at fixed `α ∈ (0, π)`, `ℓ_u² F(π) → -π² sin²α / 4` as the strip
spacing `ℓ_u → 0⁺`. Hence `F(π) < 0` for all sufficiently small spacings: every hypercycle row is unstable when
its vortices are dense enough. (This is the "negative at small spacing" input of the single-threshold argument; it
does not use the dual series.)
-/
import HyperbolicRings.Horocycle.HyperLimit

noncomputable section

namespace HyperbolicRings.Rows

open Real Filter Topology HyperbolicRings.Horocycle

/-- `∑_{m ≥ 0} 1/(2m+1)² = π²/8`. -/
theorem hasSum_odd_sq : HasSum (fun m : ℕ => 1 / ((2 * (m : ℝ) + 1)) ^ 2) (π ^ 2 / 8) := by
  have hz := hasSum_zeta_two
  set f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 with hf
  have he : HasSum (fun k : ℕ => f (2 * k)) (π ^ 2 / 24) := by
    have := hz.mul_left (1 / 4)
    convert this using 1
    · funext k; simp only [hf]; push_cast; ring
    · ring
  have hsum : Summable (fun k : ℕ => f (2 * k + 1)) := by
    have hb := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine Summable.of_nonneg_of_le (fun k => by simp only [hf]; positivity) (fun k => ?_) hb
    simp only [hf]; push_cast
    apply one_div_le_one_div_of_le (by positivity)
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    nlinarith
  have htot := he.even_add_odd hsum.hasSum
  have hu := htot.unique hz
  have hb : ∑' k : ℕ, f (2 * k + 1) = π ^ 2 / 8 := by linarith
  rw [← hb]
  convert hsum.hasSum using 1
  funext m; simp only [hf]; push_cast; ring

section small
variable {α : ℝ} (hα0 : 0 < α) (hαπ : α < π)
include hα0 hαπ

/-- The limit summand: `-2 sin²α/(n+1)²` for even `n` (odd `j = n+1`), `0` otherwise. -/
def gS (α : ℝ) (n : ℕ) : ℝ := if Even n then -2 * sin α ^ 2 / ((n : ℝ) + 1) ^ 2 else 0

theorem hasSum_gS : HasSum (gS α) (-(π ^ 2 * sin α ^ 2 / 4)) := by
  have he : HasSum (fun m : ℕ => gS α (2 * m)) (-(π ^ 2 * sin α ^ 2 / 4)) := by
    have := (hasSum_odd_sq).mul_left (-2 * sin α ^ 2)
    convert this using 1
    · funext m; simp only [gS, if_pos (even_two_mul m)]; push_cast; ring
    · ring
  have ho : HasSum (fun m : ℕ => gS α (2 * m + 1)) 0 := by
    have : (fun m : ℕ => gS α (2 * m + 1)) = fun _ => 0 := by
      funext m; simp only [gS]; rw [if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m))]
    rw [this]; exact hasSum_zero
  simpa using he.even_add_odd ho

theorem sin_sq_pos : 0 < sin α ^ 2 := by
  have := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ; positivity

/-- `ℓ² · term` in the variables `w = (c-1)/ℓ²`, `c = cosh((n+1)ℓ)`. -/
theorem term_small_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    ℓ ^ 2 * term (cos α ^ 2) ℓ π n =
      if Even n then sin α ^ 2 * ((2 * cos α ^ 2 - 1) * cj ℓ n - 1) /
          ((cj ℓ n - 1) / ℓ ^ 2 * (cj ℓ n + 1 - 2 * cos α ^ 2))
      else ℓ ^ 2 * (sin α ^ 2 * ge (cos α ^ 2) (cj ℓ n)) := by
  have hK : cos α ^ 2 < 1 := K_lt_one hα0 hαπ hℓ
  have hs : 1 - cos α ^ 2 = sin α ^ 2 := by rw [← sin_sq_add_cos_sq α]; ring
  have hc := one_lt_cj hℓ n
  have h1 := B0_sub_B1 hK hc
  have h2 := B0_add_B1 hK hc
  have hD := Dd_pos hK hc
  unfold term; rw [cos_pi_mul]
  rcases Nat.even_or_odd n with he | ho
  · rw [if_pos he, (he.add_one).neg_one_pow, mul_neg_one]
    rw [show B0 (cos α ^ 2) (cj ℓ n) + -B1 (cos α ^ 2) (cj ℓ n) = (1 - cos α ^ 2) * go (cos α ^ 2) (cj ℓ n) by
      linarith, hs]
    unfold go Dd
    have : cj ℓ n - 1 ≠ 0 := by linarith
    have : cj ℓ n + 1 - 2 * cos α ^ 2 ≠ 0 := by unfold Dd at hD; linarith
    field_simp
  · rw [if_neg (Nat.not_even_iff_odd.mpr ho), (ho.add_one).neg_one_pow, mul_one, h2, hs]

theorem tendsto_term_small (n : ℕ) :
    Tendsto (fun ℓ => ℓ ^ 2 * term (cos α ^ 2) ℓ π n) (𝓝[>] 0) (𝓝 (gS α n)) := by
  set d := (n : ℝ) + 1 with hd
  have hd0 : 0 < d := by positivity
  have hw := tendsto_w hd0
  have hcos : Tendsto (fun ℓ : ℝ => cosh (d * ℓ)) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun ℓ : ℝ => cosh (d * ℓ)) (𝓝 0) (𝓝 (cosh (d * 0))) :=
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hcj : ∀ ℓ, cj ℓ n = cosh (d * ℓ) := fun ℓ => by unfold cj; rw [hd]
  have hs := sin_sq_pos hα0 hαπ
  have hev : ∀ᶠ ℓ in 𝓝[>] (0 : ℝ), 0 < ℓ := self_mem_nhdsWithin
  rcases Nat.even_or_odd n with he | ho
  · have hden : d ^ 2 / 2 * (1 + 1 - 2 * cos α ^ 2) ≠ 0 := by
      have : 1 + 1 - 2 * cos α ^ 2 = 2 * sin α ^ 2 := by rw [← sin_sq_add_cos_sq α]; ring
      rw [this]; positivity
    have hlim := ((hcos.const_mul (2 * cos α ^ 2 - 1)).sub_const 1).const_mul (sin α ^ 2) |>.div
      (hw.mul ((hcos.add_const 1).sub_const (2 * cos α ^ 2))) hden
    have hval : sin α ^ 2 * ((2 * cos α ^ 2 - 1) * 1 - 1) / (d ^ 2 / 2 * (1 + 1 - 2 * cos α ^ 2)) = gS α n := by
      rw [gS, if_pos he, ← hd]
      have hc2 : cos α ^ 2 = 1 - sin α ^ 2 := by rw [← sin_sq_add_cos_sq α]; ring
      have hsn : sin α ^ 2 ≠ 0 := (sin_sq_pos hα0 hαπ).ne'
      rw [hc2]
      rw [show (2 * (1 - sin α ^ 2) - 1) * 1 - 1 = -2 * sin α ^ 2 by ring,
        show (1 : ℝ) + 1 - 2 * (1 - sin α ^ 2) = 2 * sin α ^ 2 by ring]
      field_simp
    rw [hval] at hlim
    apply hlim.congr'
    filter_upwards [hev] with ℓ hℓ
    rw [term_small_eq hα0 hαπ hℓ, if_pos he, hcj]
    simp only [Pi.div_apply, Pi.sub_apply, Pi.mul_apply, Pi.add_apply]
  · -- the even-j terms: ℓ² · (bounded) → 0
    have hK1 : 1 + 1 - 2 * cos α ^ 2 ≠ 0 := by
      have : 1 + 1 - 2 * cos α ^ 2 = 2 * sin α ^ 2 := by rw [← sin_sq_add_cos_sq α]; ring
      rw [this]; positivity
    have hg : Tendsto (fun ℓ : ℝ => sin α ^ 2 * (((4 * cos α ^ 2 - 1) * cosh (d * ℓ) - (4 * (cos α ^ 2) ^ 2
        - 2 * cos α ^ 2 + 1)) / (cosh (d * ℓ) + 1 - 2 * cos α ^ 2) ^ 2)) (𝓝[>] 0) (𝓝 (sin α ^ 2 *
        (((4 * cos α ^ 2 - 1) * 1 - (4 * (cos α ^ 2) ^ 2 - 2 * cos α ^ 2 + 1)) / (1 + 1 - 2 * cos α ^ 2) ^ 2))) :=
      (((hcos.const_mul _).sub_const _).div (((hcos.add_const 1).sub_const _).pow 2) (pow_ne_zero 2 hK1)).const_mul _
    have hl2 : Tendsto (fun ℓ : ℝ => ℓ ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun ℓ : ℝ => ℓ ^ 2) (𝓝 0) (𝓝 (0 ^ 2)) := (continuous_pow 2).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have hlim := hl2.mul hg
    rw [zero_mul] at hlim
    have hval : gS α n = 0 := by rw [gS, if_neg (Nat.not_even_iff_odd.mpr ho)]
    rw [hval]
    apply hlim.congr'
    filter_upwards [hev] with ℓ hℓ
    rw [term_small_eq hα0 hαπ hℓ, if_neg (Nat.not_even_iff_odd.mpr ho), hcj, ge, Dd]

/-- Domination: `|ℓ² term_n| ≤ 12/(n+1)²` for every `ℓ > 0`. -/
theorem term_small_bound {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    ‖ℓ ^ 2 * term (cos α ^ 2) ℓ π n‖ ≤ 12 * (1 / ((n : ℝ) + 1) ^ 2) := by
  have hK : cos α ^ 2 < 1 := K_lt_one hα0 hαπ hℓ
  have hs := sin_sq_pos hα0 hαπ
  have hs1 : sin α ^ 2 ≤ 1 := by nlinarith [sin_sq_add_cos_sq α]
  have hcK : cos α ^ 2 = 1 - sin α ^ 2 := by rw [← sin_sq_add_cos_sq α]; ring
  have hc := one_lt_cj hℓ n
  have hy : 0 ≤ ((n : ℝ) + 1) * ℓ := by positivity
  have hcl : ((n : ℝ) + 1) ^ 2 * ℓ ^ 2 / 2 ≤ cj ℓ n - 1 := by
    have := HyperbolicRings.Tanh.LargeN.one_add_sq_half_le_cosh hy
    unfold cj; nlinarith
  set c := cj ℓ n with hcdef
  have hc1 : 0 < c - 1 := by linarith
  have hinv : ℓ ^ 2 / (c - 1) ≤ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
    rw [div_le_iff₀ hc1]
    have h2 : 2 * (1 / ((n : ℝ) + 1) ^ 2) * (((n : ℝ) + 1) ^ 2 * ℓ ^ 2 / 2) = ℓ ^ 2 := by field_simp
    have h3 := mul_le_mul_of_nonneg_left hcl (by positivity : (0:ℝ) ≤ 2 * (1 / ((n : ℝ) + 1) ^ 2))
    linarith
  have hDpos := Dd_pos hK hc
  have hDeq : Dd (cos α ^ 2) c = (c - 1) + 2 * sin α ^ 2 := by unfold Dd; rw [hcK]; ring
  have h1 := B0_sub_B1 hK hc
  have h2 := B0_add_B1 hK hc
  have hsK : 1 - cos α ^ 2 = sin α ^ 2 := by rw [hcK]; ring
  rw [Real.norm_eq_abs]
  unfold term; rw [cos_pi_mul]
  have hl2 : 0 < ℓ ^ 2 := by positivity
  rcases Nat.even_or_odd n with he | ho
  · rw [(he.add_one).neg_one_pow, mul_neg_one,
      show B0 (cos α ^ 2) c + -B1 (cos α ^ 2) c = (1 - cos α ^ 2) * go (cos α ^ 2) c by linarith, hsK]
    have hnum : |(2 * cos α ^ 2 - 1) * c - 1| ≤ (c - 1) + 2 := by
      rw [abs_le, hcK]; constructor <;> nlinarith
    have hg : sin α ^ 2 * |go (cos α ^ 2) c| ≤ 2 / (c - 1) := by
      unfold go
      rw [abs_div, abs_of_pos (mul_pos hc1 hDpos), ← mul_div_assoc, div_le_div_iff₀ (mul_pos hc1 hDpos) hc1]
      rw [hDeq]
      have := mul_le_mul_of_nonneg_left hnum hs.le
      nlinarith [mul_le_mul_of_nonneg_right this hc1.le, mul_nonneg (sub_nonneg.mpr hs1) (sq_nonneg (c - 1)),
        mul_pos hc1 hs]
    rw [abs_mul, abs_mul, abs_of_pos hl2, abs_of_pos hs]
    calc ℓ ^ 2 * (sin α ^ 2 * |go (cos α ^ 2) c|) ≤ ℓ ^ 2 * (2 / (c - 1)) := mul_le_mul_of_nonneg_left hg hl2.le
      _ = 2 * (ℓ ^ 2 / (c - 1)) := by ring
      _ ≤ 2 * (2 * (1 / ((n : ℝ) + 1) ^ 2)) := by linarith
      _ ≤ 12 * (1 / ((n : ℝ) + 1) ^ 2) := by nlinarith [show (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) ^ 2 by positivity]
  · rw [(ho.add_one).neg_one_pow, mul_one, h2, hsK]
    have hnum : |(4 * cos α ^ 2 - 1) * c - (4 * (cos α ^ 2) ^ 2 - 2 * cos α ^ 2 + 1)| ≤ 3 * (c - 1) + 6 := by
      rw [abs_le, hcK]; constructor <;> nlinarith
    have hg : sin α ^ 2 * |ge (cos α ^ 2) c| ≤ 6 / (c - 1) := by
      unfold ge
      rw [abs_div, abs_of_pos (pow_pos hDpos 2), ← mul_div_assoc, div_le_div_iff₀ (pow_pos hDpos 2) hc1]
      rw [hDeq]
      have := mul_le_mul_of_nonneg_left hnum hs.le
      nlinarith [mul_le_mul_of_nonneg_right this hc1.le, mul_nonneg (sub_nonneg.mpr hs1) (sq_nonneg (c - 1)),
        mul_pos hc1 hs, mul_pos hs hs]
    rw [abs_mul, abs_mul, abs_of_pos hl2, abs_of_pos hs]
    calc ℓ ^ 2 * (sin α ^ 2 * |ge (cos α ^ 2) c|) ≤ ℓ ^ 2 * (6 / (c - 1)) := mul_le_mul_of_nonneg_left hg hl2.le
      _ = 6 * (ℓ ^ 2 / (c - 1)) := by ring
      _ ≤ 6 * (2 * (1 / ((n : ℝ) + 1) ^ 2)) := by linarith
      _ = 12 * (1 / ((n : ℝ) + 1) ^ 2) := by ring

/-- `ℓ_u² F(π) → -π² sin²α/4` as `ℓ_u → 0⁺` (fixed `α ∈ (0,π)`). -/
theorem tendsto_F_small :
    Tendsto (fun ℓ => ℓ ^ 2 * F (cos α ^ 2) ℓ π) (𝓝[>] 0) (𝓝 (-(π ^ 2 * sin α ^ 2 / 4))) := by
  rw [← (hasSum_gS hα0 hαπ).tsum_eq]
  have e : (fun ℓ => ℓ ^ 2 * F (cos α ^ 2) ℓ π) = fun ℓ => ∑' n, ℓ ^ 2 * term (cos α ^ 2) ℓ π n := by
    funext ℓ; unfold F; rw [tsum_mul_left]
  rw [e]
  refine tendsto_tsum_of_dominated_convergence (f := fun ℓ n => ℓ ^ 2 * term (cos α ^ 2) ℓ π n)
    (bound := fun n => 12 * (1 / ((n : ℝ) + 1) ^ 2)) ?_ (tendsto_term_small hα0 hαπ) ?_
  · have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [Nat.cast_add, Nat.cast_one] using this.mul_left 12
  · filter_upwards [self_mem_nhdsWithin] with ℓ hℓ
    exact term_small_bound hα0 hαπ hℓ

/-- **Dense rows are unstable.** For fixed `α ∈ (0,π)` there is `δ > 0` with `F(π) < 0` for every strip spacing
`0 < ℓ_u < δ`; the pairing mode is then unstable. -/
theorem F_neg_small : ∃ δ > 0, ∀ ℓ ∈ Set.Ioo 0 δ, F (cos α ^ 2) ℓ π < 0 ∧ ¬ RowStable α ℓ := by
  have hlim := tendsto_F_small hα0 hαπ
  have hneg : -(π ^ 2 * sin α ^ 2 / 4) < 0 := by
    have := mul_pos (pow_pos Real.pi_pos 2) (sin_sq_pos hα0 hαπ); linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp (hlim.eventually (gt_mem_nhds hneg))
  refine ⟨δ, hδ, fun ℓ hℓ => ?_⟩
  have hmem : ℓ ∈ Metric.ball 0 δ ∩ Set.Ioi 0 :=
    ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hℓ.1]; exact hℓ.2, hℓ.1⟩
  have h : ℓ ^ 2 * F (cos α ^ 2) ℓ π < 0 := hball hmem
  have hl2 : 0 < ℓ ^ 2 := by have := hℓ.1; positivity
  have hF : F (cos α ^ 2) ℓ π < 0 := by
    by_contra hc; push_neg at hc; nlinarith [mul_nonneg hl2.le hc]
  refine ⟨hF, fun hst => ?_⟩
  have := (rowStable_iff hα0 hαπ hℓ.1).mp hst
  linarith

end small

end HyperbolicRings.Rows
