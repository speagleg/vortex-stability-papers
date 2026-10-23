/-
New module for paper 01-conjecture-13 (not copied; written for this paper).

Montaldi–Tokieda's even-`n` computation (arXiv:1210.5662v1, §3.5.1, p. 21) expands the augmented
Hamiltonian `F = H − ω₀J₃` along the straight line `z_j = (1 + (−1)^j t) e^{2πij/n}`, which leaves the
momentum level set at order `t²`. This module

* derives, from the Hamiltonian of paper eq. (2.1), the jet of `F` along that line:
  `F(line t) − F(ring) = v₂ t² + D t⁴ + O(t⁶)` (`Fline_jet`), with `v₂ = −M·thr/(1+b)²`;
* gives the normalised limit `(F(line t) − F(ring))/ε⁴ → D/n²` at the threshold (`Fline_limit`);
* proves the algebraic bending identity `D + B·u₂ + A·u₂² = n²·c4even(n)` on the threshold
  (`bending_identity`, `bending_at_bn`), where `A, B, u₂` are the stated coefficients (their derivation
  from `F` and `J₃` on the two-parameter family is the exact sympy script `mt_line_vs_levelset.py`);
* at `n = 4`: `D = 6 − 4√3/3 ≈ 3.6906`, so `D/16 ≠ c4even 4 = 1/4` (`n4_line_value`, `n4_line_ne`),
  while along the level-set curve `(H − H₀)/ε⁴ → 1/4` (`EvenQuartic.c4even_limit_at_bn`).
-/
import Conj13.EvenQuartic

open Real Asymptotics Filter Topology

namespace Conj13.MTLine

open Conj13.Config Conj13.Even Conj13.Series Conj13.EvenQuartic

/-- MT's straight line inside the linear slice: radii `ρ± = 1 ± t`. -/
noncomputable def line (M : ℕ) (t : ℝ) : Fin M × Fin 2 → ℂ := stag M (1 + t) (1 - t)

/-- The angular velocity of the ring at `r₀ = 1` (so that `dF(ring) = 0`): `ω₀ = (2M−1)(b²−1)/2`. -/
noncomputable def om0 (M b : ℝ) : ℝ := (2 * M - 1) * (b ^ 2 - 1) / 2

/-- The augmented Hamiltonian along the line. -/
noncomputable def Fline (M : ℕ) (b t : ℝ) : ℝ := Ham b (line M t) - om0 M b * J3 b (line M t)

/-- Auxiliary coefficients: `(1+b(1+t)²)(1+b(1−t)²)/(1+b)² = 1 + α t² + β t⁴`. -/
noncomputable def al (b : ℝ) : ℝ := 2 * b * (1 - b) / (1 + b) ^ 2
noncomputable def be (b : ℝ) : ℝ := b ^ 2 / (1 + b) ^ 2
/-- `g((1+t)²) + g((1−t)²) − 2g(1) = g₂ t² + g₄ t⁴ + O(t⁶)`. -/
noncomputable def g2 (b : ℝ) : ℝ := -2 * (3 * b - 1) / (1 + b) ^ 3
noncomputable def g4 (b : ℝ) : ℝ := -2 * b * (5 * b ^ 2 - 10 * b + 1) / (1 + b) ^ 5

/-- The `t²` coefficient of `F` along the line, as assembled from the pieces. -/
noncomputable def v2 (M b : ℝ) : ℝ :=
  M * (M - 1) + M ^ 2 - M ^ 3 + (2 * M - 1) * M * al b - om0 M b * M * g2 b

/-- The `t⁴` coefficient `D` of `F` along the line (MT's quantity), as assembled from the pieces. -/
noncomputable def Dline (M b : ℝ) : ℝ :=
  M * (M - 1) / 2 + M ^ 2 / 2 - 2 * M * (M ^ 2 / 3 - M ^ 4 / 12)
    + (2 * M - 1) * M * (be b - al b ^ 2 / 2) - om0 M b * M * g4 b

/-- The threshold polynomial: `thr = 0 ⇔` MT (3.7) for `n = 2M`. -/
noncomputable def thr (M b : ℝ) : ℝ := M ^ 2 * (1 + b) ^ 2 - (4 * M - 2) * (1 + b ^ 2)

theorem v2_eq (M b : ℝ) (hb : 1 + b ≠ 0) : v2 M b = -M * thr M b / (1 + b) ^ 2 := by
  unfold v2 al g2 om0 thr; field_simp; ring

theorem v2_eq_h2 (M b : ℝ) (hb : 1 + b ≠ 0) : v2 M b = 4 / (1 + b) ^ 4 * h2 M b := by
  rw [v2_eq M b hb]; unfold h2 thr; field_simp

theorem Dline_eq (M b : ℝ) (hb : 1 + b ≠ 0) :
    Dline M b = M * (M ^ 4 * (1 + b) ^ 4 - 4 * M ^ 2 * (1 + b) ^ 4 + 6 * M * (9 * b ^ 4 - 14 * b ^ 3
      + 26 * b ^ 2 + 2 * b + 1) - 3 * (9 * b ^ 4 - 14 * b ^ 3 + 26 * b ^ 2 + 2 * b + 1)) / (6 * (1 + b) ^ 4) := by
  unfold Dline al be g4 om0; field_simp; ring

/-! ### One-variable jets -/

/-- `log(1 + αt² + βt⁴) = αt² + (β − α²/2)t⁴ + O(t⁶)`. -/
theorem log_quartic_jet (α β : ℝ) :
    (fun t : ℝ => Real.log (1 + α * t ^ 2 + β * t ^ 4) - α * t ^ 2 - (β - α ^ 2 / 2) * t ^ 4)
      =O[𝓝 0] (fun t => t ^ 6) := by
  have hy : (fun t : ℝ => -(α * t ^ 2 + β * t ^ 4)) =O[𝓝 0] (fun t => t ^ 2) := by
    have : (fun t : ℝ => t ^ 2 * (-(α + β * t ^ 2))) =O[𝓝 0] (fun t => t ^ 2) := mul_cont (by fun_prop)
    exact this.congr_left (fun t => by ring)
  have hL := comp_bigO (by norm_num) log_one_sub_jet hy
  have h6 : (fun t : ℝ => t ^ 6 * (α * β + β ^ 2 * t ^ 2 / 2)) =O[𝓝 0] (fun t => t ^ 6) :=
    mul_cont (by fun_prop)
  refine (hL.sub h6).congr_left (fun t => ?_)
  simp only [sub_neg_eq_add]
  ring_nf

/-- `log(1 − t²) = −t² − t⁴/2 + O(t⁶)`. -/
theorem log_one_sub_sq_jet' :
    (fun t : ℝ => Real.log (1 - t ^ 2) + t ^ 2 + t ^ 4 / 2) =O[𝓝 0] (fun t => t ^ 6) := by
  simpa using log_one_sub_sq_jet 1

/-- `log cosh(M·artanh t) = (M²/2)t² + (M²/3 − M⁴/12)t⁴ + O(t⁶)`. -/
theorem log_cosh_ath_jet (M : ℝ) :
    (fun t => Real.log (Real.cosh (M * ath t)) - M ^ 2 / 2 * t ^ 2 - (M ^ 2 / 3 - M ^ 4 / 12) * t ^ 4)
      =O[𝓝 0] (fun t => t ^ 6) := by
  have hY : (fun t => M * ath t - M * t - (M / 3) * t ^ 3) =O[𝓝 0] (fun t => t ^ 5) := by
    refine (artanh_jet.const_mul_left M).congr_left (fun t => ?_)
    simp only [ath]; ring
  refine (log_cosh_comp_jet hY).congr_left (fun t => ?_)
  ring

/-- The polynomial `Q(t) = (1+b(1+t)²)(1+b(1−t)²)`. -/
noncomputable def Qp (b t : ℝ) : ℝ := (1 + b * (1 + t) ^ 2) * (1 + b * (1 - t) ^ 2)

/-- The `J₃` part: `g((1+t)²) + g((1−t)²) − 2g(1) − g₂t² − g₄t⁴ = t⁶ R(t)/((1+b)⁵Q(t))`. -/
theorem gsum_exact (b t : ℝ) (hb : 1 + b ≠ 0) (hq : Qp b t ≠ 0) :
    gfun b ((1 + t) ^ 2) + gfun b ((1 - t) ^ 2) - 2 * gfun b 1 - g2 b * t ^ 2 - g4 b * t ^ 4
      = t ^ 6 * (2 * b ^ 2 * (5 * b ^ 3 * t ^ 2 - 7 * b ^ 3 - 10 * b ^ 2 * t ^ 2 + 35 * b ^ 2 + b * t ^ 2
          - 21 * b + 1) / ((1 + b) ^ 5 * Qp b t)) := by
  have hp : 1 + b * (1 + t) ^ 2 ≠ 0 := fun h => hq (by unfold Qp; rw [h, zero_mul])
  have hm : 1 + b * (1 - t) ^ 2 ≠ 0 := fun h => hq (by unfold Qp; rw [h, mul_zero])
  have hp2 : 1 + (1 + t) ^ 2 * b ≠ 0 := by rwa [mul_comm]
  have hm2 : 1 + (1 - t) ^ 2 * b ≠ 0 := by rwa [mul_comm]
  unfold gfun g2 g4 Qp
  rw [mul_one, div_add_div _ _ hp hm]
  field_simp
  ring

theorem gsum_jet (b : ℝ) (hb : 0 < 1 + b) :
    (fun t => gfun b ((1 + t) ^ 2) + gfun b ((1 - t) ^ 2) - 2 * gfun b 1 - g2 b * t ^ 2 - g4 b * t ^ 4)
      =O[𝓝 0] (fun t => t ^ 6) := by
  have hQ0 : Qp b 0 ≠ 0 := by unfold Qp; simp; positivity
  have hc : ContinuousAt (fun t => 2 * b ^ 2 * (5 * b ^ 3 * t ^ 2 - 7 * b ^ 3 - 10 * b ^ 2 * t ^ 2
      + 35 * b ^ 2 + b * t ^ 2 - 21 * b + 1) / ((1 + b) ^ 5 * Qp b t)) 0 := by
    apply ContinuousAt.div (by fun_prop) (by unfold Qp; fun_prop)
    exact mul_ne_zero (pow_ne_zero 5 hb.ne') hQ0
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), Qp b t ≠ 0 :=
    (show ContinuousAt (Qp b) 0 by unfold Qp; fun_prop).eventually_ne hQ0
  refine (mul_cont hc).congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hev] with t ht
  rw [gsum_exact b t hb.ne' ht]

/-! ### The closed form of `F` along the line, and its jet -/

/-- For `t` near `0`: `F(line t) − F(ring)` in terms of one-variable functions. -/
theorem Fline_closed (M : ℕ) (hM : M ≠ 0) (b t : ℝ) (hb : -1 < b) (ht : |t| < 1)
    (hσp : 0 < 1 + b * (1 + t) ^ 2) (hσm : 0 < 1 + b * (1 - t) ^ 2) :
    Fline M b t - Fline M b 0
      = -(M * (M - 1)) * Real.log (1 - t ^ 2)
        - 2 * M * (M / 2 * Real.log (1 - t ^ 2) + Real.log (Real.cosh (M * ath t)))
        + (2 * M - 1) * M * Real.log (1 + al b * t ^ 2 + be b * t ^ 4)
        - om0 M b * M * (gfun b ((1 + t) ^ 2) + gfun b ((1 - t) ^ 2) - 2 * gfun b 1) := by
  rw [abs_lt] at ht
  have hp : 0 < 1 + t := by linarith
  have hm : 0 < 1 - t := by linarith
  have hb1 : 0 < 1 + b := by linarith
  have hb1' : (0 : ℝ) < 1 + b * 1 ^ 2 := by linarith
  unfold Fline line
  simp only [add_zero, sub_zero]
  rw [J3_stag, J3_stag]
  have hH := Ham_stag_sub M hM b (1 + t) (1 - t) hb hp hm hσp hσm
  -- the pieces
  have hsq : Real.log ((1 + t) ^ 2) + Real.log ((1 - t) ^ 2) = 2 * Real.log (1 - t ^ 2) := by
    rw [Real.log_pow, Real.log_pow, show 1 - t ^ 2 = (1 + t) * (1 - t) by ring,
      Real.log_mul hp.ne' hm.ne']; push_cast; ring
  have hpow := log_half_sum_pow M ((1 + t) ^ 2) ((1 - t) ^ 2) (by positivity) (by positivity)
  rw [Real.sqrt_sq hp.le, Real.sqrt_sq hm.le] at hpow
  have hdiff : (M : ℝ) * (Real.log ((1 + t) ^ 2) - Real.log ((1 - t) ^ 2)) / 4 = M * ath t := by
    unfold ath; rw [Real.log_pow, Real.log_pow]; push_cast; ring
  rw [hdiff, hsq] at hpow
  have hQ : (1 + b * (1 + t) ^ 2) * (1 + b * (1 - t) ^ 2)
      = (1 + b) ^ 2 * (1 + al b * t ^ 2 + be b * t ^ 4) := by
    unfold al be; field_simp; ring
  have hQpos : 0 < 1 + al b * t ^ 2 + be b * t ^ 4 := by
    have := mul_pos hσp hσm
    rw [hQ] at this
    exact pos_of_mul_pos_right this (by positivity)
  have hsig : Real.log (1 + b * (1 + t) ^ 2) + Real.log (1 + b * (1 - t) ^ 2) - 2 * Real.log (1 + b)
      = Real.log (1 + al b * t ^ 2 + be b * t ^ 4) := by
    rw [← Real.log_mul hσp.ne' hσm.ne', hQ, Real.log_mul (by positivity) hQpos.ne', Real.log_pow]
    push_cast; ring
  rw [hpow, hsq, hsig] at hH
  simp only [one_pow]
  linear_combination hH

/-- **The jet of `F` along MT's line**, derived from the Hamiltonian: for `|b| < 1`,
`F(line t) − F(ring) − v₂ t² − D t⁴ = O(t⁶)`. -/
theorem Fline_jet (M : ℕ) (hM : M ≠ 0) (b : ℝ) (hb : |b| < 1) :
    (fun t => Fline M b t - Fline M b 0 - v2 M b * t ^ 2 - Dline M b * t ^ 4)
      =O[𝓝 0] (fun t => t ^ 6) := by
  have hb' := abs_lt.mp hb
  have hb1 : 0 < 1 + b := by linarith
  have hJ := ((((log_one_sub_sq_jet'.const_mul_left (-(M * (M - 1) : ℝ))).sub
    ((log_one_sub_sq_jet'.const_mul_left ((M : ℝ) / 2)).add (log_cosh_ath_jet M) |>.const_mul_left
      (2 * (M : ℝ)))).add ((log_quartic_jet (al b) (be b)).const_mul_left ((2 * M - 1) * M))).sub
    ((gsum_jet b hb1).const_mul_left (om0 M b * M)))
  have hev1 : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < 1 :=
    (continuous_abs.continuousAt (x := (0 : ℝ))).eventually_lt continuousAt_const (by simp)
  have hev2 : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < 1 + b * (1 + t) ^ 2 :=
    continuousAt_const.eventually_lt (show ContinuousAt (fun t : ℝ => 1 + b * (1 + t) ^ 2) 0 by fun_prop)
      (by simpa using hb1)
  have hev3 : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < 1 + b * (1 - t) ^ 2 :=
    continuousAt_const.eventually_lt (show ContinuousAt (fun t : ℝ => 1 + b * (1 - t) ^ 2) 0 by fun_prop)
      (by simpa using hb1)
  refine hJ.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hev1, hev2, hev3] with t h1 h2 h3
  rw [Fline_closed M hM b t hb'.1 h1 h2 h3]
  unfold v2 Dline
  ring

/-! ### The normalised limit along the line -/

/-- `ε = ⟨q − x₀, e⟩ = √n · t` exactly on the line (`n = 2M`). -/
theorem epsK_line (M : ℕ) (hM : M ≠ 0) (t : ℝ) : epsK M (line M t) = √(2 * M) * t := by
  unfold line; rw [(epsK_stag M hM _ _).1]; ring

/-- **At the threshold** (`thr = 0`, i.e. `v₂ = 0`): along MT's line
`(F(line t) − F(ring))/ε⁴ → D/n²`. -/
theorem Fline_limit (M : ℕ) (hM : M ≠ 0) (b : ℝ) (hb : |b| < 1) (hthr : thr M b = 0) :
    Tendsto (fun t => (Fline M b t - Fline M b 0) / epsK M (line M t) ^ 4) (𝓝[≠] 0)
      (𝓝 (Dline M b / (2 * M) ^ 2)) := by
  have hb1 : 1 + b ≠ 0 := by have := (abs_lt.mp hb).1; intro h; linarith
  have hv : v2 M b = 0 := by rw [v2_eq M b hb1, hthr]; simp
  have hjet := Fline_jet M hM b hb
  rw [hv] at hjet
  have hq : Tendsto (fun t => (Fline M b t - Fline M b 0 - Dline M b * t ^ 4) * (t ^ 4)⁻¹)
      (𝓝[≠] 0) (𝓝 0) := by
    have h1 := (hjet.mono nhdsWithin_le_nhds).mul (isBigO_refl (fun t : ℝ => (t ^ 4)⁻¹) (𝓝[≠] 0))
    have h2 : Tendsto (fun t : ℝ => t ^ 6 * (t ^ 4)⁻¹) (𝓝[≠] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => t ^ 2) (𝓝[≠] 0) (𝓝 0) := by
        have hc : Continuous (fun t : ℝ => t ^ 2) := by fun_prop
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      field_simp
    refine (h1.trans_tendsto h2).congr' ?_
    filter_upwards with t
    simp only [zero_mul, sub_zero]
  have hΦ4 : Tendsto (fun t => (Fline M b t - Fline M b 0) / t ^ 4) (𝓝[≠] 0) (𝓝 (Dline M b)) := by
    have := hq.add_const (Dline M b)
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have : t ^ 4 ≠ 0 := pow_ne_zero 4 ht
    rw [sub_mul, mul_inv_cancel_right₀ this, div_eq_mul_inv]
    ring
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  have hlim := hΦ4.div_const (4 * (M : ℝ) ^ 2)
  rw [show Dline M b / (4 * (M : ℝ) ^ 2) = Dline M b / (2 * M) ^ 2 by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  have hsq : √(2 * (M : ℝ)) ^ 2 = 2 * M := Real.sq_sqrt (by positivity)
  rw [epsK_line M hM t, mul_pow, show √(2 * (M : ℝ)) ^ 4 = (√(2 * (M : ℝ)) ^ 2) ^ 2 by ring, hsq]
  field_simp
  ring

/-! ### The level-set bending identity -/

/-- `A`: the coefficient of `u²` in `F` on the family `ρ± = 1 + u ± v` (radial `V₀` weight). -/
noncomputable def Aline (M b : ℝ) : ℝ := 2 * M * (2 * M - 1) * (1 + b ^ 2) / (1 + b) ^ 2
/-- `B`: the coefficient of `u v²`. -/
noncomputable def Bline (M b : ℝ) : ℝ :=
  2 * M * (M ^ 2 * (1 + b) ^ 3 - 2 * M * (5 * b ^ 3 - 3 * b ^ 2 + 9 * b + 1)
    + (5 * b ^ 3 - 3 * b ^ 2 + 9 * b + 1)) / (1 + b) ^ 3
/-- `u₂`: on the level set `J₃ = J₃(ring)`, `u = u₂ v² + O(v⁴)`. -/
noncomputable def u2 (b : ℝ) : ℝ := (3 * b - 1) / (2 * (1 + b))

/-- **Bending identity** (exact, no threshold assumed). -/
theorem bending_identity (M b : ℝ) (hM : M ≠ 0) (hM1 : 2 * M - 1 ≠ 0) (hb : 1 + b ≠ 0) :
    Dline M b + Bline M b * u2 b + Aline M b * u2 b ^ 2 - (2 * M) ^ 2 * c4even (2 * M)
      = thr M b * (M * (3 * M ^ 2 * (1 + b) ^ 2 + 8 * M * (b ^ 2 - 3 * b - 1) - 4 * (b ^ 2 - 3 * b - 1)))
        / (2 * (2 * M - 1) * (1 + b) ^ 4) := by
  rw [Dline_eq M b hb]
  have h2M : M * 2 - 1 ≠ 0 := by intro h; apply hM1; linarith
  have h2M' : 2 * M ≠ 0 := by positivity
  unfold Bline Aline u2 thr c4even
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hM1) (pow_ne_zero 4 hb))]
  field_simp
  ring

/-- **At the threshold `b_n`** (every even `n = 2M ≥ 4`): the line quartic `D` plus the bending
contribution `B u₂ + A u₂²` is exactly `n² c₄`, the level-set value of paper Thm even. -/
theorem bending_at_bn (M : ℕ) (hM : 2 ≤ M) :
    Dline M (bn (2 * M)) + Bline M (bn (2 * M)) * u2 (bn (2 * M)) + Aline M (bn (2 * M)) * u2 (bn (2 * M)) ^ 2
      = (2 * M) ^ 2 * c4even (2 * (M : ℝ)) := by
  obtain ⟨h1, -, -⟩ := bn_spec (2 * M) (by omega)
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hthr : thr M (bn (2 * M)) = 0 := by
    have := even_rel_bn M hM; unfold thr; linarith
  have := bending_identity M (bn (2 * M)) (by positivity) (by linarith) (by linarith)
  rw [hthr, zero_mul, zero_div, sub_eq_zero] at this
  exact this

/-! ### `n = 4` -/

theorem thr_four : thr 2 (2 - √3) = 0 := by
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold thr; linear_combination (-2 : ℝ) * hs

/-- **`n = 4`, MT's line**: `D = 6 − 4√3/3 ≈ 3.6906` at `b₄ = 2 − √3`. -/
theorem n4_line_value : Dline 2 (2 - √3) = 6 - 4 * √3 / 3 := by
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3 : (1 : ℝ) + (2 - √3) ≠ 0 := by
    have : √3 < 2 := by rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  rw [Dline_eq 2 (2 - √3) h3, div_eq_iff (by positivity)]
  linear_combination (8 * √3 ^ 3 + 30 * √3 ^ 2 - 156 * √3 + 126) * hs

/-- **`n = 4`: line versus level set.** The line value `D/n² = (6 − 4√3/3)/16` differs from the
level-set value `c4even 4 = 1/4` (equivalently `D ≠ 4`). -/
theorem n4_line_ne : Dline 2 (2 - √3) / (2 * 2) ^ 2 ≠ c4even (4 : ℝ) ∧ c4even (4 : ℝ) = 1 / 4 := by
  have hc : c4even (4 : ℝ) = 1 / 4 := by unfold c4even; norm_num
  refine ⟨?_, hc⟩
  rw [n4_line_value, hc]
  intro h
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have : √3 = 3 / 2 := by linarith
  rw [this] at hs; norm_num at hs

/-- **`n = 4`, the limit along MT's line** at `b₄ = 2 − √3`:
`(F(line t) − F(ring))/ε⁴ → (6 − 4√3/3)/16 ≈ 0.2307`, whereas along the level set the limit is
`1/4` (`EvenQuartic.c4even_limit_at_bn 2`). -/
theorem n4_line_limit :
    Tendsto (fun t => (Fline 2 (2 - √3) t - Fline 2 (2 - √3) 0) / epsK 2 (line 2 t) ^ 4) (𝓝[≠] 0)
      (𝓝 ((6 - 4 * √3 / 3) / 16)) := by
  have hs3 : √3 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs1 : 1 < √3 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hb : |2 - √3| < 1 := by rw [abs_lt]; constructor <;> linarith
  have := Fline_limit 2 (by norm_num) (2 - √3) hb (by exact_mod_cast thr_four)
  simp only [Nat.cast_ofNat] at this
  rw [n4_line_value] at this
  convert this using 2; norm_num

end Conj13.MTLine
