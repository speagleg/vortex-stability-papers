/-
New module for paper 01-conjecture-13 (not copied).

The two-parameter `D_{n/2}`-invariant family `ρ± = 1 + u ± v` of paper §6, eq. (6.1). Restricting to the curves
`u = κ v²` (every `κ ∈ ℝ`) turns the two-variable jet into one-variable jets, which we derive from the Hamiltonian:

* `Ffam_jet`: `F(κv², v) − F₀ = v₂ v² + (A κ² + B κ + D) v⁴ + O(v⁶)` for every `κ`, with `v₂`, `A`, `B`, `D`
  exactly the coefficients `MTLine.v2`, `Aline`, `Bline`, `Dline` (`c2fam_eq`, `c4fam_eq`). Since a quadratic
  polynomial in `κ` determines its coefficients, this identifies `A`, `B`, `D` as the coefficients of
  `u²`, `u v²`, `v⁴` in `F` (paper eq. (6.1)).
* `J3fam_jet`, `gc2_eq_zero_iff`: `J₃(κv², v) − J₃(ring) = M·g₂(κ) v² + O(v⁴)` with `g₂(κ) = 0 ⇔ κ = u₂`, so the
  momentum level set is `u = u₂v² + O(v⁴)`, `u₂ = (3b−1)/(2(1+b))`.
* `level_quartic_at_bn`: at `b_n` the quartic along `u = u₂v²` is `n² c₄` (via `MTLine.bending_at_bn`).
-/
import Conj13.MTLine

open Real Asymptotics Filter Topology

namespace Conj13.MTFamily

open Conj13.Config Conj13.Even Conj13.Series Conj13.EvenQuartic Conj13.MTLine

/-! ### Generic jets -/

/-- `log(1 + αt² + βt⁴ + t⁶ r(t)) = αt² + (β − α²/2)t⁴ + O(t⁶)` for `r` continuous at `0`. -/
theorem log_sextic_jet (α β : ℝ) {r : ℝ → ℝ} (hr : ContinuousAt r 0) :
    (fun t : ℝ => Real.log (1 + α * t ^ 2 + β * t ^ 4 + t ^ 6 * r t) - α * t ^ 2 - (β - α ^ 2 / 2) * t ^ 4)
      =O[𝓝 0] (fun t => t ^ 6) := by
  have hy : (fun t : ℝ => -(α * t ^ 2 + β * t ^ 4 + t ^ 6 * r t)) =O[𝓝 0] (fun t => t ^ 2) := by
    have : (fun t : ℝ => t ^ 2 * (-(α + β * t ^ 2 + t ^ 4 * r t))) =O[𝓝 0] (fun t => t ^ 2) :=
      mul_cont (by fun_prop)
    exact this.congr_left (fun t => by ring)
  have hL := comp_bigO (by norm_num) log_one_sub_jet hy
  have h6 : (fun t : ℝ => t ^ 6 * (r t - (2 * α * β + β ^ 2 * t ^ 2 + 2 * α * t ^ 2 * r t
      + 2 * β * t ^ 4 * r t + t ^ 6 * r t ^ 2) / 2)) =O[𝓝 0] (fun t => t ^ 6) := mul_cont (by fun_prop)
  refine (hL.add h6).congr_left (fun t => ?_)
  simp only [sub_neg_eq_add]
  ring_nf

/-- A rational jet: `N/D = (n₂/d₀)t² + ((n₄ − n₂d₂/d₀)/d₀)t⁴ + O(t⁶)` for `N = n₂t² + n₄t⁴ + t⁶ nr(t)`,
`D = d₀ + d₂t² + t⁴ dr(t)`, `d₀ ≠ 0`, `nr, dr` continuous at `0`. -/
theorem rat_jet (n2 n4 d0 d2 : ℝ) {nr dr : ℝ → ℝ} (hd0 : d0 ≠ 0) (hnr : ContinuousAt nr 0)
    (hdr : ContinuousAt dr 0) :
    (fun t : ℝ => (n2 * t ^ 2 + n4 * t ^ 4 + t ^ 6 * nr t) / (d0 + d2 * t ^ 2 + t ^ 4 * dr t)
        - n2 / d0 * t ^ 2 - (n4 - n2 / d0 * d2) / d0 * t ^ 4) =O[𝓝 0] (fun t => t ^ 6) := by
  set c2 := n2 / d0
  set c4 := (n4 - n2 / d0 * d2) / d0
  have hD : ContinuousAt (fun t : ℝ => d0 + d2 * t ^ 2 + t ^ 4 * dr t) 0 := by fun_prop
  have hD0 : (fun t : ℝ => d0 + d2 * t ^ 2 + t ^ 4 * dr t) 0 ≠ 0 := by simpa using hd0
  have hev := hD.eventually_ne hD0
  have hq : ContinuousAt (fun t => (nr t - c2 * dr t - c4 * d2 - c4 * t ^ 2 * dr t)
      / (d0 + d2 * t ^ 2 + t ^ 4 * dr t)) 0 := ContinuousAt.div (by fun_prop) hD hD0
  refine (mul_cont hq).congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hev] with t ht
  have hn2 : n2 = c2 * d0 := by simp only [c2]; field_simp
  have hn4 : n4 = c4 * d0 + c2 * d2 := by simp only [c4, c2]; field_simp; ring
  clear_value c2 c4
  subst hn2 hn4
  rw [← mul_div_assoc, div_eq_iff ht, sub_mul, sub_mul, div_mul_cancel₀ _ ht]
  ring

/-- `M·artanh(v/(1+κv²)) = Mv + M(1/3 − κ)v³ + O(v⁵)`. -/
theorem ath_w_jet (M κ : ℝ) :
    (fun v => M * ath (v / (1 + κ * v ^ 2)) - M * v - (M * (1 / 3 - κ)) * v ^ 3)
      =O[𝓝 0] (fun v => v ^ 5) := by
  set w : ℝ → ℝ := fun v => v / (1 + κ * v ^ 2) with hwdef
  have hc : ContinuousAt (fun v : ℝ => 1 + κ * v ^ 2) 0 := by fun_prop
  have hev : ∀ᶠ v in 𝓝 (0 : ℝ), 1 + κ * v ^ 2 ≠ 0 := hc.eventually_ne (by simp)
  have hinv : ContinuousAt (fun v : ℝ => 1 / (1 + κ * v ^ 2)) 0 := ContinuousAt.div (by fun_prop) hc (by simp)
  have hw1 : w =O[𝓝 0] (fun v => v ^ 1) := by
    refine (mul_cont hinv).congr_left (fun v => ?_)
    simp only [hwdef, pow_one]; ring
  have hA := comp_bigO (by norm_num) artanh_jet hw1
  -- `w − v + κv³ = κ²v⁵/(1+κv²)`
  have hB : (fun v => w v - v + κ * v ^ 3) =O[𝓝 0] (fun v => v ^ 5) := by
    have : (fun v : ℝ => v ^ 5 * (κ ^ 2 * (1 / (1 + κ * v ^ 2)))) =O[𝓝 0] (fun v => v ^ 5) :=
      mul_cont (continuousAt_const.mul hinv)
    refine this.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [hev] with v hv
    have hv' : 1 + v ^ 2 * κ ≠ 0 := by rwa [mul_comm]
    simp only [hwdef]; field_simp; ring
  -- `w³ − v³ = (w − v)(w² + wv + v²) = O(v⁵)`
  have hm : (fun v => w v - v) =O[𝓝 0] (fun v => v ^ 3) := by
    have : (fun v : ℝ => v ^ 3 * (-κ * (1 / (1 + κ * v ^ 2)))) =O[𝓝 0] (fun v => v ^ 3) :=
      mul_cont (continuousAt_const.mul hinv)
    refine this.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [hev] with v hv
    have hv' : 1 + v ^ 2 * κ ≠ 0 := by rwa [mul_comm]
    simp only [hwdef]; field_simp; ring
  have hq : (fun v => w v ^ 2 + w v * v + v ^ 2) =O[𝓝 0] (fun v => v ^ 2) := by
    have : (fun v : ℝ => v ^ 2 * ((1 / (1 + κ * v ^ 2)) ^ 2 + 1 / (1 + κ * v ^ 2) + 1)) =O[𝓝 0]
        (fun v => v ^ 2) := mul_cont (by fun_prop)
    refine this.congr_left (fun v => ?_)
    simp only [hwdef]; ring
  have hC : (fun v => (w v - v) * (w v ^ 2 + w v * v + v ^ 2)) =O[𝓝 0] (fun v => v ^ 5) :=
    mul_pow_bigO hm hq
  have := ((hA.add hB).add (hC.const_mul_left (1 / 3))).const_mul_left M
  refine this.congr_left (fun v => ?_)
  simp only [hwdef, ath]
  ring

/-! ### The family -/

/-- `ρ± = 1 + κv² ± v`. -/
noncomputable def fam (M : ℕ) (κ v : ℝ) : Fin M × Fin 2 → ℂ := stag M (1 + κ * v ^ 2 + v) (1 + κ * v ^ 2 - v)

/-- `F = H − ω₀J₃` on the family. -/
noncomputable def Ffam (M : ℕ) (b κ v : ℝ) : ℝ := Ham b (fam M κ v) - om0 M b * J3 b (fam M κ v)

/-- `(1+bρ₊²)(1+bρ₋²)/(1+b)² = 1 + α v² + β v⁴ + v⁶ r(v)`. -/
noncomputable def fa (b κ : ℝ) : ℝ := 2 * b * (2 * b * κ - b + 2 * κ + 1) / (1 + b) ^ 2
noncomputable def fb (b κ : ℝ) : ℝ := b * (6 * b * κ ^ 2 - 4 * b * κ + b + 2 * κ ^ 2) / (1 + b) ^ 2
noncomputable def fr (b κ v : ℝ) : ℝ := b ^ 2 * κ ^ 2 * (κ ^ 2 * v ^ 2 + 4 * κ - 2) / (1 + b) ^ 2
noncomputable def Pf (b κ v : ℝ) : ℝ := 1 + fa b κ * v ^ 2 + fb b κ * v ^ 4 + v ^ 6 * fr b κ v

/-- The numerator of `g(ρ₊²) + g(ρ₋²) − 2g(1)` over `(1+b)³P`. -/
noncomputable def gn2 (b κ : ℝ) : ℝ := 2 * (2 * b * κ - 3 * b + 2 * κ + 1)
noncomputable def gn4 (b κ : ℝ) : ℝ := 2 * (5 * b * κ ^ 2 - 4 * b * κ + b + κ ^ 2)
noncomputable def gnr (b κ v : ℝ) : ℝ := 2 * b * κ ^ 2 * (κ ^ 2 * v ^ 2 + 4 * κ - 2)

/-- The `v²` and `v⁴` coefficients of the `J₃` part (`rat_jet` outputs). -/
noncomputable def gc2 (b κ : ℝ) : ℝ := gn2 b κ / (1 + b) ^ 3
noncomputable def gc4 (b κ : ℝ) : ℝ := (gn4 b κ - gn2 b κ / (1 + b) ^ 3 * ((1 + b) ^ 3 * fa b κ)) / (1 + b) ^ 3

/-- The assembled `v²` and `v⁴` coefficients of `F` on `u = κv²`. -/
noncomputable def c2fam (M b κ : ℝ) : ℝ :=
  -(M * (M - 1)) * (2 * κ - 1) - 2 * M * (M / 2 * (2 * κ - 1) + M ^ 2 / 2)
    + (2 * M - 1) * M * fa b κ - om0 M b * M * gc2 b κ
noncomputable def c4fam (M b κ : ℝ) : ℝ :=
  -(M * (M - 1)) * (κ ^ 2 - (2 * κ - 1) ^ 2 / 2)
    - 2 * M * (M / 2 * (κ ^ 2 - (2 * κ - 1) ^ 2 / 2) + (M * (M * (1 / 3 - κ)) - M ^ 4 / 12))
    + (2 * M - 1) * M * (fb b κ - fa b κ ^ 2 / 2) - om0 M b * M * gc4 b κ

theorem c2fam_eq (M b κ : ℝ) (hb : 1 + b ≠ 0) : c2fam M b κ = v2 M b := by
  unfold c2fam v2 gc2 gn2 om0 al g2
  unfold fa
  field_simp; ring

/-- **The coefficients `A`, `B`, `D` of paper eq. (6.1)**: on `u = κv²` the `v⁴` coefficient of `F` is
`Aκ² + Bκ + D`. -/
theorem c4fam_eq (M b κ : ℝ) (hb : 1 + b ≠ 0) :
    c4fam M b κ = Aline M b * κ ^ 2 + Bline M b * κ + Dline M b := by
  rw [Dline_eq M b hb]
  unfold c4fam gc4 gn2 gn4 Aline Bline om0
  unfold fa fb
  field_simp; ring

/-- The `J₃` part as an exact quotient. -/
theorem gsum_fam (b κ v : ℝ) (hb : 1 + b ≠ 0) (hp : 1 + b * (1 + κ * v ^ 2 + v) ^ 2 ≠ 0)
    (hm : 1 + b * (1 + κ * v ^ 2 - v) ^ 2 ≠ 0) :
    gfun b ((1 + κ * v ^ 2 + v) ^ 2) + gfun b ((1 + κ * v ^ 2 - v) ^ 2) - 2 * gfun b 1
      = (gn2 b κ * v ^ 2 + gn4 b κ * v ^ 4 + v ^ 6 * gnr b κ v)
        / ((1 + b) ^ 3 + (1 + b) ^ 3 * fa b κ * v ^ 2 + v ^ 4 * ((1 + b) ^ 3 * (fb b κ + v ^ 2 * fr b κ v))) := by
  have hp2 : 1 + (1 + κ * v ^ 2 + v) ^ 2 * b ≠ 0 := by rwa [mul_comm]
  have hm2 : 1 + (1 + κ * v ^ 2 - v) ^ 2 * b ≠ 0 := by rwa [mul_comm]
  have hden : (1 + b) ^ 3 + (1 + b) ^ 3 * fa b κ * v ^ 2 + v ^ 4 * ((1 + b) ^ 3 * (fb b κ + v ^ 2 * fr b κ v))
      = (1 + b) * ((1 + b * (1 + κ * v ^ 2 + v) ^ 2) * (1 + b * (1 + κ * v ^ 2 - v) ^ 2)) := by
    unfold fa fb fr; field_simp; ring
  rw [hden]
  unfold gfun gn2 gn4 gnr
  rw [mul_one, div_add_div _ _ hp hm]
  field_simp
  ring

/-- `F(κv², v) − F₀` in terms of one-variable functions, for `v` near `0`. -/
theorem Ffam_closed (M : ℕ) (hM : M ≠ 0) (b κ v : ℝ) (hb : -1 < b) (hp : 0 < 1 + κ * v ^ 2 + v)
    (hm : 0 < 1 + κ * v ^ 2 - v) (hσp : 0 < 1 + b * (1 + κ * v ^ 2 + v) ^ 2)
    (hσm : 0 < 1 + b * (1 + κ * v ^ 2 - v) ^ 2) :
    Ffam M b κ v - Ffam M b κ 0
      = -(M * (M - 1)) * Real.log (1 + (2 * κ - 1) * v ^ 2 + κ ^ 2 * v ^ 4)
        - 2 * M * (M / 2 * Real.log (1 + (2 * κ - 1) * v ^ 2 + κ ^ 2 * v ^ 4)
          + Real.log (Real.cosh (M * ath (v / (1 + κ * v ^ 2)))))
        + (2 * M - 1) * M * Real.log (Pf b κ v)
        - om0 M b * M * (gfun b ((1 + κ * v ^ 2 + v) ^ 2) + gfun b ((1 + κ * v ^ 2 - v) ^ 2) - 2 * gfun b 1) := by
  have hb1 : 0 < 1 + b := by linarith
  have hk : 0 < 1 + κ * v ^ 2 := by linarith
  have hk' : 1 + v ^ 2 * κ ≠ 0 := by rw [mul_comm]; exact hk.ne'
  have hprod : (1 + κ * v ^ 2 + v) * (1 + κ * v ^ 2 - v) = 1 + (2 * κ - 1) * v ^ 2 + κ ^ 2 * v ^ 4 := by ring
  have hPpos : 0 < 1 + (2 * κ - 1) * v ^ 2 + κ ^ 2 * v ^ 4 := by rw [← hprod]; positivity
  unfold Ffam fam
  simp only [mul_zero, zero_pow two_ne_zero, add_zero, sub_zero]
  rw [J3_stag, J3_stag]
  have hH := Ham_stag_sub M hM b (1 + κ * v ^ 2 + v) (1 + κ * v ^ 2 - v) hb hp hm hσp hσm
  have hsq : Real.log ((1 + κ * v ^ 2 + v) ^ 2) + Real.log ((1 + κ * v ^ 2 - v) ^ 2)
      = 2 * Real.log (1 + (2 * κ - 1) * v ^ 2 + κ ^ 2 * v ^ 4) := by
    rw [Real.log_pow, Real.log_pow, ← hprod, Real.log_mul hp.ne' hm.ne']; push_cast; ring
  have hpow := log_half_sum_pow M ((1 + κ * v ^ 2 + v) ^ 2) ((1 + κ * v ^ 2 - v) ^ 2) (by positivity) (by positivity)
  rw [Real.sqrt_sq hp.le, Real.sqrt_sq hm.le] at hpow
  have hw1 : 0 < 1 + v / (1 + κ * v ^ 2) := by
    rw [show 1 + v / (1 + κ * v ^ 2) = (1 + κ * v ^ 2 + v) / (1 + κ * v ^ 2) by field_simp]; positivity
  have hw2 : 0 < 1 - v / (1 + κ * v ^ 2) := by
    rw [show 1 - v / (1 + κ * v ^ 2) = (1 + κ * v ^ 2 - v) / (1 + κ * v ^ 2) by field_simp]; positivity
  have hdiff : (M : ℝ) * (Real.log ((1 + κ * v ^ 2 + v) ^ 2) - Real.log ((1 + κ * v ^ 2 - v) ^ 2)) / 4
      = M * ath (v / (1 + κ * v ^ 2)) := by
    have e1 : 1 + κ * v ^ 2 + v = (1 + κ * v ^ 2) * (1 + v / (1 + κ * v ^ 2)) := by field_simp
    have e2 : 1 + κ * v ^ 2 - v = (1 + κ * v ^ 2) * (1 - v / (1 + κ * v ^ 2)) := by field_simp
    unfold ath
    rw [Real.log_pow, Real.log_pow, e1, e2, Real.log_mul hk.ne' hw1.ne', Real.log_mul hk.ne' hw2.ne']
    push_cast; ring
  rw [hdiff, hsq] at hpow
  have hQ : (1 + b * (1 + κ * v ^ 2 + v) ^ 2) * (1 + b * (1 + κ * v ^ 2 - v) ^ 2) = (1 + b) ^ 2 * Pf b κ v := by
    unfold Pf fa fb fr; field_simp; ring
  have hPf : 0 < Pf b κ v := by
    have := mul_pos hσp hσm
    rw [hQ] at this
    exact pos_of_mul_pos_right this (by positivity)
  have hsig : Real.log (1 + b * (1 + κ * v ^ 2 + v) ^ 2) + Real.log (1 + b * (1 + κ * v ^ 2 - v) ^ 2)
      - 2 * Real.log (1 + b) = Real.log (Pf b κ v) := by
    rw [← Real.log_mul hσp.ne' hσm.ne', hQ, Real.log_mul (by positivity) hPf.ne', Real.log_pow]
    push_cast; ring
  rw [hsq, hpow, hsig] at hH
  have hone : (1 : ℝ) + κ * 0 ^ 2 = 1 := by simp
  simp only [one_pow] at hH ⊢
  linear_combination hH

/-- **The jet of `F` on `u = κv²`, derived from the Hamiltonian** (`|b| < 1`, every `κ`):
`F(κv², v) − F₀ − v₂v² − (Aκ² + Bκ + D)v⁴ = O(v⁶)`. -/
theorem Ffam_jet (M : ℕ) (hM : M ≠ 0) (b κ : ℝ) (hb : |b| < 1) :
    (fun v => Ffam M b κ v - Ffam M b κ 0 - v2 M b * v ^ 2
        - (Aline M b * κ ^ 2 + Bline M b * κ + Dline M b) * v ^ 4) =O[𝓝 0] (fun v => v ^ 6) := by
  have hb' := abs_lt.mp hb
  have hb1 : 0 < 1 + b := by linarith
  have hL1 : (fun t : ℝ => Real.log (1 + (2 * κ - 1) * t ^ 2 + κ ^ 2 * t ^ 4) - (2 * κ - 1) * t ^ 2
      - (κ ^ 2 - (2 * κ - 1) ^ 2 / 2) * t ^ 4) =O[𝓝 0] (fun t => t ^ 6) := log_quartic_jet _ _
  have hC := log_cosh_comp_jet (ath_w_jet M κ)
  have hP : (fun t : ℝ => Real.log (Pf b κ t) - fa b κ * t ^ 2 - (fb b κ - fa b κ ^ 2 / 2) * t ^ 4)
      =O[𝓝 0] (fun t => t ^ 6) := by
    have := log_sextic_jet (fa b κ) (fb b κ) (r := fun t => fr b κ t) (by unfold fr; fun_prop)
    exact this.congr_left (fun t => by unfold Pf; rfl)
  have hG : (fun t : ℝ => (gn2 b κ * t ^ 2 + gn4 b κ * t ^ 4 + t ^ 6 * gnr b κ t)
        / ((1 + b) ^ 3 + (1 + b) ^ 3 * fa b κ * t ^ 2 + t ^ 4 * ((1 + b) ^ 3 * (fb b κ + t ^ 2 * fr b κ t)))
        - gc2 b κ * t ^ 2 - gc4 b κ * t ^ 4) =O[𝓝 0] (fun t => t ^ 6) :=
    rat_jet _ _ _ _ (pow_ne_zero 3 hb1.ne') (by unfold gnr; fun_prop) (by unfold fr; fun_prop)
  have hJ := (((hL1.const_mul_left (-((M : ℝ) * (M - 1)))).sub
    (((hL1.const_mul_left ((M : ℝ) / 2)).add hC).const_mul_left (2 * (M : ℝ)))).add
      (hP.const_mul_left ((2 * (M : ℝ) - 1) * M))).sub (hG.const_mul_left (om0 M b * M))
  -- eventual positivity conditions
  have ev := fun (f : ℝ → ℝ) (hf : ContinuousAt f 0) (h0 : 0 < f 0) =>
    (continuousAt_const.eventually_lt hf h0 : ∀ᶠ v in 𝓝 (0 : ℝ), 0 < f v)
  have e1 := ev (fun v => 1 + κ * v ^ 2 + v) (by fun_prop) (by simp)
  have e2 := ev (fun v => 1 + κ * v ^ 2 - v) (by fun_prop) (by simp)
  have e3 := ev (fun v => 1 + b * (1 + κ * v ^ 2 + v) ^ 2) (by fun_prop) (by simpa using hb1)
  have e4 := ev (fun v => 1 + b * (1 + κ * v ^ 2 - v) ^ 2) (by fun_prop) (by simpa using hb1)
  refine hJ.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [e1, e2, e3, e4] with v h1 h2 h3 h4
  rw [Ffam_closed M hM b κ v hb'.1 h1 h2 h3 h4, gsum_fam b κ v hb1.ne' h3.ne' h4.ne',
    ← c2fam_eq M b κ hb1.ne', ← c4fam_eq M b κ hb1.ne']
  unfold c2fam c4fam
  ring

/-- **The level set**: `J₃(κv², v) − J₃(ring) = M g₂(κ) v² + O(v⁴)`. -/
theorem J3fam_jet (M : ℕ) (b κ : ℝ) (hb : -1 < b) :
    (fun v => J3 b (fam M κ v) - J3 b (fam M κ 0) - M * gc2 b κ * v ^ 2) =O[𝓝 0] (fun v => v ^ 4) := by
  have hb1 : 0 < 1 + b := by linarith
  have hG : (fun t : ℝ => (gn2 b κ * t ^ 2 + gn4 b κ * t ^ 4 + t ^ 6 * gnr b κ t)
        / ((1 + b) ^ 3 + (1 + b) ^ 3 * fa b κ * t ^ 2 + t ^ 4 * ((1 + b) ^ 3 * (fb b κ + t ^ 2 * fr b κ t)))
        - gc2 b κ * t ^ 2 - gc4 b κ * t ^ 4) =O[𝓝 0] (fun t => t ^ 6) :=
    rat_jet _ _ _ _ (pow_ne_zero 3 hb1.ne') (by unfold gnr; fun_prop) (by unfold fr; fun_prop)
  have h4 : (fun t : ℝ => t ^ 4 * gc4 b κ) =O[𝓝 0] (fun t => t ^ 4) := mul_cont continuousAt_const
  have hJ := ((Series.bigO_weaken (by norm_num : 4 ≤ 6) hG).add h4).const_mul_left (M : ℝ)
  have ev := fun (f : ℝ → ℝ) (hf : ContinuousAt f 0) (h0 : 0 < f 0) =>
    (continuousAt_const.eventually_lt hf h0 : ∀ᶠ v in 𝓝 (0 : ℝ), 0 < f v)
  have e3 := ev (fun v => 1 + b * (1 + κ * v ^ 2 + v) ^ 2) (by fun_prop) (by simpa using hb1)
  have e4 := ev (fun v => 1 + b * (1 + κ * v ^ 2 - v) ^ 2) (by fun_prop) (by simpa using hb1)
  refine hJ.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [e3, e4] with v h3 h4
  unfold fam
  rw [J3_stag, J3_stag]
  simp only [mul_zero, zero_pow two_ne_zero, add_zero, sub_zero, one_pow]
  have := gsum_fam b κ v hb1.ne' h3.ne' h4.ne'
  rw [show (M : ℝ) * (gfun b ((1 + κ * v ^ 2 + v) ^ 2) + gfun b ((1 + κ * v ^ 2 - v) ^ 2))
      - M * (gfun b 1 + gfun b 1)
      = M * (gfun b ((1 + κ * v ^ 2 + v) ^ 2) + gfun b ((1 + κ * v ^ 2 - v) ^ 2) - 2 * gfun b 1) by ring,
    this]
  ring

/-- `g₂(κ) = 0 ⇔ κ = u₂ = (3b−1)/(2(1+b))`: the level set is `u = u₂ v² + O(v⁴)`. -/
theorem gc2_eq_zero_iff (b κ : ℝ) (hb : 1 + b ≠ 0) : gc2 b κ = 0 ↔ κ = u2 b := by
  unfold gc2 gn2 u2
  rw [div_eq_zero_iff, or_iff_left (pow_ne_zero 3 hb)]
  constructor
  · intro h; field_simp; linarith
  · intro h; rw [h]; field_simp; ring

/-- **At the threshold**, the quartic of `F` along `u = u₂v²` is `n² c₄` (every even `n = 2M ≥ 4`). -/
theorem level_quartic_at_bn (M : ℕ) (hM : 2 ≤ M) :
    Aline M (bn (2 * M)) * u2 (bn (2 * M)) ^ 2 + Bline M (bn (2 * M)) * u2 (bn (2 * M)) + Dline M (bn (2 * M))
      = (2 * M) ^ 2 * c4even (2 * (M : ℝ)) := by
  rw [← bending_at_bn M hM]; ring

end Conj13.MTFamily
