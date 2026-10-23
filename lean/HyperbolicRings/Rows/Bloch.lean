/-
New in this paper (vortex-stability-papers, paper 3). Not copied from the source repositories.

The Bloch symbol of a hypercycle row, assembled from the per-pair second derivatives of `Rows.PairTerm`
(paper, Proposition "Bloch symbol"), and the spectral criterion.

The row is `u_k = k ℓ`, `φ_k = α` (`ℓ > 0` the strip spacing, `0 < α < π`, `κ = cos α`). On the Bloch wave
`(δu_k, δφ_k) = e^{iqk}(δu, δφ)` the linearised velocity of vortex `0` is `∑_{k ≠ 0}` of
(on-site coefficient) `+ e^{iqk}` (coupling coefficient) of the pair `(0,k)`, exactly as for the horocycle row
(`row_bloch_from_hessian`). We prove that these lattice sums converge and equal

  `δφ` in `u̇`: `B(q) = 2 F(q)`,   `δu` in `φ̇`: `C(q) = 2 ∑_{j≥1} C⁽¹⁾(c_j)(1 - cos qj)`,
  `δu` in `u̇` and `δφ` in `φ̇`: the same value `i ϖ(q)`, `ϖ` real.

`rowFlow ϖ B C = [[iϖ, B], [C, iϖ]]`; `rowFlow_re_iff`: if `C < 0`, all its eigenvalues are imaginary iff
`B ≥ 0`. `bloch_stable_iff`: for `cos q ≠ 1`, the Bloch mode `q` of the row is spectrally stable iff `F(q) ≥ 0`.
-/
import HyperbolicRings.Rows.PairTerm
import HyperbolicRings.Rows.Criterion

noncomputable section

namespace HyperbolicRings.Rows

open Real Filter Topology
open Complex (I)

/-- The Bloch phase `e^{iqk}`. -/
def phase (q : ℝ) (k : ℤ) : ℂ := Complex.exp (((q * (k : ℝ) : ℝ) : ℂ) * I)

theorem phase_eq (q : ℝ) (k : ℤ) :
    phase q k = (Real.cos (q * k) : ℂ) + (Real.sin (q * k) : ℂ) * I := by
  unfold phase; rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem phase_pos (q : ℝ) (n : ℕ) :
    phase q ((n : ℤ) + 1) = (Real.cos (q * ((n : ℝ) + 1)) : ℂ) + (Real.sin (q * ((n : ℝ) + 1)) : ℂ) * I := by
  rw [phase_eq]; push_cast; rfl

theorem phase_neg (q : ℝ) (n : ℕ) :
    phase q (-((n : ℤ) + 1)) =
      (Real.cos (q * ((n : ℝ) + 1)) : ℂ) - (Real.sin (q * ((n : ℝ) + 1)) : ℂ) * I := by
  rw [phase_eq]
  have : q * (((-((n : ℤ) + 1) : ℤ)) : ℝ) = -(q * ((n : ℝ) + 1)) := by push_cast; ring
  rw [this, Real.cos_neg, Real.sin_neg]; push_cast; ring

theorem cast_pos_mul (ℓ : ℝ) (n : ℕ) : (((((n : ℤ) + 1 : ℤ)) : ℝ) * ℓ) = ((n : ℝ) + 1) * ℓ := by
  push_cast; ring
theorem cast_neg_mul (ℓ : ℝ) (n : ℕ) : (((-((n : ℤ) + 1) : ℤ)) : ℝ) * ℓ = -(((n : ℝ) + 1) * ℓ) := by
  push_cast; ring

/-- A `ℤ`-indexed sum with zero `0`-th term, from the sums over positive and negative indices. -/
theorem hasSum_int_of_pairs {g : ℤ → ℂ} (h0 : g 0 = 0)
    (hA : Summable (fun n : ℕ => g ((n : ℤ) + 1))) (hB : Summable (fun n : ℕ => g (-((n : ℤ) + 1))))
    {S : ℂ} (hS : HasSum (fun n : ℕ => g ((n : ℤ) + 1) + g (-((n : ℤ) + 1))) S) : HasSum g S := by
  have hA' : HasSum (fun n : ℕ => g n) (∑' n : ℕ, g ((n : ℤ) + 1)) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [h0] using hA.hasSum
  have h := HasSum.of_nat_of_neg_add_one hA' hB.hasSum
  have : (∑' n : ℕ, g ((n : ℤ) + 1)) + (∑' n : ℕ, g (-((n : ℤ) + 1))) = S :=
    (hA.hasSum.add hB.hasSum).unique hS
  rwa [this] at h

section sums
variable {α ℓ : ℝ} (hα0 : 0 < α) (hαπ : α < π) (hℓ : 0 < ℓ)
include hα0 hαπ hℓ

theorem K_lt_one : cos α ^ 2 < 1 := by
  have hs : 0 < sin α := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ
  nlinarith [sin_sq_add_cos_sq α]

theorem kl_ne (n : ℕ) : ((n : ℝ) + 1) * ℓ ≠ 0 := by positivity
theorem kl_ne' (n : ℕ) : -(((n : ℝ) + 1) * ℓ) ≠ 0 := neg_ne_zero.mpr (by positivity)


theorem summable_B0 : Summable (fun n => B0 (cos α ^ 2) (cj ℓ n)) := by
  have hK := K_lt_one hα0 hαπ hℓ
  have h0 : 0 ≤ cos α ^ 2 := sq_nonneg _
  have := ((summable_go h0 hK hℓ).add (summable_ge h0 hK hℓ)).mul_left ((1 - cos α ^ 2) / 2)
  convert this using 1
  funext n
  have h1 := B0_sub_B1 hK (one_lt_cj hℓ n)
  have h2 := B0_add_B1 hK (one_lt_cj hℓ n)
  linarith

theorem summable_B1 : Summable (fun n => B1 (cos α ^ 2) (cj ℓ n)) := by
  have hK := K_lt_one hα0 hαπ hℓ
  have h0 : 0 ≤ cos α ^ 2 := sq_nonneg _
  have := ((summable_ge h0 hK hℓ).sub (summable_go h0 hK hℓ)).mul_left ((1 - cos α ^ 2) / 2)
  convert this using 1
  funext n
  have h1 := B0_sub_B1 hK (one_lt_cj hℓ n)
  have h2 := B0_add_B1 hK (one_lt_cj hℓ n)
  linarith

theorem summable_C1 : Summable (fun n => C1 (cos α ^ 2) (cj ℓ n)) := by
  have hK := K_lt_one hα0 hαπ hℓ
  have h0 : 0 ≤ cos α ^ 2 := sq_nonneg _
  have hc1 := one_lt_cosh_of_pos hℓ
  apply summable_bound hℓ (2 * ((cosh ℓ + 1) / (cosh ℓ - 1)) ^ 2)
    (by have : 0 < (cosh ℓ + 1) / (cosh ℓ - 1) := div_pos (by linarith) (by linarith); positivity)
  intro n
  have hc := one_lt_cj hℓ n
  have hge := cj_ge hℓ n
  set c := cj ℓ n
  have hD := Dd_pos hK hc
  have hDge : c - 1 ≤ Dd (cos α ^ 2) c := Dd_ge hK.le
  have hc1' : 0 < c - 1 := by linarith
  unfold C1
  have hs0 : 0 ≤ (1 - cos α ^ 2) ^ 2 := sq_nonneg _
  have hs1 : (1 - cos α ^ 2) ^ 2 ≤ 1 := by nlinarith
  have hnum : 0 ≤ c ^ 2 + c - 2 * cos α ^ 2 := by nlinarith
  rw [abs_div, abs_of_pos (by positivity : 0 < (c - 1) * Dd (cos α ^ 2) c ^ 2), abs_mul, abs_neg,
    abs_of_nonneg hs0, abs_of_nonneg hnum]
  have hM : (c + 1) / (c - 1) ≤ (cosh ℓ + 1) / (cosh ℓ - 1) := by
    rw [div_le_div_iff₀ hc1' (by linarith)]; nlinarith
  have hMn : 0 ≤ (c + 1) / (c - 1) := div_nonneg (by linarith) hc1'.le
  calc (1 - cos α ^ 2) ^ 2 * (c ^ 2 + c - 2 * cos α ^ 2) / ((c - 1) * Dd (cos α ^ 2) c ^ 2)
      ≤ 1 * (2 * (c + 1) ^ 2) / ((c - 1) * (c - 1) ^ 2) := by
        apply div_le_div₀ (by positivity) (mul_le_mul hs1 (by nlinarith) hnum (by norm_num))
          (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc1'.le hDge 2) hc1'.le
    _ = 2 * ((c + 1) / (c - 1)) ^ 2 * (1 / (c - 1)) := by field_simp
    _ ≤ 2 * ((cosh ℓ + 1) / (cosh ℓ - 1)) ^ 2 * (1 / (c - 1)) := by
        apply mul_le_mul_of_nonneg_right _ (one_div_nonneg.mpr hc1'.le)
        have := pow_le_pow_left₀ hMn hM 2
        linarith

theorem summable_oddW : Summable (fun n : ℕ => oddW α (((n : ℝ) + 1) * ℓ)) := by
  have hc1 := one_lt_cosh_of_pos hℓ
  apply summable_bound hℓ (1 + 1 / (cosh ℓ - 1)) (by have h : 0 < cosh ℓ - 1 := (by linarith); positivity)
  intro n
  have hc := one_lt_cj hℓ n
  have hge := cj_ge hℓ n
  have hb : 0 < ((n : ℝ) + 1) * ℓ := by positivity
  have hsh : 0 < sinh (((n : ℝ) + 1) * ℓ) := Real.sinh_pos_iff.mpr hb
  have hshc : sinh (((n : ℝ) + 1) * ℓ) ≤ cj ℓ n := by
    unfold cj; have := Real.sinh_lt_cosh (((n : ℝ) + 1) * ℓ); linarith
  set c := cj ℓ n
  have hc1' : 0 < c - 1 := by linarith
  have hDp : c - 1 ≤ c - cos (2 * α) := by have := cos_le_one (2 * α); linarith
  unfold oddW
  have hcd : cosh (((n : ℝ) + 1) * ℓ) = c := rfl
  rw [hcd, abs_div, abs_mul, abs_mul, abs_of_pos hsh, abs_of_pos (mul_pos two_pos (pow_pos (by linarith) 2) : 0 < 2 * (c - cos (2 * α)) ^ 2)]
  have hs2 : |sin α ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [sin_sq_add_cos_sq α]
  have hsin : |sin (2 * α)| ≤ 1 := abs_sin_le_one _
  calc |sin α ^ 2| * |sin (2 * α)| * sinh (((n : ℝ) + 1) * ℓ) / (2 * (c - cos (2 * α)) ^ 2)
      ≤ 1 * 1 * c / (1 * (c - 1) ^ 2) := by
        apply div_le_div₀ (by positivity)
          (mul_le_mul (mul_le_mul hs2 hsin (abs_nonneg _) (by norm_num)) hshc hsh.le (by norm_num))
          (by positivity)
        have := pow_le_pow_left₀ hc1'.le hDp 2
        nlinarith
    _ = (1 + 1 / (c - 1)) * (1 / (c - 1)) := by field_simp; ring
    _ ≤ (1 + 1 / (cosh ℓ - 1)) * (1 / (c - 1)) := by
        apply mul_le_mul_of_nonneg_right _ (one_div_nonneg.mpr hc1'.le)
        have : 1 / (c - 1) ≤ 1 / (cosh ℓ - 1) := one_div_le_one_div_of_le (by linarith) (by linarith)
        linarith

/-- `δφ` in `u̇`: `∑_{k≠0} [onB(kℓ) + e^{iqk} cpB(kℓ)] = 2 F(q)`. -/
theorem hasSum_symB (q : ℝ) :
    HasSum (fun k : ℤ => if k = 0 then 0 else (onB α (k * ℓ) : ℂ) + phase q k * cpB α (k * ℓ))
      ((2 * F (cos α ^ 2) ℓ q : ℝ) : ℂ) := by
  have hK := K_lt_one hα0 hαπ hℓ
  have hp : ∀ n : ℕ, onB α (((n : ℝ) + 1) * ℓ) = B0 (cos α ^ 2) (cj ℓ n) ∧
      cpB α (((n : ℝ) + 1) * ℓ) = B1 (cos α ^ 2) (cj ℓ n) := fun n =>
    ⟨by rw [onB_eq_B0 (kl_ne hα0 hαπ hℓ n)]; rfl, by rw [cpB_eq_B1 (kl_ne hα0 hαπ hℓ n)]; rfl⟩
  have hm : ∀ n : ℕ, onB α (-(((n : ℝ) + 1) * ℓ)) = B0 (cos α ^ 2) (cj ℓ n) ∧
      cpB α (-(((n : ℝ) + 1) * ℓ)) = B1 (cos α ^ 2) (cj ℓ n) := fun n =>
    ⟨by rw [onB_eq_B0 (kl_ne' hα0 hαπ hℓ n), Real.cosh_neg]; rfl,
     by rw [cpB_eq_B1 (kl_ne' hα0 hαπ hℓ n), Real.cosh_neg]; rfl⟩
  have sB0 := Complex.summable_ofReal.mpr (summable_B0 hα0 hαπ hℓ)
  have sB1 := summable_B1 hα0 hαπ hℓ
  have hsum1 : ∀ s : ℝ, Summable (fun n : ℕ => (B1 (cos α ^ 2) (cj ℓ n) : ℂ) *
      ((Real.cos (q * ((n : ℝ) + 1)) : ℂ) + s * (Real.sin (q * ((n : ℝ) + 1)) : ℂ) * I)) := by
    intro s
    apply Summable.of_norm_bounded (sB1.abs.mul_left (1 + |s|))
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : ‖(Real.cos (q * ((n : ℝ) + 1)) : ℂ) + s * (Real.sin (q * ((n : ℝ) + 1)) : ℂ) * I‖ ≤ 1 + |s| := by
      calc _ ≤ ‖(Real.cos (q * ((n : ℝ) + 1)) : ℂ)‖ + ‖(s : ℂ) * (Real.sin (q * ((n : ℝ) + 1)) : ℂ) * I‖ :=
            norm_add_le _ _
        _ ≤ 1 + |s| := by
          rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
          have := abs_cos_le_one (q * ((n : ℝ) + 1)); have := abs_sin_le_one (q * ((n : ℝ) + 1))
          nlinarith [abs_nonneg s]
    calc |B1 (cos α ^ 2) (cj ℓ n)| * ‖_‖ ≤ |B1 (cos α ^ 2) (cj ℓ n)| * (1 + |s|) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = (1 + |s|) * |B1 (cos α ^ 2) (cj ℓ n)| := by ring
  apply hasSum_int_of_pairs (by simp)
  · have := sB0.add (hsum1 1)
    convert this using 1; funext n
    rw [if_neg (by omega : ¬ _), cast_pos_mul ℓ, (hp n).1, (hp n).2, phase_pos]; push_cast; ring
  · have := sB0.add (hsum1 (-1))
    convert this using 1; funext n
    rw [if_neg (by omega : ¬ _), cast_neg_mul ℓ, (hm n).1, (hm n).2, phase_neg]; push_cast; ring
  · have hF := (F_summable (sq_nonneg _) hK hℓ q).hasSum
    have := (Complex.hasSum_ofReal.mpr hF).mul_left 2
    convert this using 1
    · funext n
      rw [if_neg (by omega : ¬ _), if_neg (by omega : ¬ _), cast_pos_mul ℓ, cast_neg_mul ℓ, (hp n).1, (hp n).2, (hm n).1,
        (hm n).2, phase_pos, phase_neg, term]
      push_cast; ring
    · unfold F; push_cast; ring

/-- `δu` in `φ̇`: `∑_{k≠0} [onC(kℓ) + e^{iqk} cpC(kℓ)] = 2 ∑_{j≥1} C⁽¹⁾(c_j)(1 - cos qj)`. -/
def Cser (K ℓ q : ℝ) : ℝ := 2 * ∑' n : ℕ, C1 K (cj ℓ n) * (1 - Real.cos (q * ((n : ℝ) + 1)))

theorem summable_Cterm (q : ℝ) :
    Summable (fun n : ℕ => C1 (cos α ^ 2) (cj ℓ n) * (1 - Real.cos (q * ((n : ℝ) + 1)))) := by
  apply Summable.of_norm_bounded ((summable_C1 hα0 hαπ hℓ).abs.mul_left 2)
  intro n
  rw [Real.norm_eq_abs, abs_mul]
  have := abs_le.mp (abs_cos_le_one (q * ((n : ℝ) + 1)))
  have : |1 - Real.cos (q * ((n : ℝ) + 1))| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  nlinarith [abs_nonneg (C1 (cos α ^ 2) (cj ℓ n))]

theorem hasSum_symC (q : ℝ) :
    HasSum (fun k : ℤ => if k = 0 then 0 else (onC α (k * ℓ) : ℂ) + phase q k * cpC α (k * ℓ))
      ((Cser (cos α ^ 2) ℓ q : ℝ) : ℂ) := by
  have hp : ∀ n : ℕ, onC α (((n : ℝ) + 1) * ℓ) = C1 (cos α ^ 2) (cj ℓ n) ∧
      cpC α (((n : ℝ) + 1) * ℓ) = -C1 (cos α ^ 2) (cj ℓ n) := fun n =>
    ⟨by rw [onC_eq_C1 (kl_ne hα0 hαπ hℓ n)]; rfl, by rw [cpC_eq_C1 (kl_ne hα0 hαπ hℓ n)]; rfl⟩
  have hm : ∀ n : ℕ, onC α (-(((n : ℝ) + 1) * ℓ)) = C1 (cos α ^ 2) (cj ℓ n) ∧
      cpC α (-(((n : ℝ) + 1) * ℓ)) = -C1 (cos α ^ 2) (cj ℓ n) := fun n =>
    ⟨by rw [onC_eq_C1 (kl_ne' hα0 hαπ hℓ n), Real.cosh_neg]; rfl,
     by rw [cpC_eq_C1 (kl_ne' hα0 hαπ hℓ n), Real.cosh_neg]; rfl⟩
  have sC := summable_C1 hα0 hαπ hℓ
  have hsum : ∀ s : ℝ, Summable (fun n : ℕ => (C1 (cos α ^ 2) (cj ℓ n) : ℂ) *
      (1 - ((Real.cos (q * ((n : ℝ) + 1)) : ℂ) + s * (Real.sin (q * ((n : ℝ) + 1)) : ℂ) * I))) := by
    intro s
    apply Summable.of_norm_bounded (sC.abs.mul_left (2 + |s|))
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : ‖(1 : ℂ) - ((Real.cos (q * ((n : ℝ) + 1)) : ℂ) + s * (Real.sin (q * ((n : ℝ) + 1)) : ℂ) * I)‖
        ≤ 2 + |s| := by
      calc _ ≤ ‖(1 : ℂ)‖ + (‖(Real.cos (q * ((n : ℝ) + 1)) : ℂ)‖
              + ‖(s : ℂ) * (Real.sin (q * ((n : ℝ) + 1)) : ℂ) * I‖) :=
            (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        _ ≤ 2 + |s| := by
          rw [norm_one, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
          have := abs_cos_le_one (q * ((n : ℝ) + 1)); have := abs_sin_le_one (q * ((n : ℝ) + 1))
          nlinarith [abs_nonneg s]
    calc |C1 (cos α ^ 2) (cj ℓ n)| * ‖_‖ ≤ |C1 (cos α ^ 2) (cj ℓ n)| * (2 + |s|) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = (2 + |s|) * |C1 (cos α ^ 2) (cj ℓ n)| := by ring
  apply hasSum_int_of_pairs (by simp)
  · convert hsum 1 using 1; funext n
    rw [if_neg (by omega : ¬ _), cast_pos_mul ℓ, (hp n).1, (hp n).2, phase_pos]; push_cast; ring
  · convert hsum (-1) using 1; funext n
    rw [if_neg (by omega : ¬ _), cast_neg_mul ℓ, (hm n).1, (hm n).2, phase_neg]; push_cast; ring
  · have := (Complex.hasSum_ofReal.mpr (summable_Cterm hα0 hαπ hℓ q).hasSum).mul_left 2
    convert this using 1
    · funext n
      rw [if_neg (by omega : ¬ _), if_neg (by omega : ¬ _), cast_pos_mul ℓ, cast_neg_mul ℓ, (hp n).1, (hp n).2, (hm n).1,
        (hm n).2, phase_pos, phase_neg]
      push_cast; ring
    · unfold Cser; push_cast; ring

/-- The real frequency shift `ϖ(q) = -2 ∑_{j≥1} oddW(jℓ) sin qj`. -/
def varpi (α ℓ q : ℝ) : ℝ := -2 * ∑' n : ℕ, oddW α (((n : ℝ) + 1) * ℓ) * Real.sin (q * ((n : ℝ) + 1))

theorem oddW_neg (b : ℝ) : oddW α (-b) = -oddW α b := by
  unfold oddW; rw [Real.sinh_neg, Real.cosh_neg]; ring

theorem summable_oddW_sin (q : ℝ) :
    Summable (fun n : ℕ => oddW α (((n : ℝ) + 1) * ℓ) * Real.sin (q * ((n : ℝ) + 1))) := by
  apply Summable.of_norm_bounded (summable_oddW hα0 hαπ hℓ).abs
  intro n
  rw [Real.norm_eq_abs, abs_mul]
  have := abs_sin_le_one (q * ((n : ℝ) + 1))
  nlinarith [abs_nonneg (oddW α (((n : ℝ) + 1) * ℓ))]

/-- `δu` in `u̇`: `∑_{k≠0} [onU(kℓ) + e^{iqk} cpU(kℓ)] = i ϖ(q)`. -/
theorem hasSum_symU (q : ℝ) :
    HasSum (fun k : ℤ => if k = 0 then 0 else (onU α (k * ℓ) : ℂ) + phase q k * cpU α (k * ℓ))
      (I * (varpi α ℓ q : ℂ)) := by
  have hp : ∀ n : ℕ, onU α (((n : ℝ) + 1) * ℓ) = oddW α (((n : ℝ) + 1) * ℓ) ∧
      cpU α (((n : ℝ) + 1) * ℓ) = -oddW α (((n : ℝ) + 1) * ℓ) := fun n =>
    ⟨onU_val (kl_ne hα0 hαπ hℓ n), cpU_val (kl_ne hα0 hαπ hℓ n)⟩
  have hm : ∀ n : ℕ, onU α (-(((n : ℝ) + 1) * ℓ)) = -oddW α (((n : ℝ) + 1) * ℓ) ∧
      cpU α (-(((n : ℝ) + 1) * ℓ)) = oddW α (((n : ℝ) + 1) * ℓ) := fun n =>
    ⟨by rw [onU_val (kl_ne' hα0 hαπ hℓ n), oddW_neg hα0 hαπ hℓ],
     by rw [cpU_val (kl_ne' hα0 hαπ hℓ n), oddW_neg hα0 hαπ hℓ, neg_neg]⟩
  have sO := summable_oddW hα0 hαπ hℓ
  have hsum : ∀ s : ℝ, Summable (fun n : ℕ => (oddW α (((n : ℝ) + 1) * ℓ) : ℂ) *
      (1 - ((Real.cos (q * ((n : ℝ) + 1)) : ℂ) + s * (Real.sin (q * ((n : ℝ) + 1)) : ℂ) * I))) := by
    intro s
    apply Summable.of_norm_bounded (sO.abs.mul_left (2 + |s|))
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : ‖(1 : ℂ) - ((Real.cos (q * ((n : ℝ) + 1)) : ℂ) + s * (Real.sin (q * ((n : ℝ) + 1)) : ℂ) * I)‖
        ≤ 2 + |s| := by
      calc _ ≤ ‖(1 : ℂ)‖ + (‖(Real.cos (q * ((n : ℝ) + 1)) : ℂ)‖
              + ‖(s : ℂ) * (Real.sin (q * ((n : ℝ) + 1)) : ℂ) * I‖) :=
            (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        _ ≤ 2 + |s| := by
          rw [norm_one, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
          have := abs_cos_le_one (q * ((n : ℝ) + 1)); have := abs_sin_le_one (q * ((n : ℝ) + 1))
          nlinarith [abs_nonneg s]
    calc |oddW α (((n : ℝ) + 1) * ℓ)| * ‖_‖ ≤ |oddW α (((n : ℝ) + 1) * ℓ)| * (2 + |s|) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = (2 + |s|) * |oddW α (((n : ℝ) + 1) * ℓ)| := by ring
  apply hasSum_int_of_pairs (by simp)
  · convert hsum 1 using 1; funext n
    rw [if_neg (by omega : ¬ _), cast_pos_mul ℓ, (hp n).1, (hp n).2, phase_pos]; push_cast; ring
  · have := (hsum (-1)).neg
    convert this using 1; funext n
    rw [if_neg (by omega : ¬ _), cast_neg_mul ℓ, (hm n).1, (hm n).2, phase_neg]; push_cast; ring
  · have := (Complex.hasSum_ofReal.mpr (summable_oddW_sin hα0 hαπ hℓ q).hasSum).mul_left (-2 * I)
    convert this using 1
    · funext n
      rw [if_neg (by omega : ¬ _), if_neg (by omega : ¬ _), cast_pos_mul ℓ, cast_neg_mul ℓ, (hp n).1, (hp n).2, (hm n).1,
        (hm n).2, phase_pos, phase_neg]
      push_cast; ring
    · unfold varpi; push_cast; ring

/-- `E(b) = sin α cos α sinh b (1/(cosh b - cos 2α) - 1/(cosh b - 1))`, the drift part of `onP`. -/
def driftE (α b : ℝ) : ℝ := sin α * cos α * sinh b * (1 / (cosh b - cos (2 * α)) - 1 / (cosh b - 1))

theorem driftE_neg (b : ℝ) : driftE α (-b) = -driftE α b := by
  unfold driftE; rw [Real.sinh_neg, Real.cosh_neg]; ring

theorem summable_driftE : Summable (fun n : ℕ => driftE α (((n : ℝ) + 1) * ℓ)) := by
  have hc1 := one_lt_cosh_of_pos hℓ
  apply summable_bound hℓ (2 * (1 + 1 / (cosh ℓ - 1))) (by have h : 0 < cosh ℓ - 1 := (by linarith); positivity)
  intro n
  have hc := one_lt_cj hℓ n
  have hge := cj_ge hℓ n
  have hb : 0 < ((n : ℝ) + 1) * ℓ := by positivity
  have hsh : 0 < sinh (((n : ℝ) + 1) * ℓ) := Real.sinh_pos_iff.mpr hb
  have hshc : sinh (((n : ℝ) + 1) * ℓ) ≤ cj ℓ n := by
    unfold cj; have := Real.sinh_lt_cosh (((n : ℝ) + 1) * ℓ); linarith
  set c := cj ℓ n
  have hc1' : 0 < c - 1 := by linarith
  have hDp : c - 1 ≤ c - cos (2 * α) := by have := cos_le_one (2 * α); linarith
  have hDp' : c - cos (2 * α) ≤ c + 1 := by have := neg_one_le_cos (2 * α); linarith
  have hcd : cosh (((n : ℝ) + 1) * ℓ) = c := rfl
  unfold driftE
  rw [hcd]
  have hDpos : 0 < c - cos (2 * α) := by linarith
  have hdiff : 1 / (c - cos (2 * α)) - 1 / (c - 1) = (cos (2 * α) - 1) / ((c - cos (2 * α)) * (c - 1)) := by
    field_simp; ring
  rw [hdiff, abs_mul, abs_mul, abs_mul, abs_of_pos hsh, abs_div, abs_of_pos (by positivity :
    0 < (c - cos (2 * α)) * (c - 1))]
  have hsc : |sin α| * |cos α| ≤ 1 := by
    have := abs_sin_le_one α; have := abs_cos_le_one α; nlinarith [abs_nonneg (sin α), abs_nonneg (cos α)]
  have hcn : |cos (2 * α) - 1| ≤ 2 := by
    rw [abs_le]; have := neg_one_le_cos (2 * α); have := cos_le_one (2 * α); constructor <;> linarith
  calc |sin α| * |cos α| * sinh (((n : ℝ) + 1) * ℓ) * (|cos (2 * α) - 1| / ((c - cos (2 * α)) * (c - 1)))
      ≤ 1 * c * (2 / ((c - 1) * (c - 1))) := by
        apply mul_le_mul (mul_le_mul hsc hshc hsh.le (by norm_num)) _ (by positivity) (by positivity)
        apply div_le_div₀ (by norm_num) hcn (by positivity)
        exact mul_le_mul_of_nonneg_right hDp hc1'.le
    _ = 2 * (1 + 1 / (c - 1)) * (1 / (c - 1)) := by field_simp; ring
    _ ≤ 2 * (1 + 1 / (cosh ℓ - 1)) * (1 / (c - 1)) := by
        apply mul_le_mul_of_nonneg_right _ (one_div_nonneg.mpr hc1'.le)
        have : 1 / (c - 1) ≤ 1 / (cosh ℓ - 1) := one_div_le_one_div_of_le (by linarith) (by linarith)
        linarith

/-- `δφ` in `φ̇`: `∑_{k≠0} [onP(kℓ) + e^{iqk} cpP(kℓ)] = i ϖ(q)`, the same value as `hasSum_symU`. -/
theorem hasSum_symP (q : ℝ) :
    HasSum (fun k : ℤ => if k = 0 then 0 else (onP α (k * ℓ) : ℂ) + phase q k * cpP α (k * ℓ))
      (I * (varpi α ℓ q : ℂ)) := by
  have hp : ∀ n : ℕ, onP α (((n : ℝ) + 1) * ℓ) = driftE α (((n : ℝ) + 1) * ℓ) - oddW α (((n : ℝ) + 1) * ℓ) ∧
      cpP α (((n : ℝ) + 1) * ℓ) = -oddW α (((n : ℝ) + 1) * ℓ) := fun n =>
    ⟨onP_val (kl_ne hα0 hαπ hℓ n), cpP_val (kl_ne hα0 hαπ hℓ n)⟩
  have hm : ∀ n : ℕ, onP α (-(((n : ℝ) + 1) * ℓ)) =
      -driftE α (((n : ℝ) + 1) * ℓ) + oddW α (((n : ℝ) + 1) * ℓ) ∧
      cpP α (-(((n : ℝ) + 1) * ℓ)) = oddW α (((n : ℝ) + 1) * ℓ) := fun n => by
    refine ⟨?_, ?_⟩
    · have := onP_val (α := α) (kl_ne' hα0 hαπ hℓ n)
      rw [oddW_neg hα0 hαπ hℓ] at this
      rw [this, ← driftE, driftE_neg hα0 hαπ hℓ]; ring
    · rw [cpP_val (kl_ne' hα0 hαπ hℓ n), oddW_neg hα0 hαπ hℓ, neg_neg]
  have sO := summable_oddW hα0 hαπ hℓ
  have sE := Complex.summable_ofReal.mpr (summable_driftE hα0 hαπ hℓ)
  have hsum : ∀ s : ℝ, Summable (fun n : ℕ => (oddW α (((n : ℝ) + 1) * ℓ) : ℂ) *
      (1 + ((Real.cos (q * ((n : ℝ) + 1)) : ℂ) + s * (Real.sin (q * ((n : ℝ) + 1)) : ℂ) * I))) := by
    intro s
    apply Summable.of_norm_bounded (sO.abs.mul_left (2 + |s|))
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : ‖(1 : ℂ) + ((Real.cos (q * ((n : ℝ) + 1)) : ℂ) + s * (Real.sin (q * ((n : ℝ) + 1)) : ℂ) * I)‖
        ≤ 2 + |s| := by
      calc _ ≤ ‖(1 : ℂ)‖ + (‖(Real.cos (q * ((n : ℝ) + 1)) : ℂ)‖
              + ‖(s : ℂ) * (Real.sin (q * ((n : ℝ) + 1)) : ℂ) * I‖) :=
            (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        _ ≤ 2 + |s| := by
          rw [norm_one, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
          have := abs_cos_le_one (q * ((n : ℝ) + 1)); have := abs_sin_le_one (q * ((n : ℝ) + 1))
          nlinarith [abs_nonneg s]
    calc |oddW α (((n : ℝ) + 1) * ℓ)| * ‖_‖ ≤ |oddW α (((n : ℝ) + 1) * ℓ)| * (2 + |s|) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = (2 + |s|) * |oddW α (((n : ℝ) + 1) * ℓ)| := by ring
  apply hasSum_int_of_pairs (by simp)
  · have := sE.sub (hsum 1)
    convert this using 1; funext n
    rw [if_neg (by omega : ¬ _), cast_pos_mul ℓ, (hp n).1, (hp n).2, phase_pos]; push_cast; ring
  · have := sE.neg.add (hsum (-1))
    convert this using 1; funext n
    rw [if_neg (by omega : ¬ _), cast_neg_mul ℓ, (hm n).1, (hm n).2, phase_neg]; push_cast; ring
  · have := (Complex.hasSum_ofReal.mpr (summable_oddW_sin hα0 hαπ hℓ q).hasSum).mul_left (-2 * I)
    convert this using 1
    · funext n
      rw [if_neg (by omega : ¬ _), if_neg (by omega : ¬ _), cast_pos_mul ℓ, cast_neg_mul ℓ, (hp n).1, (hp n).2, (hm n).1,
        (hm n).2, phase_pos, phase_neg]
      push_cast; ring
    · unfold varpi; push_cast; ring

/-- `C(q) < 0` whenever `cos q ≠ 1`. -/
theorem Cser_neg {q : ℝ} (hq : Real.cos q ≠ 1) : Cser (cos α ^ 2) ℓ q < 0 := by
  have hK := K_lt_one hα0 hαπ hℓ
  have hnn : ∀ n, 0 ≤ -(C1 (cos α ^ 2) (cj ℓ n) * (1 - Real.cos (q * ((n : ℝ) + 1)))) := fun n => by
    have := C1_neg (sq_nonneg _) hK (one_lt_cj hℓ n)
    have := cos_le_one (q * ((n : ℝ) + 1))
    nlinarith
  have hp0 : 0 < -(C1 (cos α ^ 2) (cj ℓ 0) * (1 - Real.cos (q * (((0 : ℕ) : ℝ) + 1)))) := by
    have := C1_neg (sq_nonneg _) hK (one_lt_cj hℓ 0)
    have h1 : Real.cos (q * (((0 : ℕ) : ℝ) + 1)) < 1 := by
      simp only [Nat.cast_zero, zero_add, mul_one]; exact lt_of_le_of_ne (cos_le_one q) hq
    nlinarith
  have := (summable_Cterm hα0 hαπ hℓ q).neg.tsum_pos hnn 0 hp0
  unfold Cser; rw [tsum_neg] at this; linarith

end sums

/-! ## The spectral criterion for the Bloch matrix -/

/-- The linearised flow on a Bloch wave, in the order `(δu, δφ)`: `[[iϖ, B], [C, iϖ]]`. -/
def rowFlow (ϖ B C : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![I * ϖ, B; C, I * ϖ]

theorem rowFlow_hasEigenvalue_iff (ϖ B C : ℝ) (σ : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' (rowFlow ϖ B C)) σ ↔ (σ - I * ϖ) ^ 2 = B * C := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin',
    Polynomial.IsRoot.def, Matrix.eval_charpoly, Matrix.det_fin_two]
  simp [rowFlow, Matrix.scalar_apply]
  constructor <;> intro h <;> linear_combination h

/-- If `C < 0`, every eigenvalue of `[[iϖ, B], [C, iϖ]]` is purely imaginary iff `B ≥ 0`; if `B < 0`,
`iϖ + √(BC)` is an eigenvalue with positive real part. -/
theorem rowFlow_re_iff (ϖ B C : ℝ) (hC : C < 0) :
    (∀ σ, Module.End.HasEigenvalue (Matrix.toLin' (rowFlow ϖ B C)) σ → σ.re = 0) ↔ 0 ≤ B := by
  constructor
  · intro h
    by_contra hneg
    replace hneg := not_le.mp hneg
    have hBC : 0 < B * C := mul_pos_of_neg_of_neg hneg hC
    have hs : ((Real.sqrt (B * C) : ℝ) : ℂ) ^ 2 = (B : ℂ) * C := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hBC.le]; push_cast; ring
    have he := h (I * ϖ + Real.sqrt (B * C)) ((rowFlow_hasEigenvalue_iff ϖ B C _).2 (by
      rw [show I * (ϖ : ℂ) + (Real.sqrt (B * C) : ℂ) - I * ϖ = Real.sqrt (B * C) by ring, hs]))
    simp at he
    have : 0 < Real.sqrt (B * C) := Real.sqrt_pos.2 hBC
    linarith
  · intro hB σ hσ
    rw [rowFlow_hasEigenvalue_iff] at hσ
    have hre := congrArg Complex.re hσ
    have him := congrArg Complex.im hσ
    simp [sq] at hre him
    have h2 : σ.re * (σ.im - ϖ) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · have : σ.im = ϖ := by linarith
      rw [this] at hre
      nlinarith [sq_nonneg σ.re, mul_nonpos_of_nonneg_of_nonpos hB hC.le]

/-- **Spectral criterion for hypercycle rows.** For `0 < α < π`, `ℓ > 0` and `cos q ≠ 1`, the Bloch
matrix built from the lattice sums of the per-pair second derivatives is `[[iϖ, 2F(q)], [C(q), iϖ]]`
with `C(q) < 0`; hence the Bloch mode `q` is spectrally stable iff `F(q) ≥ 0`. -/
theorem bloch_stable_iff {α ℓ q : ℝ} (hα0 : 0 < α) (hαπ : α < π) (hℓ : 0 < ℓ) (hq : Real.cos q ≠ 1) :
    (∀ σ, Module.End.HasEigenvalue
        (Matrix.toLin' (rowFlow (varpi α ℓ q) (2 * F (cos α ^ 2) ℓ q) (Cser (cos α ^ 2) ℓ q))) σ →
        σ.re = 0) ↔ 0 ≤ F (cos α ^ 2) ℓ q := by
  rw [rowFlow_re_iff _ _ _ (Cser_neg hα0 hαπ hℓ hq)]
  constructor <;> intro h <;> linarith

end HyperbolicRings.Rows
