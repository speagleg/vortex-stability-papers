/-
New in this paper (vortex-stability-papers, paper 3). Not copied from the source repositories.

Hypercycle rows: generating function of `B⁽¹⁾` and the critical mode `q = π`
(paper, Proposition "critical mode").

* `hasSum_n_cos`: `∑_n n zⁿ cos nθ = z((1+z²)cos θ - 2z)/(1 - 2z cos θ + z²)²` for `0 ≤ z < 1`.
* `hasSum_cos_geom`: `∑_{j≥0} r^{j+1} cos((j+1)q) = (r cos q - r²)/(1 - 2r cos q + r²)` for `0 ≤ r < 1`.
* `B1_gen`: `B⁽¹⁾(cosh x) = 2 sin²α ∑_n n cos²(nα) e^{-nx}` (`x > 0`, `K = cos²α`).
* `F_strictAnti`: `F` is strictly decreasing on `[0, π]`.
* `F_ge_F_pi`, `row_stable_iff_F_pi`: hence `F(q) ≥ F(π)` for every `q`, and every Bloch mode with `cos q ≠ 1` is
  spectrally stable iff `F(π) ≥ 0`.
-/
import HyperbolicRings.Rows.Bloch

noncomputable section

namespace HyperbolicRings.Rows

open Real Filter Topology
open Complex (I)

/-! ## Two generating functions -/

theorem den_pos {z t : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) (ht : t ≤ 1) : 0 < 1 - 2 * z * t + z ^ 2 := by
  nlinarith [mul_nonneg hz0 (sub_nonneg.mpr ht)]

/-- `∑_n n zⁿ cos nθ`. -/
theorem hasSum_n_cos (θ : ℝ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (fun n : ℕ => (n : ℝ) * z ^ n * Real.cos (n * θ))
      (z * ((1 + z ^ 2) * Real.cos θ - 2 * z) / (1 - 2 * z * Real.cos θ + z ^ 2) ^ 2) := by
  set e : ℂ := Complex.exp ((θ : ℂ) * I)
  have he : ‖e‖ = 1 := by simpa [e] using Complex.norm_exp_ofReal_mul_I θ
  have he0 : e ≠ 0 := Complex.exp_ne_zero _
  have hw1 : ‖(z : ℂ) * e‖ < 1 := by rw [norm_mul, he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz0]; simpa
  have hw2 : ‖(z : ℂ) * e⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv, he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz0]; simpa
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hw1
  have h2 := hasSum_coe_mul_geometric_of_norm_lt_one hw2
  have h := (h1.add h2).div_const 2
  have hc : Complex.cos (θ : ℂ) = (e + e⁻¹) / 2 := by
    rw [Complex.cos, neg_mul, Complex.exp_neg]
  have hn1 : (1 : ℂ) - (z : ℂ) * e ≠ 0 := by
    intro h0; have : ‖(z : ℂ) * e‖ = 1 := by
      rw [show (z : ℂ) * e = 1 by linear_combination -h0, norm_one]
    linarith
  have hn2 : (1 : ℂ) - (z : ℂ) * e⁻¹ ≠ 0 := by
    intro h0; have : ‖(z : ℂ) * e⁻¹‖ = 1 := by
      rw [show (z : ℂ) * e⁻¹ = 1 by linear_combination -h0, norm_one]
    linarith
  have hD := den_pos hz0 hz1 (Real.cos_le_one θ)
  rw [← Complex.hasSum_ofReal]
  convert h using 1
  · funext n
    push_cast
    have e1 : e ^ n = Complex.exp ((n : ℂ) * θ * I) := by rw [← Complex.exp_nat_mul]; ring_nf
    have e2 : e⁻¹ ^ n = Complex.exp (-((n : ℂ) * θ) * I) := by
      rw [← Complex.exp_neg, ← Complex.exp_nat_mul]; ring_nf
    rw [mul_pow, mul_pow, e1, e2, Complex.cos]; ring
  · have hez : e - (z : ℂ) ≠ 0 := by
      intro h0
      have : ‖e‖ = |z| := by rw [show e = (z : ℂ) by linear_combination h0, Complex.norm_real, Real.norm_eq_abs]
      rw [he, abs_of_nonneg hz0] at this; linarith
    have hden : (1 : ℂ) - 2 * z * ((e + e⁻¹) / 2) + z ^ 2 = (1 - z * e) * (e - z) / e := by
      field_simp; ring
    have hinv : (1 : ℂ) - z * e⁻¹ = (e - z) / e := by field_simp
    push_cast
    rw [hc, hden, hinv]
    field_simp
    ring

/-- `∑_{j≥0} r^{j+1} cos((j+1)q)`. -/
theorem hasSum_cos_geom (q : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun j : ℕ => r ^ (j + 1) * Real.cos (q * ((j : ℝ) + 1)))
      ((r * Real.cos q - r ^ 2) / (1 - 2 * r * Real.cos q + r ^ 2)) := by
  set e : ℂ := Complex.exp ((q : ℂ) * I)
  have he : ‖e‖ = 1 := by simpa [e] using Complex.norm_exp_ofReal_mul_I q
  have he0 : e ≠ 0 := Complex.exp_ne_zero _
  have hw1 : ‖(r : ℂ) * e‖ < 1 := by rw [norm_mul, he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; simpa
  have hw2 : ‖(r : ℂ) * e⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv, he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; simpa
  have h1 := (hasSum_geometric_of_norm_lt_one hw1).mul_left ((r : ℂ) * e)
  have h2 := (hasSum_geometric_of_norm_lt_one hw2).mul_left ((r : ℂ) * e⁻¹)
  have h := (h1.add h2).div_const 2
  have hc : Complex.cos (q : ℂ) = (e + e⁻¹) / 2 := by
    rw [Complex.cos, neg_mul, Complex.exp_neg]
  have hn1 : (1 : ℂ) - (r : ℂ) * e ≠ 0 := by
    intro h0; have : ‖(r : ℂ) * e‖ = 1 := by
      rw [show (r : ℂ) * e = 1 by linear_combination -h0, norm_one]
    linarith
  have hn2 : (1 : ℂ) - (r : ℂ) * e⁻¹ ≠ 0 := by
    intro h0; have : ‖(r : ℂ) * e⁻¹‖ = 1 := by
      rw [show (r : ℂ) * e⁻¹ = 1 by linear_combination -h0, norm_one]
    linarith
  have hD := den_pos hr0 hr1 (Real.cos_le_one q)
  rw [← Complex.hasSum_ofReal]
  convert h using 1
  · funext j
    push_cast
    have e1 : e ^ (j + 1) = Complex.exp ((q : ℂ) * ((j : ℂ) + 1) * I) := by
      rw [← Complex.exp_nat_mul]; push_cast; ring_nf
    have e2 : e⁻¹ ^ (j + 1) = Complex.exp (-((q : ℂ) * ((j : ℂ) + 1)) * I) := by
      rw [← Complex.exp_neg, ← Complex.exp_nat_mul]; push_cast; ring_nf
    rw [← pow_succ', ← pow_succ', mul_pow, mul_pow, e1, e2, Complex.cos]; ring
  · have hez : e - (r : ℂ) ≠ 0 := by
      intro h0
      have : ‖e‖ = |r| := by rw [show e = (r : ℂ) by linear_combination h0, Complex.norm_real, Real.norm_eq_abs]
      rw [he, abs_of_nonneg hr0] at this; linarith
    have hden : (1 : ℂ) - 2 * r * ((e + e⁻¹) / 2) + r ^ 2 = (1 - r * e) * (e - r) / e := by
      field_simp; ring
    have hinv : (1 : ℂ) - r * e⁻¹ = (e - r) / e := by field_simp
    push_cast
    rw [hc, hden, hinv]
    field_simp
    ring

/-- `P(r, t) = (r t - r²)/(1 - 2rt + r²)` is strictly increasing in `t ∈ [-1, 1]` for `0 < r < 1`. -/
theorem P_strictMono {r t₁ t₂ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ht1 : -1 ≤ t₁) (h12 : t₁ < t₂) (ht2 : t₂ ≤ 1) :
    (r * t₁ - r ^ 2) / (1 - 2 * r * t₁ + r ^ 2) < (r * t₂ - r ^ 2) / (1 - 2 * r * t₂ + r ^ 2) := by
  have hd1 := den_pos hr0.le hr1 (by linarith : t₁ ≤ 1)
  have hd2 := den_pos hr0.le hr1 ht2
  rw [div_lt_div_iff₀ hd1 hd2]
  have : 0 < r * (1 - r ^ 2) * (t₂ - t₁) := by
    apply mul_pos (mul_pos hr0 (by nlinarith)) (by linarith)
  nlinarith

/-! ## The generating function of `B⁽¹⁾` -/

/-- `B⁽¹⁾(cosh x) = 2 sin²α ∑_n n cos²(nα) e^{-nx}` (`K = cos²α`, `x > 0`). -/
theorem B1_gen (α : ℝ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => 2 * sin α ^ 2 * ((n : ℝ) * Real.cos (n * α) ^ 2 * exp (-x) ^ n))
      (B1 (cos α ^ 2) (cosh x)) := by
  set z := exp (-x) with hz
  have hz0 : 0 < z := exp_pos _
  have hz1 : z < 1 := by rw [hz, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hA := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := z)
    (by rw [Real.norm_eq_abs, abs_of_pos hz0]; exact hz1)
  have hB := hasSum_n_cos (2 * α) hz0.le hz1
  have h := ((hA.add hB).div_const 2).mul_left (2 * sin α ^ 2)
  convert h using 1
  · funext n
    have : Real.cos (n * α) ^ 2 = (1 + Real.cos (n * (2 * α))) / 2 := by
      rw [show (n : ℝ) * (2 * α) = 2 * (n * α) by ring, Real.cos_two_mul]; ring
    rw [this]; ring
  · -- the rational identity
    have hzne : z ≠ 0 := hz0.ne'
    have hcosh : cosh x = (1 + z ^ 2) / (2 * z) := by
      rw [Real.cosh_eq, hz, Real.exp_neg]; field_simp
    have hs : sin α ^ 2 = 1 - cos α ^ 2 := by rw [← sin_sq_add_cos_sq α]; ring
    have hc2 : Real.cos (2 * α) = 2 * cos α ^ 2 - 1 := Real.cos_two_mul α
    have hD := den_pos hz0.le hz1 (Real.cos_le_one (2 * α))
    rw [hc2] at hD
    set Q := 1 - 2 * z * (2 * cos α ^ 2 - 1) + z ^ 2 with hQ
    have hz1' : (1 : ℝ) - z ≠ 0 := by linarith
    have hDd : Dd (cos α ^ 2) (cosh x) = Q / (2 * z) := by
      unfold Dd; rw [hcosh, hQ]; field_simp; ring
    have hcm : cosh x - 1 = (1 - z) ^ 2 / (2 * z) := by rw [hcosh]; field_simp; ring
    unfold B1
    have hQne : Q ≠ 0 := hD.ne'
    rw [hDd, hcm, hcosh, hc2, hs, ← hQ]
    field_simp
    ring

/-! ## Monotonicity of `F` -/

/-- The doubly indexed term `T(j,n) = 2 s n cos²(nα) e^{-n(j+1)ℓ} cos((j+1)q)`. -/
def Tjn (α ℓ q : ℝ) (p : ℕ × ℕ) : ℝ :=
  2 * sin α ^ 2 * ((p.2 : ℝ) * Real.cos (p.2 * α) ^ 2 * exp (-(((p.1 : ℝ) + 1) * ℓ)) ^ p.2) *
    Real.cos (q * ((p.1 : ℝ) + 1))

/-- `P(r,t) = (r t - r²)/(1 - 2rt + r²)`. -/
def Pq (r t : ℝ) : ℝ := (r * t - r ^ 2) / (1 - 2 * r * t + r ^ 2)

/-- `G(n,q) = 2 s n cos²(nα) P(e^{-nℓ}, cos q)`. -/
def Gn (α ℓ q : ℝ) (n : ℕ) : ℝ := 2 * sin α ^ 2 * ((n : ℝ) * Real.cos (n * α) ^ 2) * Pq (exp (-(n * ℓ))) (Real.cos q)

section mono
variable {α ℓ : ℝ} (hα0 : 0 < α) (hαπ : α < π) (hℓ : 0 < ℓ)
include hα0 hαπ hℓ

theorem rho_lt (j : ℕ) : exp (-(((j : ℝ) + 1) * ℓ)) < 1 := by
  have h : 0 < ((j : ℝ) + 1) * ℓ := by positivity
  have := Real.exp_lt_exp.mpr (show -(((j : ℝ) + 1) * ℓ) < 0 by linarith)
  rwa [Real.exp_zero] at this

theorem summable_Tjn (q : ℝ) : Summable (Tjn α ℓ q) := by
  set ρ := exp (-ℓ) with hρ
  have hρ0 : 0 < ρ := exp_pos _
  have hρ1 : ρ < 1 := by rw [hρ, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  -- dominating family g(j,n) = 2 n ρ_j^n
  set g : ℕ × ℕ → ℝ := fun p => 2 * ((p.2 : ℝ) * exp (-(((p.1 : ℝ) + 1) * ℓ)) ^ p.2) with hg
  have hg0 : 0 ≤ g := fun p => by simp only [hg]; positivity
  have hgs : Summable g := by
    rw [summable_prod_of_nonneg hg0]
    have hfib : ∀ j : ℕ, HasSum (fun n => g (j, n))
        (2 * (exp (-(((j : ℝ) + 1) * ℓ)) / (1 - exp (-(((j : ℝ) + 1) * ℓ))) ^ 2)) := fun j => by
      have := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := exp (-(((j : ℝ) + 1) * ℓ)))
        (by rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]; exact rho_lt hα0 hαπ hℓ j)
      exact this.mul_left 2
    refine ⟨fun j => (hfib j).summable, ?_⟩
    have hb : ∀ j : ℕ, ∑' n, g (j, n) ≤ (2 / (1 - ρ) ^ 2) * ρ ^ (j + 1) := fun j => by
      rw [(hfib j).tsum_eq]
      have hrj : exp (-(((j : ℝ) + 1) * ℓ)) = ρ ^ (j + 1) := by
        rw [hρ, ← Real.exp_nat_mul]; push_cast; ring_nf
      rw [hrj]
      have hpow : ρ ^ (j + 1) ≤ ρ := by
        calc ρ ^ (j + 1) ≤ ρ ^ 1 := pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
          _ = ρ := pow_one ρ
      have h1 : 0 < 1 - ρ := by linarith
      have h2 : 1 - ρ ≤ 1 - ρ ^ (j + 1) := by linarith
      have hp0 : 0 < ρ ^ (j + 1) := by positivity
      rw [show 2 * (ρ ^ (j + 1) / (1 - ρ ^ (j + 1)) ^ 2) = 2 * ρ ^ (j + 1) * (1 / (1 - ρ ^ (j + 1)) ^ 2) by ring,
        show 2 / (1 - ρ) ^ 2 * ρ ^ (j + 1) = 2 * ρ ^ (j + 1) * (1 / (1 - ρ) ^ 2) by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ h1.le h2 2
    apply Summable.of_nonneg_of_le (fun j => tsum_nonneg (fun n => hg0 (j, n))) hb
    exact ((summable_geometric_of_lt_one hρ0.le hρ1).mul_left ρ |>.congr (fun j => by ring)).mul_left _
  apply Summable.of_norm_bounded hgs
  intro p
  rw [Real.norm_eq_abs]
  simp only [Tjn, hg]
  have hs : |sin α ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [sin_sq_add_cos_sq α]
  have hc2 : |Real.cos (p.2 * α) ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [Real.sin_sq_add_cos_sq (p.2 * α)]
  have hc : |Real.cos (q * ((p.1 : ℝ) + 1))| ≤ 1 := abs_cos_le_one _
  have hr : 0 ≤ (p.2 : ℝ) * exp (-(((p.1 : ℝ) + 1) * ℓ)) ^ p.2 := by positivity
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_two]
  rw [show |(p.2 : ℝ)| = p.2 from abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (pow_nonneg (exp_pos _).le _)]
  have : |sin α ^ 2| * (↑p.2 * |Real.cos (↑p.2 * α) ^ 2| * exp (-((↑p.1 + 1) * ℓ)) ^ p.2) *
      |Real.cos (q * (↑p.1 + 1))| ≤ 1 * (↑p.2 * 1 * exp (-((↑p.1 + 1) * ℓ)) ^ p.2) * 1 := by
    gcongr
  nlinarith

/-- `∑_n T(j,n) = B⁽¹⁾(c_j) cos((j+1)q)`. -/
theorem hasSum_Tjn_fiber (q : ℝ) (j : ℕ) :
    HasSum (fun n => Tjn α ℓ q (j, n)) (B1 (cos α ^ 2) (cj ℓ j) * Real.cos (q * ((j : ℝ) + 1))) := by
  have hx : 0 < ((j : ℝ) + 1) * ℓ := by positivity
  have := (B1_gen α hx).mul_right (Real.cos (q * ((j : ℝ) + 1)))
  convert this using 1
  · funext n; simp only [Tjn]
  · rfl

/-- `∑_j T(j,n) = G(n,q)`. -/
theorem hasSum_Tjn_fiber' (q : ℝ) (n : ℕ) : HasSum (fun j => Tjn α ℓ q (j, n)) (Gn α ℓ q n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Tjn, Gn]
  · have hr0 : 0 ≤ exp (-(n * ℓ)) := (exp_pos _).le
    have hr1 : exp (-(n * ℓ)) < 1 := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by
        have : (0 : ℝ) < n := by exact_mod_cast hn
        have : 0 < (n : ℝ) * ℓ := by positivity
        linarith)
    have := (hasSum_cos_geom q hr0 hr1).mul_left (2 * sin α ^ 2 * ((n : ℝ) * Real.cos (n * α) ^ 2))
    convert this using 1
    funext j
    simp only [Tjn]
    have : exp (-(((j : ℝ) + 1) * ℓ)) ^ n = exp (-(n * ℓ)) ^ (j + 1) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [this]; ring
    · rfl

/-- `F(q) = ∑_j B⁽⁰⁾(c_j) + ∑_n G(n,q)`. -/
theorem F_eq_split (q : ℝ) :
    F (cos α ^ 2) ℓ q = (∑' j, B0 (cos α ^ 2) (cj ℓ j)) + ∑' n, Gn α ℓ q n := by
  have hT := summable_Tjn hα0 hαπ hℓ q
  have hcomm := hT.tsum_comm (f := fun j n => Tjn α ℓ q (j, n))
  have h1 : ∑' n, ∑' j, Tjn α ℓ q (j, n) = ∑' n, Gn α ℓ q n :=
    tsum_congr fun n => (hasSum_Tjn_fiber' hα0 hαπ hℓ q n).tsum_eq
  have h2 : ∑' j, ∑' n, Tjn α ℓ q (j, n) = ∑' j, B1 (cos α ^ 2) (cj ℓ j) * Real.cos (q * ((j : ℝ) + 1)) :=
    tsum_congr fun j => (hasSum_Tjn_fiber hα0 hαπ hℓ q j).tsum_eq
  have sB0 := summable_B0 hα0 hαπ hℓ
  have sB1c : Summable (fun j => B1 (cos α ^ 2) (cj ℓ j) * Real.cos (q * ((j : ℝ) + 1))) := by
    apply Summable.of_norm_bounded (summable_B1 hα0 hαπ hℓ).abs
    intro j; rw [Real.norm_eq_abs, abs_mul]
    have := abs_cos_le_one (q * ((j : ℝ) + 1))
    nlinarith [abs_nonneg (B1 (cos α ^ 2) (cj ℓ j))]
  unfold F term
  rw [sB0.tsum_add sB1c, ← h2, ← hcomm, h1]

theorem summable_Gn (q : ℝ) : Summable (Gn α ℓ q) := by
  have hT := summable_Tjn hα0 hαπ hℓ q
  have := hT.prod_symm.prod
  refine this.congr (fun n => ?_)
  exact (hasSum_Tjn_fiber' hα0 hαπ hℓ q n).tsum_eq

/-- **Critical mode.** `F` is strictly decreasing on `[0, π]`. -/
theorem F_strictAntiOn : StrictAntiOn (F (cos α ^ 2) ℓ) (Set.Icc 0 π) := by
  intro q₁ hq₁ q₂ hq₂ h12
  rw [F_eq_split hα0 hαπ hℓ, F_eq_split hα0 hαπ hℓ]
  have hcos : Real.cos q₂ < Real.cos q₁ := Real.cos_lt_cos_of_nonneg_of_le_pi hq₁.1 hq₂.2 h12
  have hs : 0 < sin α ^ 2 := by have := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ; positivity
  have hle : ∀ n, Gn α ℓ q₂ n ≤ Gn α ℓ q₁ n := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Gn]
    · unfold Gn
      have hr0 : 0 < exp (-(n * ℓ)) := exp_pos _
      have hr1 : exp (-(n * ℓ)) < 1 := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by
          have : (0 : ℝ) < n := by exact_mod_cast hn
          have : 0 < (n : ℝ) * ℓ := by positivity
          linarith)
      have := P_strictMono hr0 hr1 (Real.neg_one_le_cos q₂) hcos (Real.cos_le_one q₁)
      unfold Pq
      have hcoef : 0 ≤ 2 * sin α ^ 2 * ((n : ℝ) * Real.cos (n * α) ^ 2) := by positivity
      exact mul_le_mul_of_nonneg_left this.le hcoef
  have hstrict : ∀ n : ℕ, 0 < n → Real.cos (n * α) ≠ 0 → Gn α ℓ q₂ n < Gn α ℓ q₁ n := fun n hn hc => by
    unfold Gn
    have hr0 : 0 < exp (-(n * ℓ)) := exp_pos _
    have hr1 : exp (-(n * ℓ)) < 1 := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by
        have : (0 : ℝ) < n := by exact_mod_cast hn
        have : 0 < (n : ℝ) * ℓ := by positivity
        linarith)
    have := P_strictMono hr0 hr1 (Real.neg_one_le_cos q₂) hcos (Real.cos_le_one q₁)
    unfold Pq
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hcoef : 0 < 2 * sin α ^ 2 * ((n : ℝ) * Real.cos (n * α) ^ 2) := by
      have : 0 < Real.cos (n * α) ^ 2 := by positivity
      positivity
    exact mul_lt_mul_of_pos_left this hcoef
  have hlt : ∑' n, Gn α ℓ q₂ n < ∑' n, Gn α ℓ q₁ n := by
    by_cases hc1 : Real.cos α = 0
    · have hc2 : Real.cos (((2 : ℕ) : ℝ) * α) ≠ 0 := by
        rw [show ((2 : ℕ) : ℝ) * α = 2 * α by norm_num, Real.cos_two_mul, hc1]; norm_num
      exact (summable_Gn hα0 hαπ hℓ q₂).tsum_lt_tsum hle (hstrict 2 (by norm_num) hc2)
        (summable_Gn hα0 hαπ hℓ q₁)
    · have hc1' : Real.cos (((1 : ℕ) : ℝ) * α) ≠ 0 := by simpa using hc1
      exact (summable_Gn hα0 hαπ hℓ q₂).tsum_lt_tsum hle (hstrict 1 (by norm_num) hc1')
        (summable_Gn hα0 hαπ hℓ q₁)
  linarith

/-- `F` depends on `q` only through `cos q`. -/
theorem F_arccos (q : ℝ) : F (cos α ^ 2) ℓ q = F (cos α ^ 2) ℓ (Real.arccos (Real.cos q)) := by
  unfold F term
  congr 1; funext n
  congr 2
  have h1 := Polynomial.Chebyshev.T_real_cos q ((n : ℤ) + 1)
  have h2 := Polynomial.Chebyshev.T_real_cos (Real.arccos (Real.cos q)) ((n : ℤ) + 1)
  rw [Real.cos_arccos (Real.neg_one_le_cos q) (Real.cos_le_one q)] at h2
  push_cast at h1 h2
  rw [mul_comm q, mul_comm (Real.arccos _), ← h1, ← h2]

/-- `F(q) ≥ F(π)` for every `q`: the pairing mode is critical. -/
theorem F_ge_F_pi (q : ℝ) : F (cos α ^ 2) ℓ π ≤ F (cos α ^ 2) ℓ q := by
  rw [F_arccos hα0 hαπ hℓ q]
  have hmem : Real.arccos (Real.cos q) ∈ Set.Icc 0 π := ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  rcases eq_or_lt_of_le hmem.2 with h | h
  · rw [h]
  · exact (F_strictAntiOn hα0 hαπ hℓ hmem ⟨by linarith [Real.pi_pos], le_rfl⟩ h).le

/-- **Stability of hypercycle rows.** For `0 < α < π` and `ℓ > 0`, every Bloch mode with `cos q ≠ 1` of the
row is spectrally stable iff `F(π) ≥ 0`. -/
theorem row_stable_iff_F_pi :
    (∀ q : ℝ, Real.cos q ≠ 1 → ∀ σ, Module.End.HasEigenvalue
        (Matrix.toLin' (rowFlow (varpi α ℓ q) (2 * F (cos α ^ 2) ℓ q) (Cser (cos α ^ 2) ℓ q))) σ →
        σ.re = 0) ↔ 0 ≤ F (cos α ^ 2) ℓ π := by
  constructor
  · intro h
    have hπ : Real.cos π ≠ 1 := by rw [Real.cos_pi]; norm_num
    exact (bloch_stable_iff hα0 hαπ hℓ hπ).mp (h π hπ)
  · intro h q hq
    exact (bloch_stable_iff hα0 hαπ hℓ hq).mpr (h.trans (F_ge_F_pi hα0 hαπ hℓ q))

end mono

end HyperbolicRings.Rows
