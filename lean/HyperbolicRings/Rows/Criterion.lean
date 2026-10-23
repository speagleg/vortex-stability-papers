/-
New in this paper (vortex-stability-papers, paper 3). Not copied from the source repositories.

Hypercycle rows of the tanh kernel: consequences of the Bloch criterion
(paper, Theorem "critical curvature", parts (a)-(c)).

`F K ℓ q = ∑_{j ≥ 1} [B⁽⁰⁾(c_j) + B⁽¹⁾(c_j) cos(q j)]`, `c_j = cosh(j ℓ)` (here `ℓ` is the strip
spacing `ℓ_u`), is the quantity whose sign decides spectral stability of the Bloch mode `q`
(the row is spectrally stable iff `F q ≥ 0` for all `q`; that reduction is by hand in the paper).
Proved here, for `K = κ² ∈ [0,1)` and every `ℓ > 0`:

* `F_summable`: the series converges absolutely;
* `stability_bound`: if `(2K-1) cosh ℓ ≥ 1` then `F q > 0` for every `q`;
* `all_mode_instability`: if `K ≤ 1/4` then `F q < 0` for every `q`;
* `pairing_instability`: if `K ≤ 1/2` then `F π < 0` (the pairing mode is unstable at every spacing,
  i.e. `κ_c = 1/√2` bounds the unstable region from above).
-/
import HyperbolicRings.Rows.Pair
import HyperbolicRings.Tanh.LargeN.CritMode

noncomputable section

namespace HyperbolicRings.Rows

open Real

/-- `c_j = cosh(j ℓ)` with `j = n + 1`. -/
def cj (ℓ : ℝ) (n : ℕ) : ℝ := cosh (((n : ℝ) + 1) * ℓ)

/-- The summand of `F(q)` at `j = n + 1`. -/
def term (K ℓ q : ℝ) (n : ℕ) : ℝ := B0 K (cj ℓ n) + B1 K (cj ℓ n) * cos (q * ((n : ℝ) + 1))

/-- `F(q) = ∑_{j≥1} [B⁽⁰⁾(c_j) + B⁽¹⁾(c_j) cos qj]`. -/
def F (K ℓ q : ℝ) : ℝ := ∑' n, term K ℓ q n

variable {K ℓ : ℝ}

theorem cj_ge (hℓ : 0 < ℓ) (n : ℕ) : cosh ℓ ≤ cj ℓ n := by
  unfold cj
  rw [Real.cosh_le_cosh, abs_of_pos hℓ, abs_of_pos (by positivity)]
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith

theorem one_lt_cosh_of_pos (hℓ : 0 < ℓ) : 1 < cosh ℓ := Real.one_lt_cosh.mpr hℓ.ne'

theorem one_lt_cj (hℓ : 0 < ℓ) (n : ℕ) : 1 < cj ℓ n :=
  lt_of_lt_of_le (one_lt_cosh_of_pos hℓ) (cj_ge hℓ n)

theorem cj_lt_succ (hℓ : 0 < ℓ) (n : ℕ) : cj ℓ n < cj ℓ (n + 1) := by
  unfold cj
  rw [Real.cosh_lt_cosh, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  push_cast; nlinarith

/-- `1/(c_j - 1) ≤ 2/(ℓ² j²)`. -/
theorem inv_cj_sub_one_le (hℓ : 0 < ℓ) (n : ℕ) :
    1 / (cj ℓ n - 1) ≤ 2 / ℓ ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
  have hy0 : 0 < ((n : ℝ) + 1) * ℓ := mul_pos (by positivity) hℓ
  have hy : 0 ≤ ((n : ℝ) + 1) * ℓ := hy0.le
  have h := HyperbolicRings.Tanh.LargeN.one_add_sq_half_le_cosh hy
  have hpos : 0 < (((n : ℝ) + 1) * ℓ) ^ 2 / 2 := div_pos (pow_pos hy0 2) two_pos
  have : 1 / (cj ℓ n - 1) ≤ 1 / ((((n : ℝ) + 1) * ℓ) ^ 2 / 2) :=
    one_div_le_one_div_of_le hpos (by unfold cj; linarith)
  calc 1 / (cj ℓ n - 1) ≤ 1 / ((((n : ℝ) + 1) * ℓ) ^ 2 / 2) := this
    _ = 2 / ℓ ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by field_simp

theorem summable_inv_sq_shift (A : ℝ) :
    Summable (fun n : ℕ => A * (1 / ((n : ℝ) + 1) ^ 2)) := by
  apply Summable.mul_left
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa [Nat.cast_add, Nat.cast_one] using h

/-- For `c ≥ c₁ > 1`: `|𝔤_o(c)|, |𝔤_e(c)| ≤ 3 M/(c-1)` with `M = (c₁+1)/(c₁-1)`. -/
theorem abs_go_le (hK0 : 0 ≤ K) (hK : K < 1) {c₁ c : ℝ} (hc₁ : 1 < c₁) (hc : c₁ ≤ c) :
    |go K c| ≤ 3 * ((c₁ + 1) / (c₁ - 1)) * (1 / (c - 1)) := by
  have hc1 : 0 < c - 1 := by linarith
  have hD := Dd_pos hK (by linarith : 1 < c)
  have hDge : c - 1 ≤ Dd K c := Dd_ge hK.le
  have hM : (c + 1) / (c - 1) ≤ (c₁ + 1) / (c₁ - 1) := by
    rw [div_le_div_iff₀ hc1 (by linarith)]; nlinarith
  unfold go
  rw [abs_div, abs_of_pos (mul_pos hc1 hD)]
  have hnum : |(2 * K - 1) * c - 1| ≤ c + 1 := by
    rw [abs_le]; constructor <;> nlinarith
  calc |(2 * K - 1) * c - 1| / ((c - 1) * Dd K c) ≤ (c + 1) / ((c - 1) * (c - 1)) := by
        apply div_le_div₀ (by linarith) hnum (by positivity)
        exact mul_le_mul_of_nonneg_left hDge hc1.le
    _ = (c + 1) / (c - 1) * (1 / (c - 1)) := by field_simp
    _ ≤ 3 * ((c₁ + 1) / (c₁ - 1)) * (1 / (c - 1)) := by
        apply mul_le_mul_of_nonneg_right _ (one_div_nonneg.mpr hc1.le)
        have : 0 ≤ (c + 1) / (c - 1) := div_nonneg (by linarith) hc1.le
        nlinarith

theorem abs_ge_le (hK0 : 0 ≤ K) (hK : K < 1) {c₁ c : ℝ} (hc₁ : 1 < c₁) (hc : c₁ ≤ c) :
    |ge K c| ≤ 3 * ((c₁ + 1) / (c₁ - 1)) * (1 / (c - 1)) := by
  have hc1 : 0 < c - 1 := by linarith
  have hD := Dd_pos hK (by linarith : 1 < c)
  have hDge : c - 1 ≤ Dd K c := Dd_ge hK.le
  have hM : (c + 1) / (c - 1) ≤ (c₁ + 1) / (c₁ - 1) := by
    rw [div_le_div_iff₀ hc1 (by linarith)]; nlinarith
  unfold ge
  rw [abs_div, abs_of_pos (by positivity : 0 < Dd K c ^ 2)]
  have hnum : |(4 * K - 1) * c - (4 * K ^ 2 - 2 * K + 1)| ≤ 3 * (c + 1) := by
    rw [abs_le]; constructor <;> nlinarith
  calc |(4 * K - 1) * c - (4 * K ^ 2 - 2 * K + 1)| / Dd K c ^ 2
        ≤ 3 * (c + 1) / ((c - 1) * (c - 1)) := by
        apply div_le_div₀ (by linarith) hnum (by positivity)
        rw [sq]; exact mul_le_mul hDge hDge hc1.le hD.le
    _ = 3 * ((c + 1) / (c - 1)) * (1 / (c - 1)) := by field_simp
    _ ≤ 3 * ((c₁ + 1) / (c₁ - 1)) * (1 / (c - 1)) := by
        apply mul_le_mul_of_nonneg_right _ (one_div_nonneg.mpr hc1.le)
        linarith

theorem summable_bound (hℓ : 0 < ℓ) (A : ℝ) (hA : 0 ≤ A) {f : ℕ → ℝ}
    (hf : ∀ n, |f n| ≤ A * (1 / (cj ℓ n - 1))) : Summable f := by
  apply Summable.of_norm_bounded (summable_inv_sq_shift (A * (2 / ℓ ^ 2)))
  intro n
  rw [Real.norm_eq_abs]
  calc |f n| ≤ A * (1 / (cj ℓ n - 1)) := hf n
    _ ≤ A * (2 / ℓ ^ 2 * (1 / ((n : ℝ) + 1) ^ 2)) :=
        mul_le_mul_of_nonneg_left (inv_cj_sub_one_le hℓ n) hA
    _ = A * (2 / ℓ ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by ring

theorem summable_go (hK0 : 0 ≤ K) (hK : K < 1) (hℓ : 0 < ℓ) :
    Summable (fun n => go K (cj ℓ n)) :=
  summable_bound hℓ _ (by have := one_lt_cosh_of_pos hℓ
                          have : 0 < (cosh ℓ + 1) / (cosh ℓ - 1) := div_pos (by linarith) (by linarith)
                          positivity)
    (fun n => abs_go_le hK0 hK (one_lt_cosh_of_pos hℓ) (cj_ge hℓ n))

theorem summable_ge (hK0 : 0 ≤ K) (hK : K < 1) (hℓ : 0 < ℓ) :
    Summable (fun n => ge K (cj ℓ n)) :=
  summable_bound hℓ _ (by have := one_lt_cosh_of_pos hℓ
                          have : 0 < (cosh ℓ + 1) / (cosh ℓ - 1) := div_pos (by linarith) (by linarith)
                          positivity)
    (fun n => abs_ge_le hK0 hK (one_lt_cosh_of_pos hℓ) (cj_ge hℓ n))

/-- `B⁽⁰⁾ = s(𝔤_o + 𝔤_e)/2`, `B⁽¹⁾ = s(𝔤_e - 𝔤_o)/2`. -/
theorem term_eq (hK : K < 1) (hℓ : 0 < ℓ) (q : ℝ) (n : ℕ) :
    term K ℓ q n = (1 - K) / 2 * (go K (cj ℓ n) + ge K (cj ℓ n)) +
      (1 - K) / 2 * (ge K (cj ℓ n) - go K (cj ℓ n)) * cos (q * ((n : ℝ) + 1)) := by
  have h1 := B0_sub_B1 hK (one_lt_cj hℓ n)
  have h2 := B0_add_B1 hK (one_lt_cj hℓ n)
  unfold term
  have e0 : B0 K (cj ℓ n) = (1 - K) / 2 * (go K (cj ℓ n) + ge K (cj ℓ n)) := by linarith
  have e1 : B1 K (cj ℓ n) = (1 - K) / 2 * (ge K (cj ℓ n) - go K (cj ℓ n)) := by linarith
  rw [e0, e1]

/-- The series defining `F(q)` converges absolutely. -/
theorem F_summable (hK0 : 0 ≤ K) (hK : K < 1) (hℓ : 0 < ℓ) (q : ℝ) :
    Summable (term K ℓ q) := by
  have so := summable_go hK0 hK hℓ
  have se := summable_ge hK0 hK hℓ
  have hs : Summable (fun n => (1 - K) / 2 * (|go K (cj ℓ n)| + |ge K (cj ℓ n)|) * 2) :=
    ((so.abs.add se.abs).mul_left _).mul_right _
  apply Summable.of_norm_bounded hs
  intro n
  rw [Real.norm_eq_abs, term_eq hK hℓ q n]
  have hs0 : 0 ≤ (1 - K) / 2 := by linarith
  have hc := abs_le.mp (abs_cos_le_one (q * ((n : ℝ) + 1)))
  set a := go K (cj ℓ n); set b := ge K (cj ℓ n); set x := cos (q * ((n : ℝ) + 1))
  have h1 : |(1 - K) / 2 * (a + b)| ≤ (1 - K) / 2 * (|a| + |b|) := by
    rw [abs_mul, abs_of_nonneg hs0]; exact mul_le_mul_of_nonneg_left (abs_add_le a b) hs0
  have h2 : |(1 - K) / 2 * (b - a) * x| ≤ (1 - K) / 2 * (|a| + |b|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hs0]
    have hx1 : |x| ≤ 1 := abs_cos_le_one _
    have hba : |b - a| ≤ |a| + |b| := by
      calc |b - a| ≤ |b| + |a| := abs_sub b a
        _ = |a| + |b| := add_comm _ _
    have hba0 : 0 ≤ |b - a| := abs_nonneg _
    calc (1 - K) / 2 * |b - a| * |x| ≤ (1 - K) / 2 * |b - a| * 1 :=
          mul_le_mul_of_nonneg_left hx1 (mul_nonneg hs0 hba0)
      _ ≤ (1 - K) / 2 * (|a| + |b|) := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hba hs0
  calc |(1 - K) / 2 * (a + b) + (1 - K) / 2 * (b - a) * x|
      ≤ |(1 - K) / 2 * (a + b)| + |(1 - K) / 2 * (b - a) * x| := abs_add_le _ _
    _ ≤ (1 - K) / 2 * (|a| + |b|) * 2 := by linarith

/-- `B⁽⁰⁾ + B⁽¹⁾ cos θ ≥ B⁽⁰⁾ - B⁽¹⁾` and `≤ B⁽⁰⁾ + B⁽¹⁾` (since `B⁽¹⁾ > 0`). -/
theorem term_bounds (hK0 : 0 ≤ K) (hK : K < 1) (hℓ : 0 < ℓ) (q : ℝ) (n : ℕ) :
    (1 - K) * go K (cj ℓ n) ≤ term K ℓ q n ∧ term K ℓ q n ≤ (1 - K) * ge K (cj ℓ n) := by
  have hb := B1_pos hK0 hK (one_lt_cj hℓ n)
  have h1 := B0_sub_B1 hK (one_lt_cj hℓ n)
  have h2 := B0_add_B1 hK (one_lt_cj hℓ n)
  have hc := abs_le.mp (abs_cos_le_one (q * ((n : ℝ) + 1)))
  unfold term
  constructor <;> nlinarith

/-- **Stability bound.** If `(2K-1) cosh ℓ ≥ 1` (so `K > 1/2`), then `F(q) > 0` for every `q`:
every Bloch mode is spectrally stable. -/
theorem stability_bound (hK0 : 0 ≤ K) (hK : K < 1) (hℓ : 0 < ℓ)
    (h : 1 ≤ (2 * K - 1) * cosh ℓ) (q : ℝ) : 0 < F K ℓ q := by
  have hcosh := one_lt_cosh_of_pos hℓ
  have h2K : 0 < 2 * K - 1 := by
    by_contra hneg; push_neg at hneg; nlinarith
  have hs : 0 < 1 - K := by linarith
  have hnn : ∀ n, 0 ≤ term K ℓ q n := fun n => by
    have := (term_bounds hK0 hK hℓ q n).1
    have : 0 ≤ go K (cj ℓ n) := go_nonneg hK (one_lt_cj hℓ n) (by
      have := cj_ge hℓ n; nlinarith)
    nlinarith
  have hp : 0 < term K ℓ q 1 := by
    have := (term_bounds hK0 hK hℓ q 1).1
    have : 0 < go K (cj ℓ 1) := go_pos hK (one_lt_cj hℓ 1) (by
      have h01 := cj_lt_succ hℓ 0
      have := cj_ge hℓ 0; nlinarith)
    nlinarith
  exact (F_summable hK0 hK hℓ q).tsum_pos hnn 1 hp

/-- **All-mode instability.** If `K ≤ 1/4` (`|κ| ≤ 1/2`, geodesics included), then `F(q) < 0` for
every `q`: every Bloch mode `q ≠ 0` grows, at every spacing. -/
theorem all_mode_instability (hK0 : 0 ≤ K) (hK : K ≤ 1 / 4) (hℓ : 0 < ℓ) (q : ℝ) :
    F K ℓ q < 0 := by
  have hK1 : K < 1 := by linarith
  have hs : 0 < 1 - K := by linarith
  have hneg : ∀ n, 0 < -term K ℓ q n := fun n => by
    have := (term_bounds hK0 hK1 hℓ q n).2
    have := ge_neg hK0 hK (one_lt_cj hℓ n)
    nlinarith
  have := (F_summable hK0 hK1 hℓ q).neg.tsum_pos (fun n => (hneg n).le) 0 (hneg 0)
  unfold F; rw [tsum_neg] at this; linarith

/-- `1/cosh x ≤ 2 e^{-x}`. -/
theorem inv_cosh_le (x : ℝ) : 1 / cosh x ≤ 2 * exp (-x) := by
  have hc : 0 < cosh x := cosh_pos x
  rw [div_le_iff₀ hc, Real.cosh_eq]
  have : exp (-x) * exp x = 1 := by rw [← Real.exp_add]; simp
  have : 0 < exp (-x) := exp_pos _
  nlinarith [exp_pos x]

/-- The comparison sequence for the pairing sum. -/
def bnd (ℓ : ℝ) : ℕ → ℝ
  | 0 => -1 / ((cosh ℓ - 1) * cosh ℓ)
  | n + 1 => 2 * exp (-2 * ℓ) * exp (-ℓ) ^ n

theorem cos_pi_mul (n : ℕ) : cos (π * ((n : ℝ) + 1)) = (-1) ^ (n + 1) := by
  rw [mul_comm, show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring]
  exact Real.cos_nat_mul_pi (n + 1)

/-- Termwise comparison at `q = π` for `K ≤ 1/2`: `term n ≤ s·bnd n`. -/
theorem term_pi_le (hK0 : 0 ≤ K) (hK : K ≤ 1 / 2) (hℓ : 0 < ℓ) (n : ℕ) :
    term K ℓ π n ≤ (1 - K) * bnd ℓ n := by
  have hK1 : K < 1 := by linarith
  have hs : 0 < 1 - K := by linarith
  have hc := one_lt_cj hℓ n
  have h1 := B0_sub_B1 hK1 hc
  have h2 := B0_add_B1 hK1 hc
  have ho := go_le_half hK hc
  have he := ge_le_half hK0 hK hc
  have hcpos : 0 < cj ℓ n := by linarith
  -- even-j bound: (c-1)/c² ≤ 1/c ≤ 2 e^{-jℓ}
  have hEven : (cj ℓ n - 1) / cj ℓ n ^ 2 ≤ 2 * exp (-(((n : ℝ) + 1) * ℓ)) := by
    have : (cj ℓ n - 1) / cj ℓ n ^ 2 ≤ 1 / cj ℓ n := by
      rw [div_le_div_iff₀ (by positivity) hcpos]; nlinarith
    exact this.trans (inv_cosh_le _)
  have hOdd : -1 / ((cj ℓ n - 1) * cj ℓ n) < 0 := by
    apply div_neg_of_neg_of_pos (by norm_num); exact mul_pos (by linarith) hcpos
  have hexp : 0 < 2 * exp (-(((n : ℝ) + 1) * ℓ)) := by positivity
  have hcos := cos_pi_mul n
  unfold term
  rw [hcos]
  rcases Nat.even_or_odd (n + 1) with hev | hod
  · -- j = n+1 even, so n ≥ 1
    rw [hev.neg_one_pow, mul_one]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by obtain ⟨k, hk⟩ := hev; omega⟩
    simp only [bnd]
    have : 2 * exp (-2 * ℓ) * exp (-ℓ) ^ m = 2 * exp (-((((m + 1 : ℕ) : ℝ) + 1) * ℓ)) := by
      rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]; push_cast; ring_nf
    rw [this]
    have := mul_le_mul_of_nonneg_left (he.trans hEven) hs.le
    have : B0 K (cj ℓ (m + 1)) + B1 K (cj ℓ (m + 1)) = (1 - K) * ge K (cj ℓ (m + 1)) := h2
    push_cast at *
    nlinarith
  · rw [hod.neg_one_pow]
    have hT : B0 K (cj ℓ n) + B1 K (cj ℓ n) * -1 = (1 - K) * go K (cj ℓ n) := by linarith
    rw [hT]
    rcases n with _ | m
    · simp only [bnd]
      have : cj ℓ 0 = cosh ℓ := by simp [cj]
      rw [← this]
      exact mul_le_mul_of_nonneg_left ho hs.le
    · simp only [bnd]
      have hpos : 0 < 2 * exp (-2 * ℓ) * exp (-ℓ) ^ m := by positivity
      have := mul_le_mul_of_nonneg_left ho hs.le
      nlinarith

theorem bnd_summable (hℓ : 0 < ℓ) : Summable (bnd ℓ) := by
  rw [← summable_nat_add_iff 1]
  have hr : exp (-ℓ) < 1 := by
    have := Real.exp_lt_exp.mpr (show -ℓ < 0 by linarith); simpa using this
  exact (summable_geometric_of_lt_one (exp_pos _).le hr).mul_left _

theorem bnd_tsum_neg (hℓ : 0 < ℓ) : ∑' n, bnd ℓ n < 0 := by
  have hr : exp (-ℓ) < 1 := by
    have := Real.exp_lt_exp.mpr (show -ℓ < 0 by linarith); simpa using this
  rw [(bnd_summable hℓ).tsum_eq_zero_add]
  have hg : ∑' n, bnd ℓ (n + 1) = 2 * exp (-2 * ℓ) / (1 - exp (-ℓ)) := by
    simp only [bnd]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (exp_pos _).le hr]; ring
  rw [hg]
  simp only [bnd]
  -- with u = e^ℓ > 1: 1/((c-1)c) > 2/(u(u-1))
  set u := exp ℓ with hu
  have hu1 : 1 < u := by
    have := Real.exp_lt_exp.mpr hℓ; simpa [hu] using this
  have hinv : exp (-ℓ) = u⁻¹ := by rw [hu, Real.exp_neg]
  have hinv2 : exp (-2 * ℓ) = (u ^ 2)⁻¹ := by
    rw [hu, ← Real.exp_nat_mul, ← Real.exp_neg]; push_cast; ring_nf
  have hc : cosh ℓ = (u + u⁻¹) / 2 := by rw [Real.cosh_eq, hu, Real.exp_neg]
  rw [hinv, hinv2, hc]
  have hu0 : 0 < u := by linarith
  have hA : 0 < ((u + u⁻¹) / 2 - 1) * ((u + u⁻¹) / 2) := by
    have e : ((u + u⁻¹) / 2 - 1) * ((u + u⁻¹) / 2) = (u - 1) ^ 2 * (u ^ 2 + 1) / (4 * u ^ 2) := by
      field_simp; ring
    rw [e]; have : 0 < u - 1 := by linarith
    positivity
  have e : ((u + u⁻¹) / 2 - 1) * ((u + u⁻¹) / 2) = (u - 1) ^ 2 * (u ^ 2 + 1) / (4 * u ^ 2) := by
    field_simp; ring
  have e2 : 2 * (u ^ 2)⁻¹ / (1 - u⁻¹) = 2 / (u * (u - 1)) := by
    have : u - 1 ≠ 0 := by linarith
    field_simp
  rw [e, e2]
  have hu1' : 0 < u - 1 := by linarith
  rw [neg_div, div_div_eq_mul_div, neg_add_lt_iff_lt_add, add_zero]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos hu0 3, pow_pos hu0 4, mul_pos hu0 hu1']

/-- **Pairing instability below `κ_c`.** If `K ≤ 1/2` (`|κ| ≤ 1/√2`), then `F(π) < 0` at every
spacing `ℓ > 0`: the pairing mode `q = π` is unstable (its exponents are `±√(B(π) C(π))`, real,
since `B(π) = 2F(π) < 0` and `C(π) < 0` by `C1_neg`). -/
theorem pairing_instability (hK0 : 0 ≤ K) (hK : K ≤ 1 / 2) (hℓ : 0 < ℓ) : F K ℓ π < 0 := by
  have hK1 : K < 1 := by linarith
  have hs : 0 < 1 - K := by linarith
  have hle : F K ℓ π ≤ ∑' n, (1 - K) * bnd ℓ n :=
    (F_summable hK0 hK1 hℓ π).tsum_le_tsum (term_pi_le hK0 hK hℓ) ((bnd_summable hℓ).mul_left _)
  rw [tsum_mul_left] at hle
  have := bnd_tsum_neg hℓ
  nlinarith

end HyperbolicRings.Rows
