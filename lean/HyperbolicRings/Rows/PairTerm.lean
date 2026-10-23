/-
New in this paper (vortex-stability-papers, paper 3). Not copied from the source repositories.

The tanh pair term in the strip chart and its second partial derivatives at a hypercycle row
(paper, Proposition "Bloch symbol" and Appendix C).

* `stripW u₀ φ₀ u₁ φ₁ = ½[log(cosh(u₀-u₁) - cos(φ₀+φ₁)) - log(cosh(u₀-u₁) - cos(φ₀-φ₁))]`.
* `stripW_eq_pairG`: it is the tanh pair term `-log|z₀ - z₁| + log|z₀ - z̄₁|` of the upper half-plane
  (`pairG`, used for the horocycle row) at `z_j = e^{u_j + iφ_j}`.
* Second partial derivatives are iterated one-variable `deriv`s of restrictions, at the row pair
  `(u₀, φ₀, u₁, φ₁) = (0, α, b, α)`, exactly as for the horocycle row (`RowHessian.lean`). Their values are
  computed in closed form (`onB_val`, `cpB_val`, `onC_val`, `cpC_val`, `onU_val`, `cpU_val`, `onP_val`, `cpP_val`),
  and the even ones are identified with the pair functions `B0`, `B1`, `C1` of `Rows.Pair` (`onB_eq_B0`,
  `cpB_eq_B1`, `onC_eq_C1`).

Equations of motion (strip chart, area form `du dφ / sin² φ`): `u̇ = sin²φ ∂_φ H`, `φ̇ = -sin²φ ∂_u H`.
The per-pair coefficients of the linearisation of vortex `0` are:
  `δφ₀` in `u̇₀`: `onB = ∂_{φ₀}(sin²φ₀ ∂_{φ₀} W)`;   `δφ_k` in `u̇₀`: `cpB = sin²α ∂_{φ_k}∂_{φ₀} W`;
  `δu₀` in `φ̇₀`: `onC = -sin²α ∂²_{u₀} W`;           `δu_k` in `φ̇₀`: `cpC = -sin²α ∂_{u_k}∂_{u₀} W`;
  `δu₀` in `u̇₀`: `onU = sin²α ∂_{u₀}∂_{φ₀} W`;        `δu_k` in `u̇₀`: `cpU = sin²α ∂_{u_k}∂_{φ₀} W`;
  `δφ₀` in `φ̇₀`: `onP = -∂_{φ₀}(sin²φ₀ ∂_{u₀} W)`;   `δφ_k` in `φ̇₀`: `cpP = -sin²α ∂_{φ_k}∂_{u₀} W`.
(The momentum of the `u`-translations contributes only the constant drift; see the paper.)
-/
import HyperbolicRings.Rows.Pair
import HyperbolicRings.Tanh.LargeN.RowHessian

noncomputable section

namespace HyperbolicRings.Rows

open Real Filter Topology

/-- The tanh pair term in the strip chart `z = e^{u + iφ}` of the upper half-plane. -/
def stripW (u₀ φ₀ u₁ φ₁ : ℝ) : ℝ :=
  (log (cosh (u₀ - u₁) - cos (φ₀ + φ₁)) - log (cosh (u₀ - u₁) - cos (φ₀ - φ₁))) / 2

theorem A_pos {u σ : ℝ} (hu : u ≠ 0) : 0 < cosh u - cos σ := by
  have := Real.one_lt_cosh.mpr hu
  have := cos_le_one σ
  linarith

/-- The strip-chart pair term is the upper-half-plane tanh pair term `pairG` (for `u₀ ≠ u₁`). -/
theorem stripW_eq_pairG {u₀ φ₀ u₁ φ₁ : ℝ} (hu : u₀ ≠ u₁) :
    stripW u₀ φ₀ u₁ φ₁ = HyperbolicRings.Tanh.LargeN.pairG (exp u₀ * cos φ₀) (exp u₀ * sin φ₀)
      (exp u₁ * cos φ₁) (exp u₁ * sin φ₁) := by
  rw [HyperbolicRings.Tanh.LargeN.pairG_eq]
  simp only [HyperbolicRings.Tanh.LargeN.rowLq]
  have hd : u₀ - u₁ ≠ 0 := sub_ne_zero.mpr hu
  have hp := A_pos (σ := φ₀ + φ₁) hd
  have hm := A_pos (σ := φ₀ - φ₁) hd
  have hE : 0 < 2 * exp (u₀ + u₁) := by positivity
  have hch : 2 * exp (u₀ + u₁) * cosh (u₀ - u₁) = exp u₀ ^ 2 + exp u₁ ^ 2 := by
    rw [Real.cosh_eq, Real.exp_add, Real.exp_sub, Real.exp_neg, Real.exp_sub]
    field_simp
  have e1 : (exp u₀ * cos φ₀ - exp u₁ * cos φ₁) ^ 2 + (exp u₀ * sin φ₀ - exp u₁ * sin φ₁) ^ 2
      = 2 * exp (u₀ + u₁) * (cosh (u₀ - u₁) - cos (φ₀ - φ₁)) := by
    rw [mul_sub, hch, cos_sub, Real.exp_add]
    have := sin_sq_add_cos_sq φ₀; have := sin_sq_add_cos_sq φ₁
    linear_combination (exp u₀ ^ 2) * ‹sin φ₀ ^ 2 + cos φ₀ ^ 2 = 1› +
      (exp u₁ ^ 2) * ‹sin φ₁ ^ 2 + cos φ₁ ^ 2 = 1›
  have e2 : (exp u₀ * cos φ₀ - exp u₁ * cos φ₁) ^ 2 + (exp u₀ * sin φ₀ + exp u₁ * sin φ₁) ^ 2
      = 2 * exp (u₀ + u₁) * (cosh (u₀ - u₁) - cos (φ₀ + φ₁)) := by
    rw [mul_sub, hch, cos_add, Real.exp_add]
    have := sin_sq_add_cos_sq φ₀; have := sin_sq_add_cos_sq φ₁
    linear_combination (exp u₀ ^ 2) * ‹sin φ₀ ^ 2 + cos φ₀ ^ 2 = 1› +
      (exp u₁ ^ 2) * ‹sin φ₁ ^ 2 + cos φ₁ ^ 2 = 1›
  rw [e1, e2, Real.log_mul hE.ne' hm.ne', Real.log_mul hE.ne' hp.ne', stripW]
  ring

/-! ## One-variable derivative helpers -/

theorem hasDerivAt_logA {U S : ℝ → ℝ} {U' S' t : ℝ} (hU : HasDerivAt U U' t) (hS : HasDerivAt S S' t)
    (h : cosh (U t) - cos (S t) ≠ 0) :
    HasDerivAt (fun x => log (cosh (U x) - cos (S x)))
      ((sinh (U t) * U' + sin (S t) * S') / (cosh (U t) - cos (S t))) t := by
  have hc : HasDerivAt (fun x => cosh (U x)) (sinh (U t) * U') t := (hasDerivAt_cosh (U t)).comp t hU
  have hs : HasDerivAt (fun x => cos (S x)) (-sin (S t) * S') t := (hasDerivAt_cos (S t)).comp t hS
  have := (hc.fun_sub hs).log h
  convert this using 1
  ring

theorem hasDerivAt_quotA {U S : ℝ → ℝ} {U' S' t : ℝ} {N : ℝ → ℝ} {N' : ℝ} (hN : HasDerivAt N N' t)
    (hU : HasDerivAt U U' t) (hS : HasDerivAt S S' t) (h : cosh (U t) - cos (S t) ≠ 0) :
    HasDerivAt (fun x => N x / (cosh (U x) - cos (S x)))
      ((N' * (cosh (U t) - cos (S t)) - N t * (sinh (U t) * U' + sin (S t) * S'))
        / (cosh (U t) - cos (S t)) ^ 2) t := by
  have hc : HasDerivAt (fun x => cosh (U x)) (sinh (U t) * U') t := (hasDerivAt_cosh (U t)).comp t hU
  have hs : HasDerivAt (fun x => cos (S x)) (-sin (S t) * S') t := (hasDerivAt_cos (S t)).comp t hS
  have := hN.fun_div (hc.fun_sub hs) h
  convert this using 1
  ring

/-! ## First derivatives as functions -/

/-- `∂_{φ₀} W` at `(u₀, φ, u₁, φ₁)`. -/
def dWφ₀ (u₀ φ u₁ φ₁ : ℝ) : ℝ :=
  (sin (φ + φ₁) / (cosh (u₀ - u₁) - cos (φ + φ₁)) - sin (φ - φ₁) / (cosh (u₀ - u₁) - cos (φ - φ₁))) / 2

/-- `∂_{u₀} W` at `(u, φ₀, u₁, φ₁)`. -/
def dWu₀ (u φ₀ u₁ φ₁ : ℝ) : ℝ :=
  (sinh (u - u₁) / (cosh (u - u₁) - cos (φ₀ + φ₁)) - sinh (u - u₁) / (cosh (u - u₁) - cos (φ₀ - φ₁))) / 2

theorem hasDerivAt_stripW_φ₀ {u₀ φ u₁ φ₁ : ℝ} (h1 : cosh (u₀ - u₁) - cos (φ + φ₁) ≠ 0)
    (h2 : cosh (u₀ - u₁) - cos (φ - φ₁) ≠ 0) :
    HasDerivAt (fun x => stripW u₀ x u₁ φ₁) (dWφ₀ u₀ φ u₁ φ₁) φ := by
  have hp := hasDerivAt_logA (hasDerivAt_const φ (u₀ - u₁)) ((hasDerivAt_id' φ).add_const φ₁) h1
  have hm := hasDerivAt_logA (hasDerivAt_const φ (u₀ - u₁)) ((hasDerivAt_id' φ).sub_const φ₁) h2
  have := (hp.sub hm).div_const 2
  convert this using 1
  · funext x; simp [stripW]
  · simp [dWφ₀]

theorem hasDerivAt_stripW_u₀ {u φ₀ u₁ φ₁ : ℝ} (h1 : cosh (u - u₁) - cos (φ₀ + φ₁) ≠ 0)
    (h2 : cosh (u - u₁) - cos (φ₀ - φ₁) ≠ 0) :
    HasDerivAt (fun x => stripW x φ₀ u₁ φ₁) (dWu₀ u φ₀ u₁ φ₁) u := by
  have hp := hasDerivAt_logA ((hasDerivAt_id' u).sub_const u₁) (hasDerivAt_const u (φ₀ + φ₁)) h1
  have hm := hasDerivAt_logA ((hasDerivAt_id' u).sub_const u₁) (hasDerivAt_const u (φ₀ - φ₁)) h2
  have := (hp.sub hm).div_const 2
  convert this using 1
  · funext x; simp [stripW]
  · simp [dWu₀]

theorem deriv_stripW_φ₀ {u₀ φ u₁ φ₁ : ℝ} (h : u₀ - u₁ ≠ 0) :
    deriv (fun x => stripW u₀ x u₁ φ₁) φ = dWφ₀ u₀ φ u₁ φ₁ :=
  (hasDerivAt_stripW_φ₀ (A_pos h).ne' (A_pos h).ne').deriv

theorem deriv_stripW_u₀ {u φ₀ u₁ φ₁ : ℝ} (h : u - u₁ ≠ 0) :
    deriv (fun x => stripW x φ₀ u₁ φ₁) u = dWu₀ u φ₀ u₁ φ₁ :=
  (hasDerivAt_stripW_u₀ (A_pos h).ne' (A_pos h).ne').deriv

/-! ## Second partial derivatives at the row pair `(0, α, b, α)` -/

/-- `δφ₀`-coefficient in `u̇₀`: `∂_{φ₀}(sin²φ₀ ∂_{φ₀} W)`. -/
def onB (α b : ℝ) : ℝ := deriv (fun φ => sin φ ^ 2 * deriv (fun φ' => stripW 0 φ' b α) φ) α
/-- `δφ_k`-coefficient in `u̇₀`: `sin²α ∂_{φ_k}∂_{φ₀} W`. -/
def cpB (α b : ℝ) : ℝ := sin α ^ 2 * deriv (fun φ₁ => deriv (fun φ => stripW 0 φ b φ₁) α) α
/-- `δu₀`-coefficient in `φ̇₀`: `-sin²α ∂²_{u₀} W`. -/
def onC (α b : ℝ) : ℝ := -(sin α ^ 2) * deriv (fun u => deriv (fun u' => stripW u' α b α) u) 0
/-- `δu_k`-coefficient in `φ̇₀`: `-sin²α ∂_{u_k}∂_{u₀} W`. -/
def cpC (α b : ℝ) : ℝ := -(sin α ^ 2) * deriv (fun u₁ => deriv (fun u => stripW u α u₁ α) 0) b
/-- `δu₀`-coefficient in `u̇₀`: `sin²α ∂_{u₀}∂_{φ₀} W`. -/
def onU (α b : ℝ) : ℝ := sin α ^ 2 * deriv (fun u => deriv (fun φ => stripW u φ b α) α) 0
/-- `δu_k`-coefficient in `u̇₀`: `sin²α ∂_{u_k}∂_{φ₀} W`. -/
def cpU (α b : ℝ) : ℝ := sin α ^ 2 * deriv (fun u₁ => deriv (fun φ => stripW 0 φ u₁ α) α) b
/-- `δφ₀`-coefficient in `φ̇₀`: `-∂_{φ₀}(sin²φ₀ ∂_{u₀} W)`. -/
def onP (α b : ℝ) : ℝ := -deriv (fun φ => sin φ ^ 2 * deriv (fun u => stripW u φ b α) 0) α
/-- `δφ_k`-coefficient in `φ̇₀`: `-sin²α ∂_{φ_k}∂_{u₀} W`. -/
def cpP (α b : ℝ) : ℝ := -(sin α ^ 2) * deriv (fun φ₁ => deriv (fun u => stripW u α b φ₁) 0) α

/-- The odd pair quantity `sin²α sin 2α sinh b / (2 (cosh b - cos 2α)²)`. -/
def oddW (α b : ℝ) : ℝ := sin α ^ 2 * sin (2 * α) * sinh b / (2 * (cosh b - cos (2 * α)) ^ 2)

section values
variable {α b : ℝ} (hb : b ≠ 0)
include hb

theorem hb' : (0 : ℝ) - b ≠ 0 := by simpa using hb

theorem Dp_pos : 0 < cosh b - cos (2 * α) := A_pos hb
theorem Dm_pos : 0 < cosh b - 1 := by have := Real.one_lt_cosh.mpr hb; linarith

theorem onB_val : onB α b = 2 * sin α * cos α * (sin (2 * α) / (cosh b - cos (2 * α)) / 2)
    + sin α ^ 2 * (((cos (2 * α) * (cosh b - cos (2 * α)) - sin (2 * α) ^ 2) / (cosh b - cos (2 * α)) ^ 2
      - 1 / (cosh b - 1)) / 2) := by
  have hD := (Dp_pos (α := α) hb).ne'
  have hM := (Dm_pos hb).ne'
  unfold onB
  have e : (fun φ => sin φ ^ 2 * deriv (fun φ' => stripW 0 φ' b α) φ)
      = fun φ => sin φ ^ 2 * dWφ₀ 0 φ b α := by
    funext φ; rw [deriv_stripW_φ₀ (hb' hb)]
  rw [e]
  have hs2 : HasDerivAt (fun φ => sin φ ^ 2) (2 * sin α * cos α) α := by
    have := (hasDerivAt_sin α).pow 2; convert this using 1; simp
  have h0 : cosh ((0 : ℝ) - b) = cosh b := by simp
  have hp := hasDerivAt_quotA (N := fun φ => sin (φ + α)) (U := fun _ => (0:ℝ) - b) (S := fun φ => φ + α)
    (((hasDerivAt_id' α).add_const α).sin) (hasDerivAt_const α _) ((hasDerivAt_id' α).add_const α)
    (by rw [h0, ← two_mul]; exact hD)
  have hm := hasDerivAt_quotA (N := fun φ => sin (φ - α)) (U := fun _ => (0:ℝ) - b) (S := fun φ => φ - α)
    (((hasDerivAt_id' α).sub_const α).sin) (hasDerivAt_const α _) ((hasDerivAt_id' α).sub_const α)
    (by simp; exact hM)
  have hW : HasDerivAt (fun φ => dWφ₀ 0 φ b α) _ α := (hp.sub hm).div_const 2
  have hT : HasDerivAt (fun φ => sin φ ^ 2 * dWφ₀ 0 φ b α) _ α := hs2.mul hW
  rw [hT.deriv]
  simp only [dWφ₀, h0, sub_self, sin_zero, cos_zero, ← two_mul, zero_mul, mul_one, sub_zero, zero_div]
  field_simp
  ring

theorem cpB_val : cpB α b = sin α ^ 2 * (((cos (2 * α) * (cosh b - cos (2 * α)) - sin (2 * α) ^ 2)
      / (cosh b - cos (2 * α)) ^ 2 + 1 / (cosh b - 1)) / 2) := by
  have hD := (Dp_pos (α := α) hb).ne'
  have hM := (Dm_pos hb).ne'
  unfold cpB
  have e : (fun φ₁ => deriv (fun φ => stripW 0 φ b φ₁) α) = fun φ₁ => dWφ₀ 0 α b φ₁ := by
    funext φ₁; rw [deriv_stripW_φ₀ (hb' hb)]
  rw [e]
  have h0 : cosh ((0 : ℝ) - b) = cosh b := by simp
  have hp := hasDerivAt_quotA (N := fun φ₁ => sin (α + φ₁)) (U := fun _ => (0:ℝ) - b)
    (S := fun φ₁ => α + φ₁) (((hasDerivAt_id' α).const_add α).sin) (hasDerivAt_const α _)
    ((hasDerivAt_id' α).const_add α) (by rw [h0, ← two_mul]; exact hD)
  have hm := hasDerivAt_quotA (N := fun φ₁ => sin (α - φ₁)) (U := fun _ => (0:ℝ) - b)
    (S := fun φ₁ => α - φ₁) (((hasDerivAt_id' α).const_sub α).sin) (hasDerivAt_const α _)
    ((hasDerivAt_id' α).const_sub α) (by simp; exact hM)
  have hW : HasDerivAt (fun φ₁ => dWφ₀ 0 α b φ₁) _ α := (hp.sub hm).div_const 2
  rw [hW.deriv]
  simp only [h0, sub_self, sin_zero, cos_zero, ← two_mul, zero_mul, mul_one, sub_zero, zero_div]
  field_simp
  try ring

theorem onC_val : onC α b = -(sin α ^ 2) * (((cosh b * (cosh b - cos (2 * α)) - sinh b ^ 2)
      / (cosh b - cos (2 * α)) ^ 2 - (cosh b * (cosh b - 1) - sinh b ^ 2) / (cosh b - 1) ^ 2) / 2) := by
  have hD := (Dp_pos (α := α) hb).ne'
  have hM := (Dm_pos hb).ne'
  unfold onC
  have e : (fun u => deriv (fun u' => stripW u' α b α) u) =ᶠ[𝓝 0] fun u => dWu₀ u α b α := by
    have hopen : {u : ℝ | u - b ≠ 0} ∈ 𝓝 (0 : ℝ) :=
      (isOpen_ne_fun (continuous_id.sub continuous_const) continuous_const).mem_nhds (by simpa using hb)
    filter_upwards [hopen] with u hu
    exact deriv_stripW_u₀ hu
  rw [e.deriv_eq]
  have hp := hasDerivAt_quotA (N := fun u => sinh (u - b)) (U := fun u => u - b) (S := fun _ => α + α)
    (((hasDerivAt_id' (0:ℝ)).sub_const b).sinh) ((hasDerivAt_id' (0:ℝ)).sub_const b) (hasDerivAt_const _ _)
    (by simp only [zero_sub, cosh_neg, ← two_mul]; exact hD)
  have hm := hasDerivAt_quotA (N := fun u => sinh (u - b)) (U := fun u => u - b) (S := fun _ => α - α)
    (((hasDerivAt_id' (0:ℝ)).sub_const b).sinh) ((hasDerivAt_id' (0:ℝ)).sub_const b) (hasDerivAt_const _ _)
    (by simp only [zero_sub, cosh_neg, sub_self, cos_zero]; exact hM)
  have hW : HasDerivAt (fun u => dWu₀ u α b α) _ 0 := (hp.sub hm).div_const 2
  rw [hW.deriv]
  simp only [zero_sub, cosh_neg, sinh_neg, sub_self, cos_zero, sin_zero, ← two_mul, mul_zero, add_zero,
    mul_one, neg_mul, neg_neg]
  ring

theorem cpC_val : cpC α b = -onC α b := by
  have hD := (Dp_pos (α := α) hb).ne'
  have hM := (Dm_pos hb).ne'
  rw [onC_val hb]
  unfold cpC
  have e : (fun u₁ => deriv (fun u => stripW u α u₁ α) 0) =ᶠ[𝓝 b] fun u₁ => dWu₀ 0 α u₁ α := by
    have hopen : {u₁ : ℝ | (0:ℝ) - u₁ ≠ 0} ∈ 𝓝 b :=
      (isOpen_ne_fun (continuous_const.sub continuous_id) continuous_const).mem_nhds (by simpa using hb)
    filter_upwards [hopen] with u₁ hu
    exact deriv_stripW_u₀ hu
  rw [e.deriv_eq]
  have hU : HasDerivAt (fun u₁ : ℝ => (0:ℝ) - u₁) (-1) b := by
    simpa using (hasDerivAt_id' b).const_sub (0:ℝ)
  have hp := hasDerivAt_quotA (N := fun u₁ => sinh ((0:ℝ) - u₁)) (U := fun u₁ => (0:ℝ) - u₁)
    (S := fun _ => α + α) (hU.sinh) hU (hasDerivAt_const _ _)
    (by simp only [zero_sub, cosh_neg, ← two_mul]; exact hD)
  have hm := hasDerivAt_quotA (N := fun u₁ => sinh ((0:ℝ) - u₁)) (U := fun u₁ => (0:ℝ) - u₁)
    (S := fun _ => α - α) (hU.sinh) hU (hasDerivAt_const _ _)
    (by simp only [zero_sub, cosh_neg, sub_self, cos_zero]; exact hM)
  have hW : HasDerivAt (fun u₁ => dWu₀ 0 α u₁ α) _ b := (hp.sub hm).div_const 2
  rw [hW.deriv]
  simp only [zero_sub, cosh_neg, sinh_neg, sub_self, cos_zero, sin_zero, ← two_mul, mul_zero, add_zero,
    mul_one, neg_mul, neg_neg, mul_neg]
  ring

theorem onU_val : onU α b = oddW α b := by
  have hD := (Dp_pos (α := α) hb).ne'
  unfold onU oddW
  have e : (fun u => deriv (fun φ => stripW u φ b α) α) =ᶠ[𝓝 0]
      fun u => sin (α + α) / (cosh (u - b) - cos (α + α)) / 2 := by
    have hopen : {u : ℝ | u - b ≠ 0} ∈ 𝓝 (0 : ℝ) :=
      (isOpen_ne_fun (continuous_id.sub continuous_const) continuous_const).mem_nhds (by simpa using hb)
    filter_upwards [hopen] with u hu
    rw [deriv_stripW_φ₀ hu, dWφ₀]; simp
  rw [e.deriv_eq]
  have hp := hasDerivAt_quotA (N := fun _ => sin (α + α)) (U := fun u => u - b) (S := fun _ => α + α)
    (hasDerivAt_const _ _) ((hasDerivAt_id' (0:ℝ)).sub_const b) (hasDerivAt_const _ _)
    (by simp only [zero_sub, cosh_neg, ← two_mul]; exact hD)
  rw [(hp.div_const 2).deriv]
  simp only [zero_sub, cosh_neg, sinh_neg, ← two_mul, mul_zero, add_zero, mul_one, zero_mul]
  field_simp
  try ring

theorem cpU_val : cpU α b = -oddW α b := by
  have hD := (Dp_pos (α := α) hb).ne'
  unfold cpU oddW
  have e : (fun u₁ => deriv (fun φ => stripW 0 φ u₁ α) α) =ᶠ[𝓝 b]
      fun u₁ => sin (α + α) / (cosh ((0:ℝ) - u₁) - cos (α + α)) / 2 := by
    have hopen : {u₁ : ℝ | (0:ℝ) - u₁ ≠ 0} ∈ 𝓝 b :=
      (isOpen_ne_fun (continuous_const.sub continuous_id) continuous_const).mem_nhds (by simpa using hb)
    filter_upwards [hopen] with u₁ hu
    rw [deriv_stripW_φ₀ hu, dWφ₀]; simp
  rw [e.deriv_eq]
  have hU : HasDerivAt (fun u₁ : ℝ => (0:ℝ) - u₁) (-1) b := by
    simpa using (hasDerivAt_id' b).const_sub (0:ℝ)
  have hp := hasDerivAt_quotA (N := fun _ => sin (α + α)) (U := fun u₁ => (0:ℝ) - u₁) (S := fun _ => α + α)
    (hasDerivAt_const _ _) hU (hasDerivAt_const _ _)
    (by simp only [zero_sub, cosh_neg, ← two_mul]; exact hD)
  rw [(hp.div_const 2).deriv]
  simp only [zero_sub, cosh_neg, sinh_neg, ← two_mul, mul_zero, add_zero, mul_one, zero_mul]
  field_simp
  try ring

theorem onP_val : onP α b = sin α * cos α * sinh b * (1 / (cosh b - cos (2 * α)) - 1 / (cosh b - 1))
    - oddW α b := by
  have hD := (Dp_pos (α := α) hb).ne'
  have hM := (Dm_pos hb).ne'
  unfold onP oddW
  have e : (fun φ => sin φ ^ 2 * deriv (fun u => stripW u φ b α) 0)
      = fun φ => sin φ ^ 2 * dWu₀ 0 φ b α := by
    funext φ; rw [deriv_stripW_u₀ (hb' hb)]
  rw [e]
  have hs2 : HasDerivAt (fun φ => sin φ ^ 2) (2 * sin α * cos α) α := by
    have := (hasDerivAt_sin α).pow 2; convert this using 1; simp
  have h0 : cosh ((0 : ℝ) - b) = cosh b := by simp
  have hp := hasDerivAt_quotA (N := fun _ => sinh ((0:ℝ) - b)) (U := fun _ => (0:ℝ) - b)
    (S := fun φ => φ + α) (hasDerivAt_const _ _) (hasDerivAt_const α _) ((hasDerivAt_id' α).add_const α)
    (by rw [h0, ← two_mul]; exact hD)
  have hm := hasDerivAt_quotA (N := fun _ => sinh ((0:ℝ) - b)) (U := fun _ => (0:ℝ) - b)
    (S := fun φ => φ - α) (hasDerivAt_const _ _) (hasDerivAt_const α _) ((hasDerivAt_id' α).sub_const α)
    (by simp; exact hM)
  have hW : HasDerivAt (fun φ => dWu₀ 0 φ b α) _ α := (hp.sub hm).div_const 2
  have hT : HasDerivAt (fun φ => sin φ ^ 2 * dWu₀ 0 φ b α) _ α := hs2.mul hW
  rw [hT.deriv]
  simp only [dWu₀, h0, sub_self, sin_zero, cos_zero, ← two_mul, zero_mul, mul_one, sub_zero, zero_div,
    zero_sub, sinh_neg, cosh_neg, mul_zero]
  field_simp
  try ring

theorem cpP_val : cpP α b = -oddW α b := by
  have hD := (Dp_pos (α := α) hb).ne'
  have hM := (Dm_pos hb).ne'
  unfold cpP oddW
  have e : (fun φ₁ => deriv (fun u => stripW u α b φ₁) 0) = fun φ₁ => dWu₀ 0 α b φ₁ := by
    funext φ₁; rw [deriv_stripW_u₀ (hb' hb)]
  rw [e]
  have h0 : cosh ((0 : ℝ) - b) = cosh b := by simp
  have hp := hasDerivAt_quotA (N := fun _ => sinh ((0:ℝ) - b)) (U := fun _ => (0:ℝ) - b)
    (S := fun φ₁ => α + φ₁) (hasDerivAt_const _ _) (hasDerivAt_const α _) ((hasDerivAt_id' α).const_add α)
    (by rw [h0, ← two_mul]; exact hD)
  have hm := hasDerivAt_quotA (N := fun _ => sinh ((0:ℝ) - b)) (U := fun _ => (0:ℝ) - b)
    (S := fun φ₁ => α - φ₁) (hasDerivAt_const _ _) (hasDerivAt_const α _) ((hasDerivAt_id' α).const_sub α)
    (by simp; exact hM)
  have hW : HasDerivAt (fun φ₁ => dWu₀ 0 α b φ₁) _ α := (hp.sub hm).div_const 2
  rw [hW.deriv]
  simp only [h0, sub_self, sin_zero, cos_zero, ← two_mul, zero_mul, mul_one, sub_zero, zero_div,
    zero_sub, sinh_neg, cosh_neg, mul_zero]
  field_simp
  try ring

end values

/-! ## Identification with the pair functions `B0`, `B1`, `C1` (`K = cos²α`, `c = cosh b`) -/

section ident
variable {α b : ℝ} (hb : b ≠ 0)
include hb

theorem Dd_cos : Dd (cos α ^ 2) (cosh b) = cosh b - cos (2 * α) := by
  unfold Dd; rw [cos_two_mul]; ring

theorem onB_eq_B0 : onB α b = B0 (cos α ^ 2) (cosh b) := by
  have hD := (Dp_pos (α := α) hb).ne'
  have hM := (Dm_pos hb).ne'
  rw [onB_val hb, B0, Dd_cos hb]
  have hs : sin α ^ 2 = 1 - cos α ^ 2 := by rw [← sin_sq_add_cos_sq α]; ring
  simp only [sin_two_mul, cos_two_mul] at hD ⊢
  field_simp
  rw [hs]; ring

theorem cpB_eq_B1 : cpB α b = B1 (cos α ^ 2) (cosh b) := by
  have hD := (Dp_pos (α := α) hb).ne'
  have hM := (Dm_pos hb).ne'
  rw [cpB_val hb, B1, Dd_cos hb]
  have hs : sin α ^ 2 = 1 - cos α ^ 2 := by rw [← sin_sq_add_cos_sq α]; ring
  simp only [sin_two_mul, cos_two_mul] at hD ⊢
  field_simp
  rw [hs]; ring

theorem onC_eq_C1 : onC α b = C1 (cos α ^ 2) (cosh b) := by
  have hD := (Dp_pos (α := α) hb).ne'
  have hM := (Dm_pos hb).ne'
  rw [onC_val hb, C1, Dd_cos hb]
  have hs : sin α ^ 2 = 1 - cos α ^ 2 := by rw [← sin_sq_add_cos_sq α]; ring
  have hsh : sinh b ^ 2 = cosh b ^ 2 - 1 := by rw [← cosh_sq_sub_sinh_sq b]; ring
  simp only [cos_two_mul] at hD ⊢
  rw [hsh]
  field_simp
  rw [hs]; ring

theorem cpC_eq_C1 : cpC α b = -C1 (cos α ^ 2) (cosh b) := by
  rw [cpC_val hb, onC_eq_C1 hb]

end ident

end HyperbolicRings.Rows
