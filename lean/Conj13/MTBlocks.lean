/-
New module for paper 01-conjecture-13, adapted from
havelock-vortex-rings@2cc1ee5:lean/Havelock/Sinh/Hessian.lean (the sinh model on the Poincaré disk). The pair-term
calculus (`hasD2_pairS`, `pairD1_zero`, `qForm_pair`) is copied from there unchanged in substance; the model, the
one-body terms, the criticality and the Fourier blocks are rewritten for Montaldi–Tokieda's family.

# Montaldi–Tokieda family: the ring is critical, and the Hessian is diagonal on Fourier modes (paper Prop. 2.3)

`n` unit vortices at `z_j = w^j e^{s_j + iθ_j}` (`w = e^{2πi/n}`, ring radius `r₀ = 1`, so `b = λ`), with paper
eq. (2.1):
`H = −Σ_{j<k} log(|z_j−z_k|²/(σ_jσ_k)) = 2 Σ_{j<k} (−log|z_j − z_k|) + (n−1) Σ_k log(1 + b|z_k|²)`,
`J₃ = Σ_k |z_k|²/(1 + b|z_k|²)`, `F = H − ωJ₃`. One formula for the sphere (`b > 0`), the plane (`b = 0`) and the
hyperbolic plane (`−1 < b < 0`).

Derivatives are taken along lines `t ↦ F(ts, tθ)` through the ring; the Hessian quadratic form is
`d²/dt² F(ts,tθ)|₀` and the entries are obtained by polarisation (as in the source module).

Main results (all `b > −1`):
* `mt_grad_formula`, `mt_ring_critical`, `mt_ring_critical_iff`: the ring is critical exactly for
  `ω = ω₀ = −(n−1)(1−b)(1+b)/2`.
* `mtD_omega`: the one-body diagonal at `ω₀` is `C₁ = 2(n−1)(1+b²)/(1+b)²`.
* `mt_blocks_eigen`: on `v_b = w^{mb}` (`0 ≤ m ≤ n`), `∂²F/∂s∂s` acts by `a_m = C₁ − m(n−m)`, `∂²F/∂θ∂θ` by
  `b_m = m(n−m)`, and the mixed blocks vanish.
* `mt_blocks_hermitian`: no coupling between different Fourier modes.
-/
import Conj13.Ring.BlocksFourier

noncomputable section

namespace Conj13.MTBlocks

open Conj13.Ring
open Filter Topology
open scoped ComplexConjugate

/-! ## The model -/

/-- Paper eq. (2.1) at ring radius `1`: `H = 2Σ_{j<k}(−log|z_j−z_k|) + (n−1)Σ_k log(1+b|z_k|²)`. -/
def mtH (N : ℕ) (b : ℝ) (s θ : Fin N → ℝ) : ℝ :=
  2 * (∑ j : Fin N, ∑ k : Fin N,
      if j < k then -Real.log ‖ringZ N 1 s θ j - ringZ N 1 s θ k‖ else 0)
    + ((N : ℝ) - 1) * ∑ k : Fin N, Real.log (1 + b * ‖ringZ N 1 s θ k‖ ^ 2)

/-- `J₃ = Σ_k |z_k|²/(1 + b|z_k|²)`. -/
def mtJ3 (N : ℕ) (b : ℝ) (s θ : Fin N → ℝ) : ℝ :=
  ∑ k : Fin N, ‖ringZ N 1 s θ k‖ ^ 2 / (1 + b * ‖ringZ N 1 s θ k‖ ^ 2)

/-- `F = H − ωJ₃`. -/
def mtF (N : ℕ) (b ω : ℝ) (s θ : Fin N → ℝ) : ℝ := mtH N b s θ - ω * mtJ3 N b s θ

/-- `ω₀ = −(n−1)(1−b)(1+b)/2`. -/
def mtOmega (N : ℕ) (b : ℝ) : ℝ := -(((N : ℝ) - 1) * (1 - b) * (1 + b)) / 2

/-- `C₁ = 2(n−1)(1+b²)/(1+b)²`. -/
def mtC1 (N : ℕ) (b : ℝ) : ℝ := 2 * ((N : ℝ) - 1) * (1 + b ^ 2) / (1 + b) ^ 2

/-- `a_m = C₁ − m(n−m)`. -/
def mtA (N m : ℕ) (b : ℝ) : ℝ := mtC1 N b - (m : ℝ) * ((N : ℝ) - m)

/-- `b_m = m(n−m)`. -/
def mtB (N m : ℕ) : ℝ := (m : ℝ) * ((N : ℝ) - m)

theorem rho_zero (ζ : ℂ) : rho 0 ζ = 0 := by simp [rho]

theorem rho1_zero (ζ : ℂ) : rho1 0 ζ = 0 := by simp [rho1]

/-! ## One-body terms along a line -/

theorem hasDerivAt_e (σ t : ℝ) :
    HasDerivAt (fun t => Real.exp (2 * t * σ)) (2 * σ * Real.exp (2 * t * σ)) t := by
  have h2 : HasDerivAt (fun t => 2 * t * σ) (2 * σ) t := by
    simpa using ((hasDerivAt_id t).const_mul 2).mul_const σ
  have := h2.exp
  convert this using 1; ring

theorem ev_pos (b σ : ℝ) (hb : 0 < 1 + b) :
    ∀ᶠ t in 𝓝 (0 : ℝ), 0 < 1 + b * Real.exp (2 * t * σ) := by
  have hc : ContinuousAt (fun t => 1 + b * Real.exp (2 * t * σ)) 0 :=
    (((hasDerivAt_e σ 0).const_mul b).const_add 1).continuousAt
  exact hc.eventually (lt_mem_nhds (by simpa using hb))

/-- The one-body term `log(1 + b e^{2tσ})`: second derivative `4σ²b/(1+b)²` at `0`. -/
theorem hasD2_logS (b σ : ℝ) (hb : 0 < 1 + b) :
    HasD2 (fun t => Real.log (1 + b * Real.exp (2 * t * σ)))
      (fun t => 2 * σ * b * Real.exp (2 * t * σ) / (1 + b * Real.exp (2 * t * σ)))
      (4 * σ ^ 2 * b / (1 + b) ^ 2) := by
  have he := hasDerivAt_e σ
  refine ⟨(ev_pos b σ hb).mono fun t ht => ?_, ?_⟩
  · have := (((he t).const_mul b).const_add 1).log ht.ne'
    convert this using 1; ring
  · have h0 : 1 + b * Real.exp (2 * 0 * σ) ≠ 0 := by simp; linarith
    have := ((he 0).const_mul (2 * σ * b)).div (((he 0).const_mul b).const_add 1) h0
    convert this using 1
    simp only [mul_zero, zero_mul, Real.exp_zero, mul_one]
    have : (1 : ℝ) + b ≠ 0 := hb.ne'
    field_simp
    ring

/-- The `J₃` term `e^{2tσ}/(1 + b e^{2tσ})`: second derivative `4σ²(1−b)/(1+b)³` at `0`. -/
theorem hasD2_J3 (b σ : ℝ) (hb : 0 < 1 + b) :
    HasD2 (fun t => Real.exp (2 * t * σ) / (1 + b * Real.exp (2 * t * σ)))
      (fun t => 2 * σ * Real.exp (2 * t * σ) / (1 + b * Real.exp (2 * t * σ)) ^ 2)
      (4 * σ ^ 2 * (1 - b) / (1 + b) ^ 3) := by
  have he := hasDerivAt_e σ
  refine ⟨(ev_pos b σ hb).mono fun t ht => ?_, ?_⟩
  · have := (he t).div (((he t).const_mul b).const_add 1) ht.ne'
    convert this using 1
    field_simp
    ring
  · have h0 : (1 + b * Real.exp (2 * 0 * σ)) ^ 2 ≠ 0 := by simp; exact hb.ne'
    have := ((he 0).const_mul (2 * σ)).div ((((he 0).const_mul b).const_add 1).pow 2) h0
    convert this using 1
    simp only [mul_zero, zero_mul, Real.exp_zero, mul_one, Pi.pow_apply, Nat.cast_ofNat, pow_one,
      show (2 : ℕ) - 1 = 1 from rfl]
    have : (1 : ℝ) + b ≠ 0 := hb.ne'
    field_simp
    ring

/-! ## The pair term (copied from the sinh development) -/

/-- First derivative of the pair term `−ln|z_j − z_k|` along the line. -/
def pairD1 (N : ℕ) (ξ : ℝ) (s θ : Fin N → ℝ) (j k : Fin N) (t : ℝ) : ℝ :=
  -((expLin ((Real.sqrt ξ : ℂ) * ringW N ^ (j : ℕ) * epsC s θ j) (epsC s θ j) t
        - expLin ((Real.sqrt ξ : ℂ) * ringW N ^ (k : ℕ) * epsC s θ k) (epsC s θ k) t)
      / (expLin ((Real.sqrt ξ : ℂ) * ringW N ^ (j : ℕ)) (epsC s θ j) t
        - expLin ((Real.sqrt ξ : ℂ) * ringW N ^ (k : ℕ)) (epsC s θ k) t)).re

/-- The pair term: its second derivative is `qPair N 0` (geometry-independent). -/
theorem hasD2_pairS {N : ℕ} (hN : 0 < N) {ξ : ℝ} (h0 : 0 < ξ) (s θ : Fin N → ℝ)
    {j k : Fin N} (hjk : j ≠ k) :
    HasD2 (fun t => -Real.log ‖ringZ N ξ (t • s) (t • θ) j - ringZ N ξ (t • s) (t • θ) k‖)
      (pairD1 N ξ s θ j k) (qPair N 0 s θ j k) := by
  have hsq : ((Real.sqrt ξ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.mpr h0).ne'
  have hw := ringW_pow_ne hN hjk
  have hab : (Real.sqrt ξ : ℂ) * ringW N ^ (j : ℕ) ≠ (Real.sqrt ξ : ℂ) * ringW N ^ (k : ℕ) := by
    intro h; exact hw (mul_left_cancel₀ hsq h)
  have HP := hasD2_pairLog _ _ (epsC s θ j) (epsC s θ k) hab
  have H := HP.congr_f (g := fun t =>
      -Real.log ‖ringZ N ξ (t • s) (t • θ) j - ringZ N ξ (t • s) (t • θ) k‖)
    (fun t => by rw [ringZ_line, ringZ_line])
  refine H.congr_c ?_
  set a := (Real.sqrt ξ : ℂ) * ringW N ^ (j : ℕ)
  set b := (Real.sqrt ξ : ℂ) * ringW N ^ (k : ℕ)
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have e1 : (a * epsC s θ j * epsC s θ j * (a - b) - b * epsC s θ k * epsC s θ k * (a - b)
      - (a * epsC s θ j - b * epsC s θ k) * (a * epsC s θ j - b * epsC s θ k)) / (a - b) ^ 2
      = (-(a * b) / (a - b) ^ 2) * (epsC s θ j - epsC s θ k) ^ 2 := by
    field_simp; ring
  have e2 : -(a * b) / (a - b) ^ 2 = ((alphaF (zeta N j k) : ℝ) : ℂ) := by
    have := alpha_eq j k hw _ hsq
    simpa [a, b, mul_assoc, mul_comm, mul_left_comm] using this
  rw [e1, e2, Complex.re_ofReal_mul, re_sq_sub]
  unfold qPair
  simp only [rho_zero, Complex.zero_re, Complex.zero_im]
  ring

theorem pairD1_zero {N : ℕ} {ξ : ℝ} (h0 : 0 < ξ) (s θ : Fin N → ℝ) (j k : Fin N) :
    pairD1 N ξ s θ j k 0 = lPair N 0 s θ j k := by
  have hsq : ((Real.sqrt ξ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.mpr h0).ne'
  unfold pairD1 lPair
  simp only [expLin_zero, rho1_zero, zero_mul, Complex.zero_re, sub_zero]
  rw [show (Real.sqrt ξ : ℂ) * ringW N ^ (j : ℕ) * epsC s θ j
      - (Real.sqrt ξ : ℂ) * ringW N ^ (k : ℕ) * epsC s θ k
      = (Real.sqrt ξ : ℂ) * (ringW N ^ (j : ℕ) * epsC s θ j - ringW N ^ (k : ℕ) * epsC s θ k)
      by ring,
    show (Real.sqrt ξ : ℂ) * ringW N ^ (j : ℕ) - (Real.sqrt ξ : ℂ) * ringW N ^ (k : ℕ)
      = (Real.sqrt ξ : ℂ) * (ringW N ^ (j : ℕ) - ringW N ^ (k : ℕ)) by ring,
    mul_div_mul_left _ _ hsq]

/-! ## First and second derivative of `F` along a line -/

theorem hasD2_mtF {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : -1 < b) (ω : ℝ) (s θ : Fin N → ℝ) :
    ∃ f1 : ℝ → ℝ, HasD2 (fun t => mtF N b ω (t • s) (t • θ)) f1
        (2 * ∑ j : Fin N, ∑ k : Fin N, (if j < k then qPair N 0 s θ j k else 0)
          + ((N : ℝ) - 1) * ∑ k : Fin N, 4 * s k ^ 2 * b / (1 + b) ^ 2
          - ω * ∑ k : Fin N, 4 * s k ^ 2 * (1 - b) / (1 + b) ^ 3)
      ∧ f1 0 = 2 * ∑ j : Fin N, ∑ k : Fin N, (if j < k then lPair N 0 s θ j k else 0)
          + ((N : ℝ) - 1) * ∑ k : Fin N, 2 * s k * b / (1 + b)
          - ω * ∑ k : Fin N, 2 * s k / (1 + b) ^ 2 := by
  have hb1 : 0 < 1 + b := by linarith
  have HP := (HasD2.sum (Finset.univ : Finset (Fin N)) (fun j _ =>
    HasD2.sum (Finset.univ : Finset (Fin N)) (fun k _ =>
      HasD2.ite (j < k) (fun hjk => hasD2_pairS hN one_pos s θ (ne_of_lt hjk))))).const_mul 2
  have HW := (HasD2.sum (Finset.univ : Finset (Fin N))
    (fun k _ => hasD2_logS b (s k) hb1)).const_mul ((N : ℝ) - 1)
  have HJ := (HasD2.sum (Finset.univ : Finset (Fin N)) (fun k _ => hasD2_J3 b (s k) hb1)).const_mul ω
  have H := (HP.add HW).sub HJ
  refine ⟨_, (H.congr_f (fun t => ?_)).congr_c ?_, ?_⟩
  · unfold mtF mtH mtJ3
    simp only [norm_ringZ_sq_line hN zero_le_one, one_mul]
  · rfl
  · simp only [mul_zero, zero_mul, Real.exp_zero, mul_one]
    congr 2
    congr 1; refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hjk
    exacts [pairD1_zero one_pos s θ j k, rfl]

/-! ## Criticality -/

/-- The directional derivative of `F` at the ring along `(s, θ)`. -/
theorem mt_grad_formula {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : -1 < b) (ω : ℝ) (s θ : Fin N → ℝ) :
    deriv (fun t : ℝ => mtF N b ω (t • s) (t • θ)) 0
      = -(((N : ℝ) - 1) * (1 - b) / (1 + b) + 2 * ω / (1 + b) ^ 2) * ∑ j : Fin N, s j := by
  obtain ⟨f1, H, hf⟩ := hasD2_mtF hN hb ω s θ
  rw [H.deriv1, hf, sum_lPair hN (le_refl 0) zero_lt_one s θ, zero_pow hN.ne']
  have hb1 : (1 : ℝ) + b ≠ 0 := by linarith
  have e2 : ∑ k : Fin N, 2 * s k * b / (1 + b) = (2 * b / (1 + b)) * ∑ k : Fin N, s k := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
  have e3 : ∑ k : Fin N, 2 * s k / (1 + b) ^ 2 = (2 / (1 + b) ^ 2) * ∑ k : Fin N, s k := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
  rw [e2, e3]
  field_simp
  ring

/-- **The ring is a relative equilibrium**: with `ω = ω₀` the derivative of `F` at the ring along every line
is `0`. -/
theorem mt_ring_critical {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : -1 < b) (s θ : Fin N → ℝ) :
    deriv (fun t : ℝ => mtF N b (mtOmega N b) (t • s) (t • θ)) 0 = 0 := by
  rw [mt_grad_formula hN hb]
  have hb1 : (1 : ℝ) + b ≠ 0 := by linarith
  unfold mtOmega
  field_simp
  ring

/-- Uniqueness of `ω`. -/
theorem mt_ring_critical_iff {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : -1 < b) (ω : ℝ) :
    (∀ s θ : Fin N → ℝ, deriv (fun t : ℝ => mtF N b ω (t • s) (t • θ)) 0 = 0) ↔ ω = mtOmega N b := by
  have hb1 : (1 : ℝ) + b ≠ 0 := by linarith
  constructor
  · intro h
    have := h (fun _ => 1) 0
    rw [mt_grad_formula hN hb] at this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rcases mul_eq_zero.mp this with h' | h'
    · unfold mtOmega
      field_simp at h' ⊢
      linarith
    · exact absurd h' hN'
  · rintro rfl s θ
    exact mt_ring_critical hN hb s θ

/-! ## The Hessian -/

/-- The one-body diagonal: `(n−1)·4b/(1+b)² − ω·4(1−b)/(1+b)³`. -/
def mtD (N : ℕ) (b ω : ℝ) : ℝ :=
  ((N : ℝ) - 1) * (4 * b / (1 + b) ^ 2) - ω * (4 * (1 - b) / (1 + b) ^ 3)

/-- At `ω₀` the one-body diagonal is `C₁ = 2(n−1)(1+b²)/(1+b)²`. -/
theorem mtD_omega (N : ℕ) {b : ℝ} (hb : -1 < b) : mtD N b (mtOmega N b) = mtC1 N b := by
  have hb1 : (1 : ℝ) + b ≠ 0 := by linarith
  unfold mtD mtOmega mtC1
  field_simp
  ring

/-- `∂²F/∂s_a∂s_b` in closed form. -/
def mSS (N : ℕ) (b ω : ℝ) (a c : Fin N) : ℝ := 2 * hSS N 0 0 a c + if a = c then mtD N b ω else 0
/-- `∂²F/∂s_a∂θ_b` in closed form. -/
def mST (N : ℕ) (a c : Fin N) : ℝ := 2 * hST N 0 a c
/-- `∂²F/∂θ_a∂θ_b` in closed form. -/
def mTT (N : ℕ) (a c : Fin N) : ℝ := 2 * hTT N 0 a c

theorem mSS_symm (N : ℕ) (b ω : ℝ) (a c : Fin N) : mSS N b ω a c = mSS N b ω c a := by
  unfold mSS
  rw [hSS_symm N 0 0 a c]
  by_cases h : a = c
  · subst h; rfl
  · simp [h, Ne.symm h]

theorem mTT_symm (N : ℕ) (a c : Fin N) : mTT N a c = mTT N c a := by
  unfold mTT; rw [hTT_symm]

theorem hST_zero (N : ℕ) (a c : Fin N) : hST N 0 a c = 0 := by
  unfold hST gammaM
  simp [rho_zero]

theorem mST_zero (N : ℕ) (a c : Fin N) : mST N a c = 0 := by
  unfold mST; rw [hST_zero]; ring

/-- The Hessian quadratic form `d²/dt² F(ts,tθ)|_{t=0}`. -/
def mtHessQ (N : ℕ) (b ω : ℝ) (s θ : Fin N → ℝ) : ℝ :=
  deriv (deriv (fun t : ℝ => mtF N b ω (t • s) (t • θ))) 0

theorem qForm_pair (N : ℕ) (s θ : Fin N → ℝ) :
    qForm (hSS N 0 0) (hST N 0) (hTT N 0) s θ
      = ∑ j : Fin N, ∑ k : Fin N, (if j < k then qPair N 0 s θ j k else 0) := by
  simp_rw [qPair_eq]
  rw [sum_lt_add_swap (fun j k => R1 N 0 s θ j k + R2 N 0 s θ j k)]
  have hq : qForm (hSS N 0 0) (hST N 0) (hTT N 0) s θ = ∑ a : Fin N, ∑ b : Fin N,
      (s a * hSS N 0 0 a b * s b + 2 * (s a * hST N 0 a b * θ b) + θ a * hTT N 0 a b * θ b) := by
    unfold qForm bil
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [hq]
  simp_rw [row_eq]
  simp [Vj]

theorem bil_two {N : ℕ} (A : Fin N → Fin N → ℝ) (x y : Fin N → ℝ) :
    bil (fun a c => 2 * A a c) x y = 2 * bil A x y := by
  unfold bil
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- **The Hessian quadratic form in matrix form.** -/
theorem mtHessQ_eq {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : -1 < b) (ω : ℝ) (s θ : Fin N → ℝ) :
    mtHessQ N b ω s θ = qForm (mSS N b ω) (mST N) (mTT N) s θ := by
  obtain ⟨f1, H, _⟩ := hasD2_mtF hN hb ω s θ
  unfold mtHessQ
  rw [H.deriv2]
  have hbil : bil (mSS N b ω) s s = 2 * bil (hSS N 0 0) s s + ∑ a : Fin N, mtD N b ω * s a ^ 2 := by
    rw [← bil_two]
    unfold bil mSS
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  have hq : qForm (mSS N b ω) (mST N) (mTT N) s θ
      = 2 * qForm (hSS N 0 0) (hST N 0) (hTT N 0) s θ + ∑ a : Fin N, mtD N b ω * s a ^ 2 := by
    unfold qForm
    rw [hbil, show mST N = fun a c => 2 * hST N 0 a c from rfl,
      show mTT N = fun a c => 2 * hTT N 0 a c from rfl, bil_two, bil_two]
    ring
  rw [hq, qForm_pair]
  have hD : ((N : ℝ) - 1) * ∑ k : Fin N, 4 * s k ^ 2 * b / (1 + b) ^ 2
      - ω * ∑ k : Fin N, 4 * s k ^ 2 * (1 - b) / (1 + b) ^ 3
      = ∑ a : Fin N, mtD N b ω * s a ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold mtD; ring
  rw [← hD]
  ring

/-! ## Polarisation: the Hessian entries -/

/-- Polarisation of `mtHessQ`. -/
def mtHessB (N : ℕ) (b ω : ℝ) (s θ s' θ' : Fin N → ℝ) : ℝ :=
  (mtHessQ N b ω (s + s') (θ + θ') - mtHessQ N b ω (s - s') (θ - θ')) / 4

/-- `∂²F/∂s_a∂s_c` at the ring. -/
def mtHessSS (N : ℕ) (b ω : ℝ) (a c : Fin N) : ℝ := mtHessB N b ω (Pi.single a 1) 0 (Pi.single c 1) 0
/-- `∂²F/∂θ_a∂θ_c` at the ring. -/
def mtHessTT (N : ℕ) (b ω : ℝ) (a c : Fin N) : ℝ := mtHessB N b ω 0 (Pi.single a 1) 0 (Pi.single c 1)
/-- `∂²F/∂s_a∂θ_c` at the ring. -/
def mtHessST (N : ℕ) (b ω : ℝ) (a c : Fin N) : ℝ := mtHessB N b ω (Pi.single a 1) 0 0 (Pi.single c 1)
/-- `∂²F/∂θ_a∂s_c` at the ring. -/
def mtHessTS (N : ℕ) (b ω : ℝ) (a c : Fin N) : ℝ := mtHessB N b ω 0 (Pi.single a 1) (Pi.single c 1) 0

section entries
variable {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : -1 < b) (ω : ℝ) (a c : Fin N)
include hN hb

theorem mtHessSS_eq : mtHessSS N b ω a c = mSS N b ω a c := by
  unfold mtHessSS mtHessB
  rw [mtHessQ_eq hN hb, mtHessQ_eq hN hb]
  unfold qForm
  simp only [add_zero, sub_zero, bil_add_left, bil_add_right, bil_sub_left, bil_sub_right,
    bil_zero_right, bil_single]
  rw [mSS_symm N b ω c a]; ring

theorem mtHessTT_eq : mtHessTT N b ω a c = mTT N a c := by
  unfold mtHessTT mtHessB
  rw [mtHessQ_eq hN hb, mtHessQ_eq hN hb]
  unfold qForm
  simp only [add_zero, zero_add, sub_self, bil_add_left, bil_add_right, bil_sub_left,
    bil_sub_right, bil_zero_left, bil_zero_right, bil_single]
  rw [mTT_symm N c a]; ring

theorem mtHessST_eq : mtHessST N b ω a c = 0 := by
  unfold mtHessST mtHessB
  rw [mtHessQ_eq hN hb, mtHessQ_eq hN hb]
  unfold qForm
  simp only [add_zero, sub_zero, zero_add, bil_sub_left,
    bil_sub_right, bil_zero_left, bil_zero_right, bil_single]
  rw [mST_zero]; ring

theorem mtHessTS_eq : mtHessTS N b ω a c = 0 := by
  unfold mtHessTS mtHessB
  rw [mtHessQ_eq hN hb, mtHessQ_eq hN hb]
  unfold qForm
  simp only [add_zero, sub_zero, zero_add, zero_sub, bil_neg_left, bil_neg_right, bil_single]
  rw [mST_zero]; ring

end entries

/-! ## The Fourier blocks (paper Prop. 2.3) -/

theorem sBeta_zero (N m : ℕ) : sBeta N 0 m = 0 := by
  unfold sBeta; simp [rho_zero]

/-- **Paper Prop. 2.3 (Fourier blocks), derived from the Hamiltonian.** For `b > −1`, `ω = ω₀`, `0 ≤ m ≤ n` and
`v_c = w^{mc}`: `Σ_c ∂²F/∂s_a∂s_c v_c = a_m v_a`, `Σ_c ∂²F/∂θ_a∂θ_c v_c = b_m v_a`, and the mixed blocks
vanish, with `a_m = C₁ − m(n−m)`, `b_m = m(n−m)`, `C₁ = 2(n−1)(1+b²)/(1+b)²`. -/
theorem mt_blocks_eigen {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : -1 < b) (m : ℕ) (hmN : m ≤ N) (a : Fin N) :
    ∑ c : Fin N, ((mtHessSS N b (mtOmega N b) a c : ℝ) : ℂ) * (ringW N ^ (c : ℕ)) ^ m
        = (mtA N m b : ℂ) * (ringW N ^ (a : ℕ)) ^ m
      ∧ ∑ c : Fin N, ((mtHessTT N b (mtOmega N b) a c : ℝ) : ℂ) * (ringW N ^ (c : ℕ)) ^ m
        = (mtB N m : ℂ) * (ringW N ^ (a : ℕ)) ^ m
      ∧ ∑ c : Fin N, ((mtHessST N b (mtOmega N b) a c : ℝ) : ℂ) * (ringW N ^ (c : ℕ)) ^ m = 0
      ∧ ∑ c : Fin N, ((mtHessTS N b (mtOmega N b) a c : ℝ) : ℂ) * (ringW N ^ (c : ℕ)) ^ m = 0 := by
  have : NeZero N := ⟨hN.ne'⟩
  have hsA := sAlpha_eq (N := N) m hmN
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [mtHessSS_eq hN hb]
    unfold mSS
    simp only [Complex.ofReal_add, Complex.ofReal_mul, add_mul, Finset.sum_add_distrib]
    have e1 : ∑ x : Fin N, ((2 : ℝ) : ℂ) * ((hSS N 0 0 a x : ℝ) : ℂ) * (ringW N ^ (x : ℕ)) ^ m
        = ((2 : ℝ) : ℂ) * ∑ x : Fin N, ((hSS N 0 0 a x : ℝ) : ℂ) * (ringW N ^ (x : ℕ)) ^ m := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => ?_; ring
    have hdiag : ∑ x : Fin N, (((if a = x then mtD N b (mtOmega N b) else 0 : ℝ)) : ℂ)
        * (ringW N ^ (x : ℕ)) ^ m = (mtD N b (mtOmega N b) : ℂ) * (ringW N ^ (a : ℕ)) ^ m := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro x _ hx; simp [Ne.symm hx]
      · intro h; exact absurd (Finset.mem_univ a) h
    rw [e1, eig_hSS, hsA, sBeta_zero, sBeta_zero, hdiag, mtD_omega N hb]
    unfold mtA Vj
    push_cast
    ring
  · simp_rw [mtHessTT_eq hN hb]
    unfold mTT
    simp only [Complex.ofReal_mul]
    have e1 : ∑ x : Fin N, ((2 : ℝ) : ℂ) * ((hTT N 0 a x : ℝ) : ℂ) * (ringW N ^ (x : ℕ)) ^ m
        = ((2 : ℝ) : ℂ) * ∑ x : Fin N, ((hTT N 0 a x : ℝ) : ℂ) * (ringW N ^ (x : ℕ)) ^ m := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => ?_; ring
    rw [e1, eig_hTT, hsA, sBeta_zero, sBeta_zero]
    unfold mtB
    push_cast
    ring
  · simp_rw [mtHessST_eq hN hb]
    simp
  · simp_rw [mtHessTS_eq hN hb]
    simp

/-- **Hermitian form**: for `0 ≤ m, m' ≤ n−1` the Hessian is block-diagonal over Fourier modes,
`diag(a_m, b_m)` on mode `m`, with no coupling between different modes and no `sθ` coupling. -/
theorem mt_blocks_hermitian {N : ℕ} {b : ℝ} (hb : -1 < b) (m m' : ℕ) (hmN : m < N) (hm' : m' < N) :
    (∑ a : Fin N, ∑ c : Fin N, conj ((ringW N ^ (a : ℕ)) ^ m')
        * ((mtHessSS N b (mtOmega N b) a c : ℝ) : ℂ) * (ringW N ^ (c : ℕ)) ^ m
      = if m = m' then (N : ℂ) * (mtA N m b : ℂ) else 0)
    ∧ (∑ a : Fin N, ∑ c : Fin N, conj ((ringW N ^ (a : ℕ)) ^ m')
        * ((mtHessTT N b (mtOmega N b) a c : ℝ) : ℂ) * (ringW N ^ (c : ℕ)) ^ m
      = if m = m' then (N : ℂ) * (mtB N m : ℂ) else 0)
    ∧ (∑ a : Fin N, ∑ c : Fin N, conj ((ringW N ^ (a : ℕ)) ^ m')
        * ((mtHessST N b (mtOmega N b) a c : ℝ) : ℂ) * (ringW N ^ (c : ℕ)) ^ m = 0)
    ∧ (∑ a : Fin N, ∑ c : Fin N, conj ((ringW N ^ (a : ℕ)) ^ m')
        * ((mtHessTS N b (mtOmega N b) a c : ℝ) : ℂ) * (ringW N ^ (c : ℕ)) ^ m = 0) := by
  have hN : 0 < N := by omega
  have E := mt_blocks_eigen hN hb m hmN.le
  refine ⟨herm_of_eig hN (fun a => (E a).1) m' hmN hm',
    herm_of_eig hN (fun a => (E a).2.1) m' hmN hm', ?_, ?_⟩
  · have := herm_of_eig hN (μ := 0) (fun a => by rw [(E a).2.2.1, zero_mul]) m' hmN hm'
    rw [this]; simp
  · have := herm_of_eig hN (μ := 0) (fun a => by rw [(E a).2.2.2, zero_mul]) m' hmN hm'
    rw [this]; simp

/-- At the threshold `C₁ = ⌊n²/4⌋` the radial eigenvalue `a_m` vanishes exactly on the critical mode and is
positive on the other modes `m ≤ ⌊n/2⌋` (combining with `Conj13.am_nonneg_and_kernel`). -/
theorem mtA_at_threshold (N m : ℕ) (b : ℝ) (hC : mtC1 N b = ((N ^ 2 / 4 : ℕ) : ℝ)) :
    mtA N m b = ((N ^ 2 / 4 : ℕ) : ℝ) - (m : ℝ) * ((N : ℝ) - m) := by
  unfold mtA; rw [hC]

end Conj13.MTBlocks
