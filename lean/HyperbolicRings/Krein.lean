/-
New in this paper (vortex-stability-papers, paper 3). Not copied from the source repositories.

Krein signatures in the odd-N window (paper, Theorem "Krein window", part (c)).

For a Hermitian block `M = [[a, i g], [-i g, b]]` with `a b > 0` and `a b - g² < 0`, the flow block
`J₀ M` has the two distinct purely imaginary eigenvalues `σ = i(-g ± √(ab))`, and the Hessian form
`v* M v` has opposite signs on the corresponding eigenvectors (opposite Krein signatures).
Combined with the Lean results `krein_window_odd` and `unique_threshold_of_ge_eight` this gives, for
every odd `N ≥ 9`, a right neighbourhood of `ξ_*(N)` on which the critical mode carries two
eigenvalues of opposite Krein signature.
-/
import HyperbolicRings.Tanh.LargeN.AllN
import HyperbolicRings.Tanh.LargeN.ThresholdKrein
import HyperbolicRings.Tanh.LargeN.Dynamics

noncomputable section

namespace HyperbolicRings.Krein

open Complex Matrix HyperbolicRings.Tanh HyperbolicRings.Tanh.LargeN

/-- The Hermitian form `v* M v` of the block `M = hessBlock a b g`. -/
def form (a b g : ℝ) (v : Fin 2 → ℂ) : ℂ := star v ⬝ᵥ (hessBlock a b g *ᵥ v)

/-- If `v ≠ 0` is an eigenvector of `J₀ M` for `σ = i(-g + μ)`, with `b ≠ 0`, then
`v₁ ≠ 0`, `v₂ = i μ v₁ / b`, and `v* M v = 2 μ (μ - g) |v₁|² / b` when `μ² = a b`. -/
theorem form_eigvec {a b g μ : ℝ} (hb : b ≠ 0) (hμ : μ ^ 2 = a * b) {v : Fin 2 → ℂ}
    (hv : flowBlock a b g *ᵥ v = (I * ((-g + μ : ℝ) : ℂ)) • v) :
    form a b g v = ((2 * μ * (μ - g) / b : ℝ) : ℂ) * (Complex.normSq (v 0) : ℂ) := by
  have h0 := congrFun hv 0
  simp [flowBlock, hessBlock, J0, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
  -- first row: (-i g) v0 + b v1 = i(-g+μ) v0, i.e. b v1 = i μ v0
  have hv1 : v 1 = I * μ * v 0 / b := by
    have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb
    field_simp
    linear_combination h0
  simp only [form, hessBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, Pi.star_apply,
    Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_cons]
  rw [hv1]
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  have hn : (Complex.normSq (v 0) : ℂ) = star (v 0) * v 0 := by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  rw [hn]
  have hμC : ((μ : ℂ)) ^ 2 = (a : ℂ) * b := by exact_mod_cast hμ
  simp only [star_div₀, star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  field_simp
  linear_combination ((starRingEnd ℂ) (v 0) * v 0 * (2 * (g : ℂ) * μ - (μ : ℂ) ^ 2)) * I_sq
    - ((starRingEnd ℂ) (v 0) * v 0) * hμC

/-- Opposite Krein signatures: if `a b > 0` and `a b - g² < 0`, eigenvectors `v`, `w` of `J₀ M`
for the eigenvalues `i(-g + √(ab))` and `i(-g - √(ab))` have `(v* M v)(w* M w) < 0`. -/
theorem opposite_signatures {a b g : ℝ} (hab : 0 < a * b) (hdet : a * b - g ^ 2 < 0)
    {v w : Fin 2 → ℂ} (hv0 : v ≠ 0) (hw0 : w ≠ 0)
    (hv : flowBlock a b g *ᵥ v = (I * ((-g + Real.sqrt (a * b) : ℝ) : ℂ)) • v)
    (hw : flowBlock a b g *ᵥ w = (I * ((-g + -Real.sqrt (a * b) : ℝ) : ℂ)) • w) :
    (form a b g v * form a b g w).re < 0 := by
  have hb : b ≠ 0 := by rintro rfl; simp at hab
  set μ := Real.sqrt (a * b) with hμdef
  have hμ2 : μ ^ 2 = a * b := Real.sq_sqrt hab.le
  have hμ2' : (-μ) ^ 2 = a * b := by rw [neg_sq]; exact hμ2
  have hμpos : 0 < μ := Real.sqrt_pos.mpr hab
  rw [form_eigvec hb hμ2 hv, form_eigvec hb hμ2' hw]
  -- first components are nonzero
  have nz : ∀ {u : Fin 2 → ℂ} {ν : ℝ}, u ≠ 0 →
      flowBlock a b g *ᵥ u = (I * ((-g + ν : ℝ) : ℂ)) • u → u 0 ≠ 0 := by
    intro u ν hu hfl h
    apply hu
    have h0 := congrFun hfl 0
    simp [flowBlock, hessBlock, J0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h] at h0
    have h1 : u 1 = 0 := by
      rcases h0 with h0 | h0
      · exact absurd (by exact_mod_cast h0) hb
      · exact h0
    funext i; fin_cases i <;> simp [h, h1]
  have hv1 := nz hv0 hv
  have hw1 := nz hw0 hw
  have pv : 0 < Complex.normSq (v 0) := Complex.normSq_pos.mpr hv1
  have pw : 0 < Complex.normSq (w 0) := Complex.normSq_pos.mpr hw1
  have key : (2 * μ * (μ - g) / b) * (2 * -μ * (-μ - g) / b) < 0 := by
    have : (2 * μ * (μ - g) / b) * (2 * -μ * (-μ - g) / b)
        = 4 * μ ^ 2 * (μ ^ 2 - g ^ 2) / b ^ 2 := by field_simp; ring
    rw [this, hμ2]
    apply div_neg_of_neg_of_pos _ (by positivity)
    have : 0 < 4 * (a * b) := by positivity
    nlinarith
  have : ((((2 * μ * (μ - g) / b : ℝ) : ℂ) * (Complex.normSq (v 0) : ℂ)) *
      (((2 * -μ * (-μ - g) / b : ℝ) : ℂ) * (Complex.normSq (w 0) : ℂ))).re
      = ((2 * μ * (μ - g) / b) * (2 * -μ * (-μ - g) / b)) *
          (Complex.normSq (v 0) * Complex.normSq (w 0)) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
  rw [this]
  exact mul_neg_of_neg_of_pos key (mul_pos pv pw)

/-- The two eigenvalues are distinct and purely imaginary under the same hypotheses. -/
theorem eigenvalues_imaginary_distinct {a b g : ℝ} (hab : 0 < a * b) :
    (I * ((-g + Real.sqrt (a * b) : ℝ) : ℂ)).re = 0 ∧
      (I * ((-g + -Real.sqrt (a * b) : ℝ) : ℂ)).re = 0 ∧
      (I * ((-g + Real.sqrt (a * b) : ℝ) : ℂ)) ≠ I * ((-g + -Real.sqrt (a * b) : ℝ) : ℂ) := by
  refine ⟨by simp, by simp, ?_⟩
  intro h
  have h' := congrArg Complex.im h
  simp at h'
  have := Real.sqrt_pos.mpr hab
  linarith

/-- Ring version: for every odd `N ≥ 9` there is `η > 0` such that on `(ξ_*, ξ_* + η)` the critical
block `M_{⌊N/2⌋}` satisfies `a b > 0` and `a b - g² < 0`; hence (by `opposite_signatures`) the two
eigenvalues of the critical mode are distinct, purely imaginary, and of opposite Krein signature. -/
theorem ring_window_hypotheses {N : ℕ} (hN : 9 ≤ N) (hodd : Odd N) :
    ∃ η > 0, ∀ ξ ∈ Set.Ioo (xiStar N) (xiStar N + η),
      0 < aBlock N (N / 2) ξ * bBlock N (N / 2) ξ ∧
      aBlock N (N / 2) ξ * bBlock N (N / 2) ξ - gBlock N (N / 2) ξ ^ 2 < 0 := by
  obtain ⟨hs0, hs1, -, -, ⟨η, hη, hdet⟩, -⟩ := krein_window_odd hN hodd
  obtain ⟨ξ₀, hξ₀, -, -, hpos, hstar, -⟩ := unique_threshold_of_ge_eight (by omega : 8 ≤ N)
  refine ⟨min η (1 - xiStar N), lt_min hη (by linarith), fun ξ hξ => ⟨?_, ?_⟩⟩
  · have hξ1 : ξ < 1 := by
      have := hξ.2; have := min_le_right η (1 - xiStar N); linarith
    have hξ0 : 0 < ξ := lt_trans hs0 hξ.1
    have ha : 0 < aBlock N (N / 2) ξ := hpos ξ ⟨by rw [← hstar]; exact hξ.1, hξ1⟩
    have hm1 : 1 ≤ N / 2 := by omega
    have hmN : N / 2 < N := by omega
    exact mul_pos ha (bBlock_pos (by omega) hm1 hmN hξ0 hξ1)
  · exact hdet ξ ⟨hξ.1, lt_of_lt_of_le hξ.2 (by simp)⟩

/-- `ξ_EM(N) < 1` for every `N ≥ 3` (the Hessian is definite near `ξ = 1`, where `Φ_N > 0`). -/
theorem xiEM_lt_one {N : ℕ} (hN : 3 ≤ N) : xiEM N < 1 := by
  obtain ⟨ξ₁, h0, h1, hP⟩ := exists_emDefinite_near_one hN
  exact lt_of_le_of_lt (thr_le (emDefinite N) h0.le h1.le hP) h1

/-- The odd-`N` Krein window lies inside `(0,1)`: `0 < ξ_* < ξ_EM < 1` for every odd `N ≥ 9`. -/
theorem krein_window_bounds {N : ℕ} (hN : 9 ≤ N) (hodd : Odd N) :
    0 < xiStar N ∧ xiStar N < xiEM N ∧ xiEM N < 1 := by
  obtain ⟨h0, -, -, -, -, h⟩ := krein_window_odd hN hodd
  exact ⟨h0, h, xiEM_lt_one (by omega)⟩

end HyperbolicRings.Krein
