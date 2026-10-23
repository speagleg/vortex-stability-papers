/-
Paper 2 (finite-core heptagon), Section 6: the threshold shifts on S² and H² (G model) from the r⁴
coefficient 𝔄_N(y) of the critical stiffness.

The critical stiffness is a_⊥ = ½[(N-1)(1+y) - ⌊N²/4⌋] + ε 𝔄_N(y)/(1-y)²; its zero moves from
y = Θ_N to Θ_N + 𝔇_N ε with 𝔇_N = -2 𝔄_N(Θ_N)/((N-1)(1-Θ_N)²).  Here we check, for the closed forms of
𝔄_N (even and odd N; obtained by exact computer algebra in the paper, code/curved_general.py), that this
formula gives the closed forms of 𝔇_N, the tabulated values, and the signs of 𝔇_N.
What is not proved here: the closed forms of 𝔄_N themselves (exact computer algebra from the lattice-sum
reduction) and the curved-surface effective Hamiltonian (formal asymptotics).
Written for this paper (no source module).
-/
import Mathlib

set_option autoImplicit false

namespace Heptagon

/-- `𝔄_N(y)`, even `N`. -/
noncomputable def AcurvEven (N y : ℝ) : ℝ :=
  -(N - 1) * (3 * N ^ 2 - 12 * N + 10) / 32 * y ^ 2
    + (N - 2) * (9 * N ^ 4 + 179 * N ^ 3 - 938 * N ^ 2 + 1492 * N - 760) / 2304 * y
    - (N - 2) ^ 2 * (N - 1) * (3 * N ^ 3 + 6 * N ^ 2 - 28 * N + 40) / 2304
/-- `𝔄_N(y)`, odd `N`. -/
noncomputable def AcurvOdd (N y : ℝ) : ℝ :=
  -3 * (N - 3) * (N - 1) ^ 2 / 32 * y ^ 2
    + (N - 1) ^ 2 * (9 * N ^ 3 + 179 * N ^ 2 - 965 * N + 1169) / 2304 * y
    - (N - 3) * (N - 1) ^ 2 * (N ^ 3 + 2 * N ^ 2 - 11 * N + 12) / 768

/-- thresholds `Θ_N = ⌊N²/4⌋/(N-1) - 1`. -/
noncomputable def ThEven (N : ℝ) : ℝ := N ^ 2 / 4 / (N - 1) - 1
noncomputable def ThOdd (N : ℝ) : ℝ := (N ^ 2 - 1) / 4 / (N - 1) - 1

noncomputable def DEven (N : ℝ) : ℝ :=
  (N - 2) ^ 2 * (N - 1) * (3 * N ^ 4 - 104 * N ^ 3 + 612 * N ^ 2 - 1088 * N + 640)
    / (288 * (N ^ 2 - 8 * N + 8) ^ 2)
noncomputable def DOdd (N : ℝ) : ℝ :=
  (N - 3) * (N - 1) * (3 * N ^ 3 - 101 * N ^ 2 + 509 * N - 539) / (288 * (N - 7) ^ 2)

/-- The threshold formula turns 𝔄 into 𝔇 (even `N`). -/
theorem D_from_A_even (N : ℝ) (h1 : N - 1 ≠ 0) (h2 : N ^ 2 - 8 * N + 8 ≠ 0) :
    -2 * AcurvEven N (ThEven N) / ((N - 1) * (1 - ThEven N) ^ 2) = DEven N := by
  have h3 : 1 - ThEven N = -(N ^ 2 - 8 * N + 8) / (4 * (N - 1)) := by
    unfold ThEven; field_simp; ring
  rw [h3]
  unfold AcurvEven ThEven DEven
  field_simp
  ring

/-- The threshold formula turns 𝔄 into 𝔇 (odd `N`). -/
theorem D_from_A_odd (N : ℝ) (h1 : N - 1 ≠ 0) (h2 : N - 7 ≠ 0) :
    -2 * AcurvOdd N (ThOdd N) / ((N - 1) * (1 - ThOdd N) ^ 2) = DOdd N := by
  have h3 : 1 - ThOdd N = -(N - 7) / 4 := by
    unfold ThOdd
    have : N ^ 2 - 1 = (N - 1) * (N + 1) := by ring
    rw [this]; field_simp; ring
  rw [h3]
  unfold AcurvOdd ThOdd DOdd
  have : N ^ 2 - 1 = (N - 1) * (N + 1) := by ring
  rw [this]
  field_simp
  ring

/-- Tabulated values: `𝔇₄ = 1/8`, `𝔇₅ = -1`, `𝔇₆ = -380/9` (sphere); `𝔇₈, …, 𝔇₁₂` (H², G model). -/
theorem D_values : DEven 4 = 1 / 8 ∧ DOdd 5 = -1 ∧ DEven 6 = -380 / 9 ∧ DEven 8 = -539 / 4 ∧
    DOdd 9 = -244 / 3 ∧ DEven 10 = -2880 / 49 ∧ DOdd 11 = -55 ∧ DEven 12 = -179575 / 3528 := by
  unfold DEven DOdd; norm_num

/-- `𝔄_N(1)` on the curved surfaces equals the planar coefficient of Corollary 4.4. -/
theorem A_at_one_even (N : ℝ) :
    AcurvEven N 1 = -(N ^ 6 - 6 * N ^ 5 - 65 * N ^ 4 + 576 * N ^ 3 - 1632 * N ^ 2 + 1920 * N - 800) / 768 := by
  unfold AcurvEven; ring

theorem A_at_one_odd (N : ℝ) :
    AcurvOdd N 1 = -(N - 1) ^ 2 * (3 * N ^ 4 - 12 * N ^ 3 - 230 * N ^ 2 + 1316 * N - 1925) / 2304 := by
  unfold AcurvOdd; ring

/-- Signs: `𝔇_N < 0` for `5 ≤ N ≤ 27`, `N ≠ 7`; `𝔇₄ > 0`. -/
theorem D_neg_small (n : ℕ) (h1 : 5 ≤ n) (h2 : n ≤ 27) (h3 : n ≠ 7) :
    (Even n → DEven n < 0) ∧ (¬ Even n → DOdd n < 0) := by
  interval_cases n <;> first | exact absurd rfl h3 | (unfold DEven DOdd; norm_num [Nat.even_iff])

theorem D4_pos : 0 < DEven 4 := by unfold DEven; norm_num

/-- `𝔇_N > 0` for all real `N ≥ 28` (even form) and `N ≥ 29` (odd form). -/
theorem DEven_pos (N : ℝ) (h : 28 ≤ N) : 0 < DEven N := by
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ N = 28 + t := ⟨N - 28, by linarith, by ring⟩
  unfold DEven
  have e : 3 * (28 + t) ^ 4 - 104 * (28 + t) ^ 3 + 612 * (28 + t) ^ 2 - 1088 * (28 + t) + 640
      = 3 * t ^ 4 + 232 * t ^ 3 + 5988 * t ^ 2 + 52000 * t + 10944 := by ring
  rw [e]
  have hq : 0 < 3 * t ^ 4 + 232 * t ^ 3 + 5988 * t ^ 2 + 52000 * t + 10944 := by positivity
  have hd : 0 < (28 + t) ^ 2 - 8 * (28 + t) + 8 := by nlinarith
  have ha : 0 < 28 + t - 2 := by linarith
  have hb : 0 < 28 + t - 1 := by linarith
  positivity

theorem DOdd_pos (N : ℝ) (h : 29 ≤ N) : 0 < DOdd N := by
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ N = 29 + t := ⟨N - 29, by linarith, by ring⟩
  unfold DOdd
  have e : 3 * (29 + t) ^ 3 - 101 * (29 + t) ^ 2 + 509 * (29 + t) - 539
      = 3 * t ^ 3 + 160 * t ^ 2 + 2220 * t + 2448 := by ring
  rw [e]
  have hq : 0 < 3 * t ^ 3 + 160 * t ^ 2 + 2220 * t + 2448 := by positivity
  have ha : 0 < 29 + t - 3 := by linarith
  have hb : 0 < 29 + t - 1 := by linarith
  have hc : 0 < 29 + t - 7 := by linarith
  positivity

end Heptagon
