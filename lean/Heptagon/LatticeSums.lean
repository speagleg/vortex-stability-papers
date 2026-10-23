/-
Paper 2 (finite-core heptagon), Lemma 4.1: lattice sums over the N-th roots of unity.

  T a n = ∑_{j=1}^{N-1} ζ^(j n) / (1 - ζ^j)^a      (ζ a primitive N-th root of unity)

We prove: periodicity, the difference relation T (a+1) n - T (a+1) (n+1) = T a n, the zero sum
∑_{n<N} T a n = 0, the values of T 0, and the closed forms of T 1, …, T 4 on 1 ≤ n ≤ N.
Written for this paper (no source module).
-/
import Mathlib

namespace Heptagon

open Finset

/-- The lattice sum `T a n = ∑_{j=1}^{N-1} ζ^(j n) / (1 - ζ^j)^a`. -/
noncomputable def T (N : ℕ) (ζ : ℂ) (a n : ℕ) : ℂ :=
  ∑ j ∈ Ico 1 N, ζ ^ (j * n) / (1 - ζ ^ j) ^ a

variable {N : ℕ} {ζ : ℂ}

lemma pow_ne_one_of_mem (hζ : IsPrimitiveRoot ζ N) {j : ℕ} (hj : j ∈ Ico 1 N) : ζ ^ j ≠ 1 := by
  rw [mem_Ico] at hj
  exact hζ.pow_ne_one_of_pos_of_lt (by omega) hj.2

lemma one_sub_pow_ne_zero (hζ : IsPrimitiveRoot ζ N) {j : ℕ} (hj : j ∈ Ico 1 N) :
    1 - ζ ^ j ≠ 0 := by
  intro h
  exact pow_ne_one_of_mem hζ hj (by linear_combination -h)

/-- Periodicity in `n`. -/
lemma T_add_N (hζ : IsPrimitiveRoot ζ N) (a n : ℕ) : T N ζ a (n + N) = T N ζ a n := by
  unfold T
  apply sum_congr rfl
  intro j _
  rw [show j * (n + N) = j * n + N * j by ring, pow_add, pow_mul ζ N j, hζ.pow_eq_one, one_pow, mul_one]

lemma T_N (hζ : IsPrimitiveRoot ζ N) (a : ℕ) : T N ζ a N = T N ζ a 0 := by
  simpa using T_add_N hζ a 0

/-- The difference relation. -/
lemma T_sub_succ (hζ : IsPrimitiveRoot ζ N) (a n : ℕ) :
    T N ζ (a + 1) n - T N ζ (a + 1) (n + 1) = T N ζ a n := by
  unfold T
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  have h := one_sub_pow_ne_zero hζ hj
  rw [show j * (n + 1) = j * n + j by ring, pow_add, pow_succ]
  field_simp
  ring

/-- The zero sum over a period. -/
lemma sum_T (hζ : IsPrimitiveRoot ζ N) (a : ℕ) : ∑ n ∈ range N, T N ζ a n = 0 := by
  unfold T
  rw [sum_comm]
  apply sum_eq_zero
  intro j hj
  have hj1 := pow_ne_one_of_mem hζ hj
  have e : ∑ n ∈ range N, ζ ^ (j * n) / (1 - ζ ^ j) ^ a
      = (∑ n ∈ range N, (ζ ^ j) ^ n) / (1 - ζ ^ j) ^ a := by
    rw [sum_div]
    apply sum_congr rfl
    intro n _
    rw [pow_mul]
  rw [e, geom_sum_eq hj1, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  simp

/-- `T 0 n = -1` for `0 < n < N`. -/
lemma T_zero (hζ : IsPrimitiveRoot ζ N) {n : ℕ} (h1 : 1 ≤ n) (h2 : n < N) : T N ζ 0 n = -1 := by
  unfold T
  have hn : ζ ^ n ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by omega) h2
  have hN : 1 ≤ N := by omega
  simp only [pow_zero, div_one]
  rw [sum_Ico_eq_sub _ hN]
  have e : ∑ j ∈ range N, ζ ^ (j * n) = ∑ j ∈ range N, (ζ ^ n) ^ j := by
    apply sum_congr rfl; intro j _; rw [← pow_mul, mul_comm]
  rw [e, geom_sum_eq hn, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  simp

/-- `T a 0 = ∑_{j=1}^{N-1} (1 - ζ^j)^(-a)`. -/
lemma T_at_zero (a : ℕ) : T N ζ a 0 = ∑ j ∈ Ico 1 N, 1 / (1 - ζ ^ j) ^ a := by
  simp [T]

/-- Inductive step for the closed forms: if `P n - P (n+1) = T a n` on `1 ≤ n ≤ N-1` and
`∑_{n<N} P (n+1) = 0`, then `T (a+1) n = P n` on `1 ≤ n ≤ N`. -/
lemma T_eq_of (hζ : IsPrimitiveRoot ζ N) (hN : 1 ≤ N) (a : ℕ) (P : ℕ → ℂ)
    (hP : ∀ n, 1 ≤ n → n + 1 ≤ N → P n - P (n + 1) = T N ζ a n)
    (hsum : ∑ n ∈ range N, P (n + 1) = 0) :
    ∀ n, 1 ≤ n → n ≤ N → T N ζ (a + 1) n = P n := by
  set D : ℕ → ℂ := fun n => T N ζ (a + 1) (n + 1) - P (n + 1) with hD
  have hconst : ∀ n, n < N → D n = D 0 := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have h1 := T_sub_succ hζ a (k + 1)
      have h2 := hP (k + 1) (by omega) (by omega)
      rw [← ih (by omega)]
      simp only [hD]
      linear_combination -h1 + h2
  have hsumT : ∑ n ∈ range N, T N ζ (a + 1) (n + 1) = 0 := by
    have h := sum_T hζ (a + 1)
    have hT : T N ζ (a + 1) N = T N ζ (a + 1) 0 := T_N hζ (a + 1)
    obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have e1 : ∑ n ∈ range N, T N ζ (a + 1) n
        = ∑ k ∈ range M, T N ζ (a + 1) (k + 1) + T N ζ (a + 1) 0 := by
      rw [hM, sum_range_succ']
    have e2 : ∑ n ∈ range N, T N ζ (a + 1) (n + 1)
        = ∑ k ∈ range M, T N ζ (a + 1) (k + 1) + T N ζ (a + 1) N := by
      conv_lhs => rw [hM]
      rw [sum_range_succ, hM]
    rw [e2, hT, ← e1, h]
  have hsumD : ∑ n ∈ range N, D n = (N : ℂ) * D 0 := by
    rw [sum_congr rfl (fun n hn => hconst n (mem_range.mp hn))]
    simp
  have hsumD' : ∑ n ∈ range N, D n = 0 := by
    simp only [hD, sum_sub_distrib, hsumT, hsum, sub_zero]
  have hD0 : D 0 = 0 := by
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have := hsumD.symm.trans hsumD'
    exact (mul_eq_zero.mp this).resolve_left hNc
  intro n h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have := hconst k (by omega)
  rw [hD0] at this
  simp only [hD] at this
  linear_combination this

/-! ### Closed forms (polynomials in `N` and `n`, valid for `1 ≤ n ≤ N`) -/

/-- `P₁(N, n) = (2n - N - 1)/2`. -/
noncomputable def P1 (N : ℕ) (n : ℕ) : ℂ := (2 * n - N - 1) / 2
noncomputable def P2 (N : ℕ) (n : ℕ) : ℂ :=
  (-(N : ℂ) ^ 2 + 6 * N * n - 6 * N - 6 * (n : ℂ) ^ 2 + 12 * n - 5) / 12
noncomputable def P3 (N : ℕ) (n : ℕ) : ℂ :=
  (2 * (N : ℂ) ^ 2 * n - 3 * (N : ℂ) ^ 2 - 6 * N * (n : ℂ) ^ 2 + 18 * N * n - 12 * N
    + 4 * (n : ℂ) ^ 3 - 18 * (n : ℂ) ^ 2 + 24 * n - 9) / 24
noncomputable def P4 (N : ℕ) (n : ℕ) : ℂ :=
  ((N : ℂ) ^ 4 - 30 * (N : ℂ) ^ 2 * (n : ℂ) ^ 2 + 120 * (N : ℂ) ^ 2 * n - 110 * (N : ℂ) ^ 2
    + 60 * N * (n : ℂ) ^ 3 - 360 * N * (n : ℂ) ^ 2 + 660 * N * n - 360 * N - 30 * (n : ℂ) ^ 4
    + 240 * (n : ℂ) ^ 3 - 660 * (n : ℂ) ^ 2 + 720 * n - 251) / 720

/-- Telescoping: if `Q (n+1) - Q n = f (n+1)`, `Q 0 = 0` and `Q N = 0` then `∑_{n<N} f (n+1) = 0`. -/
lemma sum_eq_zero_of_antideriv (f Q : ℕ → ℂ) (h : ∀ n, Q (n + 1) - Q n = f (n + 1))
    (h0 : Q 0 = 0) (hN : Q N = 0) : ∑ n ∈ range N, f (n + 1) = 0 := by
  rw [← sum_congr rfl (fun n _ => h n), sum_range_sub, h0, hN, sub_zero]

theorem T1_closed (hζ : IsPrimitiveRoot ζ N) (hN : 1 ≤ N) :
    ∀ n, 1 ≤ n → n ≤ N → T N ζ 1 n = P1 N n := by
  apply T_eq_of hζ hN 0
  · intro n h1 h2
    rw [T_zero hζ h1 (by omega)]
    simp only [P1]; push_cast; ring
  · apply sum_eq_zero_of_antideriv _ (fun n => (n : ℂ) * ((n : ℂ) - N) / 2)
    · intro n; simp only [P1]; push_cast; ring
    · simp
    · simp

theorem T2_closed (hζ : IsPrimitiveRoot ζ N) (hN : 1 ≤ N) :
    ∀ n, 1 ≤ n → n ≤ N → T N ζ 2 n = P2 N n := by
  apply T_eq_of hζ hN 1
  · intro n h1 h2
    rw [T1_closed hζ hN n h1 (by omega)]
    simp only [P1, P2]; push_cast; ring
  · apply sum_eq_zero_of_antideriv _
      (fun n => -(n : ℂ) * ((n : ℂ) - N) * (-(N : ℂ) + 2 * n - 3) / 12)
    · intro n; simp only [P2]; push_cast; ring
    · simp
    · simp

theorem T3_closed (hζ : IsPrimitiveRoot ζ N) (hN : 1 ≤ N) :
    ∀ n, 1 ≤ n → n ≤ N → T N ζ 3 n = P3 N n := by
  apply T_eq_of hζ hN 2
  · intro n h1 h2
    rw [T2_closed hζ hN n h1 (by omega)]
    simp only [P2, P3]; push_cast; ring
  · apply sum_eq_zero_of_antideriv _
      (fun n => (n : ℂ) * ((n : ℂ) - N) * ((n : ℂ) - 2) * ((n : ℂ) - N - 2) / 24)
    · intro n; simp only [P3]; push_cast; ring
    · simp
    · simp

theorem T4_closed (hζ : IsPrimitiveRoot ζ N) (hN : 1 ≤ N) :
    ∀ n, 1 ≤ n → n ≤ N → T N ζ 4 n = P4 N n := by
  apply T_eq_of hζ hN 3
  · intro n h1 h2
    rw [T3_closed hζ hN n h1 (by omega)]
    simp only [P3, P4]; push_cast; ring
  · apply sum_eq_zero_of_antideriv _
      (fun n => -(n : ℂ) * ((n : ℂ) - N) * ((N : ℂ) ^ 3 + (N : ℂ) ^ 2 * n - 9 * N * (n : ℂ) ^ 2
        + 45 * N * n - 55 * N + 6 * (n : ℂ) ^ 3 - 45 * (n : ℂ) ^ 2 + 110 * n - 90) / 720)
    · intro n; simp only [P4]; push_cast; ring
    · simp
    · simp

/-- The classical sums `∑ 1/(1-ζ^j) = (N-1)/2` and `∑ 1/(1-ζ^j)^2 = -(N-1)(N-5)/12`. -/
theorem sum_inv_one_sub (hζ : IsPrimitiveRoot ζ N) (hN : 1 ≤ N) :
    ∑ j ∈ Ico 1 N, 1 / (1 - ζ ^ j) = ((N : ℂ) - 1) / 2 := by
  have h := T1_closed hζ hN N hN le_rfl
  rw [T_N hζ, T_at_zero] at h
  simp only [pow_one] at h
  rw [h]; simp only [P1]; ring

theorem sum_inv_one_sub_sq (hζ : IsPrimitiveRoot ζ N) (hN : 1 ≤ N) :
    ∑ j ∈ Ico 1 N, 1 / (1 - ζ ^ j) ^ 2 = -((N : ℂ) - 1) * ((N : ℂ) - 5) / 12 := by
  have h := T2_closed hζ hN N hN le_rfl
  rw [T_N hζ, T_at_zero] at h
  rw [h]; simp only [P2]; ring

end Heptagon
