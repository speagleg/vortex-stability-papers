/-
Paper 2 (finite-core heptagon), Theorem 4.3 and Corollaries 4.4, 4.5: the Fourier blocks of the planar ring of
N patches, at order 0 and at order r^4, as polynomials in (N, m); the heptagon values (0, 6) and
(14, 56, 16); the critical-mode coefficient 𝔄_N(1) for even and odd N and its sign.

What is proved here: the lattice-sum expressions of Proposition 4.2 (which the paper derives by hand from
the effective Hamiltonian) equal the stated polynomials, for every N ≥ 2 and 1 ≤ m ≤ N - 1.
What is not proved here: the reduction of the Hessian of the effective Hamiltonian to these lattice-sum
expressions (Proposition 4.2, by hand), and the effective Hamiltonian itself (formal asymptotics).
Written for this paper (no source module).
-/
import Heptagon.LatticeSums

namespace Heptagon

open Finset

variable {N : ℕ} {ζ : ℂ}

/-- `μ = T₂(0) = ∑ (1-ζ^j)^(-2)`. -/
noncomputable def mu (N : ℕ) (ζ : ℂ) : ℂ := T N ζ 2 0
/-- `Λ(m) = -2 (T₃(0) - T₃(m+1))`. -/
noncomputable def LamP (N : ℕ) (ζ : ℂ) (m : ℕ) : ℂ := -2 * (T N ζ 3 0 - T N ζ 3 (m + 1))
/-- `Λ(-m) = -2 (T₃(0) - T₃(1-m))`, with `1 - m ≡ N + 1 - m (mod N)`. -/
noncomputable def LamM (N : ℕ) (ζ : ℂ) (m : ℕ) : ℂ := -2 * (T N ζ 3 0 - T N ζ 3 (N + 1 - m))
/-- `κ(m) = -T₂(0) + 3 (T₄(0) - T₄(1-m) - T₄(1+m) + T₄(2))`. -/
noncomputable def kap (N : ℕ) (ζ : ℂ) (m : ℕ) : ℂ :=
  -T N ζ 2 0 + 3 * (T N ζ 4 0 - T N ζ 4 (N + 1 - m) - T N ζ 4 (m + 1) + T N ζ 4 2)

/-- `Ω₁ = -μ²`: the r⁴ correction of the rotation rate (in the convention `F = H - Ω J`). -/
noncomputable def Om1 (N : ℕ) (ζ : ℂ) : ℂ := -(mu N ζ) ^ 2
/-- r⁴ coefficient of `a_⊥` (Proposition 4.2). -/
noncomputable def dPerp (N : ℕ) (ζ : ℂ) (m : ℕ) : ℂ :=
  (LamP N ζ m ^ 2 + LamM N ζ m ^ 2) / 4 + mu N ζ * kap N ζ m - 2 * Om1 N ζ
/-- r⁴ coefficient of `a_∥`. -/
noncomputable def dPar (N : ℕ) (ζ : ℂ) (m : ℕ) : ℂ :=
  (LamP N ζ m ^ 2 + LamM N ζ m ^ 2) / 4 - mu N ζ * kap N ζ m
/-- r⁴ coefficient of `ϖ`. -/
noncomputable def dVarpi (N : ℕ) (ζ : ℂ) (m : ℕ) : ℂ :=
  (LamP N ζ m ^ 2 - LamM N ζ m ^ 2) / 4
/-- point-vortex blocks from the lattice sums: `a_⊥⁰ = N - 1 + g(0) - g(m)`, `a_∥⁰ = g(m) - g(0)`,
with `g(n) = ∑ ζ^(jn) ζ^j/(1-ζ^j)² = T₂(n) - T₁(n)`. -/
noncomputable def aPerp0 (N : ℕ) (ζ : ℂ) (m : ℕ) : ℂ :=
  (N : ℂ) - 1 + (T N ζ 2 0 - T N ζ 1 0) - (T N ζ 2 m - T N ζ 1 m)
noncomputable def aPar0 (N : ℕ) (ζ : ℂ) (m : ℕ) : ℂ :=
  -((T N ζ 2 0 - T N ζ 1 0) - (T N ζ 2 m - T N ζ 1 m))

/-- The polynomial `d_⊥(N, m)` (times 144). -/
noncomputable def dPerpPoly (N m : ℂ) : ℂ :=
  (-N ^ 4 * m ^ 2 + 6 * N ^ 4 - 6 * N ^ 3 * m ^ 3 + 18 * N ^ 3 * m ^ 2 + 24 * N ^ 3 * m - 72 * N ^ 3
    + 23 * N ^ 2 * m ^ 4 - 36 * N ^ 2 * m ^ 3 - 21 * N ^ 2 * m ^ 2 - 144 * N ^ 2 * m + 276 * N ^ 2
    - 24 * N * m ^ 5 + 18 * N * m ^ 4 - 6 * N * m ^ 3 + 144 * N * m ^ 2 + 120 * N * m - 360 * N
    + 8 * m ^ 6 + 3 * m ^ 4 - 120 * m ^ 2 + 150) / 144

lemma T_zero_eq (hζ : IsPrimitiveRoot ζ N) (a : ℕ) : T N ζ a 0 = T N ζ a N := (T_N hζ a).symm

/-- Point-vortex blocks: `a_⊥⁰ = N - 1 - m(N-m)/2`, `a_∥⁰ = m(N-m)/2` for `1 ≤ m ≤ N`. -/
theorem pv_blocks (hζ : IsPrimitiveRoot ζ N) (hN : 1 ≤ N) (m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ N) :
    aPerp0 N ζ m = (N : ℂ) - 1 - (m : ℂ) * ((N : ℂ) - m) / 2 ∧
    aPar0 N ζ m = (m : ℂ) * ((N : ℂ) - m) / 2 := by
  have e1 := T1_closed hζ hN; have e2 := T2_closed hζ hN
  simp only [aPerp0, aPar0, T_zero_eq hζ, e1 N hN le_rfl, e2 N hN le_rfl, e1 m h1 h2, e2 m h1 h2,
    P1, P2]
  constructor <;> ring

/-- Theorem 4.3: the r⁴ blocks of the planar ring, for every `N ≥ 2` and `1 ≤ m ≤ N - 1`. -/
theorem r4_blocks (hζ : IsPrimitiveRoot ζ N) (hN : 2 ≤ N) (m : ℕ) (h1 : 1 ≤ m) (h2 : m + 1 ≤ N) :
    mu N ζ = -((N : ℂ) - 5) * ((N : ℂ) - 1) / 12 ∧
    Om1 N ζ = -(((N : ℂ) - 5) * ((N : ℂ) - 1)) ^ 2 / 144 ∧
    dPerp N ζ m = dPerpPoly N m ∧
    dPar N ζ m = (m : ℂ) ^ 2 * ((N : ℂ) - m) ^ 2
        * (5 * (N : ℂ) ^ 2 - 8 * N * m - 18 * N + 8 * (m : ℂ) ^ 2 + 33) / 144 ∧
    dVarpi N ζ m = -(m : ℂ) * ((N : ℂ) - m) * ((N : ℂ) - 2 * m)
        * (-(N : ℂ) ^ 2 - 3 * N * m + 6 * N + 3 * (m : ℂ) ^ 2 - 5) / 36 := by
  have hN1 : 1 ≤ N := by omega
  have e2 := T2_closed hζ hN1; have e3 := T3_closed hζ hN1; have e4 := T4_closed hζ hN1
  have hc : ((N + 1 - m : ℕ) : ℂ) = (N : ℂ) + 1 - m := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  simp only [dPerp, dPar, dVarpi, Om1, mu, LamP, LamM, kap, T_zero_eq hζ,
    e2 N hN1 le_rfl, e3 N hN1 le_rfl, e4 N hN1 le_rfl,
    e3 (m + 1) (by omega) h2, e4 (m + 1) (by omega) h2,
    e3 (N + 1 - m) (by omega) (by omega), e4 (N + 1 - m) (by omega) (by omega),
    e4 2 (by omega) hN, P2, P3, P4, hc, dPerpPoly]
  push_cast
  refine ⟨by ring, by ring, by ring, by ring, by ring⟩

/-- The heptagon: `N = 7`, `m = 3`: point-vortex block `(0, 6)`, r⁴ block `(14, 56, 16)`, `Ω₁ = -1`. -/
theorem heptagon_blocks (hζ : IsPrimitiveRoot ζ 7) :
    aPerp0 7 ζ 3 = 0 ∧ aPar0 7 ζ 3 = 6 ∧
    dPerp 7 ζ 3 = 14 ∧ dPar 7 ζ 3 = 56 ∧ dVarpi 7 ζ 3 = 16 ∧ Om1 7 ζ = -1 := by
  obtain ⟨p1, p2⟩ := pv_blocks hζ (by norm_num) 3 (by norm_num) (by norm_num)
  obtain ⟨_, q1, q2, q3, q4⟩ := r4_blocks hζ (by norm_num) 3 (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p1]; norm_num
  · rw [p2]; norm_num
  · rw [q2, dPerpPoly]; norm_num
  · rw [q3]; norm_num
  · rw [q4]; norm_num
  · rw [q1]; norm_num

/-- The same with the explicit root `ζ = exp(2πi/7)`. -/
theorem heptagon_blocks_exp :
    let ζ := Complex.exp (2 * Real.pi * Complex.I / 7)
    aPerp0 7 ζ 3 = 0 ∧ aPar0 7 ζ 3 = 6 ∧
    dPerp 7 ζ 3 = 14 ∧ dPar 7 ζ 3 = 56 ∧ dVarpi 7 ζ 3 = 16 ∧ Om1 7 ζ = -1 :=
  heptagon_blocks (Complex.isPrimitiveRoot_exp 7 (by norm_num))

/-! ### The critical mode `m = ⌊N/2⌋`: the coefficient `𝔄_N(1)` -/

/-- even `N = 2k`, `m = k`. -/
theorem A_even (k : ℂ) :
    dPerpPoly (2 * k) k = -((2 * k) ^ 6 - 6 * (2 * k) ^ 5 - 65 * (2 * k) ^ 4 + 576 * (2 * k) ^ 3
      - 1632 * (2 * k) ^ 2 + 1920 * (2 * k) - 800) / 768 := by
  unfold dPerpPoly; ring

/-- odd `N = 2k+1`, `m = k`. -/
theorem A_odd (k : ℂ) :
    dPerpPoly (2 * k + 1) k = -((2 * k + 1) - 1) ^ 2 * (3 * (2 * k + 1) ^ 4 - 12 * (2 * k + 1) ^ 3
      - 230 * (2 * k + 1) ^ 2 + 1316 * (2 * k + 1) - 1925) / 2304 := by
  unfold dPerpPoly; ring

/-- Real forms of `𝔄_N(1)`. -/
noncomputable def AevenR (N : ℝ) : ℝ := -(N ^ 6 - 6 * N ^ 5 - 65 * N ^ 4 + 576 * N ^ 3 - 1632 * N ^ 2 + 1920 * N - 800) / 768
noncomputable def AoddR (N : ℝ) : ℝ := -(N - 1) ^ 2 * (3 * N ^ 4 - 12 * N ^ 3 - 230 * N ^ 2 + 1316 * N - 1925) / 2304

/-- Signs: cores stabilise the critical mode for `N ≤ 7` and destabilise it for `N ≥ 8`. -/
theorem A_values : AevenR 2 = 1 / 16 ∧ AoddR 3 = 2 / 9 ∧ AevenR 4 = 11 / 8 ∧ AoddR 5 = 5 ∧
    AevenR 6 = 491 / 48 ∧ AoddR 7 = 14 ∧ AevenR 8 = -45 / 8 ∧ AoddR 9 = -556 / 9 := by
  unfold AevenR AoddR; norm_num

theorem A_even_neg (N : ℝ) (h : 8 ≤ N) : AevenR N < 0 := by
  unfold AevenR
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ N = 8 + t := ⟨N - 8, by linarith, by ring⟩
  have : 0 < (8 + t) ^ 6 - 6 * (8 + t) ^ 5 - 65 * (8 + t) ^ 4 + 576 * (8 + t) ^ 3
      - 1632 * (8 + t) ^ 2 + 1920 * (8 + t) - 800 := by
    have e : (8 + t) ^ 6 - 6 * (8 + t) ^ 5 - 65 * (8 + t) ^ 4 + 576 * (8 + t) ^ 3
        - 1632 * (8 + t) ^ 2 + 1920 * (8 + t) - 800
        = t ^ 6 + 42 * t ^ 5 + 655 * t ^ 4 + 4896 * t ^ 3 + 17952 * t ^ 2 + 27008 * t + 4320 := by ring
    rw [e]; positivity
  linarith

theorem A_odd_neg (N : ℝ) (h : 8 ≤ N) : AoddR N < 0 := by
  unfold AoddR
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ N = 8 + t := ⟨N - 8, by linarith, by ring⟩
  have h1 : 0 < 3 * (8 + t) ^ 4 - 12 * (8 + t) ^ 3 - 230 * (8 + t) ^ 2 + 1316 * (8 + t) - 1925 := by
    have e : 3 * (8 + t) ^ 4 - 12 * (8 + t) ^ 3 - 230 * (8 + t) ^ 2 + 1316 * (8 + t) - 1925
        = 3 * t ^ 4 + 84 * t ^ 3 + 634 * t ^ 2 + 1476 * t + 27 := by ring
    rw [e]; positivity
  have h2 : 0 < (8 + t - 1) ^ 2 := by
    have : 0 < 8 + t - 1 := by linarith
    positivity
  have := mul_pos h2 h1
  have e2 : -(8 + t - 1) ^ 2 * (3 * (8 + t) ^ 4 - 12 * (8 + t) ^ 3 - 230 * (8 + t) ^ 2
      + 1316 * (8 + t) - 1925) / 2304
      = -((8 + t - 1) ^ 2 * (3 * (8 + t) ^ 4 - 12 * (8 + t) ^ 3 - 230 * (8 + t) ^ 2
      + 1316 * (8 + t) - 1925)) / 2304 := by ring
  rw [e2]
  linarith

end Heptagon
