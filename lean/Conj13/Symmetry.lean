/-
New module for paper 01-conjecture-13 (not copied; written for this paper).

Small exact facts used in §3 of the paper (the symmetry argument for the absence of a cubic term and the
form of the quartic) and in the remark on `n = 3`.
-/
import Conj13.Algebra

namespace Conj13.Symmetry

/-- **No cubic, a single quartic** (paper Lemma 3.3, odd `n`): the rotation acts on the kernel
`K₀ ≅ ℂ` by `a ↦ ζ a` with `ζ` a primitive `n`-th root of unity, so the monomial `a^p ā^q` is invariant
iff `n ∣ p − q`. For `n ≥ 5` and `p + q ≤ 4` this forces `p = q`. -/
theorem invariant_monomial (n p q : ℕ) (hn : 5 ≤ n) (hpq : p + q ≤ 4) (hdvd : (n : ℤ) ∣ (p : ℤ) - q) :
    p = q := by
  have h : (p : ℤ) - q = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hdvd
    rw [abs_lt]; constructor <;> omega
  omega

/-- For odd `n = 2M+1`, the critical mode `l = M = (n−1)/2` is prime to `n` (so the rotation generator
acts on the kernel by a *primitive* `n`-th root of unity); and `2l = n − 1 ≡ −1 (mod n)`. -/
theorem crit_mode_coprime (M : ℕ) : Nat.Coprime M (2 * M + 1) := by
  simp

/-- The odd closed form vanishes at `n = 3` (paper Remark 5.2). -/
theorem c4odd_three : c4odd (3 : ℚ) = 0 := by unfold c4odd; norm_num

end Conj13.Symmetry
