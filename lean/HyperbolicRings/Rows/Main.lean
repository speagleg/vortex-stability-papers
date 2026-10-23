/-
New in this paper (vortex-stability-papers, paper 3). Not copied from the source repositories.

Hypercycle rows: the critical-curvature theorem stated for the Bloch matrices assembled from the pair term
(paper, Theorem "critical curvature"), combining `Rows.Criterion` with `Rows.Bloch` and `Rows.CriticalMode`.

Notation: `0 < α < π`, `κ = cos α`, `K = κ²`, `ℓ > 0` the strip spacing; "mode `q` stable" means every eigenvalue of
the Bloch matrix `rowFlow (ϖ(q)) (B(q)) (C(q))` has zero real part.
-/
import HyperbolicRings.Rows.CriticalMode

noncomputable section

namespace HyperbolicRings.Rows

open Real

/-- Mode `q` of the hypercycle row is spectrally stable. -/
def ModeStable (α ℓ q : ℝ) : Prop :=
  ∀ σ, Module.End.HasEigenvalue
    (Matrix.toLin' (rowFlow (varpi α ℓ q) (2 * F (cos α ^ 2) ℓ q) (Cser (cos α ^ 2) ℓ q))) σ → σ.re = 0

/-- The row is spectrally stable: every Bloch mode with `cos q ≠ 1` is. -/
def RowStable (α ℓ : ℝ) : Prop := ∀ q : ℝ, Real.cos q ≠ 1 → ModeStable α ℓ q

variable {α ℓ : ℝ} (hα0 : 0 < α) (hαπ : α < π) (hℓ : 0 < ℓ)
include hα0 hαπ hℓ

/-- `|κ| ≤ 1/√2` (i.e. `cos²α ≤ 1/2`): the row is unstable at every spacing; the pairing mode `q = π` is unstable. -/
theorem row_unstable_of_le_kappa_c (hK : cos α ^ 2 ≤ 1 / 2) : ¬ RowStable α ℓ ∧ ¬ ModeStable α ℓ π := by
  have hneg := pairing_instability (sq_nonneg (cos α)) hK hℓ
  have hπ : Real.cos π ≠ 1 := by rw [Real.cos_pi]; norm_num
  have hm : ¬ ModeStable α ℓ π := fun h => by
    have := (bloch_stable_iff hα0 hαπ hℓ hπ).mp h; linarith
  exact ⟨fun h => hm (h π hπ), hm⟩

/-- `|κ| ≤ 1/2`: every Bloch mode with `cos q ≠ 1` is unstable, at every spacing. -/
theorem every_mode_unstable (hK : cos α ^ 2 ≤ 1 / 4) (q : ℝ) (hq : Real.cos q ≠ 1) : ¬ ModeStable α ℓ q := by
  intro h
  have := (bloch_stable_iff hα0 hαπ hℓ hq).mp h
  have := all_mode_instability (sq_nonneg (cos α)) hK hℓ q
  linarith

/-- `|κ| > 1/√2` and `(2κ² - 1) cosh ℓ ≥ 1`: the row is spectrally stable. -/
theorem row_stable_of_bound (h : 1 ≤ (2 * cos α ^ 2 - 1) * cosh ℓ) : RowStable α ℓ := by
  have hK : cos α ^ 2 < 1 := K_lt_one hα0 hαπ hℓ
  intro q hq
  exact (bloch_stable_iff hα0 hαπ hℓ hq).mpr (stability_bound (sq_nonneg _) hK hℓ h q).le

/-- The row is spectrally stable iff `F(π) ≥ 0`. -/
theorem rowStable_iff : RowStable α ℓ ↔ 0 ≤ F (cos α ^ 2) ℓ π := row_stable_iff_F_pi hα0 hαπ hℓ

end HyperbolicRings.Rows
