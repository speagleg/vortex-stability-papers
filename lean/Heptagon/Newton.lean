/-
Paper 2 (finite-core heptagon), Lemma 3.1 ("rigid discs are point vortices"): the mean-value identities
behind the absence of an r² term on the plane.

(1) For 0 < R < |c - a|, the average of log|z - a| over the circle |z - c| = R equals log|c - a|.
    Hence (integrating over radii, by hand) the stream function of a uniform disc outside the disc equals
    that of a point vortex at its centre with the same circulation.
(2) For two circles with R₁ + R₂ < |c₁ - c₂|, the double average of log|z - w| equals log|c₁ - c₂|:
    the mutual energy of two disjoint uniform rings (and hence discs) equals that of two point vortices.
What is not proved here: the integration over radii (elementary), and the statement that all other
finite-core effects enter through shape deformations (formal asymptotics).
Written for this paper (no source module); it uses Mathlib's
`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`.
-/
import Mathlib

set_option autoImplicit false

namespace Heptagon

open Real Metric

/-- Newton's theorem for the logarithmic kernel on one circle. -/
theorem circleAverage_log_far (c a : ℂ) (R : ℝ) (hR : 0 < R) (h : R < ‖c - a‖) :
    circleAverage (fun z => log ‖z - a‖) c R = log ‖c - a‖ := by
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hR.ne']
  have h1 : 1 ≤ |R⁻¹ * ‖c - a‖| := by
    rw [abs_of_nonneg (by positivity)]
    rw [le_inv_mul_iff₀ hR]; linarith
  rw [posLog_eq_log h1, log_mul (inv_ne_zero hR.ne') (by linarith [norm_nonneg (c - a)]), log_inv]
  ring

/-- Two circles: the mutual logarithmic energy of two disjoint uniform rings equals that of their centres. -/
theorem circleAverage_log_two_circles (c₁ c₂ : ℂ) (R₁ R₂ : ℝ) (h₁ : 0 < R₁) (h₂ : 0 < R₂)
    (h : R₁ + R₂ < ‖c₁ - c₂‖) :
    circleAverage (fun z => circleAverage (fun w => log ‖z - w‖) c₂ R₂) c₁ R₁ = log ‖c₁ - c₂‖ := by
  have inner : Set.EqOn (fun z => circleAverage (fun w => log ‖z - w‖) c₂ R₂)
      (fun z => log ‖z - c₂‖) (sphere c₁ |R₁|) := by
    intro z hz
    rw [mem_sphere, abs_of_pos h₁, dist_eq_norm] at hz
    have hfar : R₂ < ‖c₂ - z‖ := by
      have tri : ‖c₁ - c₂‖ ≤ ‖z - c₁‖ + ‖z - c₂‖ := by
        calc ‖c₁ - c₂‖ = ‖(z - c₂) - (z - c₁)‖ := by congr 1; ring
          _ ≤ ‖z - c₂‖ + ‖z - c₁‖ := norm_sub_le _ _
          _ = ‖z - c₁‖ + ‖z - c₂‖ := by ring
      rw [norm_sub_rev c₂ z]
      linarith
    have hsym : (fun w => log ‖z - w‖) = (fun w => log ‖w - z‖) := by
      funext w; rw [norm_sub_rev]
    simp only
    rw [hsym, circleAverage_log_far c₂ z R₂ h₂ hfar, norm_sub_rev]
  rw [circleAverage_congr_sphere inner]
  exact circleAverage_log_far c₁ c₂ R₁ h₁ (by linarith)

end Heptagon
