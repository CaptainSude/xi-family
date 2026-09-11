import StonehamNormality.DependentSumWindows
import StonehamNormality.IndependentSum
import StonehamNormality.GeneralSeriesBridge

/-!
# Denominator growth for every pair of Stoneham truncations

The multiplicatively independent and dependent cases exhaust all parameters.
No normality or exponential-sum theorem is assumed in this arithmetic result.
-/

open Filter

namespace StonehamNormality

theorem dependent_pair_den_lower (b c d : ℕ)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hbc : Nat.Coprime b c)
    (hdep : ∃ r s : ℕ, 0 < r ∧ 0 < s ∧ c ^ r = d ^ s) :
    ∃ a M : ℕ, 2 ≤ a ∧ ∀ᶠ n : ℕ in atTop,
      2 ^ (Nat.log a n - M) ≤
        (radixStonehamTruncation b c n + radixStonehamTruncation b d n).den := by
  obtain ⟨r, s, hr, hs, heq⟩ := hdep
  obtain ⟨a, p, M, N, ha, hp, _, hbound⟩ :=
    dependent_pair_denominator_growth (by omega : 0 < b) hc hd hr hs hbc heq
  refine ⟨a, M, ha, ?_⟩
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hnN : N ≤ n := (Nat.le_max_left _ _).trans hn
  have hnpos : 0 < n := by have := (Nat.le_max_right N 1).trans hn; omega
  rw [radixStonehamTruncation_eq_powerTruncation_log b c n hc hnpos,
    radixStonehamTruncation_eq_powerTruncation_log b d n hd hnpos]
  exact (Nat.pow_le_pow_left hp.two_le _).trans (hbound n hnN)

/-- Every allowed pair has reduced denominators that grow at least as a fixed
positive power of the digit position.  The displayed integer-logarithm form
avoids real-power estimates at this purely arithmetic stage. -/
theorem all_pair_denominator_growth (b c d : ℕ)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hbc : Nat.Coprime b c) (hbd : Nat.Coprime b d) :
    ∃ a M : ℕ, 2 ≤ a ∧ ∀ᶠ n : ℕ in atTop,
      2 ^ (Nat.log a n - M) ≤
        (radixStonehamTruncation b c n + radixStonehamTruncation b d n).den := by
  classical
  by_cases hind : ∀ r s : ℕ, 0 < r → 0 < s → c ^ r ≠ d ^ s
  · obtain ⟨a, ha, hbound⟩ := independent_pair_den_lower b c d hb hc hd hbc hbd hind
    refine ⟨a, 0, ha, ?_⟩
    simpa only [Nat.sub_zero] using hbound
  · push_neg at hind
    exact dependent_pair_den_lower b c d hb hc hd hbc hind

end StonehamNormality
