import StonehamNormality.PeriodicSums
import StonehamNormality.DependentSumValuation

/-!
# Positive periodic coefficient cycles

The overlap coefficients of two positive exponent progressions have positive
cycle values at every shift.  The exact finite-prefix identity is inherited
from `PeriodicSums` and is the algebraic input for the parameter-two case.
-/

open scoped BigOperators

namespace StonehamNormality

theorem dependentCoefficient_periodic (r s n : ℕ) :
    dependentCoefficient r s (n + r * s) = dependentCoefficient r s n := by
  unfold dependentCoefficient
  have hr : r ∣ r * s := dvd_mul_right r s
  have hs : s ∣ r * s := dvd_mul_left s r
  have hrn : r ∣ n + r * s ↔ r ∣ n := by
    constructor
    · intro h
      simpa using Nat.dvd_sub h hr
    · intro h
      exact dvd_add h hr
  have hsn : s ∣ n + r * s ↔ s ∣ n := by
    constructor
    · intro h
      simpa using Nat.dvd_sub h hs
    · intro h
      exact dvd_add h hs
  simp only [hrn, hsn]

theorem dependentCoefficient_positive_in_cycle {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (t : ℕ) :
    ∃ j < r * s, 0 < dependentCoefficient r s (t + j + 1) := by
  let j := r - 1 - t % r
  have hm : t % r < r := Nat.mod_lt t hr
  have hjr : j < r := by dsimp [j]; omega
  have hrs : r ≤ r * s := Nat.le_mul_of_pos_right r hs
  refine ⟨j, hjr.trans_le hrs, ?_⟩
  have hid : t + j + 1 = (t / r + 1) * r := by
    have ht := Nat.mod_add_div t r
    have hj : j + 1 + t % r = r := by dsimp [j]; omega
    nlinarith
  have hdiv : r ∣ t + j + 1 := by rw [hid]; exact dvd_mul_left r (t / r + 1)
  unfold dependentCoefficient
  simp only [if_pos hdiv]
  omega

theorem blockNumerator_pos_of_nonnegative (A : ℕ → ℚ) (p : ℚ) (L t : ℕ)
    (hp : 0 < p) (hA : ∀ n, 0 ≤ A n)
    (hpos : ∃ j < L, 0 < A (t + j + 1)) :
    0 < blockNumerator A p L t := by
  unfold blockNumerator
  obtain ⟨j, hj, hjA⟩ := hpos
  apply Finset.sum_pos'
  · intro k hk
    exact mul_nonneg (hA _) (pow_nonneg hp.le _)
  · exact ⟨j, Finset.mem_range.mpr hj, mul_pos hjA (pow_pos hp _)⟩

theorem cycleValue_pos_of_nonnegative (A : ℕ → ℚ) (p : ℚ) (L t : ℕ)
    (hp : 1 < p) (hL : 0 < L) (hA : ∀ n, 0 ≤ A n)
    (hpos : ∃ j < L, 0 < A (t + j + 1)) :
    0 < cycleValue A p L t := by
  apply div_pos
  · exact blockNumerator_pos_of_nonnegative A p L t (by linarith) hA hpos
  · exact sub_pos.mpr (one_lt_pow₀ hp (Nat.ne_of_gt hL))

theorem dependent_cycleValue_pos {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (t : ℕ) :
    0 < cycleValue (fun k => (dependentCoefficient r s k : ℚ)) 2 (r * s) t := by
  apply cycleValue_pos_of_nonnegative _ _ _ _ (by norm_num) (Nat.mul_pos hr hs)
  · intro n
    positivity
  · obtain ⟨j, hj, hpos⟩ := dependentCoefficient_positive_in_cycle hr hs t
    exact ⟨j, hj, by exact_mod_cast hpos⟩

theorem dependent_cycleValue_ne_zero {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (t : ℕ) :
    cycleValue (fun k => (dependentCoefficient r s k : ℚ)) 2 (r * s) t ≠ 0 :=
  ne_of_gt (dependent_cycleValue_pos hr hs t)

theorem dependent_periodic_prefix {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (K : ℕ) :
    (∑ j ∈ Finset.range K, (dependentCoefficient r s (j + 1) : ℚ) / 2 ^ (j + 1)) =
      cycleValue (fun k => (dependentCoefficient r s k : ℚ)) 2 (r * s) 0 -
      cycleValue (fun k => (dependentCoefficient r s k : ℚ)) 2 (r * s) K / 2 ^ K := by
  simpa using periodic_sum_nat_base
    (fun k => (dependentCoefficient r s k : ℚ)) 2 (r * s) K
    (by norm_num) (Nat.mul_pos hr hs) (fun n => by rw [dependentCoefficient_periodic])

end StonehamNormality
