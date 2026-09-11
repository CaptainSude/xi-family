import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

/-!
# Exact formulas for periodic rational coefficients

The cycle value packages one full period as a rational geometric sum.
Its first-order recurrence gives an exact finite-prefix identity. Everything in
this file is finite algebra; no convergence or unproved normality input is used.
-/

open scoped BigOperators

namespace StonehamNormality

/-- A finite coefficient block after clearing its radix denominator. -/
def blockNumerator (a : ℕ → ℚ) (p : ℚ) (L r : ℕ) : ℚ :=
  ∑ j ∈ Finset.range L, a (r + j + 1) * p ^ (L - 1 - j)

/-- The rational value of the repeating block beginning just after position `r`. -/
def cycleValue (a : ℕ → ℚ) (p : ℚ) (L r : ℕ) : ℚ :=
  blockNumerator a p L r / (p ^ L - 1)

/-- Append one coefficient to a finite block. -/
theorem blockNumerator_succ (a : ℕ → ℚ) (p : ℚ) (L r : ℕ) :
    blockNumerator a p (L + 1) r =
      p * blockNumerator a p L r + a (r + L + 1) := by
  unfold blockNumerator
  rw [Finset.sum_range_succ]
  have heq :
      (∑ j ∈ Finset.range L, a (r + j + 1) * p ^ (L + 1 - 1 - j)) =
        p * ∑ j ∈ Finset.range L, a (r + j + 1) * p ^ (L - 1 - j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjL := Finset.mem_range.mp hj
    have hexp : L + 1 - 1 - j = (L - 1 - j) + 1 := by omega
    rw [hexp, pow_succ]
    ring
  rw [heq]
  simp

/-- Remove the first coefficient from a finite block. -/
theorem blockNumerator_succ_front (a : ℕ → ℚ) (p : ℚ) (L r : ℕ) :
    blockNumerator a p (L + 1) r =
      a (r + 1) * p ^ L + blockNumerator a p L (r + 1) := by
  unfold blockNumerator
  rw [Finset.sum_range_succ']
  have heq (j : ℕ) :
      a (r + (j + 1) + 1) * p ^ (L + 1 - 1 - (j + 1)) =
        a (r + 1 + j + 1) * p ^ (L - 1 - j) := by
    congr 2 <;> omega
  simp_rw [heq]
  simp
  ring

/-- Periodicity closes the first-order recurrence for a whole block. -/
theorem blockNumerator_periodic_recurrence (a : ℕ → ℚ) (p : ℚ) (L r : ℕ)
    (hperiod : ∀ n : ℕ, a (n + L) = a n) :
    p * blockNumerator a p L r =
      a (r + 1) * (p ^ L - 1) + blockNumerator a p L (r + 1) := by
  have hlast : a (r + L + 1) = a (r + 1) := by
    simpa only [Nat.add_right_comm r L 1] using hperiod (r + 1)
  have hback := blockNumerator_succ a p L r
  have hfront := blockNumerator_succ_front a p L r
  rw [hlast] at hback
  linarith

/-- The cycle value satisfies the expected digit-shift recurrence. -/
theorem cycleValue_recurrence (a : ℕ → ℚ) (p : ℚ) (L r : ℕ)
    (hperiod : ∀ n : ℕ, a (n + L) = a n) (hden : p ^ L - 1 ≠ 0) :
    p * cycleValue a p L r = a (r + 1) + cycleValue a p L (r + 1) := by
  unfold cycleValue
  rw [← mul_div_assoc, blockNumerator_periodic_recurrence a p L r hperiod,
    add_div, mul_div_cancel_right₀ _ hden]

/-- Clearing denominators gives an exact identity for every finite prefix.
Equivalently, the unscaled prefix is `C₀ - p⁻ᴷ C_K` when `p` is nonzero. -/
theorem cycleValue_scaled_prefix (a : ℕ → ℚ) (p : ℚ) (L K : ℕ)
    (hperiod : ∀ n : ℕ, a (n + L) = a n) (hden : p ^ L - 1 ≠ 0) :
    p ^ K * cycleValue a p L 0 =
      blockNumerator a p K 0 + cycleValue a p L K := by
  induction K with
  | zero => simp [blockNumerator]
  | succ K ih =>
    calc
      p ^ (K + 1) * cycleValue a p L 0 =
          p * (p ^ K * cycleValue a p L 0) := by rw [pow_succ]; ring
      _ = p * (blockNumerator a p K 0 + cycleValue a p L K) := by rw [ih]
      _ = p * blockNumerator a p K 0 +
          (a (K + 1) + cycleValue a p L (K + 1)) := by
            rw [mul_add, cycleValue_recurrence a p L K hperiod hden]
      _ = blockNumerator a p (K + 1) 0 + cycleValue a p L (K + 1) := by
        rw [blockNumerator_succ]
        simp only [zero_add]
        ring

/-- The cycle value has the same period as its coefficient sequence. -/
theorem cycleValue_periodic (a : ℕ → ℚ) (p : ℚ) (L r : ℕ)
    (hperiod : ∀ n : ℕ, a (n + L) = a n) :
    cycleValue a p L (r + L) = cycleValue a p L r := by
  unfold cycleValue blockNumerator
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hindex : r + L + j + 1 = (r + j + 1) + L := by omega
  rw [hindex, hperiod]

/-- Clearing the radix denominators in an ordinary finite prefix. -/
theorem blockNumerator_eq_scaled_sum (a : ℕ → ℚ) (p : ℚ) (K : ℕ)
    (hp : p ≠ 0) :
    blockNumerator a p K 0 =
      p ^ K * ∑ j ∈ Finset.range K, a (j + 1) / p ^ (j + 1) := by
  unfold blockNumerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [zero_add]
  have hjK := Finset.mem_range.mp hj
  have hpow : p ^ K = p ^ (K - 1 - j) * p ^ (j + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  field_simp [hp]

/-- The exact rational finite-prefix formula for periodic coefficients. -/
theorem periodic_sum_eq_cycle_difference (a : ℕ → ℚ) (p : ℚ) (L K : ℕ)
    (hperiod : ∀ n : ℕ, a (n + L) = a n)
    (hp : p ≠ 0) (hden : p ^ L - 1 ≠ 0) :
    (∑ j ∈ Finset.range K, a (j + 1) / p ^ (j + 1)) =
      cycleValue a p L 0 - cycleValue a p L K / p ^ K := by
  have h := cycleValue_scaled_prefix a p L K hperiod hden
  rw [blockNumerator_eq_scaled_sum a p K hp] at h
  apply (eq_sub_iff_add_eq).mpr
  apply (mul_right_cancel₀ (pow_ne_zero K hp))
  rw [add_mul, div_mul_cancel₀ _ (pow_ne_zero K hp)]
  nlinarith [h]

/-- For an integer radix at least two, a positive period has nonzero denominator. -/
theorem nat_base_cycle_den_ne_zero (p L : ℕ) (hp : 2 ≤ p) (hL : 0 < L) :
    (p : ℚ) ^ L - 1 ≠ 0 := by
  have hpNat : 1 < p := by omega
  have hpRat : (1 : ℚ) < p := by exact_mod_cast hpNat
  exact sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ hpRat (Nat.ne_of_gt hL)))

/-- The prefix formula specialized to ordinary integer radices and positive periods. -/
theorem periodic_sum_nat_base (a : ℕ → ℚ) (p L K : ℕ)
    (hp : 2 ≤ p) (hL : 0 < L) (hperiod : ∀ n : ℕ, a (n + L) = a n) :
    (∑ j ∈ Finset.range K, a (j + 1) / (p : ℚ) ^ (j + 1)) =
      cycleValue a p L 0 - cycleValue a p L K / (p : ℚ) ^ K := by
  apply periodic_sum_eq_cycle_difference a p L K hperiod
  · have hpNat : p ≠ 0 := by omega
    exact_mod_cast hpNat
  · exact nat_base_cycle_den_ne_zero p L hp hL

end StonehamNormality
