import XiFamilySupport

/-!
# Unshifted rational Xi terms and their exact valuations
-/

noncomputable section
open scoped BigOperators Classical

namespace XiFamily

def unshiftedTerm (b c a m : ℕ) : ℚ :=
  if IsIndex a c m then 1 / ((m : ℚ) * (b : ℚ) ^ m) else 0

def unshiftedPrefix (b c a n : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (n + 1), unshiftedTerm b c a m

theorem unshiftedTerm_cast (b c a m : ℕ) :
    (unshiftedTerm b c a m : ℝ) = term b c a m := by
  unfold unshiftedTerm term
  split_ifs <;> simp

theorem unshiftedPrefix_cast (b c a n : ℕ) :
    (unshiftedPrefix b c a n : ℝ) = ∑ m ∈ Finset.range (n + 1), term b c a m := by
  simp [unshiftedPrefix, unshiftedTerm_cast]

theorem truncation_eq_pow_mul_unshiftedPrefix (b c a n : ℕ) (hb : 2 ≤ b) :
    truncation b c a n = (b : ℚ) ^ n * unshiftedPrefix b c a n := by
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  unfold truncation unshiftedPrefix
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := by simpa using Finset.mem_range.mp hm
  by_cases hs : IsIndex a c m
  · simp only [hs, ite_true, unshiftedTerm]
    rw [pow_sub₀ (b : ℚ) hb0 hmn]
    ring
  · simp [hs, unshiftedTerm]

theorem unshiftedTerm_eq_zero_of_not_index {b c a m : ℕ} (hm : ¬ IsIndex a c m) :
    unshiftedTerm b c a m = 0 := by simp [unshiftedTerm, hm]

theorem unshiftedTerm_ne_zero {b c a m : ℕ} (hb : 0 < b) (ha : 0 < a) (hc : 0 < c)
    (hm : IsIndex a c m) : unshiftedTerm b c a m ≠ 0 := by
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (isIndex_pos ha hc hm).ne'
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  simp only [unshiftedTerm, hm, ite_true]
  exact one_div_ne_zero (mul_ne_zero hm0 (pow_ne_zero _ hb0))

/-- A radix-unit factor contributes no valuation. -/
theorem unshiftedTerm_valuation {p b c a m : ℕ} [Fact p.Prime]
    (hb : 0 < b) (ha : 0 < a) (hc : 0 < c) (hpb : ¬ p ∣ b)
    (hm : IsIndex a c m) :
    padicValRat p (unshiftedTerm b c a m) = -(padicValNat p m : ℤ) := by
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (isIndex_pos ha hc hm).ne'
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  simp only [unshiftedTerm, hm, ite_true, one_div]
  rw [padicValRat.inv, padicValRat.mul hm0 (pow_ne_zero _ hb0), padicValRat.pow,
    padicValRat.of_nat, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpb]
  simp

/-- The exponent of the second generator is the exact denominator depth. -/
theorem unshiftedTerm_valuation_pair {p b c a : ℕ} [Fact p.Prime]
    (i k : ℕ) (hb : 0 < b) (ha : 0 < a) (hc : 0 < c)
    (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    padicValRat p (unshiftedTerm b c a (a ^ i * c ^ k)) =
      -(k : ℤ) * padicValNat p c := by
  rw [unshiftedTerm_valuation hb ha hc hpb (isIndex_mul_pow a c i k),
    padicValNat.mul (pow_ne_zero _ ha.ne') (pow_ne_zero _ hc.ne'),
    padicValNat.pow, padicValNat.pow, padicValNat.eq_zero_of_not_dvd hpa]
  push_cast
  ring

theorem truncation_valuation_eq_unshiftedPrefix {p b c a n : ℕ} [Fact p.Prime]
    (hb : 2 ≤ b) (hpb : ¬ p ∣ b) :
    padicValRat p (truncation b c a n) = padicValRat p (unshiftedPrefix b c a n) := by
  rw [truncation_eq_pow_mul_unshiftedPrefix b c a n hb]
  by_cases hprefix : unshiftedPrefix b c a n = 0
  · simp [hprefix]
  · have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
    rw [padicValRat.mul (pow_ne_zero _ hb0) hprefix, padicValRat.pow,
      padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpb]
    simp

/-- All reduced denominators in a finite rational combination divide one
explicit factor whose prime support is independent of the cutoff. -/
theorem rational_combination_den_dvd {ι : Type*} (J : Finset ι)
    (b : ℕ) (c a : ι → ℕ) (q : ι → ℚ) (q₀ : ℚ) (n : ℕ)
    (ha : ∀ j ∈ J, 2 ≤ a j) (hc : ∀ j ∈ J, 2 ≤ c j) :
    (q₀ * (b : ℚ) ^ n + ∑ j ∈ J, q j * truncation b (c j) (a j) n).den ∣
      q₀.den * ∏ j ∈ J, (q j).den * denominatorBound (a j) (c j) n := by
  apply (Rat.add_den_dvd_lcm _ _).trans
  apply Nat.lcm_dvd
  · have hd : (q₀ * (b : ℚ) ^ n).den ∣ q₀.den := by
      simpa using Rat.mul_den_dvd q₀ ((b : ℚ) ^ n)
    exact hd.trans (Nat.dvd_mul_right _ _)
  · apply sum_den_dvd_of_den_dvd
    intro j hj
    have hd : (q j * truncation b (c j) (a j) n).den ∣
        (q j).den * denominatorBound (a j) (c j) n :=
      (Rat.mul_den_dvd _ _).trans
        (Nat.mul_dvd_mul_left _ (truncation_den_dvd _ _ _ _ (ha j hj) (hc j hj)))
    exact hd.trans ((Finset.dvd_prod_of_mem
      (fun j => (q j).den * denominatorBound (a j) (c j) n) hj).trans
        (Nat.dvd_mul_left _ _))

theorem rational_combination_den_le {ι : Type*} (J : Finset ι)
    (b : ℕ) (c a : ι → ℕ) (q : ι → ℚ) (q₀ : ℚ) (n : ℕ)
    (ha : ∀ j ∈ J, 2 ≤ a j) (hc : ∀ j ∈ J, 2 ≤ c j) (hn : n ≠ 0) :
    (q₀ * (b : ℚ) ^ n + ∑ j ∈ J, q j * truncation b (c j) (a j) n).den ≤
      (q₀.den * ∏ j ∈ J, (q j).den) * n ^ (2 * J.card) := by
  have hpos : 0 < q₀.den * ∏ j ∈ J, (q j).den * denominatorBound (a j) (c j) n := by
    apply Nat.mul_pos q₀.den_pos
    apply Finset.prod_pos
    intro j hj
    exact Nat.mul_pos (q j).den_pos (denominatorBound_pos _ _ _ (ha j hj) (hc j hj))
  apply (Nat.le_of_dvd hpos (rational_combination_den_dvd J b c a q q₀ n ha hc)).trans
  calc
    _ ≤ q₀.den * ∏ j ∈ J, (q j).den * n ^ 2 := by
      apply Nat.mul_le_mul_left
      exact Finset.prod_le_prod' (fun j hj =>
        Nat.mul_le_mul_left _ (denominatorBound_le_square (a j) (c j) n hn))
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp [pow_mul, mul_assoc]

end XiFamily
