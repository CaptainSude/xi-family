import XiFamilyRational

/-!
# Clearing radix primes in logarithmic time

Multiplication by `b^t` removes every radix prime from a rational denominator
once `t` exceeds its binary logarithm. The denominator can only decrease.
An explicit logarithmic buffer is provided for polynomial denominator bounds.
-/

noncomputable section
open scoped BigOperators Classical

namespace XiFamily

theorem radix_mul_den_dvd (b t : ℕ) (q : ℚ) :
    ((b : ℚ) ^ t * q).den ∣ q.den := by
  simpa using Rat.mul_den_dvd ((b : ℚ) ^ t) q

theorem radix_mul_den_le (b t : ℕ) (q : ℚ) :
    ((b : ℚ) ^ t * q).den ≤ q.den :=
  Nat.le_of_dvd q.den_pos (radix_mul_den_dvd b t q)

theorem valuation_nonneg_not_dvd_den {p : ℕ} (hp : p.Prime) (q : ℚ)
    (hv : 0 ≤ padicValRat p q) : ¬ p ∣ q.den := by
  have : Fact p.Prime := ⟨hp⟩
  intro hd
  have hpos : 0 < padicValNat p q.den := one_le_padicValNat_of_dvd q.den_ne_zero hd
  have hnum : padicValInt p q.num = 0 := by
    rcases Rat.num_or_den_zero_padicVal q hp with h | h
    · exact h
    · omega
  rw [padicValRat_def, hnum] at hv
  omega

theorem radix_mul_den_coprime (b t : ℕ) (q : ℚ) (hb : 2 ≤ b)
    (ht : Nat.log 2 q.den ≤ t) : Nat.Coprime b (((b : ℚ) ^ t * q).den) := by
  by_cases hq : q = 0
  · subst q
    simp
  apply Nat.coprime_of_dvd
  intro p hp hpb hpd
  have : Fact p.Prime := ⟨hp⟩
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hpbval : 1 ≤ padicValNat p b :=
    one_le_padicValNat_of_dvd (by omega) hpb
  have hdenval : padicValNat p q.den ≤ t := by
    calc
      _ ≤ Nat.log p q.den := padicValNat_le_nat_log q.den
      _ ≤ Nat.log 2 q.den := Nat.log_mono (by norm_num) hp.two_le le_rfl
      _ ≤ t := ht
  have hv : 0 ≤ padicValRat p ((b : ℚ) ^ t * q) := by
    rw [padicValRat.mul (pow_ne_zero _ hb0) hq, padicValRat.pow, padicValRat.of_nat,
      padicValRat_def]
    have hmul : (t : ℤ) ≤ (t : ℤ) * (padicValNat p b : ℤ) := by
      have hvb : (1 : ℤ) ≤ padicValNat p b := by exact_mod_cast hpbval
      nlinarith
    have hd : (padicValNat p q.den : ℤ) ≤ t := by exact_mod_cast hdenval
    have hnum : (0 : ℤ) ≤ padicValInt p q.num := by positivity
    omega
  exact valuation_nonneg_not_dvd_den hp _ hv hpd

def polynomialClearingBuffer (C A n : ℕ) : ℕ :=
  (Nat.log 2 C + 1) + A * (Nat.log 2 n + 1)

theorem log_polynomial_le_buffer (C A n : ℕ) :
    Nat.log 2 (C * n ^ A) ≤ polynomialClearingBuffer C A n := by
  have hC : C ≤ 2 ^ (Nat.log 2 C + 1) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) C).le
  have hn : n ≤ 2 ^ (Nat.log 2 n + 1) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n).le
  have hpow : C * n ^ A ≤ 2 ^ polynomialClearingBuffer C A n := by
    calc
      _ ≤ 2 ^ (Nat.log 2 C + 1) * (2 ^ (Nat.log 2 n + 1)) ^ A :=
        Nat.mul_le_mul hC (Nat.pow_le_pow_left hn A)
      _ = _ := by
        rw [← pow_mul, ← pow_add]
        congr 1
        simp [polynomialClearingBuffer, Nat.mul_comm]
  exact (Nat.log_mono_right hpow).trans_eq (Nat.log_pow (by norm_num) _)

theorem polynomial_den_cleared (b C A n t : ℕ) (q : ℚ) (hb : 2 ≤ b)
    (hq : q.den ≤ C * n ^ A) (ht : polynomialClearingBuffer C A n ≤ t) :
    Nat.Coprime b (((b : ℚ) ^ t * q).den) ∧
      ((b : ℚ) ^ t * q).den ≤ C * n ^ A := by
  refine ⟨radix_mul_den_coprime b t q hb ?_, (radix_mul_den_le b t q).trans hq⟩
  exact ((Nat.log_mono_right hq).trans (log_polynomial_le_buffer C A n)).trans ht

/-- Clearing deletes radix primes from any previously fixed finite prime set. -/
theorem polynomial_den_cleared_support (b C A n t : ℕ) (q : ℚ) (S : Finset ℕ)
    (hb : 2 ≤ b) (hq : q.den ≤ C * n ^ A)
    (ht : polynomialClearingBuffer C A n ≤ t)
    (hS : ∀ p : ℕ, p.Prime → p ∣ q.den → p ∈ S) :
    ∀ p : ℕ, p.Prime → p ∣ ((b : ℚ) ^ t * q).den →
      p ∈ S.filter (fun p => ¬ p ∣ b) := by
  intro p hp hpd
  have hcop := (polynomial_den_cleared b C A n t q hb hq ht).1
  refine Finset.mem_filter.mpr ⟨hS p hp (hpd.trans (radix_mul_den_dvd b t q)), ?_⟩
  intro hpb
  have hdiv : p ∣ 1 := by simpa [hcop.gcd_eq_one] using Nat.dvd_gcd hpb hpd
  exact hp.not_dvd_one hdiv

/-- A single integer containing every possible denominator prime of the
finite rational combination, independently of the cutoff. -/
def combinationPrimeContainer {ι : Type*} (J : Finset ι) (a c : ι → ℕ)
    (q : ι → ℚ) (q₀ : ℚ) : ℕ :=
  q₀.den * ∏ j ∈ J, (q j).den * (a j * c j)

theorem combinationPrimeContainer_pos {ι : Type*} (J : Finset ι) (a c : ι → ℕ)
    (q : ι → ℚ) (q₀ : ℚ) (ha : ∀ j ∈ J, 2 ≤ a j) (hc : ∀ j ∈ J, 2 ≤ c j) :
    0 < combinationPrimeContainer J a c q q₀ := by
  apply Nat.mul_pos q₀.den_pos
  apply Finset.prod_pos
  intro j hj
  apply Nat.mul_pos (q j).den_pos
  exact Nat.mul_pos (by have := ha j hj; omega) (by have := hc j hj; omega)

theorem rational_combination_den_prime {ι : Type*} (J : Finset ι)
    (b : ℕ) (c a : ι → ℕ) (q : ι → ℚ) (q₀ : ℚ) (n p : ℕ)
    (ha : ∀ j ∈ J, 2 ≤ a j) (hc : ∀ j ∈ J, 2 ≤ c j) (hp : p.Prime)
    (hpd : p ∣
      (q₀ * (b : ℚ) ^ n + ∑ j ∈ J, q j * truncation b (c j) (a j) n).den) :
    p ∣ combinationPrimeContainer J a c q q₀ := by
  have hbound := hpd.trans (rational_combination_den_dvd J b c a q q₀ n ha hc)
  rcases hp.dvd_mul.mp hbound with hzero | hprod
  · exact hzero.trans (Nat.dvd_mul_right _ _)
  · obtain ⟨j, hj, hterm⟩ := (hp.prime.dvd_finsetProd_iff _).mp hprod
    have hgen : p ∣ (q j).den * (a j * c j) := by
      rcases hp.dvd_mul.mp hterm with hqj | hD
      · exact hqj.trans (Nat.dvd_mul_right _ _)
      · rcases hp.dvd_mul.mp hD with ha' | hc'
        · exact ((hp.dvd_of_dvd_pow ha').trans (Nat.dvd_mul_right _ _)).trans
            (Nat.dvd_mul_left _ _)
        · exact ((hp.dvd_of_dvd_pow hc').trans (Nat.dvd_mul_left _ _)).trans
            (Nat.dvd_mul_left _ _)
    exact (hgen.trans (Finset.dvd_prod_of_mem (fun j => (q j).den * (a j * c j)) hj)).trans
      (Nat.dvd_mul_left _ _)

theorem rational_combination_den_prime_mem {ι : Type*} (J : Finset ι)
    (b : ℕ) (c a : ι → ℕ) (q : ι → ℚ) (q₀ : ℚ) (n p : ℕ)
    (ha : ∀ j ∈ J, 2 ≤ a j) (hc : ∀ j ∈ J, 2 ≤ c j) (hp : p.Prime)
    (hpd : p ∣
      (q₀ * (b : ℚ) ^ n + ∑ j ∈ J, q j * truncation b (c j) (a j) n).den) :
    p ∈ (combinationPrimeContainer J a c q q₀).primeFactors :=
  hp.mem_primeFactors (rational_combination_den_prime J b c a q q₀ n p ha hc hp hpd)
    (combinationPrimeContainer_pos J a c q q₀ ha hc).ne'

end XiFamily
