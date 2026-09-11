import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases

/-!
# Denominator survival for dependent Stoneham parameters

Finite rational valuation arguments.  The coefficients may vanish.  A bound
strictly smaller than the valuation of the common parameter makes the final
nonzero term the unique term of least valuation.
-/

open scoped BigOperators

namespace StonehamNormality

theorem padicValRat_sum_lower_bound {ι : Type*} {p : ℕ} [Fact p.Prime]
    (s : Finset ι) (f : ι → ℚ) (v : ℤ)
    (hf : ∀ i ∈ s, f i ≠ 0 → v ≤ padicValRat p (f i))
    (hne : ∑ i ∈ s, f i ≠ 0) : v ≤ padicValRat p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hne
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha] at hne ⊢
      by_cases hfa : f a = 0
      · simp only [hfa, zero_add] at hne ⊢
        exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) hne
      by_cases hs : ∑ i ∈ s, f i = 0
      · simpa [hs] using hf a (Finset.mem_insert_self a s) hfa
      exact le_trans (le_min (hf a (Finset.mem_insert_self a s) hfa)
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) hs))
        (padicValRat.min_le_padicValRat_add hne)

theorem padicValRat_sum_eq_unique_min {ι : Type*} {p : ℕ} [Fact p.Prime]
    (s : Finset ι) (f : ι → ℚ) (j : ι) (hj : j ∈ s) (hfj : f j ≠ 0)
    (hmin : ∀ i ∈ s, i ≠ j → f i ≠ 0 →
      padicValRat p (f j) < padicValRat p (f i)) :
    padicValRat p (∑ i ∈ s, f i) = padicValRat p (f j) := by
  classical
  rw [← Finset.add_sum_erase s f hj]
  by_cases hs : ∑ i ∈ s.erase j, f i = 0
  · simp [hs]
  have hv : padicValRat p (f j) < padicValRat p (∑ i ∈ s.erase j, f i) := by
    have h := padicValRat_sum_lower_bound (p := p) (s.erase j) f
      (padicValRat p (f j) + 1) (by
        intro i hi hfi
        have hi' := Finset.mem_erase.mp hi
        exact hmin i hi'.2 hi'.1 hfi) hs
    omega
  have hsum : f j + ∑ i ∈ s.erase j, f i ≠ 0 := by
    intro hz
    have he : f j = -(∑ i ∈ s.erase j, f i) := (eq_neg_iff_add_eq_zero).mpr hz
    have heval := congrArg (padicValRat p) he
    rw [padicValRat.neg] at heval
    omega
  exact padicValRat.add_eq_of_lt hsum hfj hs hv

/-- A finite unshifted truncation with coefficients indexed from one. -/
def dependentPrefix (A : ℕ → ℕ) (a b J : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 J, (A k : ℚ) / ((a : ℚ) ^ k * (b : ℚ) ^ (a ^ k))

theorem dependent_term_valuation {p a b k : ℕ} [Fact p.Prime]
    (A : ℕ → ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hk : A k ≠ 0)
    (hbval : padicValNat p b = 0) :
    padicValRat p ((A k : ℚ) / ((a : ℚ) ^ k * (b : ℚ) ^ (a ^ k))) =
      (padicValNat p (A k) : ℤ) - k * padicValNat p a := by
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hk' : (A k : ℚ) ≠ 0 := by exact_mod_cast hk
  rw [padicValRat.div hk' (mul_ne_zero (pow_ne_zero _ ha') (pow_ne_zero _ hb')),
    padicValRat.mul (pow_ne_zero _ ha') (pow_ne_zero _ hb')]
  simp [hbval]

/-- Strictly separated coefficient valuations force the last term to survive. -/
theorem dependentPrefix_valuation {p a b J : ℕ} [Fact p.Prime]
    (A : ℕ → ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hJ : 1 ≤ J)
    (hAJ : A J ≠ 0) (hbval : padicValNat p b = 0)
    (hcoeff : ∀ k ∈ Finset.Icc 1 J, A k ≠ 0 →
      padicValNat p (A k) < padicValNat p a) :
    padicValRat p (dependentPrefix A a b J) =
      (padicValNat p (A J) : ℤ) - J * padicValNat p a := by
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  unfold dependentPrefix
  rw [padicValRat_sum_eq_unique_min (j := J)]
  · exact dependent_term_valuation A ha hb hAJ hbval
  · exact Finset.mem_Icc.mpr ⟨hJ, le_rfl⟩
  · exact div_ne_zero (by exact_mod_cast hAJ)
      (mul_ne_zero (pow_ne_zero _ ha') (pow_ne_zero _ hb'))
  · intro k hk hkj hterm
    have hkA : A k ≠ 0 := by
      intro hz
      simp [hz] at hterm
    rw [dependent_term_valuation A ha hb hAJ hbval,
      dependent_term_valuation A ha hb hkA hbval]
    have hcoeffJ := hcoeff J (Finset.mem_Icc.mpr ⟨hJ, le_rfl⟩) hAJ
    have hkJ : k + 1 ≤ J := by have := (Finset.mem_Icc.mp hk).2; omega
    have hcoeffJ' : (padicValNat p (A J) : ℤ) < padicValNat p a := by
      exact_mod_cast hcoeffJ
    have hkJ' : (k : ℤ) + 1 ≤ J := by exact_mod_cast hkJ
    have hmul := mul_le_mul_of_nonneg_right hkJ'
      (show (0 : ℤ) ≤ padicValNat p a by positivity)
    have hcoeffk : (0 : ℤ) ≤ padicValNat p (A k) := by positivity
    nlinarith

/-- The overlap coefficient of two arithmetic progressions of exponents. -/
def dependentCoefficient (r s k : ℕ) : ℕ :=
  (if r ∣ k then 1 else 0) + (if s ∣ k then 1 else 0)

theorem dependentCoefficient_le_two (r s k : ℕ) : dependentCoefficient r s k ≤ 2 := by
  unfold dependentCoefficient
  split_ifs <;> omega

theorem padicValNat_small_coefficient {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : n ≤ 2) (hn0 : n ≠ 0) : padicValNat p n = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  have hn12 : n = 1 ∨ n = 2 := by omega
  rcases hn12 with rfl | rfl
  · exact hp.not_dvd_one
  · intro h
    have := (Nat.dvd_prime Nat.prime_two).mp h
    rcases this with he | he
    · exact hp.ne_one he
    · exact hp2 he

theorem dependentPrefix_odd_prime {p a b J r s : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : a ≠ 0) (hpa : p ∣ a) (hb : b ≠ 0)
    (hpb : ¬ p ∣ b) (hJ : 1 ≤ J) (hAJ : dependentCoefficient r s J ≠ 0) :
    padicValRat p (dependentPrefix (dependentCoefficient r s) a b J) =
      -(J : ℤ) * padicValNat p a := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpa' := one_le_padicValNat_of_dvd ha hpa
  rw [dependentPrefix_valuation (dependentCoefficient r s) ha hb hJ hAJ
    (padicValNat.eq_zero_of_not_dvd hpb)]
  · rw [padicValNat_small_coefficient hp hp2 (dependentCoefficient_le_two r s J) hAJ]
    simp
  · intro k hk hkA
    rw [padicValNat_small_coefficient hp hp2 (dependentCoefficient_le_two r s k) hkA]
    omega

theorem padicValNat_two_small_coefficient {n : ℕ} (hn : n ≤ 2) :
    padicValNat 2 n ≤ 1 := by
  interval_cases n <;> norm_num

theorem dependentPrefix_two_high_valuation {a b J r s : ℕ}
    (ha : a ≠ 0) (hva : 2 ≤ padicValNat 2 a) (hb : b ≠ 0)
    (hpb : ¬ 2 ∣ b) (hJ : 1 ≤ J) (hAJ : dependentCoefficient r s J ≠ 0) :
    padicValRat 2 (dependentPrefix (dependentCoefficient r s) a b J) =
      (padicValNat 2 (dependentCoefficient r s J) : ℤ) - J * padicValNat 2 a := by
  apply dependentPrefix_valuation (dependentCoefficient r s) ha hb hJ hAJ
    (padicValNat.eq_zero_of_not_dvd hpb)
  intro k hk hkA
  have h := padicValNat_two_small_coefficient (dependentCoefficient_le_two r s k)
  omega

end StonehamNormality
