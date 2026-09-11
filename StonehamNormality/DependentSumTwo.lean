import StonehamNormality.DependentSumPeriodic
import Mathlib.Data.Nat.Periodic

/-!
# The exceptional common-parameter-two case

The radix perturbation is 2-integral.  The positive periodic cycle identity
therefore controls the eventual exact denominator valuation.
-/

open scoped BigOperators

namespace StonehamNormality

theorem two_pow_dvd_odd_pow_sub_one (b : ℤ) (hb : Odd b) (k : ℕ) :
    (2 : ℤ) ^ k ∣ b ^ (2 ^ k) - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hodd : Odd (b ^ (2 ^ k)) := hb.pow
      have htwo : (2 : ℤ) ∣ b ^ (2 ^ k) + 1 :=
        even_iff_two_dvd.mp (hodd.add_odd odd_one)
      have h := mul_dvd_mul ih htwo
      have hfactor : b ^ (2 ^ (k + 1)) - 1 =
          (b ^ (2 ^ k) - 1) * (b ^ (2 ^ k) + 1) := by
        rw [Nat.pow_succ, pow_mul]
        ring
      rw [pow_succ, hfactor]
      exact h

/-- No LTE theorem is necessary: a weaker elementary divisibility suffices. -/
theorem dependent_two_term_error_integral (A b k : ℕ) (hb : Odd b) (hb0 : b ≠ 0) :
    let E : ℚ := (A : ℚ) / ((2 : ℚ) ^ k * (b : ℚ) ^ (2 ^ k)) - A / 2 ^ k
    E = 0 ∨ 0 ≤ padicValRat 2 E := by
  dsimp only
  have hb' : Odd (b : ℤ) := by exact_mod_cast hb
  obtain ⟨z, hz⟩ := two_pow_dvd_odd_pow_sub_one (b : ℤ) hb' k
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
  have hzq : (b : ℚ) ^ (2 ^ k) - 1 = (2 : ℚ) ^ k * (z : ℚ) := by
    exact_mod_cast hz
  have he : (A : ℚ) / ((2 : ℚ) ^ k * (b : ℚ) ^ (2 ^ k)) - A / 2 ^ k =
      -((A : ℚ) * z) / (b : ℚ) ^ (2 ^ k) := by
    field_simp
    nlinarith [hzq]
  rw [he]
  by_cases hAz : -((A : ℚ) * z) = 0
  · left
    simp [hAz]
  right
  rw [padicValRat.div hAz (pow_ne_zero _ hbq), padicValRat.neg]
  have hpb : ¬ 2 ∣ b := by
    simpa only [← even_iff_two_dvd, Nat.not_even_iff_odd] using hb
  have hbval : padicValRat 2 (b : ℚ) = 0 := by
    simp [padicValNat.eq_zero_of_not_dvd hpb]
  rw [padicValRat.pow, hbval, mul_zero, sub_zero]
  have hi : (A : ℚ) * z = ((A : ℤ) * z : ℤ) := by push_cast; rfl
  rw [hi, padicValRat.of_int]
  positivity

def dependentTwoPlainPrefix (A : ℕ → ℕ) (K : ℕ) : ℚ :=
  ∑ j ∈ Finset.range K, (A (j + 1) : ℚ) / 2 ^ (j + 1)

def dependentTwoPrefix (A : ℕ → ℕ) (b K : ℕ) : ℚ :=
  ∑ j ∈ Finset.range K,
    (A (j + 1) : ℚ) / ((2 : ℚ) ^ (j + 1) * (b : ℚ) ^ (2 ^ (j + 1)))

theorem dependentTwoPrefix_error_integral (A : ℕ → ℕ) (b K : ℕ)
    (hb : Odd b) (hb0 : b ≠ 0) :
    dependentTwoPrefix A b K - dependentTwoPlainPrefix A K = 0 ∨
    0 ≤ padicValRat 2 (dependentTwoPrefix A b K - dependentTwoPlainPrefix A K) := by
  unfold dependentTwoPrefix dependentTwoPlainPrefix
  rw [← Finset.sum_sub_distrib]
  by_cases hzero : (∑ j ∈ Finset.range K,
      ((A (j + 1) : ℚ) / ((2 : ℚ) ^ (j + 1) * (b : ℚ) ^ (2 ^ (j + 1))) -
        A (j + 1) / 2 ^ (j + 1))) = 0
  · exact Or.inl hzero
  right
  apply padicValRat_sum_lower_bound _ _ 0 _ hzero
  intro j hj hne
  exact (dependent_two_term_error_integral (A (j + 1)) b (j + 1) hb hb0).resolve_left hne

theorem periodic_padicValRat_bounded (C : ℕ → ℚ) {L : ℕ} (hL : 0 < L)
    (hperiod : ∀ n, C (n + L) = C n) :
    ∃ M : ℕ, ∀ n, padicValRat 2 (C n) ≤ M := by
  refine ⟨(Finset.range L).sup (fun j => (padicValRat 2 (C j)).natAbs), ?_⟩
  intro n
  have hmod : C (n % L) = C n :=
    Function.Periodic.map_mod_nat hperiod n
  have hbound : (padicValRat 2 (C (n % L))).natAbs ≤
      (Finset.range L).sup (fun j => (padicValRat 2 (C j)).natAbs) :=
    Finset.le_sup (f := fun j => (padicValRat 2 (C j)).natAbs)
      (Finset.mem_range.mpr (Nat.mod_lt n hL))
  rw [hmod] at hbound
  have habs : padicValRat 2 (C n) ≤ ((padicValRat 2 (C n)).natAbs : ℤ) := Int.le_natAbs
  exact habs.trans (by exact_mod_cast hbound)

theorem padicValRat_add_eq_right_of_lt {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hy : y ≠ 0) (hx : x = 0 ∨ padicValRat p y < padicValRat p x) :
    padicValRat p (x + y) = padicValRat p y := by
  rcases hx with rfl | hv
  · simp
  by_cases hx0 : x = 0
  · simp [hx0]
  have hsum : y + x ≠ 0 := by
    intro h
    have he : y = -x := (eq_neg_iff_add_eq_zero).mpr h
    have hv' := congrArg (padicValRat p) he
    rw [padicValRat.neg] at hv'
    omega
  rw [add_comm]
  exact padicValRat.add_eq_of_lt hsum hy hx0 hv

/-- A nonzero periodic cycle cannot be destroyed by a uniformly integral error. -/
theorem periodic_cycle_valuation_survives (C T : ℕ → ℚ) {L : ℕ}
    (hL : 0 < L) (hperiod : ∀ n, C (n + L) = C n) (hC : ∀ n, C n ≠ 0)
    (herror : ∀ K, T K - (C 0 - C K / (2 : ℚ) ^ K) = 0 ∨
      0 ≤ padicValRat 2 (T K - (C 0 - C K / (2 : ℚ) ^ K))) :
    ∃ K₀ : ℕ, ∀ K, K₀ ≤ K →
      padicValRat 2 (T K) = padicValRat 2 (C K) - K := by
  obtain ⟨M, hM⟩ := periodic_padicValRat_bounded C hL hperiod
  refine ⟨M + (padicValRat 2 (C 0)).natAbs + 1, ?_⟩
  intro K hK
  let E := T K - (C 0 - C K / (2 : ℚ) ^ K)
  have hv0 : padicValRat 2 (C K) - (K : ℤ) < 0 := by
    have := hM K
    omega
  have hvC : padicValRat 2 (C K) - (K : ℤ) < padicValRat 2 (C 0) := by
    have hneg : -(padicValRat 2 (C 0)) ≤ ((-(padicValRat 2 (C 0))).natAbs : ℤ) :=
      Int.le_natAbs
    simp only [Int.natAbs_neg] at hneg
    have := hM K
    omega
  have htail : -(C K / (2 : ℚ) ^ K) ≠ 0 := by
    exact neg_ne_zero.mpr (div_ne_zero (hC K) (pow_ne_zero _ (by norm_num)))
  have htailval : padicValRat 2 (-(C K / (2 : ℚ) ^ K)) =
      padicValRat 2 (C K) - K := by
    rw [padicValRat.neg, padicValRat.div (hC K) (pow_ne_zero _ (by norm_num))]
    have htwo : padicValRat 2 (2 : ℚ) = 1 := by
      simpa using padicValRat.self (by norm_num : 1 < (2 : ℕ))
    rw [padicValRat.pow, htwo, mul_one]
  have hmain : padicValRat 2 (C 0 - C K / (2 : ℚ) ^ K) =
      padicValRat 2 (C K) - K := by
    rw [sub_eq_add_neg, padicValRat_add_eq_right_of_lt htail (Or.inr (by rwa [htailval]))]
    exact htailval
  have hmain0 : C 0 - C K / (2 : ℚ) ^ K ≠ 0 := by
    intro hz
    rw [hz, padicValRat.zero] at hmain
    omega
  have hE : E = 0 ∨ padicValRat 2 (C 0 - C K / (2 : ℚ) ^ K) < padicValRat 2 E := by
    rcases herror K with hz | hv
    · exact Or.inl hz
    · right
      rw [hmain]
      exact hv0.trans_le hv
  have heq : T K = E + (C 0 - C K / (2 : ℚ) ^ K) := by dsimp [E]; ring
  rw [heq, padicValRat_add_eq_right_of_lt hmain0 hE, hmain]

theorem dependent_two_eventual_valuation {r s b : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hb : Odd b) (hb0 : b ≠ 0) :
    ∃ K₀ : ℕ, ∀ K, K₀ ≤ K →
      padicValRat 2 (dependentTwoPrefix (dependentCoefficient r s) b K) =
        padicValRat 2 (cycleValue (fun k => (dependentCoefficient r s k : ℚ))
          2 (r * s) K) - K := by
  apply periodic_cycle_valuation_survives
    (C := fun t => cycleValue (fun k => (dependentCoefficient r s k : ℚ)) 2 (r * s) t)
    (T := fun K => dependentTwoPrefix (dependentCoefficient r s) b K)
    (Nat.mul_pos hr hs)
  · intro n
    exact cycleValue_periodic _ 2 (r * s) n
      (fun k => by rw [dependentCoefficient_periodic])
  · exact dependent_cycleValue_ne_zero hr hs
  · intro K
    rw [← dependent_periodic_prefix hr hs K]
    exact dependentTwoPrefix_error_integral (dependentCoefficient r s) b K hb hb0

end StonehamNormality
