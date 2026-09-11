import StonehamNormality.DependentSumTwo

/-! Explicit reduced-denominator lower bounds extracted from the finite valuation proofs. -/

namespace StonehamNormality

theorem prime_power_dvd_den_of_padicVal_le {p k : ℕ} [Fact p.Prime] (q : ℚ)
    (hv : padicValRat p q ≤ -(k : ℤ)) : p ^ k ∣ q.den := by
  apply (padicValNat_dvd_iff_le q.den_ne_zero).mpr
  unfold padicValRat at hv
  omega

theorem prime_power_le_den_of_padicVal_le {p k : ℕ} [Fact p.Prime] (q : ℚ)
    (hv : padicValRat p q ≤ -(k : ℤ)) : p ^ k ≤ q.den :=
  Nat.le_of_dvd q.pos (prime_power_dvd_den_of_padicVal_le q hv)

theorem dependentPrefix_odd_prime_denominator {p a b J r s : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : a ≠ 0) (hpa : p ∣ a) (hb : b ≠ 0)
    (hpb : ¬ p ∣ b) (hJ : 1 ≤ J) (hAJ : dependentCoefficient r s J ≠ 0) :
    p ^ (J * padicValNat p a) ≤ (dependentPrefix (dependentCoefficient r s) a b J).den := by
  letI : Fact p.Prime := ⟨hp⟩
  apply prime_power_le_den_of_padicVal_le
  rw [dependentPrefix_odd_prime hp hp2 ha hpa hb hpb hJ hAJ]
  push_cast
  ring_nf
  exact le_rfl

theorem dependentPrefix_two_high_denominator {a b J r s : ℕ}
    (ha : a ≠ 0) (hva : 2 ≤ padicValNat 2 a) (hb : b ≠ 0)
    (hpb : ¬ 2 ∣ b) (hJ : 1 ≤ J) (hAJ : dependentCoefficient r s J ≠ 0) :
    2 ^ (J * padicValNat 2 a - 1) ≤
      (dependentPrefix (dependentCoefficient r s) a b J).den := by
  apply prime_power_le_den_of_padicVal_le
  rw [dependentPrefix_two_high_valuation ha hva hb hpb hJ hAJ]
  have hcoeff := padicValNat_two_small_coefficient (dependentCoefficient_le_two r s J)
  have hprod : 1 ≤ J * padicValNat 2 a := by nlinarith
  rw [Nat.cast_sub hprod, Nat.cast_mul, Nat.cast_one]
  have hcoeff' : (padicValNat 2 (dependentCoefficient r s J) : ℤ) ≤ 1 := by
    exact_mod_cast hcoeff
  linarith

theorem dependent_two_denominator_growth {r s b : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hb : Odd b) (hb0 : b ≠ 0) :
    ∃ M K₀ : ℕ, ∀ K, K₀ ≤ K →
      2 ^ K ≤ 2 ^ M * (dependentTwoPrefix (dependentCoefficient r s) b K).den := by
  let C := fun t => cycleValue (fun k => (dependentCoefficient r s k : ℚ)) 2 (r * s) t
  have hperiod : ∀ n, C (n + r * s) = C n := by
    intro n
    exact cycleValue_periodic _ 2 (r * s) n
      (fun k => by rw [dependentCoefficient_periodic])
  obtain ⟨M, hM⟩ := periodic_padicValRat_bounded C (Nat.mul_pos hr hs) hperiod
  obtain ⟨K₀, hK₀⟩ := dependent_two_eventual_valuation hr hs hb hb0
  refine ⟨M, max K₀ M, ?_⟩
  intro K hK
  have hKK₀ : K₀ ≤ K := (Nat.le_max_left _ _).trans hK
  have hMK : M ≤ K := (Nat.le_max_right _ _).trans hK
  have hden : 2 ^ (K - M) ≤ (dependentTwoPrefix (dependentCoefficient r s) b K).den := by
    apply prime_power_le_den_of_padicVal_le
    rw [hK₀ K hKK₀, Nat.cast_sub hMK]
    have hbound := hM K
    change padicValRat 2 (C K) - (K : ℤ) ≤ -((K : ℤ) - M)
    linarith
  have hpow : (2 : ℕ) ^ K = 2 ^ M * 2 ^ (K - M) := by
    rw [← pow_add, Nat.add_sub_of_le hMK]
  rw [hpow]
  exact Nat.mul_le_mul_left _ hden

end StonehamNormality
