import StonehamNormality.DependentSumBridge

/-! Polynomially growing prime-power denominators on every common power window. -/

namespace StonehamNormality

theorem not_dvd_left_of_coprime_right {p a b : ℕ}
    (hp : p.Prime) (hba : Nat.Coprime b a) (hpa : p ∣ a) : ¬ p ∣ b := by
  intro hpb
  have h : p ∣ 1 := by simpa [hba.gcd_eq_one] using Nat.dvd_gcd hpb hpa
  exact hp.not_dvd_one h

theorem dependent_parameter_cases {a : ℕ} (ha : 2 ≤ a) :
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ a) ∨ a = 2 ∨ 2 ≤ padicValNat 2 a := by
  obtain ⟨e, m, hm, hae⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : a ≠ 0)
  have hm2 : ¬ 2 ∣ m := by
    simpa only [← even_iff_two_dvd, Nat.not_even_iff_odd] using hm
  by_cases hm1 : m = 1
  · have hapow : a = 2 ^ e := by simpa [hm1] using hae
    by_cases he1 : e = 1
    · exact Or.inr (Or.inl (by simpa [he1] using hapow))
    · right
      right
      have he0 : e ≠ 0 := by
        intro he
        simp [he] at hapow
        omega
      rw [hapow, padicValNat.pow]
      norm_num
      omega
  · obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
    left
    refine ⟨p, hp, ?_, ?_⟩
    · intro he
      subst p
      exact hm2 hpm
    · rw [hae]
      exact dvd_mul_of_dvd_right hpm _

/-- Complete dependent-parameter denominator survival, uniformly in the digit shift.
The cutoff for `a^r` is `K/r` on the common `a`-power window. -/
theorem dependent_pair_all_windows {a b r s : ℕ}
    (ha : 2 ≤ a) (hb : 0 < b) (hr : 0 < r) (hs : 0 < s)
    (hba : Nat.Coprime b a) :
    ∃ p M K₀ : ℕ, p.Prime ∧ p ∣ a ∧
      ∀ K n : ℕ, K₀ ≤ K → a ^ K ≤ n →
        p ^ (K - M) ≤
          (powerTruncation b (a ^ r) n (K / r) +
            powerTruncation b (a ^ s) n (K / s)).den := by
  have ha0 : a ≠ 0 := by omega
  rcases dependent_parameter_cases ha with ⟨p, hp, hp2, hpa⟩ | ha2 | hva
  · letI : Fact p.Prime := ⟨hp⟩
    have hpb := not_dvd_left_of_coprime_right hp hba hpa
    have hva : 1 ≤ padicValNat p a := one_le_padicValNat_of_dvd ha0 hpa
    refine ⟨p, r, r, hp, hpa, ?_⟩
    intro K n hK hwin
    obtain ⟨J, hJ, hJK, hgap, hAJ, hzero⟩ := dependentCoefficient_last_index (s := s) hr hK
    apply prime_power_le_den_of_padicVal_le
    rw [pair_powerTruncation_eq_scaled_prefix (by omega : 1 ≤ a) hb.ne' hr hs n K hwin,
      padicValRat_radix_shift hb.ne' hpb,
      dependentPrefix_last_index _ a b J K hJK hzero,
      dependentPrefix_odd_prime hp hp2 ha0 hpa hb.ne' hpb hJ hAJ]
    have hg : K - r ≤ J := by omega
    have hvnat : K - r ≤ J * padicValNat p a := by nlinarith
    have hvint : ((K - r : ℕ) : ℤ) ≤ (J : ℤ) * padicValNat p a := by
      exact_mod_cast hvnat
    nlinarith
  · subst a
    have hpb := not_dvd_left_of_coprime_right Nat.prime_two hba (dvd_refl 2)
    have hbOdd : Odd b := by
      simpa only [← even_iff_two_dvd, Nat.not_even_iff_odd] using hpb
    let C := fun t => cycleValue (fun k => (dependentCoefficient r s k : ℚ)) 2 (r * s) t
    have hperiod : ∀ n, C (n + r * s) = C n := by
      intro n
      exact cycleValue_periodic _ 2 (r * s) n
        (fun k => by rw [dependentCoefficient_periodic])
    obtain ⟨M, hM⟩ := periodic_padicValRat_bounded C (Nat.mul_pos hr hs) hperiod
    obtain ⟨K₀, hK₀⟩ := dependent_two_eventual_valuation hr hs hbOdd hb.ne'
    refine ⟨2, M, max K₀ M, Nat.prime_two, dvd_refl 2, ?_⟩
    intro K n hK hwin
    have hKK₀ := (Nat.le_max_left K₀ M).trans hK
    have hMK := (Nat.le_max_right K₀ M).trans hK
    apply prime_power_le_den_of_padicVal_le
    rw [pair_powerTruncation_eq_scaled_prefix (by norm_num : 1 ≤ (2 : ℕ))
      hb.ne' hr hs n K hwin, padicValRat_radix_shift hb.ne' hpb,
      ← dependentTwoPrefix_eq_dependentPrefix,
      hK₀ K hKK₀, Nat.cast_sub hMK]
    have hbound := hM K
    change padicValRat 2 (C K) - (K : ℤ) ≤ -((K : ℤ) - M)
    linarith
  · have hpa : 2 ∣ a := dvd_of_one_le_padicValNat (by omega : 1 ≤ padicValNat 2 a)
    have hpb := not_dvd_left_of_coprime_right Nat.prime_two hba hpa
    refine ⟨2, r, r, Nat.prime_two, hpa, ?_⟩
    intro K n hK hwin
    obtain ⟨J, hJ, hJK, hgap, hAJ, hzero⟩ := dependentCoefficient_last_index (s := s) hr hK
    apply prime_power_le_den_of_padicVal_le
    rw [pair_powerTruncation_eq_scaled_prefix (by omega : 1 ≤ a) hb.ne' hr hs n K hwin,
      padicValRat_radix_shift hb.ne' hpb,
      dependentPrefix_last_index _ a b J K hJK hzero,
      dependentPrefix_two_high_valuation ha0 hva hb.ne' hpb hJ hAJ]
    have hcoeff := padicValNat_two_small_coefficient (dependentCoefficient_le_two r s J)
    have hg : K - r < J := by omega
    have hvnat : K - r + 1 ≤ J * padicValNat 2 a := by nlinarith
    have hvint : ((K - r : ℕ) : ℤ) + 1 ≤ (J : ℤ) * padicValNat 2 a := by
      exact_mod_cast hvnat
    have hcoeff' : (padicValNat 2 (dependentCoefficient r s J) : ℤ) ≤ 1 := by
      exact_mod_cast hcoeff
    linarith

/-- The denominator bound for the actual pair and its actual logarithmic cutoffs. -/
theorem dependent_pair_denominator_growth {b c d u v : ℕ}
    (hb : 0 < b) (hc : 2 ≤ c) (hd : 2 ≤ d) (hu : 0 < u) (hv : 0 < v)
    (hbc : Nat.Coprime b c) (hdep : c ^ u = d ^ v) :
    ∃ a p M N : ℕ, 2 ≤ a ∧ p.Prime ∧ p ∣ a ∧
      ∀ n : ℕ, N ≤ n → p ^ (Nat.log a n - M) ≤
        (powerTruncation b c n (Nat.log c n) +
          powerTruncation b d n (Nat.log d n)).den := by
  obtain ⟨a, r, s, ha, hr, hs, hca, hda⟩ :=
    dependent_parameters_common_base hc hd hu hv hdep
  have hac : a ∣ c := by
    rw [hca]
    exact dvd_pow_self a hr.ne'
  have hba : Nat.Coprime b a := hbc.of_dvd_right hac
  obtain ⟨p, M, K₀, hp, hpa, hbound⟩ := dependent_pair_all_windows ha hb hr hs hba
  refine ⟨a, p, M, a ^ K₀, ha, hp, hpa, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := by
    have hpos : 0 < a ^ K₀ := pow_pos (by omega : 0 < a) _
    omega
  have hlog : K₀ ≤ Nat.log a n := Nat.le_log_of_pow_le (by omega : 1 < a) hn
  have hwin : a ^ Nat.log a n ≤ n := Nat.pow_log_le_self a hn0
  rw [hca, hda, Nat.log_pow_left, Nat.log_pow_left]
  exact hbound (Nat.log a n) n hlog hwin

end StonehamNormality
