import StonehamNormality.StonehamSeries

/-!
# Exact denominators of Stoneham truncations

The term at the largest retained prime power is the unique term of minimal
valuation. We prove this with an explicit integral numerator modulo the prime.
-/

noncomputable section
open scoped BigOperators Classical

namespace StonehamNormality

theorem stoneham_exponent_le {p n k K : ℕ} (hp : 1 < p)
    (hm : p ^ k ≤ n) (hn : n < p ^ (K + 1)) : k ≤ K := by
  have hk : k < K + 1 := (pow_lt_pow_iff_right₀ hp).mp (hm.trans_lt hn)
  omega

def stonehamNumerator (p n K : ℕ) : ℕ :=
  ∑ m ∈ (Finset.range (n + 1)).filter (IsStonehamIndex p),
    2 ^ (n - m) * p ^ (K - m.factorization p)

theorem stoneham_scaled_term {p n k K : ℕ} (hp : 0 < p) (hk : k ≤ K) :
    (p : ℚ) ^ K * ((2 : ℚ) ^ (n - p ^ k) / (p ^ k : ℕ)) =
      ((2 ^ (n - p ^ k) * p ^ (K - k) : ℕ) : ℚ) := by
  have hK : K = (K - k) + k := by omega
  nth_rw 1 [hK]
  simp only [pow_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

theorem stonehamTruncation_scaled_eq_numerator {p n K : ℕ}
    (hp : Nat.Prime p) (hn : n < p ^ (K + 1)) :
    (p : ℚ) ^ K * stonehamTruncation p n = (stonehamNumerator p n K : ℚ) := by
  classical
  unfold stonehamTruncation stonehamNumerator
  rw [Finset.mul_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  obtain ⟨k, hk, rfl⟩ := hm.2
  simp only [hp.factorization_pow, Finsupp.single_eq_same]
  exact stoneham_scaled_term (n := n) (k := k) hp.pos
    (stoneham_exponent_le (k := k) hp.one_lt (by omega) hn)

theorem stonehamNumerator_mod_prime {p n K : ℕ}
    (hp : Nat.Prime p) (hK : 1 ≤ K)
    (hlo : p ^ K ≤ n) (hhi : n < p ^ (K + 1)) :
    (stonehamNumerator p n K : ZMod p) = (2 : ZMod p) ^ (n - p ^ K) := by
  classical
  have htop : IsStonehamIndex p (p ^ K) := ⟨K, hK, rfl⟩
  unfold stonehamNumerator
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  calc
    _ = ∑ m ∈ (Finset.range (n + 1)).filter (IsStonehamIndex p),
        if m = p ^ K then (2 : ZMod p) ^ (n - p ^ K) else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm
      obtain ⟨k, hk, rfl⟩ := hm.2
      have hkK : k ≤ K := stoneham_exponent_le hp.one_lt (by omega) hhi
      simp only [hp.factorization_pow]
      by_cases he : k = K
      · subst k
        simp
      · have hpow : p ^ k ≠ p ^ K := by
          intro h
          have hlt : p ^ k < p ^ K := pow_lt_pow_right₀ hp.one_lt (by omega)
          exact hlt.ne h
        have hsub : K - k ≠ 0 := by omega
        simp [hpow, hsub]
    _ = _ := by simp [Finset.sum_ite_eq', htop, hlo]

theorem stonehamNumerator_not_dvd {p n K : ℕ}
    (hp : Nat.Prime p) (hcop : Nat.Coprime 2 p) (hK : 1 ≤ K)
    (hlo : p ^ K ≤ n) (hhi : n < p ^ (K + 1)) :
    ¬ p ∣ stonehamNumerator p n K := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff, stonehamNumerator_mod_prime hp hK hlo hhi]
  apply pow_ne_zero
  have hnd : ¬ p ∣ 2 := hp.coprime_iff_not_dvd.mp hcop.symm
  intro hz
  exact hnd ((ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hz))

theorem den_eq_prime_pow_of_scaled {p A K : ℕ} {r : ℚ}
    (hp : Nat.Prime p) (hr : (p : ℚ) ^ K * r = (A : ℚ)) (hA : ¬ p ∣ A) :
    r.den = p ^ K := by
  have hcop : Nat.Coprime A (p ^ K) := hp.coprime_pow_of_not_dvd hA
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hre : r = (A : ℚ) / p ^ K := by
    apply (eq_div_iff (pow_ne_zero _ hp0)).2
    simpa [mul_comm] using hr
  rw [hre]
  have hd := Rat.den_div_eq_of_coprime
    (a := (A : ℤ)) (b := ((p ^ K : ℕ) : ℤ))
    (by exact_mod_cast (pow_pos hp.pos K)) (by simpa using hcop)
  have hquot : (((A : ℤ) : ℚ) / (((p ^ K : ℕ) : ℤ) : ℚ)) =
      (A : ℚ) / (p : ℚ) ^ K := by
    rw [Int.cast_natCast, Int.cast_natCast, Nat.cast_pow]
  rw [hquot] at hd
  exact Int.ofNat_inj.mp hd

theorem stonehamTruncation_denominator {p n K : ℕ}
    (hp : Nat.Prime p) (hcop : Nat.Coprime 2 p) (hK : 1 ≤ K)
    (hlo : p ^ K ≤ n) (hhi : n < p ^ (K + 1)) :
    (stonehamTruncation p n).den = p ^ K := by
  exact den_eq_prime_pow_of_scaled hp (stonehamTruncation_scaled_eq_numerator hp hhi)
    (stonehamNumerator_not_dvd hp hcop hK hlo hhi)

theorem stonehamTruncation_exists_coprime_numerator {p n K : ℕ}
    (hp : Nat.Prime p) (hcop : Nat.Coprime 2 p) (hK : 1 ≤ K)
    (hlo : p ^ K ≤ n) (hhi : n < p ^ (K + 1)) :
    ∃ A : ℤ, stonehamTruncation p n = (A : ℚ) / (p : ℚ) ^ K ∧ ¬ (p : ℤ) ∣ A := by
  refine ⟨stonehamNumerator p n K, ?_, ?_⟩
  · apply (eq_div_iff (pow_ne_zero K (by exact_mod_cast hp.ne_zero : (p : ℚ) ≠ 0))).2
    simpa [mul_comm] using stonehamTruncation_scaled_eq_numerator hp hhi
  · exact_mod_cast stonehamNumerator_not_dvd hp hcop hK hlo hhi

theorem stonehamTruncation_add_of_power_window {p n t K : ℕ}
    (hp : 1 < p) (hlo : p ^ K ≤ n) (hhi : n + t < p ^ (K + 1)) :
    stonehamTruncation p (n + t) = (2 : ℚ) ^ t * stonehamTruncation p n := by
  apply stonehamTruncation_add_of_no_new_terms
  intro m hm hmn
  obtain ⟨k, hk, rfl⟩ := hm
  have hkK : k ≤ K := stoneham_exponent_le hp hmn hhi
  exact (pow_le_pow_right₀ (by omega : 1 ≤ p) hkK).trans hlo

theorem int_exists_prime_power_factor {p : ℕ} (hp : Nat.Prime p)
    {h : ℤ} (hh : h ≠ 0) :
    ∃ v : ℕ, ∃ u : ℤ, h = (p : ℤ) ^ v * u ∧ ¬ (p : ℤ) ∣ u := by
  have hf : FiniteMultiplicity (p : ℤ) h :=
    Int.finiteMultiplicity_iff.mpr ⟨by simpa using hp.ne_one, hh⟩
  obtain ⟨u, hu, hnu⟩ := hf.exists_eq_pow_mul_and_not_dvd
  exact ⟨multiplicity (p : ℤ) h, u, hu, hnu⟩

theorem intCast_isUnit_prime_pow {p : ℕ} (hp : Nat.Prime p)
    {A : ℤ} (hA : ¬ (p : ℤ) ∣ A) (K : ℕ) :
    IsUnit (A : ZMod (p ^ K)) := by
  have hn : ¬ p ∣ A.natAbs := by
    intro hd
    exact hA (Int.natCast_dvd.mpr hd)
  have hc : Nat.Coprime A.natAbs (p ^ K) := hp.coprime_pow_of_not_dvd hn
  have hu := (ZMod.isUnit_iff_coprime A.natAbs (p ^ K)).mpr hc
  rcases Int.natAbs_eq A with he | he
  · rw [he, Int.cast_natCast]
    exact hu
  · rw [he, Int.cast_neg, Int.cast_natCast]
    exact hu.neg

theorem stoneham_frequency_representation {p : ℕ}
    (hp : Nat.Prime p) (hcop : Nat.Coprime 2 p) (h : ℤ) (hh : h ≠ 0) :
    ∃ v : ℕ, ∀ n K : ℕ, v + 1 ≤ K → p ^ K ≤ n → n < p ^ (K + 1) →
      ∃ A : ℤ, ¬ (p : ℤ) ∣ A ∧
        (h : ℚ) * stonehamTruncation p n = (A : ℚ) / (p : ℚ) ^ (K - v) := by
  obtain ⟨v, u, hu, hnu⟩ := int_exists_prime_power_factor hp hh
  refine ⟨v, ?_⟩
  intro n K hK hlo hhi
  obtain ⟨A, hr, hA⟩ := stonehamTruncation_exists_coprime_numerator
    hp hcop (by omega) hlo hhi
  refine ⟨u * A, ?_, ?_⟩
  · intro hd
    exact ((Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hd).elim hnu hA
  · rw [hu, hr]
    push_cast
    have hK' : K = v + (K - v) := by omega
    conv_lhs => rw [hK', pow_add]
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    field_simp

theorem mixedNumerator_not_dvd_three {A B : ℤ} {k l : ℕ}
    (hA : ¬ (3 : ℤ) ∣ A) (hk : 1 ≤ k) :
    ¬ (3 : ℤ) ∣ A * 5 ^ l + B * 3 ^ k := by
  have hAnz : (A : ZMod 3) ≠ 0 := by
    intro hz
    exact hA ((ZMod.intCast_zmod_eq_zero_iff_dvd A 3).mp hz)
  have h5 : (5 : ZMod 3) ^ l ≠ 0 := pow_ne_zero _ (by decide)
  have h3 : (3 : ZMod 3) ^ k = 0 := by
    rw [show (3 : ZMod 3) = 0 by decide, zero_pow (by omega : k ≠ 0)]
  intro hd
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (A * 5 ^ l + B * 3 ^ k) 3).mpr hd
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at hz
  rw [h3, mul_zero, add_zero] at hz
  exact (mul_ne_zero hAnz h5) hz

theorem mixedNumerator_not_dvd_five {A B : ℤ} {k l : ℕ}
    (hB : ¬ (5 : ℤ) ∣ B) (hl : 1 ≤ l) :
    ¬ (5 : ℤ) ∣ A * 5 ^ l + B * 3 ^ k := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hBnz : (B : ZMod 5) ≠ 0 := by
    intro hz
    exact hB ((ZMod.intCast_zmod_eq_zero_iff_dvd B 5).mp hz)
  have h3unit : IsUnit (3 : ZMod 5) :=
    (ZMod.isUnit_iff_coprime 3 5).mpr (by norm_num)
  have h3 : (3 : ZMod 5) ^ k ≠ 0 := (h3unit.pow k).ne_zero
  have h5 : (5 : ZMod 5) ^ l = 0 := by
    rw [show (5 : ZMod 5) = 0 from ZMod.natCast_self 5, zero_pow (by omega : l ≠ 0)]
  intro hd
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (A * 5 ^ l + B * 3 ^ k) 5).mpr hd
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at hz
  rw [h5, mul_zero, zero_add] at hz
  exact (mul_ne_zero hBnz h3) hz

theorem intCast_isUnit_three_five {A : ℤ}
    (h3 : ¬ (3 : ℤ) ∣ A) (h5 : ¬ (5 : ℤ) ∣ A) (k l : ℕ) :
    IsUnit (A : ZMod (3 ^ k * 5 ^ l)) := by
  have h3n : ¬ 3 ∣ A.natAbs := by
    intro hd
    exact h3 (Int.natCast_dvd.mpr hd)
  have h5n : ¬ 5 ∣ A.natAbs := by
    intro hd
    exact h5 (Int.natCast_dvd.mpr hd)
  have hc3 : Nat.Coprime A.natAbs (3 ^ k) := Nat.prime_three.coprime_pow_of_not_dvd h3n
  have hc5 : Nat.Coprime A.natAbs (5 ^ l) :=
    (by norm_num : Nat.Prime 5).coprime_pow_of_not_dvd h5n
  have hu := (ZMod.isUnit_iff_coprime A.natAbs (3 ^ k * 5 ^ l)).mpr (hc3.mul_right hc5)
  rcases Int.natAbs_eq A with he | he
  · rw [he, Int.cast_natCast]
    exact hu
  · rw [he, Int.cast_neg, Int.cast_natCast]
    exact hu.neg

/-- Every fixed nonzero pair of integer frequencies loses only fixed powers
of three and five from the two rational denominators. -/
theorem stoneham_three_five_frequency_representation (u v : ℤ)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ a b : ℕ, ∀ n K L : ℕ,
      a + 1 ≤ K → b + 1 ≤ L →
      3 ^ K ≤ n → n < 3 ^ (K + 1) →
      5 ^ L ≤ n → n < 5 ^ (L + 1) →
      ∃ A : ℤ,
        IsUnit (A : ZMod (3 ^ (K - a) * 5 ^ (L - b))) ∧
        (u : ℚ) * stonehamTruncation 3 n + (v : ℚ) * stonehamTruncation 5 n =
          (A : ℚ) / ((3 : ℚ) ^ (K - a) * (5 : ℚ) ^ (L - b)) := by
  obtain ⟨a, ha⟩ := stoneham_frequency_representation Nat.prime_three (by norm_num) u hu
  obtain ⟨b, hb⟩ := stoneham_frequency_representation (by norm_num : Nat.Prime 5)
    (by norm_num) v hv
  refine ⟨a, b, ?_⟩
  intro n K L haK hbL h3lo h3hi h5lo h5hi
  obtain ⟨A, hA, hAr⟩ := ha n K haK h3lo h3hi
  obtain ⟨B, hB, hBr⟩ := hb n L hbL h5lo h5hi
  refine ⟨A * 5 ^ (L - b) + B * 3 ^ (K - a), ?_, ?_⟩
  · apply intCast_isUnit_three_five
    · exact mixedNumerator_not_dvd_three hA (by omega)
    · exact mixedNumerator_not_dvd_five hB (by omega)
  · rw [hAr, hBr]
    push_cast
    field_simp

theorem reduced_prime_power_bounds {p n K v : ℕ} (hp : 1 < p)
    (hv : v ≤ K) (hlo : p ^ K ≤ n) (hhi : n < p ^ (K + 1)) :
    p ^ (K - v) ≤ n ∧ n < p ^ (v + 1) * p ^ (K - v) := by
  constructor
  · exact (pow_le_pow_right₀ (by omega : 1 ≤ p) (Nat.sub_le K v)).trans hlo
  · have he : v + 1 + (K - v) = K + 1 := by omega
    rw [← pow_add, he]
    exact hhi

/-- A convenient eventual interface using the actual logarithmic cutoffs. -/
theorem stoneham_three_five_eventual_representation (u v : ℤ)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ a b : ℕ, ∀ n : ℕ, 3 ^ (a + 1) ≤ n → 5 ^ (b + 1) ≤ n →
      ∃ k l : ℕ, ∃ A : ℤ,
        1 ≤ k ∧ 1 ≤ l ∧
        3 ^ k ≤ n ∧ 5 ^ l ≤ n ∧
        n < 3 ^ (a + 1) * 3 ^ k ∧ n < 5 ^ (b + 1) * 5 ^ l ∧
        IsUnit (A : ZMod (3 ^ k * 5 ^ l)) ∧
        (u : ℚ) * stonehamTruncation 3 n + (v : ℚ) * stonehamTruncation 5 n =
          (A : ℚ) / ((3 : ℚ) ^ k * (5 : ℚ) ^ l) := by
  obtain ⟨a, b, hab⟩ := stoneham_three_five_frequency_representation u v hu hv
  refine ⟨a, b, ?_⟩
  intro n h3n h5n
  have hn0 : n ≠ 0 := by
    have hp : 0 < (3 : ℕ) ^ (a + 1) := by positivity
    omega
  let K := Nat.log 3 n
  let L := Nat.log 5 n
  have hKlo : 3 ^ K ≤ n := Nat.pow_log_le_self 3 hn0
  have hKhi : n < 3 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hLlo : 5 ^ L ≤ n := Nat.pow_log_le_self 5 hn0
  have hLhi : n < 5 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have haK : a + 1 ≤ K := Nat.le_log_of_pow_le (by norm_num) h3n
  have hbL : b + 1 ≤ L := Nat.le_log_of_pow_le (by norm_num) h5n
  obtain ⟨A, hA, hr⟩ := hab n K L haK hbL hKlo hKhi hLlo hLhi
  have h3bounds := reduced_prime_power_bounds (by norm_num : 1 < (3 : ℕ))
    (by omega : a ≤ K) hKlo hKhi
  have h5bounds := reduced_prime_power_bounds (by norm_num : 1 < (5 : ℕ))
    (by omega : b ≤ L) hLlo hLhi
  exact ⟨K - a, L - b, A, by omega, by omega,
    h3bounds.1, h5bounds.1, h3bounds.2, h5bounds.2, hA, hr⟩

/-- Scale bounds used by the two-stage correlation estimate. -/
theorem stoneham_three_five_scale_representation (u v : ℤ)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ B₀ : ℕ, ∀ B n : ℕ, B₀ ≤ B →
      2 ^ (18 * B) ≤ n → n ≤ 2 ^ (20 * B) →
      ∃ k l : ℕ, ∃ A : ℤ,
        1 ≤ k ∧ 1 ≤ l ∧
        2 ^ (17 * B) ≤ 3 ^ k ∧ 3 ^ k ≤ 2 ^ (20 * B) ∧
        2 ^ (17 * B) ≤ 5 ^ l ∧ 5 ^ l ≤ 2 ^ (20 * B) ∧
        IsUnit (A : ZMod (3 ^ k * 5 ^ l)) ∧
        (u : ℚ) * stonehamTruncation 3 n + (v : ℚ) * stonehamTruncation 5 n =
          (A : ℚ) / ((3 : ℚ) ^ k * (5 : ℚ) ^ l) := by
  obtain ⟨a, b, hab⟩ := stoneham_three_five_eventual_representation u v hu hv
  refine ⟨max (3 ^ (a + 1)) (5 ^ (b + 1)), ?_⟩
  intro B n hB hlo hhi
  have hB2 : B ≤ 2 ^ B := (show B < 2 ^ B from Nat.lt_two_pow_self).le
  have h3c : 3 ^ (a + 1) ≤ 2 ^ B := ((Nat.le_max_left _ _).trans hB).trans hB2
  have h5c : 5 ^ (b + 1) ≤ 2 ^ B := ((Nat.le_max_right _ _).trans hB).trans hB2
  have h2n : 2 ^ B ≤ n :=
    (pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) (by omega : B ≤ 18 * B)).trans hlo
  obtain ⟨k, l, A, hk, hl, h3n, h5n, h3low, h5low, hA, hr⟩ :=
    hab n (h3c.trans h2n) (h5c.trans h2n)
  have hpow18 : (2 : ℕ) ^ (18 * B) = 2 ^ B * 2 ^ (17 * B) := by
    rw [← pow_add]
    congr 1
    omega
  have h3lt : 2 ^ (17 * B) < 3 ^ k := by
    have hm := hlo.trans_lt (h3low.trans_le (Nat.mul_le_mul_right (3 ^ k) h3c))
    rw [hpow18] at hm
    exact Nat.lt_of_mul_lt_mul_left hm
  have h5lt : 2 ^ (17 * B) < 5 ^ l := by
    have hm := hlo.trans_lt (h5low.trans_le (Nat.mul_le_mul_right (5 ^ l) h5c))
    rw [hpow18] at hm
    exact Nat.lt_of_mul_lt_mul_left hm
  exact ⟨k, l, A, hk, hl, h3lt.le, h3n.trans hhi, h5lt.le, h5n.trans hhi, hA, hr⟩

end StonehamNormality
