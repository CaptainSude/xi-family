import StonehamNormality.DependentSumDenominator
import StonehamNormality.GeneralArithmetic
import Mathlib.Data.Nat.Factorization.Basic

/-! Reindexing actual two-component truncations along their common parameter. -/

open scoped BigOperators

namespace StonehamNormality

theorem dependent_parameters_common_base {c d u v : ℕ}
    (hc : 2 ≤ c) (hd : 2 ≤ d) (hu : 0 < u) (hv : 0 < v)
    (heq : c ^ u = d ^ v) :
    ∃ a r s : ℕ, 2 ≤ a ∧ 0 < r ∧ 0 < s ∧ c = a ^ r ∧ d = a ^ s := by
  obtain ⟨a, hca, hda⟩ := Nat.exists_eq_pow_of_pow_eq_pow (Or.inl hu.ne') heq
  have hr : 0 < v / Nat.gcd u v := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, pow_zero] at hca
    omega
  have hs : 0 < u / Nat.gcd u v := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, pow_zero] at hda
    omega
  have ha : 2 ≤ a := by
    by_contra h
    have ha01 : a = 0 ∨ a = 1 := by omega
    rcases ha01 with rfl | rfl
    · simp [zero_pow hr.ne'] at hca
      omega
    · simp at hca
      omega
  exact ⟨a, v / Nat.gcd u v, u / Nat.gcd u v, ha, hr, hs, hca, hda⟩

theorem sum_Icc_multiples (f : ℕ → ℚ) {r : ℕ} (hr : 0 < r) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 (K / r), f (r * k)) =
      ∑ j ∈ Finset.Icc 1 K, if r ∣ j then f j else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun k _ => r * k)
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right r k⟩
    have h := (Nat.le_div_iff_mul_le hr).mp hk'.2
    nlinarith
  · intro k hk l hl heq
    exact Nat.eq_of_mul_eq_mul_left hr heq
  · intro j hj
    obtain ⟨hjK, hd⟩ := Finset.mem_filter.mp hj
    obtain ⟨k, rfl⟩ := hd
    have hk' := Finset.mem_Icc.mp hjK
    refine ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · by_contra h
      have : k = 0 := by omega
      simp [this] at hk'
    · apply (Nat.le_div_iff_mul_le hr).mpr
      simpa [mul_comm] using hk'.2
  · intro k hk
    rfl

theorem powerTruncation_common_power {a b r : ℕ} (hr : 0 < r) (n K : ℕ) :
    powerTruncation b (a ^ r) n (K / r) =
      ∑ j ∈ Finset.Icc 1 K,
        if r ∣ j then (b : ℚ) ^ (n - a ^ j) / (a : ℚ) ^ j else 0 := by
  rw [← sum_Icc_multiples (fun j => (b : ℚ) ^ (n - a ^ j) / (a : ℚ) ^ j) hr K]
  unfold powerTruncation
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Nat.cast_pow, pow_mul]

theorem pair_powerTruncation_common_coefficients {a b r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (n K : ℕ) :
    powerTruncation b (a ^ r) n (K / r) + powerTruncation b (a ^ s) n (K / s) =
      ∑ j ∈ Finset.Icc 1 K,
        (dependentCoefficient r s j : ℚ) * (b : ℚ) ^ (n - a ^ j) / (a : ℚ) ^ j := by
  rw [powerTruncation_common_power hr n K, powerTruncation_common_power hs n K,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  unfold dependentCoefficient
  split_ifs <;> simp <;> ring

theorem pair_powerTruncation_eq_scaled_prefix {a b r s : ℕ}
    (ha : 1 ≤ a) (hb : b ≠ 0) (hr : 0 < r) (hs : 0 < s)
    (n K : ℕ) (hwin : a ^ K ≤ n) :
    powerTruncation b (a ^ r) n (K / r) + powerTruncation b (a ^ s) n (K / s) =
      (b : ℚ) ^ n * dependentPrefix (dependentCoefficient r s) a b K := by
  rw [pair_powerTruncation_common_coefficients hr hs n K]
  unfold dependentPrefix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkK := (Finset.mem_Icc.mp hk).2
  have hkn : a ^ k ≤ n := (pow_le_pow_right₀ ha hkK).trans hwin
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hpow : (b : ℚ) ^ n = (b : ℚ) ^ (n - a ^ k) * (b : ℚ) ^ (a ^ k) := by
    rw [← pow_add, Nat.sub_add_cancel hkn]
  rw [hpow]
  field_simp

theorem dependentTwoPrefix_eq_dependentPrefix (A : ℕ → ℕ) (b K : ℕ) :
    dependentTwoPrefix A b K = dependentPrefix A 2 b K := by
  unfold dependentTwoPrefix dependentPrefix
  have hset : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

theorem padicValRat_radix_shift {p b : ℕ} [Fact p.Prime]
    (hb : b ≠ 0) (hpb : ¬ p ∣ b) (q : ℚ) (n : ℕ) :
    padicValRat p ((b : ℚ) ^ n * q) = padicValRat p q := by
  by_cases hq : q = 0
  · simp [hq]
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  rw [padicValRat.mul (pow_ne_zero _ hbq) hq]
  simp [padicValNat.eq_zero_of_not_dvd hpb]

theorem dependentCoefficient_last_index {r s K : ℕ}
    (hr : 0 < r) (hK : r ≤ K) :
    ∃ J : ℕ, 1 ≤ J ∧ J ≤ K ∧ K - J < r ∧ dependentCoefficient r s J ≠ 0 ∧
      ∀ k, J < k → k ≤ K → dependentCoefficient r s k = 0 := by
  classical
  let S := (Finset.Icc 1 K).filter (fun j => dependentCoefficient r s j ≠ 0)
  let m := K / r * r
  have hm : 1 ≤ m ∧ m ≤ K ∧ K - m < r := by
    have hmod := Nat.mod_lt K hr
    have heq := Nat.mod_add_div K r
    have heq' : K % r + K / r * r = K := by simpa [mul_comm] using heq
    dsimp [m]
    constructor
    · have hd : 1 ≤ K / r := (Nat.le_div_iff_mul_le hr).mpr (by simpa using hK)
      nlinarith
    · constructor <;> omega
  have hmA : dependentCoefficient r s m ≠ 0 := by
    have hrm : r ∣ m := dvd_mul_left r (K / r)
    simp only [dependentCoefficient, if_pos hrm]
    omega
  have hmS : m ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm.1, hm.2.1⟩, hmA⟩
  have hS : S.Nonempty := ⟨m, hmS⟩
  let J := S.max' hS
  have hJS := Finset.max'_mem S hS
  have hJmem := Finset.mem_filter.mp hJS
  have hmJ : m ≤ J := Finset.le_max' S m hmS
  have hJbounds := Finset.mem_Icc.mp hJmem.1
  refine ⟨J, hJbounds.1, hJbounds.2, by omega, hJmem.2, ?_⟩
  intro k hJk hkK
  by_contra hkA
  have hkS : k ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨by omega, hkK⟩, hkA⟩
  have hkJ : k ≤ J := Finset.le_max' S k hkS
  omega

theorem dependentPrefix_last_index (A : ℕ → ℕ) (a b J K : ℕ)
    (hJK : J ≤ K) (hzero : ∀ k, J < k → k ≤ K → A k = 0) :
    dependentPrefix A a b K = dependentPrefix A a b J := by
  unfold dependentPrefix
  symm
  apply Finset.sum_subset
  · intro k hk
    have h := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨h.1, h.2.trans hJK⟩
  · intro k hk hn
    have hk' := Finset.mem_Icc.mp hk
    have hJk : J < k := by
      by_contra h
      exact hn (Finset.mem_Icc.mpr ⟨hk'.1, by omega⟩)
    simp [hzero k hJk hk'.2]

end StonehamNormality
