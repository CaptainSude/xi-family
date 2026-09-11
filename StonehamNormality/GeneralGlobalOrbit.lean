import StonehamNormality.GeneralModulusScale
import StonehamNormality.GeneralSupportConstants
import Mathlib.Data.Nat.Log

/-!
# Uniform character cancellation at global Stoneham scales

This module translates the modulus-scale estimate into the uniform geometric
bound used by the arbitrary-base normality transfer theorem.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace StonehamNormality

theorem modulus_log_scale_bounds (q B M : ℕ) (hq : q ≠ 0)
    (hql : 2 ^ (144 * B) ≤ q) (hqu : q ≤ 2 ^ (576 * M * B)) :
    let k := Nat.log (2 ^ 36) q
    4 * B ≤ k ∧ k ≤ 16 * M * B ∧
      2 ^ (36 * k) ≤ q ∧ q < 2 ^ (36 * (k + 1)) := by
  let k := Nat.log (2 ^ 36) q
  have hbase : 1 < (2 : ℕ) ^ 36 := by norm_num
  have hklo : 4 * B ≤ k := by
    apply Nat.le_log_of_pow_le hbase
    convert hql using 1
    rw [← pow_mul]
    congr 1
    ring
  have hlow : 2 ^ (36 * k) ≤ q := by
    simpa only [pow_mul] using Nat.pow_log_le_self (2 ^ 36) hq
  have hupp : q < 2 ^ (36 * (k + 1)) := by
    simpa only [pow_mul] using Nat.lt_pow_succ_log_self hbase q
  have hkhi : k ≤ 16 * M * B := by
    have h := (pow_le_pow_iff_right₀ (by norm_num : 1 < (2 : ℕ))).mp
      (hlow.trans hqu)
    have hh : 36 * k ≤ 36 * (16 * M * B) := by convert h using 1 <;> ring
    exact Nat.le_of_mul_le_mul_left hh (by norm_num)
  exact ⟨hklo, hkhi, hlow, hupp⟩

/-- Every fixed finite prime support has a uniform power saving at the global
scales needed for the Stoneham two-sum theorem. -/
theorem fixed_support_global_character_bound (b S M : ℕ)
    (hb : 1 < b) (hS : 0 < S) (hcop : b.Coprime S) (hM : 1 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (q : ℕ) [NeZero q] (A : ℤ) (t : ℕ),
        2 ^ (144 * B) ≤ q → q ≤ 2 ^ (576 * M * B) →
        (∀ p : ℕ, p.Prime → p ∣ q → p ∣ S) →
        IsUnit (A : ZMod q) → t ≤ (2 ^ (288 * M)) ^ B →
        ‖∑ i ∈ Finset.range t,
          ZMod.stdAddChar ((A : ZMod q) * (b : ZMod q) ^ i)‖ ≤
            K * ((2 : ℝ) ^ (288 * M - 1)) ^ B := by
  let C := supportStrideExponent S
  let D := b ^ C - 1
  let K₀ : ℝ := 2 * ((2 : ℝ) ^ 36 + 3)
  let K : ℝ := max 1 (Real.sqrt K₀)
  have hK0 : 0 ≤ K₀ := by dsimp [K₀]; positivity
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK : 0 ≤ K := zero_le_one.trans hK1
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (max (D ^ 4) (C * D)))] with B hB
  intro q _ A t hql hqu hsupport hA ht
  have hB1 : 1 ≤ B := (Nat.le_max_left _ _).trans hB
  have hBmax : max (D ^ 4) (C * D) ≤ B := (Nat.le_max_right _ _).trans hB
  have hBD : D ^ 4 ≤ B := (Nat.le_max_left _ _).trans hBmax
  have hBC : C * D ≤ B := (Nat.le_max_right _ _).trans hBmax
  have hBpow : B ≤ (2 : ℕ) ^ B := (Nat.lt_two_pow_self).le
  let k := Nat.log (2 ^ 36) q
  obtain ⟨hklo, hkhi, hkqlo, hkqhi⟩ :=
    modulus_log_scale_bounds q B M (NeZero.ne q) hql hqu
  change 4 * B ≤ k at hklo
  change k ≤ 16 * M * B at hkhi
  change 2 ^ (36 * k) ≤ q at hkqlo
  change q < 2 ^ (36 * (k + 1)) at hkqhi
  have hDscale : D ^ 4 ≤ 2 ^ (5 * k) :=
    hBD.trans (hBpow.trans (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hCscale : C * D ≤ 2 ^ (2 * k) :=
    hBC.trans (hBpow.trans (pow_le_pow_right₀ (by norm_num) (by omega)))
  have htarget : ((2 : ℝ) ^ (288 * M - 1)) ^ B =
      (2 : ℝ) ^ ((288 * M - 1) * B) := by rw [pow_mul]
  rw [htarget]
  by_cases hlong : 2 ^ (17 * k) ≤ t
  · have hbound := power_character_modulus_scale_bound b C q k t A hb
      (supportStrideExponent_pos hS).ne'
      (coprime_of_prime_support b S q hcop hsupport)
      (support_primes_dvd_base_pow_sub_one b S q hcop hsupport)
      (support_four_dvd_base_pow_sub_one b S q hcop hsupport) hA
      (by omega) hkqlo hkqhi hDscale hCscale hlong
    have hgain := norm_bound_of_integer_scaled_square
      (∑ i ∈ Finset.range t, ZMod.stdAddChar ((A : ZMod q) * (b : ZMod q) ^ i))
      B k t K₀ hK0 (by omega) hbound
    have htReal : (t : ℝ) ≤ (2 : ℝ) ^ (288 * M * B) := by
      rw [← pow_mul] at ht
      exact_mod_cast ht
    have hsplit : B + (288 * M - 1) * B = 288 * M * B := by
      have hm : 1 ≤ 288 * M := by omega
      rw [Nat.sub_mul, one_mul, Nat.add_sub_of_le]
      simpa only [one_mul] using Nat.mul_le_mul_right B hm
    have hmul : (2 : ℝ) ^ B *
        ‖∑ i ∈ Finset.range t, ZMod.stdAddChar ((A : ZMod q) * (b : ZMod q) ^ i)‖ ≤
        (2 : ℝ) ^ B * (K * (2 : ℝ) ^ ((288 * M - 1) * B)) := by
      calc
        _ ≤ Real.sqrt K₀ * t := hgain
        _ ≤ K * (2 : ℝ) ^ (288 * M * B) :=
          mul_le_mul (le_max_right _ _) htReal (Nat.cast_nonneg _) hK
        _ = _ := by rw [mul_left_comm, ← pow_add, hsplit]
    exact (mul_le_mul_iff_right₀ (show 0 < (2 : ℝ) ^ B by positivity)).mp hmul
  · have htshort : t ≤ 2 ^ (17 * k) := (Nat.lt_of_not_ge hlong).le
    have hexp : 17 * k ≤ (288 * M - 1) * B := by
      calc
        _ ≤ 17 * (16 * M * B) := Nat.mul_le_mul_left 17 hkhi
        _ = 272 * M * B := by ring
        _ ≤ (288 * M - 1) * B := Nat.mul_le_mul_right B (by omega)
    have htReal : (t : ℝ) ≤ (2 : ℝ) ^ ((288 * M - 1) * B) := by
      exact_mod_cast htshort.trans (pow_le_pow_right₀ (by norm_num) hexp)
    calc
      _ ≤ ∑ i ∈ Finset.range t,
          ‖ZMod.stdAddChar ((A : ZMod q) * (b : ZMod q) ^ i)‖ := norm_sum_le _ _
      _ = (t : ℝ) := by simp only [XiNormality.norm_stdAddChar, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, mul_one]
      _ ≤ (2 : ℝ) ^ ((288 * M - 1) * B) := htReal
      _ ≤ K * (2 : ℝ) ^ ((288 * M - 1) * B) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hK1
          (by positivity : 0 ≤ (2 : ℝ) ^ ((288 * M - 1) * B))

end StonehamNormality
