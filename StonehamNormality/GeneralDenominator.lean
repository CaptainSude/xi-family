import StonehamNormality.GeneralSeriesBridge
import Mathlib.Data.Nat.Log

/-! Size and prime-support bounds for the actual two-summand approximations. -/

noncomputable section
open Filter
open scoped Topology
namespace StonehamNormality

theorem int_mul_den_dvd (h : ℤ) (r : ℚ) : ((h : ℚ) * r).den ∣ r.den := by
  simpa using Rat.mul_den_dvd (h : ℚ) r

theorem den_le_int_abs_mul_den (h : ℤ) (r : ℚ) (hh : h ≠ 0) :
    r.den ≤ h.natAbs * ((h : ℚ) * r).den := by
  have hhq : (h : ℚ) ≠ 0 := by exact_mod_cast hh
  have heq : (h : ℚ)⁻¹ * ((h : ℚ) * r) = r := by field_simp
  have hdiv := Rat.mul_den_dvd (h : ℚ)⁻¹ ((h : ℚ) * r)
  rw [heq, Rat.inv_intCast_den, if_neg hh] at hdiv
  exact Nat.le_of_dvd (Nat.mul_pos (Int.natAbs_pos.mpr hh) (Rat.den_pos _)) hdiv

theorem pair_frequency_den_bounds (b c d n : ℕ) (h : ℤ)
    (hc : 2 ≤ c) (hd : 2 ≤ d) (hbc : Nat.Coprime b c) (hbd : Nat.Coprime b d)
    (hn : max c d ≤ n) :
    let q := ((h : ℚ) * (radixStonehamTruncation b c n + radixStonehamTruncation b d n)).den
    q ≤ n ^ 2 ∧ Nat.Coprime b q ∧
      ∀ p : ℕ, p.Prime → p ∣ q → p ∣ c * d := by
  dsimp only
  have hcn : c ≤ n := (Nat.le_max_left _ _).trans hn
  have hdn : d ≤ n := (Nat.le_max_right _ _).trans hn
  have hnpos : 0 < n := by omega
  have hK : 1 ≤ Nat.log c n := Nat.log_pos (by omega) hcn
  have hL : 1 ≤ Nat.log d n := Nat.log_pos (by omega) hdn
  have hdc : (radixStonehamTruncation b c n).den = c ^ Nat.log c n := by
    rw [radixStonehamTruncation_eq_powerTruncation_log b c n hc hnpos]
    exact powerTruncation_denominator b c n _ (by omega) hK hbc
  have hdd : (radixStonehamTruncation b d n).den = d ^ Nat.log d n := by
    rw [radixStonehamTruncation_eq_powerTruncation_log b d n hd hnpos]
    exact powerTruncation_denominator b d n _ (by omega) hL hbd
  have hdiv : ((h : ℚ) * (radixStonehamTruncation b c n + radixStonehamTruncation b d n)).den ∣
      c ^ Nat.log c n * d ^ Nat.log d n := by
    apply (int_mul_den_dvd h _).trans
    simpa only [hdc, hdd] using Rat.add_den_dvd (radixStonehamTruncation b c n)
      (radixStonehamTruncation b d n)
  refine ⟨?_, ?_, ?_⟩
  · have hpos : 0 < c ^ Nat.log c n * d ^ Nat.log d n := by positivity
    calc
      _ ≤ c ^ Nat.log c n * d ^ Nat.log d n := Nat.le_of_dvd hpos hdiv
      _ ≤ n * n := Nat.mul_le_mul (Nat.pow_log_le_self c hnpos.ne')
        (Nat.pow_log_le_self d hnpos.ne')
      _ = n ^ 2 := (pow_two n).symm
  · exact ((hbc.pow_right _).mul_right (hbd.pow_right _)).of_dvd_right hdiv
  · intro p hp hpq
    rcases hp.dvd_mul.mp (hpq.trans hdiv) with hpc | hpd
    · exact (hp.dvd_of_dvd_pow hpc).trans (dvd_mul_right c d)
    · exact (hp.dvd_of_dvd_pow hpd).trans (dvd_mul_left d c)

end StonehamNormality
