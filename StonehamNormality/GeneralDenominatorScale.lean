import StonehamNormality.AllPairDenominator
import StonehamNormality.GeneralDenominator

/-! Uniform denominator bounds on geometric intervals of digit positions. -/

noncomputable section
open Filter

namespace StonehamNormality

theorem frequency_den_lower_of_log (a J B n : ℕ) (h : ℤ) (r : ℚ)
    (ha : 2 ≤ a) (hh : h ≠ 0) (hB : J + h.natAbs ≤ B)
    (hn : (2 ^ (288 * a)) ^ B ≤ n)
    (hr : 2 ^ (Nat.log a n - J) ≤ r.den) :
    2 ^ (144 * B) ≤ ((h : ℚ) * r).den := by
  have ha2 : a ≤ 2 ^ a := Nat.lt_two_pow_self.le
  have hlog : 288 * B ≤ Nat.log a n := by
    apply Nat.le_log_of_pow_le (by omega)
    calc
      a ^ (288 * B) ≤ (2 ^ a) ^ (288 * B) := Nat.pow_le_pow_left ha2 _
      _ = (2 ^ (288 * a)) ^ B := by rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ ≤ n := hn
  have he : 144 * B + h.natAbs ≤ Nat.log a n - J := by omega
  have hbound : 2 ^ h.natAbs * 2 ^ (144 * B) ≤
      2 ^ h.natAbs * ((h : ℚ) * r).den := by
    calc
      _ = 2 ^ (144 * B + h.natAbs) := by rw [pow_add]; ac_rfl
      _ ≤ 2 ^ (Nat.log a n - J) := Nat.pow_le_pow_right (by omega) he
      _ ≤ r.den := hr
      _ ≤ h.natAbs * ((h : ℚ) * r).den := den_le_int_abs_mul_den h r hh
      _ ≤ 2 ^ h.natAbs * ((h : ℚ) * r).den :=
        Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
  exact Nat.le_of_mul_le_mul_left hbound (by positivity)

/-- A common choice of geometric scales works for every nonzero Fourier frequency.
Only the starting scale is allowed to depend on the frequency. -/
theorem pair_frequency_denominator_scales (b c d : ℕ)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hbc : Nat.Coprime b c) (hbd : Nat.Coprime b d) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ h : ℤ, h ≠ 0 → ∀ᶠ B : ℕ in atTop,
      ∀ n : ℕ, (2 ^ (288 * (M - 1))) ^ B ≤ n →
        n ≤ (2 ^ (288 * M)) ^ B →
      let q := ((h : ℚ) * (radixStonehamTruncation b c n +
        radixStonehamTruncation b d n)).den
      2 ^ (144 * B) ≤ q ∧ q ≤ 2 ^ (576 * M * B) ∧ Nat.Coprime b q ∧
        ∀ p : ℕ, p.Prime → p ∣ q → p ∣ c * d := by
  obtain ⟨a, J, ha, hgrowth⟩ := all_pair_denominator_growth b c d hb hc hd hbc hbd
  obtain ⟨N, hN⟩ := eventually_atTop.mp hgrowth
  refine ⟨a + 1, by omega, ?_⟩
  intro h hh
  filter_upwards [eventually_ge_atTop (max (max N (max c d)) (J + h.natAbs))] with B hB
  intro n hn hnu
  simp only [Nat.add_sub_cancel] at hn ⊢
  have hNB : N ≤ B := (Nat.le_max_left _ _).trans ((Nat.le_max_left _ _).trans hB)
  have hcdB : max c d ≤ B := (Nat.le_max_right _ _).trans ((Nat.le_max_left _ _).trans hB)
  have hJB : J + h.natAbs ≤ B := (Nat.le_max_right _ _).trans hB
  have hbase : 2 ≤ (2 : ℕ) ^ (288 * a) := by
    have hh := Nat.pow_le_pow_right (by omega : 0 < 2) (show 1 ≤ 288 * a by omega)
    simpa using hh
  have hBn : B ≤ n := calc
    B ≤ 2 ^ B := Nat.lt_two_pow_self.le
    _ ≤ (2 ^ (288 * a)) ^ B := Nat.pow_le_pow_left hbase _
    _ ≤ n := hn
  have hparts := pair_frequency_den_bounds b c d n h hc hd hbc hbd (hcdB.trans hBn)
  refine ⟨frequency_den_lower_of_log a J B n h _ ha hh hJB hn (hN n (hNB.trans hBn)),
    ?_, hparts.2.1, hparts.2.2⟩
  calc
    _ ≤ n ^ 2 := hparts.1
    _ ≤ ((2 ^ (288 * (a + 1))) ^ B) ^ 2 := Nat.pow_le_pow_left hnu _
    _ = 2 ^ (576 * (a + 1) * B) := by rw [← pow_mul, ← pow_mul]; congr 1; ring

end StonehamNormality
