import StonehamNormality.GeneralRadixSupport
import StonehamNormality.GeneralCharacterPhase
import StonehamNormality.GeneralDenominatorScale
import StonehamNormality.GeneralGlobalOrbit

/-! Final assembly of the two-summand Stoneham normality theorem. -/

noncomputable section

open Filter
open scoped BigOperators Topology Classical

namespace StonehamNormality

theorem rational_reduced_num_isUnit (r : ℚ) : IsUnit (r.num : ZMod r.den) := by
  have hunit : IsUnit (r.num.natAbs : ZMod r.den) :=
    (ZMod.isUnit_iff_coprime r.num.natAbs r.den).mpr r.reduced
  rcases Int.natAbs_eq r.num with he | he
  · rw [he, Int.cast_natCast]
    exact hunit
  · rw [he, Int.cast_neg, Int.cast_natCast]
    exact hunit.neg

theorem rational_reduced_representation (r : ℚ) : r = (r.num : ℚ) / r.den :=
  (Rat.num_div_den r).symm

theorem fourier_rational_radix_eq_reduced_char (b : ℕ) (h : ℤ) (r : ℚ) (t : ℕ) :
    let q := ((h : ℚ) * r).den
    letI : NeZero q := ⟨Rat.den_ne_zero _⟩
    fourier (T := 1) h ((((b : ℚ) ^ t * r : ℚ) : ℝ) : UnitAddCircle) =
      ZMod.stdAddChar ((((h : ℚ) * r).num : ZMod q) * (b : ZMod q) ^ t) := by
  dsimp only
  letI : NeZero ((h : ℚ) * r).den := ⟨Rat.den_ne_zero _⟩
  exact fourier_rational_radix_eq_stdAddChar b h _ r
    (rational_reduced_representation ((h : ℚ) * r)) t

theorem two_sum_scale_lt {M : ℕ} (hM : 1 ≤ M) :
    1 < (2 : ℕ) ^ (288 * M) ∧
    2 ^ (288 * (M - 1)) < 2 ^ (288 * M) ∧
    2 ^ (288 * M - 1) < 2 ^ (288 * M) := by
  constructor
  · exact one_lt_pow₀ (by norm_num) (by omega)
  constructor <;> apply pow_lt_pow_right₀ (by norm_num : 1 < (2 : ℕ)) <;> omega

theorem two_sum_normalInBase_of_character_scale_bound
    (b c d M : ℕ) (C : ℝ)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (hM : 1 ≤ M) (hC : 0 ≤ C)
    (hden : ∀ h : ℤ, h ≠ 0 → ∀ᶠ B : ℕ in atTop, ∀ n : ℕ,
      (2 ^ (288 * (M - 1))) ^ B ≤ n → n ≤ (2 ^ (288 * M)) ^ B →
      let q := ((h : ℚ) * (radixStonehamTruncation b c n + radixStonehamTruncation b d n)).den
      2 ^ (144 * B) ≤ q ∧ q ≤ 2 ^ (576 * M * B) ∧ Nat.Coprime b q ∧
        ∀ p : ℕ, p.Prime → p ∣ q → p ∣ c * d)
    (hchar : ∀ᶠ B : ℕ in atTop, ∀ (q : ℕ) [NeZero q] (A : ℤ) (t : ℕ),
      2 ^ (144 * B) ≤ q → q ≤ 2 ^ (576 * M * B) →
      (∀ p : ℕ, p.Prime → p ∣ q → p ∣ c * d) → IsUnit (A : ZMod q) →
      t ≤ (2 ^ (288 * M)) ^ B →
      ‖∑ i ∈ Finset.range t, ZMod.stdAddChar ((A : ZMod q) * (b : ZMod q) ^ i)‖ ≤
        C * ((2 : ℝ) ^ (288 * M - 1)) ^ B) :
    NormalInBase b (stonehamConstant b c + stonehamConstant b d) := by
  obtain ⟨hQ, hU, hV⟩ := two_sum_scale_lt hM
  have hnormal := stoneham_pair_normalInBase_of_orbit_bounds b c d 1 1 hb hc hd
    (2 ^ (288 * M)) (2 ^ (288 * (M - 1))) (2 ^ (288 * M - 1)) hQ hU hV
  apply (by simpa only [Rat.cast_one, one_mul] using hnormal)
  intro h hh
  refine ⟨C, hC, ?_⟩
  filter_upwards [hden h hh, hchar] with B hdenB hcharB
  intro n t hn hnt
  let r : ℚ := radixStonehamTruncation b c n + radixStonehamTruncation b d n
  let q : ℕ := ((h : ℚ) * r).den
  let A : ℤ := ((h : ℚ) * r).num
  letI : NeZero q := ⟨Rat.den_ne_zero _⟩
  obtain ⟨hqlo, hqhi, _, hqsupport⟩ := hdenB n hn (by omega)
  have hbound := hcharB q A t hqlo hqhi hqsupport
    (rational_reduced_num_isUnit ((h : ℚ) * r)) (by omega : t ≤ (2 ^ (288 * M)) ^ B)
  have hsum :
      (∑ i ∈ Finset.range t, fourier (T := 1) h
        ((((b : ℚ) ^ i * (1 * radixStonehamTruncation b c n +
          1 * radixStonehamTruncation b d n) : ℚ) : ℝ) : UnitAddCircle)) =
      ∑ i ∈ Finset.range t, ZMod.stdAddChar ((A : ZMod q) * (b : ZMod q) ^ i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [one_mul]
    exact fourier_rational_radix_eq_stdAddChar b h A r
      (rational_reduced_representation ((h : ℚ) * r)) i
  simp only [one_mul] at hsum
  rw [hsum]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hbound

/-- The full two-summand Stoneham sum-normality question: no relationship between
the parameters is required, beyond each being coprime to the defining base. -/
theorem stoneham_two_sum_normalInBase (b c d : ℕ)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hbc : Nat.Coprime b c) (hbd : Nat.Coprime b d) :
    NormalInBase b (stonehamConstant b c + stonehamConstant b d) := by
  obtain ⟨M, hM, hden⟩ := pair_frequency_denominator_scales b c d hb hc hd hbc hbd
  obtain ⟨C, hC, hchar⟩ := fixed_support_global_character_bound b (c * d) M
    (by omega : 1 < b) (Nat.mul_pos (by omega) (by omega))
    (hbc.mul_right hbd) (by omega : 1 ≤ M)
  exact two_sum_normalInBase_of_character_scale_bound b c d M C hb hc hd
    (by omega) hC hden hchar

/-- The same theorem with both conventional defining series displayed explicitly. -/
theorem stoneham_two_sum_series_normalInBase (b c d : ℕ)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hbc : Nat.Coprime b c) (hbd : Nat.Coprime b d) :
    NormalInBase b
      ((∑' k : ℕ, 1 / ((c : ℝ) ^ (k + 1) * (b : ℝ) ^ (c ^ (k + 1)))) +
        ∑' k : ℕ, 1 / ((d : ℝ) ^ (k + 1) * (b : ℝ) ^ (d ^ (k + 1)))) := by
  simpa only [stonehamConstant] using stoneham_two_sum_normalInBase b c d hb hc hd hbc hbd

/-- Every word has its expected frequency, counted at all overlapping positions
and with a limit along all prefix lengths. -/
theorem stoneham_two_sum_word_frequencies (b c d : ℕ)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hbc : Nat.Coprime b c) (hbd : Nat.Coprime b d)
    (l j : ℕ) (hj : j < b ^ l) :
    Tendsto (radixWordFrequency b (stonehamConstant b c + stonehamConstant b d) l j)
      atTop (𝓝 ((b : ℝ) ^ l)⁻¹) :=
  (stoneham_two_sum_normalInBase b c d hb hc hd hbc hbd).2 l j hj

end StonehamNormality
