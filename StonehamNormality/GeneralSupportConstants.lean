import StonehamNormality.GeneralOrder
import StonehamNormality.GeneralSupportedOrbit

noncomputable section

open scoped BigOperators

namespace StonehamNormality

theorem coprime_of_prime_support (b S q : ℕ) (hcop : b.Coprime S)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ S) : b.Coprime q := by
  apply Nat.coprime_of_dvd'
  intro p hp hpb hpq
  have hdiv := Nat.dvd_gcd hpb (hsupport p hp hpq)
  simpa only [hcop.gcd_eq_one] using hdiv

/-- One fixed exponent handles every modulus with prime support in `S`. -/
def supportStrideExponent (S : ℕ) : ℕ := 2 * S.totient

theorem supportStrideExponent_pos {S : ℕ} (hS : 0 < S) :
    0 < supportStrideExponent S := by
  exact mul_pos (by norm_num) (Nat.totient_pos.mpr hS)

/-- Euler's theorem makes the chosen power one modulo the support parameter. -/
theorem support_dvd_base_pow_sub_one (b S : ℕ) (hcop : b.Coprime S) :
    S ∣ b ^ supportStrideExponent S - 1 := by
  have h := (Nat.ModEq.pow_totient hcop).pow 2
  have he : b ^ supportStrideExponent S ≡ 1 [MOD S] := by
    simpa only [supportStrideExponent, one_pow, ← pow_mul, Nat.mul_comm] using h
  exact he.symm.dvd'

/-- All primes of every supported modulus divide the fixed principal step. -/
theorem support_primes_dvd_base_pow_sub_one (b S q : ℕ) (hcop : b.Coprime S)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ S) :
    ∀ p : ℕ, p.Prime → p ∣ q → p ∣ b ^ supportStrideExponent S - 1 := by
  intro p hp hpq
  exact (hsupport p hp hpq).trans (support_dvd_base_pow_sub_one b S hcop)

/-- At the prime two the even exponent automatically enters the depth-two
principal kernel; no primitive-root assumption is required. -/
theorem support_four_dvd_base_pow_sub_one (b S q : ℕ) (hcop : b.Coprime S)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ S) :
    2 ∣ q → 4 ∣ b ^ supportStrideExponent S - 1 := by
  intro h2
  have htwo : b.Coprime 2 := hcop.of_dvd_right (hsupport 2 Nat.prime_two h2)
  have hodd : Odd b := Nat.coprime_two_right.mp htwo
  have h8 := Nat.eight_dvd_sq_sub_one_of_odd
    (show Odd (b ^ S.totient) from hodd.pow)
  have h4 := (by norm_num : 4 ∣ 8).trans h8
  simpa only [supportStrideExponent, ← pow_mul, Nat.mul_comm] using h4

/-- The general inner estimate for every modulus with a fixed prime support,
with the supporting exponent chosen explicitly by Euler's theorem. -/
theorem fixed_support_character_arbitrary_length_bound (b S q L H : ℕ) [NeZero q]
    (hb : 1 < b) (hS : 0 < S) (hcop : b.Coprime S)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ S)
    (hlarge : b ^ supportStrideExponent S - 1 < q)
    (hH : H * (b ^ supportStrideExponent S - 1) ^ 2 ≤ q)
    (w : ZMod q) (hw : IsUnit w) :
    (H : ℝ) * ‖∑ t ∈ Finset.range L, ZMod.stdAddChar (w * (b : ZMod q) ^ t)‖ ≤
      Real.sqrt ((q : ℝ) * ((H : ℝ) * q)) + 2 * (H : ℝ) ^ 2 := by
  exact supported_power_character_arbitrary_length_bound b (supportStrideExponent S) q L H
    hb (supportStrideExponent_pos hS).ne' (NeZero.pos q)
    (coprime_of_prime_support b S q hcop hsupport)
    (support_primes_dvd_base_pow_sub_one b S q hcop hsupport)
    (support_four_dvd_base_pow_sub_one b S q hcop hsupport)
    hlarge hH w hw

end StonehamNormality
