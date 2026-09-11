import StonehamNormality.GeneralOrbitScale
import StonehamNormality.GeneralOrder
import StonehamNormality.GeneralCorrelation
import StonehamNormality.SmoothDivisor

/-! The complete finite character estimate at modulus scales `2^(36k)`. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace StonehamNormality

theorem reduced_modulus_integer_scale_bounds (k D q m j Q : ℕ)
    (hk : 1 ≤ k) (hD : 0 < D)
    (hql : 2 ^ (36 * k) ≤ q) (hqu : q < 2 ^ (36 * (k + 1)))
    (hml : 2 ^ (12 * k) ≤ m) (hmu : m ≤ D * 2 ^ (12 * k))
    (hj : j < 2 ^ (3 * k)) (hDscale : D ^ 4 ≤ 2 ^ (5 * k))
    (hredl : q ≤ (D * m * j) * Q) (hredu : m * Q ≤ q) :
    Q ≤ 2 ^ 36 * 2 ^ (24 * k) ∧ 2 ^ (16 * k) * D ^ 2 ≤ Q ∧ D < Q := by
  have hupper : Q ≤ 2 ^ 36 * 2 ^ (24 * k) := by
    have hh : 2 ^ (12 * k) * Q ≤ 2 ^ (36 * (k + 1)) :=
      (Nat.mul_le_mul_right Q hml).trans (hredu.trans hqu.le)
    have heq : (2 : ℕ) ^ (36 * (k + 1)) =
        2 ^ (12 * k) * (2 ^ 36 * 2 ^ (24 * k)) := by
      rw [show 36 * (k + 1) = 12 * k + (36 + 24 * k) by omega, pow_add, pow_add]
    rw [heq] at hh
    exact Nat.le_of_mul_le_mul_left hh (by positivity)
  have hsurvive : 2 ^ (21 * k) ≤ D ^ 2 * Q := by
    have hh : 2 ^ (36 * k) ≤ 2 ^ (15 * k) * (D ^ 2 * Q) := by
      calc
        _ ≤ q := hql
        _ ≤ (D * m * j) * Q := hredl
        _ ≤ (D * (D * 2 ^ (12 * k)) * 2 ^ (3 * k)) * Q :=
          Nat.mul_le_mul_right Q (Nat.mul_le_mul (Nat.mul_le_mul_left D hmu) hj.le)
        _ = 2 ^ (15 * k) * (D ^ 2 * Q) := by
          rw [show 15 * k = 12 * k + 3 * k by omega, pow_add]
          ring
    rw [show 36 * k = 15 * k + 21 * k by omega, pow_add] at hh
    exact Nat.le_of_mul_le_mul_left hh (by positivity)
  have hsep : 2 ^ (16 * k) * D ^ 2 ≤ Q := by
    have hh : D ^ 2 * (2 ^ (16 * k) * D ^ 2) ≤ D ^ 2 * Q := by
      calc
        _ = 2 ^ (16 * k) * D ^ 4 := by ring
        _ ≤ 2 ^ (16 * k) * 2 ^ (5 * k) := Nat.mul_le_mul_left _ hDscale
        _ = 2 ^ (21 * k) := by rw [← pow_add]; congr 1; omega
        _ ≤ D ^ 2 * Q := hsurvive
    exact Nat.le_of_mul_le_mul_left hh (by positivity)
  have hlarge : D < Q := by
    have htwo : 2 ≤ (2 : ℕ) ^ (16 * k) := by
      have hh := pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) (show 1 ≤ 16 * k by omega)
      simpa using hh
    have hh : 2 * D ^ 2 ≤ Q := (Nat.mul_le_mul_right _ htwo).trans hsep
    nlinarith
  exact ⟨hupper, hsep, hlarge⟩

theorem supported_power_character_integer_scale_bound
    (b C q k L : ℕ) [NeZero q] (A : ℤ)
    (hb : 1 < b) (hC : C ≠ 0) (hcop : b.Coprime q)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ b ^ C - 1)
    (hfour : 2 ∣ q → 4 ∣ b ^ C - 1)
    (hA : IsUnit (A : ZMod q)) (hDq : b ^ C - 1 < q)
    (hsep : 2 ^ (16 * k) * (b ^ C - 1) ^ 2 ≤ q)
    (hupper : q ≤ 2 ^ 36 * 2 ^ (24 * k)) :
    ‖∑ t ∈ Finset.range L, ZMod.stdAddChar ((A : ZMod q) * (b : ZMod q) ^ t)‖ ≤
      ((2 : ℝ) ^ 36 + 2) * (2 : ℝ) ^ (16 * k) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hD : 0 < b ^ C - 1 := by have := one_lt_pow₀ hb hC; omega
  have hd : 0 < Nat.gcd q (b ^ C - 1) := Nat.gcd_pos_of_pos_left _ hq
  have hdnz : (Nat.gcd q (b ^ C - 1) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hd ((Nat.gcd_le_right q hD).trans_lt hDq)
  apply power_character_integer_scale_bound (b : ZMod q)
    (Nat.gcd q (b ^ C - 1) : ZMod q) (A : ZMod q)
    (ZMod.unitOfCoprime b hcop).isUnit hA hdnz
    (base_principal_kernel_mem_powers b C q hb hC hq hsupport hfour) k L ((2 : ℝ) ^ 36)
    (by positivity)
  · exact_mod_cast hupper
  · intro i hi j hj hij
    exact base_principal_kernel_shift_separation b C q (2 ^ (16 * k))
      hb hC hq hcop hsupport hfour hsep i j hi hj hij

/-- A uniform relative character estimate for every supported modulus in its
integer-power block. The fixed data enter only the threshold hypotheses. -/
theorem power_character_modulus_scale_bound (b C q k L : ℕ) [NeZero q] (A : ℤ)
    (hb : 1 < b) (hC : C ≠ 0) (hcop : b.Coprime q)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ b ^ C - 1)
    (hfour : 2 ∣ q → 4 ∣ b ^ C - 1) (hA : IsUnit (A : ZMod q))
    (hk : 1 ≤ k)
    (hql : 2 ^ (36 * k) ≤ q) (hqu : q < 2 ^ (36 * (k + 1)))
    (hDscale : (b ^ C - 1) ^ 4 ≤ 2 ^ (5 * k))
    (hCscale : C * (b ^ C - 1) ≤ 2 ^ (2 * k))
    (hL : 2 ^ (17 * k) ≤ L) :
    (2 : ℝ) ^ k *
      ‖∑ t ∈ Finset.range L, ZMod.stdAddChar ((A : ZMod q) * (b : ZMod q) ^ t)‖ ^ 2 ≤
        2 * ((2 : ℝ) ^ 36 + 3) * (L : ℝ) ^ 2 := by
  let D := b ^ C - 1
  have hD : 0 < D := by have := one_lt_pow₀ hb hC; dsimp [D]; omega
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hTq : 2 ^ (12 * k) ≤ q :=
    (pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) (by omega)).trans hql
  obtain ⟨m, hmq, hml, hmu⟩ := exists_divisor_between q D (2 ^ (12 * k))
    (by omega) (one_le_pow₀ (by norm_num)) hTq
    (fun p hp hpq => Nat.le_of_dvd hD (hsupport p hp hpq))
  have hm : 0 < m := (by positivity : 0 < (2 : ℕ) ^ (12 * k)).trans_le hml
  have hstep : 2 ^ (3 * k) * (C * m) ≤ L := by
    calc
      _ ≤ 2 ^ (3 * k) * (C * (D * 2 ^ (12 * k))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left C hmu)
      _ = (C * D) * 2 ^ (15 * k) := by
        rw [show 15 * k = 3 * k + 12 * k by omega, pow_add]
        ring
      _ ≤ 2 ^ (2 * k) * 2 ^ (15 * k) := Nat.mul_le_mul_right _ hCscale
      _ = 2 ^ (17 * k) := by rw [← pow_add]; congr 1; omega
      _ ≤ L := hL
  have hbound := interval_differencing_integer_scale
    (fun t => ZMod.stdAddChar ((A : ZMod q) * (b : ZMod q) ^ t))
    k L (C * m) ((2 : ℝ) ^ 36 + 2) (by positivity) hL hstep
    (fun t ht => XiNormality.norm_stdAddChar _) ?_
  · convert hbound using 1 <;> ring
  · intro j hj hjH
    let Q := q / Nat.gcd q (b ^ (j * (C * m)) - 1)
    have hQ : 0 < Q := Nat.div_gcd_pos_of_pos_left _ hq
    letI : NeZero Q := ⟨hQ.ne'⟩
    have hQdvd : Q ∣ q := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
    have hred := stride_reduced_modulus_bounds b C q m j hb hC hq hm hj hmq hsupport hfour
    have hscales := reduced_modulus_integer_scale_bounds k D q m j Q hk hD
      hql hqu hml hmu hjH hDscale hred.2 hred.1
    obtain ⟨E, hE, hphase⟩ := radix_reduced_stride_correlation b (C * m) j Q hb.le rfl A hA
    have hin := supported_power_character_integer_scale_bound b C Q k (L - j * (C * m)) E
      hb hC (hcop.of_dvd_right hQdvd)
      (fun p hp hpQ => hsupport p hp (hpQ.trans hQdvd))
      (fun h2 => hfour (h2.trans hQdvd)) hE hscales.2.2 hscales.2.1 hscales.1
    simpa only [hphase] using hin

end StonehamNormality
