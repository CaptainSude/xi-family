import XiNormality.Exponential

/-!
# Powers of two modulo powers of five

Arithmetic building blocks for the three-and-five joint-normality argument.
This file proves the modular order and separation statements. It does not
assert normality of any Stoneham constant.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace StonehamNormality

theorem orderOf_two_mod_five : orderOf (2 : ZMod 5) = 4 := by
  apply (orderOf_eq_iff (by norm_num : 0 < (4 : ℕ))).2
  constructor
  · decide
  · intro m hm hm0
    interval_cases m <;> decide

/-- Two generates the unit group modulo every positive power of five. -/
theorem orderOf_two_five_pow_succ (k : ℕ) :
    orderOf (2 : ZMod (5 ^ (k + 1))) = 4 * 5 ^ k := by
  have hsixteen : orderOf (16 : ZMod (5 ^ (k + 1))) = 5 ^ k := by
    convert ZMod.orderOf_one_add_mul_prime (by norm_num : Nat.Prime 5)
      (by norm_num : (5 : ℕ) ≠ 2) 3 (by norm_num) k using 1
    norm_num
  have hdvd : 4 ∣ orderOf (2 : ZMod (5 ^ (k + 1))) := by
    have hmap := orderOf_map_dvd
      (ZMod.castHom (dvd_pow_self 5 (by omega : k + 1 ≠ 0)) (ZMod 5)).toMonoidHom
      (2 : ZMod (5 ^ (k + 1)))
    have hcast : ZMod.cast (2 : ZMod (5 ^ (k + 1))) = (2 : ZMod 5) :=
      ZMod.cast_natCast (dvd_pow_self 5 (by omega : k + 1 ≠ 0)) 2
    simpa [hcast, orderOf_two_mod_five] using hmap
  have hpow := orderOf_pow_of_dvd (x := (2 : ZMod (5 ^ (k + 1))))
    (by norm_num : (4 : ℕ) ≠ 0) hdvd
  have hfour : (2 : ZMod (5 ^ (k + 1))) ^ 4 = 16 := by ring
  rw [hfour, hsixteen] at hpow
  calc
    orderOf (2 : ZMod (5 ^ (k + 1))) =
        (orderOf (2 : ZMod (5 ^ (k + 1))) / 4) * 4 :=
      (Nat.div_mul_cancel hdvd).symm
    _ = 4 * 5 ^ k := by rw [← hpow, mul_comm]

def twoFiveUnit (k : ℕ) : (ZMod (5 ^ (k + 1)))ˣ :=
  ZMod.unitOfCoprime 2 ((show Nat.Coprime 2 5 by norm_num).pow_right (k + 1))

@[simp] theorem coe_twoFiveUnit (k : ℕ) :
    (twoFiveUnit k : ZMod (5 ^ (k + 1))) = 2 := rfl

theorem orderOf_twoFiveUnit (k : ℕ) :
    orderOf (twoFiveUnit k) = 4 * 5 ^ k := by
  rw [← orderOf_injective _ Units.coeHom_injective (twoFiveUnit k)]
  exact orderOf_two_five_pow_succ k

theorem twoFiveUnit_powers_bijective (k : ℕ) :
    Function.Bijective (fun t : Fin (4 * 5 ^ k) => twoFiveUnit k ^ (t : ℕ)) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro i j hij
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (x := twoFiveUnit k)
      (by simpa only [Set.mem_Iio, orderOf_twoFiveUnit] using i.isLt)
      (by simpa only [Set.mem_Iio, orderOf_twoFiveUnit] using j.isLt) hij
  · simp [ZMod.card_units_eq_totient,
      Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 5), mul_comm]

noncomputable def twoFiveUnitPowersEquiv (k : ℕ) :
    Fin (4 * 5 ^ k) ≃ (ZMod (5 ^ (k + 1)))ˣ :=
  Equiv.ofBijective _ (twoFiveUnit_powers_bijective k)

/-- The complete one-prime character sum used when one Weyl coefficient is zero. -/
theorem sum_powers_stdAddChar_five_pow_eq_zero (k : ℕ)
    (w : ZMod (5 ^ (k + 1))) (hw : w * 5 ≠ 0) :
    ∑ t ∈ Finset.range (4 * 5 ^ k), ZMod.stdAddChar (w * 2 ^ t) = 0 := by
  have hzero : ∑ u : (ZMod (5 ^ (k + 1)))ˣ,
      ZMod.stdAddChar (w * (u : ZMod _)) = 0 := by
    apply XiNormality.sum_units_addChar_eq_zero ZMod.stdAddChar w 5
    · refine ⟨k + 1, ?_⟩
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        ZMod.natCast_self (5 ^ (k + 1))
    · intro hchar
      apply hw
      apply ZMod.injective_stdAddChar
      simpa only [AddChar.map_zero_eq_one] using hchar
  have heq := (twoFiveUnitPowersEquiv k).sum_comp
    (fun u : (ZMod (5 ^ (k + 1)))ˣ => ZMod.stdAddChar (w * (u : ZMod _)))
  have h := heq.trans hzero
  rw [← Fin.sum_univ_eq_sum_range (fun t : ℕ => ZMod.stdAddChar (w * 2 ^ t))]
  simpa only [twoFiveUnitPowersEquiv, Equiv.ofBijective_apply,
    Units.val_pow_eq_pow_val, coe_twoFiveUnit] using h

/-- Short translates remain distinct at the next lower five-power modulus. -/
theorem two_pow_sub_mul_five_ne_zero (k : ℕ) {a b : ℕ}
    (ha : a < 4 * 5 ^ k) (hb : b < 4 * 5 ^ k) (hab : a ≠ b) :
    ((2 : ZMod (5 ^ (k + 2))) ^ a - 2 ^ b) * 5 ≠ 0 := by
  intro hz
  have hdiv : (((5 ^ (k + 2) : ℕ) : ℤ)) ∣ ((2 : ℤ) ^ a - 2 ^ b) * 5 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa only [Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_ofNat] using hz
  rw [Nat.cast_pow, Nat.cast_ofNat, show k + 2 = (k + 1) + 1 by omega,
    pow_succ, Int.mul_dvd_mul_iff_right (by norm_num : (5 : ℤ) ≠ 0)] at hdiv
  have hlow : (2 : ZMod (5 ^ (k + 1))) ^ a = 2 ^ b := by
    apply sub_eq_zero.mp
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((2 : ℤ) ^ a - 2 ^ b) (5 ^ (k + 1))).2 (by exact_mod_cast hdiv)
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_ofNat] using hc
  exact hab (pow_injOn_Iio_orderOf (x := (2 : ZMod (5 ^ (k + 1))))
    (by simpa only [Set.mem_Iio, orderOf_two_five_pow_succ] using ha)
    (by simpa only [Set.mem_Iio, orderOf_two_five_pow_succ] using hb) hlow)

end StonehamNormality
