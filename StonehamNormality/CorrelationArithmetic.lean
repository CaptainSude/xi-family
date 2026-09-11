import StonehamNormality.PrimeFive

/-! Exact denominator reduction for the outer differencing step. -/

noncomputable section
open scoped ComplexConjugate
namespace StonehamNormality

/-- A chosen stride removes a large power of three from every correlation. -/
theorem three_pow_dvd_two_stride_sub (a j : ℕ) :
    3 ^ (a + 1) ∣ 2 ^ (j * (2 * 3 ^ a)) - 1 := by
  have hp : (2 : ZMod (3 ^ (a + 1))) ^ (2 * 3 ^ a) = 1 := by
    rw [← XiNormality.orderOf_two_three_pow_succ a]
    exact pow_orderOf_eq_one _
  have hm : (2 : ZMod (3 ^ (a + 1))) ^ (j * (2 * 3 ^ a)) = 1 := by
    rw [Nat.mul_comm j, pow_mul, hp, one_pow]
  apply (ZMod.natCast_eq_zero_iff _ _).1
  rw [Nat.cast_sub (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)))]
  simpa using sub_eq_zero.mpr hm

/-- The same strides remove at most five times the shift index at prime five. -/
theorem five_gcd_two_stride_sub_le (a j l : ℕ) (hj : 0 < j) :
    Nat.gcd (5 ^ l) (2 ^ (j * (2 * 3 ^ a)) - 1) ≤ 5 * j := by
  obtain ⟨c, hc, heq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1
    (Nat.gcd_dvd_left (5 ^ l) (2 ^ (j * (2 * 3 ^ a)) - 1))
  have hdvd : 5 ^ c ∣ 2 ^ (j * (2 * 3 ^ a)) - 1 := by
    rw [← heq]
    exact Nat.gcd_dvd_right _ _
  rw [heq]
  rcases c with _ | c
  · simp
    omega
  · have hm : (2 : ZMod (5 ^ (c + 1))) ^ (j * (2 * 3 ^ a)) = 1 := by
      apply sub_eq_zero.mp
      have hcast := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
      rw [Nat.cast_sub (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)))] at hcast
      simpa using hcast
    have hord : 4 * 5 ^ c ∣ j * (2 * 3 ^ a) := by
      rw [← orderOf_two_five_pow_succ c]
      exact orderOf_dvd_of_pow_eq_one hm
    have hsmall : 5 ^ c ∣ j * (2 * 3 ^ a) :=
      (dvd_mul_left (5 ^ c) 4).trans hord
    have hcop : Nat.Coprime (5 ^ c) (2 * 3 ^ a) :=
      ((show Nat.Coprime 5 2 by norm_num).pow_left c).mul_right
        (((show Nat.Coprime 5 3 by norm_num).pow_left c).pow_right a)
    have hdivj : 5 ^ c ∣ j := hcop.dvd_mul_right.mp hsmall
    have hle : 5 ^ c ≤ j := Nat.le_of_dvd hj hdivj
    rw [pow_succ]
    omega

/-- Reduction by any numerator retains a modulus supported on three and five. -/
theorem reduced_mixed_modulus (k l c : ℕ) :
    ∃ r s : ℕ,
      (3 ^ k * 5 ^ l) / Nat.gcd (3 ^ k * 5 ^ l) c = 3 ^ r * 5 ^ s ∧
      3 ^ r * Nat.gcd (3 ^ k) c = 3 ^ k ∧
      5 ^ s * Nat.gcd (5 ^ l) c = 5 ^ l := by
  obtain ⟨u, hu, he3⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
    (Nat.gcd_dvd_left (3 ^ k) c)
  obtain ⟨v, hv, he5⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1
    (Nat.gcd_dvd_left (5 ^ l) c)
  refine ⟨k - u, l - v, ?_, ?_, ?_⟩
  · have hc : Nat.Coprime (3 ^ k) (5 ^ l) :=
      (show Nat.Coprime 3 5 by norm_num).pow k l
    rw [hc.mul_gcd, ← Nat.div_mul_div_comm (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)]
    rw [he3, he5, Nat.pow_div hu (by norm_num), Nat.pow_div hv (by norm_num)]
  · rw [he3, ← pow_add, Nat.sub_add_cancel hu]
  · rw [he5, ← pow_add, Nat.sub_add_cancel hv]

/-- Quantitative bounds for the surviving factors, without logarithms or valuations. -/
theorem reduced_stride_modulus_bounds (k l a j : ℕ) (ha : a + 1 ≤ k) (hj : 0 < j) :
    ∃ r s : ℕ,
      (3 ^ k * 5 ^ l) / Nat.gcd (3 ^ k * 5 ^ l) (2 ^ (j * (2 * 3 ^ a)) - 1) =
        3 ^ r * 5 ^ s ∧
      3 ^ (a + 1) * (3 ^ r * 5 ^ s) ≤ 3 ^ k * 5 ^ l ∧
      5 ^ l ≤ (5 * j) * 5 ^ s := by
  let c := 2 ^ (j * (2 * 3 ^ a)) - 1
  obtain ⟨r, s, heq, he3, he5⟩ := reduced_mixed_modulus k l c
  refine ⟨r, s, heq, ?_, ?_⟩
  · have hdiv : 3 ^ (a + 1) ∣ Nat.gcd (3 ^ k * 5 ^ l) c := Nat.dvd_gcd
      ((pow_dvd_pow 3 ha).trans (dvd_mul_right (3 ^ k) (5 ^ l)))
      (three_pow_dvd_two_stride_sub a j)
    have hgpos : 0 < Nat.gcd (3 ^ k * 5 ^ l) c :=
      Nat.gcd_pos_of_pos_left _ (by positivity)
    have hle := Nat.le_of_dvd hgpos hdiv
    have hmul := Nat.mul_le_mul_right (3 ^ r * 5 ^ s) hle
    have hprod : Nat.gcd (3 ^ k * 5 ^ l) c * (3 ^ r * 5 ^ s) = 3 ^ k * 5 ^ l := by
      rw [← heq, Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)]
    exact hmul.trans_eq hprod
  · have hle := Nat.mul_le_mul_left (5 ^ s) (five_gcd_two_stride_sub_le a j l hj)
    change 5 ^ s * Nat.gcd (5 ^ l) c ≤ 5 ^ s * (5 * j) at hle
    rw [he5] at hle
    simpa only [Nat.mul_comm] using hle

/-- Equal rational phases define equal standard additive characters. -/
theorem stdAddChar_intCast_eq_of_cross_mul {q Q : ℕ} [NeZero q] [NeZero Q]
    (A B : ℤ) (h : A * (Q : ℤ) = B * (q : ℤ)) :
    ZMod.stdAddChar (A : ZMod q) = ZMod.stdAddChar (B : ZMod Q) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  have hcast : (A : ℂ) * (Q : ℂ) = (B : ℂ) * (q : ℂ) := by exact_mod_cast h
  have hdiv : (A : ℂ) / q = (B : ℂ) / Q :=
    (div_eq_div_iff (by exact_mod_cast NeZero.ne q) (by exact_mod_cast NeZero.ne Q)).2 hcast
  congr 1
  simpa only [mul_div_assoc] using congrArg (fun z : ℂ => 2 * Real.pi * Complex.I * z) hdiv

/-- Reduction of a rational additive character also preserves a unit numerator. -/
theorem reduce_stdAddChar {q : ℕ} [NeZero q] (c Q : ℕ) [NeZero Q]
    (hQ : Q = q / Nat.gcd q c) (A : ℤ) (hA : IsUnit (A : ZMod q)) :
    ∃ D : ℤ, IsUnit (D : ZMod Q) ∧ ∀ t : ℕ,
      ZMod.stdAddChar ((A : ZMod q) * (c : ZMod q) * 2 ^ t) =
        ZMod.stdAddChar ((D : ZMod Q) * 2 ^ t) := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hgpos : 0 < Nat.gcd q c := Nat.gcd_pos_of_pos_left _ hqpos
  have hQdvd : Q ∣ q := hQ ▸ Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q c)
  have hAU : IsUnit (A : ZMod Q) := by
    simpa only [map_intCast] using hA.map (ZMod.castHom hQdvd (ZMod Q))
  have hdU : IsUnit ((c / Nat.gcd q c : ℕ) : ZMod Q) :=
    (ZMod.isUnit_iff_coprime _ _).2 (by
      rw [hQ]
      exact (Nat.coprime_div_gcd_div_gcd hgpos).symm)
  refine ⟨A * (c / Nat.gcd q c : ℕ), ?_, ?_⟩
  · simpa only [Int.cast_mul, Int.cast_natCast] using hAU.mul hdU
  · intro t
    have hcrossNat : c * Q = (c / Nat.gcd q c) * q := by
      calc
        c * Q = ((c / Nat.gcd q c) * Nat.gcd q c) * Q := by
          rw [Nat.div_mul_cancel (Nat.gcd_dvd_right q c)]
        _ = (c / Nat.gcd q c) * q := by
          rw [Nat.mul_assoc, hQ, Nat.mul_div_cancel' (Nat.gcd_dvd_left q c)]
    have hcross : (c : ℤ) * Q = ((c / Nat.gcd q c : ℕ) : ℤ) * q := by
      exact_mod_cast hcrossNat
    have h :=
      stdAddChar_intCast_eq_of_cross_mul (q := q) (Q := Q)
        (A * (c : ℤ) * 2 ^ t) ((A * (c / Nat.gcd q c : ℕ)) * 2 ^ t) (by
          calc
            _ = A * 2 ^ t * ((c : ℤ) * Q) := by ring
            _ = _ := by rw [hcross]; ring)
    simpa only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat] using h

/-- Every outer correlation is a unit character orbit at the reduced modulus. -/
theorem reduced_stride_correlation (k l a j : ℕ) (ha : a + 1 ≤ k) (hj : 0 < j)
    (A : ℤ) (hA : IsUnit (A : ZMod (3 ^ k * 5 ^ l))) :
    ∃ r s : ℕ, ∃ D : ℤ,
      3 ^ (a + 1) * (3 ^ r * 5 ^ s) ≤ 3 ^ k * 5 ^ l ∧
      5 ^ l ≤ (5 * j) * 5 ^ s ∧
      IsUnit (D : ZMod (3 ^ r * 5 ^ s)) ∧
      ∀ t : ℕ,
        ZMod.stdAddChar ((A : ZMod (3 ^ k * 5 ^ l)) * 2 ^ (t + j * (2 * 3 ^ a))) *
          conj (ZMod.stdAddChar ((A : ZMod (3 ^ k * 5 ^ l)) * 2 ^ t)) =
            ZMod.stdAddChar ((D : ZMod (3 ^ r * 5 ^ s)) * 2 ^ t) := by
  obtain ⟨r, s, hq, hthree, hfive⟩ := reduced_stride_modulus_bounds k l a j ha hj
  let c := 2 ^ (j * (2 * 3 ^ a)) - 1
  obtain ⟨D, hD, hphase⟩ := reduce_stdAddChar c (3 ^ r * 5 ^ s) hq.symm A hA
  refine ⟨r, s, D, hthree, hfive, hD, ?_⟩
  intro t
  rw [XiNormality.conj_stdAddChar, ← AddChar.map_add_eq_mul]
  rw [← hphase t]
  congr 1
  dsimp [c]
  rw [Nat.cast_sub (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)))]
  push_cast
  rw [pow_add]
  ring

end StonehamNormality
