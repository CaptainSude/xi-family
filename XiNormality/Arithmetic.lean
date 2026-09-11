import XiNormality.Definitions

/-!
# Arithmetic of the smooth indices

These lemmas isolate the arithmetic in the denominator argument. In particular,
the only terms at the largest power of three have indices `3^k` and `2*3^k`,
and their normalized contributions agree modulo three.
-/

noncomputable section

open scoped BigOperators Classical

namespace XiNormality

@[simp] theorem smoothIndex_pos (a c : ℕ) : 0 < smoothIndex a c := by
  unfold smoothIndex
  positivity

@[simp] theorem smoothIndex_ne_zero (a c : ℕ) : smoothIndex a c ≠ 0 :=
  (smoothIndex_pos a c).ne'

theorem IsSmooth.pos {m : ℕ} (hm : IsSmooth m) : 0 < m := by
  obtain ⟨a, c, rfl⟩ := hm
  exact smoothIndex_pos a c

@[simp] theorem not_isSmooth_zero : ¬ IsSmooth 0 := by
  intro h
  exact (Nat.lt_irrefl 0) h.pos

@[simp] theorem smoothIndex_factorization_two (a c : ℕ) :
    (smoothIndex a c).factorization 2 = a := by
  simp [smoothIndex, Nat.factorization_mul, Nat.prime_two, Nat.prime_three]

@[simp] theorem smoothIndex_factorization_three (a c : ℕ) :
    (smoothIndex a c).factorization 3 = c := by
  simp [smoothIndex, Nat.factorization_mul, Nat.prime_two, Nat.prime_three]

theorem smoothIndex_injective :
    Function.Injective (fun p : ℕ × ℕ => smoothIndex p.1 p.2) := by
  rintro ⟨a, c⟩ ⟨b, d⟩ h
  have ha := congrArg (fun m : ℕ => m.factorization 2) h
  have hc := congrArg (fun m : ℕ => m.factorization 3) h
  simp only [smoothIndex_factorization_two] at ha
  simp only [smoothIndex_factorization_three] at hc
  exact Prod.ext ha hc

theorem smoothIndex_eq_iff {a b c d : ℕ} :
    smoothIndex a c = smoothIndex b d ↔ a = b ∧ c = d := by
  constructor
  · intro h
    have hp := smoothIndex_injective (show smoothIndex (a, c).1 (a, c).2 =
      smoothIndex (b, d).1 (b, d).2 from h)
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem two_pow_le_smoothIndex (a c : ℕ) : 2 ^ a ≤ smoothIndex a c := by
  unfold smoothIndex
  exact Nat.le_mul_of_pos_right _ (by positivity)

theorem three_pow_le_smoothIndex (a c : ℕ) : 3 ^ c ≤ smoothIndex a c := by
  unfold smoothIndex
  exact Nat.le_mul_of_pos_left _ (by positivity)

theorem smoothIndex_lt_two_pow_exponents {a c B : ℕ} (hm : smoothIndex a c < 2 ^ B) :
    a < B ∧ c < B := by
  have ha : 2 ^ a < 2 ^ B := (two_pow_le_smoothIndex a c).trans_lt hm
  have hc : 2 ^ c < 2 ^ B :=
    ((Nat.pow_le_pow_left (by omega : 2 ≤ 3) c).trans
      (three_pow_le_smoothIndex a c)).trans_lt hm
  exact ⟨(pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp ha,
    (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp hc⟩

/-- A deliberately coarse count suffices for qualitative normality. -/
theorem smooth_count_lt_two_pow (B : ℕ) :
    ((Finset.range (2 ^ B)).filter IsSmooth).card ≤ B ^ 2 := by
  classical
  have hs : (Finset.range (2 ^ B)).filter IsSmooth ⊆
      ((Finset.range B) ×ˢ (Finset.range B)).image
        (fun p : ℕ × ℕ => smoothIndex p.1 p.2) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨a, c, rfl⟩ := hm.2
    have hac := smoothIndex_lt_two_pow_exponents hm.1
    exact Finset.mem_image.mpr ⟨(a, c), by simp [hac.1, hac.2], rfl⟩
  calc
    _ ≤ (((Finset.range B) ×ˢ (Finset.range B)).image
        (fun p : ℕ × ℕ => smoothIndex p.1 p.2)).card := Finset.card_le_card hs
    _ ≤ ((Finset.range B) ×ˢ (Finset.range B)).card := Finset.card_image_le
    _ = B ^ 2 := by simp [pow_two]

theorem three_exponent_le {a c n k : ℕ}
    (hm : smoothIndex a c ≤ n) (hn : n < 3 ^ (k + 1)) : c ≤ k := by
  have hp : 3 ^ c < 3 ^ (k + 1) := lt_of_le_of_lt
    ((three_pow_le_smoothIndex a c).trans hm) hn
  have hc : c < k + 1 := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 3)).mp hp
  omega

theorem maximal_three_exponent_two_le_one {a n k : ℕ}
    (hm : smoothIndex a k ≤ n) (hn : n < 3 ^ (k + 1)) : a ≤ 1 := by
  by_contra ha
  have htwo : 2 ^ 2 ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) (by omega)
  have hmul := Nat.mul_le_mul_right (3 ^ k) htwo
  have hthree : 0 < (3 : ℕ) ^ k := by positivity
  unfold smoothIndex at hm
  rw [pow_succ] at hn
  norm_num at htwo
  nlinarith [hmul]

theorem maximal_three_indices {a n k : ℕ}
    (hm : smoothIndex a k ≤ n) (hn : n < 3 ^ (k + 1)) :
    smoothIndex a k = 3 ^ k ∨ smoothIndex a k = 2 * 3 ^ k := by
  have ha := maximal_three_exponent_two_le_one hm hn
  interval_cases a <;> simp [smoothIndex]

theorem cancel_two_power {n a c : ℕ} (hn : smoothIndex a c + a ≤ n) :
    (2 : ℚ) ^ (n - smoothIndex a c) / smoothIndex a c =
      (2 : ℚ) ^ (n - smoothIndex a c - a) / 3 ^ c := by
  have he : n - smoothIndex a c = (n - smoothIndex a c - a) + a := by omega
  nth_rw 1 [he]
  rw [pow_add]
  simp only [smoothIndex, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

theorem scaled_smooth_term {n a c k : ℕ}
    (hn : smoothIndex a c + a ≤ n) (hc : c ≤ k) :
    (3 : ℚ) ^ k * ((2 : ℚ) ^ (n - smoothIndex a c) / smoothIndex a c) =
      ((2 ^ (n - smoothIndex a c - a) * 3 ^ (k - c) : ℕ) : ℚ) := by
  rw [cancel_two_power hn]
  have hk : k = (k - c) + c := by omega
  nth_rw 1 [hk]
  simp only [pow_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

theorem two_pow_three_pow_mod_three (k : ℕ) :
    (2 : ZMod 3) ^ (3 ^ k) = 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, ih]
    norm_num
    decide

theorem two_pow_three_pow_add_one_mod_three (k : ℕ) :
    (2 : ZMod 3) ^ (3 ^ k + 1) = 1 := by
  rw [pow_succ, two_pow_three_pow_mod_three]
  norm_num
  decide

theorem highest_terms_agree_mod_three {n k : ℕ} (hn : 2 * 3 ^ k + 1 ≤ n) :
    (2 : ZMod 3) ^ (n - 3 ^ k) = (2 : ZMod 3) ^ (n - 2 * 3 ^ k - 1) := by
  have he : n - 3 ^ k = (n - 2 * 3 ^ k - 1) + (3 ^ k + 1) := by omega
  rw [he, pow_add, two_pow_three_pow_add_one_mod_three, mul_one]

theorem highest_single_nonzero_mod_three (n k : ℕ) :
    (2 : ZMod 3) ^ (n - 3 ^ k) ≠ 0 := by
  exact pow_ne_zero _ (by decide)

theorem highest_pair_nonzero_mod_three {n k : ℕ} (hn : 2 * 3 ^ k + 1 ≤ n) :
    (2 : ZMod 3) ^ (n - 3 ^ k) + (2 : ZMod 3) ^ (n - 2 * 3 ^ k - 1) ≠ 0 := by
  rw [highest_terms_agree_mod_three hn, ← two_mul]
  exact mul_ne_zero (by decide) (pow_ne_zero _ (by decide))

/-- The arithmetic property supplied by excluding the short exceptional intervals. -/
def SafeShift (n : ℕ) : Prop :=
  ∀ a c : ℕ, smoothIndex a c ≤ n → smoothIndex a c + a ≤ n

theorem safeShift_of_gap {n B : ℕ} (hn : n < 2 ^ B)
    (hgap : ∀ m : ℕ, IsSmooth m → m ≤ n → B ≤ n - m) : SafeShift n := by
  intro a c hm
  have ha := (smoothIndex_lt_two_pow_exponents (hm.trans_lt hn)).1
  have hg := hgap (smoothIndex a c) ⟨a, c, rfl⟩ hm
  omega

/-- All unsafe shifts below `2^B` lie in at most `B^2` intervals of length `B`. -/
theorem unsafe_count_lt_two_pow (B : ℕ) :
    ((Finset.range (2 ^ B)).filter (fun n => ¬ SafeShift n)).card ≤ B ^ 3 := by
  classical
  let s := (Finset.range (2 ^ B)).filter IsSmooth
  have hs : (Finset.range (2 ^ B)).filter (fun n => ¬ SafeShift n) ⊆
      (s ×ˢ Finset.range B).image (fun p : ℕ × ℕ => p.1 + p.2) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hlt, hunsafe⟩ := hn
    change ¬ ∀ a c : ℕ, smoothIndex a c ≤ n → smoothIndex a c + a ≤ n at hunsafe
    push Not at hunsafe
    obtain ⟨a, c, hm, hfail⟩ := hunsafe
    have hmB := hm.trans_lt hlt
    have ha := (smoothIndex_lt_two_pow_exponents hmB).1
    refine Finset.mem_image.mpr ⟨(smoothIndex a c, n - smoothIndex a c), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmB, ⟨a, c, rfl⟩⟩
      · exact Finset.mem_range.mpr (by omega)
    · exact Nat.add_sub_of_le hm
  calc
    _ ≤ ((s ×ˢ Finset.range B).image (fun p : ℕ × ℕ => p.1 + p.2)).card :=
      Finset.card_le_card hs
    _ ≤ (s ×ˢ Finset.range B).card := Finset.card_image_le
    _ = s.card * B := by simp
    _ ≤ B ^ 2 * B := Nat.mul_le_mul_right B (smooth_count_lt_two_pow B)
    _ = B ^ 3 := by ring

def normalizedNumerator (n k : ℕ) : ℕ :=
  ∑ m ∈ (Finset.range (n + 1)).filter IsSmooth,
    2 ^ (n - m - m.factorization 2) * 3 ^ (k - m.factorization 3)

theorem truncation_scaled_eq_normalizedNumerator {n k : ℕ}
    (hsafe : SafeShift n) (hn : n < 3 ^ (k + 1)) :
    (3 : ℚ) ^ k * truncation n = (normalizedNumerator n k : ℚ) := by
  classical
  unfold truncation normalizedNumerator
  rw [Finset.mul_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  obtain ⟨a, c, rfl⟩ := hm.2
  simp only [smoothIndex_factorization_two, smoothIndex_factorization_three]
  exact scaled_smooth_term (hsafe a c (by omega))
    (three_exponent_le (a := a) (by omega) hn)

theorem lower_three_term_zero {n a c k : ℕ} (hc : c < k) :
    (2 : ZMod 3) ^ (n - smoothIndex a c - a) * 3 ^ (k - c) = 0 := by
  have he : k - c ≠ 0 := by omega
  rw [show (3 : ZMod 3) = 0 by decide, zero_pow he, mul_zero]

theorem normalizedNumerator_mod_three {n k : ℕ}
    (hlo : 3 ^ k ≤ n) (hhi : n < 3 ^ (k + 1)) :
    (normalizedNumerator n k : ZMod 3) =
      (2 : ZMod 3) ^ (n - 3 ^ k) +
        if 2 * 3 ^ k ≤ n then (2 : ZMod 3) ^ (n - 2 * 3 ^ k - 1) else 0 := by
  classical
  have hne : (3 : ℕ) ^ k ≠ 2 * 3 ^ k := by
    have hp : 0 < (3 : ℕ) ^ k := by positivity
    omega
  have hp_smooth : IsSmooth (3 ^ k) := ⟨0, k, by simp [smoothIndex]⟩
  have hq_smooth : IsSmooth (2 * 3 ^ k) := ⟨1, k, by simp [smoothIndex]⟩
  unfold normalizedNumerator
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  calc
    _ = ∑ m ∈ (Finset.range (n + 1)).filter IsSmooth,
        ((if m = 3 ^ k then (2 : ZMod 3) ^ (n - 3 ^ k) else 0) +
        (if m = 2 * 3 ^ k then (2 : ZMod 3) ^ (n - 2 * 3 ^ k - 1) else 0)) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm
      obtain ⟨a, c, rfl⟩ := hm.2
      simp only [smoothIndex_factorization_two, smoothIndex_factorization_three]
      by_cases hp : smoothIndex a c = 3 ^ k
      · have hac : a = 0 ∧ c = k := smoothIndex_eq_iff.mp
          (show smoothIndex a c = smoothIndex 0 k by simpa [smoothIndex] using hp)
        rcases hac with ⟨rfl, rfl⟩
        simp [smoothIndex, hne]
      · by_cases hq : smoothIndex a c = 2 * 3 ^ k
        · have hac : a = 1 ∧ c = k := smoothIndex_eq_iff.mp
            (show smoothIndex a c = smoothIndex 1 k by simpa [smoothIndex] using hq)
          rcases hac with ⟨rfl, rfl⟩
          simp [smoothIndex, hne.symm]
        · simp only [ite_eq_right hp, ite_eq_right hq, add_zero]
          have hcle : c ≤ k := three_exponent_le (a := a) (by omega) hhi
          have hcne : c ≠ k := by
            intro hck
            subst c
            exact (maximal_three_indices (by omega : smoothIndex a k ≤ n) hhi).elim hp hq
          exact lower_three_term_zero (by omega)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_ite_eq', hp_smooth, hq_smooth, hlo]

theorem normalizedNumerator_not_divisible_by_three {n k : ℕ}
    (hsafe : SafeShift n) (hlo : 3 ^ k ≤ n) (hhi : n < 3 ^ (k + 1)) :
    (normalizedNumerator n k : ZMod 3) ≠ 0 := by
  rw [normalizedNumerator_mod_three hlo hhi]
  split_ifs with htwo
  · have hn : 2 * 3 ^ k + 1 ≤ n := by
      simpa [smoothIndex] using hsafe 1 k (by simpa [smoothIndex] using htwo)
    exact highest_pair_nonzero_mod_three hn
  · simpa using highest_single_nonzero_mod_three n k

theorem den_eq_three_pow_of_scaled {r : ℚ} {A k : ℕ}
    (hr : (3 : ℚ) ^ k * r = (A : ℚ)) (hA : (A : ZMod 3) ≠ 0) :
    r.den = 3 ^ k := by
  have hdiv : ¬ 3 ∣ A := by
    rwa [← ZMod.natCast_eq_zero_iff A 3]
  have hcop : Nat.Coprime A (3 ^ k) :=
    Nat.prime_three.coprime_pow_of_not_dvd hdiv
  have hre : r = (A : ℚ) / 3 ^ k := by
    apply (eq_div_iff (by positivity : (3 : ℚ) ^ k ≠ 0)).2
    simpa [mul_comm] using hr
  rw [hre]
  have hd := Rat.den_div_eq_of_coprime
    (a := (A : ℤ)) (b := ((3 ^ k : ℕ) : ℤ))
    (by positivity) (by simpa using hcop)
  have hquot : (((A : ℤ) : ℚ) / (((3 ^ k : ℕ) : ℤ) : ℚ)) = (A : ℚ) / 3 ^ k := by
    rw [Int.cast_natCast, Int.cast_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rw [hquot] at hd
  exact Int.ofNat_inj.mp hd

/-- The exact denominator calculation, under the cancellation property supplied
by a nonexceptional shift. -/
theorem truncation_denominator {n k : ℕ}
    (hsafe : SafeShift n) (hlo : 3 ^ k ≤ n) (hhi : n < 3 ^ (k + 1)) :
    (truncation n).den = 3 ^ k := by
  exact den_eq_three_pow_of_scaled (truncation_scaled_eq_normalizedNumerator hsafe hhi)
    (normalizedNumerator_not_divisible_by_three hsafe hlo hhi)

theorem truncation_exists_coprime_numerator {n k : ℕ}
    (hsafe : SafeShift n) (hlo : 3 ^ k ≤ n) (hhi : n < 3 ^ (k + 1)) :
    ∃ A : ℤ, truncation n = (A : ℚ) / 3 ^ k ∧ ¬ (3 : ℤ) ∣ A := by
  refine ⟨normalizedNumerator n k, ?_, ?_⟩
  · apply (eq_div_iff (by positivity : (3 : ℚ) ^ k ≠ 0)).2
    simpa [mul_comm] using truncation_scaled_eq_normalizedNumerator hsafe hhi
  · change ¬ ((3 : ℕ) : ℤ) ∣ ((normalizedNumerator n k : ℕ) : ℤ)
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa using normalizedNumerator_not_divisible_by_three hsafe hlo hhi

/-- On a block with no new retained indices, truncations follow a doubling orbit. -/
theorem truncation_add_of_no_new_terms (n t : ℕ)
    (hnew : ∀ m : ℕ, IsSmooth m → m ≤ n + t → m ≤ n) :
    truncation (n + t) = (2 : ℚ) ^ t * truncation n := by
  classical
  have hs : (Finset.range (n + t + 1)).filter IsSmooth =
      (Finset.range (n + 1)).filter IsSmooth := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hm, hsm⟩
      exact ⟨by have := hnew m hsm (by omega); omega, hsm⟩
    · rintro ⟨hm, hsm⟩
      exact ⟨by omega, hsm⟩
  unfold truncation
  rw [hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  have he : n + t - m = t + (n - m) := by omega
  rw [he, pow_add, mul_div_assoc]

theorem orderOf_two_mod_three : orderOf (2 : ZMod 3) = 2 := by
  apply orderOf_eq_prime <;> decide

/-- Two generates the full unit group modulo every positive power of three. -/
theorem orderOf_two_three_pow_succ (k : ℕ) :
    orderOf (2 : ZMod (3 ^ (k + 1))) = 2 * 3 ^ k := by
  have hfour : orderOf (4 : ZMod (3 ^ (k + 1))) = 3 ^ k := by
    convert ZMod.orderOf_one_add_prime Nat.prime_three (by omega) k using 1
    norm_num
  have hdvd : 2 ∣ orderOf (2 : ZMod (3 ^ (k + 1))) := by
    have hmap := orderOf_map_dvd
      (ZMod.castHom (dvd_pow_self 3 (by omega : k + 1 ≠ 0)) (ZMod 3)).toMonoidHom
      (2 : ZMod (3 ^ (k + 1)))
    have hcast : ZMod.cast (2 : ZMod (3 ^ (k + 1))) = (2 : ZMod 3) :=
      ZMod.cast_natCast (dvd_pow_self 3 (by omega : k + 1 ≠ 0)) 2
    simpa [hcast, orderOf_two_mod_three] using hmap
  have hpow := orderOf_pow_of_dvd (x := (2 : ZMod (3 ^ (k + 1))))
    (by omega : (2 : ℕ) ≠ 0) hdvd
  simp only [show (2 : ZMod (3 ^ (k + 1))) ^ 2 = 4 by ring] at hpow
  rw [hfour] at hpow
  calc
    orderOf (2 : ZMod (3 ^ (k + 1))) =
        (orderOf (2 : ZMod (3 ^ (k + 1))) / 2) * 2 := (Nat.div_mul_cancel hdvd).symm
    _ = 2 * 3 ^ k := by rw [← hpow, mul_comm]

def twoUnit (k : ℕ) : (ZMod (3 ^ (k + 1)))ˣ :=
  ZMod.unitOfCoprime 2 ((show Nat.Coprime 2 3 by norm_num).pow_right (k + 1))

@[simp] theorem coe_twoUnit (k : ℕ) : (twoUnit k : ZMod (3 ^ (k + 1))) = 2 := rfl

theorem orderOf_twoUnit (k : ℕ) : orderOf (twoUnit k) = 2 * 3 ^ k := by
  rw [← orderOf_injective _ Units.coeHom_injective (twoUnit k)]
  exact orderOf_two_three_pow_succ k

theorem twoUnit_powers_bijective (k : ℕ) :
    Function.Bijective (fun t : Fin (2 * 3 ^ k) => twoUnit k ^ (t : ℕ)) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro i j hij
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (x := twoUnit k)
      (by simpa only [Set.mem_Iio, orderOf_twoUnit] using i.isLt)
      (by simpa only [Set.mem_Iio, orderOf_twoUnit] using j.isLt) hij
  · simp [ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ Nat.prime_three, mul_comm]

/-- Enumeration of all units by consecutive powers of two. -/
noncomputable def twoUnitPowersEquiv (k : ℕ) :
    Fin (2 * 3 ^ k) ≃ (ZMod (3 ^ (k + 1)))ˣ :=
  Equiv.ofBijective _ (twoUnit_powers_bijective k)

@[simp] theorem twoUnitPowersEquiv_apply (k : ℕ) (t : Fin (2 * 3 ^ k)) :
    twoUnitPowersEquiv k t = twoUnit k ^ (t : ℕ) := rfl

theorem two_pow_sub_mul_three_ne_zero (k : ℕ) {a b : ℕ}
    (ha : a < 2 * 3 ^ k) (hb : b < 2 * 3 ^ k) (hab : a ≠ b) :
    ((2 : ZMod (3 ^ (k + 2))) ^ a - 2 ^ b) * 3 ≠ 0 := by
  intro hz
  have hdiv : (((3 ^ (k + 2) : ℕ) : ℤ)) ∣ ((2 : ℤ) ^ a - 2 ^ b) * 3 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa only [Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_ofNat] using hz
  rw [Nat.cast_pow, Nat.cast_ofNat, show k + 2 = (k + 1) + 1 by omega,
    pow_succ, Int.mul_dvd_mul_iff_right (by norm_num : (3 : ℤ) ≠ 0)] at hdiv
  have hlow : (2 : ZMod (3 ^ (k + 1))) ^ a = 2 ^ b := by
    apply sub_eq_zero.mp
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((2 : ℤ) ^ a - 2 ^ b) (3 ^ (k + 1))).2 (by exact_mod_cast hdiv)
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_ofNat] using hc
  exact hab (pow_injOn_Iio_orderOf (x := (2 : ZMod (3 ^ (k + 1))))
    (by simpa only [Set.mem_Iio, orderOf_two_three_pow_succ] using ha)
    (by simpa only [Set.mem_Iio, orderOf_two_three_pow_succ] using hb) hlow)

theorem unit_mul_two_pow_sub_mul_three_ne_zero (k : ℕ)
    (w : ZMod (3 ^ (k + 2))) (hw : IsUnit w) {a b : ℕ}
    (ha : a < 2 * 3 ^ k) (hb : b < 2 * 3 ^ k) (hab : a ≠ b) :
    (w * ((2 : ZMod (3 ^ (k + 2))) ^ a - 2 ^ b)) * 3 ≠ 0 := by
  intro hz
  apply two_pow_sub_mul_three_ne_zero k ha hb hab
  apply hw.mul_right_eq_zero.mp
  simpa only [mul_assoc] using hz

end XiNormality
