import StonehamNormality.GeneralKernel
import Mathlib.NumberTheory.Multiplicity

noncomputable section

namespace StonehamNormality

theorem prime_not_dvd_of_dvd_sub_one {p g : ℕ} (hp : p.Prime)
    (hg : 1 ≤ g) (hpg : p ∣ g - 1) : ¬ p ∣ g := by
  intro h
  have h1 := Nat.dvd_sub h hpg
  have he : g - (g - 1) = 1 := by omega
  rw [he] at h1
  exact hp.not_dvd_one h1

/-- Exact two-adic lifting in the principal kernel of depth two. -/
theorem two_padicVal_pow_sub_one {g j : ℕ} (hg : 1 < g)
    (hfour : 4 ∣ g - 1) (hj : j ≠ 0) :
    padicValNat 2 (g ^ j - 1) = padicValNat 2 (g - 1) + padicValNat 2 j := by
  have htwo : 2 ∣ g - 1 := (by norm_num : 2 ∣ 4).trans hfour
  have hgodd := prime_not_dvd_of_dvd_sub_one Nat.prime_two hg.le htwo
  have hfourI : (4 : ℤ) ∣ (g : ℤ) - 1 := by
    have hc : (4 : ℤ) ∣ ((g - 1 : ℕ) : ℤ) := by exact_mod_cast hfour
    simpa only [Nat.cast_sub hg.le, Nat.cast_one] using hc
  have hgoddI : ¬ (2 : ℤ) ∣ (g : ℤ) := by exact_mod_cast hgodd
  have h := Int.two_pow_sub_pow' (x := (g : ℤ)) (y := 1) j hfourI hgoddI
  have hg0 : g - 1 ≠ 0 := by omega
  have hpow : g ^ j - 1 ≠ 0 := by
    have := one_lt_pow₀ hg hj
    omega
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add,
    padicValNat_eq_emultiplicity hpow, padicValNat_eq_emultiplicity hg0,
    padicValNat_eq_emultiplicity hj]
  simp only [one_pow] at h
  rw [← Int.natCast_emultiplicity, ← Int.natCast_emultiplicity,
    ← Int.natCast_emultiplicity]
  simpa only [Nat.cast_sub (one_le_pow₀ hg.le), Nat.cast_sub hg.le,
    Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] using h

/-- Local lifting holds at every prime dividing a supported modulus. -/
theorem lifting_valuations_of_prime_support (g q : ℕ) (hg : 1 < g)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ g - 1)
    (hfour : 2 ∣ q → 4 ∣ g - 1) :
    ∀ p : ℕ, p.Prime → p ∣ q → ∀ j : ℕ, j ≠ 0 →
      padicValNat p (g ^ j - 1) = padicValNat p (g - 1) + padicValNat p j := by
  intro p hp hpq j hj
  by_cases hp2 : p = 2
  · subst p
    exact two_padicVal_pow_sub_one hg (hfour hpq) hj
  · letI : Fact p.Prime := ⟨hp⟩
    simpa only [one_pow] using
      padicValNat.pow_sub_pow (hp.odd_of_ne_two hp2) hg (hsupport p hp hpq)
        (prime_not_dvd_of_dvd_sub_one hp hg.le (hsupport p hp hpq)) hj

theorem div_gcd_dvd_iff_dvd_mul (q D j : ℕ) (hq : 0 < q) :
    q / Nat.gcd q D ∣ j ↔ q ∣ D * j := by
  let d := Nat.gcd q D
  have hd : 0 < d := Nat.gcd_pos_of_pos_left D hq
  have hc : (q / d).Coprime (D / d) := Nat.coprime_div_gcd_div_gcd hd
  calc
    _ ↔ q / d ∣ (D / d) * j := hc.dvd_mul_left.symm
    _ ↔ q ∣ d * ((D / d) * j) :=
      Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left q D) hd
    _ ↔ q ∣ D * j := by rw [← Nat.mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_right q D)]

/-- Exact local lifting identities determine divisibility at a composite modulus. -/
theorem pow_sub_one_dvd_iff_of_valuations (g q : ℕ) (hg : 1 < g) (hq : 0 < q)
    (hv : ∀ p : ℕ, p.Prime → p ∣ q → ∀ j : ℕ, j ≠ 0 →
      padicValNat p (g ^ j - 1) = padicValNat p (g - 1) + padicValNat p j)
    (j : ℕ) (hj : j ≠ 0) :
    q ∣ g ^ j - 1 ↔ q ∣ (g - 1) * j := by
  have hg0 : g - 1 ≠ 0 := by omega
  have hpow : g ^ j - 1 ≠ 0 := by
    have := one_lt_pow₀ hg hj
    omega
  rw [← Nat.factorization_prime_le_iff_dvd hq.ne' hpow,
    ← Nat.factorization_prime_le_iff_dvd hq.ne' (mul_ne_zero hg0 hj)]
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  by_cases hpq : p ∣ q
  · letI : Fact p.Prime := ⟨hp⟩
    simp only [Nat.factorization_def _ hp]
    rw [hv p hp hpq j hj, padicValNat.mul hg0 hj]
  · simp [Nat.factorization_eq_zero_of_not_dvd hpq]

/-- A composite order formula from exact local lifting identities. -/
theorem orderOf_eq_div_gcd_of_valuations (g q : ℕ) (hg : 1 < g) (hq : 0 < q)
    (hv : ∀ p : ℕ, p.Prime → p ∣ q → ∀ j : ℕ, j ≠ 0 →
      padicValNat p (g ^ j - 1) = padicValNat p (g - 1) + padicValNat p j) :
    orderOf (g : ZMod q) = q / Nat.gcd q (g - 1) := by
  have hN := Nat.div_gcd_pos_of_pos_left (g - 1) hq
  have hpow (j : ℕ) (hj : j ≠ 0) :
      (g : ZMod q) ^ j = 1 ↔ q / Nat.gcd q (g - 1) ∣ j := by
    have hc : ((g ^ j - 1 : ℕ) : ZMod q) = (g : ZMod q) ^ j - 1 := by
      rw [Nat.cast_sub (one_le_pow₀ hg.le), Nat.cast_pow, Nat.cast_one]
    rw [← sub_eq_zero, ← hc, ZMod.natCast_eq_zero_iff,
      pow_sub_one_dvd_iff_of_valuations g q hg hq hv j hj,
      ← div_gcd_dvd_iff_dvd_mul q (g - 1) j hq]
  apply (orderOf_eq_iff hN).2
  constructor
  · exact (hpow _ hN.ne').2 (dvd_refl _)
  · intro j hj hj0 h
    have hd := (hpow j hj0.ne').1 h
    exact (Nat.le_of_dvd hj0 hd).not_gt hj

/-- Principal-unit order at an arbitrary supported composite modulus. -/
theorem orderOf_eq_div_gcd_of_prime_support (g q : ℕ) (hg : 1 < g) (hq : 0 < q)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ g - 1)
    (hfour : 2 ∣ q → 4 ∣ g - 1) :
    orderOf (g : ZMod q) = q / Nat.gcd q (g - 1) :=
  orderOf_eq_div_gcd_of_valuations g q hg hq
    (lifting_valuations_of_prime_support g q hg hsupport hfour)

/-- Every principal kernel element is a power, for arbitrary finite prime support. -/
theorem principal_kernel_mem_powers_of_prime_support (g q : ℕ)
    (hg : 1 < g) (hq : 0 < q)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ g - 1)
    (hfour : 2 ∣ q → 4 ∣ g - 1) (z : ZMod q) :
    ∃ j : ℕ, (g : ZMod q) ^ j = 1 + (Nat.gcd q (g - 1) : ZMod q) * z := by
  let d := Nat.gcd q (g - 1)
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left (g - 1) hq
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : NeZero d := ⟨hd0.ne'⟩
  have hd : d ∣ q := Nat.gcd_dvd_left q (g - 1)
  apply principal_kernel_mem_powers_of_order q d hd (g : ZMod q) _
    (orderOf_eq_div_gcd_of_prime_support g q hg hq hsupport hfour) z
  rw [map_natCast]
  apply sub_eq_zero.mp
  have hc : ((g - 1 : ℕ) : ZMod d) = (g : ZMod d) - 1 := by
    rw [Nat.cast_sub hg.le, Nat.cast_one]
  rw [← hc, ZMod.natCast_eq_zero_iff]
  exact Nat.gcd_dvd_right q (g - 1)

/-- The principal kernel generated by a power of the base is also generated
by the base itself. This is the interface used by the character-sum argument. -/
theorem base_principal_kernel_mem_powers (b C q : ℕ) (hb : 1 < b) (hC : C ≠ 0)
    (hq : 0 < q)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ b ^ C - 1)
    (hfour : 2 ∣ q → 4 ∣ b ^ C - 1) (z : ZMod q) :
    ∃ j : ℕ, (b : ZMod q) ^ j = 1 + (Nat.gcd q (b ^ C - 1) : ZMod q) * z := by
  obtain ⟨j, hj⟩ := principal_kernel_mem_powers_of_prime_support (b ^ C) q
    (one_lt_pow₀ hb hC) hq hsupport hfour z
  refine ⟨C * j, ?_⟩
  simpa only [Nat.cast_pow, pow_mul] using hj

/-- Fixed prime support forces a linear lower bound on the base's order. -/
theorem base_order_lower_bound_of_prime_support (b C q : ℕ)
    (hb : 1 < b) (hC : C ≠ 0) (hq : 0 < q) (hcop : b.Coprime q)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ b ^ C - 1)
    (hfour : 2 ∣ q → 4 ∣ b ^ C - 1) :
    q ≤ (b ^ C - 1) * orderOf (b : ZMod q) := by
  have hg := one_lt_pow₀ hb hC
  have hD : 0 < b ^ C - 1 := by omega
  have horder : orderOf ((b : ZMod q) ^ C) = q / Nat.gcd q (b ^ C - 1) := by
    simpa only [Nat.cast_pow] using
      orderOf_eq_div_gcd_of_prime_support (b ^ C) q hg hq hsupport hfour
  have hordpos : 0 < orderOf (b : ZMod q) :=
    (ZMod.unitOfCoprime b hcop).isUnit.isOfFinOrder.orderOf_pos
  have hle : q / Nat.gcd q (b ^ C - 1) ≤ orderOf (b : ZMod q) := by
    rw [← horder]
    exact Nat.le_of_dvd hordpos (orderOf_pow_dvd C)
  calc
    q = Nat.gcd q (b ^ C - 1) * (q / Nat.gcd q (b ^ C - 1)) :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left q (b ^ C - 1))).symm
    _ ≤ (b ^ C - 1) * orderOf (b : ZMod q) :=
      Nat.mul_le_mul (Nat.gcd_le_right q hD) hle

/-- Multiplication by a divisor can be cancelled after reducing the modulus. -/
theorem reduction_eq_zero_of_mul_divisor_eq_zero (q d : ℕ)
    (hq : 0 < q) (hd0 : 0 < d) (hd : d ∣ q) (z : ZMod q)
    (hz : z * (d : ZMod q) = 0) :
    ZMod.castHom (Nat.div_dvd_of_dvd hd) (ZMod (q / d)) z = 0 := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hc : q ∣ d * z.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).1
    simpa only [Nat.cast_mul, ZMod.natCast_zmod_val, mul_comm] using hz
  have hred : q / d ∣ z.val := (Nat.div_dvd_iff_dvd_mul hd hd0).2 hc
  calc
    _ = ((z.val : ℕ) : ZMod (q / d)) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val z]
      exact map_natCast _ _
    _ = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hred

/-- Distinct short shifts remain distinct on the principal kernel. -/
theorem principal_kernel_shift_separation (b q d H : ℕ)
    (hq : 0 < q) (hd0 : 0 < d) (hd : d ∣ q)
    (hH : H ≤ orderOf (b : ZMod (q / d)))
    (i j : ℕ) (hi : i < H) (hj : j < H) (hij : i ≠ j) :
    ((b : ZMod q) ^ i - b ^ j) * (d : ZMod q) ≠ 0 := by
  intro h
  have hz := reduction_eq_zero_of_mul_divisor_eq_zero q d hq hd0 hd
    ((b : ZMod q) ^ i - b ^ j) h
  simp only [map_sub, map_pow, map_natCast] at hz
  apply hij
  exact pow_injOn_Iio_orderOf (x := (b : ZMod (q / d)))
    (hi.trans_le hH) (hj.trans_le hH) (sub_eq_zero.mp hz)

/-- The fixed squared index supplies the separation range required for
inner orthogonality at every supported modulus. -/
theorem base_principal_kernel_shift_separation (b C q H : ℕ)
    (hb : 1 < b) (hC : C ≠ 0) (hq : 0 < q) (hcop : b.Coprime q)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ b ^ C - 1)
    (hfour : 2 ∣ q → 4 ∣ b ^ C - 1)
    (hH : H * (b ^ C - 1) ^ 2 ≤ q)
    (i j : ℕ) (hi : i < H) (hj : j < H) (hij : i ≠ j) :
    ((b : ZMod q) ^ i - b ^ j) * (Nat.gcd q (b ^ C - 1) : ZMod q) ≠ 0 := by
  let D := b ^ C - 1
  let d := Nat.gcd q D
  have hD : 0 < D := by
    have := one_lt_pow₀ hb hC
    dsimp [D]
    omega
  have hd : d ∣ q := Nat.gcd_dvd_left q D
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left D hq
  have hQ : 0 < q / d := Nat.div_gcd_pos_of_pos_left D hq
  have hQdvd : q / d ∣ q := Nat.div_dvd_of_dvd hd
  have horder := base_order_lower_bound_of_prime_support b C (q / d) hb hC hQ
    (hcop.of_dvd_right hQdvd)
    (fun p hp hpq => hsupport p hp (hpq.trans hQdvd))
    (fun h2 => hfour (h2.trans hQdvd))
  have htotal : q ≤ D ^ 2 * orderOf (b : ZMod (q / d)) := by
    calc
      q = d * (q / d) := (Nat.mul_div_cancel' hd).symm
      _ ≤ D * (D * orderOf (b : ZMod (q / d))) :=
        Nat.mul_le_mul (Nat.gcd_le_right q hD) horder
      _ = _ := by ring
  have hrange : H ≤ orderOf (b : ZMod (q / d)) := by
    have hs : 0 < D ^ 2 := pow_pos hD 2
    have hh : D ^ 2 * H ≤ D ^ 2 * orderOf (b : ZMod (q / d)) := by
      simpa only [Nat.mul_comm (D ^ 2) H] using hH.trans htotal
    exact Nat.le_of_mul_le_mul_left hh hs
  exact principal_kernel_shift_separation b q d H hq hd0 hd hrange i j hi hj hij

/-- Exact gcd reduction for every positive exponent in a principal kernel. -/
theorem gcd_pow_sub_one_eq_gcd_mul (g q t : ℕ) (hg : 1 < g) (hq : 0 < q)
    (ht : t ≠ 0)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ g - 1)
    (hfour : 2 ∣ q → 4 ∣ g - 1) :
    Nat.gcd q (g ^ t - 1) = Nat.gcd q ((g - 1) * t) := by
  have hlocal (d : ℕ) (hd : d ∣ q) (hd0 : 0 < d) :
      d ∣ g ^ t - 1 ↔ d ∣ (g - 1) * t :=
    pow_sub_one_dvd_iff_of_valuations g d hg hd0
      (lifting_valuations_of_prime_support g d hg
        (fun p hp hpd => hsupport p hp (hpd.trans hd))
        (fun h2 => hfour (h2.trans hd))) t ht
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    exact (hlocal _ (Nat.gcd_dvd_left _ _) (Nat.gcd_pos_of_pos_left _ hq)).1
      (Nat.gcd_dvd_right _ _)
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    exact (hlocal _ (Nat.gcd_dvd_left _ _) (Nat.gcd_pos_of_pos_left _ hq)).2
      (Nat.gcd_dvd_right _ _)

/-- Quantitative denominator survival after an outer differencing stride.
The inequalities use multiplication only, avoiding division inequalities. -/
theorem stride_reduced_modulus_bounds (b C q m j : ℕ)
    (hb : 1 < b) (hC : C ≠ 0) (hq : 0 < q) (hm : 0 < m) (hj : 0 < j)
    (hmq : m ∣ q)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ b ^ C - 1)
    (hfour : 2 ∣ q → 4 ∣ b ^ C - 1) :
    let Q := q / Nat.gcd q (b ^ (j * (C * m)) - 1)
    m * Q ≤ q ∧ q ≤ ((b ^ C - 1) * m * j) * Q := by
  let G := Nat.gcd q (b ^ (j * (C * m)) - 1)
  have hg : 1 < b ^ C := one_lt_pow₀ hb hC
  have hD : 0 < b ^ C - 1 := by omega
  have hexp : b ^ (j * (C * m)) = (b ^ C) ^ (m * j) := by
    rw [← pow_mul]
    congr 1
    ring
  have heq : G = Nat.gcd q ((b ^ C - 1) * m * j) := by
    dsimp [G]
    rw [hexp, gcd_pow_sub_one_eq_gcd_mul (b ^ C) q (m * j) hg hq
      (mul_ne_zero hm.ne' hj.ne') hsupport hfour]
    rw [Nat.mul_assoc]
  have hG : 0 < G := Nat.gcd_pos_of_pos_left _ hq
  have hlo : m ≤ G := by
    apply Nat.le_of_dvd hG
    rw [heq]
    apply Nat.dvd_gcd hmq
    exact dvd_mul_of_dvd_left (dvd_mul_left m (b ^ C - 1)) j
  have hhi : G ≤ (b ^ C - 1) * m * j := by
    rw [heq]
    exact Nat.gcd_le_right _ (mul_pos (mul_pos hD hm) hj)
  have hprod : G * (q / G) = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  change m * (q / G) ≤ q ∧ q ≤ ((b ^ C - 1) * m * j) * (q / G)
  constructor
  · exact (Nat.mul_le_mul_right (q / G) hlo).trans_eq hprod
  · exact hprod.symm.trans_le (Nat.mul_le_mul_right (q / G) hhi)

end StonehamNormality
