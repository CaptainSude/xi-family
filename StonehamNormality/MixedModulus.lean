import StonehamNormality.PrimeFive

/-!
# Complete cancellation for moduli supported on three and five

The full principal five-kernel is contained in the powers of two. Averaging
over that kernel gives the complete sums used by the inner orthogonality bound.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace StonehamNormality

/-- A principal five-adic unit is a power of two whose exponent is divisible
by four and may also be required to contain any fixed power of three. -/
theorem five_principal_power_representation (r k : ℕ)
    (z : ZMod (5 ^ (k + 2))) :
    ∃ d : ℕ, 4 ∣ d ∧ (2 : ZMod (5 ^ (k + 2))) ^ (d * 3 ^ r) = 1 + 5 * z := by
  let R := ZMod (5 ^ (k + 2))
  have hnil : IsNilpotent ((5 : R) * z) := by
    refine ⟨k + 2, ?_⟩
    rw [mul_pow]
    have hz : (5 : R) ^ (k + 2) = 0 := by
      simpa only [R, Nat.cast_pow, Nat.cast_ofNat] using
        ZMod.natCast_self (5 ^ (k + 2))
    rw [hz, zero_mul]
  have hx : IsUnit ((1 : R) + 5 * z) :=
    hnil.isUnit_add_left_of_commute isUnit_one (Commute.all _ _)
  let x : Rˣ := hx.unit
  have hxval : (x : R) = 1 + 5 * z := IsUnit.unit_spec _
  have hcard : Nat.card Rˣ = 4 * 5 ^ (k + 1) := by
    simp [R, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 5), mul_comm]
  have hc : (Nat.card Rˣ).Coprime (3 ^ r) := by
    rw [hcard]
    exact ((show Nat.Coprime 4 3 by norm_num).mul_left
      ((show Nat.Coprime 5 3 by norm_num).pow_left (k + 1))).pow_right r
  let v : ℕ := ((3 ^ r : ℕ)⁻¹ : ZMod (Nat.card Rˣ)).val
  let y : Rˣ := x ^ v
  have hy : y ^ (3 ^ r) = x := pow_zmod_val_inv_pow hc x
  obtain ⟨d, hd⟩ := (twoFiveUnit_powers_bijective (k + 1)).surjective y
  have hdval : (2 : R) ^ (d : ℕ) = (y : R) := by
    have h := congrArg (fun u : Rˣ => (u : R)) hd
    simpa only [Units.val_pow_eq_pow_val, coe_twoFiveUnit] using h
  let π : R →+* ZMod 5 :=
    ZMod.castHom (dvd_pow_self 5 (by omega : k + 2 ≠ 0)) (ZMod 5)
  have hπfive : π (5 : R) = 0 := by
    change π ((5 : ℕ) : R) = 0
    rw [map_natCast]
    decide
  have hπtwo : π (2 : R) = (2 : ZMod 5) := map_natCast π 2
  have hπx : π (x : R) = 1 := by rw [hxval]; simp [hπfive]
  have hπy : π (y : R) = 1 := by
    change π ((x ^ v : Rˣ) : R) = 1
    simp only [Units.val_pow_eq_pow_val, map_pow, hπx, one_pow]
  have hdmod : (2 : ZMod 5) ^ (d : ℕ) = 1 := by
    have h := congrArg π hdval
    simpa only [map_pow, hπtwo, hπy] using h
  have hd4 : 4 ∣ (d : ℕ) := by
    simpa only [orderOf_two_mod_five] using orderOf_dvd_of_pow_eq_one hdmod
  refine ⟨d, hd4, ?_⟩
  rw [pow_mul, hdval]
  have hyval := congrArg (fun u : Rˣ => (u : R)) hy
  simpa only [Units.val_pow_eq_pow_val, hxval] using hyval

theorem two_pow_four_mul_three_pow (r : ℕ) :
    (2 : ZMod (3 ^ r)) ^ (4 * 3 ^ r) = 1 := by
  cases r with
  | zero => decide
  | succ r =>
    have heq : 4 * 3 ^ (r + 1) = (2 * 3 ^ r) * 6 := by rw [pow_succ]; ring
    rw [heq, pow_mul, ← XiNormality.orderOf_two_three_pow_succ r,
      pow_orderOf_eq_one, one_pow]

/-- Every element of the full principal five-kernel is a power of two. -/
theorem mixed_kernel_mem_powers (r k : ℕ) (z : ZMod (3 ^ r * 5 ^ (k + 2))) :
    ∃ d : ℕ, (2 : ZMod (3 ^ r * 5 ^ (k + 2))) ^ d =
      1 + ((3 ^ r * 5 : ℕ) : ZMod (3 ^ r * 5 ^ (k + 2))) * z := by
  let E := ZMod.chineseRemainder
    (((show Nat.Coprime 3 5 by norm_num).pow_left r).pow_right (k + 2))
  obtain ⟨d, hd4, hd5⟩ := five_principal_power_representation r k
    (((3 ^ r : ℕ) : ZMod (5 ^ (k + 2))) * (E z).2)
  have hd3 : (2 : ZMod (3 ^ r)) ^ (d * 3 ^ r) = 1 := by
    obtain ⟨m, hm⟩ := hd4
    rw [hm, show 4 * m * 3 ^ r = (4 * 3 ^ r) * m by ring,
      pow_mul, two_pow_four_mul_three_pow, one_pow]
  refine ⟨d * 3 ^ r, E.injective ?_⟩
  rw [map_pow, map_add, map_mul, map_one, map_natCast]
  have htwo : E (2 : ZMod (3 ^ r * 5 ^ (k + 2))) =
      (2 : ZMod (3 ^ r) × ZMod (5 ^ (k + 2))) := map_natCast E 2
  rw [htwo]
  apply Prod.ext
  · change (2 : ZMod (3 ^ r)) ^ (d * 3 ^ r) =
      1 + ((3 ^ r * 5 : ℕ) : ZMod (3 ^ r)) * (E z).1
    rw [hd3, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_mul, add_zero]
  · change (2 : ZMod (5 ^ (k + 2))) ^ (d * 3 ^ r) =
      1 + ((3 ^ r * 5 : ℕ) : ZMod (5 ^ (k + 2))) * (E z).2
    rw [hd5, Nat.cast_mul]
    ring

/-- Translation invariance of a finite multiplicative orbit forces additive
character cancellation when the translating character is nontrivial. -/
theorem sum_powers_addChar_eq_zero_of_add_closed {R : Type*} [CommRing R]
    (ψ : AddChar R ℂ) (x w s : R)
    (hclosed : ∀ i : Fin (orderOf x), ∃ j : Fin (orderOf x),
      x ^ (j : ℕ) = x ^ (i : ℕ) + s)
    (hne : ψ (w * s) ≠ 1) :
    ∑ t ∈ Finset.range (orderOf x), ψ (w * x ^ t) = 0 := by
  classical
  let g : Fin (orderOf x) → Fin (orderOf x) := fun i => Classical.choose (hclosed i)
  have hg (i : Fin (orderOf x)) : x ^ (g i : ℕ) = x ^ (i : ℕ) + s :=
    Classical.choose_spec (hclosed i)
  have hginj : Function.Injective g := by
    intro i j hij
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := x) i.isLt j.isLt
    apply add_right_cancel (b := s)
    have hi := hg i
    rw [hij] at hi
    exact hi.symm.trans (hg j)
  have hgbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).2 ⟨hginj, rfl⟩
  have hperm := (Equiv.ofBijective g hgbij).sum_comp
    (fun i : Fin (orderOf x) => ψ (w * x ^ (i : ℕ)))
  change (∑ i : Fin (orderOf x), ψ (w * x ^ (g i : ℕ))) =
    ∑ i : Fin (orderOf x), ψ (w * x ^ (i : ℕ)) at hperm
  simp_rw [hg, mul_add, AddChar.map_add_eq_mul, ← Finset.sum_mul] at hperm
  have hz : (∑ i : Fin (orderOf x), ψ (w * x ^ (i : ℕ))) *
      (ψ (w * s) - 1) = 0 := by linear_combination hperm
  have hzero : (∑ i : Fin (orderOf x), ψ (w * x ^ (i : ℕ))) = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact (hne (sub_eq_zero.mp h)).elim
  rw [← Fin.sum_univ_eq_sum_range (fun t : ℕ => ψ (w * x ^ t))]
  exact hzero

theorem isUnit_two_mixed (r k : ℕ) : IsUnit (2 : ZMod (3 ^ r * 5 ^ (k + 2))) := by
  exact (ZMod.unitOfCoprime 2
    (((show Nat.Coprime 2 3 by norm_num).pow_right r).mul_right
      ((show Nat.Coprime 2 5 by norm_num).pow_right (k + 2)))).isUnit

/-- Addition of the kernel step preserves the complete powers-of-two orbit. -/
theorem mixed_power_orbit_add_closed (r k : ℕ)
    (i : Fin (orderOf (2 : ZMod (3 ^ r * 5 ^ (k + 2))))) :
    ∃ j : Fin (orderOf (2 : ZMod (3 ^ r * 5 ^ (k + 2)))),
      (2 : ZMod (3 ^ r * 5 ^ (k + 2))) ^ (j : ℕ) =
        2 ^ (i : ℕ) + ((3 ^ r * 5 : ℕ) : ZMod (3 ^ r * 5 ^ (k + 2))) := by
  let R := ZMod (3 ^ r * 5 ^ (k + 2))
  have hu : IsUnit ((2 : R) ^ (i : ℕ)) := (isUnit_two_mixed r k).pow _
  let u : Rˣ := hu.unit
  obtain ⟨d, hd⟩ := mixed_kernel_mem_powers r k ((u⁻¹ : Rˣ) : R)
  have hcancel : (2 : R) ^ (i : ℕ) * ((u⁻¹ : Rˣ) : R) = 1 := by
    rw [← IsUnit.unit_spec hu]
    exact Units.mul_inv u
  have hnext : (2 : R) ^ ((i : ℕ) + d) =
      2 ^ (i : ℕ) + ((3 ^ r * 5 : ℕ) : R) := by
    rw [pow_add, hd]
    calc
      _ = (2 : R) ^ (i : ℕ) + ((3 ^ r * 5 : ℕ) : R) *
          ((2 : R) ^ (i : ℕ) * ((u⁻¹ : Rˣ) : R)) := by ring
      _ = _ := by rw [hcancel, mul_one]
  refine ⟨⟨((i : ℕ) + d) % orderOf (2 : R),
    Nat.mod_lt _ (isUnit_two_mixed r k).isOfFinOrder.orderOf_pos⟩, ?_⟩
  change (2 : R) ^ (((i : ℕ) + d) % orderOf (2 : R)) = _
  rw [pow_mod_orderOf]
  exact hnext

/-- Complete mixed-modulus sums vanish when the full five-kernel character
is nontrivial. The hypothesis is the ring form of five-adic denominator survival. -/
theorem mixed_sum_powers_eq_zero (r k : ℕ)
    (w : ZMod (3 ^ r * 5 ^ (k + 2)))
    (hw : w * ((3 ^ r * 5 : ℕ) : ZMod (3 ^ r * 5 ^ (k + 2))) ≠ 0) :
    ∑ t ∈ Finset.range (orderOf (2 : ZMod (3 ^ r * 5 ^ (k + 2)))),
      ZMod.stdAddChar (w * 2 ^ t) = 0 := by
  apply sum_powers_addChar_eq_zero_of_add_closed ZMod.stdAddChar 2 w
    ((3 ^ r * 5 : ℕ) : ZMod (3 ^ r * 5 ^ (k + 2)))
    (mixed_power_orbit_add_closed r k)
  intro h
  apply hw
  apply ZMod.injective_stdAddChar
  simpa only [AddChar.map_zero_eq_one] using h

/-- Short distinct shifts retain a nontrivial character on the five-kernel. -/
theorem mixed_unit_mul_two_pow_sub_step_ne_zero (r k : ℕ)
    (w : ZMod (3 ^ r * 5 ^ (k + 2))) (hw : IsUnit w) {a b : ℕ}
    (ha : a < 4 * 5 ^ k) (hb : b < 4 * 5 ^ k) (hab : a ≠ b) :
    (w * (2 ^ a - 2 ^ b)) *
      ((3 ^ r * 5 : ℕ) : ZMod (3 ^ r * 5 ^ (k + 2))) ≠ 0 := by
  intro hz
  let π : ZMod (3 ^ r * 5 ^ (k + 2)) →+* ZMod (5 ^ (k + 2)) :=
    ZMod.castHom (dvd_mul_left _ _) (ZMod (5 ^ (k + 2)))
  have htwo : π 2 = 2 := map_natCast π 2
  have hstep : π ((3 ^ r * 5 : ℕ) : ZMod (3 ^ r * 5 ^ (k + 2))) =
      ((3 ^ r : ℕ) : ZMod (5 ^ (k + 2))) * 5 := by
    rw [map_natCast, Nat.cast_mul]
    rfl
  have hz5 := congrArg π hz
  simp only [map_mul, map_sub, map_pow, htwo, hstep, map_zero] at hz5
  have hthree : IsUnit (((3 ^ r : ℕ) : ZMod (5 ^ (k + 2)))) :=
    (ZMod.unitOfCoprime (3 ^ r)
      (((show Nat.Coprime 3 5 by norm_num).pow_left r).pow_right (k + 2))).isUnit
  have hproduct : (π w * ((3 ^ r : ℕ) : ZMod (5 ^ (k + 2)))) *
      (((2 : ZMod (5 ^ (k + 2))) ^ a - 2 ^ b) * 5) = 0 := by
    convert hz5 using 1
    ring
  apply two_pow_sub_mul_five_ne_zero k ha hb hab
  exact ((hw.map π).mul hthree).mul_right_eq_zero.mp hproduct

/-- Correlations of distinct shifts are complete mixed-modulus character sums. -/
theorem mixed_correlation_zero (r k : ℕ)
    (w : ZMod (3 ^ r * 5 ^ (k + 2))) (hw : IsUnit w) {a b : ℕ}
    (ha : a < 4 * 5 ^ k) (hb : b < 4 * 5 ^ k) (hab : a ≠ b) :
    ∑ t ∈ Finset.range (orderOf (2 : ZMod (3 ^ r * 5 ^ (k + 2)))),
      ZMod.stdAddChar (w * 2 ^ (t + a)) *
        conj (ZMod.stdAddChar (w * 2 ^ (t + b))) = 0 := by
  have hterm (t : ℕ) :
      ZMod.stdAddChar (w * 2 ^ (t + a)) *
          conj (ZMod.stdAddChar (w * 2 ^ (t + b))) =
        ZMod.stdAddChar ((w * (2 ^ a - 2 ^ b)) * 2 ^ t) := by
    rw [XiNormality.conj_stdAddChar, ← AddChar.map_add_eq_mul]
    congr 1
    simp only [pow_add]
    ring
  simp_rw [hterm]
  exact mixed_sum_powers_eq_zero r k _
    (mixed_unit_mul_two_pow_sub_step_ne_zero r k w hw ha hb hab)

theorem mixed_unit_mean_zero (r k : ℕ)
    (w : ZMod (3 ^ r * 5 ^ (k + 2))) (hw : IsUnit w) :
    ∑ t ∈ Finset.range (orderOf (2 : ZMod (3 ^ r * 5 ^ (k + 2)))),
      ZMod.stdAddChar (w * 2 ^ t) = 0 := by
  apply mixed_sum_powers_eq_zero r k w
  have h := mixed_unit_mul_two_pow_sub_step_ne_zero r k w hw (a := 1) (b := 0)
    (by
      have hp : 0 < 5 ^ k := by positivity
      omega) (by positivity) (by decide)
  simpa only [pow_one, pow_zero,
    show (2 : ZMod (3 ^ r * 5 ^ (k + 2))) - 1 = 1 by ring, mul_one] using h

theorem mixed_powers_periodic (r k : ℕ) (w : ZMod (3 ^ r * 5 ^ (k + 2))) :
    Function.Periodic (fun t : ℕ => ZMod.stdAddChar (w * 2 ^ t))
      (orderOf (2 : ZMod (3 ^ r * 5 ^ (k + 2)))) := by
  intro t
  change ZMod.stdAddChar (w * 2 ^ (t + orderOf (2 : ZMod (3 ^ r * 5 ^ (k + 2))))) = _
  simp only [pow_add, pow_orderOf_eq_one, mul_one]

theorem mixed_order_pos (r k : ℕ) :
    0 < orderOf (2 : ZMod (3 ^ r * 5 ^ (k + 2))) :=
  (isUnit_two_mixed r k).isOfFinOrder.orderOf_pos

theorem mixed_order_le_modulus (r k : ℕ) :
    orderOf (2 : ZMod (3 ^ r * 5 ^ (k + 2))) ≤ 3 ^ r * 5 ^ (k + 2) := by
  simpa only [ZMod.card] using
    (orderOf_le_card_univ (x := (2 : ZMod (3 ^ r * 5 ^ (k + 2)))))

/-- The inner orthogonality estimate, uniform in the length of the sum.
The only restriction on the averaging length is the next lower five-power order. -/
theorem mixed_arbitrary_length_bound (r k L H : ℕ)
    (w : ZMod (3 ^ r * 5 ^ (k + 2))) (hw : IsUnit w) (hH : H ≤ 4 * 5 ^ k) :
    (H : ℝ) * ‖∑ t ∈ Finset.range L, ZMod.stdAddChar (w * 2 ^ t)‖ ≤
      Real.sqrt (((orderOf (2 : ZMod (3 ^ r * 5 ^ (k + 2)))) : ℝ) *
        ((H : ℝ) * (orderOf (2 : ZMod (3 ^ r * 5 ^ (k + 2)))))) +
          2 * (H : ℝ) ^ 2 := by
  let T := orderOf (2 : ZMod (3 ^ r * 5 ^ (k + 2)))
  have hreduce := XiNormality.sum_range_eq_mod_of_periodic_zero
    (fun t => ZMod.stdAddChar (w * 2 ^ t)) T
    (mixed_powers_periodic r k w) (mixed_unit_mean_zero r k w hw) L
  rw [hreduce]
  have hLT : L % T ≤ T := (Nat.mod_lt _ (mixed_order_pos r k)).le
  have hbound := XiNormality.sliding_window_bound
    (fun t => ZMod.stdAddChar (w * 2 ^ t)) (L % T) H T hLT
    (fun t => XiNormality.norm_stdAddChar _)
    (fun a ha b hb hab => mixed_correlation_zero r k w hw
      ((Finset.mem_range.mp ha).trans_le hH)
      ((Finset.mem_range.mp hb).trans_le hH) hab)
  refine hbound.trans ?_
  gcongr

/-- The prime-five specialization handles the zero-coordinate case directly. -/
theorem five_arbitrary_length_bound (k L H : ℕ)
    (w : ZMod (5 ^ (k + 2))) (hw : IsUnit w) (hH : H ≤ 4 * 5 ^ k) :
    (H : ℝ) * ‖∑ t ∈ Finset.range L, ZMod.stdAddChar (w * 2 ^ t)‖ ≤
      Real.sqrt ((4 * (5 : ℝ) ^ (k + 1)) *
        ((H : ℝ) * (4 * 5 ^ (k + 1)))) + 2 * (H : ℝ) ^ 2 := by
  have hsep {a b : ℕ} (ha : a < 4 * 5 ^ k) (hb : b < 4 * 5 ^ k) (hab : a ≠ b) :
      (w * (2 ^ a - 2 ^ b)) * 5 ≠ 0 := by
    intro hz
    apply two_pow_sub_mul_five_ne_zero k ha hb hab
    apply hw.mul_right_eq_zero.mp
    simpa only [mul_assoc] using hz
  have hmean : w * 5 ≠ 0 := by
    have h := hsep (a := 1) (b := 0)
      (by have hp : 0 < 5 ^ k := by positivity
          omega) (by positivity) (by decide)
    simpa only [pow_one, pow_zero, show (2 : ZMod (5 ^ (k + 2))) - 1 = 1 by ring,
      mul_one] using h
  have hzero := sum_powers_stdAddChar_five_pow_eq_zero (k + 1) w hmean
  have hperiod : Function.Periodic
      (fun t : ℕ => ZMod.stdAddChar (w * 2 ^ t)) (4 * 5 ^ (k + 1)) := by
    have hp : (2 : ZMod (5 ^ (k + 2))) ^ (4 * 5 ^ (k + 1)) = 1 := by
      rw [← orderOf_two_five_pow_succ (k + 1)]
      exact pow_orderOf_eq_one _
    intro t
    change ZMod.stdAddChar (w * 2 ^ (t + (4 * 5 ^ (k + 1)))) = _
    rw [pow_add (2 : ZMod (5 ^ (k + 2))) t (4 * 5 ^ (k + 1)), hp, mul_one]
  have horth : ∀ a ∈ Finset.range H, ∀ b ∈ Finset.range H, a ≠ b →
      ∑ t ∈ Finset.range (4 * 5 ^ (k + 1)),
        ZMod.stdAddChar (w * 2 ^ (t + a)) *
          conj (ZMod.stdAddChar (w * 2 ^ (t + b))) = 0 := by
    intro a ha b hb hab
    have hterm (t : ℕ) :
        ZMod.stdAddChar (w * 2 ^ (t + a)) *
            conj (ZMod.stdAddChar (w * 2 ^ (t + b))) =
          ZMod.stdAddChar ((w * (2 ^ a - 2 ^ b)) * 2 ^ t) := by
      rw [XiNormality.conj_stdAddChar, ← AddChar.map_add_eq_mul]
      congr 1
      simp only [pow_add]
      ring
    simp_rw [hterm]
    exact sum_powers_stdAddChar_five_pow_eq_zero (k + 1) _
      (hsep ((Finset.mem_range.mp ha).trans_le hH)
        ((Finset.mem_range.mp hb).trans_le hH) hab)
  have hreduce := XiNormality.sum_range_eq_mod_of_periodic_zero
    (fun t => ZMod.stdAddChar (w * 2 ^ t)) (4 * 5 ^ (k + 1)) hperiod hzero L
  rw [hreduce]
  have hLT : L % (4 * 5 ^ (k + 1)) ≤ 4 * 5 ^ (k + 1) :=
    (Nat.mod_lt _ (by positivity)).le
  have hbound := XiNormality.sliding_window_bound
    (fun t => ZMod.stdAddChar (w * 2 ^ t)) (L % (4 * 5 ^ (k + 1))) H
    (4 * 5 ^ (k + 1)) hLT (fun t => XiNormality.norm_stdAddChar _) horth
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hbound
  refine hbound.trans ?_
  gcongr
  exact_mod_cast hLT

end StonehamNormality
