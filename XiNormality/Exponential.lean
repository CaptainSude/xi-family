import XiNormality.Orthogonality
import XiNormality.Arithmetic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Data.Nat.Periodic

/-!
# Additive character sums over units

Translation by a nilpotent element permutes the units of a commutative ring.
This makes the vanishing of the Ramanujan sums needed here particularly short:
in `ZMod (3 ^ k)`, translate the units by `3`.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace XiNormality

/-- Adding a nilpotent element is a permutation of the units. -/
def unitsAddEquiv {R : Type*} [CommRing R] (s : R) (hs : IsNilpotent s) : Rˣ ≃ Rˣ where
  toFun u := (hs.isUnit_add_left_of_commute u.isUnit (Commute.all _ _)).unit
  invFun u := (hs.neg.isUnit_add_left_of_commute u.isUnit (Commute.all _ _)).unit
  left_inv u := by
    apply Units.ext
    simp [IsUnit.unit_spec]
  right_inv u := by
    apply Units.ext
    simp [IsUnit.unit_spec]

@[simp] theorem unitsAddEquiv_coe {R : Type*} [CommRing R]
    (s : R) (hs : IsNilpotent s) (u : Rˣ) :
    (unitsAddEquiv s hs u : R) = (u : R) + s :=
  IsUnit.unit_spec _

/-- A character sum over units vanishes if translation by a nilpotent element
multiplies it by a nontrivial scalar. -/
theorem sum_units_addChar_eq_zero {R : Type*} [CommRing R] [Fintype Rˣ]
    (ψ : AddChar R ℂ) (w s : R) (hs : IsNilpotent s) (hne : ψ (w * s) ≠ 1) :
    ∑ u : Rˣ, ψ (w * (u : R)) = 0 := by
  have hperm := (unitsAddEquiv s hs).sum_comp (fun u : Rˣ => ψ (w * (u : R)))
  simp only [unitsAddEquiv_coe, mul_add, AddChar.map_add_eq_mul,
    ← Finset.sum_mul] at hperm
  have hzero : (∑ u : Rˣ, ψ (w * (u : R))) * (ψ (w * s) - 1) = 0 := by
    linear_combination hperm
  rcases mul_eq_zero.mp hzero with h | h
  · exact h
  · exact (hne (sub_eq_zero.mp h)).elim

/-- The only vanishing statement about Ramanujan sums needed for the proof. -/
theorem sum_units_stdAddChar_three_pow_eq_zero (k : ℕ)
    (w : ZMod (3 ^ (k + 1))) (hw : w * 3 ≠ 0) :
    ∑ u : (ZMod (3 ^ (k + 1)))ˣ, ZMod.stdAddChar (w * (u : ZMod _)) = 0 := by
  apply sum_units_addChar_eq_zero ZMod.stdAddChar w 3
  · refine ⟨k + 1, ?_⟩
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      ZMod.natCast_self (3 ^ (k + 1))
  · intro hchar
    apply hw
    apply ZMod.injective_stdAddChar
    simpa only [AddChar.map_zero_eq_one] using hchar

/-- Complete sums along the powers of two inherit the unit-sum vanishing. -/
theorem sum_powers_stdAddChar_three_pow_eq_zero (k : ℕ)
    (w : ZMod (3 ^ (k + 1))) (hw : w * 3 ≠ 0) :
    ∑ t ∈ Finset.range (2 * 3 ^ k), ZMod.stdAddChar (w * 2 ^ t) = 0 := by
  have heq := (twoUnitPowersEquiv k).sum_comp
    (fun u : (ZMod (3 ^ (k + 1)))ˣ => ZMod.stdAddChar (w * (u : ZMod _)))
  have hzero := heq.trans (sum_units_stdAddChar_three_pow_eq_zero k w hw)
  rw [← Fin.sum_univ_eq_sum_range (fun t : ℕ => ZMod.stdAddChar (w * 2 ^ t))]
  simpa only [twoUnitPowersEquiv_apply, Units.val_pow_eq_pow_val, coe_twoUnit] using hzero

@[simp] theorem norm_stdAddChar {N : ℕ} [NeZero N] (x : ZMod N) :
    ‖ZMod.stdAddChar x‖ = 1 := by
  simp [ZMod.stdAddChar_apply]

@[simp] theorem conj_stdAddChar {N : ℕ} [NeZero N] (x : ZMod N) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (norm_stdAddChar x)]

/-- Correlations of two translates reduce to a complete additive-character sum. -/
theorem powers_stdAddChar_correlation_zero (k : ℕ)
    (w : ZMod (3 ^ (k + 1))) (a b : ℕ)
    (hw : (w * (2 ^ a - 2 ^ b)) * 3 ≠ 0) :
    ∑ t ∈ Finset.range (2 * 3 ^ k),
      ZMod.stdAddChar (w * 2 ^ (t + a)) *
        conj (ZMod.stdAddChar (w * 2 ^ (t + b))) = 0 := by
  have hterm (t : ℕ) :
      ZMod.stdAddChar (w * 2 ^ (t + a)) *
          conj (ZMod.stdAddChar (w * 2 ^ (t + b))) =
        ZMod.stdAddChar ((w * (2 ^ a - 2 ^ b)) * 2 ^ t) := by
    rw [conj_stdAddChar, ← AddChar.map_add_eq_mul]
    congr 1
    simp only [pow_add]
    ring
  simp_rw [hterm]
  exact sum_powers_stdAddChar_three_pow_eq_zero k _ hw

/-- The finite analytic estimate, with arithmetic separation of the shifts as
its only remaining hypothesis. -/
theorem powers_stdAddChar_sliding_bound (k : ℕ)
    (w : ZMod (3 ^ (k + 1))) (L H : ℕ) (hL : L ≤ 2 * 3 ^ k)
    (hsep : ∀ a ∈ Finset.range H, ∀ b ∈ Finset.range H, a ≠ b →
      (w * (2 ^ a - 2 ^ b)) * 3 ≠ 0) :
    (H : ℝ) * ‖∑ t ∈ Finset.range L, ZMod.stdAddChar (w * 2 ^ t)‖ ≤
      Real.sqrt ((L : ℝ) * ((H : ℝ) * (2 * 3 ^ k))) + 2 * (H : ℝ) ^ 2 := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
    sliding_window_bound (fun t => ZMod.stdAddChar (w * 2 ^ t)) L H (2 * 3 ^ k) hL
      (fun t => norm_stdAddChar _) (fun a ha b hb hab =>
        powers_stdAddChar_correlation_zero k w a b (hsep a ha b hb hab))

/-- A zero-mean periodic sequence has exactly the same prefix sum after deleting
any number of complete periods. -/
theorem sum_range_eq_mod_of_periodic_zero (f : ℕ → ℂ) (T : ℕ)
    (hperiod : Function.Periodic f T) (hzero : ∑ t ∈ Finset.range T, f t = 0) (L : ℕ) :
    ∑ t ∈ Finset.range L, f t = ∑ t ∈ Finset.range (L % T), f t := by
  have hsums : Function.Periodic (fun L => ∑ t ∈ Finset.range L, f t) T := by
    intro L
    change (∑ t ∈ Finset.range (L + T), f t) = ∑ t ∈ Finset.range L, f t
    rw [Nat.add_comm L T, Finset.sum_range_add, hzero, zero_add]
    apply Finset.sum_congr rfl
    intro t ht
    simpa only [Nat.add_comm] using hperiod t
  exact (hsums.map_mod_nat L).symm

theorem powers_stdAddChar_periodic (k : ℕ) (w : ZMod (3 ^ (k + 1))) :
    Function.Periodic (fun t : ℕ => ZMod.stdAddChar (w * 2 ^ t)) (2 * 3 ^ k) := by
  have hp : (2 : ZMod (3 ^ (k + 1))) ^ (2 * 3 ^ k) = 1 := by
    rw [← orderOf_two_three_pow_succ k]
    exact pow_orderOf_eq_one _
  intro t
  simp only [pow_add, hp, mul_one]

/-- An interval bound independent of its length; complete periods contribute
exactly zero. -/
theorem powers_stdAddChar_arbitrary_length_bound (k : ℕ)
    (w : ZMod (3 ^ (k + 1))) (hw : w * 3 ≠ 0) (L H : ℕ)
    (hsep : ∀ a ∈ Finset.range H, ∀ b ∈ Finset.range H, a ≠ b →
      (w * (2 ^ a - 2 ^ b)) * 3 ≠ 0) :
    (H : ℝ) * ‖∑ t ∈ Finset.range L, ZMod.stdAddChar (w * 2 ^ t)‖ ≤
      Real.sqrt ((2 * (3 : ℝ) ^ k) * ((H : ℝ) * (2 * 3 ^ k))) + 2 * (H : ℝ) ^ 2 := by
  have hreduce := sum_range_eq_mod_of_periodic_zero
    (fun t => ZMod.stdAddChar (w * 2 ^ t)) (2 * 3 ^ k)
    (powers_stdAddChar_periodic k w) (sum_powers_stdAddChar_three_pow_eq_zero k w hw) L
  rw [hreduce]
  have hmod : L % (2 * 3 ^ k) ≤ 2 * 3 ^ k := Nat.le_of_lt (Nat.mod_lt _ (by positivity))
  calc
    _ ≤ Real.sqrt ((L % (2 * 3 ^ k) : ℕ) * ((H : ℝ) * (2 * 3 ^ k))) +
        2 * (H : ℝ) ^ 2 :=
      powers_stdAddChar_sliding_bound k w _ H hmod hsep
    _ ≤ _ := by
      gcongr
      exact_mod_cast hmod

/-- A convenient uniform estimate using integer powers only.  If the modulus is
at most `16 ^ B`, the incomplete sum is at most `3 * 8 ^ B`. -/
theorem powers_stdAddChar_bound_by_integer_power (k B L : ℕ)
    (w : ZMod (3 ^ (k + 2))) (hw : IsUnit w) (hq : 3 ^ (k + 2) ≤ 16 ^ B) :
    ‖∑ t ∈ Finset.range L, ZMod.stdAddChar (w * 2 ^ t)‖ ≤ 3 * (8 : ℝ) ^ B := by
  have hmean : w * 3 ≠ 0 := by
    have h1 : 1 < 2 * 3 ^ k := by
      have hp : 0 < 3 ^ k := by positivity
      omega
    simpa only [pow_one, pow_zero, show (2 : ZMod (3 ^ (k + 2))) - 1 = 1 by ring,
      mul_one] using unit_mul_two_pow_sub_mul_three_ne_zero k w hw h1 (by positivity)
      (by decide : (1 : ℕ) ≠ 0)
  have h48 : (4 : ℝ) ^ B ≤ 8 ^ B := by gcongr <;> norm_num
  by_cases hcut : 4 ^ B ≤ 2 * 3 ^ k
  · have hsep : ∀ a ∈ Finset.range (4 ^ B), ∀ b ∈ Finset.range (4 ^ B), a ≠ b →
        (w * (2 ^ a - 2 ^ b)) * 3 ≠ 0 := by
      intro a ha b hb hab
      exact unit_mul_two_pow_sub_mul_three_ne_zero k w hw
        ((Finset.mem_range.mp ha).trans_le hcut)
        ((Finset.mem_range.mp hb).trans_le hcut) hab
    have hscaled := powers_stdAddChar_arbitrary_length_bound (k + 1) w hmean L (4 ^ B) hsep
    simp only [Nat.cast_pow, Nat.cast_ofNat] at hscaled
    have hT : 2 * (3 : ℝ) ^ (k + 1) ≤ 16 ^ B := by
      have htNat : 2 * 3 ^ (k + 1) ≤ 3 ^ (k + 2) := by
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
        omega
      exact_mod_cast htNat.trans hq
    have hrad :
        (2 * (3 : ℝ) ^ (k + 1)) * (4 ^ B * (2 * 3 ^ (k + 1))) ≤ (32 ^ B) ^ 2 := by
      calc
        _ ≤ (16 : ℝ) ^ B * (4 ^ B * 16 ^ B) := by gcongr
        _ = (32 ^ B) ^ 2 := by
          rw [← mul_pow, ← mul_pow, pow_right_comm (32 : ℝ) B 2]
          norm_num
    have hsqrt :
        Real.sqrt ((2 * (3 : ℝ) ^ (k + 1)) * (4 ^ B * (2 * 3 ^ (k + 1)))) ≤
          32 ^ B := Real.sqrt_le_iff.mpr ⟨by positivity, hrad⟩
    have hpowers : (4 : ℝ) ^ B * 8 ^ B = 32 ^ B := by rw [← mul_pow]; norm_num
    apply (mul_le_mul_iff_right₀ (show 0 < (4 : ℝ) ^ B by positivity)).mp
    calc
      _ ≤ (32 : ℝ) ^ B + 2 * (4 ^ B) ^ 2 :=
        hscaled.trans (add_le_add hsqrt le_rfl)
      _ = (4 : ℝ) ^ B * (8 ^ B + 2 * 4 ^ B) := by rw [← hpowers]; ring
      _ ≤ (4 : ℝ) ^ B * (3 * 8 ^ B) := by gcongr; linarith
  · have hreduce := sum_range_eq_mod_of_periodic_zero
      (fun t => ZMod.stdAddChar (w * 2 ^ t)) (2 * 3 ^ (k + 1))
      (powers_stdAddChar_periodic (k + 1) w)
      (sum_powers_stdAddChar_three_pow_eq_zero (k + 1) w hmean) L
    rw [hreduce]
    have hshort : 2 * 3 ^ (k + 1) ≤ 3 * 4 ^ B := by
      have hh : 2 * 3 ^ k ≤ 4 ^ B := Nat.le_of_lt (Nat.lt_of_not_ge hcut)
      rw [pow_succ]
      nlinarith
    calc
      _ ≤ ((L % (2 * 3 ^ (k + 1)) : ℕ) : ℝ) :=
        norm_sum_range_le_length _ _ (fun t => (norm_stdAddChar _).le)
      _ ≤ ((2 * 3 ^ (k + 1) : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_of_lt (Nat.mod_lt L (by positivity : 0 < 2 * 3 ^ (k + 1)))
      _ ≤ 3 * (4 : ℝ) ^ B := by exact_mod_cast hshort
      _ ≤ 3 * (8 : ℝ) ^ B := by gcongr

end XiNormality
