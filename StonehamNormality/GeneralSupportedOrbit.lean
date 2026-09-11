import StonehamNormality.GeneralOrder
import StonehamNormality.GeneralOrbit

noncomputable section

open scoped BigOperators

namespace StonehamNormality

/-- The arbitrary-length inner character bound with all kernel and separation
hypotheses discharged by concrete fixed prime-support arithmetic. -/
theorem supported_power_character_arbitrary_length_bound (b C q L H : ℕ) [NeZero q]
    (hb : 1 < b) (hC : C ≠ 0) (hq : 0 < q) (hcop : b.Coprime q)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ b ^ C - 1)
    (hfour : 2 ∣ q → 4 ∣ b ^ C - 1)
    (hlarge : b ^ C - 1 < q) (hH : H * (b ^ C - 1) ^ 2 ≤ q)
    (w : ZMod q) (hw : IsUnit w) :
    (H : ℝ) * ‖∑ t ∈ Finset.range L, ZMod.stdAddChar (w * (b : ZMod q) ^ t)‖ ≤
      Real.sqrt ((q : ℝ) * ((H : ℝ) * q)) + 2 * (H : ℝ) ^ 2 := by
  have hDpos : 0 < b ^ C - 1 := by
    have := one_lt_pow₀ hb hC
    omega
  have hdpos : 0 < Nat.gcd q (b ^ C - 1) := Nat.gcd_pos_of_pos_left _ hq
  have hdne : (Nat.gcd q (b ^ C - 1) : ZMod q) ≠ 0 := by
    intro h
    have hdiv := (ZMod.natCast_eq_zero_iff _ _).1 h
    have hle := Nat.le_of_dvd hdpos hdiv
    have hsmall := Nat.gcd_le_right q hDpos
    omega
  apply power_character_arbitrary_length_bound (b : ZMod q)
    (Nat.gcd q (b ^ C - 1) : ZMod q) w
    (ZMod.unitOfCoprime b hcop).isUnit hw hdne
    (fun z => base_principal_kernel_mem_powers b C q hb hC hq hsupport hfour z) L H
  intro i hi j hj hij
  exact base_principal_kernel_shift_separation b C q H hb hC hq hcop
    hsupport hfour hH i j hi hj hij

end StonehamNormality
