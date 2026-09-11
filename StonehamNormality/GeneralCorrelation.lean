import StonehamNormality.CorrelationArithmetic

/-! Exact correlation reduction for an arbitrary integer radix. -/

noncomputable section
open scoped ComplexConjugate
namespace StonehamNormality

theorem reduce_stdAddChar_radix {q : ℕ} [NeZero q] (b c Q : ℕ) [NeZero Q]
    (hQ : Q = q / Nat.gcd q c) (A : ℤ) (hA : IsUnit (A : ZMod q)) :
    ∃ D : ℤ, IsUnit (D : ZMod Q) ∧ ∀ t : ℕ,
      ZMod.stdAddChar ((A : ZMod q) * (c : ZMod q) * (b : ZMod q) ^ t) =
        ZMod.stdAddChar ((D : ZMod Q) * (b : ZMod Q) ^ t) := by
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
    have h := stdAddChar_intCast_eq_of_cross_mul (q := q) (Q := Q)
      (A * (c : ℤ) * (b : ℤ) ^ t) ((A * (c / Nat.gcd q c : ℕ)) * (b : ℤ) ^ t) (by
        calc
          _ = A * (b : ℤ) ^ t * ((c : ℤ) * Q) := by ring
          _ = _ := by rw [hcross]; ring)
    simpa only [Int.cast_mul, Int.cast_natCast, Int.cast_pow] using h

theorem radix_reduced_stride_correlation {q : ℕ} [NeZero q]
    (b step j Q : ℕ) [NeZero Q] (hb : 1 ≤ b)
    (hQ : Q = q / Nat.gcd q (b ^ (j * step) - 1))
    (A : ℤ) (hA : IsUnit (A : ZMod q)) :
    ∃ D : ℤ, IsUnit (D : ZMod Q) ∧ ∀ t : ℕ,
      ZMod.stdAddChar ((A : ZMod q) * (b : ZMod q) ^ (t + j * step)) *
        conj (ZMod.stdAddChar ((A : ZMod q) * (b : ZMod q) ^ t)) =
      ZMod.stdAddChar ((D : ZMod Q) * (b : ZMod Q) ^ t) := by
  obtain ⟨D, hD, hphase⟩ := reduce_stdAddChar_radix b (b ^ (j * step) - 1) Q hQ A hA
  refine ⟨D, hD, ?_⟩
  intro t
  rw [XiNormality.conj_stdAddChar, ← AddChar.map_add_eq_mul, ← hphase t]
  congr 1
  rw [Nat.cast_sub (one_le_pow₀ hb)]
  push_cast
  rw [pow_add]
  ring

end StonehamNormality
