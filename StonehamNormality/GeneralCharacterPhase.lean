import StonehamNormality.CharacterPhase

/-! Rational circle characters in an arbitrary integer radix. -/

noncomputable section
namespace StonehamNormality

theorem fourier_rational_radix_eq_stdAddChar
    (b : ℕ) {q : ℕ} [NeZero q] (h A : ℤ) (r : ℚ)
    (hr : (h : ℚ) * r = (A : ℚ) / q) (t : ℕ) :
    fourier (T := 1) h ((((b : ℚ) ^ t * r : ℚ) : ℝ) : UnitAddCircle) =
      ZMod.stdAddChar ((A : ZMod q) * (b : ZMod q) ^ t) := by
  have hc : (h : ℂ) * (r : ℂ) = (A : ℂ) / q := by exact_mod_cast hr
  have hcast : (A : ZMod q) * (b : ZMod q) ^ t =
      ((A * (b : ℤ) ^ t : ℤ) : ZMod q) := by
    push_cast
    rfl
  rw [hcast, ZMod.stdAddChar_coe, fourier_coe_apply]
  congr 1
  push_cast
  calc
    2 * Real.pi * Complex.I * h * ((b : ℂ) ^ t * r) / 1 =
        (2 * Real.pi * Complex.I * (b : ℂ) ^ t) * ((h : ℂ) * r) := by ring
    _ = _ := by rw [hc]; ring

end StonehamNormality
