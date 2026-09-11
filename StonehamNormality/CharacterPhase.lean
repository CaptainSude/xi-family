import StonehamNormality.PrimeFive

/-! The rational-character identity from the published Xi development,
restated independently of its specialized truncation arithmetic. -/

noncomputable section
namespace StonehamNormality

theorem fourier_rational_doubling_eq_stdAddChar
    {q : ℕ} [NeZero q] (h A : ℤ) (r : ℚ)
    (hr : (h : ℚ) * r = (A : ℚ) / q) (t : ℕ) :
    fourier (T := 1) h ((((2 : ℚ) ^ t * r : ℚ) : ℝ) : UnitAddCircle) =
      ZMod.stdAddChar ((A : ZMod q) * 2 ^ t) := by
  have hc : (h : ℂ) * (r : ℂ) = (A : ℂ) / q := by exact_mod_cast hr
  have hcast : (A : ZMod q) * 2 ^ t = ((A * 2 ^ t : ℤ) : ZMod q) := by
    push_cast
    rfl
  rw [hcast, ZMod.stdAddChar_coe, fourier_coe_apply]
  congr 1
  push_cast
  calc
    2 * Real.pi * Complex.I * h * ((2 : ℂ) ^ t * r) / 1 =
        (2 * Real.pi * Complex.I * (2 : ℂ) ^ t) * ((h : ℂ) * r) := by ring
    _ = _ := by rw [hc]; ring

end StonehamNormality
