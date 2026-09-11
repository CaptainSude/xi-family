import StonehamNormality.GeneralOrbit
import StonehamNormality.Differencing

/-!
# Integer scales for the general character estimate

An inner averaging length `2^(16B)` gives a correlation bound of that size.
Outer averaging with `2^(3B)` shifts then gives a relative squared bound,
expressed without division or real powers.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace StonehamNormality

/-- The elementary all-length inner bound at the chosen integer scales. -/
theorem power_character_integer_scale_bound {q : ℕ} [NeZero q]
    (b D w : ZMod q) (hb : IsUnit b) (hw : IsUnit w) (hD : D ≠ 0)
    (hkernel : ∀ z : ZMod q, ∃ d : ℕ, b ^ d = 1 + D * z)
    (B L : ℕ) (K : ℝ) (_hK : 0 ≤ K)
    (hq : (q : ℝ) ≤ K * (2 : ℝ) ^ (24 * B))
    (hsep : ∀ i < 2 ^ (16 * B), ∀ j < 2 ^ (16 * B), i ≠ j →
      (b ^ i - b ^ j) * D ≠ 0) :
    ‖∑ t ∈ Finset.range L, ZMod.stdAddChar (w * b ^ t)‖ ≤
      (K + 2) * (2 : ℝ) ^ (16 * B) := by
  have h := power_character_arbitrary_length_bound b D w hb hw hD hkernel
    L (2 ^ (16 * B)) hsep
  simp only [Nat.cast_pow, Nat.cast_ofNat] at h
  have hroot : Real.sqrt ((q : ℝ) * ((2 : ℝ) ^ (16 * B) * q)) =
      (q : ℝ) * (2 : ℝ) ^ (8 * B) := by
    have heq : (q : ℝ) * ((2 : ℝ) ^ (16 * B) * q) =
        ((q : ℝ) * (2 : ℝ) ^ (8 * B)) ^ 2 := by
      rw [mul_pow, ← pow_mul, show 8 * B * 2 = 16 * B by omega]
      ring
    rw [heq, Real.sqrt_sq (by positivity)]
  rw [hroot] at h
  have hqmul := mul_le_mul_of_nonneg_right hq (by positivity : 0 ≤ (2 : ℝ) ^ (8 * B))
  have heq : K * (2 : ℝ) ^ (24 * B) * (2 : ℝ) ^ (8 * B) +
      2 * ((2 : ℝ) ^ (16 * B)) ^ 2 =
        (2 : ℝ) ^ (16 * B) * ((K + 2) * (2 : ℝ) ^ (16 * B)) := by
    rw [mul_assoc K, ← pow_add, show 24 * B + 8 * B = 16 * B + 16 * B by omega,
      pow_add]
    ring
  apply le_of_mul_le_mul_left (a := (2 : ℝ) ^ (16 * B)) _ (by positivity)
  apply h.trans
  rw [← heq]
  linarith

/-- The stride fits into a long interval once its fixed factor is absorbed by
the gap between exponents fifteen and seventeen. -/
theorem outer_integer_scale_stride_le (B C step L : ℕ)
    (hstep : step ≤ C * 2 ^ (12 * B + 12))
    (hC : C * 2 ^ 12 ≤ 2 ^ (2 * B)) (hL : 2 ^ (17 * B) ≤ L) :
    2 ^ (3 * B) * step ≤ L := by
  calc
    _ ≤ 2 ^ (3 * B) * (C * 2 ^ (12 * B + 12)) := Nat.mul_le_mul_left _ hstep
    _ = (C * 2 ^ 12) * 2 ^ (15 * B) := by
      rw [pow_add, show 15 * B = 3 * B + 12 * B by omega, pow_add]
      ring
    _ ≤ 2 ^ (2 * B) * 2 ^ (15 * B) := Nat.mul_le_mul_right _ hC
    _ = 2 ^ (17 * B) := by rw [← pow_add]; congr 1; omega
    _ ≤ L := hL

/-- One outer differencing step, with a division-free relative error bound. -/
theorem interval_differencing_integer_scale (f : ℕ → ℂ) (B L step : ℕ) (K : ℝ)
    (hK : 0 ≤ K) (hL : 2 ^ (17 * B) ≤ L)
    (hstep : 2 ^ (3 * B) * step ≤ L)
    (hf : ∀ t < L, ‖f t‖ = 1)
    (hcorr : ∀ j : ℕ, 0 < j → j < 2 ^ (3 * B) →
      ‖∑ t ∈ Finset.range (L - j * step),
        f (t + j * step) * conj (f t)‖ ≤ K * (2 : ℝ) ^ (16 * B)) :
    (2 : ℝ) ^ B * ‖∑ t ∈ Finset.range L, f t‖ ^ 2 ≤
      2 * (1 + K) * (L : ℝ) ^ 2 := by
  let H : ℝ := (2 : ℝ) ^ (3 * B)
  let P : ℝ := (2 : ℝ) ^ B
  let C : ℝ := K * (2 : ℝ) ^ (16 * B)
  have hHpos : 0 < H := by dsimp [H]; positivity
  have hPpos : 0 < P := by dsimp [P]; positivity
  have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
  have hLP : (2 : ℝ) ^ (17 * B) ≤ L := by exact_mod_cast hL
  have hPH : P ≤ H := by
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    omega
  have hPC : P * C ≤ K * (L : ℝ) := by
    calc
      P * C = K * (2 : ℝ) ^ (17 * B) := by
        dsimp [P, C]
        rw [mul_left_comm, ← pow_add, show B + 16 * B = 17 * B by omega]
      _ ≤ K * L := mul_le_mul_of_nonneg_left hLP hK
  have hwindow : (L : ℝ) + H * step ≤ 2 * L := by
    have hs : H * (step : ℝ) ≤ L := by
      change (2 : ℝ) ^ (3 * B) * (step : ℝ) ≤ L
      exact_mod_cast hstep
    linarith
  have henergy : H * L + H * (H - 1) * C ≤ H * L + H ^ 2 * C := by
    have := mul_nonneg hHpos.le hCnonneg
    nlinarith
  have hout := interval_differencing f L (2 ^ (3 * B)) step C hf hcorr
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hout
  change H ^ 2 * ‖∑ t ∈ Finset.range L, f t‖ ^ 2 ≤
    ((L : ℝ) + H * step) * (H * L + H * (H - 1) * C) at hout
  have hs : H ^ 2 * ‖∑ t ∈ Finset.range L, f t‖ ^ 2 ≤
      2 * L * (H * L + H ^ 2 * C) := by
    apply hout.trans
    exact (mul_le_mul_of_nonneg_left henergy (by positivity)).trans
      (mul_le_mul_of_nonneg_right hwindow (by positivity))
  apply le_of_mul_le_mul_left (a := H ^ 2) _ (by positivity)
  calc
    H ^ 2 * ((2 : ℝ) ^ B * ‖∑ t ∈ Finset.range L, f t‖ ^ 2) =
        P * (H ^ 2 * ‖∑ t ∈ Finset.range L, f t‖ ^ 2) := by dsimp [P]; ring
    _ ≤ P * (2 * L * (H * L + H ^ 2 * C)) := mul_le_mul_of_nonneg_left hs hPpos.le
    _ = (2 * (L : ℝ) ^ 2 * H) * P + (2 * H ^ 2 * L) * (P * C) := by ring
    _ ≤ (2 * (L : ℝ) ^ 2 * H) * H + (2 * H ^ 2 * L) * (K * L) :=
      add_le_add (mul_le_mul_of_nonneg_left hPH (by positivity))
        (mul_le_mul_of_nonneg_left hPC (by positivity))
    _ = H ^ 2 * (2 * (1 + K) * (L : ℝ) ^ 2) := by ring

/-- The character-specific outer estimate, before reducing the correlation
coefficients to their smaller moduli. -/
theorem power_character_outer_integer_scale {q : ℕ} [NeZero q]
    (b w : ZMod q) (B L step : ℕ) (K : ℝ)
    (hK : 0 ≤ K) (hL : 2 ^ (17 * B) ≤ L)
    (hstep : 2 ^ (3 * B) * step ≤ L)
    (hcorr : ∀ j : ℕ, 0 < j → j < 2 ^ (3 * B) →
      ‖∑ t ∈ Finset.range (L - j * step),
        ZMod.stdAddChar ((w * (b ^ (j * step) - 1)) * b ^ t)‖ ≤
          K * (2 : ℝ) ^ (16 * B)) :
    (2 : ℝ) ^ B * ‖∑ t ∈ Finset.range L, ZMod.stdAddChar (w * b ^ t)‖ ^ 2 ≤
      2 * (1 + K) * (L : ℝ) ^ 2 := by
  apply interval_differencing_integer_scale
    (fun t => ZMod.stdAddChar (w * b ^ t)) B L step K hK hL hstep
  · intro t ht
    exact XiNormality.norm_stdAddChar _
  · intro j hj hjH
    have hterm (t : ℕ) :
        ZMod.stdAddChar (w * b ^ (t + j * step)) *
          conj (ZMod.stdAddChar (w * b ^ t)) =
        ZMod.stdAddChar ((w * (b ^ (j * step) - 1)) * b ^ t) := by
      rw [XiNormality.conj_stdAddChar, ← AddChar.map_add_eq_mul]
      congr 1
      rw [pow_add]
      ring
    simpa only [hterm] using hcorr j hj hjH

/-- Extract an integer-power gain from the squared estimate, avoiding fractional
real powers. In the global assembly one can take `A = 2 * Bglobal`. -/
theorem norm_bound_of_integer_scaled_square (S : ℂ) (A B L : ℕ) (K : ℝ)
    (hK : 0 ≤ K) (hAB : 2 * A ≤ B)
    (hbound : (2 : ℝ) ^ B * ‖S‖ ^ 2 ≤ K * (L : ℝ) ^ 2) :
    (2 : ℝ) ^ A * ‖S‖ ≤ Real.sqrt K * L := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    ((2 : ℝ) ^ A * ‖S‖) ^ 2 = (2 : ℝ) ^ (2 * A) * ‖S‖ ^ 2 := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm A 2]
    _ ≤ (2 : ℝ) ^ B * ‖S‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hAB) (sq_nonneg _)
    _ ≤ K * (L : ℝ) ^ 2 := hbound
    _ = (Real.sqrt K * L) ^ 2 := by rw [mul_pow, Real.sq_sqrt hK]

end StonehamNormality
