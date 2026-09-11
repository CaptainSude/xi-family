import StonehamNormality.XiAnalyticIteration

/-! Integer dyadic gains for a prescribed number of amplification stages. -/

noncomputable section
open scoped BigOperators

namespace StonehamNormality

def xiAmplificationConstant (K : ℝ) : ℕ → ℝ
  | 0 => K
  | n + 1 => max (xiAmplificationConstant K n)
      (Real.sqrt (2 * (1 + xiAmplificationConstant K n)))

theorem xiAmplificationConstant_nonneg (K : ℝ) (hK : 0 ≤ K) (n : ℕ) :
    0 ≤ xiAmplificationConstant K n := by
  induction n with
  | zero => exact hK
  | succ n ih => exact ih.trans (le_max_left _ _)

theorem xiAmplificationConstant_step (K : ℝ) (n : ℕ) :
    xiAmplificationConstant K n ≤ xiAmplificationConstant K (n + 1) :=
  le_max_left _ _

theorem xiAmplificationConstant_sqrt (K : ℝ) (n : ℕ) :
    Real.sqrt (2 * (1 + xiAmplificationConstant K n)) ≤
      xiAmplificationConstant K (n + 1) := le_max_right _ _

theorem xi_gain_halves (d n : ℕ) (hn : n < d) :
    2 * 2 ^ (d - (n + 1)) = (2 : ℕ) ^ (d - n) := by
  rw [show d - n = (d - (n + 1)) + 1 by omega, pow_succ]
  omega

/-- Once the common stride fits, `d` iterations enlarge the modulus window
by `V^d`. Starting with gain `2^(2^d B)` leaves gain `2^B` at the end. -/
theorem xi_fixed_support_dyadic_iteration
    (b S R U V H B t d : ℕ) (K₀ : ℝ)
    (hb : 1 < b) (hS : 0 < S) (hcop : b.Coprime S)
    (hH : 0 < H) (hV : 0 < V) (hVU : V ≤ U) (hK₀ : 0 ≤ K₀)
    (ht : 2 ^ d ≤ t)
    (hstep : H * (supportStrideExponent S *
      ((b ^ supportStrideExponent S - 1) * V)) ≤ 2 ^ (t * B))
    (hgap : ((b ^ supportStrideExponent S - 1) ^ 2 * V * H) * R ≤ U)
    (hHG : 2 ^ ((2 * 2 ^ d) * B) ≤ H)
    (hinner : XiUniformOrbitBound b S R U (2 ^ (t * B))
      (K₀ * (2 : ℝ) ^ ((t - 2 ^ d) * B))) :
    XiUniformOrbitBound b S R (V ^ d * U) (2 ^ (t * B))
      (xiAmplificationConstant K₀ d * (2 : ℝ) ^ ((t - 1) * B)) := by
  let C : ℕ → ℝ := fun n => xiAmplificationConstant K₀ n *
    (2 : ℝ) ^ ((t - 2 ^ (d - n)) * B)
  let G : ℕ → ℝ := fun n => (2 : ℝ) ^ (2 ^ (d - (n + 1)) * B)
  let K : ℕ → ℝ := xiAmplificationConstant K₀
  have hK (n : ℕ) : 0 ≤ K n := xiAmplificationConstant_nonneg K₀ hK₀ n
  have hgain_le (n : ℕ) : (2 : ℕ) ^ (d - n) ≤ t :=
    (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)).trans ht
  have hgain_step (n : ℕ) : (2 : ℕ) ^ (d - (n + 1)) ≤ 2 ^ (d - n) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hbound := xi_fixed_support_iterate_windows_finite
    b S R U V H (2 ^ (t * B)) d C G K hb hS hcop hH hV hVU
    (fun n hn => mul_nonneg (hK n) (by positivity))
    (fun n hn => by dsimp [G]; positivity)
    (fun n hn => hK n) hstep hgap ?_ ?_ ?_ ?_ ?_
  · simpa [C] using hbound
  · intro n hn
    dsimp [G]
    rw [← pow_mul]
    have he : (2 ^ (d - (n + 1)) * B) * 2 ≤ (2 * 2 ^ d) * B := by
      have hp : (2 : ℕ) ^ (d - (n + 1)) ≤ 2 ^ d :=
        pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      nlinarith
    exact (pow_le_pow_right₀ (by norm_num) he).trans (by exact_mod_cast hHG)
  · intro n hn
    have hexp : (2 ^ (d - (n + 1)) * B) * 2 +
        (t - 2 ^ (d - n)) * B = t * B := by
      rw [Nat.mul_assoc, Nat.mul_comm B 2, ← Nat.mul_assoc,
        Nat.mul_comm (2 ^ (d - (n + 1))) 2, xi_gain_halves d n hn,
        ← Nat.add_mul, Nat.add_sub_of_le (hgain_le n)]
    change ((2 : ℝ) ^ (2 ^ (d - (n + 1)) * B)) ^ 2 *
      (K n * (2 : ℝ) ^ ((t - 2 ^ (d - n)) * B)) ≤
        K n * ((2 ^ (t * B) : ℕ) : ℝ)
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_mul, mul_left_comm, ← pow_add, hexp]
  · intro n hn
    have hexp : 2 ^ (d - (n + 1)) * B +
        (t - 2 ^ (d - (n + 1))) * B = t * B := by
      rw [← Nat.add_mul, Nat.add_sub_of_le (hgain_le (n + 1))]
    have hcoeff := xiAmplificationConstant_sqrt K₀ n
    change Real.sqrt (2 * (1 + K n)) * ((2 ^ (t * B) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (2 ^ (d - (n + 1)) * B) *
        (K (n + 1) * (2 : ℝ) ^ ((t - 2 ^ (d - (n + 1))) * B))
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [mul_left_comm, ← pow_add, hexp]
    exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
  · intro n hn
    change K n * (2 : ℝ) ^ ((t - 2 ^ (d - n)) * B) ≤
      K (n + 1) * (2 : ℝ) ^ ((t - 2 ^ (d - (n + 1))) * B)
    apply mul_le_mul (xiAmplificationConstant_step K₀ n)
      (pow_le_pow_right₀ (by norm_num) _) (by positivity) (hK (n + 1))
    exact Nat.mul_le_mul_right B (Nat.sub_le_sub_left (hgain_step n) t)
  · simpa [C, xiAmplificationConstant] using hinner

end StonehamNormality
