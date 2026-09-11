import StonehamNormality.XiAnalyticAmplification

/-!
# Iterating fixed-support rational-orbit estimates

The base input is a uniform finite character estimate on one denominator
window. The proved iteration enlarges its upper endpoint by an arbitrary
integer power. All remaining numerical hypotheses are explicit inequalities.
-/

noncomputable section
open scoped BigOperators

namespace StonehamNormality

/-- One bound simultaneously for every supported denominator, numerator, and
initial interval in the stated ranges. -/
def XiUniformOrbitBound (b S R U N : ℕ) (C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q], R ≤ q → q ≤ U →
    (∀ p : ℕ, p.Prime → p ∣ q → p ∣ S) →
    ∀ (A : ℤ), IsUnit (A : ZMod q) → ∀ L ≤ N,
      ‖∑ t ∈ Finset.range L,
        ZMod.stdAddChar ((A : ZMod q) * (b : ZMod q) ^ t)‖ ≤ C

/-- Enlarge an existing denominator window by one smooth-divisor factor. -/
theorem xi_fixed_support_extend_window
    (b S R U T H N : ℕ) (Cbound Cnext G K : ℝ)
    (hb : 1 < b) (hS : 0 < S) (hcop : b.Coprime S)
    (hH : 0 < H) (hT : 0 < T) (hTU : T ≤ U)
    (hC : 0 ≤ Cbound) (hG : 0 < G) (hK : 0 ≤ K)
    (hstep : H * (supportStrideExponent S *
      ((b ^ supportStrideExponent S - 1) * T)) ≤ N)
    (hgap : ((b ^ supportStrideExponent S - 1) ^ 2 * T * H) * R ≤ U)
    (hHG : G ^ 2 ≤ H) (hCG : G ^ 2 * Cbound ≤ K * N)
    (hgain : Real.sqrt (2 * (1 + K)) * N ≤ G * Cnext)
    (hmono : Cbound ≤ Cnext)
    (hinner : XiUniformOrbitBound b S R U N Cbound) :
    XiUniformOrbitBound b S R (T * U) N Cnext := by
  intro q _ hRq hqu hsupport A hA L hL
  by_cases hsmall : q ≤ U
  · exact (hinner q hRq hsmall hsupport A hA L hL).trans hmono
  · have hUq : U ≤ q := (Nat.lt_of_not_ge hsmall).le
    have hbound := xi_fixed_support_amplification b S q L H T N R U A Cbound G K
      hb hS hcop hA hsupport hH hT (hTU.trans hUq)
      hC hG.le hK hL hstep hHG hCG (hgap.trans hUq) hqu hinner
    exact (mul_le_mul_iff_right₀ hG).mp (hbound.trans hgain)

/-- The finite iteration principle. Every additional stage multiplies the
available upper denominator by `T`; the lower denominator stays fixed. -/
theorem xi_fixed_support_iterate_windows
    (b S R U T H N : ℕ) (C G K : ℕ → ℝ)
    (hb : 1 < b) (hS : 0 < S) (hcop : b.Coprime S)
    (hH : 0 < H) (hT : 0 < T) (hTU : T ≤ U)
    (hC : ∀ n, 0 ≤ C n) (hG : ∀ n, 0 < G n) (hK : ∀ n, 0 ≤ K n)
    (hstep : H * (supportStrideExponent S *
      ((b ^ supportStrideExponent S - 1) * T)) ≤ N)
    (hgap : ((b ^ supportStrideExponent S - 1) ^ 2 * T * H) * R ≤ U)
    (hHG : ∀ n, (G n) ^ 2 ≤ H)
    (hCG : ∀ n, (G n) ^ 2 * C n ≤ K n * N)
    (hgain : ∀ n, Real.sqrt (2 * (1 + K n)) * N ≤ G n * C (n + 1))
    (hmono : ∀ n, C n ≤ C (n + 1))
    (hinner : XiUniformOrbitBound b S R U N (C 0)) :
    ∀ n, XiUniformOrbitBound b S R (T ^ n * U) N (C n) := by
  intro n
  induction n with
  | zero => simpa using hinner
  | succ n ih =>
    have hUgrow : U ≤ T ^ n * U := by
      have hp : 1 ≤ T ^ n := one_le_pow₀ (by omega)
      simpa only [one_mul] using Nat.mul_le_mul_right U hp
    have hbound := xi_fixed_support_extend_window b S R (T ^ n * U) T H N
      (C n) (C (n + 1)) (G n) (K n) hb hS hcop hH hT (hTU.trans hUgrow)
      (hC n) (hG n) (hK n) hstep (hgap.trans hUgrow)
      (hHG n) (hCG n) (hgain n) (hmono n) ih
    convert hbound using 1 <;> simp [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- A bounded iteration, convenient when the successive gains are integer
powers whose exponents halve a prescribed number of times. -/
theorem xi_fixed_support_iterate_windows_finite
    (b S R U T H N d : ℕ) (C G K : ℕ → ℝ)
    (hb : 1 < b) (hS : 0 < S) (hcop : b.Coprime S)
    (hH : 0 < H) (hT : 0 < T) (hTU : T ≤ U)
    (hC : ∀ n < d, 0 ≤ C n) (hG : ∀ n < d, 0 < G n)
    (hK : ∀ n < d, 0 ≤ K n)
    (hstep : H * (supportStrideExponent S *
      ((b ^ supportStrideExponent S - 1) * T)) ≤ N)
    (hgap : ((b ^ supportStrideExponent S - 1) ^ 2 * T * H) * R ≤ U)
    (hHG : ∀ n < d, (G n) ^ 2 ≤ H)
    (hCG : ∀ n < d, (G n) ^ 2 * C n ≤ K n * N)
    (hgain : ∀ n < d, Real.sqrt (2 * (1 + K n)) * N ≤ G n * C (n + 1))
    (hmono : ∀ n < d, C n ≤ C (n + 1))
    (hinner : XiUniformOrbitBound b S R U N (C 0)) :
    XiUniformOrbitBound b S R (T ^ d * U) N (C d) := by
  have h : ∀ n, n ≤ d → XiUniformOrbitBound b S R (T ^ n * U) N (C n) := by
    intro n
    induction n with
    | zero => intro hn; simpa using hinner
    | succ n ih =>
      intro hn
      have hnd : n < d := by omega
      have hUgrow : U ≤ T ^ n * U := by
        have hp : 1 ≤ T ^ n := one_le_pow₀ (by omega)
        simpa only [one_mul] using Nat.mul_le_mul_right U hp
      have hbound := xi_fixed_support_extend_window b S R (T ^ n * U) T H N
        (C n) (C (n + 1)) (G n) (K n) hb hS hcop hH hT (hTU.trans hUgrow)
        (hC n hnd) (hG n hnd) (hK n hnd) hstep (hgap.trans hUgrow)
        (hHG n hnd) (hCG n hnd) (hgain n hnd) (hmono n hnd) (ih (by omega))
      convert hbound using 1 <;>
        simp [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact h d le_rfl

end StonehamNormality
