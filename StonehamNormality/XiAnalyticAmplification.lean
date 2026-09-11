import StonehamNormality.GeneralModulusScale
import StonehamNormality.GeneralSupportConstants

/-!
# All-length amplification for rational orbits

The previously verified Stoneham estimate uses one outer differencing step.
The Xi arithmetic theorem needs iterated differencing, since its denominator
may have any fixed polynomial size. These finite inequalities are the analytic
amplification step needed for that iteration. They apply also to short residual
correlation intervals: the common containing length, rather than each residual
length, controls the error.

This module does not assert the final arbitrary-polynomial orbit theorem.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace StonehamNormality

/-- An all-length version of the finite differencing inequality. -/
theorem xi_interval_differencing_all_lengths
    (f : ℕ → ℂ) (L H step N : ℕ) (C : ℝ)
    (hH : 0 < H) (hC : 0 ≤ C) (hL : L ≤ N) (hstep : H * step ≤ N)
    (hf : ∀ t < L, ‖f t‖ = 1)
    (hcorr : ∀ j : ℕ, 0 < j → j < H →
      ‖∑ t ∈ Finset.range (L - j * step),
        f (t + j * step) * conj (f t)‖ ≤ C) :
    (H : ℝ) * ‖∑ t ∈ Finset.range L, f t‖ ^ 2 ≤
      2 * (N : ℝ) ^ 2 + 2 * H * N * C := by
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  have hLr : (L : ℝ) ≤ N := by exact_mod_cast hL
  have hsr : (H : ℝ) * step ≤ N := by exact_mod_cast hstep
  have hwindow : (L : ℝ) + H * step ≤ 2 * N := by linarith
  have henergy : (H : ℝ) * L + H * (H - 1) * C ≤
      H * N + (H : ℝ) ^ 2 * C := by
    have hmul := mul_le_mul_of_nonneg_left hLr hHr.le
    have hpos : 0 ≤ (H : ℝ) * C := mul_nonneg hHr.le hC
    nlinarith
  have hbound := interval_differencing f L H step C hf hcorr
  have hfinal : (H : ℝ) ^ 2 * ‖∑ t ∈ Finset.range L, f t‖ ^ 2 ≤
      2 * N * ((H : ℝ) * N + H ^ 2 * C) := by
    apply hbound.trans
    exact (mul_le_mul_of_nonneg_left henergy (by positivity)).trans
      (mul_le_mul_of_nonneg_right hwindow (by positivity))
  apply (mul_le_mul_iff_right₀ hHr).mp
  nlinarith [hfinal]

/-- A gain for every length up to `N`, assuming a stronger gain for all reduced
correlations. Each iteration takes a square root of the previous gain. -/
theorem xi_interval_amplification
    (f : ℕ → ℂ) (L H step N : ℕ) (C G K : ℝ)
    (hH : 0 < H) (hC : 0 ≤ C) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hL : L ≤ N) (hstep : H * step ≤ N)
    (hHG : G ^ 2 ≤ H) (hCG : G ^ 2 * C ≤ K * N)
    (hf : ∀ t < L, ‖f t‖ = 1)
    (hcorr : ∀ j : ℕ, 0 < j → j < H →
      ‖∑ t ∈ Finset.range (L - j * step),
        f (t + j * step) * conj (f t)‖ ≤ C) :
    G * ‖∑ t ∈ Finset.range L, f t‖ ≤
      Real.sqrt (2 * (1 + K)) * N := by
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  have hbound := xi_interval_differencing_all_lengths f L H step N C
    hH hC hL hstep hf hcorr
  have hfirst : G ^ 2 * (2 * (N : ℝ) ^ 2) ≤
      (H : ℝ) * (2 * N ^ 2) :=
    mul_le_mul_of_nonneg_right hHG (by positivity)
  have hsecond : (2 * (H : ℝ) * N) * (G ^ 2 * C) ≤
      (2 * H * N) * (K * N) :=
    mul_le_mul_of_nonneg_left hCG (by positivity)
  have hsquare : G ^ 2 * ‖∑ t ∈ Finset.range L, f t‖ ^ 2 ≤
      2 * (1 + K) * (N : ℝ) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hHr).mp
    have h := mul_le_mul_of_nonneg_left hbound (sq_nonneg G)
    nlinarith [hfirst, hsecond]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  exact hsquare

/-- The amplification step with correlation phases reduced to their actual
denominators. All hypotheses refer to finite sums; no asymptotic estimate or
normality assumption is hidden in the conclusion. -/
theorem xi_rational_orbit_amplification
    (b q L H step N : ℕ) [NeZero q] (A : ℤ) (C G K : ℝ)
    (hb : 1 ≤ b) (hA : IsUnit (A : ZMod q))
    (hH : 0 < H) (hC : 0 ≤ C) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hL : L ≤ N) (hstep : H * step ≤ N)
    (hHG : G ^ 2 ≤ H) (hCG : G ^ 2 * C ≤ K * N)
    (hreduced : ∀ j : ℕ, 0 < j → j < H →
      ∀ (Q : ℕ) [NeZero Q],
        Q = q / Nat.gcd q (b ^ (j * step) - 1) →
        ∀ (E : ℤ), IsUnit (E : ZMod Q) → ∀ t ≤ N,
          ‖∑ i ∈ Finset.range t,
            ZMod.stdAddChar ((E : ZMod Q) * (b : ZMod Q) ^ i)‖ ≤ C) :
    G * ‖∑ t ∈ Finset.range L,
      ZMod.stdAddChar ((A : ZMod q) * (b : ZMod q) ^ t)‖ ≤
        Real.sqrt (2 * (1 + K)) * N := by
  apply xi_interval_amplification _ L H step N C G K
    hH hC hG hK hL hstep hHG hCG
  · intro t ht
    exact XiNormality.norm_stdAddChar _
  · intro j hj hjH
    let Q := q / Nat.gcd q (b ^ (j * step) - 1)
    have hQ : 0 < Q := Nat.div_gcd_pos_of_pos_left _ (NeZero.pos q)
    letI : NeZero Q := ⟨hQ.ne'⟩
    obtain ⟨E, hE, hphase⟩ :=
      radix_reduced_stride_correlation b step j Q hb rfl A hA
    simpa only [hphase] using hreduced j hj hjH Q rfl E hE
      (L - j * step) ((Nat.sub_le _ _).trans hL)

/-- An interval of supported moduli maps into a smaller interval after a
smooth stride. The lower bound retains denominator escape during iteration. -/
theorem xi_reduced_modulus_window
    (b C q m j T H R U : ℕ)
    (hb : 1 < b) (hC : C ≠ 0) (hq : 0 < q)
    (hT : 0 < T) (hH : 0 < H) (hj : 0 < j) (hjH : j ≤ H)
    (hmq : m ∣ q) (hml : T ≤ m) (hmu : m ≤ (b ^ C - 1) * T)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ b ^ C - 1)
    (hfour : 2 ∣ q → 4 ∣ b ^ C - 1)
    (hql : ((b ^ C - 1) ^ 2 * T * H) * R ≤ q)
    (hqu : q ≤ T * U) :
    let Q := q / Nat.gcd q (b ^ (j * (C * m)) - 1)
    R ≤ Q ∧ Q ≤ U := by
  let D := b ^ C - 1
  have hD : 0 < D := by
    have h := one_lt_pow₀ hb hC
    dsimp [D]
    omega
  let Q := q / Nat.gcd q (b ^ (j * (C * m)) - 1)
  have hred := stride_reduced_modulus_bounds b C q m j hb hC hq
    (hT.trans_le hml) hj hmq hsupport hfour
  change m * Q ≤ q ∧ q ≤ (D * m * j) * Q at hred
  constructor
  · have hfactor : D * m * j ≤ D ^ 2 * T * H := by
      calc
        _ ≤ D * (D * T) * H :=
          Nat.mul_le_mul (Nat.mul_le_mul_left D hmu) hjH
        _ = _ := by ring
    have hle : (D ^ 2 * T * H) * R ≤ (D ^ 2 * T * H) * Q :=
      hql.trans (hred.2.trans (Nat.mul_le_mul_right Q hfactor))
    exact Nat.le_of_mul_le_mul_left hle (by positivity)
  · have hle : T * Q ≤ T * U :=
      (Nat.mul_le_mul_right Q hml).trans (hred.1.trans hqu)
    exact Nat.le_of_mul_le_mul_left hle hT

/-- A complete fixed-support amplification stage. Its only orbit input is the
bound on a smaller explicit denominator window. Repeated applications therefore
reduce larger polynomial ranges to the existing verified one-stage estimate. -/
theorem xi_fixed_support_amplification
    (b S q L H T N R U : ℕ) [NeZero q] (A : ℤ) (Cbound G K : ℝ)
    (hb : 1 < b) (hS : 0 < S) (hcop : b.Coprime S)
    (hA : IsUnit (A : ZMod q))
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ S)
    (hH : 0 < H) (hT : 0 < T) (hTq : T ≤ q)
    (hCb : 0 ≤ Cbound) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hL : L ≤ N)
    (hstep : H * (supportStrideExponent S *
      ((b ^ supportStrideExponent S - 1) * T)) ≤ N)
    (hHG : G ^ 2 ≤ H) (hCG : G ^ 2 * Cbound ≤ K * N)
    (hql : ((b ^ supportStrideExponent S - 1) ^ 2 * T * H) * R ≤ q)
    (hqu : q ≤ T * U)
    (hinner : ∀ (Q : ℕ) [NeZero Q], R ≤ Q → Q ≤ U →
      (∀ p : ℕ, p.Prime → p ∣ Q → p ∣ S) →
      ∀ (E : ℤ), IsUnit (E : ZMod Q) → ∀ t ≤ N,
        ‖∑ i ∈ Finset.range t,
          ZMod.stdAddChar ((E : ZMod Q) * (b : ZMod Q) ^ i)‖ ≤ Cbound) :
    G * ‖∑ t ∈ Finset.range L,
      ZMod.stdAddChar ((A : ZMod q) * (b : ZMod q) ^ t)‖ ≤
        Real.sqrt (2 * (1 + K)) * N := by
  let C := supportStrideExponent S
  let D := b ^ C - 1
  have hC : C ≠ 0 := (supportStrideExponent_pos hS).ne'
  have hD : 0 < D := by
    have h := one_lt_pow₀ hb hC
    dsimp [D]
    omega
  have hsup : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ D :=
    support_primes_dvd_base_pow_sub_one b S q hcop hsupport
  have hfour : 2 ∣ q → 4 ∣ D :=
    support_four_dvd_base_pow_sub_one b S q hcop hsupport
  obtain ⟨m, hmq, hml, hmu⟩ := exists_divisor_between q D T
    (by omega) (by omega) hTq
    (fun p hp hpq => Nat.le_of_dvd hD (hsup p hp hpq))
  apply xi_rational_orbit_amplification b q L H (C * m) N A Cbound G K
    hb.le hA hH hCb hG hK hL
    ((Nat.mul_le_mul_left H (Nat.mul_le_mul_left C hmu)).trans hstep)
    hHG hCG
  intro j hj hjH Q _ hQ E hE t ht
  have hwindow := xi_reduced_modulus_window b C q m j T H R U
    hb hC (NeZero.pos q) hT hH hj hjH.le hmq hml hmu hsup hfour hql hqu
  rw [← hQ] at hwindow
  have hQdvd : Q ∣ q := hQ ▸ Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  exact hinner Q hwindow.1 hwindow.2
    (fun p hp hpQ => hsupport p hp (hpQ.trans hQdvd)) E hE t ht

end StonehamNormality
