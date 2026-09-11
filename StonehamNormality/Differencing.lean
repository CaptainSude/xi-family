import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

/-!
# Finite differencing inequalities

The outer differencing step uses translates of a zero-extended finite sequence.
The finite-family statements isolate its analytic content from the support and
modular arithmetic calculations.
-/

noncomputable section

open scoped BigOperators ComplexConjugate
open Complex

namespace StonehamNormality

/-- Finite Cauchy--Schwarz for complex sums. -/
theorem norm_sum_sq_le_card_mul_energy {ι : Type*} (T : Finset ι) (f : ι → ℂ) :
    ‖∑ t ∈ T, f t‖ ^ 2 ≤ (T.card : ℝ) * ∑ t ∈ T, ‖f t‖ ^ 2 := by
  have hnonneg : 0 ≤ ∑ t ∈ T, ‖f t‖ :=
    Finset.sum_nonneg (fun t ht => norm_nonneg (f t))
  calc
    ‖∑ t ∈ T, f t‖ ^ 2 ≤ (∑ t ∈ T, ‖f t‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hnonneg).2 (norm_sum_le T f)
    _ ≤ (T.card : ℝ) * ∑ t ∈ T, ‖f t‖ ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ))
        (fun t => ‖f t‖)

/-- The energy of a finite sum is the real part of its correlation matrix. -/
theorem finite_energy_eq_re_correlations {ι τ : Type*}
    (A : Finset ι) (T : Finset τ) (f : ι → τ → ℂ) :
    ∑ t ∈ T, ‖∑ a ∈ A, f a t‖ ^ 2 =
      (∑ a ∈ A, ∑ b ∈ A, ∑ t ∈ T, f a t * conj (f b t)).re := by
  classical
  have heq :
      ∑ t ∈ T, (∑ a ∈ A, f a t) * conj (∑ a ∈ A, f a t) =
        ∑ a ∈ A, ∑ b ∈ A, ∑ t ∈ T, f a t * conj (f b t) := by
    simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_comm]
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at heq
  have hre := congrArg Complex.re heq
  simpa only [Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re] using hre

/-- A Cauchy--Schwarz bound for a finite family, without orthogonality. -/
theorem finite_sum_sq_le_correlations {ι τ : Type*}
    (A : Finset ι) (T : Finset τ) (f : ι → τ → ℂ) :
    ‖∑ t ∈ T, ∑ a ∈ A, f a t‖ ^ 2 ≤
      (T.card : ℝ) *
        ∑ a ∈ A, ∑ b ∈ A, ‖∑ t ∈ T, f a t * conj (f b t)‖ := by
  calc
    _ ≤ (T.card : ℝ) * ∑ t ∈ T, ‖∑ a ∈ A, f a t‖ ^ 2 :=
      norm_sum_sq_le_card_mul_energy T (fun t => ∑ a ∈ A, f a t)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [finite_energy_eq_re_correlations]
      simp only [Complex.re_sum]
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      simpa only [Complex.re_sum] using
        Complex.re_le_norm (∑ t ∈ T, f a t * conj (f b t))

/-- Equal row sums allow averaging shifts without an endpoint error.
`T` must contain the supports of all rows, as it does for zero-extended shifts. -/
theorem equal_sums_sq_le_correlations {ι τ : Type*}
    (A : Finset ι) (T : Finset τ) (f : ι → τ → ℂ) (S : ℂ)
    (hsum : ∀ a ∈ A, ∑ t ∈ T, f a t = S) :
    (A.card : ℝ) ^ 2 * ‖S‖ ^ 2 ≤
      (T.card : ℝ) *
        ∑ a ∈ A, ∑ b ∈ A, ‖∑ t ∈ T, f a t * conj (f b t)‖ := by
  have heq : (∑ t ∈ T, ∑ a ∈ A, f a t) = (A.card : ℂ) * S := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_congr rfl hsum]
    simp
  have h := finite_sum_sq_le_correlations A T f
  rw [heq] at h
  simpa [norm_mul, mul_pow] using h

/-- The bounded-correlation form of finite differencing. The diagonal energy
is bounded by `L`, while every distinct-row correlation is bounded by `C`. -/
theorem equal_sums_sq_le_of_correlation_bound {ι τ : Type*}
    (A : Finset ι) (T : Finset τ) (f : ι → τ → ℂ) (S : ℂ) (L C : ℝ)
    (hsum : ∀ a ∈ A, ∑ t ∈ T, f a t = S)
    (hdiag : ∀ a ∈ A, ‖∑ t ∈ T, f a t * conj (f a t)‖ ≤ L)
    (hcorr : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      ‖∑ t ∈ T, f a t * conj (f b t)‖ ≤ C) :
    (A.card : ℝ) ^ 2 * ‖S‖ ^ 2 ≤
      (T.card : ℝ) * ((A.card : ℝ) * L +
        (A.card : ℝ) * ((A.card : ℝ) - 1) * C) := by
  classical
  have hrow (a : ι) (ha : a ∈ A) :
      ∑ b ∈ A, ‖∑ t ∈ T, f a t * conj (f b t)‖ ≤
        L + ((A.card : ℝ) - 1) * C := by
    calc
      _ ≤ ∑ b ∈ A, (C + if b = a then L - C else 0) := by
        apply Finset.sum_le_sum
        intro b hb
        by_cases hba : b = a
        · subst b
          simpa using hdiag a ha
        · simpa [hba] using hcorr a ha b hb (Ne.symm hba)
      _ = L + ((A.card : ℝ) - 1) * C := by
        simp [Finset.sum_add_distrib, ha]
        ring
  calc
    _ ≤ (T.card : ℝ) *
        ∑ a ∈ A, ∑ b ∈ A, ‖∑ t ∈ T, f a t * conj (f b t)‖ :=
      equal_sums_sq_le_correlations A T f S hsum
    _ ≤ (T.card : ℝ) * ∑ a ∈ A, (L + ((A.card : ℝ) - 1) * C) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum hrow
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Extend a finite sequence by zero, then shift its support to the right. -/
def zeroExtendedShift (f : ℕ → ℂ) (L d t : ℕ) : ℂ :=
  if t ∈ Finset.Ico d (d + L) then f (t - d) else 0

/-- A containing window captures the complete sum of a zero-extended shift. -/
theorem sum_zeroExtendedShift (f : ℕ → ℂ) (L d M : ℕ) (hM : d + L ≤ M) :
    ∑ t ∈ Finset.range M, zeroExtendedShift f L d t =
      ∑ t ∈ Finset.range L, f t := by
  have hsub : Finset.Ico d (d + L) ⊆ Finset.range M := by
    intro t ht
    exact Finset.mem_range.mpr ((Finset.mem_Ico.mp ht).2.trans_le hM)
  calc
    _ = ∑ t ∈ Finset.Ico d (d + L), zeroExtendedShift f L d t := by
      symm
      apply Finset.sum_subset hsub
      intro t ht hnot
      simp [zeroExtendedShift, hnot]
    _ = ∑ t ∈ Finset.Ico d (d + L), f (t - d) := by
      apply Finset.sum_congr rfl
      intro t ht
      simp [zeroExtendedShift, ht]
    _ = _ := by
      simpa [Nat.add_comm] using
        (Finset.sum_Ico_add_right_sub_eq (f := f) 0 L d)

/-- Unit-modulus entries have diagonal correlation exactly equal to their length. -/
theorem norm_diagonal_zeroExtendedShift (f : ℕ → ℂ) (L d M : ℕ)
    (hM : d + L ≤ M) (hf : ∀ t < L, ‖f t‖ = 1) :
    ‖∑ t ∈ Finset.range M,
      zeroExtendedShift f L d t * conj (zeroExtendedShift f L d t)‖ = L := by
  have hterm (t : ℕ) :
      zeroExtendedShift f L d t * conj (zeroExtendedShift f L d t) =
        zeroExtendedShift (fun _ => (1 : ℂ)) L d t := by
    by_cases ht : t ∈ Finset.Ico d (d + L)
    · have hlt : t - d < L := by
        have hm := Finset.mem_Ico.mp ht
        omega
      simp [zeroExtendedShift, ht, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, hf _ hlt]
    · simp [zeroExtendedShift, ht]
  simp_rw [hterm]
  rw [sum_zeroExtendedShift _ L d M hM]
  simp

/-- The zero-extended outer differencing inequality. All translates have exactly
the same sum; the containing window costs at most `L + H * step` positions. -/
theorem zeroExtendedShift_differencing (f : ℕ → ℂ) (L H step : ℕ) (C : ℝ)
    (hf : ∀ t < L, ‖f t‖ = 1)
    (hcorr : ∀ a ∈ Finset.range H, ∀ b ∈ Finset.range H, a ≠ b →
      ‖∑ t ∈ Finset.range (L + H * step),
        zeroExtendedShift f L (a * step) t *
          conj (zeroExtendedShift f L (b * step) t)‖ ≤ C) :
    (H : ℝ) ^ 2 * ‖∑ t ∈ Finset.range L, f t‖ ^ 2 ≤
      ((L : ℝ) + H * step) *
        ((H : ℝ) * L + (H : ℝ) * ((H : ℝ) - 1) * C) := by
  have hwindow (a : ℕ) (ha : a ∈ Finset.range H) :
      a * step + L ≤ L + H * step := by
    have hh := Nat.mul_le_mul_right step (Finset.mem_range.mp ha).le
    omega
  have h := equal_sums_sq_le_of_correlation_bound
    (Finset.range H) (Finset.range (L + H * step))
    (fun a t => zeroExtendedShift f L (a * step) t)
    (∑ t ∈ Finset.range L, f t) L C
    (fun a ha => sum_zeroExtendedShift f L (a * step) _ (hwindow a ha))
    (fun a ha => (norm_diagonal_zeroExtendedShift f L (a * step) _
      (hwindow a ha) hf).le) hcorr
  simpa only [Finset.card_range, Nat.cast_add, Nat.cast_mul] using h

/-- Correlations of two zero-extended translates are ordinary incomplete
correlations. Natural subtraction makes the sum empty when supports do not meet. -/
theorem zeroExtendedShift_correlation (f : ℕ → ℂ) (L d e M : ℕ)
    (hde : d ≤ e) (hM : e + L ≤ M) :
    (∑ t ∈ Finset.range M,
      zeroExtendedShift f L d t * conj (zeroExtendedShift f L e t)) =
      ∑ t ∈ Finset.range (L - (e - d)), f (t + (e - d)) * conj (f t) := by
  have hterm (t : ℕ) :
      zeroExtendedShift f L d t * conj (zeroExtendedShift f L e t) =
        zeroExtendedShift (fun u => f (u + (e - d)) * conj (f u))
          (L - (e - d)) e t := by
    by_cases ht : t ∈ Finset.Ico e (e + (L - (e - d)))
    · have hm := Finset.mem_Ico.mp ht
      have htd : t ∈ Finset.Ico d (d + L) := by
        apply Finset.mem_Ico.mpr
        omega
      have hte : t ∈ Finset.Ico e (e + L) := by
        apply Finset.mem_Ico.mpr
        omega
      have heq : t - e + (e - d) = t - d := by omega
      simp [zeroExtendedShift, ht, htd, hte, heq]
    · have hempty : ¬ (t ∈ Finset.Ico d (d + L) ∧
          t ∈ Finset.Ico e (e + L)) := by
        simp only [Finset.mem_Ico] at ht ⊢
        omega
      rcases not_and_or.mp hempty with htd | hte
      · simp [zeroExtendedShift, ht, htd]
      · simp [zeroExtendedShift, ht, hte]
  simp_rw [hterm]
  apply sum_zeroExtendedShift
  have hle : L - (e - d) ≤ L := Nat.sub_le _ _
  omega

/-- Exchanging the two rows conjugates a correlation and preserves its norm. -/
theorem norm_correlation_swap {ι : Type*} (T : Finset ι) (f g : ι → ℂ) :
    ‖∑ t ∈ T, f t * conj (g t)‖ = ‖∑ t ∈ T, g t * conj (f t)‖ := by
  calc
    _ = ‖conj (∑ t ∈ T, f t * conj (g t))‖ := (Complex.norm_conj _).symm
    _ = _ := by
      congr 1
      simp only [map_sum, map_mul, starRingEnd_self_apply]
      apply Finset.sum_congr rfl
      intro t ht
      ring

/-- A finite interval differencing estimate using positive stride multiples.
This is the outer inequality used for the two Stoneham constants. -/
theorem interval_differencing (f : ℕ → ℂ) (L H step : ℕ) (C : ℝ)
    (hf : ∀ t < L, ‖f t‖ = 1)
    (hcorr : ∀ j : ℕ, 0 < j → j < H →
      ‖∑ t ∈ Finset.range (L - j * step),
        f (t + j * step) * conj (f t)‖ ≤ C) :
    (H : ℝ) ^ 2 * ‖∑ t ∈ Finset.range L, f t‖ ^ 2 ≤
      ((L : ℝ) + H * step) *
        ((H : ℝ) * L + (H : ℝ) * ((H : ℝ) - 1) * C) := by
  apply zeroExtendedShift_differencing f L H step C hf
  intro a ha b hb hab
  have hwindow (i : ℕ) (hi : i ∈ Finset.range H) :
      i * step + L ≤ L + H * step := by
    have hh := Nat.mul_le_mul_right step (Finset.mem_range.mp hi).le
    omega
  have hforward (a b : ℕ) (ha : a ∈ Finset.range H) (hb : b ∈ Finset.range H)
      (hab : a < b) :
      ‖∑ t ∈ Finset.range (L + H * step),
        zeroExtendedShift f L (a * step) t *
          conj (zeroExtendedShift f L (b * step) t)‖ ≤ C := by
    rw [zeroExtendedShift_correlation f L (a * step) (b * step) _
      (Nat.mul_le_mul_right step hab.le) (hwindow b hb)]
    rw [← Nat.sub_mul]
    apply hcorr (b - a)
    · omega
    · have hbH := Finset.mem_range.mp hb
      omega
  rcases lt_or_gt_of_ne hab with hab | hab
  · exact hforward a b ha hb hab
  · rw [norm_correlation_swap]
    exact hforward b a hb ha hab

end StonehamNormality
