import XiNormality.Imports

/-!
# An elementary incomplete-sum estimate from orthogonal shifts

For the qualitative normality theorem, finite Cauchy--Schwarz replaces the
paper's Gauss-sum completion argument.  The lemmas in this file are independent
of the arithmetic application: they concern finite families of complex vectors.
-/

noncomputable section

open scoped BigOperators ComplexConjugate
open Complex

namespace XiNormality

/-- The energy of a sum of pairwise orthogonal unit-modulus vectors. -/
theorem finite_orthogonal_energy {ι τ : Type*}
    (A : Finset ι) (T : Finset τ) (f : ι → τ → ℂ)
    (hnorm : ∀ a ∈ A, ∀ t ∈ T, ‖f a t‖ = 1)
    (horth : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      ∑ t ∈ T, f a t * conj (f b t) = 0) :
    ∑ t ∈ T, ‖∑ a ∈ A, f a t‖ ^ 2 = (A.card : ℝ) * T.card := by
  classical
  have hdiag (a : ι) (ha : a ∈ A) :
      ∑ t ∈ T, f a t * conj (f a t) = (T.card : ℂ) := by
    calc
      _ = ∑ t ∈ T, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm a ha t ht]
        norm_num
      _ = (T.card : ℂ) := by simp
  have henergy :
      ∑ t ∈ T, (∑ a ∈ A, f a t) * conj (∑ a ∈ A, f a t) =
        (A.card : ℂ) * T.card := by
    simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      ∑ a ∈ A, ∑ t ∈ T, ∑ b ∈ A, f a t * conj (f b t) =
          ∑ a ∈ A, ∑ b ∈ A, ∑ t ∈ T, f a t * conj (f b t) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.sum_comm]
      _ = ∑ a ∈ A, (T.card : ℂ) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_eq_single a]
        · exact hdiag a ha
        · intro b hb hba
          exact horth a ha b hb hba.symm
        · exact fun h => (h ha).elim
      _ = (A.card : ℂ) * T.card := by simp
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at henergy
  have hre := congrArg Complex.re henergy
  simpa [Complex.re_sum, Complex.mul_re, ← Complex.ofReal_pow] using hre

/-- Finite Cauchy--Schwarz in a form convenient for complex interval sums. -/
theorem norm_sum_sq_le_card_mul_energy {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    ‖∑ t ∈ S, f t‖ ^ 2 ≤ (S.card : ℝ) * ∑ t ∈ S, ‖f t‖ ^ 2 := by
  have hnonneg : 0 ≤ ∑ t ∈ S, ‖f t‖ :=
    Finset.sum_nonneg (fun t ht => norm_nonneg (f t))
  calc
    ‖∑ t ∈ S, f t‖ ^ 2 ≤ (∑ t ∈ S, ‖f t‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hnonneg).2 (norm_sum_le S f)
    _ ≤ (S.card : ℝ) * ∑ t ∈ S, ‖f t‖ ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ))
        (fun t => ‖f t‖)

/-- Restricting an orthogonal family to an arbitrary subset costs only its
cardinality.  In the application the subset is an initial interval of a period. -/
theorem finite_orthogonal_subsum_sq_le {ι τ : Type*}
    (A : Finset ι) (S T : Finset τ) (f : ι → τ → ℂ) (hST : S ⊆ T)
    (hnorm : ∀ a ∈ A, ∀ t ∈ T, ‖f a t‖ = 1)
    (horth : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      ∑ t ∈ T, f a t * conj (f b t) = 0) :
    ‖∑ t ∈ S, ∑ a ∈ A, f a t‖ ^ 2 ≤
      (S.card : ℝ) * ((A.card : ℝ) * T.card) := by
  calc
    ‖∑ t ∈ S, ∑ a ∈ A, f a t‖ ^ 2 ≤
        (S.card : ℝ) * ∑ t ∈ S, ‖∑ a ∈ A, f a t‖ ^ 2 :=
      norm_sum_sq_le_card_mul_energy S (fun t => ∑ a ∈ A, f a t)
    _ ≤ (S.card : ℝ) * ∑ t ∈ T, ‖∑ a ∈ A, f a t‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun t ht hts => sq_nonneg _)
    _ = (S.card : ℝ) * ((A.card : ℝ) * T.card) := by
      rw [finite_orthogonal_energy A T f hnorm horth]

/-- A unit-bounded sequence has interval sums bounded by the interval length. -/
theorem norm_sum_range_le_length (f : ℕ → ℂ) (L : ℕ)
    (hf : ∀ t, ‖f t‖ ≤ 1) :
    ‖∑ t ∈ Finset.range L, f t‖ ≤ L := by
  calc
    ‖∑ t ∈ Finset.range L, f t‖ ≤ ∑ t ∈ Finset.range L, ‖f t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ t ∈ Finset.range L, (1 : ℝ) :=
      Finset.sum_le_sum (fun t ht => hf t)
    _ = L := by simp

/-- Translating an interval sum changes only the two end pieces. -/
theorem norm_sum_range_shift_sub_le (f : ℕ → ℂ) (L a : ℕ)
    (hf : ∀ t, ‖f t‖ ≤ 1) :
    ‖(∑ t ∈ Finset.range L, f (t + a)) - ∑ t ∈ Finset.range L, f t‖ ≤
      2 * (a : ℝ) := by
  have hsplit :
      (∑ t ∈ Finset.range a, f t) + (∑ t ∈ Finset.range L, f (t + a)) =
        (∑ t ∈ Finset.range L, f t) + ∑ t ∈ Finset.range a, f (t + L) := by
    calc
      _ = ∑ t ∈ Finset.range (a + L), f t := by
        simpa only [Nat.add_comm] using (Finset.sum_range_add f a L).symm
      _ = _ := by
        simpa only [Nat.add_comm] using Finset.sum_range_add f L a
  have hdiff :
      (∑ t ∈ Finset.range L, f (t + a)) - ∑ t ∈ Finset.range L, f t =
        (∑ t ∈ Finset.range a, f (t + L)) - ∑ t ∈ Finset.range a, f t := by
    linear_combination hsplit
  rw [hdiff]
  calc
    ‖(∑ t ∈ Finset.range a, f (t + L)) - ∑ t ∈ Finset.range a, f t‖ ≤
        ‖∑ t ∈ Finset.range a, f (t + L)‖ + ‖∑ t ∈ Finset.range a, f t‖ :=
      norm_sub_le _ _
    _ ≤ (a : ℝ) + a :=
      add_le_add (norm_sum_range_le_length (fun t => f (t + L)) a (fun t => hf _))
        (norm_sum_range_le_length f a hf)
    _ = 2 * (a : ℝ) := by ring

/-- Boundary control for an average of `H` translated intervals.  The deliberately
coarse quadratic bound is sufficient for the qualitative application. -/
theorem norm_sliding_sum_sub_mul_le (f : ℕ → ℂ) (L H : ℕ)
    (hf : ∀ t, ‖f t‖ ≤ 1) :
    ‖(∑ t ∈ Finset.range L, ∑ a ∈ Finset.range H, f (t + a)) -
      (H : ℂ) * ∑ t ∈ Finset.range L, f t‖ ≤ 2 * (H : ℝ) ^ 2 := by
  have hrewrite :
      (∑ t ∈ Finset.range L, ∑ a ∈ Finset.range H, f (t + a)) -
          (H : ℂ) * ∑ t ∈ Finset.range L, f t =
        ∑ a ∈ Finset.range H,
          ((∑ t ∈ Finset.range L, f (t + a)) - ∑ t ∈ Finset.range L, f t) := by
    rw [Finset.sum_sub_distrib, Finset.sum_comm]
    simp
  rw [hrewrite]
  calc
    ‖∑ a ∈ Finset.range H,
        ((∑ t ∈ Finset.range L, f (t + a)) - ∑ t ∈ Finset.range L, f t)‖ ≤
        ∑ a ∈ Finset.range H,
          ‖(∑ t ∈ Finset.range L, f (t + a)) - ∑ t ∈ Finset.range L, f t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.range H, 2 * (H : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      have haH : (a : ℝ) ≤ H := by exact_mod_cast (Finset.mem_range.mp ha).le
      exact (norm_sum_range_shift_sub_le f L a hf).trans (by gcongr)
    _ = 2 * (H : ℝ) ^ 2 := by simp; ring

/-- The incomplete-sum estimate obtained from orthogonal translates.  No Fourier
inversion or bound for multiplicative Gauss sums is required. -/
theorem sliding_window_bound (f : ℕ → ℂ) (L H T : ℕ) (hLT : L ≤ T)
    (hf : ∀ t, ‖f t‖ = 1)
    (horth : ∀ a ∈ Finset.range H, ∀ b ∈ Finset.range H, a ≠ b →
      ∑ t ∈ Finset.range T, f (t + a) * conj (f (t + b)) = 0) :
    (H : ℝ) * ‖∑ t ∈ Finset.range L, f t‖ ≤
      Real.sqrt ((L : ℝ) * ((H : ℝ) * T)) + 2 * (H : ℝ) ^ 2 := by
  let W : ℂ := ∑ t ∈ Finset.range L, ∑ a ∈ Finset.range H, f (t + a)
  have henergy : ‖W‖ ^ 2 ≤ (L : ℝ) * ((H : ℝ) * T) := by
    simpa only [W, Finset.card_range] using
      finite_orthogonal_subsum_sq_le (Finset.range H) (Finset.range L)
        (Finset.range T) (fun a t => f (t + a)) (Finset.range_mono hLT)
        (fun a ha t ht => hf _) horth
  have hW : ‖W‖ ≤ Real.sqrt ((L : ℝ) * ((H : ℝ) * T)) :=
    Real.le_sqrt_of_sq_le henergy
  have hboundary :
      ‖W - (H : ℂ) * ∑ t ∈ Finset.range L, f t‖ ≤ 2 * (H : ℝ) ^ 2 :=
    norm_sliding_sum_sub_mul_le f L H (fun t => (hf t).le)
  calc
    (H : ℝ) * ‖∑ t ∈ Finset.range L, f t‖ =
        ‖(H : ℂ) * ∑ t ∈ Finset.range L, f t‖ := by simp
    _ ≤ ‖W‖ + ‖W - (H : ℂ) * ∑ t ∈ Finset.range L, f t‖ := by
      exact norm_le_norm_add_norm_sub W
        ((H : ℂ) * ∑ t ∈ Finset.range L, f t)
    _ ≤ Real.sqrt ((L : ℝ) * ((H : ℝ) * T)) + 2 * (H : ℝ) ^ 2 :=
      add_le_add hW hboundary

end XiNormality
