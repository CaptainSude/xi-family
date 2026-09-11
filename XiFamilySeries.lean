import XiFamilyDefinition

/-!
# Xi rational truncations and the approximation error

These statements use the distinct-index definition, without coprimality
restrictions on the generators. Rational truncations approximate the radix
orbit with error at most one divided by the cutoff plus one.
-/

noncomputable section
open Filter
open scoped BigOperators Topology Classical

namespace XiFamily

def truncation (b c a n : ℕ) : ℚ :=
  ∑ m ∈ (Finset.range (n + 1)).filter (IsIndex a c), (b : ℚ) ^ (n - m) / m

theorem xi_eq_prefix_add_tail (b c a n : ℕ) (hb : 2 ≤ b) :
    xi b c a =
      (∑ m ∈ Finset.range (n + 1), term b c a m) +
        ∑' j : ℕ, term b c a (j + (n + 1)) :=
  ((summable_term b c a hb).sum_add_tsum_nat_add (n + 1)).symm

theorem truncation_eq_scaled_prefix (b c a n : ℕ) (hb : 2 ≤ b) :
    (truncation b c a n : ℝ) =
      (b : ℝ) ^ n * ∑ m ∈ Finset.range (n + 1), term b c a m := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  unfold truncation
  push_cast
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := by simpa using Finset.mem_range.mp hm
  by_cases hs : IsIndex a c m
  · simp only [hs, ite_true, term]
    rw [pow_sub₀ (b : ℝ) hb0 hmn]
    ring
  · simp [hs, term]

theorem scaled_tail_identity (b c a n : ℕ) (hb : 2 ≤ b) :
    (b : ℝ) ^ n * xi b c a - (truncation b c a n : ℝ) =
      ∑' j : ℕ, (b : ℝ) ^ n * term b c a (j + (n + 1)) := by
  rw [truncation_eq_scaled_prefix b c a n hb,
    xi_eq_prefix_add_tail b c a n hb, mul_add, add_sub_cancel_left]
  exact (tsum_mul_left).symm

theorem truncation_error_nonneg (b c a n : ℕ) (hb : 2 ≤ b) :
    0 ≤ (b : ℝ) ^ n * xi b c a -
      (truncation b c a n : ℝ) := by
  rw [scaled_tail_identity b c a n hb]
  exact tsum_nonneg (fun j => mul_nonneg (by positivity) (term_nonneg b c a _))

theorem scaled_tail_summand_le (b c a n j : ℕ) (hb : 2 ≤ b) :
    (b : ℝ) ^ n * term b c a (j + (n + 1)) ≤
      ((n : ℝ) + 1)⁻¹ * (1 / 2 : ℝ) ^ (j + 1) := by
  have hbr : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbp : (0 : ℝ) < b := by linarith
  unfold term
  split_ifs
  · calc
      (b : ℝ) ^ n * (1 / ((j + (n + 1) : ℕ) * (b : ℝ) ^ (j + (n + 1))))
          ≤ (b : ℝ) ^ n * (1 / (((n : ℝ) + 1) * (b : ℝ) ^ (j + (n + 1)))) := by
            gcongr
            simp only [Nat.cast_add, Nat.cast_one]
            linarith [Nat.cast_nonneg (α := ℝ) j]
      _ = ((n : ℝ) + 1)⁻¹ * (1 / (b : ℝ)) ^ (j + 1) := by
        rw [show j + (n + 1) = n + (j + 1) by omega, pow_add, one_div_pow]
        field_simp [hbp.ne']
      _ ≤ ((n : ℝ) + 1)⁻¹ * (1 / 2 : ℝ) ^ (j + 1) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity)
            (one_div_le_one_div_of_le (by norm_num) hbr) (j + 1)) (by positivity)
  · simp only [mul_zero]
    positivity

theorem truncation_error_le (b c a n : ℕ) (hb : 2 ≤ b) :
    (b : ℝ) ^ n * xi b c a - (truncation b c a n : ℝ) ≤
      ((n : ℝ) + 1)⁻¹ := by
  have hgeo : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_right (1 / 2)
  have htail : Summable (fun j : ℕ =>
      (b : ℝ) ^ n * term b c a (j + (n + 1))) :=
    ((summable_nat_add_iff (n + 1)).2 (summable_term b c a hb)).mul_left _
  rw [scaled_tail_identity b c a n hb]
  calc
    _ ≤ ∑' j : ℕ, ((n : ℝ) + 1)⁻¹ * (1 / 2 : ℝ) ^ (j + 1) :=
      htail.tsum_le_tsum (fun j => scaled_tail_summand_le b c a n j hb)
        (hgeo.mul_left _)
    _ = ((n : ℝ) + 1)⁻¹ := by
      simp_rw [pow_succ]
      rw [tsum_mul_left, tsum_mul_right,
        tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)]
      ring

theorem truncation_error_tendsto_zero (b c a : ℕ) (hb : 2 ≤ b) :
    Tendsto (fun n : ℕ => (b : ℝ) ^ n * xi b c a -
      (truncation b c a n : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => truncation_error_nonneg b c a n hb)
    (fun n => truncation_error_le b c a n hb)
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

/-- Finite rational combinations, including a rational constant term, inherit
the vanishing approximation error. This is an approximation statement,
independent of the later normality and noncancellation arguments. -/
theorem rational_combination_error_tendsto_zero {ι : Type*} (J : Finset ι)
    (b : ℕ) (c a : ι → ℕ) (q : ι → ℚ) (q₀ : ℚ) (hb : 2 ≤ b) :
    Tendsto (fun n : ℕ =>
      (b : ℝ) ^ n * ((q₀ : ℝ) + ∑ j ∈ J, (q j : ℝ) * xi b (c j) (a j)) -
        ((q₀ * (b : ℚ) ^ n + ∑ j ∈ J, q j * truncation b (c j) (a j) n : ℚ) : ℝ))
      atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ∑ j ∈ J, (q j : ℝ) *
      ((b : ℝ) ^ n * xi b (c j) (a j) - (truncation b (c j) (a j) n : ℝ)))
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum J (fun j _ =>
      (truncation_error_tendsto_zero b (c j) (a j) hb).const_mul (q j : ℝ))
  convert h using 1
  funext n
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hsum : (∑ j ∈ J, (q j : ℝ) * ((b : ℝ) ^ n * xi b (c j) (a j))) =
      (b : ℝ) ^ n * ∑ j ∈ J, (q j : ℝ) * xi b (c j) (a j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  ring

/-- A support gap gives an exact orbit in the requested radix. -/
theorem truncation_add_of_no_new_terms (b c a n t : ℕ)
    (hnew : ∀ m : ℕ, IsIndex a c m → m ≤ n + t → m ≤ n) :
    truncation b c a (n + t) = (b : ℚ) ^ t * truncation b c a n := by
  have hs : (Finset.range (n + t + 1)).filter (IsIndex a c) =
      (Finset.range (n + 1)).filter (IsIndex a c) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hm, hsm⟩
      exact ⟨by have := hnew m hsm (by omega); omega, hsm⟩
    · rintro ⟨hm, hsm⟩
      exact ⟨by omega, hsm⟩
  unfold truncation
  rw [hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  have he : n + t - m = t + (n - m) := by omega
  rw [he, pow_add, mul_div_assoc]


end XiFamily
