import StonehamNormality.GeneralRadix

/-!
# Arbitrary-base Stoneham series and sparse rational truncations

The scaled real approximation error is bounded by `1 / (n + 1)` uniformly
over all bases at least two. Between successive support events, the rational
truncations follow the exact radix orbit.
-/

noncomputable section
open Filter
open scoped BigOperators Topology Classical

namespace StonehamNormality

def radixStonehamTerm (b c m : ℕ) : ℝ :=
  if IsStonehamIndex c m then 1 / ((m : ℝ) * (b : ℝ) ^ m) else 0

def sparseStonehamConstant (b c : ℕ) : ℝ := ∑' m : ℕ, radixStonehamTerm b c m

def radixStonehamTruncation (b c n : ℕ) : ℚ :=
  ∑ m ∈ (Finset.range (n + 1)).filter (IsStonehamIndex c), (b : ℚ) ^ (n - m) / m

theorem radixStonehamTerm_nonneg (b c m : ℕ) : 0 ≤ radixStonehamTerm b c m := by
  unfold radixStonehamTerm
  split_ifs <;> positivity

theorem radixStonehamTerm_le_geometric (b c m : ℕ) (hb : 2 ≤ b) :
    radixStonehamTerm b c m ≤ (1 / 2 : ℝ) ^ m := by
  by_cases hm0 : m = 0
  · subst m
    simp [radixStonehamTerm]
  have hbr : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbp : (0 : ℝ) < b := by linarith
  have hp : (2 : ℝ) ^ m ≤ (b : ℝ) ^ m := pow_le_pow_left₀ (by norm_num) hbr m
  unfold radixStonehamTerm
  split_ifs
  · have hone : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm0)
    rw [one_div_pow]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [pow_pos hbp m]
  · positivity

theorem summable_radixStonehamTerm (b c : ℕ) (hb : 2 ≤ b) :
    Summable (radixStonehamTerm b c) :=
  Summable.of_nonneg_of_le (radixStonehamTerm_nonneg b c)
    (fun m => radixStonehamTerm_le_geometric b c m hb)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

theorem sparseStonehamConstant_nonneg (b c : ℕ) : 0 ≤ sparseStonehamConstant b c :=
  tsum_nonneg (radixStonehamTerm_nonneg b c)

theorem sparseStonehamConstant_eq_prefix_add_tail (b c n : ℕ) (hb : 2 ≤ b) :
    sparseStonehamConstant b c =
      (∑ m ∈ Finset.range (n + 1), radixStonehamTerm b c m) +
        ∑' j : ℕ, radixStonehamTerm b c (j + (n + 1)) :=
  ((summable_radixStonehamTerm b c hb).sum_add_tsum_nat_add (n + 1)).symm

theorem radixStonehamTruncation_eq_scaled_prefix (b c n : ℕ) (hb : 2 ≤ b) :
    (radixStonehamTruncation b c n : ℝ) =
      (b : ℝ) ^ n * ∑ m ∈ Finset.range (n + 1), radixStonehamTerm b c m := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  unfold radixStonehamTruncation
  push_cast
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := by simpa using Finset.mem_range.mp hm
  by_cases hs : IsStonehamIndex c m
  · simp only [hs, ite_true, radixStonehamTerm]
    rw [pow_sub₀ (b : ℝ) hb0 hmn]
    ring
  · simp [hs, radixStonehamTerm]

theorem radixStoneham_scaled_tail_identity (b c n : ℕ) (hb : 2 ≤ b) :
    (b : ℝ) ^ n * sparseStonehamConstant b c - (radixStonehamTruncation b c n : ℝ) =
      ∑' j : ℕ, (b : ℝ) ^ n * radixStonehamTerm b c (j + (n + 1)) := by
  rw [radixStonehamTruncation_eq_scaled_prefix b c n hb,
    sparseStonehamConstant_eq_prefix_add_tail b c n hb, mul_add, add_sub_cancel_left]
  exact (tsum_mul_left).symm

theorem radixStonehamTruncation_error_nonneg (b c n : ℕ) (hb : 2 ≤ b) :
    0 ≤ (b : ℝ) ^ n * sparseStonehamConstant b c -
      (radixStonehamTruncation b c n : ℝ) := by
  rw [radixStoneham_scaled_tail_identity b c n hb]
  exact tsum_nonneg (fun j => mul_nonneg (by positivity) (radixStonehamTerm_nonneg b c _))

theorem radixStoneham_scaled_tail_summand_le (b c n j : ℕ) (hb : 2 ≤ b) :
    (b : ℝ) ^ n * radixStonehamTerm b c (j + (n + 1)) ≤
      ((n : ℝ) + 1)⁻¹ * (1 / 2 : ℝ) ^ (j + 1) := by
  have hbr : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbp : (0 : ℝ) < b := by linarith
  unfold radixStonehamTerm
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

theorem radixStonehamTruncation_error_le (b c n : ℕ) (hb : 2 ≤ b) :
    (b : ℝ) ^ n * sparseStonehamConstant b c - (radixStonehamTruncation b c n : ℝ) ≤
      ((n : ℝ) + 1)⁻¹ := by
  have hgeo : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_right (1 / 2)
  have htail : Summable (fun j : ℕ =>
      (b : ℝ) ^ n * radixStonehamTerm b c (j + (n + 1))) :=
    ((summable_nat_add_iff (n + 1)).2 (summable_radixStonehamTerm b c hb)).mul_left _
  rw [radixStoneham_scaled_tail_identity b c n hb]
  calc
    _ ≤ ∑' j : ℕ, ((n : ℝ) + 1)⁻¹ * (1 / 2 : ℝ) ^ (j + 1) :=
      htail.tsum_le_tsum (fun j => radixStoneham_scaled_tail_summand_le b c n j hb)
        (hgeo.mul_left _)
    _ = ((n : ℝ) + 1)⁻¹ := by
      simp_rw [pow_succ]
      rw [tsum_mul_left, tsum_mul_right,
        tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)]
      ring

theorem sparseStonehamTruncation_error_tendsto_zero (b c : ℕ) (hb : 2 ≤ b) :
    Tendsto (fun n : ℕ => (b : ℝ) ^ n * sparseStonehamConstant b c -
      (radixStonehamTruncation b c n : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => radixStonehamTruncation_error_nonneg b c n hb)
    (fun n => radixStonehamTruncation_error_le b c n hb)
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

/-- A support gap gives an exact orbit in the requested radix. -/
theorem radixStonehamTruncation_add_of_no_new_terms (b c n t : ℕ)
    (hnew : ∀ m : ℕ, IsStonehamIndex c m → m ≤ n + t → m ≤ n) :
    radixStonehamTruncation b c (n + t) = (b : ℚ) ^ t * radixStonehamTruncation b c n := by
  have hs : (Finset.range (n + t + 1)).filter (IsStonehamIndex c) =
      (Finset.range (n + 1)).filter (IsStonehamIndex c) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hm, hsm⟩
      exact ⟨by have := hnew m hsm (by omega); omega, hsm⟩
    · rintro ⟨hm, hsm⟩
      exact ⟨by omega, hsm⟩
  unfold radixStonehamTruncation
  rw [hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  have he : n + t - m = t + (n - m) := by omega
  rw [he, pow_add, mul_div_assoc]

theorem radixStonehamTerm_support_subset_power_range (b c : ℕ) :
    Function.support (radixStonehamTerm b c) ⊆ Set.range (fun k : ℕ => c ^ (k + 1)) := by
  intro m hm
  have hs : IsStonehamIndex c m := by
    by_contra h
    simpa [Function.mem_support, radixStonehamTerm, h] using hm
  obtain ⟨k, hk, rfl⟩ := hs
  refine ⟨k - 1, ?_⟩
  dsimp
  rw [show k - 1 + 1 = k by omega]

/-- The sparse-index series is the conventional Stoneham constant. -/
theorem sparseStonehamConstant_eq_standard (b c : ℕ) (hc : 2 ≤ c) :
    sparseStonehamConstant b c = stonehamConstant b c := by
  have hinj : Function.Injective (fun k : ℕ => c ^ (k + 1)) := by
    intro k l h
    have he := Nat.pow_right_injective hc h
    omega
  calc
    sparseStonehamConstant b c = ∑' k : ℕ, radixStonehamTerm b c (c ^ (k + 1)) :=
      (hinj.tsum_eq (radixStonehamTerm_support_subset_power_range b c)).symm
    _ = stonehamConstant b c := by
      apply tsum_congr
      intro k
      have hs : IsStonehamIndex c (c ^ (k + 1)) := ⟨k + 1, by omega, rfl⟩
      simp [radixStonehamTerm, hs]

/-- The actual Stoneham constant is approximated by the rational truncations. -/
theorem radixStonehamTruncation_error_tendsto_zero (b c : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    Tendsto (fun n : ℕ => (b : ℝ) ^ n * stonehamConstant b c -
      (radixStonehamTruncation b c n : ℝ)) atTop (𝓝 0) := by
  simpa only [sparseStonehamConstant_eq_standard b c hc] using
    sparseStonehamTruncation_error_tendsto_zero b c hb

theorem radixStoneham_rat_combination_error_tendsto_zero
    (b c d : ℕ) (u v : ℚ) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) :
    Tendsto (fun n : ℕ =>
      (b : ℝ) ^ n * ((u : ℝ) * stonehamConstant b c + (v : ℝ) * stonehamConstant b d) -
        ((u * radixStonehamTruncation b c n + v * radixStonehamTruncation b d n : ℚ) : ℝ))
      atTop (𝓝 0) := by
  have he : (fun n : ℕ =>
      (b : ℝ) ^ n * ((u : ℝ) * stonehamConstant b c + (v : ℝ) * stonehamConstant b d) -
        ((u * radixStonehamTruncation b c n + v * radixStonehamTruncation b d n : ℚ) : ℝ)) =
      (fun n : ℕ =>
        (u : ℝ) * ((b : ℝ) ^ n * stonehamConstant b c -
          (radixStonehamTruncation b c n : ℝ)) +
        (v : ℝ) * ((b : ℝ) ^ n * stonehamConstant b d -
          (radixStonehamTruncation b d n : ℝ))) := by
    funext n
    push_cast
    ring
  rw [he]
  simpa using ((radixStonehamTruncation_error_tendsto_zero b c hb hc).const_mul (u : ℝ)).add
    ((radixStonehamTruncation_error_tendsto_zero b d hb hd).const_mul (v : ℝ))

end StonehamNormality
