import XiNormality.Imports
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Stoneham series and their rational radix truncations

The support consists of the positive powers `p^k`, `k ≥ 1`.
All convergence and tail estimates are proved from a geometric majorant.
-/

noncomputable section
open scoped BigOperators Classical Topology
open Filter

namespace StonehamNormality

def IsStonehamIndex (p m : ℕ) : Prop := ∃ k : ℕ, 1 ≤ k ∧ m = p ^ k

def stonehamTerm (p m : ℕ) : ℝ :=
  if IsStonehamIndex p m then 1 / ((m : ℝ) * 2 ^ m) else 0

def stoneham (p : ℕ) : ℝ := ∑' m : ℕ, stonehamTerm p m

def stonehamTruncation (p n : ℕ) : ℚ :=
  ∑ m ∈ (Finset.range (n + 1)).filter (IsStonehamIndex p),
    (2 : ℚ) ^ (n - m) / m

theorem stonehamTerm_nonneg (p m : ℕ) : 0 ≤ stonehamTerm p m := by
  unfold stonehamTerm
  split_ifs <;> positivity

theorem stonehamTerm_le_geometric (p m : ℕ) :
    stonehamTerm p m ≤ (1 / 2 : ℝ) ^ m := by
  by_cases hm0 : m = 0
  · subst m
    simp [stonehamTerm]
  unfold stonehamTerm
  split_ifs
  · have hone : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm0)
    rw [one_div_pow]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) m]
  · positivity

theorem summable_stonehamTerm (p : ℕ) : Summable (stonehamTerm p) := by
  exact Summable.of_nonneg_of_le (stonehamTerm_nonneg p)
    (stonehamTerm_le_geometric p)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

theorem stoneham_nonneg (p : ℕ) : 0 ≤ stoneham p :=
  tsum_nonneg (stonehamTerm_nonneg p)

theorem stoneham_eq_prefix_add_tail (p n : ℕ) :
    stoneham p = (∑ m ∈ Finset.range (n + 1), stonehamTerm p m) +
      ∑' j : ℕ, stonehamTerm p (j + (n + 1)) := by
  exact ((summable_stonehamTerm p).sum_add_tsum_nat_add (n + 1)).symm

theorem stonehamTruncation_eq_scaled_prefix (p n : ℕ) :
    (stonehamTruncation p n : ℝ) =
      (2 : ℝ) ^ n * ∑ m ∈ Finset.range (n + 1), stonehamTerm p m := by
  classical
  unfold stonehamTruncation
  push_cast
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := by simpa using Finset.mem_range.mp hm
  by_cases hs : IsStonehamIndex p m
  · simp only [hs, ite_true, stonehamTerm]
    rw [pow_sub₀ (2 : ℝ) (by norm_num) hmn]
    ring
  · simp [hs, stonehamTerm]

theorem stoneham_scaled_tail_identity (p n : ℕ) :
    (2 : ℝ) ^ n * stoneham p - (stonehamTruncation p n : ℝ) =
      ∑' j : ℕ, (2 : ℝ) ^ n * stonehamTerm p (j + (n + 1)) := by
  rw [stonehamTruncation_eq_scaled_prefix, stoneham_eq_prefix_add_tail p n,
    mul_add, add_sub_cancel_left]
  exact (tsum_mul_left).symm

theorem stonehamTruncation_error_nonneg (p n : ℕ) :
    0 ≤ (2 : ℝ) ^ n * stoneham p - (stonehamTruncation p n : ℝ) := by
  rw [stoneham_scaled_tail_identity]
  exact tsum_nonneg (fun j => mul_nonneg (by positivity) (stonehamTerm_nonneg p _))

theorem stoneham_scaled_tail_summand_le (p n j : ℕ) :
    (2 : ℝ) ^ n * stonehamTerm p (j + (n + 1)) ≤
      ((n : ℝ) + 1)⁻¹ * (1 / 2 : ℝ) ^ (j + 1) := by
  unfold stonehamTerm
  split_ifs
  · calc
      (2 : ℝ) ^ n * (1 / ((j + (n + 1) : ℕ) * 2 ^ (j + (n + 1))))
          ≤ (2 : ℝ) ^ n * (1 / (((n : ℝ) + 1) * 2 ^ (j + (n + 1)))) := by
            gcongr
            simp only [Nat.cast_add, Nat.cast_one]
            linarith [Nat.cast_nonneg (α := ℝ) j]
      _ = ((n : ℝ) + 1)⁻¹ * (1 / 2 : ℝ) ^ (j + 1) := by
        rw [show j + (n + 1) = n + (j + 1) by omega, pow_add, one_div_pow]
        field_simp
  · simp only [mul_zero]
    positivity

theorem stonehamTruncation_error_le (p n : ℕ) :
    (2 : ℝ) ^ n * stoneham p - (stonehamTruncation p n : ℝ) ≤
      ((n : ℝ) + 1)⁻¹ := by
  have hgeo : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_right (1 / 2)
  have htail : Summable (fun j : ℕ =>
      (2 : ℝ) ^ n * stonehamTerm p (j + (n + 1))) :=
    ((summable_nat_add_iff (n + 1)).2 (summable_stonehamTerm p)).mul_left _
  rw [stoneham_scaled_tail_identity]
  calc
    (∑' j : ℕ, (2 : ℝ) ^ n * stonehamTerm p (j + (n + 1)))
        ≤ ∑' j : ℕ, ((n : ℝ) + 1)⁻¹ * (1 / 2 : ℝ) ^ (j + 1) :=
      htail.tsum_le_tsum (stoneham_scaled_tail_summand_le p n) (hgeo.mul_left _)
    _ = ((n : ℝ) + 1)⁻¹ := by
      simp_rw [pow_succ]
      rw [tsum_mul_left, tsum_mul_right,
        tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)]
      ring

theorem stonehamTruncation_error_tendsto_zero (p : ℕ) :
    Tendsto (fun n : ℕ => (2 : ℝ) ^ n * stoneham p -
      (stonehamTruncation p n : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (stonehamTruncation_error_nonneg p) (stonehamTruncation_error_le p)
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

/-- A gap in the support gives an exact doubling orbit for the truncations. -/
theorem stonehamTruncation_add_of_no_new_terms (p n t : ℕ)
    (hnew : ∀ m : ℕ, IsStonehamIndex p m → m ≤ n + t → m ≤ n) :
    stonehamTruncation p (n + t) = (2 : ℚ) ^ t * stonehamTruncation p n := by
  classical
  have hs : (Finset.range (n + t + 1)).filter (IsStonehamIndex p) =
      (Finset.range (n + 1)).filter (IsStonehamIndex p) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hm, hsm⟩
      exact ⟨by have := hnew m hsm (by omega); omega, hsm⟩
    · rintro ⟨hm, hsm⟩
      exact ⟨by omega, hsm⟩
  unfold stonehamTruncation
  rw [hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  have he : n + t - m = t + (n - m) := by omega
  rw [he, pow_add, mul_div_assoc]

theorem stonehamTerm_support_subset_power_range (p : ℕ) :
    Function.support (stonehamTerm p) ⊆ Set.range (fun k : ℕ => p ^ (k + 1)) := by
  intro m hm
  have hs : IsStonehamIndex p m := by
    by_contra h
    simpa [Function.mem_support, stonehamTerm, h] using hm
  obtain ⟨k, hk, rfl⟩ := hs
  refine ⟨k - 1, ?_⟩
  dsimp
  rw [show k - 1 + 1 = k by omega]

/-- The sparse-index definition is exactly the conventional Stoneham series. -/
theorem stoneham_eq_power_series {p : ℕ} (hp : 2 ≤ p) :
    stoneham p = ∑' k : ℕ,
      1 / ((p : ℝ) ^ (k + 1) * (2 : ℝ) ^ (p ^ (k + 1))) := by
  have hinj : Function.Injective (fun k : ℕ => p ^ (k + 1)) := by
    intro k l h
    have he := Nat.pow_right_injective hp h
    omega
  calc
    stoneham p = ∑' k : ℕ, stonehamTerm p (p ^ (k + 1)) :=
      (hinj.tsum_eq (stonehamTerm_support_subset_power_range p)).symm
    _ = _ := by
      apply tsum_congr
      intro k
      have hs : IsStonehamIndex p (p ^ (k + 1)) := ⟨k + 1, by omega, rfl⟩
      simp [stonehamTerm, hs]

theorem stoneham_linear_combination_error_tendsto_zero (p q : ℕ) (u v : ℤ) :
    Tendsto (fun n : ℕ =>
      (2 : ℝ) ^ n * ((u : ℝ) * stoneham p + (v : ℝ) * stoneham q) -
        (((u : ℚ) * stonehamTruncation p n +
          (v : ℚ) * stonehamTruncation q n : ℚ) : ℝ)) atTop (𝓝 0) := by
  have he : (fun n : ℕ =>
      (2 : ℝ) ^ n * ((u : ℝ) * stoneham p + (v : ℝ) * stoneham q) -
        (((u : ℚ) * stonehamTruncation p n +
          (v : ℚ) * stonehamTruncation q n : ℚ) : ℝ)) =
      (fun n : ℕ =>
        (u : ℝ) * ((2 : ℝ) ^ n * stoneham p - (stonehamTruncation p n : ℝ)) +
        (v : ℝ) * ((2 : ℝ) ^ n * stoneham q - (stonehamTruncation q n : ℝ))) := by
    funext n
    push_cast
    ring
  rw [he]
  simpa using ((stonehamTruncation_error_tendsto_zero p).const_mul (u : ℝ)).add
    ((stonehamTruncation_error_tendsto_zero q).const_mul (v : ℝ))

end StonehamNormality
