import StonehamNormality.GeneralSeries
import StonehamNormality.GeneralArithmetic

/-! Identification of sparse-index truncations with power-index truncations. -/

noncomputable section
open scoped BigOperators Classical

namespace StonehamNormality

theorem radixStonehamTruncation_eq_powerTruncation (b c n K : ℕ)
    (hc : 2 ≤ c) (hcn : c ^ K ≤ n) (hnc : n < c ^ (K + 1)) :
    radixStonehamTruncation b c n = powerTruncation b c n K := by
  have him : (Finset.Icc 1 K).image (fun k => c ^ k) =
      (Finset.range (n + 1)).filter (IsStonehamIndex c) := by
    ext m
    constructor
    · intro hm
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.mp hk
      have hkn : c ^ k ≤ n := (pow_le_pow_right₀ (by omega : 1 ≤ c) hkK).trans hcn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), k, hk1, rfl⟩
    · intro hm
      obtain ⟨hmn, k, hk1, rfl⟩ := Finset.mem_filter.mp hm
      have hkn : c ^ k ≤ n := by have := Finset.mem_range.mp hmn; omega
      have hkK : k ≤ K := by
        by_contra h
        have hp := pow_le_pow_right₀ (by omega : 1 ≤ c) (show K + 1 ≤ k by omega)
        omega
      exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk1, hkK⟩, rfl⟩
  unfold radixStonehamTruncation powerTruncation
  rw [← him, Finset.sum_image]
  · simp only [Nat.cast_pow]
  · intro i hi j hj hij
    exact Nat.pow_right_injective hc hij

theorem radixStonehamTruncation_eq_powerTruncation_log (b c n : ℕ)
    (hc : 2 ≤ c) (hn : 0 < n) :
    radixStonehamTruncation b c n = powerTruncation b c n (Nat.log c n) :=
  radixStonehamTruncation_eq_powerTruncation b c n (Nat.log c n) hc
    (Nat.pow_log_le_self c hn.ne') (Nat.lt_pow_succ_log_self (by omega) n)

theorem radixStoneham_rat_combination_add_of_no_new_terms
    (b c d : ℕ) (u v : ℚ) (n t : ℕ)
    (hnew : ∀ m : ℕ, IsStonehamIndex c m ∨ IsStonehamIndex d m →
      m ≤ n + t → m ≤ n) :
    u * radixStonehamTruncation b c (n + t) + v * radixStonehamTruncation b d (n + t) =
      (b : ℚ) ^ t * (u * radixStonehamTruncation b c n + v * radixStonehamTruncation b d n) := by
  rw [radixStonehamTruncation_add_of_no_new_terms b c n t
      (fun m hm hmn => hnew m (Or.inl hm) hmn),
    radixStonehamTruncation_add_of_no_new_terms b d n t
      (fun m hm hmn => hnew m (Or.inr hm) hmn)]
  ring

end StonehamNormality
