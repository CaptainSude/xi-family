import StonehamNormality.GeneralSeriesBridge
import StonehamNormality.GeneralRadixTransfer
import StonehamNormality.StonehamTransfer

/-!
# Support counts and a complete analytic interface for arbitrary parameters

The union of two power supports has a linear number of events below a geometric
scale. Consequently subscale bounds for each uninterrupted rational orbit imply
normality of the actual Stoneham combination in the requested radix.
-/

noncomputable section
open Filter
open scoped BigOperators Topology Classical

namespace StonehamNormality

def IsPairedStonehamIndex (c d m : ℕ) : Prop :=
  IsStonehamIndex c m ∨ IsStonehamIndex d m

theorem stoneham_support_count_geometric_scale (c Q B : ℕ) (hc : 2 ≤ c) :
    ((Finset.range (Q ^ B)).filter (IsStonehamIndex c)).card ≤ Q * B := by
  have hQ : Q ≤ 2 ^ Q := by
    induction Q with
    | zero => norm_num
    | succ Q ih =>
      rw [pow_succ]
      have hh : 1 ≤ (2 : ℕ) ^ Q := one_le_pow₀ (by norm_num)
      omega
  have hpow : Q ^ B ≤ 2 ^ (Q * B) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hQ B
  have hsub : (Finset.range (Q ^ B)).filter (IsStonehamIndex c) ⊆
      (Finset.range (2 ^ (Q * B))).filter (IsStonehamIndex c) := by
    intro n hn
    obtain ⟨hnM, hs⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hnM).trans_le hpow), hs⟩
  exact (Finset.card_le_card hsub).trans (stoneham_support_count_lt_two_pow c (Q * B) hc)

theorem pairedStoneham_support_count_geometric_scale (c d Q B : ℕ)
    (hc : 2 ≤ c) (hd : 2 ≤ d) :
    ((Finset.range (Q ^ B)).filter (IsPairedStonehamIndex c d)).card ≤ 2 * Q * B := by
  have heq : (Finset.range (Q ^ B)).filter (IsPairedStonehamIndex c d) =
      ((Finset.range (Q ^ B)).filter (IsStonehamIndex c)) ∪
      ((Finset.range (Q ^ B)).filter (IsStonehamIndex d)) := by
    ext m
    simp only [Finset.mem_filter, IsPairedStonehamIndex, Finset.mem_union]
    tauto
  rw [heq]
  exact (Finset.card_union_le _ _).trans (by
    have h1 := stoneham_support_count_geometric_scale c Q B hc
    have h2 := stoneham_support_count_geometric_scale d Q B hd
    calc
      _ ≤ Q * B + Q * B := Nat.add_le_add h1 h2
      _ = 2 * Q * B := by ring)

theorem pairedStoneham_support_count_real_scale (c d Q B : ℕ)
    (hc : 2 ≤ c) (hd : 2 ≤ d) :
    (((Finset.range (Q ^ B)).filter (IsPairedStonehamIndex c d)).card : ℝ) ≤
      (2 * (Q : ℝ)) * ((B : ℝ) + 1) := by
  have h : (((Finset.range (Q ^ B)).filter (IsPairedStonehamIndex c d)).card : ℝ) ≤
      2 * (Q : ℝ) * (B : ℝ) := by
    exact_mod_cast pairedStoneham_support_count_geometric_scale c d Q B hc hd
  nlinarith [Nat.cast_nonneg (α := ℝ) Q]

/-- The only remaining hypothesis is a subscale bound for rational orbit sums.
Support counts, approximation errors, and all-prefix limits are all discharged. -/
theorem stoneham_pair_radix_fourier_of_orbit_bounds
    (b c d : ℕ) (u v : ℚ) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (Q U V : ℕ) (hQ : 1 < Q) (hU : U < Q) (hV : V < Q)
    (horbit : ∀ h : ℤ, h ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ (B : ℕ) in atTop, ∀ n t : ℕ, U ^ B ≤ n → n + t ≤ Q ^ B →
        ‖∑ i ∈ Finset.range t, fourier (T := 1) h
          ((((b : ℚ) ^ i *
            (u * radixStonehamTruncation b c n + v * radixStonehamTruncation b d n) : ℚ) :
              ℝ) : UnitAddCircle)‖ ≤ C * (V : ℝ) ^ B) :
    RadixFourierCancellation b
      ((u : ℝ) * stonehamConstant b c + (v : ℝ) * stonehamConstant b d) := by
  apply radix_fourier_of_linear_event_geometric_orbits b
    ((u : ℝ) * stonehamConstant b c + (v : ℝ) * stonehamConstant b d)
    (fun n => u * radixStonehamTruncation b c n + v * radixStonehamTruncation b d n)
    (IsPairedStonehamIndex c d) Q U V hQ hU hV (2 * (Q : ℝ))
  · exact radixStoneham_rat_combination_error_tendsto_zero b c d u v hb hc hd
  · intro n t hnew
    exact radixStoneham_rat_combination_add_of_no_new_terms b c d u v n t hnew
  · exact Eventually.of_forall (fun B => pairedStoneham_support_count_real_scale c d Q B hc hd)
  · exact horbit

theorem stoneham_pair_normalInBase_of_orbit_bounds
    (b c d : ℕ) (u v : ℚ) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (Q U V : ℕ) (hQ : 1 < Q) (hU : U < Q) (hV : V < Q)
    (horbit : ∀ h : ℤ, h ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ (B : ℕ) in atTop, ∀ n t : ℕ, U ^ B ≤ n → n + t ≤ Q ^ B →
        ‖∑ i ∈ Finset.range t, fourier (T := 1) h
          ((((b : ℚ) ^ i *
            (u * radixStonehamTruncation b c n + v * radixStonehamTruncation b d n) : ℚ) :
              ℝ) : UnitAddCircle)‖ ≤ C * (V : ℝ) ^ B) :
    NormalInBase b ((u : ℝ) * stonehamConstant b c + (v : ℝ) * stonehamConstant b d) :=
  (stoneham_pair_radix_fourier_of_orbit_bounds b c d u v hb hc hd Q U V hQ hU hV
    horbit).normalInBase hb

end StonehamNormality
