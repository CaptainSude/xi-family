import StonehamNormality.XiAnalyticDenominatorTransfer

/-! Passing from dyadic exceptional-set estimates to natural density zero. -/

noncomputable section
open Filter
open scoped BigOperators Topology Classical

namespace StonehamNormality

theorem xi_prefix_card_bound_of_dyadic_bad_bound
    (bad : ℕ → Prop) (N₀ : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hlocal : ∀ N, N₀ ≤ N →
      (((Finset.Ico N (2 * N)).filter bad).card : ℝ) ≤ ε * N) :
    ∀ N, (((Finset.range N).filter bad).card : ℝ) ≤
      (2 * N₀ + 2 : ℕ) + 2 * ε * N := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hsmall : N < 2 * N₀ + 2
    · have hcard : (((Finset.range N).filter bad).card : ℝ) ≤ N := by
        exact_mod_cast (Finset.card_filter_le (Finset.range N) bad).trans_eq
          (Finset.card_range N)
      have hn : (N : ℝ) ≤ (2 * N₀ + 2 : ℕ) := by exact_mod_cast hsmall.le
      exact hcard.trans (hn.trans (le_add_of_nonneg_right (by positivity)))
    · let C := (N + 1) / 2
      have hNC : 2 ≤ N := by omega
      have hC : C < N := by dsimp [C]; omega
      have hC₀ : N₀ ≤ C := by dsimp [C]; omega
      have hN2C : N ≤ 2 * C := by dsimp [C]; omega
      have h3C : 3 * C ≤ 2 * N := by dsimp [C]; omega
      have hsub : (Finset.range N).filter bad ⊆
          ((Finset.range C).filter bad) ∪ ((Finset.Ico C (2 * C)).filter bad) := by
        intro n hn
        obtain ⟨hnN, hnb⟩ := Finset.mem_filter.mp hn
        have hnl := Finset.mem_range.mp hnN
        by_cases hnC : n < C
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnC, hnb⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hnb⟩)
      have hcard : (((Finset.range N).filter bad).card : ℝ) ≤
          (((Finset.range C).filter bad).card : ℝ) +
          (((Finset.Ico C (2 * C)).filter bad).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hp := ih C hC
      have hd := hlocal C hC₀
      have h3Cr : 3 * (C : ℝ) ≤ 2 * N := by exact_mod_cast h3C
      have hm := mul_le_mul_of_nonneg_left h3Cr hε
      nlinarith

/-- A set negligible in every dyadic annulus has natural density zero. -/
theorem xi_density_zero_of_dyadic_density_zero
    (bad : ℕ → Prop)
    (hdyadic : Tendsto (fun N : ℕ =>
      (((Finset.Ico N (2 * N)).filter bad).card : ℝ) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter bad).card : ℝ) / N) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    exact Eventually.of_forall (fun N => lt_of_lt_of_le hr (by positivity))
  · intro ε hε
    have hsmall : ∀ᶠ N : ℕ in atTop,
        (((Finset.Ico N (2 * N)).filter bad).card : ℝ) / N < ε / 4 :=
      hdyadic.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 4))
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
      (hsmall.and (eventually_ge_atTop 1))
    have hlocal : ∀ N, N₀ ≤ N →
        (((Finset.Ico N (2 * N)).filter bad).card : ℝ) ≤ (ε / 4) * N := by
      intro N hN
      obtain ⟨hs, hpos⟩ := hN₀ N hN
      have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      exact ((div_lt_iff₀ hNR).mp hs).le
    have hprefix := xi_prefix_card_bound_of_dyadic_bad_bound bad N₀ (ε / 4)
      (by positivity) hlocal
    have hlim : Tendsto (fun N : ℕ => ((2 * N₀ + 2 : ℕ) : ℝ) / N)
        atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
          (((2 * N₀ + 2 : ℕ) : ℝ))
    filter_upwards [hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2)),
      eventually_ge_atTop 1] with N hN hpos
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hbound := (div_le_div_iff_of_pos_right hNR).mpr (hprefix N)
    have heq : (((2 * N₀ + 2 : ℕ) : ℝ) + 2 * (ε / 4) * N) / N =
        ((2 * N₀ + 2 : ℕ) : ℝ) / N + ε / 2 := by field_simp; ring
    rw [heq] at hbound
    linarith

end StonehamNormality
