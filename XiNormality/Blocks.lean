import XiNormality.Imports

noncomputable section

open scoped BigOperators Classical

namespace XiNormality

/-- A bound on each interval between cuts gives a bound on the whole sum.
Only the number of cuts matters; no sorted-list representation is needed. -/
theorem norm_sum_range_le_of_block_bound
    (f : ℕ → ℂ) (cuts : Finset ℕ) (M : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hblock : ∀ a b : ℕ, a ≤ b → b ≤ M →
      (∀ n ∈ Finset.Ioo a b, n ∉ cuts) →
      ‖∑ n ∈ Finset.Ico a b, f n‖ ≤ K) :
    ‖∑ n ∈ Finset.range M, f n‖ ≤
      (((cuts.filter (fun n => 0 < n ∧ n < M)).card : ℝ) + 1) * K := by
  have haux : ∀ b : ℕ, b ≤ M →
      ‖∑ n ∈ Finset.Ico 0 b, f n‖ ≤
        (((cuts.filter (fun n => 0 < n ∧ n < b)).card : ℝ) + 1) * K := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro hbM
      let s := cuts.filter (fun n => 0 < n ∧ n < b)
      by_cases hne : s.Nonempty
      · let a := s.max' hne
        have ha_mem : a ∈ s := Finset.max'_mem s hne
        have ha_data : a ∈ cuts ∧ 0 < a ∧ a < b := by
          simpa only [s, Finset.mem_filter] using ha_mem
        have hlast : ∀ n ∈ Finset.Ioo a b, n ∉ cuts := by
          intro n hn hnc
          have hna : a < n ∧ n < b := Finset.mem_Ioo.mp hn
          have hns : n ∈ s := by
            simp only [s, Finset.mem_filter]
            exact ⟨hnc, lt_trans ha_data.2.1 hna.1, hna.2⟩
          have hnle : n ≤ a := Finset.le_max' s n hns
          omega
        have hprefix := ih a ha_data.2.2 (le_trans ha_data.2.2.le hbM)
        have hfinal := hblock a b ha_data.2.2.le hbM hlast
        let sA := cuts.filter (fun n => 0 < n ∧ n < a)
        have ha_not : a ∉ sA := by simp [sA]
        have hsub : insert a sA ⊆ s := by
          intro n hn
          rcases Finset.mem_insert.mp hn with rfl | hn
          · exact ha_mem
          · rcases Finset.mem_filter.mp hn with ⟨hnc, hn0, hna⟩
            exact Finset.mem_filter.mpr ⟨hnc, hn0, lt_trans hna ha_data.2.2⟩
        have hcard : sA.card + 1 ≤ s.card := by
          simpa [Finset.card_insert_of_notMem ha_not] using Finset.card_le_card hsub
        have hcardR : (sA.card : ℝ) + 1 ≤ s.card := by exact_mod_cast hcard
        rw [← Finset.sum_Ico_consecutive f (Nat.zero_le a) ha_data.2.2.le]
        calc
          ‖(∑ n ∈ Finset.Ico 0 a, f n) + ∑ n ∈ Finset.Ico a b, f n‖
              ≤ ‖∑ n ∈ Finset.Ico 0 a, f n‖ + ‖∑ n ∈ Finset.Ico a b, f n‖ := norm_add_le _ _
          _ ≤ ((sA.card : ℝ) + 1) * K + K := add_le_add hprefix hfinal
          _ ≤ ((s.card : ℝ) + 1) * K := by nlinarith
      · have hs : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        have hnone : ∀ n ∈ Finset.Ioo 0 b, n ∉ cuts := by
          intro n hn hnc
          have hns : n ∈ s := Finset.mem_filter.mpr ⟨hnc, Finset.mem_Ioo.mp hn⟩
          simpa [hs] using hns
        have hbound := hblock 0 b (Nat.zero_le b) hbM hnone
        change ‖∑ n ∈ Finset.Ico 0 b, f n‖ ≤ ((s.card : ℝ) + 1) * K
        simpa [hs] using hbound
  simpa using haux M le_rfl

end XiNormality
