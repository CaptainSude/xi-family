import StonehamNormality.XiAnalyticGlobal
import StonehamNormality.GeneralRadixTransfer
import StonehamNormality.GeneralCharacterPhase

/-!
# Sparse rational orbits with a density-zero exceptional set

A cut-free block is charged for its bad initial positions, then one orbit
bound starting at its first good position. The exceptional set need not itself
be an interval or be invariant under the recurrence.
-/

noncomputable section
open Filter
open scoped BigOperators Topology Classical

namespace StonehamNormality

def xiBadBudget (good : ℕ → Prop) (n : ℕ) : ℝ := if good n then 0 else 1

/-- A block bound with an additive position-by-position error budget. -/
theorem xi_norm_sum_range_le_of_budget_block_bound
    (f : ℕ → ℂ) (w : ℕ → ℝ) (cuts : Finset ℕ) (M : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hblock : ∀ a b : ℕ, a ≤ b → b ≤ M →
      (∀ n ∈ Finset.Ioo a b, n ∉ cuts) →
      ‖∑ n ∈ Finset.Ico a b, f n‖ ≤ (∑ n ∈ Finset.Ico a b, w n) + K) :
    ‖∑ n ∈ Finset.range M, f n‖ ≤ (∑ n ∈ Finset.range M, w n) +
      (((cuts.filter (fun n => 0 < n ∧ n < M)).card : ℝ) + 1) * K := by
  have haux : ∀ b : ℕ, b ≤ M →
      ‖∑ n ∈ Finset.Ico 0 b, f n‖ ≤ (∑ n ∈ Finset.Ico 0 b, w n) +
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
          have hna := Finset.mem_Ioo.mp hn
          have hns : n ∈ s := Finset.mem_filter.mpr
            ⟨hnc, lt_trans ha_data.2.1 hna.1, hna.2⟩
          have hnle : n ≤ a := Finset.le_max' s n hns
          omega
        have hprefix := ih a ha_data.2.2 (ha_data.2.2.le.trans hbM)
        have hfinal := hblock a b ha_data.2.2.le hbM hlast
        let sA := cuts.filter (fun n => 0 < n ∧ n < a)
        have ha_not : a ∉ sA := by simp [sA]
        have hsub : insert a sA ⊆ s := by
          intro n hn
          rcases Finset.mem_insert.mp hn with rfl | hn
          · exact ha_mem
          · rcases Finset.mem_filter.mp hn with ⟨hnc, hn0, hna⟩
            exact Finset.mem_filter.mpr ⟨hnc, hn0, hna.trans ha_data.2.2⟩
        have hcard : sA.card + 1 ≤ s.card := by
          simpa [Finset.card_insert_of_notMem ha_not] using Finset.card_le_card hsub
        have hcardR : (sA.card : ℝ) + 1 ≤ s.card := by exact_mod_cast hcard
        rw [← Finset.sum_Ico_consecutive f (Nat.zero_le a) ha_data.2.2.le,
          ← Finset.sum_Ico_consecutive w (Nat.zero_le a) ha_data.2.2.le]
        apply (norm_add_le _ _).trans
        have hsum := add_le_add hprefix hfinal
        have hmul := mul_le_mul_of_nonneg_right hcardR hK
        dsimp [sA, s] at *
        linarith
      · have hs : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        have hnone : ∀ n ∈ Finset.Ioo 0 b, n ∉ cuts := by
          intro n hn hnc
          have hns : n ∈ s := Finset.mem_filter.mpr ⟨hnc, Finset.mem_Ioo.mp hn⟩
          simpa [hs] using hns
        have hbound := hblock 0 b (Nat.zero_le b) hbM hnone
        change ‖∑ n ∈ Finset.Ico 0 b, f n‖ ≤ (∑ n ∈ Finset.Ico 0 b, w n) +
          ((s.card : ℝ) + 1) * K
        simpa [hs] using hbound
  simpa using haux M le_rfl

/-- Discard only the positions preceding the first good point of an interval.
Their cost is at most the number of bad points in that interval. -/
theorem xi_block_bound_from_first_good
    (f : ℕ → ℂ) (good : ℕ → Prop) (a z : ℕ) (K : ℝ)
    (haz : a ≤ z) (hK : 0 ≤ K) (hf : ∀ n, ‖f n‖ ≤ 1)
    (htail : ∀ c ∈ Finset.Ico a z, good c →
      ‖∑ n ∈ Finset.Ico c z, f n‖ ≤ K) :
    ‖∑ n ∈ Finset.Ico a z, f n‖ ≤
      (∑ n ∈ Finset.Ico a z, xiBadBudget good n) + K := by
  let s := (Finset.Ico a z).filter good
  by_cases hs : s.Nonempty
  · let c := s.min' hs
    have hcm : c ∈ s := Finset.min'_mem s hs
    have hcz : c ∈ Finset.Ico a z := (Finset.mem_filter.mp hcm).1
    have hcg : good c := (Finset.mem_filter.mp hcm).2
    have hcl := Finset.mem_Ico.mp hcz
    have hbad : ∀ n ∈ Finset.Ico a c, ¬ good n := by
      intro n hn hng
      have hnl := Finset.mem_Ico.mp hn
      have hns : n ∈ s := Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨hnl.1, hnl.2.trans hcl.2⟩, hng⟩
      have hcn : c ≤ n := Finset.min'_le s n hns
      omega
    have hprefix : ‖∑ n ∈ Finset.Ico a c, f n‖ ≤
        ∑ n ∈ Finset.Ico a c, xiBadBudget good n := by
      apply norm_sum_le_of_le
      intro n hn
      simpa [xiBadBudget, hbad n hn] using hf n
    have hbudget : 0 ≤ ∑ n ∈ Finset.Ico c z, xiBadBudget good n := by
      apply Finset.sum_nonneg
      intro n hn
      unfold xiBadBudget
      split <;> norm_num
    rw [← Finset.sum_Ico_consecutive f hcl.1 hcl.2.le,
      ← Finset.sum_Ico_consecutive (xiBadBudget good)
        hcl.1 hcl.2.le]
    exact (norm_add_le _ _).trans
      ((add_le_add hprefix (htail c hcz hcg)).trans (by linarith))
  · have hbad : ∀ n ∈ Finset.Ico a z, ¬ good n := by
      intro n hn hng
      exact hs ⟨n, Finset.mem_filter.mpr ⟨hn, hng⟩⟩
    have hbound : ‖∑ n ∈ Finset.Ico a z, f n‖ ≤
        ∑ n ∈ Finset.Ico a z, xiBadBudget good n := by
      apply norm_sum_le_of_le
      intro n hn
      simpa [xiBadBudget, hbad n hn] using hf n
    linarith

/-- Sparse rational approximation prefixes, allowing arbitrary bad positions.
Only a good starting point is needed for each surviving orbit interval. -/
theorem xi_norm_sum_rational_prefix_with_bad
    (R : ℕ → ℚ) (S bad : ℕ → Prop) (F : ℚ → ℂ)
    (b M : ℕ) (K : ℝ) (hK : 0 ≤ K) (hF : ∀ q, ‖F q‖ ≤ 1)
    (hrec : ∀ n t : ℕ,
      (∀ m : ℕ, S m → m ≤ n + t → m ≤ n) →
      R (n + t) = (b : ℚ) ^ t * R n)
    (horbit : ∀ n t : ℕ, ¬ bad n → n + t ≤ M →
      ‖∑ i ∈ Finset.range t, F ((b : ℚ) ^ i * R n)‖ ≤ K) :
    ‖∑ n ∈ Finset.range M, F (R n)‖ ≤
      (((Finset.range M).filter bad).card : ℝ) +
      ((((Finset.range M).filter S).card : ℝ) + 1) * K := by
  let cuts := (Finset.range M).filter S
  have hblock : ∀ a z : ℕ, a ≤ z → z ≤ M →
      (∀ n ∈ Finset.Ioo a z, n ∉ cuts) →
      ‖∑ n ∈ Finset.Ico a z, F (R n)‖ ≤
        (∑ n ∈ Finset.Ico a z, xiBadBudget (fun n => ¬ bad n) n) + K := by
    intro a z haz hzM hcuts
    have htail : ∀ c ∈ Finset.Ico a z, ¬ bad c →
        ‖∑ n ∈ Finset.Ico c z, F (R n)‖ ≤ K := by
      intro c hcz hcg
      have hcl := Finset.mem_Ico.mp hcz
      have heq : (∑ n ∈ Finset.Ico c z, F (R n)) =
          ∑ i ∈ Finset.range (z - c), F ((b : ℚ) ^ i * R c) := by
        rw [Finset.sum_Ico_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        rw [hrec c i]
        intro m hm hmi
        by_contra hmc
        have hmz : m < z := by omega
        have hcut : m ∈ cuts := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (hmz.trans_le hzM), hm⟩
        exact hcuts m (Finset.mem_Ioo.mpr ⟨by omega, hmz⟩) hcut
      rw [heq]
      exact horbit c (z - c) hcg (by omega)
    exact xi_block_bound_from_first_good
      (fun n => F (R n)) (fun n => ¬ bad n) a z K haz hK
      (fun n => hF (R n)) htail
  have hglobal := xi_norm_sum_range_le_of_budget_block_bound
    (fun n => F (R n)) (xiBadBudget (fun n => ¬ bad n))
    cuts M K hK hblock
  have hbudget : (∑ n ∈ Finset.range M, xiBadBudget (fun n => ¬ bad n) n) =
      (((Finset.range M).filter bad).card : ℝ) := by
    have hterm (n : ℕ) : xiBadBudget (fun n => ¬ bad n) n =
        if bad n then (1 : ℝ) else 0 := by
      by_cases hn : bad n <;> simp [xiBadBudget, hn]
    simp_rw [hterm]
    rw [← Finset.sum_filter]
    simp
  rw [hbudget] at hglobal
  have hcard : ((cuts.filter (fun n => 0 < n ∧ n < M)).card : ℝ) ≤ cuts.card := by
    exact_mod_cast Finset.card_filter_le cuts (fun n => 0 < n ∧ n < M)
  apply hglobal.trans
  simpa only [cuts, add_comm] using (add_le_add_left
    (mul_le_mul_of_nonneg_right (add_le_add_right hcard 1) hK)
      ((((Finset.range M).filter bad).card : ℝ)))

/-- A complete Fourier transfer criterion with sparse cuts and exceptional
starting points of vanishing density. The number of cuts need not be linear
in the logarithmic scale. -/
theorem xi_radix_fourier_of_sparse_orbits_with_bad
    (b : ℕ) (x : ℝ) (R : ℕ → ℚ) (S : ℕ → Prop)
    (happrox : Tendsto (fun n => (b : ℝ) ^ n * x - (R n : ℝ)) atTop (𝓝 0))
    (hrec : ∀ n t : ℕ,
      (∀ m : ℕ, S m → m ≤ n + t → m ≤ n) →
      R (n + t) = (b : ℚ) ^ t * R n)
    (hcontrol : ∀ h : ℤ, h ≠ 0 →
      ∃ (Q : ℕ) (bad : ℕ → ℕ → Prop) (K : ℕ → ℝ),
        1 < Q ∧ (∀ B, 0 ≤ K B) ∧
        Tendsto (fun B : ℕ =>
          (((Finset.range (Q ^ (B + 1))).filter (bad (B + 1))).card : ℝ) /
            (Q : ℝ) ^ B) atTop (𝓝 0) ∧
        Tendsto (fun B : ℕ =>
          (((((Finset.range (Q ^ (B + 1))).filter S).card : ℝ) + 1) * K (B + 1)) /
            (Q : ℝ) ^ B) atTop (𝓝 0) ∧
        ∀ᶠ B in atTop, ∀ n t : ℕ, ¬ bad B n → n + t ≤ Q ^ B →
          ‖∑ i ∈ Finset.range t, fourier (T := 1) h
            ((((b : ℚ) ^ i * R n : ℚ) : ℝ) : UnitAddCircle)‖ ≤ K B) :
    RadixFourierCancellation b x := by
  intro h hh
  apply fourier_average_tendsto_of_approximation h happrox
  obtain ⟨Q, bad, K, hQ, hK, hbad, hcuts, horbit⟩ := hcontrol h hh
  let E : ℕ → ℝ := fun B =>
    ((((Finset.range (Q ^ B)).filter (bad B)).card : ℝ)) +
      (((((Finset.range (Q ^ B)).filter S).card : ℝ) + 1) * K B)
  have hdecay : Tendsto (fun B : ℕ => E (B + 1) / (Q : ℝ) ^ B)
      atTop (𝓝 0) := by
    simpa only [E, add_div, add_zero] using hbad.add hcuts
  apply average_tendsto_zero_of_eventual_scale_prefix_bound
    (fun n => fourier (T := 1) h ((R n : ℝ) : UnitAddCircle)) Q E hQ hdecay
  filter_upwards [horbit] with B ho
  intro M hM
  have hprefix := xi_norm_sum_rational_prefix_with_bad R S (bad B)
    (fun q => fourier (T := 1) h ((q : ℝ) : UnitAddCircle)) b M (K B)
    (hK B) (fun q => (fourier_norm_one h _).le) hrec
    (fun n t hn hnt => ho n t hn (hnt.trans hM.le))
  have hcard (P : ℕ → Prop) : (((Finset.range M).filter P).card : ℝ) ≤
      (((Finset.range (Q ^ B)).filter P).card : ℝ) := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnM, hnP⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hnM).trans_le hM.le), hnP⟩
  exact hprefix.trans (add_le_add (hcard (bad B))
    (mul_le_mul_of_nonneg_right (by linarith [hcard S]) (hK B)))

end StonehamNormality
