import StonehamNormality.DependentSumValuation
import Mathlib.Data.Finset.Max

/-! Finite cancellation lemmas for the Xi denominator-escape argument. -/

open scoped BigOperators Classical

namespace XiFamily

/-- Zero belongs to every valuation level. This avoids treating its conventional
`padicValRat` value, zero, as its actual valuation. -/
def ValuationAtLeast (p : ℕ) (v : ℤ) (q : ℚ) : Prop :=
  q = 0 ∨ v ≤ padicValRat p q

theorem valuationAtLeast_zero (p : ℕ) (v : ℤ) : ValuationAtLeast p v 0 :=
  Or.inl rfl

theorem valuationAtLeast_neg {p : ℕ} {v : ℤ} {q : ℚ}
    (h : ValuationAtLeast p v q) : ValuationAtLeast p v (-q) := by
  rcases h with rfl | h
  · exact Or.inl neg_zero
  · exact Or.inr (by simpa only [padicValRat.neg] using h)

theorem valuationAtLeast_add {p : ℕ} [Fact p.Prime] {v : ℤ} {x y : ℚ}
    (hx : ValuationAtLeast p v x) (hy : ValuationAtLeast p v y) :
    ValuationAtLeast p v (x + y) := by
  rcases hx with rfl | hx
  · simpa using hy
  rcases hy with rfl | hy
  · rw [add_zero]
    exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  · exact Or.inr ((le_min hx hy).trans (padicValRat.min_le_padicValRat_add hxy))

theorem valuationAtLeast_sub {p : ℕ} [Fact p.Prime] {v : ℤ} {x y : ℚ}
    (hx : ValuationAtLeast p v x) (hy : ValuationAtLeast p v y) :
    ValuationAtLeast p v (x - y) := by
  simpa only [sub_eq_add_neg] using valuationAtLeast_add hx (valuationAtLeast_neg hy)

theorem sum_ne_zero_of_unique_min {ι : Type*} {p : ℕ} [Fact p.Prime]
    (s : Finset ι) (f : ι → ℚ) (j : ι) (hj : j ∈ s) (hfj : f j ≠ 0)
    (hmin : ∀ i ∈ s, i ≠ j → f i ≠ 0 →
      padicValRat p (f j) < padicValRat p (f i)) :
    ∑ i ∈ s, f i ≠ 0 := by
  classical
  rw [← Finset.add_sum_erase s f hj]
  by_cases hs : ∑ i ∈ s.erase j, f i = 0
  · simpa [hs] using hfj
  have hv : padicValRat p (f j) < padicValRat p (∑ i ∈ s.erase j, f i) := by
    have h := StonehamNormality.padicValRat_sum_lower_bound (p := p) (s.erase j) f
      (padicValRat p (f j) + 1) (by
        intro i hi hfi
        have hi' := Finset.mem_erase.mp hi
        exact hmin i hi'.2 hi'.1 hfi) hs
    omega
  intro hz
  have he : f j = -(∑ i ∈ s.erase j, f i) := (eq_neg_iff_add_eq_zero).mpr hz
  have heval := congrArg (padicValRat p) he
  rw [padicValRat.neg] at heval
  omega

/-- When nonzero term valuations are all different, a sum cannot hide a term
below a specified valuation level. -/
theorem term_valuationAtLeast_of_sum {ι : Type*} {p : ℕ} [Fact p.Prime]
    (s : Finset ι) (f : ι → ℚ) (v : ℤ)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → f j ≠ 0 →
      padicValRat p (f i) = padicValRat p (f j) → i = j)
    (hsum : ValuationAtLeast p v (∑ i ∈ s, f i)) :
    ∀ i ∈ s, ValuationAtLeast p v (f i) := by
  classical
  intro i hi
  by_cases hfi : f i = 0
  · exact Or.inl hfi
  let t := s.filter (fun j => f j ≠ 0)
  have hit : i ∈ t := Finset.mem_filter.mpr ⟨hi, hfi⟩
  obtain ⟨j, hj, hmin⟩ := t.exists_min_image (fun j => padicValRat p (f j)) ⟨i, hit⟩
  have hjs : j ∈ s := (Finset.mem_filter.mp hj).1
  have hfj : f j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hstrict : ∀ k ∈ s, k ≠ j → f k ≠ 0 →
      padicValRat p (f j) < padicValRat p (f k) := by
    intro k hk hkj hfk
    have hkmin := hmin k (Finset.mem_filter.mpr ⟨hk, hfk⟩)
    exact lt_of_le_of_ne hkmin (fun he => hkj (hinj k hk j hjs hfk hfj he.symm))
  have hn := sum_ne_zero_of_unique_min s f j hjs hfj hstrict
  have he := StonehamNormality.padicValRat_sum_eq_unique_min s f j hjs hfj hstrict
  have hv : v ≤ padicValRat p (f j) := by
    rcases hsum with hz | hv
    · exact False.elim (hn hz)
    · simpa only [he] using hv
  exact Or.inr (hv.trans (hmin i hit))

/-- Two prefixes with bounded denominator depth cannot straddle a deeper
insertion when the intervening nonzero term valuations are distinct. -/
theorem no_deep_insertion_between_prefixes {p : ℕ} [Fact p.Prime]
    (f : ℕ → ℚ) (v : ℤ) (x y : ℕ) (hxy : x ≤ y)
    (hinj : ∀ i ∈ Finset.Ico x y, ∀ j ∈ Finset.Ico x y,
      f i ≠ 0 → f j ≠ 0 →
      padicValRat p (f i) = padicValRat p (f j) → i = j)
    (hx : ValuationAtLeast p v (∑ i ∈ Finset.range x, f i))
    (hy : ValuationAtLeast p v (∑ i ∈ Finset.range y, f i)) :
    ∀ i ∈ Finset.Ico x y, ValuationAtLeast p v (f i) := by
  apply term_valuationAtLeast_of_sum (Finset.Ico x y) f v hinj
  rw [Finset.sum_Ico_eq_sub f hxy]
  exact valuationAtLeast_sub hy hx

/-- Local separation and a bound on the gaps between deep insertions bound the
number of shallow prefixes. The bound is independent of the whole block length. -/
theorem shallow_prefix_card_le {p : ℕ} [Fact p.Prime]
    (f : ℕ → ℚ) (v : ℤ) (N U H : ℕ)
    (hinj : ∀ i ∈ Finset.Ico N U, ∀ j ∈ Finset.Ico N U,
      f i ≠ 0 → f j ≠ 0 →
      padicValRat p (f i) = padicValRat p (f j) → i = j)
    (hdeep : ∀ x, N ≤ x → x + H ≤ U →
      ∃ m ∈ Finset.Ico x (x + H), ¬ ValuationAtLeast p v (f m)) :
    ((Finset.Icc N U).filter (fun n =>
      ValuationAtLeast p v (∑ i ∈ Finset.range n, f i))).card ≤ H := by
  classical
  let s := (Finset.Icc N U).filter (fun n =>
    ValuationAtLeast p v (∑ i ∈ Finset.range n, f i))
  change s.card ≤ H
  by_cases hs : s.Nonempty
  · let j := s.min' hs
    have hj := Finset.min'_mem s hs
    have hj' := Finset.mem_filter.mp hj
    have hjN := (Finset.mem_Icc.mp hj'.1).1
    have hsub : s ⊆ Finset.Ico j (j + H) := by
      intro y hy
      have hy' := Finset.mem_filter.mp hy
      have hyU := (Finset.mem_Icc.mp hy'.1).2
      have hjy : j ≤ y := Finset.min'_le s y hy
      apply Finset.mem_Ico.mpr
      refine ⟨hjy, ?_⟩
      by_contra hylow
      have hH : j + H ≤ y := by omega
      obtain ⟨m, hm, hmv⟩ := hdeep j hjN (hH.trans hyU)
      have hlocal : ∀ i ∈ Finset.Ico j y, ∀ k ∈ Finset.Ico j y,
          f i ≠ 0 → f k ≠ 0 →
          padicValRat p (f i) = padicValRat p (f k) → i = k := by
        intro i hi k hk hfi hfk he
        have hi' := Finset.mem_Ico.mp hi
        have hk' := Finset.mem_Ico.mp hk
        exact hinj i (Finset.mem_Ico.mpr ⟨hjN.trans hi'.1, hi'.2.trans_le hyU⟩)
          k (Finset.mem_Ico.mpr ⟨hjN.trans hk'.1, hk'.2.trans_le hyU⟩) hfi hfk he
      have hterms := no_deep_insertion_between_prefixes f v j y hjy hlocal hj'.2 hy'.2
      have hm' := Finset.mem_Ico.mp hm
      exact hmv (hterms m (Finset.mem_Ico.mpr ⟨hm'.1, hm'.2.trans_le hH⟩))
    have hcard := Finset.card_le_card hsub
    simpa using hcard
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

end XiFamily
