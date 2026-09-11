import XiCombinationDepth
import XiSlopeDominance

/-! Unconditional logarithmic denominator escape for nontrivial combinations. -/

noncomputable section
open Filter
open scoped BigOperators Classical Topology

namespace XiFamily

theorem exists_combination_logarithmic_depth {b a : ℕ}
    (S : Finset ℕ) (q : ℕ → ℚ) (q₀ : ℚ)
    (ha : 2 ≤ a) (hb : 0 < b) (hSne : S.Nonempty)
    (hS : ∀ c ∈ S, 2 ≤ c) (hcop : ∀ c ∈ S, c.Coprime (a * b))
    (hq : ∀ c ∈ S, q c ≠ 0) :
    ∃ (p d : ℕ) (C : ℤ), p.Prime ∧ 2 ≤ d ∧ ¬ p ∣ b ∧
      Tendsto (fun N : ℕ =>
        (((Finset.range N).filter (combinationShallow p b a S q q₀ d C)).card : ℝ) / N)
        atTop (𝓝 0) := by
  obtain ⟨p, d, hp, hd, hpd, hpa, hpb, hmax⟩ :=
    exists_dominant_primitive_block S hSne hS hcop
  letI : Fact p.Prime := ⟨hp⟩
  have hdprop := primitiveBase_mem_properties S hS hcop hd
  have hd2 := hdprop.1.1
  have hactive : ∃ c ∈ parameterClass S d, q c ≠ 0 := by
    obtain ⟨c, hc, hcd⟩ := Finset.mem_image.mp hd
    exact ⟨c, Finset.mem_filter.mpr ⟨hc, hcd⟩, hq c hc⟩
  obtain ⟨r, _, hr⟩ := classWeight_nonzero S q d hS hactive
  obtain ⟨R, hR, hdom⟩ := finite_log_slope_eventual_dominance
    (S.image primitiveBase) hd2
    (fun e he => (primitiveBase_mem_properties S hS hcop he).1.1) hmax
  refine ⟨p, d, padicValRat p (classWeight S q d r), hp, hd2, hpb, ?_⟩
  apply combinationShallow_density_zero_of_dominance S q q₀ ha hb hS hcop hd hpa hpb
    (one_le_padicValNat_of_dvd (by omega : d ≠ 0) hpd) r hr hR
  filter_upwards [hdom (padicValRat p (classWeight S q d r))
    (fun _ => coefficientValuationFloor p S q)] with N hN
  intro e he hed
  exact (hN e he hed).le

def combinationTruncation (b a : ℕ) (S : Finset ℕ) (q : ℕ → ℚ) (q₀ : ℚ) (n : ℕ) : ℚ :=
  q₀ * (b : ℚ) ^ n + ∑ c ∈ S, q c * truncation b c a n

def combinationEvent (a : ℕ) (S : Finset ℕ) (m : ℕ) : Prop :=
  ∃ c ∈ S, IsIndex a c m

theorem combinationTruncation_eq_prefix_of_not_event {b a n : ℕ}
    (S : Finset ℕ) (q : ℕ → ℚ) (q₀ : ℚ) (hb : 2 ≤ b)
    (hnot : ¬ combinationEvent a S n) :
    combinationTruncation b a S q q₀ n = (b : ℚ) ^ n * combinationPrefix b a S q q₀ n := by
  have hnotc : ∀ c ∈ S, ¬ IsIndex a c n := by
    intro c hc hi
    exact hnot ⟨c, hc, hi⟩
  have hpref : ∀ c ∈ S, unshiftedPrefix b c a n =
      ∑ m ∈ Finset.range n, unshiftedTerm b c a m := by
    intro c hc
    rw [unshiftedPrefix, Finset.sum_range_succ,
      unshiftedTerm_eq_zero_of_not_index (hnotc c hc), add_zero]
  unfold combinationTruncation combinationPrefix
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro c hc
    rw [truncation_eq_pow_mul_unshiftedPrefix b c a n hb, hpref c hc]
    ring

theorem combinationTruncation_add_of_no_new_terms {b a : ℕ}
    (S : Finset ℕ) (q : ℕ → ℚ) (q₀ : ℚ) (n t : ℕ)
    (hnew : ∀ m, combinationEvent a S m → m ≤ n + t → m ≤ n) :
    combinationTruncation b a S q q₀ (n + t) =
      (b : ℚ) ^ t * combinationTruncation b a S q q₀ n := by
  unfold combinationTruncation
  rw [mul_add, Finset.mul_sum]
  congr 1
  · rw [pow_add]; ring
  · apply Finset.sum_congr rfl
    intro c hc
    rw [truncation_add_of_no_new_terms b c a n t
      (fun m hm hmn => hnew m ⟨c, hc, hm⟩ hmn)]
    ring

theorem combinationTruncation_depth_of_not_shallow_not_event {p b a d n : ℕ}
    [Fact p.Prime] (S : Finset ℕ) (q : ℕ → ℚ) (q₀ : ℚ) (C : ℤ)
    (hb : 2 ≤ b) (hpb : ¬ p ∣ b)
    (hshallow : ¬ combinationShallow p b a S q q₀ d C n)
    (hnot : ¬ combinationEvent a S n) :
    combinationTruncation b a S q q₀ n ≠ 0 ∧
      padicValRat p (combinationTruncation b a S q q₀ n) <
        C - ((Nat.log d (n / 2) / 2 : ℕ) : ℤ) := by
  have hpre : combinationPrefix b a S q q₀ n ≠ 0 :=
    fun h => hshallow (Or.inl h)
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  rw [combinationTruncation_eq_prefix_of_not_event S q q₀ hb hnot]
  refine ⟨mul_ne_zero (pow_ne_zero _ hb0) hpre, ?_⟩
  rw [padicValRat.mul (pow_ne_zero _ hb0) hpre, padicValRat.pow,
    padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpb]
  simp only [Int.natCast_zero, mul_zero, zero_add]
  exact lt_of_not_ge (fun h => hshallow (Or.inr h))

end XiFamily
