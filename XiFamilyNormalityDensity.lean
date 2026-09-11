import XiBlockDepth
import StonehamNormality.XiAnalyticDensity
import StonehamNormality.TwoSumMain

/-! Natural-density denominator escape for the individual Xi family. -/

noncomputable section
open Filter
open scoped BigOperators Topology Classical

namespace XiFamily

def individualShallow (p b c a n : ℕ) : Prop :=
  ValuationAtLeast p (-((Nat.log c (n / 2) / 2 : ℕ) : ℤ) * padicValNat p c)
    (∑ m ∈ Finset.range n, unshiftedTerm b c a m)

/-- The local denominator estimate gives one fixed exceptional predicate of
natural density zero. Using `n/2` makes it subordinate to the dyadic threshold. -/
theorem individualShallow_density_zero {p b c a : ℕ} [Fact p.Prime]
    (ha : 2 ≤ a) (hc : 2 ≤ c) (hb : 0 < b) (hac : a.Coprime c)
    (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpdepth : 0 < padicValNat p c) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (individualShallow p b c a)).card : ℝ) / N)
        atTop (𝓝 0) := by
  apply StonehamNormality.xi_density_zero_of_dyadic_density_zero
  have hd := unshiftedPrefix_half_log_shallow_density_zero
    ha hc hb hac hpa hpb hpdepth
  apply squeeze_zero (fun N => by positivity) ?_ hd
  intro N
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnI, hnb⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨hnI, ?_⟩
  have hni := Finset.mem_Ico.mp hnI
  have hnlo : n / 2 ≤ N := by omega
  have hk : Nat.log c (n / 2) / 2 ≤ Nat.log c N / 2 :=
    Nat.div_le_div_right (Nat.log_mono_right hnlo)
  rcases hnb with hz | hv
  · exact Or.inl hz
  · apply Or.inr
    have hkR : ((Nat.log c (n / 2) / 2 : ℕ) : ℤ) ≤
        ((Nat.log c N / 2 : ℕ) : ℤ) := by exact_mod_cast hk
    have hpos : (0 : ℤ) ≤ padicValNat p c := by positivity
    nlinarith

/-- Away from an insertion index, the range-`n` prefix is exactly the
unshifted truncation used by the analytic approximation. -/
theorem truncation_depth_of_not_shallow_not_index {p b c a n : ℕ} [Fact p.Prime]
    (hb : 2 ≤ b) (hpb : ¬ p ∣ b)
    (hshallow : ¬ individualShallow p b c a n) (hindex : ¬ IsIndex a c n) :
    truncation b c a n ≠ 0 ∧
      padicValRat p (truncation b c a n) <
        -((Nat.log c (n / 2) / 2 : ℕ) : ℤ) * padicValNat p c := by
  have hpref : unshiftedPrefix b c a n =
      ∑ m ∈ Finset.range n, unshiftedTerm b c a m := by
    rw [unshiftedPrefix, Finset.sum_range_succ,
      unshiftedTerm_eq_zero_of_not_index hindex, add_zero]
  have hnz : (∑ m ∈ Finset.range n, unshiftedTerm b c a m) ≠ 0 := by
    intro hz
    exact hshallow (Or.inl hz)
  constructor
  · rw [truncation_eq_pow_mul_unshiftedPrefix b c a n hb, hpref]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (show b ≠ 0 by omega))) hnz
  · rw [truncation_valuation_eq_unshiftedPrefix hb hpb, hpref]
    exact lt_of_not_ge (fun hv => hshallow (Or.inr hv))

/-- Negative valuation supplies an ordinary lower bound on the reduced
denominator, with base two independent of the chosen surviving prime. -/
theorem denominator_two_pow_le_of_negative_valuation {p : ℕ} [Fact p.Prime]
    (r : ℚ) (K : ℕ) (hv : padicValRat p r < -(K : ℤ)) :
    2 ^ K ≤ r.den := by
  have hp := Fact.out (p := p.Prime)
  have hdepth : K ≤ padicValNat p r.den := by
    rw [padicValRat_def] at hv
    have hnum : (0 : ℤ) ≤ padicValInt p r.num := by positivity
    omega
  calc
    2 ^ K ≤ p ^ K := Nat.pow_le_pow_left hp.two_le K
    _ ≤ p ^ padicValNat p r.den := pow_le_pow_right₀ hp.one_lt.le hdepth
    _ ≤ r.den := Nat.le_of_dvd r.den_pos (pow_padicValNat_dvd)

theorem half_log_large_on_geometric_tail (c B n : ℕ) (hc : 2 ≤ c)
    (hB : 1 ≤ B) (hn : 2 ^ ((2304 * c) * B) ≤ n) :
    576 * B ≤ Nat.log c (n / 2) / 2 := by
  have hc2 : c ≤ (2 : ℕ) ^ c := Nat.lt_two_pow_self.le
  have hcpow : c ^ (1152 * B) ≤ 2 ^ ((1152 * c) * B) := by
    calc
      _ ≤ (2 ^ c) ^ (1152 * B) := Nat.pow_le_pow_left hc2 _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  have hmul : c ^ (1152 * B) * 2 ≤ n := by
    calc
      _ ≤ 2 ^ ((1152 * c) * B) * 2 := Nat.mul_le_mul_right 2 hcpow
      _ = 2 ^ (((1152 * c) * B) + 1) := (pow_succ _ _).symm
      _ ≤ 2 ^ ((2304 * c) * B) := by
        apply pow_le_pow_right₀ (by norm_num)
        nlinarith
      _ ≤ n := hn
  have hlog : 1152 * B ≤ Nat.log c (n / 2) :=
    Nat.le_log_of_pow_le (by omega)
      ((Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).mpr hmul)
  omega

/-- A single concrete choice of scales provides the denominator lower bound
needed by the analytic theorem for every Fourier frequency. -/
theorem individual_fourier_den_lower {p b c a : ℕ} [Fact p.Prime]
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hpb : ¬ p ∣ b)
    (hpdepth : 0 < padicValNat p c) (h : ℤ) (hh : h ≠ 0) (B n : ℕ)
    (hB : 1 ≤ B) (hhB : padicValInt p h ≤ 288 * B)
    (hn : 2 ^ ((2304 * c) * B) ≤ n)
    (hshallow : ¬ individualShallow p b c a n) (hindex : ¬ IsIndex a c n) :
    2 ^ (288 * B) ≤ ((h : ℚ) * truncation b c a n).den := by
  obtain ⟨htnz, htval⟩ := truncation_depth_of_not_shallow_not_index hb hpb hshallow hindex
  have hk := half_log_large_on_geometric_tail c B n hc hB hn
  apply denominator_two_pow_le_of_negative_valuation (p := p)
  rw [padicValRat.mul (by exact_mod_cast hh) htnz, padicValRat.of_int]
  have hkR : ((576 * B : ℕ) : ℤ) ≤ ((Nat.log c (n / 2) / 2 : ℕ) : ℤ) := by
    exact_mod_cast hk
  have hpR : (1 : ℤ) ≤ padicValNat p c := by exact_mod_cast hpdepth
  have hhR : (padicValInt p h : ℤ) ≤ ((288 * B : ℕ) : ℤ) := by exact_mod_cast hhB
  push_cast at *
  nlinarith

theorem integer_mul_den_dvd (h : ℤ) (r : ℚ) : ((h : ℚ) * r).den ∣ r.den := by
  simpa using Rat.mul_den_dvd (h : ℚ) r

/-- The concrete rational-window certificate for an individual Xi truncation.
Only the arithmetic support-clearing assertion remains an input. -/
theorem individual_rational_window {p b c a : ℕ} [Fact p.Prime]
    (hb : 2 ≤ b) (ha : 2 ≤ a) (hc : 2 ≤ c) (hpb : ¬ p ∣ b)
    (hpdepth : 0 < padicValNat p c) (h : ℤ) (hh : h ≠ 0) (B n S : ℕ)
    (hB : 1 ≤ B) (hhB : padicValInt p h ≤ 288 * B)
    (hn : 2 ^ ((2304 * c) * B) ≤ n)
    (hnu : n ≤ (StonehamNormality.xiOrbitScale (8 * c) 1) ^ B)
    (hshallow : ¬ individualShallow p b c a n) (hindex : ¬ IsIndex a c n)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ (truncation b c a n).den → p ∣ S) :
    StonehamNormality.XiRationalWindow S (8 * c) 1 B
      ((h : ℚ) * truncation b c a n) := by
  let r := (h : ℚ) * truncation b c a n
  have hden : r.den ≤ n ^ 2 :=
    (Nat.le_of_dvd (truncation b c a n).den_pos (integer_mul_den_dvd h _)).trans
      (truncation_den_le_square b c a n ha hc (by
        have hp : 0 < (2 : ℕ) ^ ((2304 * c) * B) := by positivity
        omega))
  refine ⟨r.den, r.den_pos, ?_, ?_, ?_, r.num,
    StonehamNormality.rational_reduced_num_isUnit r, (Rat.num_div_den r).symm⟩
  · simpa using individual_fourier_den_lower hb hc hpb hpdepth h hh B n hB hhB hn hshallow hindex
  · calc
      r.den ≤ n ^ 2 := hden
      _ ≤ ((StonehamNormality.xiOrbitScale (8 * c) 1) ^ B) ^ 2 :=
        Nat.pow_le_pow_left hnu 2
      _ ≤ _ := by
        simp only [StonehamNormality.xiOrbitScale, ← pow_mul]
        apply pow_le_pow_right₀ (by norm_num)
        norm_num
        nlinarith
  · intro q hq hqr
    exact hsupport q hq (hqr.trans (integer_mul_den_dvd h _))

end XiFamily
