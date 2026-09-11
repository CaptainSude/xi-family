import XiGroupedSeries
import XiWeightedDepth

/-! Denominator lower bounds and the surviving primitive block. -/

noncomputable section
open Filter
open scoped BigOperators Classical Topology

namespace XiFamily

theorem valuationAtLeast_mono {p : ℕ} {u v : ℤ} {x : ℚ}
    (huv : u ≤ v) (hx : ValuationAtLeast p v x) : ValuationAtLeast p u x := by
  rcases hx with h | h
  · exact Or.inl h
  · exact Or.inr (huv.trans h)

theorem valuationAtLeast_sum {ι : Type*} {p : ℕ} [Fact p.Prime]
    (S : Finset ι) (f : ι → ℚ) (v : ℤ)
    (h : ∀ i ∈ S, ValuationAtLeast p v (f i)) :
    ValuationAtLeast p v (∑ i ∈ S, f i) := by
  induction S using Finset.induction_on with
  | empty => simp [valuationAtLeast_zero]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact valuationAtLeast_add (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem not_valuationAtLeast_add {p : ℕ} [Fact p.Prime] {v : ℤ} {x y : ℚ}
    (hx : ¬ ValuationAtLeast p v x) (hy : ValuationAtLeast p v y) :
    ¬ ValuationAtLeast p v (x + y) := by
  intro h
  have hh := valuationAtLeast_sub h hy
  exact hx (by simpa using hh)

theorem not_valuationAtLeast_sum_of_one_deep {ι : Type*} {p : ℕ} [Fact p.Prime]
    (S : Finset ι) (f : ι → ℚ) (d : ι) (hd : d ∈ S) (v : ℤ)
    (hdeep : ¬ ValuationAtLeast p v (f d))
    (hrest : ∀ e ∈ S, e ≠ d → ValuationAtLeast p v (f e)) :
    ¬ ValuationAtLeast p v (∑ e ∈ S, f e) := by
  rw [← Finset.add_sum_erase S f hd]
  apply not_valuationAtLeast_add hdeep
  apply valuationAtLeast_sum
  intro e he
  exact hrest e (Finset.mem_erase.mp he).2 (Finset.mem_erase.mp he).1

theorem classTerm_eq_weightedTerm (b a d : ℕ) (S : Finset ℕ) (q : ℕ → ℚ)
    (ha : 2 ≤ a) (hd : 2 ≤ d) (had : a.Coprime d)
    (hS : ∀ c ∈ S, 2 ≤ c) :
    classTerm b a S q d = weightedTerm b d a (classWeight S q d) := by
  funext m
  by_cases hm : IsIndex a d m
  · obtain ⟨i, k, rfl⟩ := hm
    rw [classTerm_at_pair b a d i k S q ha hd had hS,
      weightedTerm_pair _ ha hd had]
    simp [unshiftedTerm, isIndex_mul_pow, div_eq_mul_inv]
  · rw [classTerm_eq_zero_of_not_index b a d m S q hS hm,
      weightedTerm_eq_zero_of_not_index _ hm]

def coefficientValuationFloor (p : ℕ) (S : Finset ℕ) (q : ℕ → ℚ) : ℤ :=
  -(∑ c ∈ S, |padicValRat p (q c)|)

theorem coefficientValuationFloor_le (p : ℕ) (S : Finset ℕ) (q : ℕ → ℚ)
    {c : ℕ} (hc : c ∈ S) : coefficientValuationFloor p S q ≤ padicValRat p (q c) := by
  have hsum := Finset.single_le_sum (fun e (_ : e ∈ S) => abs_nonneg (padicValRat p (q e))) hc
  have hneg := neg_abs_le (padicValRat p (q c))
  unfold coefficientValuationFloor
  omega

theorem classWeight_valuationAtLeast {p : ℕ} [Fact p.Prime]
    (S : Finset ℕ) (q : ℕ → ℚ) (d k : ℕ) :
    ValuationAtLeast p (coefficientValuationFloor p S q) (classWeight S q d k) := by
  apply valuationAtLeast_sum
  intro c hc
  by_cases hr : primitiveExponent c ∣ k
  · simp only [hr, ite_true]
    exact Or.inr (coefficientValuationFloor_le p S q (Finset.mem_filter.mp hc).1)
  · simp only [hr, ite_false]
    exact valuationAtLeast_zero _ _

theorem classTerm_valuation_lower_bound {p b a d : ℕ} [Fact p.Prime]
    (S : Finset ℕ) (q : ℕ → ℚ) (ha : 2 ≤ a) (hd : 2 ≤ d) (hb : 0 < b)
    (had : a.Coprime d) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hS : ∀ c ∈ S, 2 ≤ c) (M m : ℕ) (hmM : m ≤ M) :
    ValuationAtLeast p (coefficientValuationFloor p S q -
      (Nat.log d M : ℤ) * padicValNat p d) (classTerm b a S q d m) := by
  rw [classTerm_eq_weightedTerm b a d S q ha hd had hS]
  by_cases hm : weightedTerm b d a (classWeight S q d) m = 0
  · exact Or.inl hm
  obtain ⟨i, k, rfl⟩ := weightedTerm_support (classWeight S q d) hm
  have hw := (weightedTerm_pair_ne_zero_iff (classWeight S q d) hb ha hd had i k).mp hm
  have hval := weightedTerm_valuation_pair (classWeight S q d) hb ha hd had hpa hpb i k hw
  have hwlow : coefficientValuationFloor p S q ≤ padicValRat p (classWeight S q d k) := by
    rcases classWeight_valuationAtLeast (p := p) S q d k with hz | hv
    · exact False.elim (hw hz)
    · exact hv
  have hdM : d ^ k ≤ M := by
    have hai : 1 ≤ a ^ i := one_le_pow₀ (by omega)
    nlinarith
  have hM : M ≠ 0 := by
    have hdpos : 0 < d ^ k := pow_pos (by omega) _
    omega
  have hk : k ≤ Nat.log d M := (Nat.le_log_iff_pow_le (by omega) hM).mpr hdM
  have hkZ : (k : ℤ) ≤ Nat.log d M := by exact_mod_cast hk
  exact Or.inr (by rw [hval]; nlinarith [Int.natCast_nonneg (padicValNat p d)])

theorem classPrefix_valuation_lower_bound {p b a d : ℕ} [Fact p.Prime]
    (S : Finset ℕ) (q : ℕ → ℚ) (ha : 2 ≤ a) (hd : 2 ≤ d) (hb : 0 < b)
    (had : a.Coprime d) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hS : ∀ c ∈ S, 2 ≤ c) (M n : ℕ) (hnM : n ≤ M) :
    ValuationAtLeast p (coefficientValuationFloor p S q -
      (Nat.log d M : ℤ) * padicValNat p d)
      (∑ m ∈ Finset.range n, classTerm b a S q d m) := by
  apply valuationAtLeast_sum
  intro m hm
  exact classTerm_valuation_lower_bound S q ha hd hb had hpa hpb hS M m
    ((Finset.mem_range.mp hm).le.trans hnM)

end XiFamily
