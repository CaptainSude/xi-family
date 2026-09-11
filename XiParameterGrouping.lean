import XiFamilyDefinition
import XiPeriodicWeights

/-! Exact exponent filters for multiplicatively dependent Xi parameters. -/

noncomputable section
open scoped BigOperators Classical

namespace XiFamily

theorem isIndex_power_parameter_iff {a d r : ℕ}
    (ha : 2 ≤ a) (hd : 2 ≤ d) (had : a.Coprime d) (i k : ℕ) :
    IsIndex a (d ^ r) (a ^ i * d ^ k) ↔ r ∣ k := by
  constructor
  · rintro ⟨j, l, he⟩
    rw [← pow_mul] at he
    have hij : (i, k) = (j, r * l) := index_injective ha hd had he
    have hk : k = r * l := congrArg Prod.snd hij
    exact ⟨l, hk⟩
  · rintro ⟨l, rfl⟩
    exact ⟨i, l, by rw [← pow_mul]⟩

theorem isIndex_rectangular_parameter_iff {a d r s : ℕ}
    (ha : 2 ≤ a) (hd : 2 ≤ d) (had : a.Coprime d) (i k : ℕ) :
    IsIndex (a ^ r) (d ^ s) (a ^ i * d ^ k) ↔ r ∣ i ∧ s ∣ k := by
  constructor
  · rintro ⟨j, l, he⟩
    rw [← pow_mul, ← pow_mul] at he
    have hij : (i, k) = (r * j, s * l) := index_injective ha hd had he
    exact ⟨⟨j, congrArg Prod.fst hij⟩, ⟨l, congrArg Prod.snd hij⟩⟩
  · rintro ⟨⟨j, rfl⟩, ⟨l, rfl⟩⟩
    exact ⟨j, l, by rw [← pow_mul, ← pow_mul]⟩

/-- A parameter power filters the second exponent by divisibility. -/
theorem term_power_parameter (b a d r i k : ℕ)
    (ha : 2 ≤ a) (hd : 2 ≤ d) (had : a.Coprime d) :
    term b (d ^ r) a (a ^ i * d ^ k) =
      if r ∣ k then 1 / (((a ^ i * d ^ k : ℕ) : ℝ) *
        (b : ℝ) ^ (a ^ i * d ^ k)) else 0 := by
  simp only [term, isIndex_power_parameter_iff ha hd had]

/-- Combining dependent parameters produces exactly the finite periodic
divisibility weight, including all cancellations. -/
theorem combined_term_power_parameters (b a d i k : ℕ)
    (S : Finset ℕ) (q : ℕ → ℚ)
    (ha : 2 ≤ a) (hd : 2 ≤ d) (had : a.Coprime d) :
    (∑ r ∈ S, (q r : ℝ) * term b (d ^ r) a (a ^ i * d ^ k)) =
      (divisibilityWeight S q k : ℝ) *
        (1 / (((a ^ i * d ^ k : ℕ) : ℝ) * (b : ℝ) ^ (a ^ i * d ^ k))) := by
  simp only [term_power_parameter b a d _ i k ha hd had]
  unfold divisibilityWeight
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs <;> simp

theorem combined_term_rectangular_parameters (b a d i k : ℕ)
    (S : Finset (ℕ × ℕ)) (q : (ℕ × ℕ) → ℚ)
    (ha : 2 ≤ a) (hd : 2 ≤ d) (had : a.Coprime d) :
    (∑ rs ∈ S, (q rs : ℝ) * term b (d ^ rs.2) (a ^ rs.1) (a ^ i * d ^ k)) =
      (rectangularWeight S q i k : ℝ) *
        (1 / (((a ^ i * d ^ k : ℕ) : ℝ) * (b : ℝ) ^ (a ^ i * d ^ k))) := by
  simp only [term, isIndex_rectangular_parameter_iff ha hd had]
  unfold rectangularWeight
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro rs hrs
  split_ifs <;> simp

end XiFamily
