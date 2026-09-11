import Mathlib.Analysis.Real.OfDigits
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Statements for independent review

This file states the intended constants and conclusions directly, without
importing any part of the Xi proof. Indices are distinct natural numbers.
The normality condition counts overlapping positions at every prefix length.
-/

noncomputable section
open Filter
open scoped BigOperators Classical Topology

namespace XiFamilyChallenge

def value (b c a : ℕ) : ℝ :=
  ∑' m : ℕ, if (∃ i k : ℕ, m = a ^ i * c ^ k)
    then 1 / ((m : ℝ) * (b : ℝ) ^ m) else 0

def normal (b : ℕ) (x : ℝ) : Prop :=
  2 ≤ b ∧ ∀ length word : ℕ, word < b ^ length →
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun n =>
        (word : ℝ) / (b : ℝ) ^ length ≤ Int.fract ((b : ℝ) ^ n * x) ∧
        Int.fract ((b : ℝ) ^ n * x) < ((word : ℝ) + 1) / (b : ℝ) ^ length)).card : ℝ) / N)
      atTop (𝓝 (((b : ℝ) ^ length)⁻¹))

def IndividualNormality : Prop :=
  ∀ b c a : ℕ, 2 ≤ b → 2 ≤ c → 2 ≤ a → c.Coprime (a * b) →
    normal b (value b c a)

def RationalCombinationNormality : Prop :=
  ∀ (b a : ℕ) (S : Finset ℕ) (q : ℕ → ℚ) (q₀ : ℚ),
    2 ≤ b → 2 ≤ a → (∀ c ∈ S, 2 ≤ c ∧ c.Coprime (a * b)) →
    (∃ c ∈ S, q c ≠ 0) →
    normal b ((q₀ : ℝ) + ∑ c ∈ S, (q c : ℝ) * value b c a)

end XiFamilyChallenge
