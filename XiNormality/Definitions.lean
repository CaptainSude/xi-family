import XiNormality.Imports

/-!
# The localized logarithm and binary normality

The target constant is the sum of `1 / (m * 2^m)` over the positive
integers `m = 2^a * 3^c`. Binary normality is expressed by frequencies
of all binary cylinders, with overlapping starting positions.
-/

noncomputable section

open scoped BigOperators Classical
open Filter

namespace XiNormality

def smoothIndex (a c : ℕ) : ℕ := 2 ^ a * 3 ^ c

def IsSmooth (m : ℕ) : Prop := ∃ a c : ℕ, m = smoothIndex a c

def summand (m : ℕ) : ℝ := if IsSmooth m then 1 / ((m : ℝ) * 2 ^ m) else 0

/-- The constant from the paper, indexed by the smooth integers. -/
def xi : ℝ := ∑' m : ℕ, summand m

/-- The binary radix orbit. -/
def binaryOrbit (x : ℝ) (n : ℕ) : ℝ := Int.fract ((2 : ℝ) ^ n * x)

/-- The interval specifying the binary word of length `l` and value `j`. -/
def binaryCylinder (l j : ℕ) : Set ℝ :=
  Set.Ico ((j : ℝ) / 2 ^ l) (((j : ℝ) + 1) / 2 ^ l)

def wordFrequency (x : ℝ) (l j M : ℕ) : ℝ :=
  ((Finset.range M).filter (fun n => binaryOrbit x n ∈ binaryCylinder l j)).card / (M : ℝ)

/-- Every finite binary word has its expected limiting frequency. -/
def BinaryNormal (x : ℝ) : Prop :=
  ∀ l j : ℕ, j < 2 ^ l →
    Tendsto (wordFrequency x l j) atTop (nhds ((2 : ℝ) ^ l)⁻¹)

def truncation (n : ℕ) : ℚ :=
  ∑ m ∈ (Finset.range (n + 1)).filter IsSmooth, (2 : ℚ) ^ (n - m) / m

end XiNormality
