import XiNormality.Cylinder
import StonehamNormality.StonehamSeries

/-!
# Stoneham constants and normality in an arbitrary integer base

Normality is stated by the frequencies of every finite radix word, with all
overlapping starting positions and a limit along every prefix length.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped BigOperators Topology Classical

namespace StonehamNormality

/-- The conventional Stoneham constant, with summation index starting at one. -/
def stonehamConstant (b c : ℕ) : ℝ :=
  ∑' k : ℕ, 1 / ((c : ℝ) ^ (k + 1) * (b : ℝ) ^ (c ^ (k + 1)))

theorem stonehamConstant_two (c : ℕ) (hc : 2 ≤ c) :
    stonehamConstant 2 c = stoneham c := by
  simpa only [stonehamConstant, Nat.cast_ofNat] using (stoneham_eq_power_series hc).symm

def radixOrbit (b : ℕ) (x : ℝ) (n : ℕ) : ℝ := Int.fract ((b : ℝ) ^ n * x)

/-- The half-open interval encoding the word with length `l` and value `j`. -/
def radixCylinder (b l j : ℕ) : Set ℝ :=
  Ico ((j : ℝ) / (b : ℝ) ^ l) (((j : ℝ) + 1) / (b : ℝ) ^ l)

def radixWordFrequency (b : ℕ) (x : ℝ) (l j M : ℕ) : ℝ :=
  ((Finset.range M).filter (fun n => radixOrbit b x n ∈ radixCylinder b l j)).card / (M : ℝ)

/-- Every finite word has the expected frequency in a base of at least two. -/
def NormalInBase (b : ℕ) (x : ℝ) : Prop :=
  2 ≤ b ∧ ∀ l j : ℕ, j < b ^ l →
    Tendsto (radixWordFrequency b x l j) atTop (𝓝 ((b : ℝ) ^ l)⁻¹)

/-- Cancellation of every nonconstant circle character on the radix orbit. -/
def RadixFourierCancellation (b : ℕ) (x : ℝ) : Prop :=
  ∀ h : ℤ, h ≠ 0 →
    Tendsto (fun M : ℕ => (M : ℝ)⁻¹ •
      ∑ i ∈ Finset.range M, fourier (T := 1) h
        (((b : ℝ) ^ i * x : ℝ) : UnitAddCircle)) atTop (𝓝 0)

theorem normalInBase_two_iff (x : ℝ) : NormalInBase 2 x ↔ XiNormality.BinaryNormal x := by
  change (2 ≤ (2 : ℕ) ∧ XiNormality.BinaryNormal x) ↔ XiNormality.BinaryNormal x
  simp

/-- Fourier cancellation implies interval frequencies for arbitrary real endpoints. -/
theorem radix_interval_frequency_tendsto_of_fourier (b : ℕ) (x : ℝ)
    (h : RadixFourierCancellation b x)
    {a d : ℝ} (ha : 0 ≤ a) (had : a < d) (hd : d ≤ 1) :
    Tendsto (fun M : ℕ =>
      (((Finset.range M).filter (fun n => radixOrbit b x n ∈ Ico a d)).card : ℝ) / M)
      atTop (𝓝 (d - a)) := by
  have hf := XiNormality.circleArc_frequency_tendsto_of_fourier
    (fun i => (((b : ℝ) ^ i * x : ℝ) : UnitAddCircle)) h ha had hd
  simpa only [radixOrbit, XiNormality.circleArc, Set.mem_preimage,
    XiNormality.circleRepresentative_coe] using hf

/-- The Weyl criterion with the actual overlapping word-frequency conclusion. -/
theorem normalInBase_of_fourier (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (h : RadixFourierCancellation b x) : NormalInBase b x := by
  refine ⟨hb, ?_⟩
  intro l j hj
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hp : (0 : ℝ) < (b : ℝ) ^ l := pow_pos hbpos l
  have ha : (0 : ℝ) ≤ j / (b : ℝ) ^ l := by positivity
  have had : (j : ℝ) / (b : ℝ) ^ l < ((j : ℝ) + 1) / (b : ℝ) ^ l :=
    div_lt_div_of_pos_right (by linarith) hp
  have hd : ((j : ℝ) + 1) / (b : ℝ) ^ l ≤ 1 := by
    apply (div_le_iff₀ hp).mpr
    simpa using (show (j : ℝ) + 1 ≤ (b : ℝ) ^ l by exact_mod_cast Nat.succ_le_of_lt hj)
  have hf := radix_interval_frequency_tendsto_of_fourier b x h ha had hd
  have hlength : ((j : ℝ) + 1) / (b : ℝ) ^ l - (j : ℝ) / (b : ℝ) ^ l =
      ((b : ℝ) ^ l)⁻¹ := by ring
  change Tendsto (fun M => radixWordFrequency b x l j M) atTop _
  simpa only [radixWordFrequency, radixCylinder, hlength] using hf

theorem RadixFourierCancellation.normalInBase {b : ℕ} {x : ℝ}
    (h : RadixFourierCancellation b x) (hb : 2 ≤ b) : NormalInBase b x :=
  normalInBase_of_fourier b hb x h

end StonehamNormality
