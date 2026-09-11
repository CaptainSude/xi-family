import XiFamilyChallenge
import XiFamilyDefinition
import StonehamNormality.GeneralRadix

/-! Exact correspondence between the review statements and proof definitions. -/

noncomputable section

namespace XiFamily

theorem challenge_value_eq (b c a : ℕ) : XiFamilyChallenge.value b c a = xi b c a := rfl

theorem challenge_normal_iff (b : ℕ) (x : ℝ) :
    XiFamilyChallenge.normal b x ↔ StonehamNormality.NormalInBase b x := by
  have hf (l j : ℕ) : StonehamNormality.radixWordFrequency b x l j =
      (fun N : ℕ =>
        (((Finset.range N).filter (fun n =>
          (j : ℝ) / (b : ℝ) ^ l ≤ Int.fract ((b : ℝ) ^ n * x) ∧
          Int.fract ((b : ℝ) ^ n * x) < ((j : ℝ) + 1) / (b : ℝ) ^ l)).card : ℝ) / N) := by
    funext N
    unfold StonehamNormality.radixWordFrequency StonehamNormality.radixOrbit
      StonehamNormality.radixCylinder
    apply congrArg (fun s : Finset ℕ => (s.card : ℝ) / N)
    ext n
    simp only [Finset.mem_filter, Set.mem_Ico]
  unfold XiFamilyChallenge.normal StonehamNormality.NormalInBase
  simp only [hf]

end XiFamily
