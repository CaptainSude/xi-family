import XiFamilyStatement
import XiFamilyNormality
import XiArithmeticNormality

/-! Proofs of the independently stated review targets. -/

noncomputable section

namespace XiFamilySolution

theorem individual_normality : XiFamilyChallenge.IndividualNormality := by
  intro b c a hb hc ha hcop
  apply (XiFamily.challenge_normal_iff b _).mpr
  rw [XiFamily.challenge_value_eq]
  exact XiFamily.xi_normalInBase b c a hb hc ha hcop

theorem rational_combinations : XiFamilyChallenge.RationalCombinationNormality := by
  intro b a S q q₀ hb ha hS hq
  apply (XiFamily.challenge_normal_iff b _).mpr
  simp_rw [XiFamily.challenge_value_eq]
  exact XiFamily.normalInBase_rational_combination S q q₀ ha hb
    (fun c hc => (hS c hc).1) (fun c hc => (hS c hc).2) hq

theorem full_statement :
    XiFamilyChallenge.IndividualNormality ∧ XiFamilyChallenge.RationalCombinationNormality :=
  ⟨individual_normality, rational_combinations⟩

end XiFamilySolution
