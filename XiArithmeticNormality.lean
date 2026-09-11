import XiFiniteCombinationTransfer

/-!
# Normality of finite rational combinations of Xi values

The radix and the added generator are fixed. The second generator ranges
over distinct integers coprime to their product. At least one rational
coefficient must be nonzero; a rational constant term is arbitrary.
-/

noncomputable section
open scoped BigOperators Classical

namespace XiFamily

theorem normalInBase_active_rational_combination {b a : ℕ}
    (S : Finset ℕ) (q : ℕ → ℚ) (q₀ : ℚ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hSne : S.Nonempty) (hS : ∀ c ∈ S, 2 ≤ c)
    (hcop : ∀ c ∈ S, c.Coprime (a * b)) (hq : ∀ c ∈ S, q c ≠ 0) :
    StonehamNormality.NormalInBase b ((q₀ : ℝ) + ∑ c ∈ S, (q c : ℝ) * xi b c a) := by
  obtain ⟨p, d, C, hp, hd, hpb, hshallow⟩ :=
    exists_combination_logarithmic_depth S q q₀ ha (by omega) hSne hS hcop hq
  letI : Fact p.Prime := ⟨hp⟩
  exact normalInBase_finite_combination_of_depth S q q₀ C ha hb hd hS hpb hshallow

theorem sum_xi_filter_nonzero (b a : ℕ) (S : Finset ℕ) (q : ℕ → ℚ) :
    (∑ c ∈ S.filter (fun c => q c ≠ 0), (q c : ℝ) * xi b c a) =
      ∑ c ∈ S, (q c : ℝ) * xi b c a := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hq : q c = 0
  · simp [hq]
  · simp [hq]

/-- Every nontrivial finite rational combination in a fixed eligible Xi
family is normal in its defining radix, even after a rational translation. -/
theorem normalInBase_rational_combination {b a : ℕ}
    (S : Finset ℕ) (q : ℕ → ℚ) (q₀ : ℚ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hS : ∀ c ∈ S, 2 ≤ c) (hcop : ∀ c ∈ S, c.Coprime (a * b))
    (hq : ∃ c ∈ S, q c ≠ 0) :
    StonehamNormality.NormalInBase b ((q₀ : ℝ) + ∑ c ∈ S, (q c : ℝ) * xi b c a) := by
  let T := S.filter (fun c => q c ≠ 0)
  have hTne : T.Nonempty := by
    obtain ⟨c, hc, hqc⟩ := hq
    exact ⟨c, Finset.mem_filter.mpr ⟨hc, hqc⟩⟩
  have hT := normalInBase_active_rational_combination T q q₀ ha hb hTne
    (fun c hc => hS c (Finset.mem_filter.mp hc).1)
    (fun c hc => hcop c (Finset.mem_filter.mp hc).1)
    (fun c hc => (Finset.mem_filter.mp hc).2)
  simpa only [T, sum_xi_filter_nonzero] using hT

/-- The one-term instance of the arithmetic theorem. -/
theorem normalInBase_xi_of_arithmetic {b c a : ℕ}
    (hb : 2 ≤ b) (hc : 2 ≤ c) (ha : 2 ≤ a) (hcop : c.Coprime (a * b)) :
    StonehamNormality.NormalInBase b (xi b c a) := by
  have h := normalInBase_rational_combination ({c} : Finset ℕ) (fun _ => (1 : ℚ)) 0 ha hb
    (by simpa) (by simpa) (by simp)
  simpa using h

end XiFamily
