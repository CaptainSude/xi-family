import StonehamNormality.XiAnalyticDensity

/-! Elementary exceptional-set calculus at geometric scales. -/

noncomputable section
open Filter
open scoped BigOperators Topology Classical

namespace XiFamily

def ScaleNegligible (Q : ℕ) (bad : ℕ → ℕ → Prop) : Prop :=
  Tendsto (fun B : ℕ =>
    (((Finset.range (Q ^ (B + 1))).filter (bad (B + 1))).card : ℝ) /
      (Q : ℝ) ^ B) atTop (𝓝 0)

theorem nat_geometric_tendsto_atTop (Q : ℕ) (hQ : 1 < Q) :
    Tendsto (fun B : ℕ => Q ^ B) atTop atTop := by
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [eventually_ge_atTop n] with B hB
  exact hB.trans ((Nat.lt_two_pow_self.le).trans
    (Nat.pow_le_pow_left (by omega : 2 ≤ Q) B))

theorem scaleNegligible_of_natural_density_zero
    (Q : ℕ) (hQ : 1 < Q) (bad : ℕ → Prop)
    (hbad : Tendsto (fun N : ℕ =>
      (((Finset.range N).filter bad).card : ℝ) / N) atTop (𝓝 0)) :
    ScaleNegligible Q (fun _ => bad) := by
  have hpow := (nat_geometric_tendsto_atTop Q hQ).comp (tendsto_add_atTop_nat 1)
  have hlim := (hbad.comp hpow).const_mul (Q : ℝ)
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  unfold ScaleNegligible
  convert hlim using 1
  · ext B
    simp only [Function.comp_def, Nat.cast_pow, pow_succ]
    field_simp
    push_cast
    ring
  · simp

theorem scaleNegligible_union {Q : ℕ} {bad₁ bad₂ : ℕ → ℕ → Prop}
    (h₁ : ScaleNegligible Q bad₁) (h₂ : ScaleNegligible Q bad₂) :
    ScaleNegligible Q (fun B n => bad₁ B n ∨ bad₂ B n) := by
  have hsum := h₁.add h₂
  simp only [add_zero] at hsum
  apply squeeze_zero (fun B => by positivity) ?_ hsum
  intro B
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hcard : ((Finset.range (Q ^ (B + 1))).filter
      (fun n => bad₁ (B + 1) n ∨ bad₂ (B + 1) n)).card ≤
      ((Finset.range (Q ^ (B + 1))).filter (bad₁ (B + 1))).card +
      ((Finset.range (Q ^ (B + 1))).filter (bad₂ (B + 1))).card := by
    rw [Finset.filter_or]
    exact Finset.card_union_le _ _
  convert (show (((Finset.range (Q ^ (B + 1))).filter
      (fun n => bad₁ (B + 1) n ∨ bad₂ (B + 1) n)).card : ℝ) ≤
      (((Finset.range (Q ^ (B + 1))).filter (bad₁ (B + 1))).card : ℝ) +
      (((Finset.range (Q ^ (B + 1))).filter (bad₂ (B + 1))).card : ℝ) by
    exact_mod_cast hcard) using 1 <;> congr

theorem scaleNegligible_of_eventually_subset {Q : ℕ} {bad₁ bad₂ : ℕ → ℕ → Prop}
    (h₂ : ScaleNegligible Q bad₂)
    (hsub : ∀ᶠ B : ℕ in atTop, ∀ n < Q ^ (B + 1),
      bad₁ (B + 1) n → bad₂ (B + 1) n) :
    ScaleNegligible Q bad₁ := by
  apply squeeze_zero' (Eventually.of_forall (fun B => by positivity)) ?_ h₂
  filter_upwards [hsub] with B hB
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnI, hnb⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨hnI, hB n (Finset.mem_range.mp hnI) hnb⟩

theorem scaleNegligible_early_prefix (Q U : ℕ) (hQ : 1 < Q) (hU : U < Q) :
    ScaleNegligible Q (fun B n => n < U ^ B) := by
  have hlim : Tendsto (fun B : ℕ => (U : ℝ) ^ (B + 1) / (Q : ℝ) ^ B)
      atTop (𝓝 0) := by
    simpa using StonehamNormality.geometric_scale_error_tendsto_zero
      Q U 0 (by omega) hU (by omega) 0 0
  apply squeeze_zero (fun B => by positivity) ?_ hlim
  intro B
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hcard : ((Finset.range (Q ^ (B + 1))).filter
      (fun n => n < U ^ (B + 1))).card ≤ U ^ (B + 1) := by
    calc
      _ ≤ (Finset.range (U ^ (B + 1))).card := Finset.card_le_card (by
        intro n hn
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2)
      _ = _ := Finset.card_range _
  convert (show (((Finset.range (Q ^ (B + 1))).filter
      (fun n => n < U ^ (B + 1))).card : ℝ) ≤ (U : ℝ) ^ (B + 1) by
    exact_mod_cast hcard) using 1
  all_goals first
    | rfl
    | exact congrArg (fun s : Finset ℕ => (s.card : ℝ))
        (Finset.filter_congr_decidable _ _ _)

theorem scaleNegligible_finset (Q : ℕ) (hQ : 1 < Q) (E : ℕ → Finset ℕ)
    (hE : Tendsto (fun B : ℕ => ((E B).card : ℝ) / (Q : ℝ) ^ B)
      atTop (𝓝 0)) : ScaleNegligible Q (fun B n => n ∈ E B) := by
  have hlim := (hE.comp (tendsto_add_atTop_nat 1)).const_mul (Q : ℝ)
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hshift : Tendsto (fun B : ℕ => ((E (B + 1)).card : ℝ) / (Q : ℝ) ^ B)
      atTop (𝓝 0) := by
    convert hlim using 1
    · ext B
      simp only [Function.comp_def, pow_succ]
      field_simp
    · simp
  apply squeeze_zero (fun B => by positivity) ?_ hshift
  intro B
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn
  exact hn.2

end XiFamily
