import XiFamilyNormalityFromDepth
import XiClearingBuffers

/-! Unconditional individual normality for the coprime Xi family. -/

noncomputable section
open Filter
open scoped BigOperators Topology Classical

namespace XiFamily

theorem xi_normalInBase_of_surviving_prime {p b c a : ℕ} [Fact p.Prime]
    (hb : 2 ≤ b) (ha : 2 ≤ a) (hc : 2 ≤ c) (hac : a.Coprime c)
    (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpdepth : 0 < padicValNat p c) :
    StonehamNormality.NormalInBase b (xi b c a) := by
  let T := 288 * (8 * c) * 2 ^ (2 * 2)
  have hT : 0 < T := by dsimp [T]; positivity
  have hQ : depthNormalityScale c 2 = (2 : ℕ) ^ T := rfl
  apply normalInBase_of_logarithmic_depth (p := p) b c 2 1 (nonbasePrimeSupport b (a * c)) hb hc
    (nonbasePrimeSupport_pos _ _) (nonbasePrimeSupport_coprime _ _) 0
    (xi b c a) (truncation b c a) (IsIndex a c) (individualShallow p b c a)
    (individualClearingBad a c T)
    (truncation_error_tendsto_zero b c a hb)
    (truncation_add_of_no_new_terms b c a)
  · intro n hn
    simpa using truncation_den_le_square b c a n ha hc hn.ne'
  · exact individualShallow_density_zero ha hc (by omega) hac hpa hpb hpdepth
  · intro n hn hindex
    obtain ⟨hnz, hv⟩ := truncation_depth_of_not_shallow_not_index hb hpb hn hindex
    refine ⟨hnz, ?_⟩
    have hpR : (1 : ℤ) ≤ padicValNat p c := by exact_mod_cast hpdepth
    have hk : (0 : ℤ) ≤ ((Nat.log c (n / 2) / 2 : ℕ) : ℤ) := by positivity
    nlinarith
  · refine ⟨2, (((T + 1) ^ 2 : ℕ) : ℝ), by positivity, ?_⟩
    intro B
    have hcnt : (((Finset.range ((2 ^ T) ^ (B + 1) + 1)).filter (IsIndex a c)).card) ≤
        (T + 1) ^ 2 * (B + 1) ^ 2 := by
      have hp : unionIndex ({()} : Finset Unit) (fun _ => a) (fun _ => c) = IsIndex a c := by
        funext n
        simp [unionIndex]
      have hh := unionIndex_card_at_scale_le ({()} : Finset Unit)
        (fun _ => a) (fun _ => c) (fun _ _ => ha) (fun _ _ => hc) T B
      rw [hp] at hh
      simpa using hh
    have hsub : (Finset.range ((depthNormalityScale c 2) ^ B)).filter (IsIndex a c) ⊆
        (Finset.range ((2 ^ T) ^ (B + 1) + 1)).filter (IsIndex a c) := by
      intro n hn
      obtain ⟨hnN, hni⟩ := Finset.mem_filter.mp hn
      have hnp := Finset.mem_range.mp hnN
      rw [hQ] at hnp
      have hpow : (2 ^ T) ^ B ≤ (2 ^ T) ^ (B + 1) :=
        pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hni⟩
    have hcard := (Finset.card_le_card hsub).trans hcnt
    exact_mod_cast hcard
  · exact individualClearingBad_density_zero a c T ha hc hT
  · intro B n hn hclear
    have hpow : (2 ^ T) ^ B ≤ (2 ^ T) ^ (B + 1) :=
      pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega)
    have hnn : n ≤ (2 ^ T) ^ (B + 1) := by rw [hQ] at hn; exact hn.trans hpow
    have hh := truncation_outside_clearing_buffer b c a T B hb ha hc hnn hclear 1
    refine ⟨hh.1, ?_⟩
    simpa using hh.2.2

/-- Every member of the fixed-generator coprime Xi family is normal in its
defining base. This is the individual theorem, independent of linear arithmetic. -/
theorem xi_normalInBase (b c a : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c) (ha : 2 ≤ a)
    (hcop : c.Coprime (a * b)) : StonehamNormality.NormalInBase b (xi b c a) := by
  obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd (show c ≠ 1 by omega)
  letI : Fact p.Prime := ⟨hp⟩
  have hpab : ¬ p ∣ a * b := hp.coprime_iff_not_dvd.mp (hcop.of_dvd_left hpc)
  have hpa : ¬ p ∣ a := fun hd => hpab (dvd_mul_of_dvd_left hd b)
  have hpb : ¬ p ∣ b := fun hd => hpab (dvd_mul_of_dvd_right hd a)
  have hac : a.Coprime c := (hcop.of_dvd_right (Nat.dvd_mul_right a b)).symm
  have hdepth : 0 < padicValNat p c := one_le_padicValNat_of_dvd (by omega) hpc
  exact xi_normalInBase_of_surviving_prime hb ha hc hac hpa hpb hdepth

end XiFamily
