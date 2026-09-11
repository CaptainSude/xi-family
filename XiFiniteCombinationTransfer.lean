import XiArithmeticDepth
import XiClearingBuffers
import XiFamilyNormalityFromDepth

/-!
# Analytic transfer for finite rational Xi combinations

The remaining input is the arithmetic logarithmic-depth certificate. All
convergence, sparse-event counts, radix-prime clearing, finite prime support,
and analytic estimates are supplied by proved general theorems.
-/

noncomputable section
open Filter
open scoped BigOperators Topology Classical

namespace XiFamily

theorem normalInBase_finite_combination_of_depth {p b a d : ℕ} [Fact p.Prime]
    (S : Finset ℕ) (q : ℕ → ℚ) (q₀ : ℚ) (C : ℤ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hd : 2 ≤ d) (hS : ∀ c ∈ S, 2 ≤ c)
    (hpb : ¬ p ∣ b)
    (hshallow : Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (combinationShallow p b a S q q₀ d C)).card : ℝ) / N)
      atTop (𝓝 0)) :
    StonehamNormality.NormalInBase b ((q₀ : ℝ) + ∑ c ∈ S, (q c : ℝ) * xi b c a) := by
  let A := 2 * S.card
  let C₀ := q₀.den * ∏ c ∈ S, (q c).den
  let T := 288 * (8 * d) * 2 ^ (2 * A)
  let P := combinationPrimeContainer S (fun _ => a) id q q₀
  let support := nonbasePrimeSupport b P
  let clear := combinationClearingBad S (fun _ => a) id C₀ A T
  have hT : 0 < T := by dsimp [T]; positivity
  have hQ : depthNormalityScale d A = 2 ^ T := rfl
  have haS : ∀ c ∈ S, 2 ≤ (fun _ : ℕ => a) c := fun _ _ => ha
  apply normalInBase_of_logarithmic_depth (p := p) b d A C₀ support hb hd
    (nonbasePrimeSupport_pos b P) (nonbasePrimeSupport_coprime b P) C
    ((q₀ : ℝ) + ∑ c ∈ S, (q c : ℝ) * xi b c a)
    (combinationTruncation b a S q q₀) (combinationEvent a S)
    (combinationShallow p b a S q q₀ d C) clear
  · exact rational_combination_error_tendsto_zero S b id (fun _ => a) q q₀ hb
  · exact combinationTruncation_add_of_no_new_terms S q q₀
  · intro n hn
    exact rational_combination_den_le S b id (fun _ => a) q q₀ n haS hS hn.ne'
  · exact hshallow
  · intro n hsn hEn
    exact combinationTruncation_depth_of_not_shallow_not_event S q q₀ C hb hpb hsn hEn
  · refine ⟨2, ((S.card * (T + 1) ^ 2 : ℕ) : ℝ), by positivity, ?_⟩
    intro B
    rw [hQ]
    have hscale : (2 ^ T) ^ B ≤ (2 ^ T) ^ (B + 1) :=
      Nat.pow_le_pow_right (by positivity) (by omega)
    have hsub : (Finset.range ((2 ^ T) ^ B)).filter (combinationEvent a S) ⊆
        (Finset.range ((2 ^ T) ^ (B + 1) + 1)).filter (unionIndex S (fun _ => a) id) := by
      intro m hm
      obtain ⟨hmr, hmE⟩ := Finset.mem_filter.mp hm
      refine Finset.mem_filter.mpr ⟨?_, hmE⟩
      apply Finset.mem_range.mpr
      have := Finset.mem_range.mp hmr
      omega
    have hcard := (Finset.card_le_card hsub).trans
      (unionIndex_card_at_scale_le S (fun _ => a) id haS hS T B)
    exact_mod_cast hcard
  · rw [hQ]
    exact combinationClearingBad_density_zero S (fun _ => a) id haS hS C₀ A T hT
  · intro B n hn hbad
    have hscale : (2 ^ T) ^ B ≤ (2 ^ T) ^ (B + 1) :=
      Nat.pow_le_pow_right (by positivity) (by omega)
    have hn' : n ≤ (2 ^ T) ^ (B + 1) := by
      rw [hQ] at hn
      exact hn.trans hscale
    have hc := finiteXiTruncation_outside_buffer S b id (fun _ => a) q q₀ T B
      hb haS hS hn' hbad 1
    refine ⟨hc.1, ?_⟩
    simpa only [Int.cast_one, one_mul, finiteXiTruncation, combinationTruncation,
      id_eq, support, P] using hc.2.2

end XiFamily
