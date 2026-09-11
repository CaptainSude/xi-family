import StonehamNormality.GeneralRadix
import StonehamNormality.NormalityTransfer

/-!
# Arbitrary-radix transfer from sparse rational orbits

These criteria handle all prefix lengths, not only selected endpoints. The
rational recurrence uses the requested radix; the auxiliary geometric scales
are independent parameters.
-/

noncomputable section
open Filter
open scoped BigOperators Topology Classical

namespace StonehamNormality
theorem radix_fourier_of_approximation_scale_bounds
    (b : ℕ) (x : ℝ) (R : ℕ → ℚ) (Q : ℕ) (hQ : 1 < Q)
    (happrox : Tendsto (fun n => (b : ℝ) ^ n * x - (R n : ℝ)) atTop (𝓝 0))
    (hbound : ∀ h : ℤ, h ≠ 0 → ∃ E : ℕ → ℝ,
      Tendsto (fun B : ℕ => E (B + 1) / (Q : ℝ) ^ B) atTop (𝓝 0) ∧
      ∀ᶠ B in atTop, ∀ M : ℕ, M < Q ^ B →
        ‖∑ n ∈ Finset.range M,
          fourier (T := 1) h ((R n : ℝ) : UnitAddCircle)‖ ≤ E B) :
    ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun M : ℕ => (M : ℝ)⁻¹ •
        ∑ i ∈ Finset.range M, fourier (T := 1) h
          (((b : ℝ) ^ i * x : ℝ) : UnitAddCircle)) atTop (𝓝 0) := by
  intro h hh
  apply fourier_average_tendsto_of_approximation h happrox
  obtain ⟨E, hdecay, hprefix⟩ := hbound h hh
  exact average_tendsto_zero_of_eventual_scale_prefix_bound
    (fun n => fourier (T := 1) h ((R n : ℝ) : UnitAddCircle)) Q E hQ hdecay hprefix

/-- A complete reusable criterion for sparse-event rational approximations.
The event counts, discarded prefixes, and orbit estimates are kept separate. -/
theorem radix_fourier_of_sparse_rational_orbits
    (b : ℕ) (x : ℝ) (R : ℕ → ℚ) (S : ℕ → Prop) (Q : ℕ) (hQ : 1 < Q)
    (happrox : Tendsto (fun n => (b : ℝ) ^ n * x - (R n : ℝ)) atTop (𝓝 0))
    (hrec : ∀ n t : ℕ,
      (∀ m : ℕ, S m → m ≤ n + t → m ≤ n) →
      R (n + t) = (b : ℚ) ^ t * R n)
    (hcontrol : ∀ h : ℤ, h ≠ 0 →
      ∃ (A : ℕ → ℕ) (K D : ℕ → ℝ),
        (∀ B, 0 ≤ K B) ∧
        Tendsto (fun B : ℕ =>
          ((A (B + 1) : ℝ) + (D (B + 1) + 1) * K (B + 1)) /
            (Q : ℝ) ^ B) atTop (𝓝 0) ∧
        ∀ᶠ B in atTop,
          (((Finset.range (Q ^ B)).filter S).card : ℝ) ≤ D B ∧
          ∀ n t : ℕ, A B ≤ n → n + t ≤ Q ^ B →
            ‖∑ i ∈ Finset.range t, fourier (T := 1) h
              ((((b : ℚ) ^ i * R n : ℚ) : ℝ) : UnitAddCircle)‖ ≤ K B) :
    ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun M : ℕ => (M : ℝ)⁻¹ •
        ∑ i ∈ Finset.range M, fourier (T := 1) h
          (((b : ℝ) ^ i * x : ℝ) : UnitAddCircle)) atTop (𝓝 0) := by
  apply radix_fourier_of_approximation_scale_bounds b x R Q hQ happrox
  intro h hh
  obtain ⟨A, K, D, hK, hdecay, hgood⟩ := hcontrol h hh
  refine ⟨fun B => (A B : ℝ) + (D B + 1) * K B, hdecay, ?_⟩
  filter_upwards [hgood] with B hB
  intro M hM
  let F : ℚ → ℂ := fun q => fourier (T := 1) h ((q : ℝ) : UnitAddCircle)
  have hp := norm_sum_rational_prefix_le R S F b M (A B) (K B) (hK B)
    (fun q => (fourier_norm_one h _).le) hrec
    (fun n t hn hnt => hB.2 n t hn (hnt.trans hM.le))
  have hsub : (Finset.range M).filter S ⊆ (Finset.range (Q ^ B)).filter S := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnM, hnS⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hnM).trans_le hM.le), hnS⟩
  have hcard : (((Finset.range M).filter S).card : ℝ) ≤ D B := by
    exact (show (((Finset.range M).filter S).card : ℝ) ≤
        (((Finset.range (Q ^ B)).filter S).card : ℝ) by
      exact_mod_cast Finset.card_le_card hsub).trans hB.1
  apply hp.trans
  simpa only [add_comm] using (add_le_add_left
    (mul_le_mul_of_nonneg_right (add_le_add_right hcard 1) (hK B)) (A B : ℝ))

/-- Convenient geometric-scale version: a linear number of events, a discarded
prefix below `U^B`, and orbit bounds of size `C * V^B`, with `U,V < Q`.
All thresholds and orbit constants may depend on the Fourier frequency. -/
theorem radix_fourier_of_linear_event_geometric_orbits
    (b : ℕ) (x : ℝ) (R : ℕ → ℚ) (S : ℕ → Prop) (Q U V : ℕ)
    (hQ : 1 < Q) (hU : U < Q) (hV : V < Q) (D : ℝ)
    (happrox : Tendsto (fun n => (b : ℝ) ^ n * x - (R n : ℝ)) atTop (𝓝 0))
    (hrec : ∀ n t : ℕ,
      (∀ m : ℕ, S m → m ≤ n + t → m ≤ n) →
      R (n + t) = (b : ℚ) ^ t * R n)
    (hcount : ∀ᶠ (B : ℕ) in atTop,
      (((Finset.range (Q ^ B)).filter S).card : ℝ) ≤ D * ((B : ℝ) + 1))
    (horbit : ∀ h : ℤ, h ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ (B : ℕ) in atTop, ∀ n t : ℕ, U ^ B ≤ n → n + t ≤ Q ^ B →
        ‖∑ i ∈ Finset.range t, fourier (T := 1) h
          ((((b : ℚ) ^ i * R n : ℚ) : ℝ) : UnitAddCircle)‖ ≤ C * (V : ℝ) ^ B) :
    ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun M : ℕ => (M : ℝ)⁻¹ •
        ∑ i ∈ Finset.range M, fourier (T := 1) h
          (((b : ℝ) ^ i * x : ℝ) : UnitAddCircle)) atTop (𝓝 0) := by
  apply radix_fourier_of_sparse_rational_orbits b x R S Q hQ happrox hrec
  intro h hh
  obtain ⟨C, hC, hbound⟩ := horbit h hh
  refine ⟨fun B => U ^ B, fun B => C * (V : ℝ) ^ B,
    fun B => D * ((B : ℝ) + 1), (fun B => by positivity), ?_, ?_⟩
  · convert geometric_scale_error_tendsto_zero Q U V (by omega) hU hV (C * D) C using 1
    ext B
    simp only [Nat.cast_pow]
    ring
  · filter_upwards [hcount, hbound] with B hc ho
    exact ⟨hc, ho⟩

end StonehamNormality
