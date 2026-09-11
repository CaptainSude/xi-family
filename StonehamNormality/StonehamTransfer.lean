import StonehamNormality.NormalityTransfer
import StonehamNormality.StonehamSeries

/-!
# The analytic interface for actual Stoneham combinations

Support counts, rational approximation, and exact recurrence are proved here.
The final interfaces assume only quantitative bounds for the indicated finite
rational-orbit character sums, leaving those arithmetic estimates separate.
-/

noncomputable section

open Filter
open scoped BigOperators Topology Classical

namespace StonehamNormality

def IsThreeFiveIndex (m : ℕ) : Prop :=
  IsStonehamIndex 3 m ∨ IsStonehamIndex 5 m

/-- Each power index below `2^B` comes from an exponent below `B`. -/
theorem stoneham_support_count_lt_two_pow (p B : ℕ) (hp : 2 ≤ p) :
    ((Finset.range (2 ^ B)).filter (IsStonehamIndex p)).card ≤ B := by
  have hs : (Finset.range (2 ^ B)).filter (IsStonehamIndex p) ⊆
      (Finset.range B).image (fun k : ℕ => p ^ k) := by
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmB, k, hk, rfl⟩
    have hpow : (2 : ℕ) ^ k ≤ p ^ k := Nat.pow_le_pow_left hp k
    have hkB : k < B := (pow_lt_pow_iff_right₀ (by norm_num : 1 < (2 : ℕ))).mp
      (hpow.trans_lt (Finset.mem_range.mp hmB))
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hkB, rfl⟩
  exact (Finset.card_le_card hs).trans (by simpa using
    (Finset.card_image_le (s := Finset.range B) (f := fun k : ℕ => p ^ k)))

theorem three_five_support_count_lt_two_pow (B : ℕ) :
    ((Finset.range (2 ^ B)).filter IsThreeFiveIndex).card ≤ 2 * B := by
  have heq : (Finset.range (2 ^ B)).filter IsThreeFiveIndex =
      ((Finset.range (2 ^ B)).filter (IsStonehamIndex 3)) ∪
      ((Finset.range (2 ^ B)).filter (IsStonehamIndex 5)) := by
    ext m
    simp only [Finset.mem_filter, IsThreeFiveIndex, Finset.mem_union]
    tauto
  rw [heq]
  exact (Finset.card_union_le _ _).trans (by
    have h3 := stoneham_support_count_lt_two_pow 3 B (by norm_num)
    have h5 := stoneham_support_count_lt_two_pow 5 B (by norm_num)
    omega)

theorem three_five_support_count_scale (B : ℕ) :
    (((Finset.range ((2 ^ 20) ^ B)).filter IsThreeFiveIndex).card : ℝ) ≤
      40 * ((B : ℝ) + 1) := by
  have h := three_five_support_count_lt_two_pow (20 * B)
  rw [pow_mul] at h
  have hn : ((Finset.range ((2 ^ 20) ^ B)).filter IsThreeFiveIndex).card ≤
      40 * B := by omega
  have hr : (((Finset.range ((2 ^ 20) ^ B)).filter IsThreeFiveIndex).card : ℝ) ≤
      40 * (B : ℝ) := by exact_mod_cast hn
  linarith

theorem stoneham_support_count_scale (p B : ℕ) (hp : 2 ≤ p) :
    (((Finset.range ((2 ^ 20) ^ B)).filter (IsStonehamIndex p)).card : ℝ) ≤
      20 * ((B : ℝ) + 1) := by
  have h := stoneham_support_count_lt_two_pow p (20 * B) hp
  rw [pow_mul] at h
  have hr : (((Finset.range ((2 ^ 20) ^ B)).filter (IsStonehamIndex p)).card : ℝ) ≤
      20 * (B : ℝ) := by exact_mod_cast h
  linarith

/-- The signed approximation estimate needs no positivity of the coefficients. -/
theorem stoneham_rat_linear_combination_error_tendsto_zero
    (p q : ℕ) (u v : ℚ) :
    Tendsto (fun n : ℕ =>
      (2 : ℝ) ^ n * ((u : ℝ) * stoneham p + (v : ℝ) * stoneham q) -
        ((u * stonehamTruncation p n + v * stonehamTruncation q n : ℚ) : ℝ))
      atTop (𝓝 0) := by
  have he : (fun n : ℕ =>
      (2 : ℝ) ^ n * ((u : ℝ) * stoneham p + (v : ℝ) * stoneham q) -
        ((u * stonehamTruncation p n + v * stonehamTruncation q n : ℚ) : ℝ)) =
      (fun n : ℕ =>
        (u : ℝ) * ((2 : ℝ) ^ n * stoneham p - (stonehamTruncation p n : ℝ)) +
        (v : ℝ) * ((2 : ℝ) ^ n * stoneham q - (stonehamTruncation q n : ℝ))) := by
    funext n
    push_cast
    ring
  rw [he]
  simpa using ((stonehamTruncation_error_tendsto_zero p).const_mul (u : ℝ)).add
    ((stonehamTruncation_error_tendsto_zero q).const_mul (v : ℝ))

theorem stoneham_rat_linear_combination_add_of_no_new_terms
    (p q : ℕ) (u v : ℚ) (n t : ℕ)
    (hnew : ∀ m : ℕ, IsStonehamIndex p m ∨ IsStonehamIndex q m →
      m ≤ n + t → m ≤ n) :
    u * stonehamTruncation p (n + t) + v * stonehamTruncation q (n + t) =
      (2 : ℚ) ^ t * (u * stonehamTruncation p n + v * stonehamTruncation q n) := by
  rw [stonehamTruncation_add_of_no_new_terms p n t
      (fun m hm hmn => hnew m (Or.inl hm) hmn),
    stonehamTruncation_add_of_no_new_terms q n t
      (fun m hm hmn => hnew m (Or.inr hm) hmn)]
  ring

/-- All remaining input is the per-frequency finite rational-orbit estimate.
The approximation, support count, recurrence, and all-prefix limit are discharged. -/
theorem stoneham_three_five_rat_binaryNormal_of_orbit_bounds (u v : ℚ)
    (horbit : ∀ h : ℤ, h ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ (B : ℕ) in atTop, ∀ n t : ℕ,
        2 ^ (18 * B) ≤ n → n + t ≤ 2 ^ (20 * B) →
        ‖∑ i ∈ Finset.range t, fourier (T := 1) h
          ((((2 : ℚ) ^ i *
            (u * stonehamTruncation 3 n + v * stonehamTruncation 5 n) : ℚ) : ℝ) :
              UnitAddCircle)‖ ≤ C * (2 : ℝ) ^ (19 * B)) :
    XiNormality.BinaryNormal ((u : ℝ) * stoneham 3 + (v : ℝ) * stoneham 5) := by
  apply binaryNormal_of_linear_event_geometric_orbits
    ((u : ℝ) * stoneham 3 + (v : ℝ) * stoneham 5)
    (fun n => u * stonehamTruncation 3 n + v * stonehamTruncation 5 n)
    IsThreeFiveIndex (2 ^ 20) (2 ^ 18) (2 ^ 19)
    (by norm_num) (by norm_num) (by norm_num) 40
  · exact stoneham_rat_linear_combination_error_tendsto_zero 3 5 u v
  · intro n t hnew
    exact stoneham_rat_linear_combination_add_of_no_new_terms 3 5 u v n t hnew
  · exact Eventually.of_forall three_five_support_count_scale
  · intro h hh
    obtain ⟨C, hC, hbound⟩ := horbit h hh
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with B hB
    intro n t hn hnt
    have hn' : 2 ^ (18 * B) ≤ n := by simpa only [pow_mul] using hn
    have hnt' : n + t ≤ 2 ^ (20 * B) := by simpa only [pow_mul] using hnt
    simpa only [pow_mul, Nat.cast_pow, Nat.cast_ofNat] using hB n t hn' hnt'

/-- Integer coefficients are the immediate target for the mixed-modulus bound. -/
theorem stoneham_three_five_binaryNormal_of_orbit_bounds (u v : ℤ)
    (horbit : ∀ h : ℤ, h ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ (B : ℕ) in atTop, ∀ n t : ℕ,
        2 ^ (18 * B) ≤ n → n + t ≤ 2 ^ (20 * B) →
        ‖∑ i ∈ Finset.range t, fourier (T := 1) h
          ((((2 : ℚ) ^ i *
            ((u : ℚ) * stonehamTruncation 3 n + (v : ℚ) * stonehamTruncation 5 n) : ℚ) :
              ℝ) : UnitAddCircle)‖ ≤ C * (2 : ℝ) ^ (19 * B)) :
    XiNormality.BinaryNormal ((u : ℝ) * stoneham 3 + (v : ℝ) * stoneham 5) := by
  simpa only [Rat.cast_intCast] using
    stoneham_three_five_rat_binaryNormal_of_orbit_bounds (u : ℚ) (v : ℚ) horbit

/-- A one-coordinate interface, in the same scales as the mixed case. -/
theorem stoneham_binaryNormal_of_orbit_bounds (p : ℕ) (hp : 2 ≤ p)
    (horbit : ∀ h : ℤ, h ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ (B : ℕ) in atTop, ∀ n t : ℕ,
        2 ^ (18 * B) ≤ n → n + t ≤ 2 ^ (20 * B) →
        ‖∑ i ∈ Finset.range t, fourier (T := 1) h
          ((((2 : ℚ) ^ i * stonehamTruncation p n : ℚ) : ℝ) :
            UnitAddCircle)‖ ≤ C * (2 : ℝ) ^ (19 * B)) :
    XiNormality.BinaryNormal (stoneham p) := by
  apply binaryNormal_of_linear_event_geometric_orbits
    (stoneham p) (stonehamTruncation p) (IsStonehamIndex p)
    (2 ^ 20) (2 ^ 18) (2 ^ 19) (by norm_num) (by norm_num) (by norm_num) 20
  · exact stonehamTruncation_error_tendsto_zero p
  · exact stonehamTruncation_add_of_no_new_terms p
  · exact Eventually.of_forall (fun B => stoneham_support_count_scale p B hp)
  · intro h hh
    obtain ⟨C, hC, hbound⟩ := horbit h hh
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with B hB
    intro n t hn hnt
    have hn' : 2 ^ (18 * B) ≤ n := by simpa only [pow_mul] using hn
    have hnt' : n + t ≤ 2 ^ (20 * B) := by simpa only [pow_mul] using hnt
    simpa only [pow_mul, Nat.cast_pow, Nat.cast_ofNat] using hB n t hn' hnt'

/-- Fourier cancellation, before applying any normality criterion. -/
theorem stoneham_three_five_rat_fourier_average_of_orbit_bounds (u v : ℚ)
    (horbit : ∀ h : ℤ, h ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ (B : ℕ) in atTop, ∀ n t : ℕ,
        2 ^ (18 * B) ≤ n → n + t ≤ 2 ^ (20 * B) →
        ‖∑ i ∈ Finset.range t, fourier (T := 1) h
          ((((2 : ℚ) ^ i *
            (u * stonehamTruncation 3 n + v * stonehamTruncation 5 n) : ℚ) : ℝ) :
              UnitAddCircle)‖ ≤ C * (2 : ℝ) ^ (19 * B)) :
    ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun M : ℕ => (M : ℝ)⁻¹ •
        ∑ i ∈ Finset.range M, fourier (T := 1) h
          (((2 : ℝ) ^ i * ((u : ℝ) * stoneham 3 + (v : ℝ) * stoneham 5) : ℝ) :
            UnitAddCircle)) atTop (𝓝 0) := by
  apply fourier_average_of_linear_event_geometric_orbits
    ((u : ℝ) * stoneham 3 + (v : ℝ) * stoneham 5)
    (fun n => u * stonehamTruncation 3 n + v * stonehamTruncation 5 n)
    IsThreeFiveIndex (2 ^ 20) (2 ^ 18) (2 ^ 19)
    (by norm_num) (by norm_num) (by norm_num) 40
  · exact stoneham_rat_linear_combination_error_tendsto_zero 3 5 u v
  · intro n t hnew
    exact stoneham_rat_linear_combination_add_of_no_new_terms 3 5 u v n t hnew
  · exact Eventually.of_forall three_five_support_count_scale
  · intro h hh
    obtain ⟨C, hC, hbound⟩ := horbit h hh
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with B hB
    intro n t hn hnt
    have hn' : 2 ^ (18 * B) ≤ n := by simpa only [pow_mul] using hn
    have hnt' : n + t ≤ 2 ^ (20 * B) := by simpa only [pow_mul] using hnt
    simpa only [pow_mul, Nat.cast_pow, Nat.cast_ofNat] using hB n t hn' hnt'

/-- Integer coefficients are the immediate target for the mixed-modulus bound. -/
theorem stoneham_three_five_fourier_average_of_orbit_bounds (u v : ℤ)
    (horbit : ∀ h : ℤ, h ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ (B : ℕ) in atTop, ∀ n t : ℕ,
        2 ^ (18 * B) ≤ n → n + t ≤ 2 ^ (20 * B) →
        ‖∑ i ∈ Finset.range t, fourier (T := 1) h
          ((((2 : ℚ) ^ i *
            ((u : ℚ) * stonehamTruncation 3 n + (v : ℚ) * stonehamTruncation 5 n) : ℚ) :
              ℝ) : UnitAddCircle)‖ ≤ C * (2 : ℝ) ^ (19 * B)) :
    ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun M : ℕ => (M : ℝ)⁻¹ •
        ∑ i ∈ Finset.range M, fourier (T := 1) h
          (((2 : ℝ) ^ i * ((u : ℝ) * stoneham 3 + (v : ℝ) * stoneham 5) : ℝ) :
            UnitAddCircle)) atTop (𝓝 0) := by
  simpa only [Rat.cast_intCast] using
    stoneham_three_five_rat_fourier_average_of_orbit_bounds (u : ℚ) (v : ℚ) horbit

end StonehamNormality
