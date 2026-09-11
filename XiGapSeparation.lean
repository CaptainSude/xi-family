import XiGap
import Mathlib.NumberTheory.Padics.PadicVal.Basic

open Filter Set

namespace XiGap

private lemma finite_nonzero_abs_lower_bound {α : Type*} (s : Finset α) (f : α → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ s, f x ≠ 0 → δ ≤ |f x| := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨δ, hδ, hbound⟩ := ih
    by_cases hfa : f a = 0
    · refine ⟨δ, hδ, ?_⟩
      intro x hx hfx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact False.elim (hfx hfa)
      · exact hbound x hx hfx
    · refine ⟨min δ |f a|, lt_min hδ (abs_pos.mpr hfa), ?_⟩
      intro x hx hfx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbound x hx hfx)

/-- A translated one-dimensional real lattice has a positive gap around zero,
after its possible zero element has been removed. -/
theorem lattice_nonzero_abs_lower_bound {A : ℝ} (hA : 0 < A) (c : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℤ,
      (u : ℝ) * A + c ≠ 0 → δ ≤ |(u : ℝ) * A + c| := by
  obtain ⟨I, hI⟩ := exists_nat_gt ((1 + |c|) / A)
  obtain ⟨δ, hδ, hbound⟩ := finite_nonzero_abs_lower_bound
    (Finset.Icc (-(I : ℤ)) (I : ℤ)) (fun u : ℤ => (u : ℝ) * A + c)
  refine ⟨min 1 δ, lt_min zero_lt_one hδ, ?_⟩
  intro u hu
  by_cases hlarge : 1 ≤ |(u : ℝ) * A + c|
  · exact (min_le_left _ _).trans hlarge
  have hsmall : |(u : ℝ) * A + c| < 1 := lt_of_not_ge hlarge
  have htri : |(u : ℝ) * A| ≤ |(u : ℝ) * A + c| + |c| := by
    have h := abs_sub ((u : ℝ) * A + c) c
    simpa using h
  rw [abs_mul, abs_of_pos hA] at htri
  have hI' : 1 + |c| < (I : ℝ) * A := (div_lt_iff₀ hA).mp hI
  have hucast : |(u : ℝ)| < (I : ℝ) := by nlinarith
  have huInt : |u| ≤ (I : ℤ) := by exact_mod_cast hucast.le
  have hmem : u ∈ Finset.Icc (-(I : ℤ)) (I : ℤ) := by
    simpa only [Finset.mem_Icc, abs_le] using huInt
  exact (min_le_right _ _).trans (hbound u hmem hu)

/-- Finitely many translates of a real lattice retain a uniform nonzero gap. -/
theorem finite_lattice_nonzero_abs_lower_bound {A : ℝ} (hA : 0 < A)
    (B : ℝ) (H : Finset ℤ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h ∈ H, ∀ u : ℤ,
      (u : ℝ) * A + (h : ℝ) * B ≠ 0 →
      δ ≤ |(u : ℝ) * A + (h : ℝ) * B| := by
  classical
  induction H using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert h H hh ih =>
    obtain ⟨δ, hδ, hbound⟩ := ih
    obtain ⟨η, hη, hηbound⟩ := lattice_nonzero_abs_lower_bound hA ((h : ℝ) * B)
    refine ⟨min δ η, lt_min hδ hη, ?_⟩
    intro k hk u hu
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact (min_le_right _ _).trans (hηbound u hu)
    · exact (min_le_left _ _).trans (hbound k hk u hu)

/-- Equal weighted depth forces the difference of depth coordinates into a fixed finite set. -/
theorem depth_difference_mem {V : Finset ℤ} {e : ℕ} (he : 0 < e)
    {v w : ℤ} (hv : v ∈ V) (hw : w ∈ V) {k l : ℕ}
    (hval : v - (k : ℤ) * e = w - (l : ℤ) * e) :
    (k : ℤ) - l ∈ (V ×ˢ V).image (fun vw : ℤ × ℤ => (vw.1 - vw.2) / (e : ℤ)) := by
  have he0 : (e : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt he)
  have hmul : ((k : ℤ) - l) * e = v - w := by nlinarith [hval]
  refine Finset.mem_image.mpr ⟨(v, w), Finset.mem_product.mpr ⟨hv, hw⟩, ?_⟩
  rw [← hmul]
  exact Int.mul_ediv_cancel _ he0

/-- Uniform separation for equal valuations with coefficients in a finite alphabet.
The integer `e` is the valuation of the second multiplicative generator. -/
theorem exists_uniform_equal_valuation_separation {a b : ℝ}
    (ha : 1 < a) (hb : 1 < b) (V : Finset ℤ) {e : ℕ} (he : 0 < e) :
    ∃ Λ : ℝ, 1 < Λ ∧ ∀ (N : ℝ), 0 < N → ∀ i k j l : ℕ,
      N ≤ a ^ i * b ^ k → a ^ i * b ^ k ≤ Λ * N →
      N ≤ a ^ j * b ^ l → a ^ j * b ^ l ≤ Λ * N →
      a ^ i * b ^ k ≠ a ^ j * b ^ l → ∀ v ∈ V, ∀ w ∈ V,
      v - (k : ℤ) * e ≠ w - (l : ℤ) * e := by
  let H := (V ×ˢ V).image (fun vw : ℤ × ℤ => (vw.1 - vw.2) / (e : ℤ))
  obtain ⟨δ, hδ, hgap⟩ := finite_lattice_nonzero_abs_lower_bound
    (Real.log_pos ha) (Real.log b) H
  let Λ := Real.exp (δ / 2)
  have hΛ : 1 < Λ := by
    dsimp [Λ]
    simpa using Real.exp_lt_exp.mpr (show (0 : ℝ) < δ / 2 by linarith)
  refine ⟨Λ, hΛ, ?_⟩
  intro N hN i k j l hmlo hmhi hnlo hnhi hmn v hv w hw hval
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hm0 : 0 < a ^ i * b ^ k := mul_pos (pow_pos ha0 _) (pow_pos hb0 _)
  have hn0 : 0 < a ^ j * b ^ l := mul_pos (pow_pos ha0 _) (pow_pos hb0 _)
  have hΛ0 : 0 < Λ := lt_trans zero_lt_one hΛ
  have hml := Real.log_le_log hN hmlo
  have hmh := Real.log_le_log hm0 hmhi
  have hnl := Real.log_le_log hN hnlo
  have hnh := Real.log_le_log hn0 hnhi
  have hΛlog : Real.log (Λ * N) = δ / 2 + Real.log N := by
    rw [Real.log_mul (ne_of_gt hΛ0) (ne_of_gt hN)]
    simp [Λ]
  rw [hΛlog] at hmh hnh
  have hsmall : |Real.log (a ^ i * b ^ k) - Real.log (a ^ j * b ^ l)| ≤ δ / 2 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hne : Real.log (a ^ i * b ^ k) - Real.log (a ^ j * b ^ l) ≠ 0 := by
    intro hz
    have heq := sub_eq_zero.mp hz
    exact hmn (Real.strictMonoOn_log.injOn hm0 hn0 heq)
  have hid : Real.log (a ^ i * b ^ k) - Real.log (a ^ j * b ^ l) =
      (((i : ℤ) - j : ℤ) : ℝ) * Real.log a +
        (((k : ℤ) - l : ℤ) : ℝ) * Real.log b := by
    rw [Real.log_mul (ne_of_gt (pow_pos ha0 _)) (ne_of_gt (pow_pos hb0 _)),
      Real.log_mul (ne_of_gt (pow_pos ha0 _)) (ne_of_gt (pow_pos hb0 _))]
    simp only [Real.log_pow, Int.cast_sub, Int.cast_natCast]
    ring
  have hmem : (k : ℤ) - l ∈ H := depth_difference_mem he hv hw hval
  have hlarge := hgap ((k : ℤ) - l) hmem ((i : ℤ) - j) (by rwa [← hid])
  rw [← hid] at hlarge
  linarith

/-- Direct coefficient-alphabet interface for the valuation of a weighted Xi term. -/
theorem exists_uniform_coefficient_valuation_separation {a d p : ℕ}
    (ha : 1 < a) (hd : 1 < d) (W : Finset ℚ) (hpdepth : 0 < padicValNat p d) :
    ∃ Λ : ℝ, 1 < Λ ∧ ∀ (N : ℝ), 0 < N → ∀ i k j l : ℕ,
      N ≤ (a : ℝ) ^ i * (d : ℝ) ^ k →
      (a : ℝ) ^ i * (d : ℝ) ^ k ≤ Λ * N →
      N ≤ (a : ℝ) ^ j * (d : ℝ) ^ l →
      (a : ℝ) ^ j * (d : ℝ) ^ l ≤ Λ * N →
      (a : ℝ) ^ i * (d : ℝ) ^ k ≠ (a : ℝ) ^ j * (d : ℝ) ^ l →
      ∀ v ∈ W, ∀ w ∈ W,
      padicValRat p v - (k : ℤ) * padicValNat p d ≠
        padicValRat p w - (l : ℤ) * padicValNat p d := by
  obtain ⟨Λ, hΛ, hsep⟩ := exists_uniform_equal_valuation_separation
    (a := (a : ℝ)) (b := (d : ℝ))
    (by exact_mod_cast ha) (by exact_mod_cast hd) (W.image (padicValRat p)) hpdepth
  refine ⟨Λ, hΛ, ?_⟩
  intro N hN i k j l hmlo hmhi hnlo hnhi hmn v hv w hw
  exact hsep N hN i k j l hmlo hmhi hnlo hnhi hmn
    (padicValRat p v) (Finset.mem_image_of_mem _ hv)
    (padicValRat p w) (Finset.mem_image_of_mem _ hw)

end XiGap
