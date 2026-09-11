import XiFamilyClearing
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Sparse clearing buffers on exponential scales

Closed buffers include insertion positions themselves. Their cubic size
bound on the exponent scale is negligible compared with the scale length.
Outside the buffers, old rational denominators have had enough radix
iterations to clear every radix prime.
-/

noncomputable section
open Filter
open scoped BigOperators Topology Classical

namespace XiFamily

def eventClearingBuffer (E : ℕ → Prop) (N t : ℕ) : Finset ℕ :=
  Finset.range (t + 1) ∪
    ((Finset.range (N + 1)).filter E).biUnion (fun m => Finset.Icc m (m + t))

theorem eventClearingBuffer_card_le (E : ℕ → Prop) (N t : ℕ) :
    (eventClearingBuffer E N t).card ≤
      (t + 1) * (1 + ((Finset.range (N + 1)).filter E).card) := by
  calc
    _ ≤ (Finset.range (t + 1)).card +
        (((Finset.range (N + 1)).filter E).biUnion (fun m => Finset.Icc m (m + t))).card :=
      Finset.card_union_le _ _
    _ ≤ (t + 1) + ((Finset.range (N + 1)).filter E).card * (t + 1) := by
      simp only [Finset.card_range]
      exact Nat.add_le_add_left
        (Finset.card_biUnion_le_card_mul _ _ (t + 1) (fun m hm => by simp; omega)) _
    _ = _ := by ring

theorem outside_eventClearingBuffer {E : ℕ → Prop} {N t n : ℕ}
    (hn : n ≤ N) (hbad : n ∉ eventClearingBuffer E N t) :
    t < n ∧ ¬ E n ∧ ∀ m, E m → m ≤ n → m ≤ n - t := by
  have hnrange : n ∉ Finset.range (t + 1) :=
    fun h => hbad (Finset.mem_union_left _ h)
  have hnt : t < n := by simp only [Finset.mem_range] at hnrange; omega
  have hno : ∀ m, E m → m ≤ n → n ≤ m + t → False := by
    intro m hm hmn hdist
    apply hbad
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hm⟩, ?_⟩
    exact Finset.mem_Icc.mpr ⟨hmn, hdist⟩
  refine ⟨hnt, (fun h => hno n h le_rfl (by omega)), ?_⟩
  intro m hm hmn
  by_contra hgt
  exact hno m hm hmn (by omega)

def scaleClearingLength (C A T B : ℕ) : ℕ :=
  (Nat.log 2 C + 1) + A * (T * (B + 1) + 1)

theorem scaleClearingLength_eq (C A T B : ℕ) :
    scaleClearingLength C A T B = polynomialClearingBuffer C A ((2 ^ T) ^ (B + 1)) := by
  simp only [scaleClearingLength, polynomialClearingBuffer, ← pow_mul,
    Nat.log_pow (by norm_num : 1 < (2 : ℕ))]

theorem scaleClearingLength_le (C A T B : ℕ) :
    scaleClearingLength C A T B + 1 ≤
      (Nat.log 2 C + 2 + A * (T + 1)) * (B + 1) := by
  unfold scaleClearingLength
  nlinarith

theorem log_at_scale_le {x : ℕ} (hx : 2 ≤ x) (T B : ℕ) :
    Nat.log x ((2 ^ T) ^ (B + 1)) ≤ T * (B + 1) := by
  calc
    _ ≤ Nat.log 2 ((2 ^ T) ^ (B + 1)) := Nat.log_mono (by norm_num) hx le_rfl
    _ = _ := by rw [← pow_mul, Nat.log_pow (by norm_num)]

def unionIndex {ι : Type*} (J : Finset ι) (a c : ι → ℕ) (m : ℕ) : Prop :=
  ∃ j ∈ J, IsIndex (a j) (c j) m

theorem unionIndex_filter_eq {ι : Type*} (J : Finset ι) (a c : ι → ℕ) (N : ℕ) :
    (Finset.range (N + 1)).filter (unionIndex J a c) =
      J.biUnion (fun j => indices (a j) (c j) N) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion,
    mem_indices_iff, unionIndex, Nat.lt_succ_iff]
  aesop

theorem unionIndex_card_at_scale_le {ι : Type*} (J : Finset ι) (a c : ι → ℕ)
    (ha : ∀ j ∈ J, 2 ≤ a j) (hc : ∀ j ∈ J, 2 ≤ c j) (T B : ℕ) :
    (((Finset.range ((2 ^ T) ^ (B + 1) + 1)).filter (unionIndex J a c)).card) ≤
      (J.card * (T + 1) ^ 2) * (B + 1) ^ 2 := by
  rw [unionIndex_filter_eq]
  calc
    _ ≤ ∑ j ∈ J, (Nat.log (a j) ((2 ^ T) ^ (B + 1)) + 1) *
        (Nat.log (c j) ((2 ^ T) ^ (B + 1)) + 1) :=
      indices_union_card_le J a c _ ha hc
    _ ≤ ∑ _j ∈ J, ((T + 1) * (B + 1)) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hja := log_at_scale_le (ha j hj) T B
      have hjc := log_at_scale_le (hc j hj) T B
      have h1 : Nat.log (a j) ((2 ^ T) ^ (B + 1)) + 1 ≤ (T + 1) * (B + 1) := by nlinarith
      have h2 : Nat.log (c j) ((2 ^ T) ^ (B + 1)) + 1 ≤ (T + 1) * (B + 1) := by nlinarith
      simpa only [pow_two] using Nat.mul_le_mul h1 h2
    _ = _ := by simp [mul_pow, Nat.mul_assoc]

def combinationClearingBad {ι : Type*} (J : Finset ι) (a c : ι → ℕ)
    (C A T B : ℕ) : Finset ℕ :=
  eventClearingBuffer (unionIndex J a c) ((2 ^ T) ^ (B + 1)) (scaleClearingLength C A T B)

theorem combinationClearingBad_card_le {ι : Type*} (J : Finset ι) (a c : ι → ℕ)
    (ha : ∀ j ∈ J, 2 ≤ a j) (hc : ∀ j ∈ J, 2 ≤ c j) (C A T B : ℕ) :
    (combinationClearingBad J a c C A T B).card ≤
      ((Nat.log 2 C + 2 + A * (T + 1)) * (1 + J.card * (T + 1) ^ 2)) * (B + 1) ^ 3 := by
  apply (eventClearingBuffer_card_le _ _ _).trans
  have h1 := scaleClearingLength_le C A T B
  have hcount := unionIndex_card_at_scale_le J a c ha hc T B
  have h2 : 1 + (((Finset.range ((2 ^ T) ^ (B + 1) + 1)).filter (unionIndex J a c)).card) ≤
      (1 + J.card * (T + 1) ^ 2) * (B + 1) ^ 2 := by
    have hpow : 1 ≤ (B + 1) ^ 2 := by nlinarith
    nlinarith
  calc
    _ ≤ ((Nat.log 2 C + 2 + A * (T + 1)) * (B + 1)) *
        ((1 + J.card * (T + 1) ^ 2) * (B + 1) ^ 2) := Nat.mul_le_mul h1 h2
    _ = _ := by ring

theorem shifted_polynomial_div_pow_tendsto_zero (k : ℕ) {Q : ℝ} (hQ : 1 < Q) :
    Tendsto (fun B : ℕ => ((B + 1 : ℕ) : ℝ) ^ k / Q ^ B) atTop (𝓝 0) := by
  have h := ((tendsto_pow_const_div_const_pow_of_one_lt k hQ).comp
    (tendsto_add_atTop_nat 1)).const_mul Q
  convert h using 1
  · ext B
    simp only [Function.comp_def, pow_succ]
    field_simp
  · simp

theorem combinationClearingBad_density_zero {ι : Type*} (J : Finset ι) (a c : ι → ℕ)
    (ha : ∀ j ∈ J, 2 ≤ a j) (hc : ∀ j ∈ J, 2 ≤ c j) (C A T : ℕ) (hT : 0 < T) :
    Tendsto (fun B : ℕ =>
      ((combinationClearingBad J a c C A T B).card : ℝ) / ((2 ^ T : ℕ) : ℝ) ^ B)
      atTop (𝓝 0) := by
  let D := (Nat.log 2 C + 2 + A * (T + 1)) * (1 + J.card * (T + 1) ^ 2)
  have hQ : (1 : ℝ) < (2 ^ T : ℕ) := by
    exact_mod_cast (one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) hT.ne')
  have hlim := (shifted_polynomial_div_pow_tendsto_zero 3 hQ).const_mul (D : ℝ)
  simp only [mul_zero] at hlim
  apply squeeze_zero (fun _ => by positivity) ?_ hlim
  intro B
  calc
    _ ≤ ((D : ℝ) * ((B + 1 : ℕ) : ℝ) ^ 3) / ((2 ^ T : ℕ) : ℝ) ^ B := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast combinationClearingBad_card_le J a c ha hc C A T B
    _ = _ := by ring

def nonbasePrimeSupport (b P : ℕ) : ℕ :=
  ∏ p ∈ P.primeFactors.filter (fun p => ¬ p ∣ b), p

theorem nonbasePrimeSupport_pos (b P : ℕ) : 0 < nonbasePrimeSupport b P := by
  apply Finset.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

theorem nonbasePrimeSupport_coprime (b P : ℕ) : b.Coprime (nonbasePrimeSupport b P) := by
  apply Nat.Coprime.prod_right
  intro p hp
  obtain ⟨hpP, hpb⟩ := Finset.mem_filter.mp hp
  exact ((Nat.prime_of_mem_primeFactors hpP).coprime_iff_not_dvd.mpr hpb).symm

theorem prime_dvd_nonbasePrimeSupport {b P p : ℕ} (hp : p.Prime)
    (hP : P ≠ 0) (hpd : p ∣ P) (hpb : ¬ p ∣ b) : p ∣ nonbasePrimeSupport b P := by
  exact Finset.dvd_prod_of_mem (fun p => p)
    (Finset.mem_filter.mpr ⟨hp.mem_primeFactors hpd hP, hpb⟩)

theorem polynomialClearingBuffer_mono (C A : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    polynomialClearingBuffer C A m ≤ polynomialClearingBuffer C A n := by
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left A (Nat.add_le_add_right (Nat.log_mono_right hmn) 1)) _

/-- Generic arithmetic clearing outside sparse insertion buffers. -/
theorem outside_scale_buffer_coprime (b C A T B : ℕ) (R : ℕ → ℚ) (E : ℕ → Prop)
    (hb : 2 ≤ b)
    (hrec : ∀ n t : ℕ, (∀ m, E m → m ≤ n + t → m ≤ n) →
      R (n + t) = (b : ℚ) ^ t * R n)
    (hden : ∀ n : ℕ, 0 < n → (R n).den ≤ C * n ^ A)
    {n : ℕ} (hn : n ≤ (2 ^ T) ^ (B + 1))
    (hbad : n ∉ eventClearingBuffer E ((2 ^ T) ^ (B + 1)) (scaleClearingLength C A T B)) :
    ¬ E n ∧ b.Coprime (R n).den := by
  let t := scaleClearingLength C A T B
  obtain ⟨htn, hEn, hgap⟩ := outside_eventClearingBuffer hn hbad
  have htn' : t < n := htn
  have heq : n - t + t = n := Nat.sub_add_cancel (by omega)
  have horbit : R n = (b : ℚ) ^ t * R (n - t) := by
    have hnew : ∀ m, E m → m ≤ n - t + t → m ≤ n - t := by
      intro m hm hmn
      exact hgap m hm (by simpa only [heq] using hmn)
    simpa only [heq] using hrec (n - t) t hnew
  refine ⟨hEn, ?_⟩
  rw [horbit]
  apply (polynomial_den_cleared b C A (n - t) t (R (n - t)) hb
    (hden (n - t) (by omega)) ?_).1
  have hmono := polynomialClearingBuffer_mono C A ((Nat.sub_le n t).trans hn)
  simpa only [t, ← scaleClearingLength_eq] using hmono

/-- Integer Fourier frequencies introduce no denominator primes. -/
theorem outside_scale_buffer_frequency_support (b C A T B P : ℕ)
    (R : ℕ → ℚ) (E : ℕ → Prop) (hb : 2 ≤ b) (hP : P ≠ 0)
    (hrec : ∀ n t : ℕ, (∀ m, E m → m ≤ n + t → m ≤ n) →
      R (n + t) = (b : ℚ) ^ t * R n)
    (hden : ∀ n : ℕ, 0 < n → (R n).den ≤ C * n ^ A)
    (hprime : ∀ n p : ℕ, p.Prime → p ∣ (R n).den → p ∣ P)
    {n : ℕ} (hn : n ≤ (2 ^ T) ^ (B + 1))
    (hbad : n ∉ eventClearingBuffer E ((2 ^ T) ^ (B + 1)) (scaleClearingLength C A T B))
    (h : ℤ) :
    ¬ E n ∧ b.Coprime (((h : ℚ) * R n).den) ∧
      ∀ p : ℕ, p.Prime → p ∣ ((h : ℚ) * R n).den → p ∣ nonbasePrimeSupport b P := by
  obtain ⟨hEn, hcop⟩ := outside_scale_buffer_coprime b C A T B R E hb hrec hden hn hbad
  have hdiv : ((h : ℚ) * R n).den ∣ (R n).den := by simpa using Rat.mul_den_dvd (h : ℚ) (R n)
  refine ⟨hEn, hcop.of_dvd_right hdiv, ?_⟩
  intro p hp hpd
  have hpd' := hpd.trans hdiv
  apply prime_dvd_nonbasePrimeSupport hp hP (hprime n p hp hpd')
  intro hpb
  have hp1 : p ∣ 1 := by simpa [hcop.gcd_eq_one] using Nat.dvd_gcd hpb hpd'
  exact hp.not_dvd_one hp1

def finiteXiTruncation {ι : Type*} (J : Finset ι) (b : ℕ) (c a : ι → ℕ)
    (q : ι → ℚ) (q₀ : ℚ) (n : ℕ) : ℚ :=
  q₀ * (b : ℚ) ^ n + ∑ j ∈ J, q j * truncation b (c j) (a j) n

theorem finiteXiTruncation_gap {ι : Type*} (J : Finset ι) (b : ℕ) (c a : ι → ℕ)
    (q : ι → ℚ) (q₀ : ℚ) (n t : ℕ)
    (hnew : ∀ m, unionIndex J a c m → m ≤ n + t → m ≤ n) :
    finiteXiTruncation J b c a q q₀ (n + t) =
      (b : ℚ) ^ t * finiteXiTruncation J b c a q q₀ n := by
  have hsum : (∑ j ∈ J, q j * truncation b (c j) (a j) (n + t)) =
      (b : ℚ) ^ t * ∑ j ∈ J, q j * truncation b (c j) (a j) n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [truncation_add_of_no_new_terms b (c j) (a j) n t
      (fun m hm hmn => hnew m ⟨j, hj, hm⟩ hmn)]
    ring
  unfold finiteXiTruncation
  rw [hsum, pow_add]
  ring

theorem finiteXiTruncation_outside_buffer {ι : Type*} (J : Finset ι) (b : ℕ)
    (c a : ι → ℕ) (q : ι → ℚ) (q₀ : ℚ) (T B : ℕ)
    (hb : 2 ≤ b) (ha : ∀ j ∈ J, 2 ≤ a j) (hc : ∀ j ∈ J, 2 ≤ c j)
    {n : ℕ} (hn : n ≤ (2 ^ T) ^ (B + 1))
    (hbad : n ∉ combinationClearingBad J a c
      (q₀.den * ∏ j ∈ J, (q j).den) (2 * J.card) T B) (h : ℤ) :
    ¬ unionIndex J a c n ∧ b.Coprime (((h : ℚ) * finiteXiTruncation J b c a q q₀ n).den) ∧
      ∀ p : ℕ, p.Prime → p ∣ ((h : ℚ) * finiteXiTruncation J b c a q q₀ n).den →
        p ∣ nonbasePrimeSupport b (combinationPrimeContainer J a c q q₀) := by
  apply outside_scale_buffer_frequency_support b _ _ T B _
    (finiteXiTruncation J b c a q q₀) (unionIndex J a c) hb
    (combinationPrimeContainer_pos J a c q q₀ ha hc).ne'
    (finiteXiTruncation_gap J b c a q q₀) _ _ hn hbad h
  · intro n hn
    exact rational_combination_den_le J b c a q q₀ n ha hc hn.ne'
  · intro n p hp hpd
    exact rational_combination_den_prime J b c a q q₀ n p ha hc hp hpd

def individualClearingBad (a c T B : ℕ) : Finset ℕ :=
  eventClearingBuffer (IsIndex a c) ((2 ^ T) ^ (B + 1)) (scaleClearingLength 1 2 T B)

theorem unionIndex_unit (a c : ℕ) :
    unionIndex ({()} : Finset Unit) (fun _ => a) (fun _ => c) = IsIndex a c := by
  funext m
  simp [unionIndex]

theorem individualClearingBad_card_le (a c T B : ℕ) (ha : 2 ≤ a) (hc : 2 ≤ c) :
    (individualClearingBad a c T B).card ≤
      ((2 + 2 * (T + 1)) * (1 + (T + 1) ^ 2)) * (B + 1) ^ 3 := by
  simpa [individualClearingBad, combinationClearingBad, unionIndex_unit] using
    combinationClearingBad_card_le ({()} : Finset Unit) (fun _ => a) (fun _ => c)
      (fun _ _ => ha) (fun _ _ => hc) 1 2 T B

theorem individualClearingBad_density_zero (a c T : ℕ) (ha : 2 ≤ a) (hc : 2 ≤ c)
    (hT : 0 < T) :
    Tendsto (fun B : ℕ => ((individualClearingBad a c T B).card : ℝ) /
      ((2 ^ T : ℕ) : ℝ) ^ B) atTop (𝓝 0) := by
  simpa [individualClearingBad, combinationClearingBad, unionIndex_unit] using
    combinationClearingBad_density_zero ({()} : Finset Unit) (fun _ => a) (fun _ => c)
      (fun _ _ => ha) (fun _ _ => hc) 1 2 T hT

theorem truncation_outside_clearing_buffer (b c a T B : ℕ)
    (hb : 2 ≤ b) (ha : 2 ≤ a) (hc : 2 ≤ c) {n : ℕ}
    (hn : n ≤ (2 ^ T) ^ (B + 1)) (hbad : n ∉ individualClearingBad a c T B) (h : ℤ) :
    ¬ IsIndex a c n ∧ b.Coprime (((h : ℚ) * truncation b c a n).den) ∧
      ∀ p : ℕ, p.Prime → p ∣ ((h : ℚ) * truncation b c a n).den →
        p ∣ nonbasePrimeSupport b (a * c) := by
  apply outside_scale_buffer_frequency_support b 1 2 T B (a * c)
    (truncation b c a) (IsIndex a c) hb (by positivity)
    (truncation_add_of_no_new_terms b c a) _ _ hn hbad h
  · intro n hn
    simpa using truncation_den_le_square b c a n ha hc hn.ne'
  · intro n p hp hpd
    rcases truncation_den_prime ha hc hp hpd with hpa | hpc
    · exact hpa.trans (Nat.dvd_mul_right _ _)
    · exact hpc.trans (Nat.dvd_mul_left _ _)

theorem combinationClearingBad_filtered_density_zero {ι : Type*} (J : Finset ι)
    (a c : ι → ℕ) (ha : ∀ j ∈ J, 2 ≤ a j) (hc : ∀ j ∈ J, 2 ≤ c j)
    (C A T : ℕ) (hT : 0 < T) (F : ℕ → Finset ℕ) :
    Tendsto (fun B : ℕ =>
      (((F B).filter (fun n => n ∈ combinationClearingBad J a c C A T B)).card : ℝ) /
        ((2 ^ T : ℕ) : ℝ) ^ B) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => by positivity) ?_
    (combinationClearingBad_density_zero J a c ha hc C A T hT)
  intro B
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  exact Finset.card_le_card (fun n hn => (Finset.mem_filter.mp hn).2)

theorem individualClearingBad_filtered_density_zero (a c T : ℕ)
    (ha : 2 ≤ a) (hc : 2 ≤ c) (hT : 0 < T) (F : ℕ → Finset ℕ) :
    Tendsto (fun B : ℕ =>
      (((F B).filter (fun n => n ∈ individualClearingBad a c T B)).card : ℝ) /
        ((2 ^ T : ℕ) : ℝ) ^ B) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => by positivity) ?_
    (individualClearingBad_density_zero a c T ha hc hT)
  intro B
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  exact Finset.card_le_card (fun n hn => (Finset.mem_filter.mp hn).2)

end XiFamily
