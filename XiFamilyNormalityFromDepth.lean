import XiFamilyNormalityDensity
import XiFamilyScaleDensity

/-! A reusable normality assembly from logarithmic denominator depth. -/

noncomputable section
open Filter
open scoped BigOperators Topology Classical

namespace XiFamily

def depthNormalityScale (g A : ℕ) : ℕ :=
  StonehamNormality.xiOrbitScale (8 * g) (2 * A)

def depthEarlyScale (g A : ℕ) : ℕ := 2 ^ (1152 * g * 2 ^ (2 * A))

theorem general_half_log_large_on_geometric_tail (g s B n : ℕ)
    (hg : 2 ≤ g) (hs : 1 ≤ s) (hB : 1 ≤ B)
    (hn : 2 ^ ((1152 * g * s) * B) ≤ n) :
    (288 * s) * B ≤ Nat.log g (n / 2) / 2 := by
  have hg2 : g ≤ (2 : ℕ) ^ g := Nat.lt_two_pow_self.le
  have hgp : g ^ ((576 * s) * B) ≤ 2 ^ ((576 * g * s) * B) := by
    calc
      _ ≤ (2 ^ g) ^ ((576 * s) * B) := Nat.pow_le_pow_left hg2 _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  have hmul : g ^ ((576 * s) * B) * 2 ≤ n := by
    calc
      _ ≤ 2 ^ ((576 * g * s) * B) * 2 := Nat.mul_le_mul_right 2 hgp
      _ = 2 ^ (((576 * g * s) * B) + 1) := (pow_succ _ _).symm
      _ ≤ 2 ^ ((1152 * g * s) * B) := by
        apply pow_le_pow_right₀ (by norm_num)
        have hp : 1 ≤ g * s * B := by
          have hpos : 0 < g * s * B := by positivity
          omega
        nlinarith
      _ ≤ n := hn
  have hlog : (576 * s) * B ≤ Nat.log g (n / 2) :=
    Nat.le_log_of_pow_le (by omega)
      ((Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).mpr hmul)
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).mpr
  convert hlog using 1 <;> ring

/-- Any fixed integer valuation shift, including a Fourier frequency, is
absorbed by half the logarithmic gain. -/
theorem fourier_den_lower_of_logarithmic_depth {p : ℕ} [Fact p.Prime]
    (g s B n : ℕ) (hg : 2 ≤ g) (hs : 1 ≤ s) (hB : 1 ≤ B)
    (r : ℚ) (hr : r ≠ 0) (C : ℤ) (h : ℤ) (hh : h ≠ 0)
    (hv : padicValRat p r < C - ((Nat.log g (n / 2) / 2 : ℕ) : ℤ))
    (hshift : C + padicValInt p h ≤ (((144 * s) * B : ℕ) : ℤ))
    (hn : 2 ^ ((1152 * g * s) * B) ≤ n) :
    2 ^ ((144 * s) * B) ≤ ((h : ℚ) * r).den := by
  have hk := general_half_log_large_on_geometric_tail g s B n hg hs hB hn
  apply denominator_two_pow_le_of_negative_valuation (p := p)
  rw [padicValRat.mul (by exact_mod_cast hh) hr, padicValRat.of_int]
  have hkR : (((288 * s) * B : ℕ) : ℤ) ≤
      ((Nat.log g (n / 2) / 2 : ℕ) : ℤ) := by exact_mod_cast hk
  push_cast at *
  nlinarith

/-- An arbitrary polynomial denominator upper bound fits the amplified
window with the concrete depth `2*A`. -/
theorem rational_window_of_logarithmic_depth {p : ℕ} [Fact p.Prime]
    (g A B n C₀ S : ℕ) (hg : 2 ≤ g) (hB : 1 ≤ B)
    (r : ℚ) (hr : r ≠ 0) (C : ℤ) (h : ℤ) (hh : h ≠ 0)
    (hv : padicValRat p r < C - ((Nat.log g (n / 2) / 2 : ℕ) : ℤ))
    (hshift : C + padicValInt p h ≤ (((144 * 2 ^ (2 * A)) * B : ℕ) : ℤ))
    (hn : (depthEarlyScale g A) ^ B ≤ n)
    (hnu : n ≤ (depthNormalityScale g A) ^ B)
    (hden : r.den ≤ C₀ * n ^ A) (hC₀ : C₀ ≤ 2 ^ B)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ r.den → p ∣ S) :
    StonehamNormality.XiRationalWindow S (8 * g) (2 * A) B ((h : ℚ) * r) := by
  let q := (h : ℚ) * r
  have hs : 1 ≤ (2 : ℕ) ^ (2 * A) := one_le_pow₀ (by norm_num)
  have hql : 2 ^ ((144 * 2 ^ (2 * A)) * B) ≤ q.den :=
    fourier_den_lower_of_logarithmic_depth g (2 ^ (2 * A)) B n hg hs hB r hr C h hh hv hshift
      (by simpa only [depthEarlyScale, ← pow_mul] using hn)
  have hqden : q.den ≤ C₀ * n ^ A :=
    (Nat.le_of_dvd r.den_pos (integer_mul_den_dvd h r)).trans hden
  refine ⟨q.den, q.den_pos, hql, ?_, ?_, q.num,
    StonehamNormality.rational_reduced_num_isUnit q, (Rat.num_div_den q).symm⟩
  · calc
      q.den ≤ C₀ * n ^ A := hqden
      _ ≤ 2 ^ B * ((depthNormalityScale g A) ^ B) ^ A :=
        Nat.mul_le_mul hC₀ (Nat.pow_le_pow_left hnu A)
      _ ≤ _ := by
        simp only [depthNormalityScale, StonehamNormality.xiOrbitScale, ← pow_mul, ← pow_add]
        apply pow_le_pow_right₀ (by norm_num)
        have ht : 1 ≤ g * 2 ^ (2 * A) := by nlinarith
        nlinarith
  · intro t ht htq
    exact hsupport t ht (htq.trans (integer_mul_den_dvd h r))

/-- Normality from logarithmic valuation depth outside a density-zero set.
This is the common endpoint for individual Xi values and their finite rational
linear combinations. Every analytic ingredient is already a proved theorem. -/
theorem normalInBase_of_logarithmic_depth {p : ℕ} [Fact p.Prime]
    (b g A C₀ S : ℕ) (hb : 2 ≤ b) (hg : 2 ≤ g)
    (hS : 0 < S) (hcop : b.Coprime S) (C : ℤ)
    (x : ℝ) (R : ℕ → ℚ) (events shallow : ℕ → Prop) (clear : ℕ → Finset ℕ)
    (happrox : Tendsto (fun n => (b : ℝ) ^ n * x - (R n : ℝ)) atTop (𝓝 0))
    (hrec : ∀ n t : ℕ,
      (∀ m : ℕ, events m → m ≤ n + t → m ≤ n) →
      R (n + t) = (b : ℚ) ^ t * R n)
    (hden : ∀ n : ℕ, 0 < n → (R n).den ≤ C₀ * n ^ A)
    (hshallow : Tendsto (fun N : ℕ =>
      (((Finset.range N).filter shallow).card : ℝ) / N) atTop (𝓝 0))
    (hdepth : ∀ n : ℕ, ¬ shallow n → ¬ events n →
      R n ≠ 0 ∧ padicValRat p (R n) < C - ((Nat.log g (n / 2) / 2 : ℕ) : ℤ))
    (hcount : ∃ (k : ℕ) (D : ℝ), 0 ≤ D ∧ ∀ B : ℕ,
      (((Finset.range ((depthNormalityScale g A) ^ B)).filter events).card : ℝ) ≤
        D * ((B : ℝ) + 1) ^ k)
    (hclear : Tendsto (fun B : ℕ => ((clear B).card : ℝ) /
      (depthNormalityScale g A : ℝ) ^ B) atTop (𝓝 0))
    (hclearGood : ∀ B n : ℕ, n ≤ (depthNormalityScale g A) ^ B → n ∉ clear B →
      ¬ events n ∧ (∀ t : ℕ, t.Prime → t ∣ (R n).den → t ∣ S)) :
    StonehamNormality.NormalInBase b x := by
  let Q := depthNormalityScale g A
  let U := depthEarlyScale g A
  have hs : 1 ≤ (2 : ℕ) ^ (2 * A) := one_le_pow₀ (by norm_num)
  have hQ : 1 < Q := by
    dsimp [Q, depthNormalityScale, StonehamNormality.xiOrbitScale]
    exact one_lt_pow₀ (by norm_num) (by positivity)
  have hUQ : U < Q := by
    dsimp [U, Q, depthEarlyScale, depthNormalityScale, StonehamNormality.xiOrbitScale]
    apply (pow_lt_pow_iff_right₀ (by norm_num : 1 < (2 : ℕ))).mpr
    nlinarith
  let bad : ℕ → ℕ → Prop := fun B n => shallow n ∨ n < U ^ B ∨ n ∈ clear B
  have hbad : ScaleNegligible Q bad := scaleNegligible_union
    (scaleNegligible_of_natural_density_zero Q hQ shallow hshallow)
    (scaleNegligible_union (scaleNegligible_early_prefix Q U hQ hUQ)
      (scaleNegligible_finset Q hQ clear hclear))
  obtain ⟨k, D, hD, hcount⟩ := hcount
  apply StonehamNormality.xi_normalInBase_of_sparse_supported_denominators
    b hb x R events happrox hrec
  intro h hh
  refine ⟨8 * g, 2 * A, S, k, D, bad, by omega, hS, hcop, hD,
    hbad, Eventually.of_forall hcount, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (max C₀ (Int.toNat (C + padicValInt p h))))]
    with B hB
  intro n hn hbn
  have hB1 : 1 ≤ B := (Nat.le_max_left _ _).trans hB
  have hBmax : max C₀ (Int.toNat (C + padicValInt p h)) ≤ B :=
    (Nat.le_max_right _ _).trans hB
  have hC₀B : C₀ ≤ B := (Nat.le_max_left _ _).trans hBmax
  have hshiftB : Int.toNat (C + padicValInt p h) ≤ B := (Nat.le_max_right _ _).trans hBmax
  have hshift : C + padicValInt p h ≤ (((144 * 2 ^ (2 * A)) * B : ℕ) : ℤ) := by
    have hbcast : (Int.toNat (C + padicValInt p h) : ℤ) ≤ B := by exact_mod_cast hshiftB
    have hm : B ≤ (144 * 2 ^ (2 * A)) * B := by nlinarith
    have hmR : (B : ℤ) ≤ (((144 * 2 ^ (2 * A)) * B : ℕ) : ℤ) := by exact_mod_cast hm
    have hto : C + padicValInt p h ≤ (Int.toNat (C + padicValInt p h) : ℤ) := by omega
    exact hto.trans (hbcast.trans hmR)
  have hsn : ¬ shallow n := fun hs => hbn (Or.inl hs)
  have hen : ¬ n < U ^ B := fun he => hbn (Or.inr (Or.inl he))
  have hcn : n ∉ clear B := fun hc => hbn (Or.inr (Or.inr hc))
  have hlow : U ^ B ≤ n := Nat.le_of_not_gt hen
  have hn0 : 0 < n := (by dsimp [U, depthEarlyScale]; positivity : 0 < U ^ B).trans_le hlow
  obtain ⟨hEn, hsupport⟩ := hclearGood B n hn hcn
  obtain ⟨hr, hv⟩ := hdepth n hsn hEn
  exact rational_window_of_logarithmic_depth g A B n C₀ S hg hB1
    (R n) hr C h hh hv hshift hlow hn (hden n hn0)
    (hC₀B.trans Nat.lt_two_pow_self.le) hsupport

end XiFamily
