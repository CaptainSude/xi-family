import StonehamNormality.XiAnalyticTransfer

/-! Concrete supported-denominator input for the exceptional-set transfer. -/

noncomputable section
open Filter
open scoped BigOperators Topology Classical

namespace StonehamNormality

def xiOrbitScale (M d : ℕ) : ℕ := 2 ^ (288 * M * 2 ^ d)

def xiOrbitErrorScale (M d : ℕ) : ℕ := 2 ^ (288 * M * 2 ^ d - 1)

/-- A reduced rational representative in the explicit denominator window.
Applying this to `h * R n` handles a fixed Fourier frequency exactly. -/
def XiRationalWindow (S M d B : ℕ) (r : ℚ) : Prop :=
  ∃ (q : ℕ), 0 < q ∧
    2 ^ ((144 * 2 ^ d) * B) ≤ q ∧
    q ≤ 2 ^ (((144 * M * d + 576 * M) * 2 ^ d) * B) ∧
    (∀ p : ℕ, p.Prime → p ∣ q → p ∣ S) ∧
    ∃ (A : ℤ), IsUnit (A : ZMod q) ∧ r = (A : ℚ) / q

/-- The global character estimate applies uniformly to every rational in the
denominator window, including every starting position of the sparse sequence. -/
theorem xi_rational_window_orbit_bound
    (b S M d : ℕ) (hb : 1 < b) (hS : 0 < S)
    (hcop : b.Coprime S) (hM : 1 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (h : ℤ) (r : ℚ), XiRationalWindow S M d B ((h : ℚ) * r) →
      ∀ L ≤ (xiOrbitScale M d) ^ B,
        ‖∑ i ∈ Finset.range L, fourier (T := 1) h
          ((((b : ℚ) ^ i * r : ℚ) : ℝ) : UnitAddCircle)‖ ≤
          K * (xiOrbitErrorScale M d : ℝ) ^ B := by
  obtain ⟨K, hK, hglobal⟩ := xi_fixed_support_global_character_bound b S M d hb hS hcop hM
  refine ⟨K, hK, ?_⟩
  filter_upwards [hglobal] with B hB
  intro h r hr L hL
  obtain ⟨q, hq, hql, hqu, hs, A, hA, hrepr⟩ := hr
  letI : NeZero q := ⟨hq.ne'⟩
  have hlen : L ≤ 2 ^ ((288 * M * 2 ^ d) * B) := by
    simpa only [xiOrbitScale, ← pow_mul] using hL
  have heq := fourier_rational_radix_eq_stdAddChar b h A r hrepr
  simp_rw [heq]
  have hh := hB q hql hqu hs A hA L hlen
  simpa only [xiOrbitErrorScale, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul] using hh

/-- Every fixed polynomial number of cuts is absorbed by a geometric saving. -/
theorem xi_polynomial_scale_error_tendsto_zero
    (Q V k : ℕ) (hV : 0 < V) (hVQ : V < Q) (C D : ℝ) :
    Tendsto (fun B : ℕ =>
      ((D * (((B + 1 : ℕ) : ℝ) + 1) ^ k + 1) * C * (V : ℝ) ^ (B + 1)) /
        (Q : ℝ) ^ B) atTop (𝓝 0) := by
  let r : ℝ := (V : ℝ) / Q
  have hQ : 0 < Q := hV.trans hVQ
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := (div_lt_one hQr).mpr (by exact_mod_cast hVQ)
  have hp := tendsto_pow_const_mul_const_pow_of_lt_one k hr0.le hr1
  have hshift := hp.comp (tendsto_add_atTop_nat 2)
  have hpoly : Tendsto (fun B : ℕ => ((B : ℝ) + 2) ^ k * r ^ B) atTop (𝓝 0) := by
    convert hshift.div_const (r ^ 2) using 1
    · ext B
      simp only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat, pow_add]
      field_simp
    · simp
  have hplain := tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
  have hsum := (hpoly.const_mul (D * C * V)).add (hplain.const_mul (C * V))
  convert hsum using 1
  · ext B
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    dsimp [r]
    rw [div_pow]
    ring
  · simp

/-- Normality from a sparse rational approximation with fixed prime support,
polynomial denominator bounds, and a density-zero exceptional set.

The assumptions are arithmetic and approximation statements only. Character
cancellation is supplied by the proved arbitrary-polynomial orbit estimate.
The number of insertion events may be any fixed polynomial in the logarithmic
scale, in particular the quadratic count of the Xi family.
-/
theorem xi_normalInBase_of_sparse_supported_denominators
    (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (R : ℕ → ℚ) (events : ℕ → Prop)
    (happrox : Tendsto (fun n => (b : ℝ) ^ n * x - (R n : ℝ)) atTop (𝓝 0))
    (hrec : ∀ n t : ℕ,
      (∀ m : ℕ, events m → m ≤ n + t → m ≤ n) →
      R (n + t) = (b : ℚ) ^ t * R n)
    (hdata : ∀ h : ℤ, h ≠ 0 →
      ∃ (M d S k : ℕ) (D : ℝ) (bad : ℕ → ℕ → Prop),
        1 ≤ M ∧ 0 < S ∧ b.Coprime S ∧ 0 ≤ D ∧
        Tendsto (fun B : ℕ =>
          (((Finset.range ((xiOrbitScale M d) ^ (B + 1))).filter (bad (B + 1))).card : ℝ) /
            (xiOrbitScale M d : ℝ) ^ B) atTop (𝓝 0) ∧
        (∀ᶠ B : ℕ in atTop,
          (((Finset.range ((xiOrbitScale M d) ^ B)).filter events).card : ℝ) ≤
            D * ((B : ℝ) + 1) ^ k) ∧
        ∀ᶠ B : ℕ in atTop, ∀ n ≤ (xiOrbitScale M d) ^ B,
          ¬ bad B n → XiRationalWindow S M d B ((h : ℚ) * R n)) :
    NormalInBase b x := by
  apply normalInBase_of_fourier b hb x
  apply xi_radix_fourier_of_sparse_orbits_with_bad b x R events happrox hrec
  intro h hh
  obtain ⟨M, d, S, k, D, bad, hM, hS, hcop, hD, hbad, hcount, hgood⟩ := hdata h hh
  obtain ⟨K, hK, hbound⟩ := xi_rational_window_orbit_bound b S M d (by omega) hS hcop hM
  let Q := xiOrbitScale M d
  let V := xiOrbitErrorScale M d
  have hs : 1 ≤ (2 : ℕ) ^ d := one_le_pow₀ (by norm_num)
  have ht : 1 ≤ 288 * M * 2 ^ d := by nlinarith
  have hQ : 1 < Q := by
    dsimp [Q, xiOrbitScale]
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hV : 0 < V := by dsimp [V, xiOrbitErrorScale]; positivity
  have hVQ : V < Q := by
    dsimp [V, Q, xiOrbitErrorScale, xiOrbitScale]
    exact (pow_lt_pow_iff_right₀ (by norm_num : 1 < (2 : ℕ))).2 (by omega)
  refine ⟨Q, bad, (fun B => K * (V : ℝ) ^ B), hQ,
    (fun B => by positivity), hbad, ?_, ?_⟩
  · have hlim := xi_polynomial_scale_error_tendsto_zero Q V k hV hVQ K D
    apply squeeze_zero' (Eventually.of_forall (fun B => by positivity)) ?_ hlim
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hcount] with B hc
    have hh := mul_le_mul_of_nonneg_right (add_le_add_right hc 1)
      (show 0 ≤ K * (V : ℝ) ^ (B + 1) by positivity)
    have hd := div_le_div_of_nonneg_right hh
      (show 0 ≤ (Q : ℝ) ^ B by positivity)
    simpa [add_comm, mul_assoc] using hd
  · filter_upwards [hgood, hbound] with B hg ho
    intro n t hn hnt
    change n + t ≤ (xiOrbitScale M d) ^ B at hnt
    exact ho h (R n) (hg n (by omega) hn) t (by omega)

end StonehamNormality
