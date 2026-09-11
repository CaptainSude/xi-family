import XiNormality.Cylinder
import XiNormality.Blocks
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Generic transfer from piecewise rational orbits to binary normality

The statements here do not assume normality of any particular constant.
They isolate finite partitions, all-prefix limits, and small perturbations.
-/

noncomputable section

open Filter
open scoped BigOperators Topology Classical

namespace StonehamNormality

theorem fourier_apply_add (k : ℤ) (x y : UnitAddCircle) :
    fourier k (x + y) = fourier k x * fourier k y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem fourier_norm_one (k : ℤ) (x : UnitAddCircle) : ‖fourier k x‖ = 1 :=
  Circle.norm_coe _

theorem norm_fourier_difference (k : ℤ) (x y : UnitAddCircle) :
    ‖fourier k x - fourier k y‖ = ‖fourier k (x - y) - 1‖ := by
  have he : fourier k x - fourier k y =
      (fourier k (x - y) - 1) * fourier k y := by
    rw [sub_mul, one_mul, ← fourier_apply_add, sub_add_cancel]
  rw [he, norm_mul, fourier_norm_one, mul_one]

/-- Real perturbations tending to zero give vanishing character differences. -/
theorem fourier_difference_tendsto_zero (k : ℤ) {x y : ℕ → ℝ}
    (h : Tendsto (fun n => x n - y n) atTop (𝓝 0)) :
    Tendsto (fun n => fourier (T := 1) k (x n : UnitAddCircle) -
      fourier (T := 1) k (y n : UnitAddCircle)) atTop (𝓝 0) := by
  have hc : Continuous (fun t : ℝ => fourier (T := 1) k (t : UnitAddCircle)) := by
    fun_prop
  have hd : Tendsto (fun n => fourier (T := 1) k
      ((x n - y n : ℝ) : UnitAddCircle) - 1) atTop (𝓝 0) := by
    simpa only [Function.comp_def, QuotientAddGroup.mk_zero,
      fourier_eval_zero, sub_self] using
      (hc.continuousAt.tendsto.comp h).sub_const 1
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_fourier_difference, QuotientAddGroup.mk_sub, norm_zero] using hd.norm

/-- Fourier cancellation is unchanged by a real approximation tending to the orbit. -/
theorem fourier_average_tendsto_of_approximation (k : ℤ) {x y : ℕ → ℝ}
    (happrox : Tendsto (fun n => x n - y n) atTop (𝓝 0))
    (haverage : Tendsto (fun M : ℕ => (M : ℝ)⁻¹ •
      ∑ n ∈ Finset.range M, fourier (T := 1) k (y n : UnitAddCircle))
      atTop (𝓝 0)) :
    Tendsto (fun M : ℕ => (M : ℝ)⁻¹ •
      ∑ n ∈ Finset.range M, fourier (T := 1) k (x n : UnitAddCircle))
      atTop (𝓝 0) := by
  have hd := (fourier_difference_tendsto_zero k happrox).cesaro_smul
  have hs := hd.add haverage
  simp only [Finset.sum_sub_distrib, smul_sub, sub_add_cancel, zero_add] at hs
  exact hs

theorem nat_log_tendsto_atTop {Q : ℕ} (hQ : 1 < Q) :
    Tendsto (Nat.log Q) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (Q ^ b)] with n hn
  exact Nat.le_log_of_pow_le hQ hn

theorem linear_mul_geometric_tendsto_zero
    (r C D : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun B : ℕ => (C * (B : ℝ) + D) * r ^ B) atTop (𝓝 0) := by
  have h0 := tendsto_pow_const_mul_const_pow_of_lt_one 0 hr0 hr1
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 hr0 hr1
  convert (h1.const_mul C).add (h0.const_mul D) using 1
  · ext B
    ring
  · simp

/-- A discarded geometric prefix and a linear number of smaller geometric
orbit bounds satisfy the generic scale-decay hypothesis. -/
theorem geometric_scale_error_tendsto_zero
    (Q U V : ℕ) (hQ : 0 < Q) (hU : U < Q) (hV : V < Q) (C D : ℝ) :
    Tendsto (fun B : ℕ =>
      ((U : ℝ) ^ (B + 1) +
        (C * (((B + 1 : ℕ) : ℝ) + 1) + D) * (V : ℝ) ^ (B + 1)) /
          (Q : ℝ) ^ B) atTop (𝓝 0) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hu0 : (0 : ℝ) ≤ (U : ℝ) / Q := by positivity
  have hv0 : (0 : ℝ) ≤ (V : ℝ) / Q := by positivity
  have hu1 : (U : ℝ) / Q < 1 := (div_lt_one hQR).mpr (by exact_mod_cast hU)
  have hv1 : (V : ℝ) / Q < 1 := (div_lt_one hQR).mpr (by exact_mod_cast hV)
  have hu := (tendsto_pow_atTop_nhds_zero_of_lt_one hu0 hu1).const_mul (U : ℝ)
  have hv := linear_mul_geometric_tendsto_zero ((V : ℝ) / Q)
    (C * V) ((2 * C + D) * V) hv0 hv1
  convert hu.add hv using 1
  · ext B
    simp only [Nat.cast_add, Nat.cast_one, pow_succ, div_eq_mul_inv]
    ring
  · simp

/-- Bounds at geometric scales apply to every prefix, not just scale endpoints.
Only the normalized error at the next scale needs to tend to zero. -/
theorem average_tendsto_zero_of_scale_prefix_bound
    (f : ℕ → ℂ) (Q : ℕ) (E : ℕ → ℝ) (hQ : 1 < Q)
    (hdecay : Tendsto (fun B : ℕ => E (B + 1) / (Q : ℝ) ^ B) atTop (𝓝 0))
    (hbound : ∀ B M : ℕ, M < Q ^ B → ‖∑ n ∈ Finset.range M, f n‖ ≤ E B) :
    Tendsto (fun M : ℕ => (M : ℝ)⁻¹ • ∑ n ∈ Finset.range M, f n)
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim := hdecay.comp (nat_log_tendsto_atTop hQ)
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with M hM
  let B := Nat.log Q M
  have hM0 : M ≠ 0 := by omega
  have hlow : (Q : ℝ) ^ B ≤ M := by
    exact_mod_cast Nat.pow_log_le_self Q hM0
  have hup : M < Q ^ (B + 1) := Nat.lt_pow_succ_log_self hQ M
  have hsum := hbound (B + 1) M hup
  have hp : (0 : ℝ) < (Q : ℝ) ^ B := by
    have : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
    positivity
  have hi : (M : ℝ)⁻¹ ≤ ((Q : ℝ) ^ B)⁻¹ := inv_anti₀ hp hlow
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  change (M : ℝ)⁻¹ * ‖∑ n ∈ Finset.range M, f n‖ ≤ E (B + 1) / (Q : ℝ) ^ B
  calc
    _ ≤ ((Q : ℝ) ^ B)⁻¹ * E (B + 1) :=
      mul_le_mul hi hsum (norm_nonneg _) (by positivity)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

/-- The same scale transfer allows any finite number of exceptional scales. -/
theorem average_tendsto_zero_of_eventual_scale_prefix_bound
    (f : ℕ → ℂ) (Q : ℕ) (E : ℕ → ℝ) (hQ : 1 < Q)
    (hdecay : Tendsto (fun B : ℕ => E (B + 1) / (Q : ℝ) ^ B) atTop (𝓝 0))
    (hbound : ∀ᶠ B in atTop, ∀ M : ℕ, M < Q ^ B →
      ‖∑ n ∈ Finset.range M, f n‖ ≤ E B) :
    Tendsto (fun M : ℕ => (M : ℝ)⁻¹ • ∑ n ∈ Finset.range M, f n)
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlog := nat_log_tendsto_atTop hQ
  have hlim := hdecay.comp hlog
  have hgood : ∀ᶠ M in atTop, ∀ n : ℕ, n < Q ^ (Nat.log Q M + 1) →
      ‖∑ i ∈ Finset.range n, f i‖ ≤ E (Nat.log Q M + 1) :=
    ((tendsto_add_atTop_nat 1).comp hlog).eventually hbound
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1, hgood] with M hM hgoodM
  let B := Nat.log Q M
  have hlow : (Q : ℝ) ^ B ≤ M := by
    exact_mod_cast Nat.pow_log_le_self Q (by omega : M ≠ 0)
  have hsum := hgoodM M (Nat.lt_pow_succ_log_self hQ M)
  have hp : (0 : ℝ) < (Q : ℝ) ^ B := by
    have : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
    positivity
  have hi : (M : ℝ)⁻¹ ≤ ((Q : ℝ) ^ B)⁻¹ := inv_anti₀ hp hlow
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  change (M : ℝ)⁻¹ * ‖∑ n ∈ Finset.range M, f n‖ ≤ E (B + 1) / (Q : ℝ) ^ B
  calc
    _ ≤ ((Q : ℝ) ^ B)⁻¹ * E (B + 1) :=
      mul_le_mul hi hsum (norm_nonneg _) (by positivity)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

/-- An initial discarded segment is charged once; each later cut-free interval
is charged its uniform orbit bound. The cuts are otherwise arbitrary. -/
theorem norm_sum_range_le_of_late_block_bound
    (f : ℕ → ℂ) (cuts : Finset ℕ) (M A : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ n, ‖f n‖ ≤ 1)
    (hblock : ∀ a b : ℕ, A ≤ a → a ≤ b → b ≤ M →
      (∀ n ∈ Finset.Ioo a b, n ∉ cuts) →
      ‖∑ n ∈ Finset.Ico a b, f n‖ ≤ K) :
    ‖∑ n ∈ Finset.range M, f n‖ ≤
      (A : ℝ) + (((cuts.filter (fun n => 0 < n ∧ n < M)).card : ℝ) + 1) * K := by
  let g : ℕ → ℂ := fun n => if A ≤ n then f n else 0
  have hgblock : ∀ a b : ℕ, a ≤ b → b ≤ M →
      (∀ n ∈ Finset.Ioo a b, n ∉ cuts) →
      ‖∑ n ∈ Finset.Ico a b, g n‖ ≤ K := by
    intro a b hab hbM hcuts
    by_cases hAb : A ≤ b
    · have heq : (∑ n ∈ Finset.Ico a b, g n) =
          ∑ n ∈ Finset.Ico (max a A) b, f n := by
        dsimp only [g]
        rw [← Finset.sum_filter]
        congr 1
        ext n
        simp only [Finset.mem_filter, Finset.mem_Ico]
        omega
      rw [heq]
      exact hblock (max a A) b (le_max_right _ _) (max_le hab hAb) hbM
        (fun n hn => hcuts n (by
          have hh := Finset.mem_Ioo.mp hn
          exact Finset.mem_Ioo.mpr ⟨lt_of_le_of_lt (le_max_left _ _) hh.1, hh.2⟩))
    · have heq : (∑ n ∈ Finset.Ico a b, g n) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        have hh := Finset.mem_Ico.mp hn
        simp [g, show ¬ A ≤ n by omega]
      simpa only [heq, norm_zero] using hK
  have hg := XiNormality.norm_sum_range_le_of_block_bound g cuts M K hK hgblock
  have herr : ‖∑ n ∈ Finset.range M, (f n - g n)‖ ≤ (A : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Finset.range M, (if n < A then (1 : ℝ) else 0) := by
        apply norm_sum_le_of_le
        intro n hn
        by_cases hAn : A ≤ n
        · simp [g, hAn, show ¬ n < A by omega]
        · simpa [g, hAn, show n < A by omega] using hf n
      _ = (((Finset.range M).filter (fun n => n < A)).card : ℝ) := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ (A : ℝ) := by
        have hcard := Finset.card_le_card (show
          (Finset.range M).filter (fun n => n < A) ⊆ Finset.range A from
          fun n hn => Finset.mem_range.mpr (Finset.mem_filter.mp hn).2)
        simpa using (show
          ((((Finset.range M).filter (fun n => n < A)).card : ℝ)) ≤
            ((Finset.range A).card : ℝ) by exact_mod_cast hcard)
  have heq : (∑ n ∈ Finset.range M, f n) =
      (∑ n ∈ Finset.range M, (f n - g n)) + ∑ n ∈ Finset.range M, g n := by
    rw [Finset.sum_sub_distrib, sub_add_cancel]
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add herr hg)

/-- Partition a rational approximation at an arbitrary event predicate.
Between events it follows a single radix orbit. -/
theorem norm_sum_rational_prefix_le
    (R : ℕ → ℚ) (S : ℕ → Prop) (F : ℚ → ℂ)
    (b M A : ℕ) (K : ℝ) (hK : 0 ≤ K) (hF : ∀ q, ‖F q‖ ≤ 1)
    (hrec : ∀ n t : ℕ,
      (∀ m : ℕ, S m → m ≤ n + t → m ≤ n) →
      R (n + t) = (b : ℚ) ^ t * R n)
    (horbit : ∀ n t : ℕ, A ≤ n → n + t ≤ M →
      ‖∑ i ∈ Finset.range t, F ((b : ℚ) ^ i * R n)‖ ≤ K) :
    ‖∑ n ∈ Finset.range M, F (R n)‖ ≤
      (A : ℝ) + ((((Finset.range M).filter S).card : ℝ) + 1) * K := by
  let cuts := (Finset.range M).filter S
  have hblock : ∀ a z : ℕ, A ≤ a → a ≤ z → z ≤ M →
      (∀ n ∈ Finset.Ioo a z, n ∉ cuts) →
      ‖∑ n ∈ Finset.Ico a z, F (R n)‖ ≤ K := by
    intro a z hAa haz hzM hcuts
    have heq : (∑ n ∈ Finset.Ico a z, F (R n)) =
        ∑ i ∈ Finset.range (z - a), F ((b : ℚ) ^ i * R a) := by
      rw [Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [hrec a i]
      intro m hm hmi
      by_contra hma
      have hmz : m < z := by omega
      have hmc : m ∈ cuts := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (hmz.trans_le hzM), hm⟩
      exact hcuts m (Finset.mem_Ioo.mpr ⟨by omega, hmz⟩) hmc
    rw [heq]
    exact horbit a (z - a) hAa (by omega)
  have hglobal := norm_sum_range_le_of_late_block_bound
    (fun n => F (R n)) cuts M A K hK (fun n => hF (R n)) hblock
  have hcard : ((cuts.filter (fun n => 0 < n ∧ n < M)).card : ℝ) ≤ cuts.card := by
    exact_mod_cast Finset.card_filter_le cuts (fun n => 0 < n ∧ n < M)
  apply hglobal.trans
  simpa only [cuts, add_comm] using (add_le_add_left
    (mul_le_mul_of_nonneg_right (add_le_add_right hcard 1) hK) (A : ℝ))

/-- A scale bound for a rational approximation, together with vanishing real
error, proves binary normality. The bounds may depend on each Fourier frequency. -/
theorem binaryNormal_of_approximation_scale_bounds
    (x : ℝ) (R : ℕ → ℚ) (Q : ℕ) (hQ : 1 < Q)
    (happrox : Tendsto (fun n => (2 : ℝ) ^ n * x - (R n : ℝ)) atTop (𝓝 0))
    (hbound : ∀ h : ℤ, h ≠ 0 → ∃ E : ℕ → ℝ,
      Tendsto (fun B : ℕ => E (B + 1) / (Q : ℝ) ^ B) atTop (𝓝 0) ∧
      ∀ᶠ B in atTop, ∀ M : ℕ, M < Q ^ B →
        ‖∑ n ∈ Finset.range M,
          fourier (T := 1) h ((R n : ℝ) : UnitAddCircle)‖ ≤ E B) :
    XiNormality.BinaryNormal x := by
  apply XiNormality.binaryNormal_of_fourier
  intro h hh
  apply fourier_average_tendsto_of_approximation h happrox
  obtain ⟨E, hdecay, hprefix⟩ := hbound h hh
  exact average_tendsto_zero_of_eventual_scale_prefix_bound
    (fun n => fourier (T := 1) h ((R n : ℝ) : UnitAddCircle)) Q E hQ hdecay hprefix

/-- A complete reusable criterion for sparse-event rational approximations.
The event counts, discarded prefixes, and orbit estimates are kept separate. -/
theorem binaryNormal_of_sparse_rational_orbits
    (x : ℝ) (R : ℕ → ℚ) (S : ℕ → Prop) (Q : ℕ) (hQ : 1 < Q)
    (happrox : Tendsto (fun n => (2 : ℝ) ^ n * x - (R n : ℝ)) atTop (𝓝 0))
    (hrec : ∀ n t : ℕ,
      (∀ m : ℕ, S m → m ≤ n + t → m ≤ n) →
      R (n + t) = (2 : ℚ) ^ t * R n)
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
              ((((2 : ℚ) ^ i * R n : ℚ) : ℝ) : UnitAddCircle)‖ ≤ K B) :
    XiNormality.BinaryNormal x := by
  apply binaryNormal_of_approximation_scale_bounds x R Q hQ happrox
  intro h hh
  obtain ⟨A, K, D, hK, hdecay, hgood⟩ := hcontrol h hh
  refine ⟨fun B => (A B : ℝ) + (D B + 1) * K B, hdecay, ?_⟩
  filter_upwards [hgood] with B hB
  intro M hM
  let F : ℚ → ℂ := fun q => fourier (T := 1) h ((q : ℝ) : UnitAddCircle)
  have hp := norm_sum_rational_prefix_le R S F 2 M (A B) (K B) (hK B)
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
theorem binaryNormal_of_linear_event_geometric_orbits
    (x : ℝ) (R : ℕ → ℚ) (S : ℕ → Prop) (Q U V : ℕ)
    (hQ : 1 < Q) (hU : U < Q) (hV : V < Q) (D : ℝ)
    (happrox : Tendsto (fun n => (2 : ℝ) ^ n * x - (R n : ℝ)) atTop (𝓝 0))
    (hrec : ∀ n t : ℕ,
      (∀ m : ℕ, S m → m ≤ n + t → m ≤ n) →
      R (n + t) = (2 : ℚ) ^ t * R n)
    (hcount : ∀ᶠ (B : ℕ) in atTop,
      (((Finset.range (Q ^ B)).filter S).card : ℝ) ≤ D * ((B : ℝ) + 1))
    (horbit : ∀ h : ℤ, h ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ (B : ℕ) in atTop, ∀ n t : ℕ, U ^ B ≤ n → n + t ≤ Q ^ B →
        ‖∑ i ∈ Finset.range t, fourier (T := 1) h
          ((((2 : ℚ) ^ i * R n : ℚ) : ℝ) : UnitAddCircle)‖ ≤ C * (V : ℝ) ^ B) :
    XiNormality.BinaryNormal x := by
  apply binaryNormal_of_sparse_rational_orbits x R S Q hQ happrox hrec
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

/-- Fourier conclusions of the same sparse-orbit estimates. -/
theorem fourier_average_of_approximation_scale_bounds
    (x : ℝ) (R : ℕ → ℚ) (Q : ℕ) (hQ : 1 < Q)
    (happrox : Tendsto (fun n => (2 : ℝ) ^ n * x - (R n : ℝ)) atTop (𝓝 0))
    (hbound : ∀ h : ℤ, h ≠ 0 → ∃ E : ℕ → ℝ,
      Tendsto (fun B : ℕ => E (B + 1) / (Q : ℝ) ^ B) atTop (𝓝 0) ∧
      ∀ᶠ B in atTop, ∀ M : ℕ, M < Q ^ B →
        ‖∑ n ∈ Finset.range M,
          fourier (T := 1) h ((R n : ℝ) : UnitAddCircle)‖ ≤ E B) :
    ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun M : ℕ => (M : ℝ)⁻¹ •
        ∑ i ∈ Finset.range M, fourier (T := 1) h
          (((2 : ℝ) ^ i * x : ℝ) : UnitAddCircle)) atTop (𝓝 0) := by
  intro h hh
  apply fourier_average_tendsto_of_approximation h happrox
  obtain ⟨E, hdecay, hprefix⟩ := hbound h hh
  exact average_tendsto_zero_of_eventual_scale_prefix_bound
    (fun n => fourier (T := 1) h ((R n : ℝ) : UnitAddCircle)) Q E hQ hdecay hprefix

/-- A complete reusable criterion for sparse-event rational approximations.
The event counts, discarded prefixes, and orbit estimates are kept separate. -/
theorem fourier_average_of_sparse_rational_orbits
    (x : ℝ) (R : ℕ → ℚ) (S : ℕ → Prop) (Q : ℕ) (hQ : 1 < Q)
    (happrox : Tendsto (fun n => (2 : ℝ) ^ n * x - (R n : ℝ)) atTop (𝓝 0))
    (hrec : ∀ n t : ℕ,
      (∀ m : ℕ, S m → m ≤ n + t → m ≤ n) →
      R (n + t) = (2 : ℚ) ^ t * R n)
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
              ((((2 : ℚ) ^ i * R n : ℚ) : ℝ) : UnitAddCircle)‖ ≤ K B) :
    ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun M : ℕ => (M : ℝ)⁻¹ •
        ∑ i ∈ Finset.range M, fourier (T := 1) h
          (((2 : ℝ) ^ i * x : ℝ) : UnitAddCircle)) atTop (𝓝 0) := by
  apply fourier_average_of_approximation_scale_bounds x R Q hQ happrox
  intro h hh
  obtain ⟨A, K, D, hK, hdecay, hgood⟩ := hcontrol h hh
  refine ⟨fun B => (A B : ℝ) + (D B + 1) * K B, hdecay, ?_⟩
  filter_upwards [hgood] with B hB
  intro M hM
  let F : ℚ → ℂ := fun q => fourier (T := 1) h ((q : ℝ) : UnitAddCircle)
  have hp := norm_sum_rational_prefix_le R S F 2 M (A B) (K B) (hK B)
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
theorem fourier_average_of_linear_event_geometric_orbits
    (x : ℝ) (R : ℕ → ℚ) (S : ℕ → Prop) (Q U V : ℕ)
    (hQ : 1 < Q) (hU : U < Q) (hV : V < Q) (D : ℝ)
    (happrox : Tendsto (fun n => (2 : ℝ) ^ n * x - (R n : ℝ)) atTop (𝓝 0))
    (hrec : ∀ n t : ℕ,
      (∀ m : ℕ, S m → m ≤ n + t → m ≤ n) →
      R (n + t) = (2 : ℚ) ^ t * R n)
    (hcount : ∀ᶠ (B : ℕ) in atTop,
      (((Finset.range (Q ^ B)).filter S).card : ℝ) ≤ D * ((B : ℝ) + 1))
    (horbit : ∀ h : ℤ, h ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ (B : ℕ) in atTop, ∀ n t : ℕ, U ^ B ≤ n → n + t ≤ Q ^ B →
        ‖∑ i ∈ Finset.range t, fourier (T := 1) h
          ((((2 : ℚ) ^ i * R n : ℚ) : ℝ) : UnitAddCircle)‖ ≤ C * (V : ℝ) ^ B) :
    ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun M : ℕ => (M : ℝ)⁻¹ •
        ∑ i ∈ Finset.range M, fourier (T := 1) h
          (((2 : ℝ) ^ i * x : ℝ) : UnitAddCircle)) atTop (𝓝 0) := by
  apply fourier_average_of_sparse_rational_orbits x R S Q hQ happrox hrec
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
