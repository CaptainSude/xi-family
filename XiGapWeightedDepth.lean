import XiBlockDepth

open Filter
open scoped Topology BigOperators Classical

namespace XiFamily

/-- Finite coefficient-valuation fibers provide a fixed local separation
for an arbitrary rational sequence supported on a two-generator monoid. -/
theorem local_blocks_injective_of_finite_valuation_fibers
    {p a d e : ℕ} (f : ℕ → ℚ) (V : Finset ℤ)
    (ha : 2 ≤ a) (hd : 2 ≤ d) (he : 0 < e)
    (hfiber : ∀ m, f m ≠ 0 → ∃ i k : ℕ, ∃ w ∈ V,
      m = a ^ i * d ^ k ∧ padicValRat p (f m) = w - (k : ℤ) * e) :
    ∃ K : ℕ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ j < K, ∀ i ∈ Finset.Ico (N + j * (N / K + 1)) (N + (j + 1) * (N / K + 1)),
        ∀ k ∈ Finset.Ico (N + j * (N / K + 1)) (N + (j + 1) * (N / K + 1)),
        f i ≠ 0 → f k ≠ 0 → padicValRat p (f i) = padicValRat p (f k) → i = k := by
  obtain ⟨Λ, hΛ, hsep⟩ := XiGap.exists_uniform_equal_valuation_separation
    (a := (a : ℝ)) (b := (d : ℝ)) (by exact_mod_cast (show 1 < a by omega))
    (by exact_mod_cast (show 1 < d by omega)) V he
  apply local_blocks_injective_of_separation f hΛ
  intro T hT m n hmlo hmhi hnlo hnhi hfm hfn hval
  obtain ⟨i, k, z, hz, rfl, hv1⟩ := hfiber m hfm
  obtain ⟨j, l, w, hw, rfl, hv2⟩ := hfiber n hfn
  by_contra hne
  have hneR : (a : ℝ) ^ i * (d : ℝ) ^ k ≠ (a : ℝ) ^ j * (d : ℝ) ^ l := by
    exact_mod_cast hne
  have h := hsep T hT i k j l (by exact_mod_cast hmlo) (by exact_mod_cast hmhi)
    (by exact_mod_cast hnlo) (by exact_mod_cast hnhi) hneR z hz w hw
  exact h (hv1.symm.trans (hval.trans hv2))

/-- A deep translated residue submonoid supplies insertions in all sufficiently
large additive windows of any prescribed positive relative length. -/
theorem deep_insertions_of_active_translate {p a d L : ℕ}
    (f : ℕ → ℚ) (v : ℕ → ℤ) (r : ℕ → ℕ)
    (ha : 2 ≤ a) (hd : 2 ≤ d) (had : a.Coprime d) (hL : 0 < L)
    (hactive : ∀ᶠ N : ℕ in atTop, ∀ i j : ℕ,
      ¬ ValuationAtLeast p (v N) (f (a ^ i * d ^ (r N + L * j))))
    (hscale : Tendsto (fun N : ℕ => (N : ℝ) / (d : ℝ) ^ r N) atTop atTop) :
    ∀ Q : ℕ, 0 < Q → ∀ᶠ N : ℕ in atTop, ∀ x : ℕ,
      N ≤ x → x + N / Q ≤ 3 * N →
      ∃ m ∈ Finset.Ico x (x + N / Q), ¬ ValuationAtLeast p (v N) (f m) := by
  intro Q hQ
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hε : (0 : ℝ) < 1 / (6 * Q) := by positivity
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdL : 1 < d ^ L := one_lt_pow₀ (by omega) (ne_of_gt hL)
  have hadL : a.Coprime (d ^ L) := by simpa using had.pow 1 L
  have hirr : Irrational (Real.log (a : ℝ) / Real.log ((d : ℝ) ^ L)) := by
    simpa only [Nat.cast_pow] using
      XiGap.irrational_log_div_of_coprime (by omega) hdL hadL
  have hg := XiGap.eventually_exists_dilated_pow_mul_mem_Ioc
    (a := (a : ℝ)) (b := (d : ℝ) ^ L) (ε := 1 / (6 * Q))
    (N := fun N : ℕ => (N : ℝ)) (t := fun N => (d : ℝ) ^ r N)
    (by exact_mod_cast (show 1 < a by omega)) (by exact_mod_cast hdL) hirr hε
    (Eventually.of_forall (fun _ => pow_pos hd0 _)) hscale
  filter_upwards [hg, hactive, eventually_ge_atTop Q] with N hNg hNa hNQ
  intro x hx hxu
  obtain ⟨i, j, hmlo, hmhi⟩ := hNg (x : ℝ) (by exact_mod_cast hx)
  let m := a ^ i * d ^ (r N + L * j)
  have hmform : (m : ℝ) = (d : ℝ) ^ r N * ((a : ℝ) ^ i * ((d : ℝ) ^ L) ^ j) := by
    simp [m, pow_add, pow_mul]
    ring
  rw [← hmform] at hmlo hmhi
  have hHpos : 0 < N / Q := Nat.div_pos hNQ hQ
  have hNlt : N < 2 * (N / Q) * Q := by
    have hmod := Nat.mod_lt N hQ
    have hsplit := Nat.mod_add_div N Q
    nlinarith
  have hxR : (x : ℝ) ≤ 3 * N := by exact_mod_cast (show x ≤ 3 * N by omega)
  have hNltR : (N : ℝ) < 2 * (N / Q : ℕ) * Q := by exact_mod_cast hNlt
  have hdist : (1 / (6 * (Q : ℝ))) * x < (N / Q : ℕ) := by
    have h : (x : ℝ) / (6 * Q) < (N / Q : ℕ) :=
      (div_lt_iff₀ (show (0 : ℝ) < 6 * Q by positivity)).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using h
  have hmupper : (m : ℝ) < x + (N / Q : ℕ) := by nlinarith
  exact ⟨m, Finset.mem_Ico.mpr ⟨by exact_mod_cast hmlo.le, by exact_mod_cast hmupper⟩,
    hNa i j⟩

/-- A general weighted-block denominator-escape theorem. Only finite valuation
fibers and one deep residue submonoid are required. -/
theorem finite_valuation_fibers_shallow_density_zero {p a d e L : ℕ} [Fact p.Prime]
    (f : ℕ → ℚ) (v : ℕ → ℤ) (r : ℕ → ℕ) (V : Finset ℤ)
    (ha : 2 ≤ a) (hd : 2 ≤ d) (had : a.Coprime d) (he : 0 < e) (hL : 0 < L)
    (hfiber : ∀ m, f m ≠ 0 → ∃ i k : ℕ, ∃ w ∈ V,
      m = a ^ i * d ^ k ∧ padicValRat p (f m) = w - (k : ℤ) * e)
    (hactive : ∀ᶠ N : ℕ in atTop, ∀ i j : ℕ,
      ¬ ValuationAtLeast p (v N) (f (a ^ i * d ^ (r N + L * j))))
    (hscale : Tendsto (fun N : ℕ => (N : ℝ) / (d : ℝ) ^ r N) atTop atTop) :
    Tendsto (fun N : ℕ =>
      (((Finset.Ico N (2 * N)).filter (fun n =>
        ValuationAtLeast p (v N) (∑ i ∈ Finset.range n, f i))).card : ℝ) / N)
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hinj⟩ := local_blocks_injective_of_finite_valuation_fibers f V ha hd he hfiber
  exact shallow_prefix_dyadic_density_zero f v K hK hinj
    (deep_insertions_of_active_translate f v r ha hd had hL hactive hscale)

end XiFamily
