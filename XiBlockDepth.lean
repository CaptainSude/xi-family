import XiGapSeparation
import XiLocalDensity
import XiFamilyRational
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
open scoped Topology BigOperators Classical

namespace XiFamily

theorem tendsto_nat_log_atTop {c : ℕ} (hc : 1 < c) :
    Tendsto (Nat.log c) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (c ^ k)] with n hn
  exact Nat.le_log_of_pow_le hc hn

/-- The square-root depth leaves an unbounded scale after dilation. -/
theorem tendsto_div_pow_half_log_atTop {c : ℕ} (hc : 1 < c) :
    Tendsto (fun N : ℕ => (N : ℝ) / (c : ℝ) ^ (Nat.log c N / 2 + 1)) atTop atTop := by
  have hcR : (1 : ℝ) < c := by exact_mod_cast hc
  have hc0 : (0 : ℝ) < c := lt_trans zero_lt_one hcR
  have hk : Tendsto (fun N : ℕ => Nat.log c N / 2) atTop atTop :=
    (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp (tendsto_nat_log_atTop hc)
  have hlower : Tendsto (fun N : ℕ => (c : ℝ) ^ (Nat.log c N / 2) / c) atTop atTop :=
    ((tendsto_pow_atTop_atTop_of_one_lt hcR).comp hk).atTop_div_const hc0
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [hlower.eventually (eventually_ge_atTop M), eventually_ge_atTop 1]
    with N hNM hN1
  apply hNM.trans
  have hpow : c ^ (2 * (Nat.log c N / 2)) ≤ N := by
    have hle : 2 * (Nat.log c N / 2) ≤ Nat.log c N := by omega
    exact (Nat.pow_le_pow_right (by omega : 0 < c) hle).trans
      (Nat.pow_log_le_self c (by omega))
  have hpowR : (c : ℝ) ^ (Nat.log c N / 2) * (c : ℝ) ^ (Nat.log c N / 2) ≤ N := by
    have h : (c : ℝ) ^ (2 * (Nat.log c N / 2)) ≤ N := by exact_mod_cast hpow
    simpa only [two_mul, pow_add] using h
  rw [pow_succ]
  apply (div_le_div_iff₀ hc0 (mul_pos (pow_pos hc0 _) hc0)).mpr
  nlinarith

/-- Arbitrarily near-maximal logarithmic depths still leave an unbounded
scale. The constant `C` absorbs residue rounding and fixed valuation offsets. -/
theorem tendsto_div_pow_fractional_log_atTop {c R : ℕ} (hc : 1 < c)
    (hR : 0 < R) (C : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) /
      (c : ℝ) ^ (Nat.log c N - Nat.log c N / R + C)) atTop atTop := by
  have hcR : (1 : ℝ) < c := by exact_mod_cast hc
  have hc0 : (0 : ℝ) < c := lt_trans zero_lt_one hcR
  have hk : Tendsto (fun N : ℕ => Nat.log c N / R) atTop atTop :=
    (Nat.tendsto_div_const_atTop (ne_of_gt hR)).comp (tendsto_nat_log_atTop hc)
  have hlower : Tendsto (fun N : ℕ => (c : ℝ) ^ (Nat.log c N / R) / (c : ℝ) ^ C)
      atTop atTop :=
    ((tendsto_pow_atTop_atTop_of_one_lt hcR).comp hk).atTop_div_const (pow_pos hc0 C)
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [hlower.eventually (eventually_ge_atTop M), eventually_ge_atTop 1]
    with N hNM hN1
  apply hNM.trans
  have he : Nat.log c N / R + (Nat.log c N - Nat.log c N / R) = Nat.log c N := by
    have hle := Nat.div_le_self (Nat.log c N) R
    omega
  have hpowR : (c : ℝ) ^ (Nat.log c N / R) *
      (c : ℝ) ^ (Nat.log c N - Nat.log c N / R) ≤ N := by
    rw [← pow_add, he]
    exact_mod_cast (Nat.pow_log_le_self c (by omega : N ≠ 0))
  rw [pow_add]
  apply (div_le_div_iff₀ (pow_pos hc0 C)
    (mul_pos (pow_pos hc0 _) (pow_pos hc0 C))).mpr
  nlinarith [pow_pos hc0 C]

/-- Bounded upward changes of the selected depth, including residue rounding,
preserve the unbounded normalized scale. -/
theorem tendsto_div_pow_atTop_of_eventually_le {c : ℕ} (hc : 1 < c)
    {r k : ℕ → ℕ}
    (hscale : Tendsto (fun N : ℕ => (N : ℝ) / (c : ℝ) ^ k N) atTop atTop)
    (hle : ∀ᶠ N : ℕ in atTop, r N ≤ k N) :
    Tendsto (fun N : ℕ => (N : ℝ) / (c : ℝ) ^ r N) atTop atTop := by
  have hcR : (1 : ℝ) < c := by exact_mod_cast hc
  have hc0 : (0 : ℝ) < c := lt_trans zero_lt_one hcR
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [hscale.eventually (eventually_ge_atTop M), hle] with N hMN hNk
  apply hMN.trans
  apply (div_le_div_iff₀ (pow_pos hc0 _) (pow_pos hc0 _)).mpr
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hcR.le hNk) (Nat.cast_nonneg N)

/-- A fixed multiplicative separation supplies injectivity on a fixed number
of equal short blocks at every sufficiently large scale. -/
theorem local_blocks_injective_of_separation {p : ℕ} (f : ℕ → ℚ)
    {Λ : ℝ} (hΛ : 1 < Λ)
    (hsep : ∀ T : ℝ, 0 < T → ∀ i k : ℕ,
      T ≤ i → (i : ℝ) ≤ Λ * T → T ≤ k → (k : ℝ) ≤ Λ * T →
      f i ≠ 0 → f k ≠ 0 → padicValRat p (f i) = padicValRat p (f k) → i = k) :
    ∃ K : ℕ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ j < K, ∀ i ∈ Finset.Ico (N + j * (N / K + 1)) (N + (j + 1) * (N / K + 1)),
        ∀ k ∈ Finset.Ico (N + j * (N / K + 1)) (N + (j + 1) * (N / K + 1)),
        f i ≠ 0 → f k ≠ 0 → padicValRat p (f i) = padicValRat p (f k) → i = k := by
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / (Λ - 1))
  have hmargin : (2 : ℝ) < (K : ℝ) * (Λ - 1) := (div_lt_iff₀ (by linarith)).mp hK
  have hKR : (0 : ℝ) < K := by nlinarith
  have hKpos : 0 < K := by exact_mod_cast hKR
  refine ⟨K, hKpos, ?_⟩
  filter_upwards [eventually_ge_atTop K, eventually_ge_atTop 1] with N hNK hN1
  intro j hj i hi k hk hfi hfk hv
  let W := N / K + 1
  let T := N + j * W
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hTN : (N : ℝ) ≤ T := by exact_mod_cast (Nat.le_add_right N (j * W))
  have hT : (0 : ℝ) < T := hNR.trans_le hTN
  have hWK : (W : ℝ) * K ≤ 2 * N := by
    have hdiv := Nat.div_mul_le_self N K
    have h : W * K ≤ 2 * N := by dsimp [W]; nlinarith
    exact_mod_cast h
  have hW : (W : ℝ) < (Λ - 1) * N := by
    have h := mul_lt_mul_of_pos_right hmargin hNR
    nlinarith
  have hTW : (T : ℝ) + W ≤ Λ * T := by nlinarith
  have hico : ∀ z ∈ Finset.Ico (N + j * (N / K + 1)) (N + (j + 1) * (N / K + 1)),
      (T : ℝ) ≤ z ∧ (z : ℝ) ≤ Λ * T := by
    intro z hz
    obtain ⟨hzlo, hzhi⟩ := Finset.mem_Ico.mp hz
    have hzlo' : T ≤ z := hzlo
    have hzhi' : z < T + W := by dsimp [T, W]; nlinarith
    have hzhiR : (z : ℝ) < (T : ℝ) + W := by exact_mod_cast hzhi'
    exact ⟨by exact_mod_cast hzlo', hzhiR.le.trans hTW⟩
  exact hsep T hT i k (hico i hi).1 (hico i hi).2
    (hico k hk).1 (hico k hk).2 hfi hfk hv

theorem unshiftedTerm_local_blocks_injective {p b c a : ℕ} [Fact p.Prime]
    (ha : 2 ≤ a) (hc : 2 ≤ c) (hb : 0 < b)
    (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpdepth : 0 < padicValNat p c) :
    ∃ K : ℕ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ j < K, ∀ i ∈ Finset.Ico (N + j * (N / K + 1)) (N + (j + 1) * (N / K + 1)),
        ∀ k ∈ Finset.Ico (N + j * (N / K + 1)) (N + (j + 1) * (N / K + 1)),
        unshiftedTerm b c a i ≠ 0 → unshiftedTerm b c a k ≠ 0 →
        padicValRat p (unshiftedTerm b c a i) =
          padicValRat p (unshiftedTerm b c a k) → i = k := by
  obtain ⟨Λ, hΛ, hsep⟩ := XiGap.exists_uniform_equal_valuation_separation
    (a := (a : ℝ)) (b := (c : ℝ)) (by exact_mod_cast (show 1 < a by omega))
    (by exact_mod_cast (show 1 < c by omega)) ({0} : Finset ℤ) hpdepth
  apply local_blocks_injective_of_separation (unshiftedTerm b c a) hΛ
  intro T hT m n hmlo hmhi hnlo hnhi hfm hfn hval
  have hm : IsIndex a c m := by
    by_contra hm
    exact hfm (unshiftedTerm_eq_zero_of_not_index hm)
  have hn : IsIndex a c n := by
    by_contra hn
    exact hfn (unshiftedTerm_eq_zero_of_not_index hn)
  obtain ⟨i, k, rfl⟩ := hm
  obtain ⟨j, l, rfl⟩ := hn
  by_contra hne
  have hneR : (a : ℝ) ^ i * (c : ℝ) ^ k ≠ (a : ℝ) ^ j * (c : ℝ) ^ l := by
    exact_mod_cast hne
  have h := hsep T hT i k j l (by exact_mod_cast hmlo) (by exact_mod_cast hmhi)
    (by exact_mod_cast hnlo) (by exact_mod_cast hnhi) hneR 0 (by simp) 0 (by simp)
  rw [unshiftedTerm_valuation_pair i k hb (by omega) (by omega) hpa hpb,
    unshiftedTerm_valuation_pair j l hb (by omega) (by omega) hpa hpb] at hval
  exact h (by simpa only [zero_sub, neg_mul] using hval)

/-- Every multiplicative window gives a deep insertion in each sufficiently
large additive window of relative length one over `L`. -/
theorem unshiftedTerm_deep_insertions_of_scale {p b c a : ℕ} [Fact p.Prime]
    (ha : 2 ≤ a) (hc : 2 ≤ c) (hb : 0 < b) (hac : a.Coprime c)
    (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpdepth : 0 < padicValNat p c)
    (k : ℕ → ℕ)
    (hscale : Tendsto (fun N : ℕ => (N : ℝ) / (c : ℝ) ^ (k N + 1)) atTop atTop) :
    ∀ L : ℕ, 0 < L → ∀ᶠ N : ℕ in atTop, ∀ x : ℕ,
      N ≤ x → x + N / L ≤ 3 * N →
      ∃ m ∈ Finset.Ico x (x + N / L),
        ¬ ValuationAtLeast p (-(k N : ℤ) * padicValNat p c) (unshiftedTerm b c a m) := by
  intro L hL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hε : (0 : ℝ) < 1 / (6 * L) := by positivity
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hc0 : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have hg := XiGap.eventually_exists_dilated_pow_mul_mem_Ioc
    (a := (a : ℝ)) (b := (c : ℝ)) (ε := 1 / (6 * L))
    (N := fun N : ℕ => (N : ℝ)) (t := fun N => (c : ℝ) ^ (k N + 1))
    (by exact_mod_cast (show 1 < a by omega)) (by exact_mod_cast (show 1 < c by omega))
    (XiGap.irrational_log_div_of_coprime (by omega) (by omega) hac) hε
    (Eventually.of_forall (fun _ => pow_pos hc0 _)) hscale
  filter_upwards [hg, eventually_ge_atTop L] with N hNg hNL
  intro x hx hxu
  obtain ⟨i, j, hmlo, hmhi⟩ := hNg (x : ℝ) (by exact_mod_cast hx)
  let m := a ^ i * c ^ (k N + 1 + j)
  have hmform : (m : ℝ) = (c : ℝ) ^ (k N + 1) * ((a : ℝ) ^ i * (c : ℝ) ^ j) := by
    simp [m, pow_add]
    ring
  rw [← hmform] at hmlo hmhi
  have hHpos : 0 < N / L := Nat.div_pos hNL hL
  have hNlt : N < 2 * (N / L) * L := by
    have hmod := Nat.mod_lt N hL
    have hsplit := Nat.mod_add_div N L
    nlinarith
  have hxR : (x : ℝ) ≤ 3 * N := by exact_mod_cast (show x ≤ 3 * N by omega)
  have hNltR : (N : ℝ) < 2 * (N / L : ℕ) * L := by exact_mod_cast hNlt
  have hdist : (1 / (6 * (L : ℝ))) * x < (N / L : ℕ) := by
    have h : (x : ℝ) / (6 * L) < (N / L : ℕ) :=
      (div_lt_iff₀ (show (0 : ℝ) < 6 * L by positivity)).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using h
  have hmupper : (m : ℝ) < x + (N / L : ℕ) := by nlinarith
  refine ⟨m, Finset.mem_Ico.mpr ⟨?_, ?_⟩, ?_⟩
  · exact_mod_cast hmlo.le
  · exact_mod_cast hmupper
  · have hmnz : unshiftedTerm b c a m ≠ 0 :=
      unshiftedTerm_ne_zero hb (by omega) (by omega) (isIndex_mul_pow a c i (k N + 1 + j))
    have hmv : padicValRat p (unshiftedTerm b c a m) =
        -((k N + 1 + j : ℕ) : ℤ) * padicValNat p c :=
      unshiftedTerm_valuation_pair i (k N + 1 + j) hb (by omega) (by omega) hpa hpb
    intro hbad
    rcases hbad with hz | hv
    · exact hmnz hz
    · rw [hmv] at hv
      have hpR : (0 : ℤ) < padicValNat p c := by exact_mod_cast hpdepth
      push_cast at hv
      nlinarith

/-- Denominator depth escapes in density for any moving cutoff whose
translated semigroup still leaves an unbounded scale. -/
theorem unshiftedPrefix_shallow_density_zero_of_scale {p b c a : ℕ} [Fact p.Prime]
    (ha : 2 ≤ a) (hc : 2 ≤ c) (hb : 0 < b) (hac : a.Coprime c)
    (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpdepth : 0 < padicValNat p c)
    (k : ℕ → ℕ)
    (hscale : Tendsto (fun N : ℕ => (N : ℝ) / (c : ℝ) ^ (k N + 1)) atTop atTop) :
    Tendsto (fun N : ℕ =>
      (((Finset.Ico N (2 * N)).filter (fun n =>
        ValuationAtLeast p (-(k N : ℤ) * padicValNat p c)
          (∑ i ∈ Finset.range n, unshiftedTerm b c a i))).card : ℝ) / N)
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hinj⟩ := unshiftedTerm_local_blocks_injective ha hc hb hpa hpb hpdepth
  exact shallow_prefix_dyadic_density_zero (unshiftedTerm b c a)
    (fun N => -(k N : ℤ) * padicValNat p c) K hK hinj
    (unshiftedTerm_deep_insertions_of_scale ha hc hb hac hpa hpb hpdepth k hscale)

/-- An unconditional positive proportion of logarithmic denominator depth
survives outside a density-zero set on every dyadic scale. -/
theorem unshiftedPrefix_half_log_shallow_density_zero {p b c a : ℕ} [Fact p.Prime]
    (ha : 2 ≤ a) (hc : 2 ≤ c) (hb : 0 < b) (hac : a.Coprime c)
    (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpdepth : 0 < padicValNat p c) :
    Tendsto (fun N : ℕ =>
      (((Finset.Ico N (2 * N)).filter (fun n =>
        ValuationAtLeast p (-((Nat.log c N / 2 : ℕ) : ℤ) * padicValNat p c)
          (∑ i ∈ Finset.range n, unshiftedTerm b c a i))).card : ℝ) / N)
      atTop (𝓝 0) :=
  unshiftedPrefix_shallow_density_zero_of_scale ha hc hb hac hpa hpb hpdepth
    (fun N => Nat.log c N / 2) (tendsto_div_pow_half_log_atTop (by omega))

/-- Every fixed fraction below the maximal logarithmic depth survives
outside a density-zero exceptional set. -/
theorem unshiftedPrefix_fractional_log_shallow_density_zero {p b c a R : ℕ}
    [Fact p.Prime] (ha : 2 ≤ a) (hc : 2 ≤ c) (hb : 0 < b) (hac : a.Coprime c)
    (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpdepth : 0 < padicValNat p c) (hR : 0 < R) :
    Tendsto (fun N : ℕ =>
      (((Finset.Ico N (2 * N)).filter (fun n =>
        ValuationAtLeast p
          (-((Nat.log c N - Nat.log c N / R : ℕ) : ℤ) * padicValNat p c)
          (∑ i ∈ Finset.range n, unshiftedTerm b c a i))).card : ℝ) / N)
      atTop (𝓝 0) :=
  unshiftedPrefix_shallow_density_zero_of_scale ha hc hb hac hpa hpb hpdepth
    (fun N => Nat.log c N - Nat.log c N / R)
    (tendsto_div_pow_fractional_log_atTop (by omega) hR 1)

end XiFamily
