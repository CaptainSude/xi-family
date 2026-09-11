import XiBlockDepth
import XiPrimitiveParameters

open Filter
open scoped Topology Classical

namespace XiFamily

private theorem eventually_forall_finset {α β : Type*} {l : Filter α}
    (S : Finset β) (P : α → β → Prop)
    (h : ∀ d ∈ S, ∀ᶠ n in l, P n d) :
    ∀ᶠ n in l, ∀ d ∈ S, P n d := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hS := ih (fun d hd => h d (Finset.mem_insert_of_mem hd))
    filter_upwards [h a (Finset.mem_insert_self _ _), hS] with n hna hnS
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact hna
    · exact hnS d hd

/-- The natural logarithm cutoff differs from its real counterpart by less than one. -/
theorem nat_log_real_bounds (c N : ℕ) (hc : 2 ≤ c) (hN : 0 < N) :
    Real.log (N : ℝ) / Real.log (c : ℝ) - 1 ≤ (Nat.log c N : ℝ) ∧
      (Nat.log c N : ℝ) ≤ Real.log (N : ℝ) / Real.log (c : ℝ) := by
  have hc1 : 1 < c := by omega
  have hc0 : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hclog : 0 < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast hc1)
  constructor
  · have hp : (N : ℝ) < (c : ℝ) ^ (Nat.log c N + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self hc1 N
    have h := Real.log_lt_log hN0 hp
    rw [Real.log_pow, Nat.cast_add, Nat.cast_one] at h
    have h' := (div_lt_iff₀ hclog).mpr h
    linarith
  · have hp : (c : ℝ) ^ Nat.log c N ≤ N := by
      exact_mod_cast Nat.pow_log_le_self c (ne_of_gt hN)
    have h := Real.log_le_log (pow_pos hc0 _) hp
    rw [Real.log_pow] at h
    exact (le_div_iff₀ hclog).mpr h

/-- Removing one over `R` of the natural-log cutoff retains the corresponding
fraction of the real logarithmic slope, up to a fixed additive error. -/
theorem fractional_nat_log_lower_bound (c N : ℕ) {R : ℕ}
    (hc : 2 ≤ c) (hN : 0 < N) (hR : 1 ≤ R) :
    (1 - 1 / (R : ℝ)) * (Real.log (N : ℝ) / Real.log (c : ℝ) - 1) ≤
      ((Nat.log c N - Nat.log c N / R : ℕ) : ℝ) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hRone : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hfrac : 0 ≤ 1 - 1 / (R : ℝ) := by
    have h : 1 / (R : ℝ) ≤ 1 := (div_le_iff₀ hRpos).mpr (by simpa using hRone)
    linarith
  have hdiv : ((Nat.log c N / R : ℕ) : ℝ) ≤ (Nat.log c N : ℝ) / R := by
    apply (le_div_iff₀ hRpos).mpr
    exact_mod_cast Nat.div_mul_le_self (Nat.log c N) R
  calc
    _ ≤ (1 - 1 / (R : ℝ)) * (Nat.log c N : ℝ) :=
      mul_le_mul_of_nonneg_left (nat_log_real_bounds c N hc hN).1 hfrac
    _ = (Nat.log c N : ℝ) - (Nat.log c N : ℝ) / R := by ring
    _ ≤ (Nat.log c N : ℝ) - ((Nat.log c N / R : ℕ) : ℝ) := sub_le_sub_left hdiv _
    _ = ((Nat.log c N - Nat.log c N / R : ℕ) : ℝ) := by
      rw [Nat.cast_sub (Nat.div_le_self _ _)]

/-- A strict gap between real slopes eventually dominates all floor errors,
the factor-two change of scale, and arbitrary fixed integer offsets. -/
theorem log_slope_eventual_dominance {p c d R : ℕ}
    (hc : 2 ≤ c) (hd : 2 ≤ d) (hR : 2 ≤ R)
    (hslopes : denominatorSlope p d < (1 - 1 / (R : ℝ)) * denominatorSlope p c)
    (Cstar Cd : ℤ) :
    ∀ᶠ N : ℕ in atTop,
      Cstar - ((Nat.log c N - Nat.log c N / R : ℕ) : ℤ) * padicValNat p c <
        Cd - (Nat.log d (2 * N) : ℤ) * padicValNat p d := by
  let α : ℝ := 1 - 1 / (R : ℝ)
  let σc := denominatorSlope p c
  let σd := denominatorSlope p d
  have hgap : 0 < α * σc - σd := by dsimp [α, σc, σd]; linarith
  let T : ℝ := ((Cstar : ℝ) - Cd + α * padicValNat p c + σd * Real.log 2) /
    (α * σc - σd)
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_gt_atTop T), eventually_ge_atTop 1]
    with N hNT hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hstar := mul_le_mul_of_nonneg_right
    (fractional_nat_log_lower_bound c N hc (by omega) (by omega : 1 ≤ R))
    (Nat.cast_nonneg (α := ℝ) (padicValNat p c))
  have hstar' : α * σc * Real.log (N : ℝ) - α * padicValNat p c ≤
      ((Nat.log c N - Nat.log c N / R : ℕ) : ℝ) * padicValNat p c := by
    calc
      _ = (1 - 1 / (R : ℝ)) *
          (Real.log (N : ℝ) / Real.log (c : ℝ) - 1) * padicValNat p c := by
        dsimp [α, σc, denominatorSlope]
        ring
      _ ≤ _ := hstar
  have hother := mul_le_mul_of_nonneg_right (nat_log_real_bounds d (2 * N) hd (by omega)).2
    (Nat.cast_nonneg (α := ℝ) (padicValNat p d))
  have hlog2 : Real.log ((2 * N : ℕ) : ℝ) = Real.log 2 + Real.log (N : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul (by norm_num) (ne_of_gt hNpos)]
    norm_num
  rw [hlog2] at hother
  have hother' : (Nat.log d (2 * N) : ℝ) * padicValNat p d ≤
      σd * Real.log (N : ℝ) + σd * Real.log 2 := by
    calc
      _ ≤ ((Real.log 2 + Real.log (N : ℝ)) / Real.log (d : ℝ)) * padicValNat p d := hother
      _ = _ := by dsimp [σd, denominatorSlope]; ring
  have hlarge : (Cstar : ℝ) - Cd + α * padicValNat p c + σd * Real.log 2 <
      Real.log (N : ℝ) * (α * σc - σd) := (div_lt_iff₀ hgap).mp hNT
  have hreal : (Cstar : ℝ) -
      ((Nat.log c N - Nat.log c N / R : ℕ) : ℝ) * padicValNat p c <
        (Cd : ℝ) - (Nat.log d (2 * N) : ℝ) * padicValNat p d := by nlinarith
  have hcast : ((Cstar - ((Nat.log c N - Nat.log c N / R : ℕ) : ℤ) * padicValNat p c : ℤ) : ℝ) <
      ((Cd - (Nat.log d (2 * N) : ℤ) * padicValNat p d : ℤ) : ℝ) := by
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using hreal
  exact Int.cast_lt.mp hcast

/-- A finite family with a unique largest slope admits one common retained
fraction which still exceeds every other slope. -/
theorem exists_common_fractional_slope (D : Finset ℕ) (σ : ℕ → ℝ) (star : ℕ)
    (hmax : ∀ d ∈ D, d ≠ star → σ d < σ star) :
    ∃ R : ℕ, 2 ≤ R ∧ ∀ d ∈ D, d ≠ star → σ d < (1 - 1 / (R : ℝ)) * σ star := by
  have hlim : Tendsto (fun R : ℕ => (1 - 1 / (R : ℝ)) * σ star) atTop (𝓝 (σ star)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).mul_const (σ star)
  have hevent : ∀ᶠ R : ℕ in atTop, ∀ d ∈ D,
      d ≠ star → σ d < (1 - 1 / (R : ℝ)) * σ star := by
    apply eventually_forall_finset D
    intro d hd
    by_cases hds : d = star
    · exact Eventually.of_forall (fun _ h => False.elim (h hds))
    · filter_upwards [(tendsto_order.mp hlim).1 (σ d) (hmax d hd hds)] with R hR
      exact fun _ => hR
  obtain ⟨R, hR, hgood⟩ := ((eventually_ge_atTop 2).and hevent).exists
  exact ⟨R, hR, hgood⟩

/-- Uniform eventual dominance for every member of a finite family, with
one retained fraction chosen before any fixed integer offsets. -/
theorem finite_log_slope_eventual_dominance {p star : ℕ} (D : Finset ℕ)
    (hstar : 2 ≤ star) (hD : ∀ d ∈ D, 2 ≤ d)
    (hmax : ∀ d ∈ D, d ≠ star → denominatorSlope p d < denominatorSlope p star) :
    ∃ R : ℕ, 2 ≤ R ∧ ∀ (Cstar : ℤ) (C : ℕ → ℤ), ∀ᶠ N : ℕ in atTop,
      ∀ d ∈ D, d ≠ star →
        Cstar - ((Nat.log star N - Nat.log star N / R : ℕ) : ℤ) * padicValNat p star <
          C d - (Nat.log d (2 * N) : ℤ) * padicValNat p d := by
  obtain ⟨R, hR, hslopes⟩ := exists_common_fractional_slope D (denominatorSlope p) star hmax
  refine ⟨R, hR, ?_⟩
  intro Cstar C
  apply eventually_forall_finset D
  intro d hd
  by_cases hds : d = star
  · exact Eventually.of_forall (fun _ h => False.elim (h hds))
  · filter_upwards [log_slope_eventual_dominance hstar (hD d hd) hR
      (hslopes d hd hds) Cstar (C d)] with N hN
    exact fun _ => hN

end XiFamily
