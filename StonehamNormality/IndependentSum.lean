import StonehamNormality.GeneralArithmetic
import StonehamNormality.GeneralSeriesBridge
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Denominator separation for multiplicatively independent parameters. -/

noncomputable section
open Filter
open scoped Topology

namespace StonehamNormality

theorem log_power_window (c n K : ℕ) (hc : 2 ≤ c)
    (hlo : c ^ K ≤ n) (hhi : n < c ^ (K + 1)) :
    (K : ℝ) * Real.log c ≤ Real.log n ∧
      Real.log n < ((K : ℝ) + 1) * Real.log c := by
  have hcpos : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast lt_of_lt_of_le (pow_pos (show 0 < c by omega) K) hlo
  constructor
  · have h := Real.log_le_log (pow_pos hcpos K) (show (c : ℝ) ^ K ≤ n by exact_mod_cast hlo)
    simpa only [Real.log_pow] using h
  · have h := Real.log_lt_log hnpos (show (n : ℝ) < (c : ℝ) ^ (K + 1) by exact_mod_cast hhi)
    simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using h

theorem prime_slopes_ne_of_independent {p c d : ℕ} (hp : p.Prime)
    (hc : 2 ≤ c) (hd : 2 ≤ d) (hpc : p ∣ c)
    (hind : ∀ r s : ℕ, 0 < r → 0 < s → c ^ r ≠ d ^ s) :
    (padicValNat p c : ℝ) / Real.log c ≠
      (padicValNat p d : ℝ) / Real.log d := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcpos : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlc : 0 < Real.log c := Real.log_pos (by exact_mod_cast (show 1 < c by omega))
  have hld : 0 < Real.log d := Real.log_pos (by exact_mod_cast (show 1 < d by omega))
  have hvc : 0 < padicValNat p c := one_le_padicValNat_of_dvd (by omega) hpc
  intro heq
  have hvd : 0 < padicValNat p d := by
    have h : (0 : ℝ) < (padicValNat p d : ℝ) / Real.log d := by
      rw [← heq]
      exact div_pos (by exact_mod_cast hvc) hlc
    have h' : (0 : ℝ) < padicValNat p d := (div_pos_iff_of_pos_right hld).1 h
    exact_mod_cast h'
  have hcross : (padicValNat p c : ℝ) * Real.log d =
      (padicValNat p d : ℝ) * Real.log c :=
    (div_eq_div_iff hlc.ne' hld.ne').1 heq
  have hlogs : Real.log ((c : ℝ) ^ padicValNat p d) =
      Real.log ((d : ℝ) ^ padicValNat p c) := by
    rw [Real.log_pow, Real.log_pow]
    exact hcross.symm
  have hpows := Real.log_injOn_pos (pow_pos hcpos _) (pow_pos hdpos _) hlogs
  exact hind _ _ hvd hvc (by exact_mod_cast hpows)

theorem power_window_weights_eventually_lt (c d u v : ℕ)
    (hc : 2 ≤ c) (hd : 2 ≤ d) (hu : 0 < u)
    (hslope : (v : ℝ) / Real.log d < (u : ℝ) / Real.log c) :
    ∀ᶠ n : ℕ in atTop, ∀ K L : ℕ,
      c ^ K ≤ n → n < c ^ (K + 1) →
      d ^ L ≤ n → n < d ^ (L + 1) → L * v < K * u := by
  have hlc : 0 < Real.log c := Real.log_pos (by exact_mod_cast (show 1 < c by omega))
  have hld : 0 < Real.log d := Real.log_pos (by exact_mod_cast (show 1 < d by omega))
  have hsc : 0 < (u : ℝ) / Real.log c := div_pos (by exact_mod_cast hu) hlc
  have hsd : 0 ≤ (v : ℝ) / Real.log d := div_nonneg (Nat.cast_nonneg _) hld.le
  have hdelta : 0 < (u : ℝ) / Real.log c - (v : ℝ) / Real.log d := sub_pos.mpr hslope
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgrow := hlog.const_mul_atTop hdelta
  filter_upwards [hgrow.eventually (eventually_gt_atTop (u : ℝ))] with n hn
  intro K L hcK hcn hdL hdn
  obtain ⟨_, hk⟩ := log_power_window c n K hc hcK hcn
  obtain ⟨hl, _⟩ := log_power_window d n L hd hdL hdn
  have hku : (u : ℝ) / Real.log c * Real.log n < ((K : ℝ) + 1) * u := by
    have h := mul_lt_mul_of_pos_left hk hsc
    calc
      _ < (u / Real.log c) * (((K : ℝ) + 1) * Real.log c) := h
      _ = _ := by field_simp [hlc.ne']
  have hlv : (L : ℝ) * v ≤ (v : ℝ) / Real.log d * Real.log n := by
    have h := mul_le_mul_of_nonneg_left hl hsd
    calc
      _ = (v / Real.log d) * ((L : ℝ) * Real.log d) := by field_simp [hld.ne']
      _ ≤ _ := h
  have hout : (L : ℝ) * v < (K : ℝ) * u := by nlinarith
  exact_mod_cast hout

theorem pair_den_lower_of_slope {p : ℕ} (hp : p.Prime)
    (b c d : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hbc : Nat.Coprime b c) (hbd : Nat.Coprime b d) (hpc : p ∣ c)
    (hslope : (padicValNat p d : ℝ) / Real.log d <
      (padicValNat p c : ℝ) / Real.log c) :
    ∀ᶠ n : ℕ in atTop,
      2 ^ Nat.log c n ≤ (radixStonehamTruncation b c n + radixStonehamTruncation b d n).den := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hvc : 0 < padicValNat p c := one_le_padicValNat_of_dvd (by omega) hpc
  have hsep := power_window_weights_eventually_lt c d (padicValNat p c)
    (padicValNat p d) hc hd hvc hslope
  filter_upwards [hsep, eventually_ge_atTop (max c d)] with n hn hnlarge
  have hcn : c ≤ n := (Nat.le_max_left _ _).trans hnlarge
  have hdn : d ≤ n := (Nat.le_max_right _ _).trans hnlarge
  have hnpos : 0 < n := by omega
  have hK : 1 ≤ Nat.log c n := Nat.log_pos (by omega) hcn
  have hL : 1 ≤ Nat.log d n := Nat.log_pos (by omega) hdn
  have hweights := hn (Nat.log c n) (Nat.log d n)
    (Nat.pow_log_le_self c hnpos.ne') (Nat.lt_pow_succ_log_self (by omega) n)
    (Nat.pow_log_le_self d hnpos.ne') (Nat.lt_pow_succ_log_self (by omega) n)
  rw [radixStonehamTruncation_eq_powerTruncation_log b c n hc hnpos,
    radixStonehamTruncation_eq_powerTruncation_log b d n hd hnpos]
  calc
    2 ^ Nat.log c n ≤ p ^ Nat.log c n := Nat.pow_le_pow_left hp.two_le _
    _ ≤ p ^ (Nat.log c n * padicValNat p c) :=
      pow_le_pow_right₀ hp.one_lt.le (Nat.le_mul_of_pos_right _ hvc)
    _ ≤ _ := powerTruncation_sum_den_lower hp b c d n _ _
      (by omega) (by omega) (by omega) hK hL hbc hbd hpc hweights

theorem independent_pair_den_lower (b c d : ℕ)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hbc : Nat.Coprime b c) (hbd : Nat.Coprime b d)
    (hind : ∀ r s : ℕ, 0 < r → 0 < s → c ^ r ≠ d ^ s) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ᶠ n : ℕ in atTop,
      2 ^ Nat.log a n ≤ (radixStonehamTruncation b c n + radixStonehamTruncation b d n).den := by
  obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd (show c ≠ 1 by omega)
  haveI : Fact p.Prime := ⟨hp⟩
  have hne := prime_slopes_ne_of_independent hp hc hd hpc hind
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hvc : 0 < padicValNat p c := one_le_padicValNat_of_dvd (by omega) hpc
    have hlc : 0 < Real.log c := Real.log_pos (by exact_mod_cast (show 1 < c by omega))
    have hld : 0 < Real.log d := Real.log_pos (by exact_mod_cast (show 1 < d by omega))
    have hvd : 0 < padicValNat p d := by
      have h : (0 : ℝ) < (padicValNat p d : ℝ) / Real.log d :=
        (div_pos (by exact_mod_cast hvc) hlc).trans hlt
      exact_mod_cast (div_pos_iff_of_pos_right hld).1 h
    have hpd : p ∣ d := dvd_of_one_le_padicValNat hvd
    refine ⟨d, hd, ?_⟩
    simpa only [add_comm] using pair_den_lower_of_slope hp b d c hb hd hc hbd hbc hpd hlt
  · exact ⟨c, hc, pair_den_lower_of_slope hp b c d hb hc hd hbc hbd hpc hgt⟩

end StonehamNormality
