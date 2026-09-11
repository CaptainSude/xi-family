import StonehamNormality.DependentSumBridge
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Primitive integer parameters and their distinct denominator slopes. -/

noncomputable section
open scoped Classical

namespace XiFamily

def PrimitiveParameter (d : ℕ) : Prop :=
  2 ≤ d ∧ ∀ a k : ℕ, 2 ≤ a → 2 ≤ k → a ^ k ≠ d

theorem exists_primitive_parameter {c : ℕ} (hc : 2 ≤ c) :
    ∃ d r : ℕ, PrimitiveParameter d ∧ 0 < r ∧ c = d ^ r := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    by_cases hprim : PrimitiveParameter c
    · exact ⟨c, 1, hprim, by omega, by simp⟩
    have hproper : ∃ a k : ℕ, 2 ≤ a ∧ 2 ≤ k ∧ a ^ k = c := by
      by_contra hn
      apply hprim
      refine ⟨hc, ?_⟩
      intro a k ha hk he
      exact hn ⟨a, k, ha, hk, he⟩
    obtain ⟨a, k, ha, hk, he⟩ := hproper
    have hac : a < c := by
      rw [← he]
      have hpow : a ^ 1 < a ^ k := (Nat.pow_lt_pow_iff_right ha).mpr (by omega)
      simpa using hpow
    obtain ⟨d, r, hd, hr, har⟩ := ih a hac ha
    refine ⟨d, r * k, hd, Nat.mul_pos hr (by omega), ?_⟩
    rw [← he, har, pow_mul]

theorem primitive_parameter_power {d e r : ℕ} (hd : PrimitiveParameter d)
    (he : 2 ≤ e) (hr : 0 < r) (hdr : d = e ^ r) : r = 1 ∧ d = e := by
  have hr1 : r = 1 := by
    by_contra h
    exact hd.2 e r he (by omega) hdr.symm
  exact ⟨hr1, by simpa [hr1] using hdr⟩

theorem primitive_parameters_eq_of_pow_eq {d e u v : ℕ}
    (hd : PrimitiveParameter d) (he : PrimitiveParameter e)
    (hu : 0 < u) (hv : 0 < v) (hpow : d ^ u = e ^ v) : d = e := by
  obtain ⟨a, r, s, ha, hr, hs, hda, hea⟩ :=
    StonehamNormality.dependent_parameters_common_base hd.1 he.1 hu hv hpow
  exact (primitive_parameter_power hd ha hr hda).2.trans
    (primitive_parameter_power he ha hs hea).2.symm

def primitiveBase (c : ℕ) : ℕ :=
  if hc : 2 ≤ c then (exists_primitive_parameter hc).choose else 1

def primitiveExponent (c : ℕ) : ℕ :=
  if hc : 2 ≤ c then (exists_primitive_parameter hc).choose_spec.choose else 0

theorem primitive_parameters_spec {c : ℕ} (hc : 2 ≤ c) :
    PrimitiveParameter (primitiveBase c) ∧ 0 < primitiveExponent c ∧
      c = primitiveBase c ^ primitiveExponent c := by
  simp only [primitiveBase, primitiveExponent, dif_pos hc]
  exact (exists_primitive_parameter hc).choose_spec.choose_spec

theorem primitiveBase_dvd {c : ℕ} (hc : 2 ≤ c) : primitiveBase c ∣ c := by
  obtain ⟨_, hr, he⟩ := primitive_parameters_spec hc
  calc
    primitiveBase c ∣ primitiveBase c ^ primitiveExponent c := dvd_pow_self _ hr.ne'
    _ = c := he.symm

theorem primitiveBase_coprime {c t : ℕ} (hc : 2 ≤ c) (hct : c.Coprime t) :
    (primitiveBase c).Coprime t := hct.of_dvd_left (primitiveBase_dvd hc)

theorem primitiveBase_eq_of_pow_eq {c d u v : ℕ}
    (hc : 2 ≤ c) (hd : 2 ≤ d) (hu : 0 < u) (hv : 0 < v)
    (hpow : c ^ u = d ^ v) : primitiveBase c = primitiveBase d := by
  obtain ⟨hcprim, hcr, hce⟩ := primitive_parameters_spec hc
  obtain ⟨hdprim, hdr, hde⟩ := primitive_parameters_spec hd
  apply primitive_parameters_eq_of_pow_eq hcprim hdprim
    (Nat.mul_pos hcr hu) (Nat.mul_pos hdr hv)
  rw [hce, hde, ← pow_mul, ← pow_mul] at hpow
  exact hpow

def denominatorSlope (p d : ℕ) : ℝ := (padicValNat p d : ℝ) / Real.log d

theorem denominatorSlope_pos {p d : ℕ} [Fact p.Prime]
    (hd : 2 ≤ d) (hpd : p ∣ d) : 0 < denominatorSlope p d := by
  apply div_pos
  · exact_mod_cast one_le_padicValNat_of_dvd (by omega : d ≠ 0) hpd
  · exact Real.log_pos (by exact_mod_cast (show 1 < d by omega))

theorem pow_eq_of_denominatorSlope_eq {p c d : ℕ}
    (hc : 2 ≤ c) (hd : 2 ≤ d)
    (he : denominatorSlope p c = denominatorSlope p d) :
    c ^ padicValNat p d = d ^ padicValNat p c := by
  have hclog : Real.log (c : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < c by omega))).ne'
  have hdlog : Real.log (d : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < d by omega))).ne'
  have hcross := (div_eq_div_iff hclog hdlog).mp he
  have hlogs : Real.log ((c : ℝ) ^ padicValNat p d) =
      Real.log ((d : ℝ) ^ padicValNat p c) := by
    rw [Real.log_pow, Real.log_pow]
    exact hcross.symm
  have hpows : (c : ℝ) ^ padicValNat p d = (d : ℝ) ^ padicValNat p c :=
    (Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (by positivity)) hlogs)
  exact_mod_cast hpows

theorem primitive_denominatorSlopes_ne {p c d : ℕ} [Fact p.Prime]
    (hc : PrimitiveParameter c) (hd : PrimitiveParameter d)
    (hpc : p ∣ c) (hpd : p ∣ d) (hcd : c ≠ d) :
    denominatorSlope p c ≠ denominatorSlope p d := by
  intro he
  have hc2 := hc.1
  have hd2 := hd.1
  have hvpc := one_le_padicValNat_of_dvd (by omega : c ≠ 0) hpc
  have hvpd := one_le_padicValNat_of_dvd (by omega : d ≠ 0) hpd
  exact hcd (primitive_parameters_eq_of_pow_eq hc hd (by omega) (by omega)
    (pow_eq_of_denominatorSlope_eq hc.1 hd.1 he))

end XiFamily
