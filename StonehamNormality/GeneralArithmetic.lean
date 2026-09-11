import StonehamNormality.StonehamArithmetic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! Exact truncation denominators for arbitrary coprime radix and parameter. -/

noncomputable section
open scoped BigOperators Classical

namespace StonehamNormality

def powerTruncation (b c n K : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 K, (b : ℚ) ^ (n - c ^ k) / (c : ℚ) ^ k

def powerNumerator (b c n K : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 K, b ^ (n - c ^ k) * c ^ (K - k)

theorem powerTruncation_scaled (b c n K : ℕ) (hc : 0 < c) :
    (c : ℚ) ^ K * powerTruncation b c n K = (powerNumerator b c n K : ℚ) := by
  unfold powerTruncation powerNumerator
  rw [Finset.mul_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkK := (Finset.mem_Icc.mp hk).2
  have hK : K = (K - k) + k := by omega
  nth_rw 1 [hK]
  simp only [pow_add, Nat.cast_mul, Nat.cast_pow]
  have hc0 : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  field_simp

theorem powerNumerator_mod_dvd (b c n K p : ℕ) (hK : 1 ≤ K) (hpc : p ∣ c) :
    (powerNumerator b c n K : ZMod p) = (b : ZMod p) ^ (n - c ^ K) := by
  classical
  have hc0 : (c : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff c p).2 hpc
  unfold powerNumerator
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  calc
    _ = ∑ k ∈ Finset.Icc 1 K,
        if k = K then (b : ZMod p) ^ (n - c ^ K) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkK := (Finset.mem_Icc.mp hk).2
      by_cases h : k = K
      · subst k
        simp
      · have hsub : K - k ≠ 0 := by omega
        simp [h, hc0, hsub]
    _ = _ := by simp [hK]

theorem powerNumerator_coprime (b c n K : ℕ) (hK : 1 ≤ K)
    (hbc : Nat.Coprime b c) : Nat.Coprime (powerNumerator b c n K) c := by
  apply Nat.coprime_of_dvd
  intro p hp hpn hpc
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hb : ¬ p ∣ b := by
    intro hpb
    have hd : p ∣ 1 := by simpa [hbc.gcd_eq_one] using Nat.dvd_gcd hpb hpc
    exact hp.not_dvd_one hd
  have hbnz : (b : ZMod p) ≠ 0 := by
    intro hz
    exact hb ((ZMod.natCast_eq_zero_iff b p).1 hz)
  have hnz : (powerNumerator b c n K : ZMod p) ≠ 0 := by
    rw [powerNumerator_mod_dvd b c n K p hK hpc]
    exact pow_ne_zero _ hbnz
  exact hnz ((ZMod.natCast_eq_zero_iff _ _).2 hpn)

theorem powerTruncation_denominator (b c n K : ℕ) (hc : 0 < c)
    (hK : 1 ≤ K) (hbc : Nat.Coprime b c) :
    (powerTruncation b c n K).den = c ^ K := by
  have hcop := (powerNumerator_coprime b c n K hK hbc).pow_right K
  have hc0 : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have heq : powerTruncation b c n K = (powerNumerator b c n K : ℚ) / (c : ℚ) ^ K := by
    apply (eq_div_iff (pow_ne_zero _ hc0)).2
    simpa [mul_comm] using powerTruncation_scaled b c n K hc
  rw [heq]
  have hd := Rat.den_div_eq_of_coprime
    (a := (powerNumerator b c n K : ℤ)) (b := ((c ^ K : ℕ) : ℤ))
    (by exact_mod_cast pow_pos hc K) (by simpa using hcop)
  have hquot : (((powerNumerator b c n K : ℤ) : ℚ) / (((c ^ K : ℕ) : ℤ) : ℚ)) =
      (powerNumerator b c n K : ℚ) / (c : ℚ) ^ K := by simp
  rw [hquot] at hd
  exact Int.ofNat_inj.mp hd

theorem powerTruncation_radix_shift (b c n K t : ℕ) (hc : 1 ≤ c) (hcn : c ^ K ≤ n) :
    powerTruncation b c (n + t) K = (b : ℚ) ^ t * powerTruncation b c n K := by
  unfold powerTruncation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkK := (Finset.mem_Icc.mp hk).2
  have hkn : c ^ k ≤ n := (pow_le_pow_right₀ hc hkK).trans hcn
  rw [show n + t - c ^ k = t + (n - c ^ k) by omega, pow_add, mul_div_assoc]

theorem powerTruncation_pos (b c n K : ℕ) (hb : 0 < b) (hc : 0 < c) (hK : 1 ≤ K) :
    0 < powerTruncation b c n K := by
  unfold powerTruncation
  apply Finset.sum_pos
  · intro k hk
    have hb' : (0 : ℚ) < b := by exact_mod_cast hb
    have hc' : (0 : ℚ) < c := by exact_mod_cast hc
    exact div_pos (pow_pos hb' _) (pow_pos hc' _)
  · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hK⟩⟩

theorem powerTruncation_valuation {p : ℕ} (hp : p.Prime)
    (b c n K : ℕ) (hc : 0 < c) (hK : 1 ≤ K)
    (hbc : Nat.Coprime b c) (hpc : p ∣ c) :
    padicValRat p (powerTruncation b c n K) = -(K : ℤ) * padicValNat p c := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hden : padicValNat p (powerTruncation b c n K).den = K * padicValNat p c := by
    rw [powerTruncation_denominator b c n K hc hK hbc, padicValNat.pow]
  have hpcpos : 0 < padicValNat p c := one_le_padicValNat_of_dvd hc.ne' hpc
  have hdenpos : 0 < padicValNat p (powerTruncation b c n K).den := by
    rw [hden]
    exact Nat.mul_pos (by omega) hpcpos
  have hnum : padicValInt p (powerTruncation b c n K).num = 0 := by
    rcases Rat.num_or_den_zero_padicVal (powerTruncation b c n K) hp with h | h
    · exact h
    · omega
  rw [padicValRat_def, hnum, hden]
  push_cast
  ring

theorem powerTruncation_valuation_nonneg {p : ℕ} (hp : p.Prime)
    (b c n K : ℕ) (hc : 0 < c) (hK : 1 ≤ K)
    (hbc : Nat.Coprime b c) (hpc : ¬ p ∣ c) :
    0 ≤ padicValRat p (powerTruncation b c n K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hden : padicValNat p (powerTruncation b c n K).den = 0 := by
    rw [powerTruncation_denominator b c n K hc hK hbc]
    rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd hpc, mul_zero]
  rw [padicValRat_def, hden]
  simp

theorem prime_power_le_den_of_valuation {p : ℕ} (hp : p.Prime) (q : ℚ) (e : ℕ)
    (hq : padicValRat p q = -(e : ℤ)) : p ^ e ≤ q.den := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hval : e ≤ padicValNat p q.den := by
    rw [padicValRat_def] at hq
    omega
  exact Nat.le_of_dvd q.den_pos ((padicValNat_dvd_iff_le q.den_ne_zero).2 hval)

theorem powerTruncation_valuation_ge {p : ℕ} (hp : p.Prime)
    (b c n K : ℕ) (hc : 0 < c) (hK : 1 ≤ K) (hbc : Nat.Coprime b c) :
    -(K : ℤ) * padicValNat p c ≤ padicValRat p (powerTruncation b c n K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [padicValRat_def, powerTruncation_denominator b c n K hc hK hbc,
    padicValNat.pow]
  push_cast
  have hnonneg : (0 : ℤ) ≤ padicValInt p (powerTruncation b c n K).num := by positivity
  nlinarith

theorem powerTruncation_sum_den_lower {p : ℕ} (hp : p.Prime)
    (b c d n K L : ℕ) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hK : 1 ≤ K) (hL : 1 ≤ L) (hbc : Nat.Coprime b c) (hbd : Nat.Coprime b d)
    (hpc : p ∣ c) (hweight : L * padicValNat p d < K * padicValNat p c) :
    p ^ (K * padicValNat p c) ≤
      (powerTruncation b c n K + powerTruncation b d n L).den := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcval := powerTruncation_valuation hp b c n K hc hK hbc hpc
  have hdval := powerTruncation_valuation_ge hp b d n L hd hL hbd
  have hcpos := powerTruncation_pos b c n K hb hc hK
  have hdpos := powerTruncation_pos b d n L hb hd hL
  have hlt : padicValRat p (powerTruncation b c n K) <
      padicValRat p (powerTruncation b d n L) := by
    rw [hcval]
    have hh : (L : ℤ) * padicValNat p d < (K : ℤ) * padicValNat p c := by
      exact_mod_cast hweight
    nlinarith
  apply prime_power_le_den_of_valuation hp
  rw [padicValRat.add_eq_of_lt (ne_of_gt (add_pos hcpos hdpos))
    hcpos.ne' hdpos.ne' hlt, hcval]
  push_cast
  ring

end StonehamNormality
