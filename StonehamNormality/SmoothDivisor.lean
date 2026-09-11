import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith

/-! A divisor near any target in a number with bounded prime factors. -/

namespace StonehamNormality

theorem exists_divisor_between (q D T : ℕ) (hD : 1 ≤ D) (hT : 1 ≤ T)
    (hTq : T ≤ q) (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ≤ D) :
    ∃ m : ℕ, m ∣ q ∧ T ≤ m ∧ m ≤ D * T := by
  have hex : ∃ m : ℕ, m ∣ q ∧ T ≤ m := ⟨q, dvd_refl _, hTq⟩
  let m := Nat.find hex
  have hm : m ∣ q ∧ T ≤ m := Nat.find_spec hex
  refine ⟨m, hm.1, hm.2, ?_⟩
  by_cases hm1 : m = 1
  · subst m
    nlinarith
  have hmpos : 0 < m := by omega
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
  have hpd : p ≤ D := hsupport p hp (hpm.trans hm.1)
  have hdivlt : m / p < m := Nat.div_lt_self hmpos hp.one_lt
  have hsmall : m / p < T := by
    by_contra h
    have hdivq : m / p ∣ q := (Nat.div_dvd_of_dvd hpm).trans hm.1
    have hmin : m ≤ m / p := Nat.find_min' hex ⟨hdivq, by omega⟩
    omega
  have hrecover : m / p * p = m := Nat.div_mul_cancel hpm
  nlinarith

end StonehamNormality
