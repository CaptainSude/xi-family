import XiGroupedSeries

/-! A finite nonempty family has a unique maximal denominator slope at
some prime which is coprime to both the radix and the common generator. -/

noncomputable section
open scoped Classical

namespace XiFamily

theorem primitiveBase_mem_properties {a b : ℕ} (S : Finset ℕ)
    (hS : ∀ c ∈ S, 2 ≤ c) (hcop : ∀ c ∈ S, c.Coprime (a * b))
    {d : ℕ} (hd : d ∈ S.image primitiveBase) :
    PrimitiveParameter d ∧ d.Coprime (a * b) := by
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
  exact ⟨(primitive_parameters_spec (hS c hc)).1,
    primitiveBase_coprime (hS c hc) (hcop c hc)⟩

theorem exists_dominant_primitive_block {a b : ℕ} (S : Finset ℕ)
    (hSne : S.Nonempty) (hS : ∀ c ∈ S, 2 ≤ c)
    (hcop : ∀ c ∈ S, c.Coprime (a * b)) :
    ∃ p d : ℕ, p.Prime ∧ d ∈ S.image primitiveBase ∧ p ∣ d ∧
      ¬ p ∣ a ∧ ¬ p ∣ b ∧
      ∀ e ∈ S.image primitiveBase, e ≠ d → denominatorSlope p e < denominatorSlope p d := by
  let D := S.image primitiveBase
  have hD : D.Nonempty := hSne.image primitiveBase
  obtain ⟨d₀, hd₀⟩ := hD
  have hd₀prop := primitiveBase_mem_properties S hS hcop hd₀
  have hd₀2 := hd₀prop.1.1
  obtain ⟨p, hp, hpd₀⟩ := Nat.exists_prime_and_dvd (show d₀ ≠ 1 by omega)
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, hmax⟩ := D.exists_max_image (denominatorSlope p) ⟨d₀, hd₀⟩
  have hdprop := primitiveBase_mem_properties S hS hcop hd
  have hspos : 0 < denominatorSlope p d :=
    (denominatorSlope_pos hd₀2 hpd₀).trans_le (hmax d₀ hd₀)
  have hpd : p ∣ d := by
    by_contra h
    simp [denominatorSlope, padicValNat.eq_zero_of_not_dvd h] at hspos
  have hpab : ¬ p ∣ a * b :=
    (hp.coprime_iff_not_dvd.mp (hdprop.2.of_dvd_left hpd))
  refine ⟨p, d, hp, hd, hpd, ?_, ?_, ?_⟩
  · intro hpa
    exact hpab (dvd_mul_of_dvd_left hpa b)
  · intro hpb
    exact hpab (dvd_mul_of_dvd_right hpb a)
  · intro e he hed
    have heprop := primitiveBase_mem_properties S hS hcop he
    by_cases hpe : p ∣ e
    · exact lt_of_le_of_ne (hmax e he)
        (primitive_denominatorSlopes_ne heprop.1 hdprop.1 hpe hpd hed)
    · simpa [denominatorSlope, padicValNat.eq_zero_of_not_dvd hpe] using hspos

end XiFamily
