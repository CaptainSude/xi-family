import StonehamNormality.MixedModulus

/-! Finite orthogonality for arbitrary radices whose power orbit contains a
principal congruence kernel. All arithmetic premises are explicit. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace StonehamNormality

theorem power_orbit_add_closed_of_kernel {q : ℕ} [NeZero q]
    (b D : ZMod q) (hb : IsUnit b)
    (hkernel : ∀ z : ZMod q, ∃ d : ℕ, b ^ d = 1 + D * z)
    (i : Fin (orderOf b)) :
    ∃ j : Fin (orderOf b), b ^ (j : ℕ) = b ^ (i : ℕ) + D := by
  have hu : IsUnit (b ^ (i : ℕ)) := hb.pow _
  let u : (ZMod q)ˣ := hu.unit
  obtain ⟨d, hd⟩ := hkernel ((u⁻¹ : (ZMod q)ˣ) : ZMod q)
  have hcancel : b ^ (i : ℕ) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
    rw [← IsUnit.unit_spec hu]
    exact Units.mul_inv u
  have hnext : b ^ ((i : ℕ) + d) = b ^ (i : ℕ) + D := by
    rw [pow_add, hd]
    calc
      _ = b ^ (i : ℕ) + D * (b ^ (i : ℕ) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) := by ring
      _ = _ := by rw [hcancel, mul_one]
  refine ⟨⟨((i : ℕ) + d) % orderOf b, Nat.mod_lt _ hb.isOfFinOrder.orderOf_pos⟩, ?_⟩
  change b ^ (((i : ℕ) + d) % orderOf b) = _
  rw [pow_mod_orderOf]
  exact hnext

theorem sum_power_character_eq_zero_of_kernel {q : ℕ} [NeZero q]
    (b D w : ZMod q) (hb : IsUnit b)
    (hkernel : ∀ z : ZMod q, ∃ d : ℕ, b ^ d = 1 + D * z)
    (hwD : w * D ≠ 0) :
    ∑ t ∈ Finset.range (orderOf b), ZMod.stdAddChar (w * b ^ t) = 0 := by
  apply sum_powers_addChar_eq_zero_of_add_closed ZMod.stdAddChar b w D
    (power_orbit_add_closed_of_kernel b D hb hkernel)
  intro h
  apply hwD
  apply ZMod.injective_stdAddChar
  simpa only [AddChar.map_zero_eq_one] using h

theorem power_character_correlation_zero_of_kernel {q : ℕ} [NeZero q]
    (b D w : ZMod q) (hb : IsUnit b) (hw : IsUnit w)
    (hkernel : ∀ z : ZMod q, ∃ d : ℕ, b ^ d = 1 + D * z)
    (i j : ℕ) (hij : (b ^ i - b ^ j) * D ≠ 0) :
    ∑ t ∈ Finset.range (orderOf b),
      ZMod.stdAddChar (w * b ^ (t + i)) *
        conj (ZMod.stdAddChar (w * b ^ (t + j))) = 0 := by
  have hterm (t : ℕ) :
      ZMod.stdAddChar (w * b ^ (t + i)) *
        conj (ZMod.stdAddChar (w * b ^ (t + j))) =
      ZMod.stdAddChar ((w * (b ^ i - b ^ j)) * b ^ t) := by
    rw [XiNormality.conj_stdAddChar, ← AddChar.map_add_eq_mul]
    congr 1
    simp only [pow_add]
    ring
  simp_rw [hterm]
  apply sum_power_character_eq_zero_of_kernel b D _ hb hkernel
  rw [mul_assoc]
  exact fun hz => hij (hw.mul_right_eq_zero.mp hz)

/-- The same inner estimate as in the three-and-five development, with no
restriction on the prime support or radix in its arithmetic interface. -/
theorem power_character_arbitrary_length_bound {q : ℕ} [NeZero q]
    (b D w : ZMod q) (hb : IsUnit b) (hw : IsUnit w) (hD : D ≠ 0)
    (hkernel : ∀ z : ZMod q, ∃ d : ℕ, b ^ d = 1 + D * z)
    (L H : ℕ)
    (hsep : ∀ i < H, ∀ j < H, i ≠ j → (b ^ i - b ^ j) * D ≠ 0) :
    (H : ℝ) * ‖∑ t ∈ Finset.range L, ZMod.stdAddChar (w * b ^ t)‖ ≤
      Real.sqrt ((q : ℝ) * ((H : ℝ) * q)) + 2 * (H : ℝ) ^ 2 := by
  let T := orderOf b
  have hmean : ∑ t ∈ Finset.range T, ZMod.stdAddChar (w * b ^ t) = 0 := by
    apply sum_power_character_eq_zero_of_kernel b D w hb hkernel
    exact fun hz => hD (hw.mul_right_eq_zero.mp hz)
  have hperiod : Function.Periodic (fun t : ℕ => ZMod.stdAddChar (w * b ^ t)) T := by
    intro t
    change ZMod.stdAddChar (w * b ^ (t + orderOf b)) = _
    simp only [pow_add, pow_orderOf_eq_one, mul_one]
  have hreduce := XiNormality.sum_range_eq_mod_of_periodic_zero
    (fun t => ZMod.stdAddChar (w * b ^ t)) T hperiod hmean L
  rw [hreduce]
  have hTpos : 0 < T := hb.isOfFinOrder.orderOf_pos
  have hTq : T ≤ q := by
    simpa only [ZMod.card] using (orderOf_le_card_univ (x := b))
  have hLT : L % T ≤ T := (Nat.mod_lt _ hTpos).le
  have hbound := XiNormality.sliding_window_bound
    (fun t => ZMod.stdAddChar (w * b ^ t)) (L % T) H T hLT
    (fun t => XiNormality.norm_stdAddChar _)
    (fun i hi j hj hij => power_character_correlation_zero_of_kernel b D w hb hw
      hkernel i j (hsep i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij))
  refine hbound.trans ?_
  gcongr <;> exact_mod_cast (hLT.trans hTq)

end StonehamNormality
