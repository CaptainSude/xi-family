import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Generation of principal congruence kernels

These finite algebraic lemmas support the elementary character-sum estimate
used in the arbitrary-base Stoneham two-sum theorem.
-/

noncomputable section

namespace StonehamNormality

/-- A reduction map between finite residue rings has equally sized fibers. -/
theorem card_reduction_one_fiber (q d : ℕ) [NeZero q] [NeZero d]
    (hd : d ∣ q) :
    Fintype.card {z : ZMod q // ZMod.castHom hd (ZMod d) z = 1} = q / d := by
  classical
  let π : ZMod q →+* ZMod d := ZMod.castHom hd (ZMod d)
  have hsurj : Function.Surjective π := ZMod.castHom_surjective hd
  have hker : Nat.card π.toAddMonoidHom.ker * d = q := by
    have h := π.toAddMonoidHom.ker.card_mul_index
    rw [AddSubgroup.index_ker,
      AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top,
      Nat.card_zmod, Nat.card_zmod] at h
    exact h
  have hk : Nat.card π.toAddMonoidHom.ker = q / d := by
    calc
      _ = (Nat.card π.toAddMonoidHom.ker * d) / d :=
        (Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (NeZero.ne d))).symm
      _ = q / d := congrArg (fun a : ℕ => a / d) hker
  have hfib : Fintype.card {z : ZMod q // π z = 1} =
      Fintype.card {z : ZMod q // π z = 0} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact AddMonoidHom.card_fiber_eq_of_mem_range π
      ⟨1, map_one π⟩ ⟨0, map_zero π⟩
  change Fintype.card {z : ZMod q // π z = 1} = _
  rw [hfib]
  rw [← Nat.card_eq_fintype_card]
  exact hk

/-- If an element congruent to one has the full kernel order, its powers
generate every element in the principal congruence kernel. -/
theorem principal_kernel_mem_powers_of_order (q d : ℕ) [NeZero q] [NeZero d]
    (hd : d ∣ q) (x : ZMod q)
    (hx : ZMod.castHom hd (ZMod d) x = 1)
    (horder : orderOf x = q / d) (z : ZMod q) :
    ∃ j : ℕ, x ^ j = 1 + (d : ZMod q) * z := by
  classical
  let π : ZMod q →+* ZMod d := ZMod.castHom hd (ZMod d)
  let K := {y : ZMod q // π y = 1}
  let f : Fin (orderOf x) → K := fun j => ⟨x ^ (j : ℕ), by
    change π (x ^ (j : ℕ)) = 1
    rw [map_pow, hx, one_pow]⟩
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := x) i.isLt j.isLt
    exact congrArg Subtype.val hij
  have hcard : Fintype.card (Fin (orderOf x)) = Fintype.card K := by
    simpa only [Fintype.card_fin, K, π, horder] using
      (card_reduction_one_fiber q d hd).symm
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩).surjective
  have ht : π (1 + (d : ZMod q) * z) = 1 := by
    simp only [map_add, map_one, map_mul, map_natCast, ZMod.natCast_self,
      zero_mul, add_zero]
  obtain ⟨j, hj⟩ := hsurj ⟨1 + (d : ZMod q) * z, ht⟩
  exact ⟨j, congrArg Subtype.val hj⟩

/-- A primitive principal unit generates its entire prime-power kernel.
The numerical condition includes odd primes at depth one and the prime two
at every depth at least two. -/
theorem prime_power_principal_kernel_mem_powers {p : ℕ} (hp : p.Prime)
    (m : ℕ) (hm : m ≠ 0) (hpm : m + 2 ≤ p * m)
    (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) (n : ℕ)
    (z : ZMod (p ^ (n + m))) :
    ∃ j : ℕ, (1 + p ^ m * a : ZMod (p ^ (n + m))) ^ j =
      1 + (p ^ m : ℕ) * z := by
  haveI : NeZero (p ^ (n + m)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p ^ m) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hd : p ^ m ∣ p ^ (n + m) := pow_dvd_pow p (by omega)
  apply principal_kernel_mem_powers_of_order (p ^ (n + m)) (p ^ m) hd
    (1 + p ^ m * a) _ _ z
  · simp only [map_add, map_one, map_mul, map_pow, map_natCast, map_intCast]
    rw [← Nat.cast_pow, ZMod.natCast_self, zero_mul, add_zero]
  · rw [ZMod.orderOf_one_add_mul_prime_pow hp m hm hpm a ha n,
      pow_add, Nat.mul_div_cancel _ (pow_pos hp.pos _)]

end StonehamNormality
