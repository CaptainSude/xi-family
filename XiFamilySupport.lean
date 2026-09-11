import XiFamilySeries

/-!
# Finite support and denominator bounds for Xi truncations

Every cutoff contains at most a product of two logarithmic factors.
The reduced denominator divides the product of the two maximal generator
powers, hence has fixed prime support and is at most the square of the cutoff.
-/

noncomputable section
open scoped BigOperators Classical

namespace XiFamily

def indices (a c n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (IsIndex a c)

theorem mem_indices_iff (a c n m : ℕ) :
    m ∈ indices a c n ↔ m ≤ n ∧ IsIndex a c m := by
  simp only [indices, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

theorem exponents_le_log {a c n i k : ℕ} (ha : 2 ≤ a) (hc : 2 ≤ c)
    (hn : a ^ i * c ^ k ≤ n) : i ≤ Nat.log a n ∧ k ≤ Nat.log c n := by
  have hai : 1 ≤ a ^ i := Nat.one_le_pow _ _ (by omega)
  have hck : 1 ≤ c ^ k := Nat.one_le_pow _ _ (by omega)
  constructor
  · exact Nat.le_log_of_pow_le (by omega) (by nlinarith)
  · exact Nat.le_log_of_pow_le (by omega) (by nlinarith)

theorem indices_subset_image (a c n : ℕ) (ha : 2 ≤ a) (hc : 2 ≤ c) :
    indices a c n ⊆
      ((Finset.range (Nat.log a n + 1)) ×ˢ (Finset.range (Nat.log c n + 1))).image
        (fun p : ℕ × ℕ => a ^ p.1 * c ^ p.2) := by
  intro m hm
  obtain ⟨hmn, i, k, rfl⟩ := (mem_indices_iff a c n m).mp hm
  obtain ⟨hi, hk⟩ := exponents_le_log ha hc hmn
  exact Finset.mem_image.mpr ⟨(i, k), by simp [hi, hk, Nat.lt_succ_iff], rfl⟩

theorem indices_card_le (a c n : ℕ) (ha : 2 ≤ a) (hc : 2 ≤ c) :
    (indices a c n).card ≤ (Nat.log a n + 1) * (Nat.log c n + 1) := by
  calc
    _ ≤ (((Finset.range (Nat.log a n + 1)) ×ˢ
        (Finset.range (Nat.log c n + 1))).image
          (fun p : ℕ × ℕ => a ^ p.1 * c ^ p.2)).card :=
      Finset.card_le_card (indices_subset_image a c n ha hc)
    _ ≤ ((Finset.range (Nat.log a n + 1)) ×ˢ
        (Finset.range (Nat.log c n + 1))).card := Finset.card_image_le
    _ = _ := by simp

theorem indices_union_card_le {ι : Type*} (J : Finset ι) (a c : ι → ℕ) (n : ℕ)
    (ha : ∀ j ∈ J, 2 ≤ a j) (hc : ∀ j ∈ J, 2 ≤ c j) :
    (J.biUnion (fun j => indices (a j) (c j) n)).card ≤
      ∑ j ∈ J, (Nat.log (a j) n + 1) * (Nat.log (c j) n + 1) := by
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum (fun j hj => indices_card_le _ _ _ (ha j hj) (hc j hj)))

/-- A denominator clearing factor with only generator primes. -/
def denominatorBound (a c n : ℕ) : ℕ := a ^ Nat.log a n * c ^ Nat.log c n

theorem index_dvd_denominatorBound {a c n m : ℕ} (ha : 2 ≤ a) (hc : 2 ≤ c)
    (hm : m ∈ indices a c n) : m ∣ denominatorBound a c n := by
  obtain ⟨hmn, i, k, rfl⟩ := (mem_indices_iff a c n m).mp hm
  obtain ⟨hi, hk⟩ := exponents_le_log ha hc hmn
  exact Nat.mul_dvd_mul (pow_dvd_pow a hi) (pow_dvd_pow c hk)

theorem denominatorBound_pos (a c n : ℕ) (ha : 2 ≤ a) (hc : 2 ≤ c) :
    0 < denominatorBound a c n := by
  unfold denominatorBound
  positivity

theorem denominatorBound_le_square (a c n : ℕ) (hn : n ≠ 0) :
    denominatorBound a c n ≤ n ^ 2 := by
  have ha := Nat.pow_log_le_self a hn
  have hc := Nat.pow_log_le_self c hn
  simpa [denominatorBound, pow_two] using Nat.mul_le_mul ha hc

theorem nat_div_den_dvd (u v : ℕ) : ((u : ℚ) / v).den ∣ v := by
  have h := Rat.den_dvd (u : ℤ) (v : ℤ)
  simp only [Rat.divInt_eq_div, Int.cast_natCast] at h
  exact_mod_cast h

theorem sum_den_dvd_of_den_dvd {ι : Type*} (J : Finset ι) (f : ι → ℚ) (D : ℕ)
    (h : ∀ j ∈ J, (f j).den ∣ D) : (∑ j ∈ J, f j).den ∣ D := by
  induction J using Finset.induction_on with
  | empty => simp
  | @insert j J hj ih =>
    rw [Finset.sum_insert hj]
    apply (Rat.add_den_dvd_lcm _ _).trans
    exact Nat.lcm_dvd (h j (by simp)) (ih (fun k hk => h k (by simp [hk])))

theorem truncation_den_dvd (b c a n : ℕ) (ha : 2 ≤ a) (hc : 2 ≤ c) :
    (truncation b c a n).den ∣ denominatorBound a c n := by
  apply sum_den_dvd_of_den_dvd
  intro m hm
  have hd : ((b : ℚ) ^ (n - m) / m).den ∣ m := by
    simpa only [Nat.cast_pow] using nat_div_den_dvd (b ^ (n - m)) m
  exact hd.trans (index_dvd_denominatorBound ha hc hm)

theorem truncation_den_le_square (b c a n : ℕ) (ha : 2 ≤ a) (hc : 2 ≤ c)
    (hn : n ≠ 0) : (truncation b c a n).den ≤ n ^ 2 :=
  (Nat.le_of_dvd (denominatorBound_pos a c n ha hc) (truncation_den_dvd b c a n ha hc)).trans
    (denominatorBound_le_square a c n hn)

theorem truncation_den_prime {b c a n p : ℕ} (ha : 2 ≤ a) (hc : 2 ≤ c)
    (hp : p.Prime) (hpd : p ∣ (truncation b c a n).den) : p ∣ a ∨ p ∣ c := by
  have h := hpd.trans (truncation_den_dvd b c a n ha hc)
  rcases hp.dvd_mul.mp h with h | h
  · exact Or.inl (hp.dvd_of_dvd_pow h)
  · exact Or.inr (hp.dvd_of_dvd_pow h)

end XiFamily
