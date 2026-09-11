import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic

/-! Finite rational combinations of divisibility filters cannot vanish
identically. These filters are the exponent weights obtained by grouping
multiplicatively dependent parameters. -/

open scoped BigOperators

namespace XiFamily

def divisibilityWeight (s : Finset ℕ) (q : ℕ → ℚ) (k : ℕ) : ℚ :=
  ∑ r ∈ s, if r ∣ k then q r else 0

theorem divisibilityWeight_nonzero (s : Finset ℕ) (q : ℕ → ℚ)
    (hpos : ∀ r ∈ s, 0 < r) (hq : ∃ r ∈ s, q r ≠ 0) :
    ∃ k, 0 < k ∧ divisibilityWeight s q k ≠ 0 := by
  classical
  let t := s.filter (fun r => q r ≠ 0)
  obtain ⟨r, hr, hqr⟩ := hq
  have ht : t.Nonempty := ⟨r, Finset.mem_filter.mpr ⟨hr, hqr⟩⟩
  let j := t.min' ht
  have hj := Finset.min'_mem t ht
  have hjs : j ∈ s := (Finset.mem_filter.mp hj).1
  have hqj : q j ≠ 0 := (Finset.mem_filter.mp hj).2
  refine ⟨j, hpos j hjs, ?_⟩
  have he : divisibilityWeight s q j = q j := by
    unfold divisibilityWeight
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      by_cases hkd : k ∣ j
      · rw [if_pos hkd]
        by_contra hqk
        have hkt : k ∈ t := Finset.mem_filter.mpr ⟨hk, hqk⟩
        have hjk : j ≤ k := Finset.min'_le t k hkt
        have hkj' : k ≤ j := Nat.le_of_dvd (hpos j hjs) hkd
        exact hkj (Nat.le_antisymm hkj' hjk)
      · simp [hkd]
    · exact fun h => False.elim (h hjs)
  rw [he]
  exact hqj

theorem divisibilityWeight_periodic (s : Finset ℕ) (q : ℕ → ℚ) (L : ℕ)
    (hL : ∀ r ∈ s, r ∣ L) : Function.Periodic (divisibilityWeight s q) L := by
  intro k
  unfold divisibilityWeight
  apply Finset.sum_congr rfl
  intro r hr
  have he : r ∣ k + L ↔ r ∣ k := by
    constructor
    · intro h
      exact (Nat.dvd_add_iff_left (hL r hr)).mpr h
    · intro h
      exact dvd_add h (hL r hr)
  simp only [he]

/-- The same noncancellation result for an arbitrary finite indexing type. -/
theorem indexed_divisibility_weight_nonzero {ι : Type*} (J : Finset ι)
    (r : ι → ℕ) (q : ι → ℚ)
    (hpos : ∀ j ∈ J, 0 < r j)
    (hinj : ∀ i ∈ J, ∀ j ∈ J, r i = r j → i = j)
    (hq : ∃ j ∈ J, q j ≠ 0) :
    ∃ k, 0 < k ∧ (∑ j ∈ J, if r j ∣ k then q j else 0) ≠ 0 := by
  classical
  let S := J.filter (fun j => q j ≠ 0)
  obtain ⟨i, hi, hqi⟩ := hq
  have hS : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hqi⟩⟩
  obtain ⟨j, hj, hmin⟩ := S.exists_min_image r hS
  have hjJ := (Finset.mem_filter.mp hj).1
  have hqj := (Finset.mem_filter.mp hj).2
  refine ⟨r j, hpos j hjJ, ?_⟩
  have he : (∑ i ∈ J, if r i ∣ r j then q i else 0) = q j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij
      by_cases hdiv : r i ∣ r j
      · rw [if_pos hdiv]
        by_contra hqi
        have hle := hmin i (Finset.mem_filter.mpr ⟨hi, hqi⟩)
        have hge := Nat.le_of_dvd (hpos j hjJ) hdiv
        exact hij (hinj i hi j hjJ (Nat.le_antisymm hge hle))
      · simp [hdiv]
    · exact fun h => False.elim (h hjJ)
  simpa only [he] using hqj

def rectangularWeight (s : Finset (ℕ × ℕ)) (q : (ℕ × ℕ) → ℚ)
    (i k : ℕ) : ℚ :=
  ∑ rs ∈ s, if rs.1 ∣ i ∧ rs.2 ∣ k then q rs else 0

theorem rectangularWeight_nonzero (s : Finset (ℕ × ℕ)) (q : (ℕ × ℕ) → ℚ)
    (hpos : ∀ rs ∈ s, 0 < rs.1 ∧ 0 < rs.2)
    (hq : ∃ rs ∈ s, q rs ≠ 0) :
    ∃ i k, 0 < i ∧ 0 < k ∧ rectangularWeight s q i k ≠ 0 := by
  classical
  let t := s.filter (fun rs => q rs ≠ 0)
  obtain ⟨rs, hrs, hqrs⟩ := hq
  have ht : t.Nonempty := ⟨rs, Finset.mem_filter.mpr ⟨hrs, hqrs⟩⟩
  obtain ⟨j, hj, hmin⟩ := t.exists_min_image (fun rs => rs.1 * rs.2) ht
  have hjs : j ∈ s := (Finset.mem_filter.mp hj).1
  have hqj : q j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hjpos := hpos j hjs
  refine ⟨j.1, j.2, hjpos.1, hjpos.2, ?_⟩
  have he : rectangularWeight s q j.1 j.2 = q j := by
    unfold rectangularWeight
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      by_cases hkd : k.1 ∣ j.1 ∧ k.2 ∣ j.2
      · rw [if_pos hkd]
        by_contra hqk
        have hkt : k ∈ t := Finset.mem_filter.mpr ⟨hk, hqk⟩
        have hprod := hmin k hkt
        have hkpos := hpos k hk
        have hfirst : k.1 ≤ j.1 := Nat.le_of_dvd hjpos.1 hkd.1
        have hsecond : k.2 ≤ j.2 := Nat.le_of_dvd hjpos.2 hkd.2
        have he1 : k.1 = j.1 := by nlinarith
        have he2 : k.2 = j.2 := by nlinarith
        exact hkj (Prod.ext he1 he2)
      · simp [hkd]
    · exact fun h => False.elim (h hjs)
  rw [he]
  exact hqj

end XiFamily
