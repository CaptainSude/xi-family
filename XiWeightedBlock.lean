import XiFamilyRational
import Mathlib.Algebra.Ring.Periodic

/-!
# Periodically weighted coprime Xi blocks

The definition uses canonical exponent coordinates on the distinct-index
support. Coprimality makes the chosen coordinates unique. A periodic
nonzero residue produces a translated two-generator submonoid of active
terms and a finite alphabet of exact valuation offsets.
-/

noncomputable section
open scoped BigOperators Classical

namespace XiFamily

def exponentPair (a d m : ℕ) : ℕ × ℕ :=
  if h : IsIndex a d m then (h.choose, h.choose_spec.choose) else (0, 0)

theorem exponentPair_spec {a d m : ℕ} (hm : IsIndex a d m) :
    m = a ^ (exponentPair a d m).1 * d ^ (exponentPair a d m).2 := by
  simp only [exponentPair, dif_pos hm]
  exact hm.choose_spec.choose_spec

theorem exponentPair_of_pair {a d : ℕ} (ha : 2 ≤ a) (hd : 2 ≤ d)
    (had : Nat.Coprime a d) (i k : ℕ) :
    exponentPair a d (a ^ i * d ^ k) = (i, k) := by
  apply index_injective ha hd had
  exact (exponentPair_spec (isIndex_mul_pow a d i k)).symm

def weightedTerm (b d a : ℕ) (w : ℕ → ℚ) (m : ℕ) : ℚ :=
  w (exponentPair a d m).2 * unshiftedTerm b d a m

theorem weightedTerm_pair {b d a : ℕ} (w : ℕ → ℚ) (ha : 2 ≤ a) (hd : 2 ≤ d)
    (had : Nat.Coprime a d) (i k : ℕ) :
    weightedTerm b d a w (a ^ i * d ^ k) =
      w k * unshiftedTerm b d a (a ^ i * d ^ k) := by
  simp [weightedTerm, exponentPair_of_pair ha hd had]

theorem weightedTerm_eq_zero_of_not_index {b d a m : ℕ} (w : ℕ → ℚ)
    (hm : ¬ IsIndex a d m) : weightedTerm b d a w m = 0 := by
  simp [weightedTerm, unshiftedTerm_eq_zero_of_not_index hm]

theorem weightedTerm_support {b d a m : ℕ} (w : ℕ → ℚ)
    (hm : weightedTerm b d a w m ≠ 0) : IsIndex a d m := by
  by_contra h
  exact hm (weightedTerm_eq_zero_of_not_index w h)

theorem weightedTerm_pair_ne_zero_iff {b d a : ℕ} (w : ℕ → ℚ)
    (hb : 0 < b) (ha : 2 ≤ a) (hd : 2 ≤ d) (had : Nat.Coprime a d) (i k : ℕ) :
    weightedTerm b d a w (a ^ i * d ^ k) ≠ 0 ↔ w k ≠ 0 := by
  rw [weightedTerm_pair w ha hd had]
  exact mul_ne_zero_iff.trans (and_iff_left
    (unshiftedTerm_ne_zero hb (by omega) (by omega) (isIndex_mul_pow a d i k)))

theorem weightedTerm_valuation_pair {p b d a : ℕ} [Fact p.Prime] (w : ℕ → ℚ)
    (hb : 0 < b) (ha : 2 ≤ a) (hd : 2 ≤ d) (had : Nat.Coprime a d)
    (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (i k : ℕ) (hw : w k ≠ 0) :
    padicValRat p (weightedTerm b d a w (a ^ i * d ^ k)) =
      padicValRat p (w k) - (k : ℤ) * padicValNat p d := by
  rw [weightedTerm_pair w ha hd had,
    padicValRat.mul hw (unshiftedTerm_ne_zero hb (by omega) (by omega)
      (isIndex_mul_pow a d i k)),
    unshiftedTerm_valuation_pair i k hb (by omega) (by omega) hpa hpb]
  ring

theorem periodic_weight_mod {w : ℕ → ℚ} {L : ℕ} (hper : Function.Periodic w L)
    (k : ℕ) : w k = w (k % L) := by
  have h : w (k % L + (k / L) * L) = w (k % L) := by
    simpa using hper.nat_mul (k / L) (k % L)
  rw [Nat.mul_comm (k / L) L, Nat.mod_add_div] at h
  exact h

def weightAlphabet (w : ℕ → ℚ) (L : ℕ) : Finset ℚ :=
  ((Finset.range L).image w).erase 0

theorem weightAlphabet_nonzero (w : ℕ → ℚ) (L : ℕ) : 0 ∉ weightAlphabet w L := by
  simp [weightAlphabet]

theorem weight_mem_alphabet {w : ℕ → ℚ} {L : ℕ} (hL : 0 < L)
    (hper : Function.Periodic w L) {k : ℕ} (hw : w k ≠ 0) :
    w k ∈ weightAlphabet w L := by
  apply Finset.mem_erase.mpr
  refine ⟨hw, Finset.mem_image.mpr ⟨k % L, ?_, (periodic_weight_mod hper k).symm⟩⟩
  exact Finset.mem_range.mpr (Nat.mod_lt k hL)

def valuationAlphabet (p : ℕ) (w : ℕ → ℚ) (L : ℕ) : Finset ℤ :=
  (weightAlphabet w L).image (padicValRat p)

theorem weightedTerm_valuation_fibers {p b d a L : ℕ} [Fact p.Prime]
    (w : ℕ → ℚ) (hb : 0 < b) (ha : 2 ≤ a) (hd : 2 ≤ d)
    (had : Nat.Coprime a d) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hL : 0 < L) (hper : Function.Periodic w L) {m : ℕ}
    (hm : weightedTerm b d a w m ≠ 0) :
    ∃ i k : ℕ, ∃ v ∈ valuationAlphabet p w L,
      m = a ^ i * d ^ k ∧ padicValRat p (weightedTerm b d a w m) =
        v - (k : ℤ) * padicValNat p d := by
  obtain ⟨i, k, rfl⟩ := weightedTerm_support w hm
  have hw := (weightedTerm_pair_ne_zero_iff w hb ha hd had i k).mp hm
  refine ⟨i, k, padicValRat p (w k), ?_, rfl, ?_⟩
  · exact Finset.mem_image.mpr ⟨w k, weight_mem_alphabet hL hper hw, rfl⟩
  · exact weightedTerm_valuation_pair w hb ha hd had hpa hpb i k hw

/-- Every active residue supplies the full translated monoid
`d^r * <a, d^L>` inside the nonzero support. -/
theorem weightedTerm_active_translate {b d a L : ℕ} (w : ℕ → ℚ)
    (hb : 0 < b) (ha : 2 ≤ a) (hd : 2 ≤ d) (had : Nat.Coprime a d)
    (hper : Function.Periodic w L) (r : ℕ) (hr : w r ≠ 0) (i j : ℕ) :
    weightedTerm b d a w (d ^ r * (a ^ i * (d ^ L) ^ j)) ≠ 0 := by
  have he : d ^ r * (a ^ i * (d ^ L) ^ j) = a ^ i * d ^ (r + j * L) := by
    rw [pow_add, Nat.mul_comm j L, pow_mul]
    ring
  rw [he, weightedTerm_pair_ne_zero_iff w hb ha hd had]
  have hw : w (r + j * L) = w r := by simpa using hper.nat_mul j r
  simpa only [hw] using hr

theorem weightedTerm_active_residue_valuation {p b d a L : ℕ} [Fact p.Prime]
    (w : ℕ → ℚ) (hb : 0 < b) (ha : 2 ≤ a) (hd : 2 ≤ d) (had : Nat.Coprime a d)
    (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hper : Function.Periodic w L)
    (r : ℕ) (hr : w r ≠ 0) (i j : ℕ) :
    padicValRat p (weightedTerm b d a w (a ^ i * d ^ (r + j * L))) =
      padicValRat p (w r) - ((r + j * L : ℕ) : ℤ) * padicValNat p d := by
  have hw : w (r + j * L) = w r := hper.nat_mul j r
  rw [weightedTerm_valuation_pair w hb ha hd had hpa hpb i (r + j * L) (hw ▸ hr), hw]

end XiFamily
