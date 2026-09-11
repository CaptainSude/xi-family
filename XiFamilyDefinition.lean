import StonehamNormality.GeneralSeries

/-!
# The Xi family, defined by distinct multiplicative indices

`xi b c a` denotes the sum of `1 / (m * b^m)` over distinct natural
numbers of the form `a^i * c^k`. In particular `a = 1` includes the
Stoneham boundary without counting an index infinitely many times.
-/

noncomputable section
open scoped BigOperators Classical

namespace XiFamily

def IsIndex (a c m : ℕ) : Prop := ∃ i k : ℕ, m = a ^ i * c ^ k

def term (b c a m : ℕ) : ℝ :=
  if IsIndex a c m then 1 / ((m : ℝ) * (b : ℝ) ^ m) else 0

/-- The first argument is the expansion base; the last is the added generator. -/
def xi (b c a : ℕ) : ℝ := ∑' m : ℕ, term b c a m

theorem isIndex_one (a c : ℕ) : IsIndex a c 1 := ⟨0, 0, by simp⟩

theorem isIndex_mul_pow (a c i k : ℕ) : IsIndex a c (a ^ i * c ^ k) :=
  ⟨i, k, rfl⟩

theorem isIndex_pos {a c m : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hm : IsIndex a c m) : 0 < m := by
  obtain ⟨i, k, rfl⟩ := hm
  positivity

theorem term_nonneg (b c a m : ℕ) : 0 ≤ term b c a m := by
  unfold term
  split_ifs <;> positivity

theorem term_le_geometric (b c a m : ℕ) (hb : 2 ≤ b) :
    term b c a m ≤ (1 / 2 : ℝ) ^ m := by
  by_cases hm0 : m = 0
  · subst m
    simp [term]
  have hbr : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbp : (0 : ℝ) < b := by linarith
  have hp : (2 : ℝ) ^ m ≤ (b : ℝ) ^ m :=
    pow_le_pow_left₀ (by norm_num) hbr m
  unfold term
  split_ifs
  · have hone : (1 : ℝ) ≤ m := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm0)
    rw [one_div_pow]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [pow_pos hbp m]
  · positivity

/-- Convergence is uniform in the two multiplicative generators. -/
theorem summable_term (b c a : ℕ) (hb : 2 ≤ b) : Summable (term b c a) :=
  Summable.of_nonneg_of_le (term_nonneg b c a)
    (fun m => term_le_geometric b c a m hb)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

theorem xi_nonneg (b c a : ℕ) : 0 ≤ xi b c a :=
  tsum_nonneg (term_nonneg b c a)

theorem xi_original : xi 2 3 2 = XiNormality.xi := by
  unfold xi XiNormality.xi
  apply tsum_congr
  intro m
  rfl

theorem isIndex_one_generator_iff (c m : ℕ) :
    IsIndex 1 c m ↔ m = 1 ∨ StonehamNormality.IsStonehamIndex c m := by
  constructor
  · rintro ⟨i, k, hk⟩
    simp only [one_pow, one_mul] at hk
    by_cases hk0 : k = 0
    · left
      simpa [hk0] using hk
    · right
      exact ⟨k, Nat.pos_of_ne_zero hk0, hk⟩
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact isIndex_one 1 c
    · exact ⟨0, k, by simp⟩

theorem not_stonehamIndex_one (c : ℕ) (hc : 2 ≤ c) :
    ¬ StonehamNormality.IsStonehamIndex c 1 := by
  rintro ⟨k, hk, he⟩
  have he' : c ^ k = c ^ 0 := by simpa using he.symm
  have := Nat.pow_right_injective hc he'
  omega

/-- Removing the initial index gives exactly the conventional Stoneham series. -/
theorem xi_stoneham_boundary (b c : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    xi b c 1 = 1 / (b : ℝ) + StonehamNormality.stonehamConstant b c := by
  unfold xi
  rw [(summable_term b c 1 hb).tsum_eq_add_tsum_ite 1]
  have hfirst : term b c 1 1 = 1 / (b : ℝ) := by
    simp [term, isIndex_one]
  rw [hfirst]
  congr 1
  rw [← StonehamNormality.sparseStonehamConstant_eq_standard b c hc]
  apply tsum_congr
  intro m
  by_cases hm : m = 1
  · subst m
    simp [StonehamNormality.radixStonehamTerm, not_stonehamIndex_one c hc]
  · simp [hm, term, isIndex_one_generator_iff, StonehamNormality.radixStonehamTerm]

/-- Coprime generators give each index a unique exponent pair. -/
theorem index_injective {a c : ℕ} (ha : 2 ≤ a) (hc : 2 ≤ c)
    (hac : Nat.Coprime a c) :
    Function.Injective (fun p : ℕ × ℕ => a ^ p.1 * c ^ p.2) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ he
  dsimp at he
  have hdiv₁ : a ^ i ∣ a ^ j :=
    ((hac.pow_left i).pow_right l).dvd_of_dvd_mul_right
      (he ▸ Nat.dvd_mul_right (a ^ i) (c ^ k))
  have hdiv₂ : a ^ j ∣ a ^ i :=
    ((hac.pow_left j).pow_right k).dvd_of_dvd_mul_right
      (he.symm ▸ Nat.dvd_mul_right (a ^ j) (c ^ l))
  have haij : a ^ i = a ^ j := Nat.dvd_antisymm hdiv₁ hdiv₂
  have hij : i = j := Nat.pow_right_injective ha haij
  subst j
  have hckl : c ^ k = c ^ l := Nat.eq_of_mul_eq_mul_left (by positivity) he
  have hkl : k = l := Nat.pow_right_injective hc hckl
  exact Prod.ext rfl hkl

theorem term_support_subset_index_range (b c a : ℕ) :
    Function.support (term b c a) ⊆
      Set.range (fun p : ℕ × ℕ => a ^ p.1 * c ^ p.2) := by
  intro m hm
  have hs : IsIndex a c m := by
    by_contra h
    simp [Function.mem_support, term, h] at hm
  obtain ⟨i, k, hi⟩ := hs
  exact ⟨(i, k), hi.symm⟩

theorem summable_exponent_pairs (b c a : ℕ) (hb : 2 ≤ b) (ha : 2 ≤ a)
    (hc : 2 ≤ c) (hac : Nat.Coprime a c) :
    Summable (fun p : ℕ × ℕ =>
      1 / (((a ^ p.1 * c ^ p.2 : ℕ) : ℝ) * (b : ℝ) ^ (a ^ p.1 * c ^ p.2))) := by
  have h := (summable_term b c a hb).comp_injective (index_injective ha hc hac)
  simpa only [Function.comp_def, term, isIndex_mul_pow, ite_true] using h

/-- For coprime generators, the distinct-index and double-series definitions agree. -/
theorem xi_eq_double_series (b c a : ℕ) (hb : 2 ≤ b) (ha : 2 ≤ a)
    (hc : 2 ≤ c) (hac : Nat.Coprime a c) :
    xi b c a = ∑' i : ℕ, ∑' k : ℕ,
      1 / (((a : ℝ) ^ i * (c : ℝ) ^ k) * (b : ℝ) ^ (a ^ i * c ^ k)) := by
  calc
    xi b c a = ∑' p : ℕ × ℕ, term b c a (a ^ p.1 * c ^ p.2) :=
      ((index_injective ha hc hac).tsum_eq (term_support_subset_index_range b c a)).symm
    _ = ∑' p : ℕ × ℕ,
        1 / (((a ^ p.1 * c ^ p.2 : ℕ) : ℝ) * (b : ℝ) ^ (a ^ p.1 * c ^ p.2)) := by
      apply tsum_congr
      intro p
      simp [term, isIndex_mul_pow]
    _ = _ := by
      rw [(summable_exponent_pairs b c a hb ha hc hac).tsum_prod]
      simp only [Nat.cast_mul, Nat.cast_pow]

end XiFamily
