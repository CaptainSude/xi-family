import XiPrimitiveParameters
import XiParameterGrouping
import XiFamilyRational

/-! Grouping a finite Xi combination into primitive periodic blocks. -/

noncomputable section
open scoped BigOperators Classical

namespace XiFamily

def parameterClass (S : Finset ℕ) (d : ℕ) : Finset ℕ :=
  S.filter (fun c => primitiveBase c = d)

def classWeight (S : Finset ℕ) (q : ℕ → ℚ) (d k : ℕ) : ℚ :=
  ∑ c ∈ parameterClass S d, if primitiveExponent c ∣ k then q c else 0

theorem primitiveExponent_injOn_class (S : Finset ℕ) (d : ℕ)
    (hS : ∀ c ∈ S, 2 ≤ c) :
    ∀ c ∈ parameterClass S d, ∀ e ∈ parameterClass S d,
      primitiveExponent c = primitiveExponent e → c = e := by
  intro c hc e he hce
  obtain ⟨hcS, hcd⟩ := Finset.mem_filter.mp hc
  obtain ⟨heS, hed⟩ := Finset.mem_filter.mp he
  obtain ⟨_, _, hcp⟩ := primitive_parameters_spec (hS c hcS)
  obtain ⟨_, _, hep⟩ := primitive_parameters_spec (hS e heS)
  calc
    c = primitiveBase c ^ primitiveExponent c := hcp
    _ = primitiveBase e ^ primitiveExponent e := by rw [hcd, hed, hce]
    _ = e := hep.symm

theorem classWeight_nonzero (S : Finset ℕ) (q : ℕ → ℚ) (d : ℕ)
    (hS : ∀ c ∈ S, 2 ≤ c) (hq : ∃ c ∈ parameterClass S d, q c ≠ 0) :
    ∃ k, 0 < k ∧ classWeight S q d k ≠ 0 := by
  apply indexed_divisibility_weight_nonzero (parameterClass S d) primitiveExponent q
  · intro c hc
    exact (primitive_parameters_spec (hS c (Finset.mem_filter.mp hc).1)).2.1
  · exact primitiveExponent_injOn_class S d hS
  · exact hq

def classPeriod (S : Finset ℕ) (d : ℕ) : ℕ :=
  ∏ c ∈ parameterClass S d, primitiveExponent c

theorem classPeriod_pos (S : Finset ℕ) (d : ℕ) (hS : ∀ c ∈ S, 2 ≤ c) :
    0 < classPeriod S d := by
  apply Finset.prod_pos
  intro c hc
  exact (primitive_parameters_spec (hS c (Finset.mem_filter.mp hc).1)).2.1

theorem classWeight_periodic (S : Finset ℕ) (q : ℕ → ℚ) (d : ℕ) :
    Function.Periodic (classWeight S q d) (classPeriod S d) := by
  intro k
  unfold classWeight
  apply Finset.sum_congr rfl
  intro c hc
  have hdiv : primitiveExponent c ∣ classPeriod S d :=
    Finset.dvd_prod_of_mem primitiveExponent hc
  have he : primitiveExponent c ∣ k + classPeriod S d ↔ primitiveExponent c ∣ k :=
    (Nat.dvd_add_iff_left hdiv).symm
  simp only [he]

def coefficientAlphabet (S : Finset ℕ) (q : ℕ → ℚ) : Finset ℚ :=
  S.powerset.image (fun T => ∑ c ∈ T, q c)

theorem classWeight_mem_alphabet (S : Finset ℕ) (q : ℕ → ℚ) (d k : ℕ) :
    classWeight S q d k ∈ coefficientAlphabet S q := by
  let T := (parameterClass S d).filter (fun c => primitiveExponent c ∣ k)
  have hT : T ⊆ S := by
    intro c hc
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
  apply Finset.mem_image.mpr
  refine ⟨T, Finset.mem_powerset.mpr hT, ?_⟩
  simp [T, classWeight, Finset.sum_filter]

def classTerm (b a : ℕ) (S : Finset ℕ) (q : ℕ → ℚ) (d m : ℕ) : ℚ :=
  ∑ c ∈ parameterClass S d, q c * unshiftedTerm b c a m

theorem unshiftedTerm_power_parameter (b a d r i k : ℕ)
    (ha : 2 ≤ a) (hd : 2 ≤ d) (had : a.Coprime d) :
    unshiftedTerm b (d ^ r) a (a ^ i * d ^ k) =
      if r ∣ k then 1 / (((a ^ i * d ^ k : ℕ) : ℚ) *
        (b : ℚ) ^ (a ^ i * d ^ k)) else 0 := by
  simp only [unshiftedTerm, isIndex_power_parameter_iff ha hd had]

theorem classTerm_at_pair (b a d i k : ℕ) (S : Finset ℕ) (q : ℕ → ℚ)
    (ha : 2 ≤ a) (hd : 2 ≤ d) (had : a.Coprime d)
    (hS : ∀ c ∈ S, 2 ≤ c) :
    classTerm b a S q d (a ^ i * d ^ k) =
      classWeight S q d k /
        (((a ^ i * d ^ k : ℕ) : ℚ) * (b : ℚ) ^ (a ^ i * d ^ k)) := by
  unfold classTerm classWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨hcS, hcd⟩ := Finset.mem_filter.mp hc
  have hcp : c = d ^ primitiveExponent c := by
    simpa only [hcd] using (primitive_parameters_spec (hS c hcS)).2.2
  have ht := unshiftedTerm_power_parameter b a d (primitiveExponent c) i k ha hd had
  rw [← hcp] at ht
  rw [ht]
  split_ifs <;> simp [div_eq_mul_inv]

theorem classTerm_eq_zero_of_not_index (b a d m : ℕ)
    (S : Finset ℕ) (q : ℕ → ℚ) (hS : ∀ c ∈ S, 2 ≤ c)
    (hm : ¬ IsIndex a d m) : classTerm b a S q d m = 0 := by
  unfold classTerm
  apply Finset.sum_eq_zero
  intro c hc
  obtain ⟨hcS, hcd⟩ := Finset.mem_filter.mp hc
  have hcp : c = d ^ primitiveExponent c := by
    simpa only [hcd] using (primitive_parameters_spec (hS c hcS)).2.2
  have hnot : ¬ IsIndex a c m := by
    rintro ⟨i, k, he⟩
    apply hm
    refine ⟨i, primitiveExponent c * k, ?_⟩
    calc
      m = a ^ i * c ^ k := he
      _ = a ^ i * (d ^ primitiveExponent c) ^ k :=
        congrArg (fun t => a ^ i * t ^ k) hcp
      _ = _ := by rw [pow_mul]
  simp [unshiftedTerm_eq_zero_of_not_index hnot]

theorem sum_parameterClasses {β : Type*} [AddCommMonoid β]
    (S : Finset ℕ) (f : ℕ → β) :
    (∑ d ∈ S.image primitiveBase, ∑ c ∈ parameterClass S d, f c) = ∑ c ∈ S, f c := by
  exact Finset.sum_fiberwise_of_maps_to (g := primitiveBase) (s := S)
    (t := S.image primitiveBase) (f := f)
    (fun c hc => Finset.mem_image.mpr ⟨c, hc, rfl⟩)

theorem sum_classTerms (b a m : ℕ) (S : Finset ℕ) (q : ℕ → ℚ) :
    (∑ d ∈ S.image primitiveBase, classTerm b a S q d m) =
      ∑ c ∈ S, q c * unshiftedTerm b c a m :=
  sum_parameterClasses S (fun c => q c * unshiftedTerm b c a m)

end XiFamily
