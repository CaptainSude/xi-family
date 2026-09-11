import XiGroupedDepth
import XiDominantBlock
import StonehamNormality.XiAnalyticDensity

/-! From a dominant periodic block to denominator escape for a finite sum. -/

noncomputable section
open Filter
open scoped BigOperators Classical Topology

namespace XiFamily

def combinationPrefix (b a : ℕ) (S : Finset ℕ) (q : ℕ → ℚ) (q₀ : ℚ) (n : ℕ) : ℚ :=
  q₀ + ∑ c ∈ S, q c * ∑ m ∈ Finset.range n, unshiftedTerm b c a m

theorem combinationPrefix_eq_classes (b a : ℕ) (S : Finset ℕ)
    (q : ℕ → ℚ) (q₀ : ℚ) (n : ℕ) :
    combinationPrefix b a S q q₀ n = q₀ +
      ∑ d ∈ S.image primitiveBase, ∑ m ∈ Finset.range n, classTerm b a S q d m := by
  unfold combinationPrefix
  congr 1
  rw [Finset.sum_comm]
  simp_rw [sum_classTerms, Finset.mul_sum]
  rw [Finset.sum_comm]

def combinationShallow (p b a : ℕ) (S : Finset ℕ) (q : ℕ → ℚ) (q₀ : ℚ)
    (d : ℕ) (C : ℤ) (n : ℕ) : Prop :=
  ValuationAtLeast p (C - ((Nat.log d (n / 2) / 2 : ℕ) : ℤ))
    (combinationPrefix b a S q q₀ n)

theorem half_le_fractional_depth (L R : ℕ) (hR : 2 ≤ R) :
    L / 2 ≤ L - L / R := by
  have hd : L / R ≤ L / 2 := Nat.div_le_div_left hR (by norm_num)
  omega

theorem fractional_depth_threshold_le_half {d R e N n : ℕ}
    (hR : 2 ≤ R) (he : 0 < e) (hn : n < 2 * N) (C : ℤ) :
    C - ((Nat.log d N - Nat.log d N / R : ℕ) : ℤ) * e ≤
      C - ((Nat.log d (n / 2) / 2 : ℕ) : ℤ) := by
  have hl := half_le_fractional_depth (Nat.log d N) R hR
  have hm : Nat.log d (n / 2) / 2 ≤ Nat.log d N / 2 :=
    Nat.div_le_div_right (Nat.log_mono_right (by omega : n / 2 ≤ N))
  have hk : ((Nat.log d (n / 2) / 2 : ℕ) : ℤ) ≤
      ((Nat.log d N - Nat.log d N / R : ℕ) : ℤ) := by exact_mod_cast hm.trans hl
  have heZ : (1 : ℤ) ≤ e := by exact_mod_cast he
  have hk0 : (0 : ℤ) ≤ ((Nat.log d N - Nat.log d N / R : ℕ) : ℤ) := by positivity
  nlinarith

theorem eventually_fractional_threshold_le_constant {d R e : ℕ}
    (hd : 2 ≤ d) (hR : 2 ≤ R) (he : 0 < e) (C A : ℤ) :
    ∀ᶠ N : ℕ in atTop,
      C - ((Nat.log d N - Nat.log d N / R : ℕ) : ℤ) * e ≤ A := by
  have hk : Tendsto (fun N : ℕ => Nat.log d N / 2) atTop atTop :=
    (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (tendsto_nat_log_atTop (by omega))
  filter_upwards [hk.eventually (eventually_ge_atTop (Int.toNat (C - A)))] with N hN
  have hl := half_le_fractional_depth (Nat.log d N) R hR
  have hCA : C - A ≤ (Int.toNat (C - A) : ℤ) := by omega
  have hN' : (Int.toNat (C - A) : ℤ) ≤ (Nat.log d N / 2 : ℕ) := by exact_mod_cast hN
  have hl' : ((Nat.log d N / 2 : ℕ) : ℤ) ≤
      ((Nat.log d N - Nat.log d N / R : ℕ) : ℤ) := by exact_mod_cast hl
  have he' : (1 : ℤ) ≤ e := by exact_mod_cast he
  have hk0 : (0 : ℤ) ≤ ((Nat.log d N - Nat.log d N / R : ℕ) : ℤ) := by positivity
  nlinarith

theorem combinationShallow_density_zero_of_dominance {p b a d R : ℕ} [Fact p.Prime]
    (S : Finset ℕ) (q : ℕ → ℚ) (q₀ : ℚ)
    (ha : 2 ≤ a) (hb : 0 < b) (hS : ∀ c ∈ S, 2 ≤ c)
    (hcop : ∀ c ∈ S, c.Coprime (a * b))
    (hd : d ∈ S.image primitiveBase) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (he : 0 < padicValNat p d) (r : ℕ) (hr : classWeight S q d r ≠ 0)
    (hR : 2 ≤ R)
    (hdom : ∀ᶠ N : ℕ in atTop, ∀ e ∈ S.image primitiveBase, e ≠ d →
      padicValRat p (classWeight S q d r) -
        ((Nat.log d N - Nat.log d N / R : ℕ) : ℤ) * padicValNat p d ≤
      coefficientValuationFloor p S q - (Nat.log e (2 * N) : ℤ) * padicValNat p e) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (combinationShallow p b a S q q₀ d
        (padicValRat p (classWeight S q d r)))).card : ℝ) / N) atTop (𝓝 0) := by
  have hdprop := primitiveBase_mem_properties S hS hcop hd
  have hd2 := hdprop.1.1
  have had : a.Coprime d := (hdprop.2.of_dvd_right (dvd_mul_right a b)).symm
  have hL := classPeriod_pos S d hS
  have hper := classWeight_periodic S q d
  have hdyadic := weightedPrefix_fractional_log_shallow_density_zero
    (classWeight S q d) hb ha hd2 had hpa hpb he hL hper r hr (show 0 < R by omega)
  apply StonehamNormality.xi_density_zero_of_dyadic_density_zero
  apply squeeze_zero' (Eventually.of_forall (fun N => by positivity)) ?_ hdyadic
  have hconst := eventually_fractional_threshold_le_constant hd2 hR he
    (padicValRat p (classWeight S q d r)) (padicValRat p q₀)
  filter_upwards [hdom, hconst] with N hdomN hq₀
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnI, hnsh⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨hnI, ?_⟩
  have hnn := (Finset.mem_Ico.mp hnI).2
  let v : ℤ := padicValRat p (classWeight S q d r) -
    ((Nat.log d N - Nat.log d N / R : ℕ) : ℤ) * padicValNat p d
  have htotal : ValuationAtLeast p v (combinationPrefix b a S q q₀ n) :=
    valuationAtLeast_mono (fractional_depth_threshold_le_half hR he hnn _) hnsh
  rw [combinationPrefix_eq_classes] at htotal
  have hsum : ValuationAtLeast p v
      (∑ e ∈ S.image primitiveBase, ∑ m ∈ Finset.range n, classTerm b a S q e m) := by
    have ht := valuationAtLeast_sub htotal (Or.inr hq₀ : ValuationAtLeast p v q₀)
    simpa using ht
  have hrest : ∀ e ∈ S.image primitiveBase, e ≠ d → ValuationAtLeast p v
      (∑ m ∈ Finset.range n, classTerm b a S q e m) := by
    intro e heD hed
    have heprop := primitiveBase_mem_properties S hS hcop heD
    have hae : a.Coprime e := (heprop.2.of_dvd_right (dvd_mul_right a b)).symm
    exact valuationAtLeast_mono (hdomN e heD hed)
      (classPrefix_valuation_lower_bound S q ha heprop.1.1 hb hae hpa hpb hS
        (2 * N) n hnn.le)
  have hstar : ValuationAtLeast p v
      (∑ m ∈ Finset.range n, classTerm b a S q d m) := by
    by_contra h
    exact not_valuationAtLeast_sum_of_one_deep (S.image primitiveBase)
      (fun e => ∑ m ∈ Finset.range n, classTerm b a S q e m) d hd v h hrest hsum
  simpa only [classTerm_eq_weightedTerm b a d S q ha hd2 had hS] using hstar

end XiFamily
