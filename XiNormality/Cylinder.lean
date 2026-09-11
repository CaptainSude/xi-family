import XiNormality.Definitions
import XiNormality.Weyl

/-!
# From circle equidistribution to binary normality

The circle representative in `[0,1)` is continuous except at zero. Thus the
boundary of a cylinder arc consists of at most its two endpoints and zero,
and normalized Haar measure assigns zero mass to that boundary.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped BigOperators Topology Classical ENNReal

namespace XiNormality

def circleRepresentative (x : UnitAddCircle) : ℝ := AddCircle.equivIco 1 0 x

theorem circleRepresentative_coe (x : ℝ) :
    circleRepresentative (x : UnitAddCircle) = Int.fract x := by
  simp [circleRepresentative, AddCircle.coe_equivIco_mk_apply]

theorem coe_circleRepresentative (x : UnitAddCircle) :
    (circleRepresentative x : UnitAddCircle) = x :=
  AddCircle.coe_equivIco

theorem measurable_circleRepresentative : Measurable circleRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

theorem continuousAt_circleRepresentative {x : UnitAddCircle} (hx : x ≠ 0) :
    ContinuousAt circleRepresentative x :=
  continuousAt_subtype_val.comp (AddCircle.continuousAt_equivIco (1 : ℝ) 0 hx)

private theorem mem_frontier_preimage_of_continuousAt
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {s : Set Y} {x : X} (hf : ContinuousAt f x)
    (hx : x ∈ frontier (f ⁻¹' s)) : f x ∈ frontier s := by
  rw [frontier_eq_closure_inter_closure] at hx ⊢
  refine ⟨?_, ?_⟩
  · exact closure_mono (image_preimage_subset f s) (mem_closure_image hf hx.1)
  · exact closure_mono (image_preimage_subset f sᶜ) (mem_closure_image hf hx.2)

def circleArc (a b : ℝ) : Set UnitAddCircle := circleRepresentative ⁻¹' Ico a b

theorem measurableSet_circleArc (a b : ℝ) : MeasurableSet (circleArc a b) :=
  measurable_circleRepresentative measurableSet_Ico

theorem frontier_circleArc_subset {a b : ℝ} (hab : a < b) :
    frontier (circleArc a b) ⊆ {0, (a : UnitAddCircle), (b : UnitAddCircle)} := by
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx' := mem_frontier_preimage_of_continuousAt
    (continuousAt_circleRepresentative hx0) hx
  rw [frontier_Ico hab, mem_insert_iff, mem_singleton_iff] at hx'
  rcases hx' with ha | hb
  · have : x = (a : UnitAddCircle) := by rw [← coe_circleRepresentative x, ha]
    simp [this]
  · have : x = (b : UnitAddCircle) := by rw [← coe_circleRepresentative x, hb]
    simp [this]

theorem uniformCircle_toMeasure_eq_volume :
    (uniformCircle : Measure UnitAddCircle) = volume := by
  simpa [uniformCircle] using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm

theorem circleArc_null_frontier {a b : ℝ} (hab : a < b) :
    (uniformCircle : Measure UnitAddCircle) (frontier (circleArc a b)) = 0 := by
  apply measure_mono_null (frontier_circleArc_subset hab)
  rw [uniformCircle_toMeasure_eq_volume]
  let : NullSingletonClass (volume : Measure UnitAddCircle) :=
    ⟨fun x => by simpa using AddCircle.volume_closedBall (T := (1 : ℝ)) (x := x) (0 : ℝ)⟩
  exact (((Set.finite_singleton (b : UnitAddCircle)).insert (a : UnitAddCircle)).insert 0).measure_zero volume

theorem uniformCircle_circleArc {a b : ℝ} (ha : 0 ≤ a) (_hab : a < b) (hb : b ≤ 1) :
    (uniformCircle : Measure UnitAddCircle) (circleArc a b) = ENNReal.ofReal (b - a) := by
  rw [uniformCircle_toMeasure_eq_volume,
    ← (AddCircle.measurePreserving_mk (1 : ℝ) 0).map_eq,
    Measure.map_apply AddCircle.measurable_mk' (measurableSet_circleArc a b)]
  rw [← restrict_Ico_eq_restrict_Ioc,
    Measure.restrict_apply ((measurableSet_circleArc a b).preimage AddCircle.measurable_mk')]
  have heq : ((↑) : ℝ → UnitAddCircle) ⁻¹' circleArc a b ∩ Ico 0 (0 + 1) = Ico a b := by
    ext x
    constructor
    · rintro ⟨hx, hx01⟩
      have hfract : Int.fract x = x := Int.fract_eq_self.mpr (by simpa using hx01)
      simpa [circleArc, circleRepresentative_coe, hfract] using hx
    · intro hx
      have hx01 : x ∈ Ico (0 : ℝ) 1 := ⟨ha.trans hx.1, hx.2.trans_le hb⟩
      have hfract : Int.fract x = x := Int.fract_eq_self.mpr hx01
      exact ⟨by simpa [circleArc, circleRepresentative_coe, hfract] using hx, by simpa using hx01⟩
  rw [heq, Real.volume_Ico]

/-- The interval-frequency version of the qualitative Weyl criterion. -/
theorem circleArc_frequency_tendsto_of_fourier
    (u : ℕ → UnitAddCircle)
    (h : ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ •
        ∑ i ∈ Finset.range N, fourier (T := 1) k (u i)) atTop (𝓝 0))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Tendsto (fun N =>
      (((Finset.range N).filter (fun i => u i ∈ circleArc a b)).card : ℝ) / N)
      atTop (𝓝 (b - a)) := by
  have hshift : ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun N => ((N + 1 : ℕ) : ℝ)⁻¹ •
        ∑ i ∈ Finset.range (N + 1), fourier (T := 1) k (u i)) atTop (𝓝 0) := by
    intro k hk
    exact (h k hk).comp (tendsto_add_atTop_nat 1)
  have hm := empiricalCircle_tendsto_measure u hshift (circleArc_null_frontier hab)
  rw [uniformCircle_circleArc ha hab hb] at hm
  have hr := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hm
  have hden (N : ℕ) : ((N : ℝ≥0∞) + 1).toReal = (N : ℝ) + 1 := by
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp
  simp only [Function.comp_def, empiricalCircle_apply u _ (measurableSet_circleArc a b),
    ENNReal.toReal_div, ENNReal.toReal_natCast, hden,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)] at hr
  exact (tendsto_add_atTop_iff_nat 1).mp (by simpa using hr)

/-- Fourier cancellation of the binary radix orbit implies binary normality. -/
theorem binaryNormal_of_fourier (x : ℝ)
    (h : ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ •
        ∑ i ∈ Finset.range N,
          fourier (T := 1) k (((2 : ℝ) ^ i * x : ℝ) : UnitAddCircle))
        atTop (𝓝 0)) :
    BinaryNormal x := by
  intro l j hj
  have hp : (0 : ℝ) < 2 ^ l := by positivity
  have ha : (0 : ℝ) ≤ j / 2 ^ l := by positivity
  have hab : (j : ℝ) / 2 ^ l < ((j : ℝ) + 1) / 2 ^ l := by
    exact div_lt_div_of_pos_right (by linarith) hp
  have hb : ((j : ℝ) + 1) / 2 ^ l ≤ 1 := by
    apply (div_le_iff₀ hp).mpr
    simpa using (show (j : ℝ) + 1 ≤ (2 : ℝ) ^ l by exact_mod_cast Nat.succ_le_of_lt hj)
  have hf := circleArc_frequency_tendsto_of_fourier
    (fun i => (((2 : ℝ) ^ i * x : ℝ) : UnitAddCircle)) h ha hab hb
  have hlength : ((j : ℝ) + 1) / 2 ^ l - (j : ℝ) / 2 ^ l = ((2 : ℝ) ^ l)⁻¹ := by
    ring
  change Tendsto (fun N =>
    (((Finset.range N).filter (fun n => binaryOrbit x n ∈ binaryCylinder l j)).card : ℝ) / N)
    atTop (𝓝 ((2 : ℝ) ^ l)⁻¹)
  simpa only [binaryOrbit, binaryCylinder, circleArc, Set.mem_preimage,
    circleRepresentative_coe, hlength] using hf

end XiNormality
