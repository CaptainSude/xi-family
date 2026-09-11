import XiNormality.Imports

/-!
# A qualitative Weyl criterion on the unit circle

The first result isolates the general analytic step: convergence of the integrals
of the integer Fourier characters implies weak convergence of probability measures.
It uses the Stone--Weierstrass and tightness results already checked in mathlib.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators Topology ComplexConjugate Classical BoundedContinuousFunction ENNReal

namespace XiNormality

private lemma continuousMap_integrable (g : C(UnitAddCircle, ℂ))
    (μ : ProbabilityMeasure UnitAddCircle) : Integrable g μ := by
  exact (BoundedContinuousFunction.integrable (μ : Measure UnitAddCircle)
    (BoundedContinuousFunction.mkOfCompact g)).congr
      (Filter.Eventually.of_forall fun x => BoundedContinuousFunction.mkOfCompact_apply g x)

/-- Qualitative Weyl criterion, expressed as weak convergence of circle measures. -/
theorem probabilityMeasure_tendsto_of_fourier
    {ι : Type*} {F : Filter ι}
    {μ : ι → ProbabilityMeasure UnitAddCircle}
    {ν : ProbabilityMeasure UnitAddCircle}
    (h : ∀ k : ℤ,
      Tendsto (fun i => ∫ x, fourier (T := 1) k x ∂(μ i)) F
        (𝓝 (∫ x, fourier (T := 1) k x ∂ν))) :
    Tendsto μ F (𝓝 ν) := by
  have hspan : ∀ g : C(UnitAddCircle, ℂ),
      g ∈ Submodule.span ℂ (Set.range (fourier (T := 1))) →
      Tendsto (fun i => ∫ x, g x ∂(μ i)) F (𝓝 (∫ x, g x ∂ν)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨k, rfl⟩ := hg
        exact h k
    | zero => simpa using (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℂ)) F (𝓝 0))
    | add g₁ g₂ hg₁ hg₂ h₁ h₂ =>
        simpa only [ContinuousMap.add_apply,
          integral_add (continuousMap_integrable g₁ _) (continuousMap_integrable g₂ _)]
          using h₁.add h₂
    | smul c g hg ih =>
        simpa only [ContinuousMap.smul_apply, integral_smul]
          using ih.const_smul c
  let A : StarSubalgebra ℂ (UnitAddCircle →ᵇ ℂ) :=
    (fourierSubalgebra (T := 1)).comap
      (BoundedContinuousFunction.toContinuousMapStarₐ ℂ)
  have hmap : A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℂ) =
      fourierSubalgebra (T := 1) := by
    ext g
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact hf
    · intro hg
      exact ⟨BoundedContinuousFunction.mkOfCompact g, hg, rfl⟩
  apply ProbabilityMeasure.tendsto_of_tight_of_separatesPoints ℂ
    IsTightMeasureSet.of_compactSpace (A := A)
  · rw [hmap]
    exact fourierSubalgebra_separatesPoints
  · intro g hg
    apply hspan g.toContinuousMap
    change g.toContinuousMap ∈
      (fourierSubalgebra (T := 1)).toSubalgebra.toSubmodule at hg
    rwa [fourierSubalgebra_coe] at hg

/-- Normalized Haar measure on the unit circle as a probability measure. -/
def uniformCircle : ProbabilityMeasure UnitAddCircle :=
  ⟨AddCircle.haarAddCircle, inferInstance⟩

theorem integral_fourier_uniformCircle (k : ℤ) :
    (∫ x, fourier (T := 1) k x ∂uniformCircle) = if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) k) 0
  simpa [fourierCoeff, uniformCircle, Pi.single_apply, eq_comm] using h

/-- The usual nonzero-frequency formulation of the qualitative Weyl criterion. -/
theorem probabilityMeasure_tendsto_uniform_of_fourier
    {ι : Type*} {F : Filter ι}
    {μ : ι → ProbabilityMeasure UnitAddCircle}
    (h : ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun i => ∫ x, fourier (T := 1) k x ∂(μ i)) F (𝓝 0)) :
    Tendsto μ F (𝓝 uniformCircle) := by
  apply probabilityMeasure_tendsto_of_fourier
  intro k
  rw [integral_fourier_uniformCircle]
  by_cases hk : k = 0
  · subst k
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ι => (1 : ℂ)) F (𝓝 1))
  · simpa [hk] using h k hk

/-- Empirical measure of the first `N + 1` points; the shift avoids an empty average. -/
def empiricalCircle (u : ℕ → UnitAddCircle) (N : ℕ) : ProbabilityMeasure UnitAddCircle :=
  ProbabilityMeasure.map
    (⟨(PMF.uniformOfFintype (Fin (N + 1))).toMeasure, inferInstance⟩ :
      ProbabilityMeasure (Fin (N + 1))) (fun i => u i)

theorem integral_empiricalCircle (u : ℕ → UnitAddCircle) (N : ℕ)
    (g : C(UnitAddCircle, ℂ)) :
    (∫ x, g x ∂(empiricalCircle u N)) =
      ((N + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ Finset.range (N + 1), g (u i) := by
  change (∫ x, g x ∂Measure.map (fun i : Fin (N + 1) => u i)
    (PMF.uniformOfFintype (Fin (N + 1))).toMeasure) = _
  rw [integral_map (measurable_of_finite _).aemeasurable g.continuous.aestronglyMeasurable,
    PMF.integral_eq_sum]
  simp_rw [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  rw [← Finset.smul_sum]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => g (u i)) (N + 1)

theorem empiricalCircle_apply (u : ℕ → UnitAddCircle) (N : ℕ)
    {s : Set UnitAddCircle} (hs : MeasurableSet s) :
    (empiricalCircle u N : Measure UnitAddCircle) s =
      (((Finset.range (N + 1)).filter (fun i => u i ∈ s)).card : ℝ≥0∞) / (N + 1) := by
  change (Measure.map (fun i : Fin (N + 1) => u i)
    (PMF.uniformOfFintype (Fin (N + 1))).toMeasure) s = _
  rw [Measure.map_apply (measurable_of_finite _) hs,
    PMF.toMeasure_uniformOfFintype_apply _ (measurable_of_finite _ hs)]
  simp only [Fintype.card_fin, Fintype.card_subtype, Finset.card_filter,
    Nat.cast_add, Nat.cast_one, Set.mem_preimage]
  rw [Fin.sum_univ_eq_sum_range (fun i => if u i ∈ s then (1 : ℕ) else 0) (N + 1)]

/-- Exponential cancellation gives weak equidistribution of empirical circle measures. -/
theorem empiricalCircle_tendsto_uniform
    (u : ℕ → UnitAddCircle)
    (h : ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun N => ((N + 1 : ℕ) : ℝ)⁻¹ •
        ∑ i ∈ Finset.range (N + 1), fourier (T := 1) k (u i))
        atTop (𝓝 0)) :
    Tendsto (empiricalCircle u) atTop (𝓝 uniformCircle) := by
  apply probabilityMeasure_tendsto_uniform_of_fourier
  intro k hk
  simpa only [integral_empiricalCircle] using h k hk

/-- Consequently, empirical frequencies converge on every set of Haar-null boundary. -/
theorem empiricalCircle_tendsto_measure
    (u : ℕ → UnitAddCircle)
    (h : ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun N => ((N + 1 : ℕ) : ℝ)⁻¹ •
        ∑ i ∈ Finset.range (N + 1), fourier (T := 1) k (u i))
        atTop (𝓝 0))
    {s : Set UnitAddCircle} (hs : (uniformCircle : Measure UnitAddCircle) (frontier s) = 0) :
    Tendsto (fun N => (empiricalCircle u N : Measure UnitAddCircle) s)
      atTop (𝓝 ((uniformCircle : Measure UnitAddCircle) s)) :=
  ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (empiricalCircle_tendsto_uniform u h) hs

end XiNormality
