import XiWeightedBlock
import XiGapWeightedDepth

/-!
# Denominator depth for a nonzero periodic Xi block

One active residue suffices. Rounding a moving exponent upward into that
residue costs only a fixed number of exponent steps. The abstract translated
monoid theorem then gives denominator escape outside a density-zero set.
-/

noncomputable section
open Filter
open scoped BigOperators Classical Topology

namespace XiFamily

def activeRoundedDepth (L r k : ℕ) : ℕ := r + L * (k / L + 1)

theorem activeRoundedDepth_gt (L r k : ℕ) (hL : 0 < L) :
    k < activeRoundedDepth L r k := by
  have hmod := Nat.mod_lt k hL
  have hsplit := Nat.mod_add_div k L
  unfold activeRoundedDepth
  nlinarith

theorem activeRoundedDepth_le (L r k : ℕ) :
    activeRoundedDepth L r k ≤ k + (r + L) := by
  have hdiv := Nat.div_mul_le_self k L
  unfold activeRoundedDepth
  nlinarith

theorem weightedTerm_active_rounded_not_shallow {p b d a L : ℕ} [Fact p.Prime]
    (w : ℕ → ℚ) (hb : 0 < b) (ha : 2 ≤ a) (hd : 2 ≤ d) (had : a.Coprime d)
    (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (he : 0 < padicValNat p d)
    (hL : 0 < L) (hper : Function.Periodic w L) (r : ℕ) (hr : w r ≠ 0)
    (k i j : ℕ) :
    ¬ ValuationAtLeast p (padicValRat p (w r) - (k : ℤ) * padicValNat p d)
      (weightedTerm b d a w (a ^ i * d ^ (activeRoundedDepth L r k + L * j))) := by
  have hek : activeRoundedDepth L r k + L * j = r + (k / L + 1 + j) * L := by
    unfold activeRoundedDepth
    ring
  have hw : w (activeRoundedDepth L r k + L * j) = w r := by
    rw [hek]
    exact hper.nat_mul (k / L + 1 + j) r
  have hwnz : w (activeRoundedDepth L r k + L * j) ≠ 0 := by simpa only [hw] using hr
  have hnonzero := (weightedTerm_pair_ne_zero_iff w hb ha hd had i
    (activeRoundedDepth L r k + L * j)).mpr hwnz
  have hval := weightedTerm_valuation_pair w hb ha hd had hpa hpb i
    (activeRoundedDepth L r k + L * j) hwnz
  rw [hw] at hval
  have hdepth : k < activeRoundedDepth L r k + L * j :=
    (activeRoundedDepth_gt L r k hL).trans_le (Nat.le_add_right _ _)
  intro hbad
  rcases hbad with hzero | hv
  · exact hnonzero hzero
  · rw [hval] at hv
    have heZ : (0 : ℤ) < padicValNat p d := by exact_mod_cast he
    have hkZ : (k : ℤ) < (activeRoundedDepth L r k + L * j : ℕ) := by
      exact_mod_cast hdepth
    nlinarith

theorem weightedPrefix_shallow_density_zero_of_scale {p b d a L : ℕ} [Fact p.Prime]
    (w : ℕ → ℚ) (hb : 0 < b) (ha : 2 ≤ a) (hd : 2 ≤ d) (had : a.Coprime d)
    (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (he : 0 < padicValNat p d)
    (hL : 0 < L) (hper : Function.Periodic w L) (r : ℕ) (hr : w r ≠ 0)
    (k : ℕ → ℕ)
    (hscale : Tendsto (fun N : ℕ => (N : ℝ) / (d : ℝ) ^ (k N + (r + L))) atTop atTop) :
    Tendsto (fun N : ℕ =>
      (((Finset.Ico N (2 * N)).filter (fun n =>
        ValuationAtLeast p (padicValRat p (w r) - (k N : ℤ) * padicValNat p d)
          (∑ i ∈ Finset.range n, weightedTerm b d a w i))).card : ℝ) / N)
      atTop (𝓝 0) := by
  apply finite_valuation_fibers_shallow_density_zero
    (weightedTerm b d a w)
    (fun N => padicValRat p (w r) - (k N : ℤ) * padicValNat p d)
    (fun N => activeRoundedDepth L r (k N)) (valuationAlphabet p w L) ha hd had he hL
  · intro m hm
    exact weightedTerm_valuation_fibers w hb ha hd had hpa hpb hL hper hm
  · exact Eventually.of_forall (fun N i j =>
      weightedTerm_active_rounded_not_shallow w hb ha hd had hpa hpb he hL hper r hr (k N) i j)
  · apply tendsto_div_pow_atTop_of_eventually_le (by omega : 1 < d) hscale
    exact Eventually.of_forall (fun N => activeRoundedDepth_le L r (k N))

/-- Every fixed fraction below maximal logarithmic depth survives for a
periodic block with at least one nonzero coefficient. -/
theorem weightedPrefix_fractional_log_shallow_density_zero {p b d a L R : ℕ}
    [Fact p.Prime] (w : ℕ → ℚ) (hb : 0 < b) (ha : 2 ≤ a) (hd : 2 ≤ d)
    (had : a.Coprime d) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (he : 0 < padicValNat p d) (hL : 0 < L) (hper : Function.Periodic w L)
    (r : ℕ) (hr : w r ≠ 0) (hR : 0 < R) :
    Tendsto (fun N : ℕ =>
      (((Finset.Ico N (2 * N)).filter (fun n =>
        ValuationAtLeast p
          (padicValRat p (w r) - ((Nat.log d N - Nat.log d N / R : ℕ) : ℤ) * padicValNat p d)
          (∑ i ∈ Finset.range n, weightedTerm b d a w i))).card : ℝ) / N)
      atTop (𝓝 0) :=
  weightedPrefix_shallow_density_zero_of_scale w hb ha hd had hpa hpb he hL hper r hr
    (fun N => Nat.log d N - Nat.log d N / R)
    (tendsto_div_pow_fractional_log_atTop (by omega) hR (r + L))

end XiFamily
