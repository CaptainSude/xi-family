import XiValuationEscape
import Mathlib.Data.Finset.Card
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic

/-! A finite covering form of the denominator-escape argument. -/

open scoped BigOperators Classical
open Filter
open scoped Topology

namespace XiFamily

/-- Covering a dyadic interval by `K` short blocks converts the local gap bound
into a bound for all shallow prefixes in that interval. -/
theorem shallow_prefix_dyadic_card_le {p : ℕ} [Fact p.Prime]
    (f : ℕ → ℚ) (v : ℤ) (N K W H : ℕ)
    (hW : 0 < W) (hcover : N ≤ K * W)
    (hinj : ∀ j < K, ∀ i ∈ Finset.Ico (N + j * W) (N + (j + 1) * W),
      ∀ k ∈ Finset.Ico (N + j * W) (N + (j + 1) * W),
      f i ≠ 0 → f k ≠ 0 →
      padicValRat p (f i) = padicValRat p (f k) → i = k)
    (hdeep : ∀ x, N ≤ x → x + H ≤ N + K * W →
      ∃ m ∈ Finset.Ico x (x + H), ¬ ValuationAtLeast p v (f m)) :
    ((Finset.Ico N (2 * N)).filter (fun n =>
      ValuationAtLeast p v (∑ i ∈ Finset.range n, f i))).card ≤ K * H := by
  let bad : ℕ → Prop := fun n => ValuationAtLeast p v (∑ i ∈ Finset.range n, f i)
  let block : ℕ → Finset ℕ := fun j =>
    (Finset.Icc (N + j * W) (N + (j + 1) * W)).filter bad
  have hblock : ∀ j ∈ Finset.range K, (block j).card ≤ H := by
    intro j hj
    have hjK : j < K := Finset.mem_range.mp hj
    apply shallow_prefix_card_le f v (N + j * W) (N + (j + 1) * W) H
      (hinj j hjK)
    intro x hx hxu
    apply hdeep x (le_trans (Nat.le_add_right _ _) hx)
    have hbound : (j + 1) * W ≤ K * W := Nat.mul_le_mul_right W (by omega)
    omega
  have hsub : (Finset.Ico N (2 * N)).filter bad ⊆
      (Finset.range K).biUnion block := by
    intro n hn
    obtain ⟨hnI, hnb⟩ := Finset.mem_filter.mp hn
    have hnN := (Finset.mem_Ico.mp hnI).1
    have hn2N := (Finset.mem_Ico.mp hnI).2
    let j := (n - N) / W
    have hjK : j < K := by
      apply (Nat.div_lt_iff_lt_mul hW).mpr
      omega
    have hjlo : j * W ≤ n - N := Nat.div_mul_le_self (n - N) W
    have hjhi : n - N < (j + 1) * W := by
      have hmod := Nat.mod_lt (n - N) hW
      have hsplit := Nat.mod_add_div (n - N) W
      dsimp [j]
      nlinarith
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_range.mpr hjK, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hnb⟩
  calc
    _ ≤ ((Finset.range K).biUnion block).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range K, (block j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range K, H := Finset.sum_le_sum hblock
    _ = K * H := by simp

/-- The exceptional-prefix proportion tends to zero when valuations are
separated on a fixed number of local blocks and deeper insertions have
arbitrarily small relative gaps. The depth threshold may move with the scale. -/
theorem shallow_prefix_dyadic_density_zero {p : ℕ} [Fact p.Prime]
    (f : ℕ → ℚ) (v : ℕ → ℤ) (K : ℕ) (hK : 0 < K)
    (hinj : ∀ᶠ N : ℕ in atTop,
      ∀ j < K, ∀ i ∈ Finset.Ico (N + j * (N / K + 1)) (N + (j + 1) * (N / K + 1)),
        ∀ k ∈ Finset.Ico (N + j * (N / K + 1)) (N + (j + 1) * (N / K + 1)),
        f i ≠ 0 → f k ≠ 0 →
        padicValRat p (f i) = padicValRat p (f k) → i = k)
    (hgap : ∀ L : ℕ, 0 < L → ∀ᶠ N : ℕ in atTop,
      ∀ x, N ≤ x → x + N / L ≤ 3 * N →
        ∃ m ∈ Finset.Ico x (x + N / L), ¬ ValuationAtLeast p (v N) (f m)) :
    Tendsto (fun N : ℕ =>
      (((Finset.Ico N (2 * N)).filter (fun n =>
        ValuationAtLeast p (v N) (∑ i ∈ Finset.range n, f i))).card : ℝ) / N)
      atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    exact Eventually.of_forall (fun N => lt_of_lt_of_le hr (by positivity))
  · intro ε hε
    obtain ⟨L, hL⟩ := exists_nat_gt ((K : ℝ) / ε)
    have hLpos : 0 < L := by
      have hratio : 0 ≤ (K : ℝ) / ε := by positivity
      have : (0 : ℝ) < L := lt_of_le_of_lt hratio hL
      exact_mod_cast this
    have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
    have hsmall : (K : ℝ) / L < ε := by
      apply (div_lt_iff₀ hLR).mpr
      have h := (div_lt_iff₀ hε).mp hL
      nlinarith
    filter_upwards [hinj, hgap L hLpos, eventually_ge_atTop K,
      eventually_ge_atTop 1] with N hNinj hNdeep hNK hNpos
    have hcover : N ≤ K * (N / K + 1) := by
      have hmod := Nat.mod_lt N hK
      have hsplit := Nat.mod_add_div N K
      nlinarith
    have hupper : N + K * (N / K + 1) ≤ 3 * N := by
      have hmul := Nat.div_mul_le_self N K
      nlinarith
    have hcard := shallow_prefix_dyadic_card_le f (v N) N K (N / K + 1) (N / L)
      (Nat.succ_pos _) hcover hNinj (by
        intro x hx hxu
        exact hNdeep x hx (hxu.trans hupper))
    have hdiv := Nat.div_mul_le_self N L
    have hcount :
        (((Finset.Ico N (2 * N)).filter (fun n =>
          ValuationAtLeast p (v N) (∑ i ∈ Finset.range n, f i))).card : ℝ) * L ≤
          (K : ℝ) * N := by
      have hcardR :
          (((Finset.Ico N (2 * N)).filter (fun n =>
            ValuationAtLeast p (v N) (∑ i ∈ Finset.range n, f i))).card : ℝ) ≤
              (K : ℝ) * (N / L : ℕ) := by exact_mod_cast hcard
      have hdivR : ((N / L : ℕ) : ℝ) * L ≤ N := by exact_mod_cast hdiv
      nlinarith [Nat.cast_nonneg (α := ℝ) K]
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    exact lt_of_le_of_lt ((div_le_div_iff₀ hNR hLR).mpr hcount) hsmall

end XiFamily
