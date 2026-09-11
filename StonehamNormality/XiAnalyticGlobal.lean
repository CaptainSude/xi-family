import StonehamNormality.XiAnalyticDyadic
import StonehamNormality.GeneralGlobalOrbit

/-!
# Fixed-support cancellation at arbitrary polynomial scales

Increasing the depth `d` increases the permissible logarithmic denominator to
interval-length ratio without bound. Increasing `M` decreases the required
positive lower denominator slope. The argument uses only the previously
verified Stoneham bound and finite amplification; no published estimate is
assumed as an axiom.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace StonehamNormality

/-- A uniform power saving for every fixed polynomial denominator range.
The upper denominator exponent divided by the length exponent is `2+d/2`;
the lower ratio is `1/(2M)`. Both parameters are unrestricted. -/
theorem xi_fixed_support_global_character_bound
    (b S M d : ℕ) (hb : 1 < b) (hS : 0 < S)
    (hcop : b.Coprime S) (hM : 1 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop,
      XiUniformOrbitBound b S
        (2 ^ ((144 * 2 ^ d) * B))
        (2 ^ (((144 * M * d + 576 * M) * 2 ^ d) * B))
        (2 ^ ((288 * M * 2 ^ d) * B))
        (K * (2 : ℝ) ^ (((288 * M * 2 ^ d) - 1) * B)) := by
  obtain ⟨K₀, hK₀, hbase⟩ := fixed_support_global_character_bound b S M hb hS hcop hM
  obtain ⟨B₀, hbase⟩ := eventually_atTop.1 hbase
  let s := (2 : ℕ) ^ d
  let C := supportStrideExponent S
  let D := b ^ C - 1
  have hs : 1 ≤ s := one_le_pow₀ (by norm_num)
  have hMs : s ≤ M * s := by nlinarith
  have ht : s ≤ 288 * M * s := by nlinarith
  refine ⟨xiAmplificationConstant K₀ d, xiAmplificationConstant_nonneg K₀ hK₀ d, ?_⟩
  filter_upwards [eventually_ge_atTop (max B₀ (max (C * D) (D ^ 2)))] with B hB
  have hB₀ : B₀ ≤ B := (Nat.le_max_left _ _).trans hB
  have hBmax : max (C * D) (D ^ 2) ≤ B := (Nat.le_max_right _ _).trans hB
  have hCD : C * D ≤ 2 ^ B :=
    ((Nat.le_max_left _ _).trans hBmax).trans (Nat.lt_two_pow_self.le)
  have hDsq : D ^ 2 ≤ 2 ^ B :=
    ((Nat.le_max_right _ _).trans hBmax).trans (Nat.lt_two_pow_self.le)
  let R := (2 : ℕ) ^ ((144 * s) * B)
  let U := (2 : ℕ) ^ ((576 * M * s) * B)
  let V := (2 : ℕ) ^ ((144 * M * s) * B)
  let H := (2 : ℕ) ^ ((2 * s) * B)
  have hVU : V ≤ U := by
    apply pow_le_pow_right₀ (by norm_num)
    nlinarith
  have hstep : H * (C * (D * V)) ≤ 2 ^ ((288 * M * s) * B) := by
    calc
      _ = (C * D) * 2 ^ (((2 * s) + 144 * M * s) * B) := by
        dsimp [H, V]
        rw [Nat.add_mul, pow_add]
        ring
      _ ≤ 2 ^ B * 2 ^ (((2 * s) + 144 * M * s) * B) := Nat.mul_le_mul_right _ hCD
      _ = 2 ^ ((1 + 2 * s + 144 * M * s) * B) := by
        rw [← pow_add]
        congr 1
        ring
      _ ≤ _ := by
        apply pow_le_pow_right₀ (by norm_num)
        apply Nat.mul_le_mul_right B
        nlinarith
  have hgap : (D ^ 2 * V * H) * R ≤ U := by
    calc
      _ = D ^ 2 * 2 ^ (((144 * M * s) + 2 * s + 144 * s) * B) := by
        dsimp [V, H, R]
        rw [Nat.add_mul, Nat.add_mul, pow_add, pow_add]
        ring
      _ ≤ 2 ^ B * 2 ^ (((144 * M * s) + 2 * s + 144 * s) * B) :=
        Nat.mul_le_mul_right _ hDsq
      _ = 2 ^ ((1 + 144 * M * s + 2 * s + 144 * s) * B) := by
        rw [← pow_add]
        congr 1
        ring
      _ ≤ U := by
        apply pow_le_pow_right₀ (by norm_num)
        apply Nat.mul_le_mul_right B
        nlinarith
  have hinner : XiUniformOrbitBound b S R U (2 ^ ((288 * M * s) * B))
      (K₀ * (2 : ℝ) ^ (((288 * M * s) - s) * B)) := by
    intro q _ hRq hqU hsupport A hA L hL
    have hBs : B₀ ≤ s * B := hB₀.trans (by nlinarith)
    have hlow : 2 ^ (144 * (s * B)) ≤ q := by
      convert hRq using 1 <;> dsimp [R] <;> congr 1 <;> ring
    have hupp : q ≤ 2 ^ (576 * M * (s * B)) := by
      convert hqU using 1 <;> dsimp [U] <;> congr 1 <;> ring
    have hlen : L ≤ (2 ^ (288 * M)) ^ (s * B) := by
      rw [← pow_mul]
      convert hL using 1 <;> congr 1 <;> ring
    have hh := hbase (s * B) hBs q A L hlow hupp hsupport hA hlen
    have hexp : (288 * M - 1) * (s * B) = ((288 * M * s) - s) * B := by
      rw [← Nat.mul_assoc, Nat.sub_mul, one_mul]
    simpa only [← pow_mul, hexp] using hh
  have hfinal := xi_fixed_support_dyadic_iteration b S R U V H B (288 * M * s) d K₀
    hb hS hcop (by dsimp [H]; positivity) (by dsimp [V]; positivity) hVU hK₀ ht
    hstep hgap (by rfl) hinner
  have hupper : V ^ d * U =
      2 ^ (((144 * M * d + 576 * M) * s) * B) := by
    dsimp [V, U]
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [hupper] at hfinal
  exact hfinal

end StonehamNormality
