import Japanese.Carnot.Algebra

/-!
# Carnot's theorem: geometric part

Every relevant point of a triangle `t` is written in the affine frame
`p₀ + α • (p₁ -ᵥ p₀) + β • (p₂ -ᵥ p₀)`; the metric facts are reduced to the polynomial
identities of `Carnot.Algebra`.  The techniques (`height_sq_mul_sq`, the frame lemmas) follow the
Feuerbach development.
-/

open EuclideanGeometry Affine Affine.Simplex
open scoped RealInnerProductSpace

namespace Carnot

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

lemma inner_vsub_vsub_eq_dist (p q r : P) :
    ⟪q -ᵥ p, r -ᵥ p⟫ = (dist p q ^ 2 + dist p r ^ 2 - dist q r ^ 2) / 2 := by
  rw [dist_eq_norm_vsub' V p q, dist_eq_norm_vsub' V p r, dist_eq_norm_vsub V q r,
    ← vsub_sub_vsub_cancel_right q r p, norm_sub_sq_real]
  ring

lemma inner_vsub_vsub_eq_dist' (p q r : P) :
    ⟪p -ᵥ q, p -ᵥ r⟫ = (dist p q ^ 2 + dist p r ^ 2 - dist q r ^ 2) / 2 := by
  rw [← neg_vsub_eq_vsub_rev q p, ← neg_vsub_eq_vsub_rev r p, inner_neg_neg]
  exact inner_vsub_vsub_eq_dist p q r

/-- Gram-determinant identity for the foot of a perpendicular. -/
lemma gram_of_foot (e₁ e₂ : V) (s H : ℝ)
    (h₁ : ⟪e₁, (1 - s) • e₁ + s • e₂⟫ = H) (h₂ : ⟪e₂, (1 - s) • e₁ + s • e₂⟫ = H) :
    H * ‖e₁ - e₂‖ ^ 2 = ‖e₁‖ ^ 2 * ‖e₂‖ ^ 2 - ⟪e₁, e₂⟫ ^ 2 := by
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq] at h₁
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm e₁ e₂] at h₂
  rw [norm_sub_sq_real]
  linear_combination (⟪e₁, e₂⟫ - ‖e₂‖ ^ 2) * h₁ + (⟪e₁, e₂⟫ - ‖e₁‖ ^ 2) * h₂

/-- The height of a triangle times the opposite side, squared, is Heron's expression. -/
lemma height_sq_mul_sq (t : Triangle ℝ P) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hS : ({i}ᶜ : Set (Fin 3)) = {j, k}) :
    t.height i ^ 2 * dist (t.points j) (t.points k) ^ 2 =
      heron (dist (t.points j) (t.points k)) (dist (t.points i) (t.points k))
        (dist (t.points i) (t.points j)) := by
  have hF := t.altitudeFoot_mem_affineSpan_image_compl i
  rw [hS, Set.image_pair] at hF
  obtain ⟨s, hs⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hF
  have hrep : t.points i -ᵥ t.altitudeFoot i =
      (1 - s) • (t.points i -ᵥ t.points j) + s • (t.points i -ᵥ t.points k) := by
    rw [← hs, AffineMap.lineMap_apply, vsub_vadd_eq_vsub_sub,
      ← vsub_sub_vsub_cancel_left (t.points k) (t.points j) (t.points i)]
    module
  have h₁ := t.inner_vsub_vsub_altitudeFoot_eq_height_sq hij
  have h₂ := t.inner_vsub_vsub_altitudeFoot_eq_height_sq hik
  rw [hrep] at h₁ h₂
  have hg := gram_of_foot _ _ s _ h₁ h₂
  rw [vsub_sub_vsub_cancel_left, ← dist_eq_norm_vsub, ← dist_eq_norm_vsub,
    ← dist_eq_norm_vsub, inner_vsub_vsub_eq_dist', dist_comm (t.points k)] at hg
  unfold heron
  linear_combination hg

section Frame

variable (t : Triangle ℝ P)

/-- Points of the plane of `t` written in the frame at vertex `0`. -/
lemma affineCombination_vsub_point_zero (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination ℝ t.points w -ᵥ t.points 0 =
      w 1 • (t.points 1 -ᵥ t.points 0) + w 2 • (t.points 2 -ᵥ t.points 0) := by
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ w _ hw (t.points 0),
    vadd_vsub, Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three, vsub_self, smul_zero,
    zero_add]

lemma dist_sq_eq_qf {X Y : P} {α β γ δ : ℝ}
    (hX : X -ᵥ t.points 0 = α • (t.points 1 -ᵥ t.points 0) + β • (t.points 2 -ᵥ t.points 0))
    (hY : Y -ᵥ t.points 0 = γ • (t.points 1 -ᵥ t.points 0) + δ • (t.points 2 -ᵥ t.points 0)) :
    dist X Y ^ 2 = qf (dist (t.points 1) (t.points 2)) (dist (t.points 0) (t.points 2))
      (dist (t.points 0) (t.points 1)) (α - γ) (β - δ) := by
  rw [dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right X Y (t.points 0), hX, hY]
  have e : α • (t.points 1 -ᵥ t.points 0) + β • (t.points 2 -ᵥ t.points 0) -
      (γ • (t.points 1 -ᵥ t.points 0) + δ • (t.points 2 -ᵥ t.points 0)) =
      (α - γ) • (t.points 1 -ᵥ t.points 0) + (β - δ) • (t.points 2 -ᵥ t.points 0) := by
    module
  rw [e, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    inner_vsub_vsub_eq_dist, ← dist_eq_norm_vsub, ← dist_eq_norm_vsub, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, dist_comm (t.points 1) (t.points 0),
    dist_comm (t.points 2) (t.points 0)]
  unfold qf
  ring

lemma point_zero_vsub : t.points 0 -ᵥ t.points 0 =
    (0 : ℝ) • (t.points 1 -ᵥ t.points 0) + (0 : ℝ) • (t.points 2 -ᵥ t.points 0) := by
  simp

lemma point_one_vsub : t.points 1 -ᵥ t.points 0 =
    (1 : ℝ) • (t.points 1 -ᵥ t.points 0) + (0 : ℝ) • (t.points 2 -ᵥ t.points 0) := by
  simp

lemma point_two_vsub : t.points 2 -ᵥ t.points 0 =
    (0 : ℝ) • (t.points 1 -ᵥ t.points 0) + (1 : ℝ) • (t.points 2 -ᵥ t.points 0) := by
  simp

/-- All the data needed from the triangle: barycentric weights `w` of the circumcentre, the
circumradius equations in the frame at vertex `0`, twice the area `k`, and the heights. -/
lemma frame_data : ∃ (w : Fin 3 → ℝ) (k : ℝ), 0 < k ∧ ∑ i, w i = 1 ∧
    t.circumcenter = Finset.univ.affineCombination ℝ t.points w ∧
    t.circumradius ^ 2 = qf (dist (t.points 1) (t.points 2)) (dist (t.points 0) (t.points 2))
      (dist (t.points 0) (t.points 1)) (0 - w 1) (0 - w 2) ∧
    t.circumradius ^ 2 = qf (dist (t.points 1) (t.points 2)) (dist (t.points 0) (t.points 2))
      (dist (t.points 0) (t.points 1)) (1 - w 1) (0 - w 2) ∧
    t.circumradius ^ 2 = qf (dist (t.points 1) (t.points 2)) (dist (t.points 0) (t.points 2))
      (dist (t.points 0) (t.points 1)) (0 - w 1) (1 - w 2) ∧
    2 * k * t.circumradius = dist (t.points 1) (t.points 2) * dist (t.points 0) (t.points 2) *
      dist (t.points 0) (t.points 1) ∧
    t.height 0 = k / dist (t.points 1) (t.points 2) ∧
    t.height 1 = k / dist (t.points 0) (t.points 2) ∧
    t.height 2 = k / dist (t.points 0) (t.points 1) := by
  set a := dist (t.points 1) (t.points 2) with ha
  set b := dist (t.points 0) (t.points 2) with hb
  set c := dist (t.points 0) (t.points 1) with hc
  have ha0 : 0 < a := dist_pos.2 (t.independent.injective.ne (by decide))
  have hb0 : 0 < b := dist_pos.2 (t.independent.injective.ne (by decide))
  have hc0 : 0 < c := dist_pos.2 (t.independent.injective.ne (by decide))
  obtain ⟨w, hw, hO⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
    t.circumcenter_mem_affineSpan
  have hOv : t.circumcenter -ᵥ t.points 0 =
      w 1 • (t.points 1 -ᵥ t.points 0) + w 2 • (t.points 2 -ᵥ t.points 0) := by
    rw [hO]; exact affineCombination_vsub_point_zero t w hw
  have hx : ∀ i, t.circumradius ^ 2 = dist (t.points i) t.circumcenter ^ 2 := fun i => by
    rw [t.dist_circumcenter_eq_circumradius i]
  have hx0 := hx 0
  rw [dist_sq_eq_qf t (point_zero_vsub t) hOv] at hx0
  have hx1 := hx 1
  rw [dist_sq_eq_qf t (point_one_vsub t) hOv] at hx1
  have hx2 := hx 2
  rw [dist_sq_eq_qf t (point_two_vsub t) hOv] at hx2
  have hh0 : t.height 0 ^ 2 * a ^ 2 = heron a b c :=
    height_sq_mul_sq t (i := 0) (j := 1) (k := 2) (by decide) (by decide)
      (by ext l; fin_cases l <;> simp)
  have hh1 : t.height 1 ^ 2 * b ^ 2 = heron a b c := by
    have := height_sq_mul_sq t (i := 1) (j := 0) (k := 2) (by decide) (by decide)
      (by ext l; fin_cases l <;> simp)
    rw [this, dist_comm (t.points 1) (t.points 0)]
    unfold heron; ring
  have hh2 : t.height 2 ^ 2 * c ^ 2 = heron a b c := by
    have := height_sq_mul_sq t (i := 2) (j := 0) (k := 1) (by decide) (by decide)
      (by ext l; fin_cases l <;> simp)
    rw [this, dist_comm (t.points 2) (t.points 0), dist_comm (t.points 2) (t.points 1)]
    unfold heron; ring
  have hp0 := t.height_pos 0
  have hp1 := t.height_pos 1
  have hp2 := t.height_pos 2
  obtain ⟨k, hk⟩ : ∃ k, k = t.height 0 * a := ⟨_, rfl⟩
  have hk0 : 0 < k := hk ▸ mul_pos hp0 ha0
  have e1 : t.height 1 * b = k :=
    (pow_left_inj₀ (mul_pos hp1 hb0).le hk0.le two_ne_zero).1
      (by rw [mul_pow, hh1, hk, mul_pow, hh0])
  have e2 : t.height 2 * c = k :=
    (pow_left_inj₀ (mul_pos hp2 hc0).le hk0.le two_ne_zero).1
      (by rw [mul_pow, hh2, hk, mul_pow, hh0])
  have hkh : k ^ 2 = heron a b c := by rw [hk, mul_pow, hh0]
  have hcirc := circ_relation a b c (w 1) (w 2) t.circumradius hx0 hx1 hx2
  have hR := t.circumradius_pos
  have hRk : 2 * k * t.circumradius = a * b * c := by
    refine (pow_left_inj₀ (mul_pos (mul_pos two_pos hk0) hR).le
      (mul_pos (mul_pos ha0 hb0) hc0).le two_ne_zero).1 ?_
    linear_combination (4 * t.circumradius ^ 2) * hkh + hcirc
  refine ⟨w, k, hk0, hw, hO, hx0, hx1, hx2, hRk, ?_, ?_, ?_⟩
  · rw [hk]; field_simp
  · rw [← e1]; field_simp
  · rw [← e2]; field_simp

end Frame

end Carnot
