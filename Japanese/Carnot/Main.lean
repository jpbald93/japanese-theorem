import Japanese.Carnot.Geometry

/-!
# Carnot's theorem (inradius, circumradius)

For a triangle `t` with circumcentre `O`, circumradius `R` and inradius `r`, the signed distances
from `O` to the three side lines sum to `R + r`.

The signed distance from a point `p` to the side line opposite vertex `i` is the component of
`p -ᵥ Fᵢ` along the unit normal `(Aᵢ -ᵥ Fᵢ) / hᵢ` pointing from the side line towards the
opposite vertex `Aᵢ` (`Fᵢ` the foot of the altitude from `Aᵢ`, `hᵢ` the height). It is therefore
positive exactly on the side of the line containing the interior of the triangle; for an obtuse
triangle, the circumcentre gets a negative distance to the side opposite the obtuse angle.
We show this agrees with Mathlib's `Affine.Simplex.signedInfDist` on the plane of the triangle.
-/

open EuclideanGeometry Affine Affine.Simplex
open scoped RealInnerProductSpace

namespace Carnot

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Signed distance from `p` to the side line of `t` opposite vertex `i`, positive on the side of
vertex `i` (i.e. on the side of the interior of the triangle). -/
noncomputable def signedSideDist (t : Triangle ℝ P) (i : Fin 3) (p : P) : ℝ :=
  ⟪p -ᵥ t.altitudeFoot i, t.points i -ᵥ t.altitudeFoot i⟫ / t.height i

variable (t : Triangle ℝ P)

/-- For a point given by barycentric weights `w`, the signed distance to side `i` is
`w i * height i`. -/
lemma signedSideDist_affineCombination (w : Fin 3 → ℝ) (hw : ∑ j, w j = 1) (i : Fin 3) :
    signedSideDist t i (Finset.univ.affineCombination ℝ t.points w) = w i * t.height i := by
  unfold signedSideDist
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ w _ hw
      (t.altitudeFoot i), vadd_vsub, Finset.weightedVSubOfPoint_apply, sum_inner,
    Finset.sum_eq_single i]
  · rw [real_inner_smul_left, real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub, ← height]
    have := t.height_pos i
    field_simp
  · intro j _ hj
    rw [real_inner_smul_left, t.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero (Ne.symm hj),
      mul_zero]
  · simp

/-- Our signed distance agrees with Mathlib's `signedInfDist` on the plane of the triangle. -/
lemma signedSideDist_eq_signedInfDist {p : P} (hp : p ∈ affineSpan ℝ (Set.range t.points))
    (i : Fin 3) : signedSideDist t i p = t.signedInfDist i p := by
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
  rw [signedSideDist_affineCombination t w hw, signedInfDist_affineCombination _ _ hw, height,
    dist_eq_norm_vsub V]
  rfl

/-- The vertex `i` lies at signed distance `height i > 0` from the opposite side. -/
lemma signedSideDist_point_self (i : Fin 3) :
    signedSideDist t i (t.points i) = t.height i := by
  unfold signedSideDist
  rw [real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub, ← height]
  have := t.height_pos i
  field_simp

/-- The incentre lies at signed distance `inradius` (positive) from every side. -/
lemma signedSideDist_incenter (i : Fin 3) : signedSideDist t i t.incenter = t.inradius := by
  rw [incenter_eq_affineCombination,
    signedSideDist_affineCombination t _ t.excenterExists_empty.sum_excenterWeights_eq_one,
    inradius_eq_abs_inv_sum, abs_of_pos (inv_pos.2 t.sum_excenterWeightsUnnorm_empty_pos),
    excenterWeights, Pi.smul_apply, smul_eq_mul, excenterWeightsUnnorm_empty_apply]
  have := t.height_pos i
  field_simp

/-- **Carnot's theorem.** The signed distances from the circumcentre to the three side lines of a
triangle sum to the circumradius plus the inradius. -/
theorem carnot :
    signedSideDist t 0 t.circumcenter + signedSideDist t 1 t.circumcenter +
        signedSideDist t 2 t.circumcenter = t.circumradius + t.inradius := by
  obtain ⟨w, k, hk0, hw, hO, hx0, hx1, hx2, hRk, h0, h1, h2⟩ := frame_data t
  have ha0 : 0 < dist (t.points 1) (t.points 2) :=
    dist_pos.2 (t.independent.injective.ne (by decide))
  have hb0 : 0 < dist (t.points 0) (t.points 2) :=
    dist_pos.2 (t.independent.injective.ne (by decide))
  have hc0 : 0 < dist (t.points 0) (t.points 1) :=
    dist_pos.2 (t.independent.injective.ne (by decide))
  have hr : t.inradius = k / (dist (t.points 1) (t.points 2) + dist (t.points 0) (t.points 2) +
      dist (t.points 0) (t.points 1)) := by
    rw [inradius_eq_abs_inv_sum, abs_of_pos (inv_pos.2 t.sum_excenterWeightsUnnorm_empty_pos),
      Fin.sum_univ_three, excenterWeightsUnnorm_empty_apply, excenterWeightsUnnorm_empty_apply,
      excenterWeightsUnnorm_empty_apply, h0, h1, h2]
    field_simp
  have hw0 : w 0 = 1 - w 1 - w 2 := by rw [Fin.sum_univ_three] at hw; linarith
  rw [hO, signedSideDist_affineCombination t w hw, signedSideDist_affineCombination t w hw,
    signedSideDist_affineCombination t w hw, h0, h1, h2, hr, hw0]
  exact carnot_alg _ _ _ _ _ _ _ ha0 hb0 hc0 t.circumradius_pos hx0 hx1 hx2 hRk

/-- Carnot's theorem, stated as a sum over the three sides. -/
theorem carnot_sum :
    ∑ i, signedSideDist t i t.circumcenter = t.circumradius + t.inradius := by
  rw [Fin.sum_univ_three]; exact carnot t

/-- Law of cosines in the form `cos A = (b² + c² - a²) / (2bc)`. -/
lemma cos_angle_eq (p₁ p₂ p₃ : P) (h₁ : p₁ ≠ p₂) (h₃ : p₃ ≠ p₂) :
    Real.cos (∠ p₁ p₂ p₃) =
      (dist p₂ p₁ ^ 2 + dist p₂ p₃ ^ 2 - dist p₁ p₃ ^ 2) / (2 * dist p₂ p₁ * dist p₂ p₃) := by
  have h := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle p₁ p₂ p₃
  have d₁ : 0 < dist p₂ p₁ := dist_pos.2 h₁.symm
  have d₃ : 0 < dist p₂ p₃ := dist_pos.2 h₃.symm
  rw [dist_comm p₁ p₂, dist_comm p₃ p₂] at h
  rw [eq_div_iff (by positivity)]
  linear_combination h

/-- The signed distances from the circumcentre to the sides are `R cos A`, `R cos B`, `R cos C`. -/
theorem signedSideDist_circumcenter_eq :
    signedSideDist t 0 t.circumcenter =
        t.circumradius * Real.cos (∠ (t.points 1) (t.points 0) (t.points 2)) ∧
      signedSideDist t 1 t.circumcenter =
        t.circumradius * Real.cos (∠ (t.points 0) (t.points 1) (t.points 2)) ∧
      signedSideDist t 2 t.circumcenter =
        t.circumradius * Real.cos (∠ (t.points 0) (t.points 2) (t.points 1)) := by
  obtain ⟨w, k, hk0, hw, hO, hx0, hx1, hx2, hRk, h0, h1, h2⟩ := frame_data t
  have ne : ∀ i j : Fin 3, i ≠ j → t.points i ≠ t.points j := fun i j h =>
    t.independent.injective.ne h
  have ha0 : 0 < dist (t.points 1) (t.points 2) := dist_pos.2 (ne 1 2 (by decide))
  have hb0 : 0 < dist (t.points 0) (t.points 2) := dist_pos.2 (ne 0 2 (by decide))
  have hc0 : 0 < dist (t.points 0) (t.points 1) := dist_pos.2 (ne 0 1 (by decide))
  have hR := t.circumradius_pos
  have hw0 : w 0 = 1 - w 1 - w 2 := by rw [Fin.sum_univ_three] at hw; linarith
  rw [hO, signedSideDist_affineCombination t w hw, signedSideDist_affineCombination t w hw,
    signedSideDist_affineCombination t w hw, h0, h1, h2,
    cos_angle_eq _ _ _ (ne 1 0 (by decide)) (ne 2 0 (by decide)),
    cos_angle_eq _ _ _ (ne 0 1 (by decide)) (ne 2 1 (by decide)),
    cos_angle_eq _ _ _ (ne 0 2 (by decide)) (ne 1 2 (by decide)),
    dist_comm (t.points 1) (t.points 0), dist_comm (t.points 2) (t.points 0),
    dist_comm (t.points 2) (t.points 1)]
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 0) (t.points 2)
  set c := dist (t.points 0) (t.points 1)
  refine ⟨?_, ?_, ?_⟩
  · have := weight_height_eq a b c (1 - w 1 - w 2) _ k (c ^ 2 + b ^ 2 - a ^ 2) ha0 hb0 hc0 hR
      (by linear_combination cos0_poly _ _ _ _ _ _ hx0 hx1 hx2) hRk
    rw [hw0]
    linear_combination this
  · have := weight_height_eq b c a (w 1) _ k (c ^ 2 + a ^ 2 - b ^ 2) hb0 hc0 ha0 hR
      (by linear_combination cos1_poly _ _ _ _ _ _ hx0 hx1 hx2) (by linear_combination hRk)
    linear_combination this
  · have := weight_height_eq c b a (w 2) _ k (b ^ 2 + a ^ 2 - c ^ 2) hc0 hb0 ha0 hR
      (by linear_combination cos2_poly _ _ _ _ _ _ hx0 hx1 hx2) (by linear_combination hRk)
    linear_combination this

/-- **Carnot's theorem, cosine form**: `cos A + cos B + cos C = 1 + r / R`. -/
theorem cos_add_cos_add_cos :
    Real.cos (∠ (t.points 1) (t.points 0) (t.points 2)) +
        Real.cos (∠ (t.points 0) (t.points 1) (t.points 2)) +
        Real.cos (∠ (t.points 0) (t.points 2) (t.points 1)) =
      1 + t.inradius / t.circumradius := by
  obtain ⟨e0, e1, e2⟩ := signedSideDist_circumcenter_eq t
  have h := carnot t
  rw [e0, e1, e2] at h
  have hR := t.circumradius_pos
  field_simp
  linear_combination h

end Carnot
