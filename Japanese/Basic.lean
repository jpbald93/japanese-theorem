import Japanese.Carnot.Main

/-!
# Japanese theorem: the triangle-level formula and the cyclic quadrilateral

We work in an oriented Euclidean plane: `V` has dimension 2 and `o : Orientation ℝ V (Fin 2)`
is an orientation, with area form `o.areaForm`.

* `chordDist o O p q` is the signed distance from `O` to the line through `p` and `q`. It is
  positive when `O` is to the left of the directed chord `p → q`.
* `chordDist_swap` is the cancellation lemma: reversing the chord flips the sign.
* `triInradius a b c` is the inradius of the triangle `abc`, or `0` if the points are collinear.
* `triInradius_eq` is Carnot's theorem in chord form: for a positively oriented triangle
  inscribed in the circle `s`, `r = d(ab) + d(bc) + d(ca) - R`.
* `japanese_quadrilateral` is the Japanese theorem for a convex cyclic quadrilateral.
-/

open EuclideanGeometry Affine Affine.Simplex Module
open scoped RealInnerProductSpace

namespace Japanese

open Carnot

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- Signed distance from `O` to the line `pq`. It is positive iff `O` lies to the left of the
directed chord `p → q`, with respect to the orientation `o`. -/
noncomputable def chordDist (O p q : P) : ℝ :=
  o.areaForm (q -ᵥ p) (O -ᵥ p) / dist p q

/-- **Cancellation lemma**: the signed distance to a chord changes sign when the chord is traversed
in the opposite direction. -/
theorem chordDist_swap (O p q : P) : chordDist o O q p = -chordDist o O p q := by
  unfold chordDist
  rw [dist_comm q p, ← neg_div]
  congr 1
  rw [← vsub_add_vsub_cancel O p q, ← neg_vsub_eq_vsub_rev q p]
  simp only [map_neg, map_add, LinearMap.neg_apply, o.areaForm_apply_self, neg_zero, add_zero]

open Classical in
/-- The inradius of the triangle with vertices `a`, `b`, `c`, or `0` if they are collinear. -/
noncomputable def triInradius (a b c : P) : ℝ :=
  if h : AffineIndependent ℝ ![a, b, c] then (⟨![a, b, c], h⟩ : Triangle ℝ P).inradius else 0

omit [Fact (finrank ℝ V = 2)] in
lemma affineIndependent_of_areaForm_ne_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2))
    {Q : Type*} [MetricSpace Q] [NormedAddTorsor E Q] {a b c : Q}
    (h : o.areaForm (b -ᵥ a) (c -ᵥ a) ≠ 0) : AffineIndependent ℝ ![a, b, c] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro hc
  rw [collinear_iff_of_mem (Set.mem_insert a _)] at hc
  obtain ⟨v, hv⟩ := hc
  obtain ⟨r₁, hr₁⟩ := hv b (by simp)
  obtain ⟨r₂, hr₂⟩ := hv c (by simp)
  apply h
  rw [hr₁, hr₂, vadd_vsub, vadd_vsub]
  simp [o.areaForm_apply_self]

lemma areaForm_cyc₁ (a b c : P) :
    o.areaForm (c -ᵥ b) (a -ᵥ b) = o.areaForm (b -ᵥ a) (c -ᵥ a) := by
  rw [← vsub_sub_vsub_cancel_right c b a, ← neg_vsub_eq_vsub_rev b a]
  simp only [map_sub, map_neg, LinearMap.sub_apply, o.areaForm_apply_self]
  rw [o.areaForm_swap (c -ᵥ a) (b -ᵥ a)]
  ring

lemma areaForm_cyc₂ (a b c : P) :
    o.areaForm (a -ᵥ c) (b -ᵥ c) = o.areaForm (b -ᵥ a) (c -ᵥ a) := by
  rw [areaForm_cyc₁ o c a b, areaForm_cyc₁ o b c a]

lemma areaForm_affineCombination_vsub (t : Triangle ℝ P) (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1)
    (e : V) (q : P) :
    o.areaForm e (Finset.univ.affineCombination ℝ t.points w -ᵥ q) =
      w 0 * o.areaForm e (t.points 0 -ᵥ q) + w 1 * o.areaForm e (t.points 1 -ᵥ q) +
        w 2 * o.areaForm e (t.points 2 -ᵥ q) := by
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ w _ hw q, vadd_vsub,
    Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
  simp only [map_add, map_smul, smul_eq_mul]

/-- Height times base equals the (positive) oriented double area. -/
lemma height_mul_dist (t : Triangle ℝ P) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hS : ({i}ᶜ : Set (Fin 3)) = {j, k})
    (hpos : 0 < o.areaForm (t.points k -ᵥ t.points j) (t.points i -ᵥ t.points j)) :
    t.height i * dist (t.points j) (t.points k) =
      o.areaForm (t.points k -ᵥ t.points j) (t.points i -ᵥ t.points j) := by
  have h := height_sq_mul_sq t hij hik hS
  have g := o.inner_sq_add_areaForm_sq (t.points k -ᵥ t.points j) (t.points i -ᵥ t.points j)
  rw [inner_vsub_vsub_eq_dist, ← dist_eq_norm_vsub V, ← dist_eq_norm_vsub V] at g
  rw [dist_comm (t.points k) (t.points j), dist_comm (t.points j) (t.points i),
    dist_comm (t.points k) (t.points i)] at g
  refine (pow_left_inj₀ (mul_nonneg (t.height_pos i).le dist_nonneg) hpos.le two_ne_zero).1 ?_
  rw [mul_pow, h]
  unfold heron
  linear_combination -g

/-- For a positively oriented triangle, Carnot's signed side distances are chord distances. -/
lemma signedSideDist_eq_chordDist (t : Triangle ℝ P)
    (hpos : 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0)) {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range t.points)) :
    signedSideDist t 0 p = chordDist o p (t.points 1) (t.points 2) ∧
      signedSideDist t 1 p = chordDist o p (t.points 2) (t.points 0) ∧
      signedSideDist t 2 p = chordDist o p (t.points 0) (t.points 1) := by
  have ne : ∀ i j : Fin 3, i ≠ j → t.points i ≠ t.points j := fun i j h =>
    t.independent.injective.ne h
  have d12 : 0 < dist (t.points 1) (t.points 2) := dist_pos.2 (ne 1 2 (by decide))
  have d20 : 0 < dist (t.points 2) (t.points 0) := dist_pos.2 (ne 2 0 (by decide))
  have d01 : 0 < dist (t.points 0) (t.points 1) := dist_pos.2 (ne 0 1 (by decide))
  have H0 := height_mul_dist o t (i := 0) (j := 1) (k := 2) (by decide) (by decide)
    (by ext l; fin_cases l <;> simp) (by rw [areaForm_cyc₁]; exact hpos)
  have H1 := height_mul_dist o t (i := 1) (j := 2) (k := 0) (by decide) (by decide)
    (by ext l; fin_cases l <;> simp) (by rw [areaForm_cyc₂]; exact hpos)
  have H2 := height_mul_dist o t (i := 2) (j := 0) (k := 1) (by decide) (by decide)
    (by ext l; fin_cases l <;> simp) hpos
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
  unfold chordDist
  rw [signedSideDist_affineCombination t w hw, signedSideDist_affineCombination t w hw,
    signedSideDist_affineCombination t w hw, areaForm_affineCombination_vsub o t w hw,
    areaForm_affineCombination_vsub o t w hw, areaForm_affineCombination_vsub o t w hw]
  simp only [vsub_self, map_zero, o.areaForm_apply_self, mul_zero, add_zero, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [← H0]; field_simp
  · rw [← H1]; field_simp
  · rw [← H2]; field_simp

/-- **Carnot's theorem, chord form.** For a positively oriented triangle `abc` inscribed in the
circle `s`, the inradius is `d(ab) + d(bc) + d(ca) - R`, where `d` is the signed distance from
the centre to the directed chord. -/
theorem triInradius_eq (s : Sphere P) {a b c : P} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hpos : 0 < o.areaForm (b -ᵥ a) (c -ᵥ a)) :
    triInradius a b c =
      chordDist o s.center a b + chordDist o s.center b c + chordDist o s.center c a -
        s.radius := by
  have hind := affineIndependent_of_areaForm_ne_zero o hpos.ne'
  set t : Triangle ℝ P := ⟨![a, b, c], hind⟩ with ht
  have : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  have htop : affineSpan ℝ (Set.range t.points) = ⊤ := by
    rw [t.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one,
      (Fact.out : finrank ℝ V = 2), Fintype.card_fin]
  have hmem : s.center ∈ affineSpan ℝ (Set.range t.points) := by
    rw [htop]; exact AffineSubspace.mem_top _ _ _
  have hdist : ∀ i, dist (t.points i) s.center = s.radius := by
    intro i
    fin_cases i
    · exact mem_sphere.1 ha
    · exact mem_sphere.1 hb
    · exact mem_sphere.1 hc
  have hO : s.center = t.circumcenter := t.eq_circumcenter_of_dist_eq hmem hdist
  have hR : s.radius = t.circumradius := t.eq_circumradius_of_dist_eq hmem hdist
  have hC := carnot t
  obtain ⟨h0, h1, h2⟩ := signedSideDist_eq_chordDist o t hpos hmem
  rw [← hO, ← hR, h0, h1, h2] at hC
  rw [triInradius, dif_pos hind]
  change chordDist o s.center b c + chordDist o s.center c a + chordDist o s.center a b =
    s.radius + t.inradius at hC
  linarith

lemma mem_affineSpan_triangle (t : Triangle ℝ P) (p : P) :
    p ∈ affineSpan ℝ (Set.range t.points) := by
  have : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  have htop : affineSpan ℝ (Set.range t.points) = ⊤ := by
    rw [t.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one,
      (Fact.out : finrank ℝ V = 2), Fintype.card_fin]
  rw [htop]; exact AffineSubspace.mem_top _ _ _

/-- **Cancellation along a diagonal**, in terms of Carnot's signed side distances. The triangles
`ABC` and `ACD` (both positively oriented) share the diagonal `AC`. It is the side opposite
vertex `1` in `ABC` and the side opposite vertex `2` in `ACD`. For any point `O` of the plane,
the two signed distances from `O` to this common side are opposite. -/
theorem diagonal_signedSideDist_cancel {A B C D : P} (O : P)
    (hABC : 0 < o.areaForm (B -ᵥ A) (C -ᵥ A)) (hACD : 0 < o.areaForm (C -ᵥ A) (D -ᵥ A)) :
    signedSideDist
        (⟨![A, B, C], affineIndependent_of_areaForm_ne_zero o hABC.ne'⟩ : Triangle ℝ P) 1 O +
      signedSideDist
        (⟨![A, C, D], affineIndependent_of_areaForm_ne_zero o hACD.ne'⟩ : Triangle ℝ P) 2 O =
      0 := by
  obtain ⟨-, h1, -⟩ := signedSideDist_eq_chordDist o
    ⟨![A, B, C], affineIndependent_of_areaForm_ne_zero o hABC.ne'⟩ hABC
    (mem_affineSpan_triangle _ O)
  obtain ⟨-, -, h2⟩ := signedSideDist_eq_chordDist o
    ⟨![A, C, D], affineIndependent_of_areaForm_ne_zero o hACD.ne'⟩ hACD
    (mem_affineSpan_triangle _ O)
  rw [h1, h2]
  change chordDist o O C A + chordDist o O A C = 0
  rw [chordDist_swap o O C A]
  ring

/-- **Japanese theorem for cyclic quadrilaterals.** Let `A B C D` lie on a circle in convex
position, in counterclockwise order: every triangle formed by three of them, listed in the
cyclic order, is positively oriented. Then the two triangulations `ABC + ACD` and `ABD + BCD`
have the same sum of inradii. -/
theorem japanese_quadrilateral (s : Sphere P) {A B C D : P} (hA : A ∈ s) (hB : B ∈ s)
    (hC : C ∈ s) (hD : D ∈ s)
    (hABC : 0 < o.areaForm (B -ᵥ A) (C -ᵥ A)) (hACD : 0 < o.areaForm (C -ᵥ A) (D -ᵥ A))
    (hABD : 0 < o.areaForm (B -ᵥ A) (D -ᵥ A)) (hBCD : 0 < o.areaForm (C -ᵥ B) (D -ᵥ B)) :
    triInradius A B C + triInradius A C D = triInradius A B D + triInradius B C D := by
  rw [triInradius_eq o s hA hB hC hABC, triInradius_eq o s hA hC hD hACD,
    triInradius_eq o s hA hB hD hABD, triInradius_eq o s hB hC hD hBCD,
    chordDist_swap o s.center A C, chordDist_swap o s.center B D]
  ring

/-- Both sides of the Japanese theorem for quadrilaterals equal the chord sum minus `2R`. -/
theorem quadrilateral_inradius_sum (s : Sphere P) {A B C D : P} (hA : A ∈ s) (hB : B ∈ s)
    (hC : C ∈ s) (hD : D ∈ s)
    (hABC : 0 < o.areaForm (B -ᵥ A) (C -ᵥ A)) (hACD : 0 < o.areaForm (C -ᵥ A) (D -ᵥ A)) :
    triInradius A B C + triInradius A C D =
      chordDist o s.center A B + chordDist o s.center B C + chordDist o s.center C D +
        chordDist o s.center D A - 2 * s.radius := by
  rw [triInradius_eq o s hA hB hC hABC, triInradius_eq o s hA hC hD hACD,
    chordDist_swap o s.center A C]
  ring

end Japanese
