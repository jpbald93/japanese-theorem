import Japanese.Basic
import Japanese.Polygon
import Japanese.Combinatorial
import Japanese.Geometric

/-!
# Layer 15: classical statements

Layer 15. These definitions and statements were written independently, from textbook statements, by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves (or proves part of) one of them from this development.
-/

open EuclideanGeometry

noncomputable section

open scoped Classical

namespace Japanese.Classical

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-! ## Writer definitions and statements, verbatim (packaged as `Prop`s). -/

def triInradius (a b c : P) : ℝ :=
  if h : AffineIndependent ℝ ![a, b, c] then
    (⟨![a, b, c], h⟩ : Affine.Triangle ℝ P).inradius else 0

def triIncenter (a b c : P) : P :=
  if h : AffineIndependent ℝ ![a, b, c] then
    (⟨![a, b, c], h⟩ : Affine.Triangle ℝ P).incenter else a

def IsRectangle (p₁ p₂ p₃ p₄ : P) : Prop :=
  midpoint ℝ p₁ p₃ = midpoint ℝ p₂ p₄ ∧ dist p₁ p₃ = dist p₂ p₄ ∧
    p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₃ ≠ p₄ ∧ p₄ ≠ p₁

def IsConvexPolygon {n : ℕ} [NeZero n] (v : Fin n → V) : Prop :=
  3 ≤ n ∧ Function.Injective v ∧
    ∀ i j k : Fin n, j ≠ i → j ≠ i + 1 → k ≠ i → k ≠ i + 1 →
      (line[ℝ, v i, v (i + 1)] : AffineSubspace ℝ V).SSameSide (v j) (v k)

def IsTriangulation {n : ℕ} (v : Fin n → V) (T : Finset (Fin n × Fin n × Fin n)) : Prop :=
  (∀ t ∈ T, t.1 < t.2.1 ∧ t.2.1 < t.2.2) ∧
  (⋃ t ∈ T, convexHull ℝ {v t.1, v t.2.1, v t.2.2}) = convexHull ℝ (Set.range v) ∧
  ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' →
    Disjoint (interior (convexHull ℝ {v t.1, v t.2.1, v t.2.2}))
      (interior (convexHull ℝ {v t'.1, v t'.2.1, v t'.2.2}))

def IsConvexQuad (A B C D : P) : Prop :=
  ∃ X : P, Sbtw ℝ A X C ∧ Sbtw ℝ B X D

def classical_TriSimplex4_a [Fact (Module.finrank ℝ V = 2)] : Prop := ∀ {n : ℕ} [NeZero n]
    (v : Fin n → V) (hconv : IsConvexPolygon v) (Γ : Sphere V) (hcyc : ∀ i, v i ∈ Γ)
    (T₁ T₂ : Finset (Fin n × Fin n × Fin n))
    (h₁ : IsTriangulation v T₁) (h₂ : IsTriangulation v T₂),
    ∑ t ∈ T₁, triInradius (v t.1) (v t.2.1) (v t.2.2) =
      ∑ t ∈ T₂, triInradius (v t.1) (v t.2.1) (v t.2.2)

def classical_TriSimplex4_a_obligation [Fact (Module.finrank ℝ V = 2)] : Prop :=
  ∀ {n : ℕ} [NeZero n]
    (v : Fin n → V) (hconv : IsConvexPolygon v) (T : Finset (Fin n × Fin n × Fin n))
    (hT : IsTriangulation v T),
    ∀ t ∈ T, AffineIndependent ℝ ![v t.1, v t.2.1, v t.2.2]

def classical_TriSimplex4_b : Prop := ∀ (A B C D : P) (hconv : IsConvexQuad A B C D)
    (hcyc : Cospherical ({A, B, C, D} : Set P)),
    triInradius A B C + triInradius A C D = triInradius A B D + triInradius B C D

def classical_TriSimplex4_b_rectangle : Prop := ∀ (A B C D : P) (hconv : IsConvexQuad A B C D)
    (hcyc : Cospherical ({A, B, C, D} : Set P)),
    IsRectangle (triIncenter A B C) (triIncenter B C D) (triIncenter C D A)
      (triIncenter D A B)

def classical_TriSimplex4_b_obligation : Prop := ∀ (A B C D : P) (hconv : IsConvexQuad A B C D)
    (hcyc : Cospherical ({A, B, C, D} : Set P)),
    AffineIndependent ℝ ![A, B, C] ∧ AffineIndependent ℝ ![A, C, D] ∧
      AffineIndependent ℝ ![A, B, D] ∧ AffineIndependent ℝ ![B, C, D]

/-! ## Bridges -/

lemma triInradius_eq_repo [Fact (Module.finrank ℝ V = 2)] (a b c : P) :
    triInradius a b c = Japanese.triInradius (V := V) a b c := rfl

lemma triInradius_eq_zero_left (a c : P) : triInradius a a c = 0 := by
  rw [triInradius, dif_neg]
  intro h
  exact absurd (h.injective (a₁ := 0) (a₂ := 1) rfl) (by decide)

lemma triInradius_eq_zero_right (a b : P) : triInradius a b b = 0 := by
  rw [triInradius, dif_neg]
  intro h
  exact absurd (h.injective (a₁ := 1) (a₂ := 2) rfl) (by decide)

/-- An affinely independent triple has nonzero area form (any orientation of a plane). -/
lemma areaForm_ne_zero_of_affineIndependent [Fact (Module.finrank ℝ V = 2)]
    (o : Orientation ℝ V (Fin 2)) {a b c : P} (h : AffineIndependent ℝ ![a, b, c]) :
    o.areaForm (b -ᵥ a) (c -ᵥ a) ≠ 0 := by
  intro h0
  have hs := o.inner_sq_add_areaForm_sq (b -ᵥ a) (c -ᵥ a)
  rw [h0] at hs
  have hx : b -ᵥ a ≠ 0 := vsub_ne_zero.2 (h.injective.ne (show (1 : Fin 3) ≠ 0 by decide))
  have hy : c -ᵥ a ≠ 0 := vsub_ne_zero.2 (h.injective.ne (show (2 : Fin 3) ≠ 0 by decide))
  have habs : ‖inner ℝ (b -ᵥ a) (c -ᵥ a)‖ = ‖b -ᵥ a‖ * ‖c -ᵥ a‖ := by
    rw [Real.norm_eq_abs]
    refine (sq_eq_sq₀ (abs_nonneg _) (by positivity)).1 ?_
    rw [sq_abs, mul_pow]; linarith
  obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff (𝕜 := ℝ) hx hy).1 habs
  have hc : c ∈ line[ℝ, a, b] :=
    (mem_affineSpan_pair_iff_exists_lineMap_eq).2 ⟨r, by rw [AffineMap.lineMap_apply, ← hr, vsub_vadd]⟩
  have hcol : Collinear ℝ ({a, b, c} : Set P) := by
    refine (collinear_insert_of_mem_affineSpan_pair hc).subset ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  exact (affineIndependent_iff_not_collinear_set.1 h) hcol

/-- Orientation signs of a convex quadrilateral, from the crossing diagonals. -/
lemma quad_signs [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2)) {A B C D X : P}
    (h1 : Sbtw ℝ A X C) (h2 : Sbtw ℝ B X D) (hpos : 0 < o.areaForm (B -ᵥ A) (C -ᵥ A)) :
    0 < o.areaForm (C -ᵥ A) (D -ᵥ A) ∧ 0 < o.areaForm (B -ᵥ A) (D -ᵥ A) ∧
      0 < o.areaForm (C -ᵥ B) (D -ᵥ B) := by
  obtain ⟨⟨s, ⟨hs0, hs1⟩, hsX⟩, -⟩ := sbtw_iff_mem_image_Ioo_and_ne.1 h1
  obtain ⟨⟨t, ⟨ht0, ht1⟩, htX⟩, -⟩ := sbtw_iff_mem_image_Ioo_and_ne.1 h2
  set u := B -ᵥ A
  set v := C -ᵥ A
  set w := D -ᵥ A
  have eX1 : X -ᵥ A = s • v := by rw [← hsX, AffineMap.lineMap_vsub_left]
  have eX2 : X -ᵥ B = t • (w - u) := by
    rw [← htX, AffineMap.lineMap_vsub_left, vsub_sub_vsub_cancel_right]
  have e : s • v = t • (w - u) + u := by rw [← eX1, ← eX2, vsub_add_vsub_cancel]
  have eCB : C -ᵥ B = v - u := (vsub_sub_vsub_cancel_right C B A).symm
  have eDB : D -ᵥ B = w - u := (vsub_sub_vsub_cancel_right D B A).symm
  rw [eCB, eDB]
  have k1 := congrArg (fun z => o.areaForm u z) e
  have k2 := congrArg (fun z => o.areaForm v z) e
  simp only [map_add, map_sub, map_smul, smul_eq_mul, o.areaForm_apply_self] at k1 k2
  have sw : o.areaForm v u = -o.areaForm u v := o.areaForm_swap v u
  simp only [map_sub, LinearMap.sub_apply, o.areaForm_apply_self, sub_zero]
  rw [sw] at k2 ⊢
  set k := o.areaForm u v
  have p1 : 0 < t * o.areaForm u w := by nlinarith
  have p2 : 0 < t * o.areaForm v w := by nlinarith
  have p3 : 0 < t * (o.areaForm v w - o.areaForm u w - -k) := by nlinarith
  exact ⟨pos_of_mul_pos_right p2 ht0.le, pos_of_mul_pos_right p1 ht0.le,
    pos_of_mul_pos_right p3 ht0.le⟩

/-- NARROWER part of 4b: the writer's statement verbatim, in a Euclidean plane
(`finrank V = 2`). NEW PROOF of the reduction (orientation choice, convexity → the four
orientation signs, degenerate cases) to `Japanese.japanese_quadrilateral`. -/
theorem cov_TriSimplex4_b_part [Fact (Module.finrank ℝ V = 2)] :
    classical_TriSimplex4_b (V := V) (P := P) := by
  intro A B C D ⟨X, h1, h2⟩ ⟨c, ρ, hcr⟩
  set s : Sphere P := ⟨c, ρ⟩
  have mem : ∀ p ∈ ({A, B, C, D} : Set P), p ∈ s := fun p hp => hcr p hp
  have hA : A ∈ s := mem A (by simp)
  have hB : B ∈ s := mem B (by simp)
  have hC : C ∈ s := mem C (by simp)
  have hD : D ∈ s := mem D (by simp)
  have hAC : A ≠ C := h1.left_ne_right
  by_cases hAB : A = B
  · subst hAB; rw [triInradius_eq_zero_left, triInradius_eq_zero_left]
  by_cases hBC : B = C
  · subst hBC; rw [triInradius_eq_zero_right, triInradius_eq_zero_left]; ring
  have hind : AffineIndependent ℝ ![A, B, C] :=
    Cospherical.affineIndependent_of_ne ⟨c, ρ, fun p hp => hcr p (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢; tauto)⟩ hAB hAC hBC
  have : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  let o₀ : Orientation ℝ V (Fin 2) :=
    (Module.finBasisOfFinrankEq ℝ V (Fact.out : Module.finrank ℝ V = 2)).orientation
  obtain ⟨o, hpos⟩ : ∃ o : Orientation ℝ V (Fin 2), 0 < o.areaForm (B -ᵥ A) (C -ᵥ A) := by
    rcases lt_or_gt_of_ne (areaForm_ne_zero_of_affineIndependent o₀ hind) with h | h
    · exact ⟨-o₀, by rw [o₀.areaForm_neg_orientation]; simpa using h⟩
    · exact ⟨o₀, h⟩
  obtain ⟨q1, q2, q3⟩ := quad_signs o h1 h2 hpos
  simp only [triInradius_eq_repo]
  exact Japanese.japanese_quadrilateral o s hA hB hC hD hpos q1 q2 q3

-- The writer's statement `classical_TriSimplex4_b_obligation` is false as written.
/-- 4b obligation is FALSE as written: the writer's `IsConvexQuad` admits the degenerate
"quadrilateral" `A = B = 0`, `C = D = 1` on the real line. -/
theorem not_classical_TriSimplex4_b_obligation :
    ¬ classical_TriSimplex4_b_obligation (V := ℝ) (P := ℝ) := by
  intro h
  have hq : IsConvexQuad (0 : ℝ) 0 1 1 :=
    ⟨1 / 2, sbtw_zero_one_iff.2 ⟨by norm_num, by norm_num⟩,
      sbtw_zero_one_iff.2 ⟨by norm_num, by norm_num⟩⟩
  have hc : Cospherical ({(0 : ℝ), 0, 1, 1} : Set ℝ) := ⟨1 / 2, 1 / 2, by
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num [Real.dist_eq, abs_of_pos]⟩
  have := (h 0 0 1 1 hq hc).1
  exact absurd (this.injective (a₁ := 0) (a₂ := 1) rfl) (by decide)

-- The writer's statement `classical_TriSimplex4_b_rectangle` is false as written.
/-- 4b companion (rectangle) is FALSE as written, same degenerate configuration. -/
theorem not_classical_TriSimplex4_b_rectangle :
    ¬ classical_TriSimplex4_b_rectangle (V := ℝ) (P := ℝ) := by
  intro h
  have hq : IsConvexQuad (0 : ℝ) 0 1 1 :=
    ⟨1 / 2, sbtw_zero_one_iff.2 ⟨by norm_num, by norm_num⟩,
      sbtw_zero_one_iff.2 ⟨by norm_num, by norm_num⟩⟩
  have hc : Cospherical ({(0 : ℝ), 0, 1, 1} : Set ℝ) := ⟨1 / 2, 1 / 2, by
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num [Real.dist_eq, abs_of_pos]⟩
  obtain ⟨-, -, h12, -⟩ := h 0 0 1 1 hq hc
  apply h12
  have d1 : ¬ AffineIndependent ℝ ![(0 : ℝ), 0, 1] := fun hi =>
    absurd (hi.injective (a₁ := 0) (a₂ := 1) rfl) (by decide)
  have d2 : ¬ AffineIndependent ℝ ![(0 : ℝ), 1, 1] := fun hi =>
    absurd (hi.injective (a₁ := 1) (a₂ := 2) rfl) (by decide)
  rw [triIncenter, triIncenter, dif_neg d1, dif_neg d2]

/-- 4b obligation, corrected: with the four vertices distinct (a genuine quadrilateral), the four
triangles are non-degenerate (NEW PROOF, any dimension). -/
theorem cov_TriSimplex4_b_obligation_part (A B C D : P)
    (hcyc : Cospherical ({A, B, C, D} : Set P)) (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    AffineIndependent ℝ ![A, B, C] ∧ AffineIndependent ℝ ![A, C, D] ∧
      AffineIndependent ℝ ![A, B, D] ∧ AffineIndependent ℝ ![B, C, D] := by
  have sub : ∀ {x y z : P}, x ∈ ({A, B, C, D} : Set P) → y ∈ ({A, B, C, D} : Set P) →
      z ∈ ({A, B, C, D} : Set P) → Cospherical ({x, y, z} : Set P) := by
    intro x y z hx hy hz
    refine hcyc.subset ?_
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;> assumption
  refine ⟨(sub (by simp) (by simp) (by simp)).affineIndependent_of_ne hAB hAC hBC,
    (sub (by simp) (by simp) (by simp)).affineIndependent_of_ne hAC hAD hCD,
    (sub (by simp) (by simp) (by simp)).affineIndependent_of_ne hAB hAD hBD,
    (sub (by simp) (by simp) (by simp)).affineIndependent_of_ne hBC hBD hCD⟩

/-! ### 4a -/

/-- In a strictly convex polygon (writer's definition) no vertex lies weakly between two others. -/
lemma not_wbtw_of_isConvexPolygon {n : ℕ} [NeZero n] {v : Fin n → V} (hconv : IsConvexPolygon v)
    {x y z : Fin n} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (h : Wbtw ℝ (v x) (v y) (v z)) :
    False := by
  obtain ⟨-, hinj, hside⟩ := hconv
  have hcol := h.collinear
  have hvy : ∀ {w : Fin n}, w ≠ y → v y ≠ v w := fun hw => hinj.ne (Ne.symm hw)
  by_cases hx : x = y + 1
  · have hz : v z ∈ line[ℝ, v y, v (y + 1)] := by
      rw [← hx]
      exact hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) (hvy hxy)
    have := hside y z z hyz.symm (by rw [← hx]; exact Ne.symm hxz) hyz.symm
      (by rw [← hx]; exact Ne.symm hxz)
    exact this.left_notMem hz
  by_cases hz : z = y + 1
  · have hx' : v x ∈ line[ℝ, v y, v (y + 1)] := by
      rw [← hz]
      exact hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) (hvy hyz.symm)
    have := hside y x x hxy (by rw [← hz]; exact hxz) hxy (by rw [← hz]; exact hxz)
    exact this.left_notMem hx'
  have hs := hside y x z hxy hx hyz.symm hz
  exact hs.not_wOppSide (h.wOppSide₁₃ (left_mem_affineSpan_pair ℝ _ _))

/-- 4a obligation: COVERED by a NEW PROOF (any ambient dimension; the triangulation hypothesis is
only used for `i < j < k`). -/
theorem cov_TriSimplex4_a_obligation [Fact (Module.finrank ℝ V = 2)] :
    classical_TriSimplex4_a_obligation (V := V) := by
  intro n _ v hconv T hT t ht
  obtain ⟨h1, h2⟩ := hT.1 t ht
  have hab : t.1 ≠ t.2.1 := h1.ne
  have hbc : t.2.1 ≠ t.2.2 := h2.ne
  have hac : t.1 ≠ t.2.2 := (h1.trans h2).ne
  rw [affineIndependent_iff_not_collinear_set]
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
  · exact not_wbtw_of_isConvexPolygon hconv hab hbc hac h
  · exact not_wbtw_of_isConvexPolygon hconv hbc hac.symm hab.symm h
  · exact not_wbtw_of_isConvexPolygon hconv hac.symm hab hbc.symm h

/-- 4a, strongest part available: the repository's geometric Japanese theorem, stated with the
writer's `triInradius`, for an `ℕ`-indexed polygon in orientation-convex position and
triangulations given as maximal sets of pairwise non-crossing chords. -/
theorem cov_TriSimplex4_a_part [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (s : Sphere V) (p : ℕ → V) (n : ℕ) (hn : 2 ≤ n) (hs : ∀ l < n, p l ∈ s)
    (hconv : ∀ a b c, a < b → b < c → c < n → 0 < o.areaForm (p b -ᵥ p a) (p c -ᵥ p a))
    {E E' : Finset (ℕ × ℕ)} (hE : Japanese.IsGeomTriangulation p 0 (n - 1) E)
    (hE' : Japanese.IsGeomTriangulation p 0 (n - 1) E') :
    ∑ t ∈ Japanese.triangleSet E, triInradius (p t.1) (p t.2.1) (p t.2.2) =
      ∑ t ∈ Japanese.triangleSet E', triInradius (p t.1) (p t.2.1) (p t.2.2) :=
  Japanese.japanese_polygon_geometric o p n s hn hs hconv hE hE'

/-! ### 4b in arbitrary dimension (NEW PROOF): restrict to the plane of `A B C`. -/

lemma triInradius_subtype (S : AffineSubspace ℝ P) [Nonempty S] (a b c : S) :
    triInradius a b c = triInradius (a : P) b c := by
  have e : (![(a : P), b, c] : Fin 3 → P) = S.subtype ∘ ![a, b, c] := by
    funext i; fin_cases i <;> rfl
  by_cases h : AffineIndependent ℝ ![a, b, c]
  · have h' : AffineIndependent ℝ ![(a : P), b, c] := by
      rw [e]; exact h.map' S.subtype Subtype.val_injective
    rw [triInradius, triInradius, dif_pos h, dif_pos h']
    have hm := (⟨![a, b, c], h⟩ : Affine.Triangle ℝ S).inradius_map S.subtypeₐᵢ
    rw [← hm]
    congr 1
    ext i; fin_cases i <;> rfl
  · have h' : ¬ AffineIndependent ℝ ![(a : P), b, c] := by
      rw [e]; exact fun hh => h (AffineIndependent.of_comp S.subtype hh)
    rw [triInradius, triInradius, dif_neg h, dif_neg h']

theorem cov_TriSimplex4_b : classical_TriSimplex4_b (V := V) (P := P) := by
  intro A B C D ⟨X, h1, h2⟩ hcyc
  have hAC : A ≠ C := h1.left_ne_right
  obtain ⟨c, ρ, hcr⟩ := hcyc
  by_cases hAB : A = B
  · subst hAB; rw [triInradius_eq_zero_left, triInradius_eq_zero_left]
  by_cases hBC : B = C
  · subst hBC; rw [triInradius_eq_zero_right, triInradius_eq_zero_left]; ring
  have hind : AffineIndependent ℝ ![A, B, C] :=
    Cospherical.affineIndependent_of_ne ⟨c, ρ, fun p hp => hcr p (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢; tauto)⟩ hAB hAC hBC
  set S : AffineSubspace ℝ P := affineSpan ℝ (Set.range ![A, B, C]) with hS
  have mA : A ∈ S := mem_affineSpan ℝ ⟨0, rfl⟩
  have mB : B ∈ S := mem_affineSpan ℝ ⟨1, rfl⟩
  have mC : C ∈ S := mem_affineSpan ℝ ⟨2, rfl⟩
  have mX : X ∈ S := affineSpan_pair_le_of_mem_of_mem mA mC h1.wbtw.mem_affineSpan
  have mD : D ∈ S := by
    have hcol := h2.wbtw.collinear
    have : D ∈ line[ℝ, B, X] :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) h2.left_ne
    exact affineSpan_pair_le_of_mem_of_mem mB mX this
  have : Nonempty S := ⟨⟨A, mA⟩⟩
  have : Fact (Module.finrank ℝ S.direction = 2) := ⟨by
    rw [hS, direction_affineSpan]; exact hind.finrank_vectorSpan (by simp)⟩
  let A' : S := ⟨A, mA⟩
  let B' : S := ⟨B, mB⟩
  let C' : S := ⟨C, mC⟩
  let D' : S := ⟨D, mD⟩
  let X' : S := ⟨X, mX⟩
  have hq : IsConvexQuad A' B' C' D' := by
    refine ⟨X', ?_, ?_⟩
    · rw [← (Subtype.val_injective : Function.Injective S.subtype).sbtw_map_iff (f := S.subtype)]
      exact h1
    · rw [← (Subtype.val_injective : Function.Injective S.subtype).sbtw_map_iff (f := S.subtype)]
      exact h2
  -- the sphere centre projected to the plane
  set p : P := (EuclideanGeometry.orthogonalProjection S c : P)
  have hp : p ∈ S := (EuclideanGeometry.orthogonalProjection S c).property
  have key : ∀ y ∈ ({A, B, C, D} : Set P), y ∈ S → dist y p ^ 2 = ρ ^ 2 - dist c p ^ 2 := by
    intro y hy hyS
    have := EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
      c hyS
    rw [hcr y hy] at this
    change ρ * ρ = dist y p * dist y p + dist c p * dist c p at this
    nlinarith
  have hc' : Cospherical ({A', B', C', D'} : Set S) := by
    refine ⟨⟨p, hp⟩, dist A p, ?_⟩
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    have hA2 := key A (by simp) mA
    have f : ∀ z : P, z ∈ ({A, B, C, D} : Set P) → z ∈ S → dist z p = dist A p := fun z hz hzS =>
      (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 ((key z hz hzS).trans hA2.symm)
    rcases hy with rfl | rfl | rfl | rfl
    · exact f A (by simp) mA
    · exact f B (by simp) mB
    · exact f C (by simp) mC
    · exact f D (by simp) mD
  have := cov_TriSimplex4_b_part (V := S.direction) (P := S) A' B' C' D' hq hc'
  simpa only [triInradius_subtype] using this

end Japanese.Classical
