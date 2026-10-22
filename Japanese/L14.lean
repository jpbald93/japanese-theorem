import Japanese.Geometric

/-!
# Layer 14: Mathlib-only restatements and witnesses for the Japanese theorem

The statements `l14_*` mention only Mathlib notions:
* the inradius of a triangle `abc` is Mathlib's `Affine.Simplex.inradius` of
  `⟨![a, b, c], h⟩ : Affine.Triangle ℝ P`, for any proof `h` of affine independence
  (in the polygon statement: that inradius when `![a, b, c]` is affinely independent, else `0`);
* the signed distance from `O` to the directed chord `p → q` is written out as
  `o.areaForm (q -ᵥ p) (O -ᵥ p) / dist p q`;
* a geometric triangulation of the polygon `p 0, …, p (n-1)` is written out: a finite set of chords
  `(a, b)` with `0 ≤ a < b ≤ n - 1`, no two distinct chords whose open segments share a point
  (`Sbtw`), maximal with this property; its triangles are the triples all three of whose sides lie
  in the set.

Witness: the rational cyclic quadrilateral `1, (3 + 4i)/5, -1, -i` on the unit circle of `ℂ`
(counterclockwise), with the two triangulations by the diagonals `(0, 2)` and `(1, 3)`.
-/

namespace Japanese

open EuclideanGeometry Affine Module Complex ComplexConjugate

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-! ### Bridges -/

omit [Fact (finrank ℝ V = 2)] in
theorem l14b_triInradius_eq {a b c : P} (h : AffineIndependent ℝ ![a, b, c]) :
    triInradius a b c = (⟨![a, b, c], h⟩ : Triangle ℝ P).inradius := by
  rw [triInradius, dif_pos h]

/-! ### Mathlib-only statements -/

/-- **Carnot, chord form (Mathlib-only).** -/
theorem l14_triInradius_eq (s : Sphere P) {a b c : P} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hpos : 0 < o.areaForm (b -ᵥ a) (c -ᵥ a)) (h : AffineIndependent ℝ ![a, b, c]) :
    (⟨![a, b, c], h⟩ : Triangle ℝ P).inradius =
      o.areaForm (b -ᵥ a) (s.center -ᵥ a) / dist a b +
        o.areaForm (c -ᵥ b) (s.center -ᵥ b) / dist b c +
        o.areaForm (a -ᵥ c) (s.center -ᵥ c) / dist c a - s.radius := by
  rw [← l14b_triInradius_eq h]
  exact triInradius_eq o s ha hb hc hpos

/-- **Japanese theorem for cyclic quadrilaterals (Mathlib-only).** -/
theorem l14_japanese_quadrilateral (s : Sphere P) {A B C D : P} (hA : A ∈ s) (hB : B ∈ s)
    (hC : C ∈ s) (hD : D ∈ s)
    (hABC : 0 < o.areaForm (B -ᵥ A) (C -ᵥ A)) (hACD : 0 < o.areaForm (C -ᵥ A) (D -ᵥ A))
    (hABD : 0 < o.areaForm (B -ᵥ A) (D -ᵥ A)) (hBCD : 0 < o.areaForm (C -ᵥ B) (D -ᵥ B))
    (i₁ : AffineIndependent ℝ ![A, B, C]) (i₂ : AffineIndependent ℝ ![A, C, D])
    (i₃ : AffineIndependent ℝ ![A, B, D]) (i₄ : AffineIndependent ℝ ![B, C, D]) :
    (⟨_, i₁⟩ : Triangle ℝ P).inradius + (⟨_, i₂⟩ : Triangle ℝ P).inradius =
      (⟨_, i₃⟩ : Triangle ℝ P).inradius + (⟨_, i₄⟩ : Triangle ℝ P).inradius := by
  rw [← l14b_triInradius_eq, ← l14b_triInradius_eq, ← l14b_triInradius_eq, ← l14b_triInradius_eq]
  exact japanese_quadrilateral o s hA hB hC hD hABC hACD hABD hBCD

omit [Fact (finrank ℝ V = 2)] in
/-- A Mathlib-only description of a geometric triangulation of the polygon `p 0, …, p (n - 1)`. -/
theorem l14b_isGeomTriangulation_iff (p : ℕ → P) (n : ℕ) (E : Finset (ℕ × ℕ)) :
    IsGeomTriangulation p 0 (n - 1) E ↔
      (∀ e ∈ E, e.1 < e.2 ∧ e.2 ≤ n - 1) ∧
      (∀ e ∈ E, ∀ f ∈ E, e ≠ f → ¬ ∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧ Sbtw ℝ (p f.1) q (p f.2)) ∧
      (∀ e : ℕ × ℕ, e.1 < e.2 → e.2 ≤ n - 1 →
        (∀ f ∈ E, e ≠ f → ¬ ∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧ Sbtw ℝ (p f.1) q (p f.2)) → e ∈ E) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun e he => ⟨(h1 e he).2.1, (h1 e he).2.2⟩, h2,
      fun e he1 he2 h => h3 e ⟨Nat.zero_le _, he1, he2⟩ h⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun e he => ⟨Nat.zero_le _, (h1 e he).1, (h1 e he).2⟩, h2,
      fun e he h => h3 e he.2.1 he.2.2 h⟩

omit [Fact (finrank ℝ V = 2)] in
open Classical in
theorem l14b_triangleInradiusSum_eq (p : ℕ → P) (n : ℕ) (hn : 2 ≤ n) {E : Finset (ℕ × ℕ)}
    (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 ≤ n - 1) :
    triangleInradiusSum p (triangleSet E) =
      ∑ t ∈ Finset.range n ×ˢ Finset.range n ×ˢ Finset.range n with
          (t.1, t.2.1) ∈ E ∧ (t.2.1, t.2.2) ∈ E ∧ (t.1, t.2.2) ∈ E,
        (if h : AffineIndependent ℝ ![p t.1, p t.2.1, p t.2.2] then
          (⟨_, h⟩ : Triangle ℝ P).inradius else 0) := by
  unfold triangleInradiusSum
  congr 1
  ext ⟨a, b, c⟩
  simp only [mem_triangleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have := hE _ h1; have := hE _ h2
    exact ⟨⟨by simp at *; omega, by simp at *; omega, by simp at *; omega⟩, h1, h2, h3⟩
  · exact fun h => h.2

open Classical in
/-- **Japanese theorem for convex cyclic polygons (Mathlib-only).** For two geometric
triangulations `E`, `E'` of a strictly convex counterclockwise polygon inscribed in a circle, the
sums of the inradii of the triangles agree. -/
theorem l14_japanese_polygon (s : Sphere P) (p : ℕ → P) (n : ℕ) (hn : 2 ≤ n)
    (hs : ∀ l < n, p l ∈ s)
    (hconv : ∀ a b c, a < b → b < c → c < n → 0 < o.areaForm (p b -ᵥ p a) (p c -ᵥ p a))
    {E E' : Finset (ℕ × ℕ)}
    (hE : (∀ e ∈ E, e.1 < e.2 ∧ e.2 ≤ n - 1) ∧
      (∀ e ∈ E, ∀ f ∈ E, e ≠ f → ¬ ∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧ Sbtw ℝ (p f.1) q (p f.2)) ∧
      (∀ e : ℕ × ℕ, e.1 < e.2 → e.2 ≤ n - 1 →
        (∀ f ∈ E, e ≠ f → ¬ ∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧ Sbtw ℝ (p f.1) q (p f.2)) → e ∈ E))
    (hE' : (∀ e ∈ E', e.1 < e.2 ∧ e.2 ≤ n - 1) ∧
      (∀ e ∈ E', ∀ f ∈ E', e ≠ f → ¬ ∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧ Sbtw ℝ (p f.1) q (p f.2)) ∧
      (∀ e : ℕ × ℕ, e.1 < e.2 → e.2 ≤ n - 1 →
        (∀ f ∈ E', e ≠ f → ¬ ∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧ Sbtw ℝ (p f.1) q (p f.2)) → e ∈ E')) :
    ∑ t ∈ Finset.range n ×ˢ Finset.range n ×ˢ Finset.range n with
          (t.1, t.2.1) ∈ E ∧ (t.2.1, t.2.2) ∈ E ∧ (t.1, t.2.2) ∈ E,
        (if h : AffineIndependent ℝ ![p t.1, p t.2.1, p t.2.2] then
          (⟨_, h⟩ : Triangle ℝ P).inradius else 0) =
      ∑ t ∈ Finset.range n ×ˢ Finset.range n ×ˢ Finset.range n with
          (t.1, t.2.1) ∈ E' ∧ (t.2.1, t.2.2) ∈ E' ∧ (t.1, t.2.2) ∈ E',
        (if h : AffineIndependent ℝ ![p t.1, p t.2.1, p t.2.2] then
          (⟨_, h⟩ : Triangle ℝ P).inradius else 0) := by
  rw [← l14b_triangleInradiusSum_eq p n hn hE.1, ← l14b_triangleInradiusSum_eq p n hn hE'.1]
  exact japanese_polygon_geometric o p n s hn hs hconv
    ((l14b_isGeomTriangulation_iff p n E).2 hE) ((l14b_isGeomTriangulation_iff p n E').2 hE')

/-! ### Witnesses -/

section Witness

attribute [local instance] Complex.finrank_real_complex_fact

theorem l14b_norm {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : z.re ^ 2 + z.im ^ 2 = r ^ 2) : ‖z‖ = r := by
  rw [← Real.sqrt_sq hr, ← h, Complex.norm_def, normSq_apply]
  congr 1
  ring

theorem l14b_mem_unit {z : ℂ} (h : z.re ^ 2 + z.im ^ 2 = 1) :
    z ∈ (⟨0, 1⟩ : Sphere ℂ) := by
  rw [mem_sphere, dist_eq, sub_zero]
  exact l14b_norm zero_le_one (by rw [h]; norm_num)

theorem l14b_indep {a b c : ℂ} (h : 0 < Complex.orientation.areaForm (b -ᵥ a) (c -ᵥ a)) :
    AffineIndependent ℝ ![a, b, c] :=
  affineIndependent_of_areaForm_ne_zero Complex.orientation h.ne'

/-- The four orientation conditions for `1, (3 + 4i)/5, -1, -i`. -/
theorem l14b_quad_pos :
    0 < Complex.orientation.areaForm (((3 + 4 * I) / 5 : ℂ) -ᵥ 1) ((-1 : ℂ) -ᵥ 1) ∧
    0 < Complex.orientation.areaForm ((-1 : ℂ) -ᵥ 1) ((-I : ℂ) -ᵥ 1) ∧
    0 < Complex.orientation.areaForm (((3 + 4 * I) / 5 : ℂ) -ᵥ 1) ((-I : ℂ) -ᵥ 1) ∧
    0 < Complex.orientation.areaForm ((-1 : ℂ) -ᵥ (3 + 4 * I) / 5)
      ((-I : ℂ) -ᵥ (3 + 4 * I) / 5) := by
  simp only [Complex.areaForm, vsub_eq_sub]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [map_ofNat, div_re, div_im, normSq] <;> norm_num

/-- **Witness (quadrilateral).** `A = 1`, `B = (3 + 4i)/5`, `C = -1`, `D = -i` lie on the unit
circle, are pairwise distinct and counterclockwise; the four triangles are nondegenerate with
positive inradii, and the Japanese identity holds. -/
theorem l14w_japanese_quadrilateral :
    let A : ℂ := 1
    let B : ℂ := (3 + 4 * I) / 5
    let C : ℂ := -1
    let D : ℂ := -I
    ∃ (i₁ : AffineIndependent ℝ ![A, B, C]) (i₂ : AffineIndependent ℝ ![A, C, D])
      (i₃ : AffineIndependent ℝ ![A, B, D]) (i₄ : AffineIndependent ℝ ![B, C, D]),
      (A ∈ (⟨0, 1⟩ : Sphere ℂ) ∧ B ∈ (⟨0, 1⟩ : Sphere ℂ) ∧ C ∈ (⟨0, 1⟩ : Sphere ℂ) ∧
        D ∈ (⟨0, 1⟩ : Sphere ℂ)) ∧
      (A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D) ∧
      (0 < Complex.orientation.areaForm (B -ᵥ A) (C -ᵥ A) ∧
        0 < Complex.orientation.areaForm (C -ᵥ A) (D -ᵥ A) ∧
        0 < Complex.orientation.areaForm (B -ᵥ A) (D -ᵥ A) ∧
        0 < Complex.orientation.areaForm (C -ᵥ B) (D -ᵥ B)) ∧
      (0 < (⟨_, i₁⟩ : Triangle ℝ ℂ).inradius ∧ 0 < (⟨_, i₂⟩ : Triangle ℝ ℂ).inradius ∧
        0 < (⟨_, i₃⟩ : Triangle ℝ ℂ).inradius ∧ 0 < (⟨_, i₄⟩ : Triangle ℝ ℂ).inradius) ∧
      (⟨_, i₁⟩ : Triangle ℝ ℂ).inradius + (⟨_, i₂⟩ : Triangle ℝ ℂ).inradius =
        (⟨_, i₃⟩ : Triangle ℝ ℂ).inradius + (⟨_, i₄⟩ : Triangle ℝ ℂ).inradius := by
  intro A B C D
  obtain ⟨h1, h2, h3, h4⟩ := l14b_quad_pos
  have mA : A ∈ (⟨0, 1⟩ : Sphere ℂ) := l14b_mem_unit (by simp [A])
  have mB : B ∈ (⟨0, 1⟩ : Sphere ℂ) := l14b_mem_unit (by simp [B]; norm_num)
  have mC : C ∈ (⟨0, 1⟩ : Sphere ℂ) := l14b_mem_unit (by simp [C])
  have mD : D ∈ (⟨0, 1⟩ : Sphere ℂ) := l14b_mem_unit (by simp [D])
  refine ⟨l14b_indep h1, l14b_indep h2, l14b_indep h3, l14b_indep h4, ⟨mA, mB, mC, mD⟩, ?_,
    ⟨h1, h2, h3, h4⟩, ⟨Simplex.inradius_pos _, Simplex.inradius_pos _, Simplex.inradius_pos _,
      Simplex.inradius_pos _⟩,
    l14_japanese_quadrilateral Complex.orientation _ mA mB mC mD h1 h2 h3 h4 _ _ _ _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;>
    have h' := congrArg (fun z : ℂ => (z.re, z.im)) h <;>
    norm_num [A, B, C, D, div_re, div_im, normSq] at h'

/-- The witness quadrilateral as a polygon `ℕ → ℂ`. -/
noncomputable def l14b_quad (k : ℕ) : ℂ := [1, (3 + 4 * I) / 5, -1, -I].getD k 0

theorem l14b_quad_conv : ∀ a b c, a < b → b < c → c < 4 →
    0 < Complex.orientation.areaForm (l14b_quad b -ᵥ l14b_quad a) (l14b_quad c -ᵥ l14b_quad a) := by
  obtain ⟨h1, h2, h3, h4⟩ := l14b_quad_pos
  intro a b c hab hbc hc
  interval_cases c <;> interval_cases b <;> interval_cases a <;> assumption

theorem l14b_quad_tri {E : Finset (ℕ × ℕ)} (hE : IsTriangulation 0 3 E) :
    (∀ e ∈ E, e.1 < e.2 ∧ e.2 ≤ 4 - 1) ∧
      (∀ e ∈ E, ∀ f ∈ E, e ≠ f → ¬ ∃ q, Sbtw ℝ (l14b_quad e.1) q (l14b_quad e.2) ∧
        Sbtw ℝ (l14b_quad f.1) q (l14b_quad f.2)) ∧
      (∀ e : ℕ × ℕ, e.1 < e.2 → e.2 ≤ 4 - 1 →
        (∀ f ∈ E, e ≠ f → ¬ ∃ q, Sbtw ℝ (l14b_quad e.1) q (l14b_quad e.2) ∧
          Sbtw ℝ (l14b_quad f.1) q (l14b_quad f.2)) → e ∈ E) :=
  (l14b_isGeomTriangulation_iff l14b_quad 4 E).1
    ((isGeomTriangulation_iff Complex.orientation l14b_quad 4 l14b_quad_conv (by norm_num)).2 hE)

theorem l14b_isTri_iff (E : Finset (ℕ × ℕ)) (hc : ∀ e ∈ E, IsChord 0 3 e)
    (hn : ∀ e ∈ E, ∀ f ∈ E, ¬ Crosses e f)
    (hm : ∀ a b, a < b → b ≤ 3 → (∀ f ∈ E, ¬ Crosses (a, b) f) → (a, b) ∈ E) :
    IsTriangulation 0 3 E :=
  ⟨hc, hn, fun e he h => hm e.1 e.2 he.2.1 he.2.2 h⟩

open Classical in
/-- **Witness (polygon).** The quadrilateral `1, (3 + 4i)/5, -1, -i` (inscribed in the unit
circle, strictly convex, counterclockwise) with the two different triangulations
`E = sides ∪ {(0, 2)}` and `E' = sides ∪ {(1, 3)}`; both satisfy the Mathlib-only triangulation
conditions, and the inradius sums over their (different) triangle sets agree. -/
theorem l14w_japanese_polygon :
    let p : ℕ → ℂ := fun k => [1, (3 + 4 * I) / 5, -1, -I].getD k 0
    let E : Finset (ℕ × ℕ) := {(0, 1), (1, 2), (2, 3), (0, 3), (0, 2)}
    let E' : Finset (ℕ × ℕ) := {(0, 1), (1, 2), (2, 3), (0, 3), (1, 3)}
    E ≠ E' ∧ (∀ l < 4, p l ∈ (⟨0, 1⟩ : Sphere ℂ)) ∧
    (∀ a b c, a < b → b < c → c < 4 →
      0 < Complex.orientation.areaForm (p b -ᵥ p a) (p c -ᵥ p a)) ∧
    ((∀ e ∈ E, e.1 < e.2 ∧ e.2 ≤ 4 - 1) ∧
      (∀ e ∈ E, ∀ f ∈ E, e ≠ f → ¬ ∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧
        Sbtw ℝ (p f.1) q (p f.2)) ∧
      (∀ e : ℕ × ℕ, e.1 < e.2 → e.2 ≤ 4 - 1 →
        (∀ f ∈ E, e ≠ f → ¬ ∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧
          Sbtw ℝ (p f.1) q (p f.2)) → e ∈ E)) ∧
    ((∀ e ∈ E', e.1 < e.2 ∧ e.2 ≤ 4 - 1) ∧
      (∀ e ∈ E', ∀ f ∈ E', e ≠ f → ¬ ∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧
        Sbtw ℝ (p f.1) q (p f.2)) ∧
      (∀ e : ℕ × ℕ, e.1 < e.2 → e.2 ≤ 4 - 1 →
        (∀ f ∈ E', e ≠ f → ¬ ∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧
          Sbtw ℝ (p f.1) q (p f.2)) → e ∈ E')) ∧
    (∑ t ∈ Finset.range 4 ×ˢ Finset.range 4 ×ˢ Finset.range 4 with
          (t.1, t.2.1) ∈ E ∧ (t.2.1, t.2.2) ∈ E ∧ (t.1, t.2.2) ∈ E,
        (if h : AffineIndependent ℝ ![p t.1, p t.2.1, p t.2.2] then
          (⟨_, h⟩ : Triangle ℝ ℂ).inradius else 0) =
      ∑ t ∈ Finset.range 4 ×ˢ Finset.range 4 ×ˢ Finset.range 4 with
          (t.1, t.2.1) ∈ E' ∧ (t.2.1, t.2.2) ∈ E' ∧ (t.1, t.2.2) ∈ E',
        (if h : AffineIndependent ℝ ![p t.1, p t.2.1, p t.2.2] then
          (⟨_, h⟩ : Triangle ℝ ℂ).inradius else 0)) := by
  intro p E E'
  have hs : ∀ l < 4, l14b_quad l ∈ (⟨0, 1⟩ : Sphere ℂ) := by
    intro l hl
    interval_cases l <;> refine l14b_mem_unit ?_ <;> simp [l14b_quad] <;> norm_num
  have tE : IsTriangulation 0 3 E := by
    refine l14b_isTri_iff E ?_ ?_ ?_
    · intro e he; simp only [E, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl <;> simp [IsChord]
    · intro e he f hf; simp only [E, Finset.mem_insert, Finset.mem_singleton] at he hf
      rcases he with rfl | rfl | rfl | rfl | rfl <;> rcases hf with rfl | rfl | rfl | rfl | rfl <;>
        simp [Crosses]
    · intro a b hab hb h
      interval_cases b <;> interval_cases a <;> simp [E] <;>
        exact absurd (show Crosses (1, 3) (0, 2) by simp [Crosses]) (h _ (by simp [E]))
  have tE' : IsTriangulation 0 3 E' := by
    refine l14b_isTri_iff E' ?_ ?_ ?_
    · intro e he; simp only [E', Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl <;> simp [IsChord]
    · intro e he f hf; simp only [E', Finset.mem_insert, Finset.mem_singleton] at he hf
      rcases he with rfl | rfl | rfl | rfl | rfl <;> rcases hf with rfl | rfl | rfl | rfl | rfl <;>
        simp [Crosses]
    · intro a b hab hb h
      interval_cases b <;> interval_cases a <;> simp [E'] <;>
        exact absurd (show Crosses (0, 2) (1, 3) by simp [Crosses]) (h _ (by simp [E']))
  have gE := l14b_quad_tri tE
  have gE' := l14b_quad_tri tE'
  show E ≠ E' ∧ (∀ l < 4, l14b_quad l ∈ (⟨0, 1⟩ : Sphere ℂ)) ∧ _
  refine ⟨?_, hs, l14b_quad_conv, gE, gE', ?_⟩
  · intro h
    have : ((0, 2) : ℕ × ℕ) ∈ E' := h ▸ (by simp [E])
    simp [E'] at this
  · exact l14_japanese_polygon Complex.orientation _ l14b_quad 4 (by norm_num) hs l14b_quad_conv gE gE'

end Witness

end Japanese
