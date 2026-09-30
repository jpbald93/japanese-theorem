import Japanese.Combinatorial

/-!
# Geometric non-crossing for points in convex position

Points `p : ℕ → P` of an oriented Euclidean plane are in strictly convex counterclockwise position
if `0 < o.areaForm (p b -ᵥ p a) (p c -ᵥ p a)` for all `a < b < c < n` (the hypothesis `hconv`
used throughout the project).

* `exists_sbtw_sbtw_of_areaForm` / `not_wbtw_wbtw_of_pos` / `not_sbtw_sbtw_of_ne_zero` are the
  point-level sign criteria: two segments cross when the orientations say they interleave; a
  segment whose line has both endpoints of another (closed) segment strictly on one side does not
  meet it; two open segments from a common endpoint in different directions are disjoint.
* `sbtw_inter_iff_interleave`: for `a < b`, `c < d` with `{a,b} ∩ {c,d} = ∅`, the open segments
  `(p a, p b)` and `(p c, p d)` meet iff the indices interleave.
* `geomCrosses_iff`: for distinct chords, geometric crossing ⇔ combinatorial `Crosses`
  (this includes chords with a common endpoint, which never cross).
* `IsGeomTriangulation`: maximal set of chords whose open segments are pairwise disjoint;
  `isGeomTriangulation_iff` identifies it with `IsTriangulation`.
* `japanese_polygon_geometric`: the Japanese theorem with geometric non-crossing hypotheses.
-/

namespace Japanese

open EuclideanGeometry Module
open scoped RealInnerProductSpace

section ConvexPosition

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- In the plane, a vector annihilated by `ω u` and `ω v`, for `ω u v ≠ 0`, is zero. -/
lemma eq_zero_of_areaForm_eq_zero {u v e : V} (huv : o.areaForm u v ≠ 0)
    (hu : o.areaForm u e = 0) (hv : o.areaForm v e = 0) : e = 0 := by
  have h1 := o.inner_mul_areaForm_sub u e v
  rw [hu, o.areaForm_swap e v, hv] at h1
  have hie : ⟪u, e⟫ = 0 := by
    have : ⟪u, e⟫ * o.areaForm u v = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h huv
  have h2 := o.inner_sq_add_areaForm_sq u e
  rw [hie, hu] at h2
  have hu0 : u ≠ 0 := by rintro rfl; simp at huv
  have h3 : ‖u‖ ^ 2 * ‖e‖ ^ 2 = 0 := by linear_combination -h2
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) (norm_ne_zero_iff.mpr hu0)
  · exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)

/-- Re-basing the area form at another point. -/
lemma areaForm_vsub_expand (x y z w : P) :
    o.areaForm (y -ᵥ z) (w -ᵥ z) = o.areaForm (y -ᵥ x) (w -ᵥ x) -
      o.areaForm (y -ᵥ x) (z -ᵥ x) - o.areaForm (z -ᵥ x) (w -ᵥ x) := by
  rw [← vsub_sub_vsub_cancel_right y z x, ← vsub_sub_vsub_cancel_right w z x]
  simp only [map_sub, LinearMap.sub_apply, o.areaForm_apply_self]
  ring

/-- **Interleaving orientations ⇒ crossing.** If `x, z, y, w` are in convex counterclockwise
position (the four orientation signs of the quadruple `x z y w`), then the open segments `(x, y)`
and `(z, w)` meet. -/
lemma exists_sbtw_sbtw_of_areaForm {x y z w : P}
    (hacb : 0 < o.areaForm (z -ᵥ x) (y -ᵥ x)) (habd : 0 < o.areaForm (y -ᵥ x) (w -ᵥ x))
    (hacd : 0 < o.areaForm (z -ᵥ x) (w -ᵥ x)) (hcbd : 0 < o.areaForm (y -ᵥ z) (w -ᵥ z)) :
    ∃ q, Sbtw ℝ x q y ∧ Sbtw ℝ z q w := by
  have hxy : x ≠ y := by rintro rfl; simp at hacb
  have hzw : z ≠ w := by rintro rfl; simp at hcbd
  rw [areaForm_vsub_expand o x] at hcbd
  rw [o.areaForm_swap] at hacb
  have hd : 0 < o.areaForm (y -ᵥ x) (w -ᵥ x) - o.areaForm (y -ᵥ x) (z -ᵥ x) := by linarith
  have hd' := hd.ne'
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = o.areaForm (z -ᵥ x) (w -ᵥ x) /
      (o.areaForm (y -ᵥ x) (w -ᵥ x) - o.areaForm (y -ᵥ x) (z -ᵥ x)) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = -o.areaForm (y -ᵥ x) (z -ᵥ x) /
      (o.areaForm (y -ᵥ x) (w -ᵥ x) - o.areaForm (y -ᵥ x) (z -ᵥ x)) := ⟨_, rfl⟩
  have hq : AffineMap.lineMap x y l = AffineMap.lineMap z w t := by
    rw [← vsub_eq_zero_iff_eq,
      ← vsub_sub_vsub_cancel_right (AffineMap.lineMap x y l) (AffineMap.lineMap z w t) x,
      AffineMap.lineMap_vsub_left, ← vsub_add_vsub_cancel (AffineMap.lineMap z w t) z x,
      AffineMap.lineMap_vsub_left, ← vsub_sub_vsub_cancel_right w z x]
    apply eq_zero_of_areaForm_eq_zero o (u := y -ᵥ x) (v := (w -ᵥ x) - (z -ᵥ x))
    · rw [map_sub]; exact hd'
    · simp only [map_sub, map_add, map_smul, smul_eq_mul, o.areaForm_apply_self]
      rw [ht]; field_simp; ring
    · simp only [map_sub, map_add, map_smul, smul_eq_mul, LinearMap.sub_apply,
        o.areaForm_apply_self]
      simp only [o.areaForm_swap (w -ᵥ x) (y -ᵥ x), o.areaForm_swap (z -ᵥ x) (y -ᵥ x),
        o.areaForm_swap (w -ᵥ x) (z -ᵥ x)]
      rw [hl]
      field_simp; ring
  refine ⟨AffineMap.lineMap x y l, ?_, ?_⟩
  · rw [sbtw_lineMap_iff]
    refine ⟨hxy, ?_, ?_⟩
    · rw [hl]; exact div_pos hacd hd
    · rw [hl]; exact (div_lt_one hd).mpr (by linarith)
  · rw [hq, sbtw_lineMap_iff]
    refine ⟨hzw, ?_, ?_⟩
    · rw [ht]; exact div_pos (by linarith) hd
    · rw [ht]; exact (div_lt_one hd).mpr (by linarith)

/-- **Same side ⇒ no meeting.** If `z` and `w` lie strictly to the left of the line `x → y`, then
the closed segments `[x, y]` and `[z, w]` are disjoint. -/
lemma not_wbtw_wbtw_of_pos {x y z w : P} (hz : 0 < o.areaForm (y -ᵥ x) (z -ᵥ x))
    (hw : 0 < o.areaForm (y -ᵥ x) (w -ᵥ x)) : ¬ ∃ q, Wbtw ℝ x q y ∧ Wbtw ℝ z q w := by
  rintro ⟨q, ⟨l, -, rfl⟩, ⟨t, ⟨ht0, ht1⟩, hq⟩⟩
  have key : o.areaForm (y -ᵥ x) (AffineMap.lineMap z w t -ᵥ x) =
      o.areaForm (y -ᵥ x) (AffineMap.lineMap x y l -ᵥ x) := by rw [hq]
  rw [AffineMap.lineMap_vsub_left, ← vsub_add_vsub_cancel (AffineMap.lineMap z w t) z x,
    AffineMap.lineMap_vsub_left, ← vsub_sub_vsub_cancel_right w z x] at key
  simp only [map_add, map_smul, map_sub, smul_eq_mul, o.areaForm_apply_self] at key
  rcases ht0.eq_or_lt with h | h
  · subst h; nlinarith
  · nlinarith [mul_pos h hw, mul_nonneg (sub_nonneg.2 ht1) hz.le]

/-- **Common endpoint.** Open segments `(x, y)` and `(x, w)` with `x, y, w` not collinear are
disjoint. -/
lemma not_sbtw_sbtw_of_ne_zero {x y w : P} (h : o.areaForm (y -ᵥ x) (w -ᵥ x) ≠ 0) :
    ¬ ∃ q, Sbtw ℝ x q y ∧ Sbtw ℝ x q w := by
  rintro ⟨q, ⟨⟨l, -, rfl⟩, -, -⟩, ⟨⟨t, -, hq⟩, hqx, -⟩⟩
  have key : o.areaForm (y -ᵥ x) (AffineMap.lineMap x w t -ᵥ x) =
      o.areaForm (y -ᵥ x) (AffineMap.lineMap x y l -ᵥ x) := by rw [hq]
  simp only [AffineMap.lineMap_vsub_left, map_smul, smul_eq_mul, o.areaForm_apply_self] at key
  have ht : t ≠ 0 := by
    rintro rfl
    exact hqx (by rw [← hq, AffineMap.lineMap_apply_zero])
  have h0 : t * o.areaForm (y -ᵥ x) (w -ᵥ x) = 0 := by linear_combination key
  exact h ((mul_eq_zero.mp h0).resolve_left ht)

variable (p : ℕ → P) (n : ℕ)
  (hconv : ∀ a b c, a < b → b < c → c < n → 0 < o.areaForm (p b -ᵥ p a) (p c -ᵥ p a))
include hconv

/-- Convex position: the triangle `p i, p j, p k` is positively oriented when `i, j, k` are in
cyclic increasing order. -/
lemma areaForm_pos_of_cyclic {i j k : ℕ} (hi : i < n) (hj : j < n) (hk : k < n)
    (h : (i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j)) :
    0 < o.areaForm (p j -ᵥ p i) (p k -ᵥ p i) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hconv i j k h1 h2 hk
  · rw [← areaForm_cyc₁ o (p i) (p j) (p k)]; exact hconv j k i h1 h2 hi
  · rw [← areaForm_cyc₂ o (p i) (p j) (p k)]; exact hconv k i j h1 h2 hj

/-- Convex position: the triangle `p i, p j, p k` is negatively oriented when `i, j, k` are in
cyclic decreasing order. -/
lemma areaForm_neg_of_cyclic {i j k : ℕ} (hi : i < n) (hj : j < n) (hk : k < n)
    (h : (i < k ∧ k < j) ∨ (k < j ∧ j < i) ∨ (j < i ∧ i < k)) :
    o.areaForm (p j -ᵥ p i) (p k -ᵥ p i) < 0 := by
  rw [o.areaForm_swap]
  have := areaForm_pos_of_cyclic o p n hconv hi hk hj h
  linarith

lemma areaForm_ne_zero_of_ne {i j k : ℕ} (hi : i < n) (hj : j < n) (hk : k < n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : o.areaForm (p j -ᵥ p i) (p k -ᵥ p i) ≠ 0 := by
  rcases (show ((i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j)) ∨
      ((i < k ∧ k < j) ∨ (k < j ∧ j < i) ∨ (j < i ∧ i < k)) by omega) with h | h
  · exact (areaForm_pos_of_cyclic o p n hconv hi hj hk h).ne'
  · exact (areaForm_neg_of_cyclic o p n hconv hi hj hk h).ne

/-- Interleaving indices ⇒ the open segments cross. -/
lemma exists_sbtw_sbtw_of_interleave {a b c d : ℕ} (h1 : a < c) (h2 : c < b) (h3 : b < d)
    (hd : d < n) : ∃ q, Sbtw ℝ (p a) q (p b) ∧ Sbtw ℝ (p c) q (p d) :=
  exists_sbtw_sbtw_of_areaForm o (hconv a c b h1 h2 (by omega)) (hconv a b d (by omega) h3 hd)
    (hconv a c d h1 (by omega) hd) (hconv c b d h2 h3 hd)

/-- Disjoint, non-interleaving index pairs ⇒ even the closed segments are disjoint. -/
lemma not_wbtw_wbtw_of_not_interleave {a b c d : ℕ} (hab : a < b) (hcd : c < d) (hb : b < n)
    (hd : d < n) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hni : ¬ ((a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b))) :
    ¬ ∃ q, Wbtw ℝ (p a) q (p b) ∧ Wbtw ℝ (p c) q (p d) := by
  rcases (show (b < c ∨ d < a ∨ (c < a ∧ b < d)) ∨ (a < c ∧ d < b) by omega) with h | h
  · exact not_wbtw_wbtw_of_pos o
      (areaForm_pos_of_cyclic o p n hconv (by omega) hb (by omega) (by omega))
      (areaForm_pos_of_cyclic o p n hconv (by omega) hb hd (by omega))
  · rintro ⟨q, h1, h2⟩
    exact not_wbtw_wbtw_of_pos o
      (areaForm_pos_of_cyclic o p n hconv hb (by omega) (by omega) (by omega))
      (areaForm_pos_of_cyclic o p n hconv hb (by omega) hd (by omega)) ⟨q, wbtw_comm.mp h1, h2⟩

/-- **Geometric crossing ⇔ interleaving** (disjoint endpoints). For `a < b`, `c < d` with
`{a, b} ∩ {c, d} = ∅`, the open segments `(p a, p b)` and `(p c, p d)` meet iff
`a < c < b < d` or `c < a < d < b`. -/
theorem sbtw_inter_iff_interleave {a b c d : ℕ} (hab : a < b) (hcd : c < d) (hb : b < n)
    (hd : d < n) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (∃ q, Sbtw ℝ (p a) q (p b) ∧ Sbtw ℝ (p c) q (p d)) ↔
      (a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b) := by
  constructor
  · rintro ⟨q, h1, h2⟩
    by_contra hni
    exact not_wbtw_wbtw_of_not_interleave o p n hconv hab hcd hb hd hac had hbc hbd hni
      ⟨q, h1.wbtw, h2.wbtw⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact exists_sbtw_sbtw_of_interleave o p n hconv h1 h2 h3 hd
    · obtain ⟨q, h, h'⟩ := exists_sbtw_sbtw_of_interleave o p n hconv h1 h2 h3 hb
      exact ⟨q, h', h⟩

end ConvexPosition

section Triangulations

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The chords `e` and `f` cross geometrically: their open segments share a point. -/
def GeomCrosses (p : ℕ → P) (e f : ℕ × ℕ) : Prop :=
  ∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧ Sbtw ℝ (p f.1) q (p f.2)

/-- A geometric triangulation of the polygon `p i, …, p j`: a set of chords whose open segments
are pairwise disjoint, maximal with this property. -/
structure IsGeomTriangulation (p : ℕ → P) (i j : ℕ) (E : Finset (ℕ × ℕ)) : Prop where
  chord : ∀ e ∈ E, IsChord i j e
  noncross : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → ¬ GeomCrosses p e f
  maximal : ∀ e, IsChord i j e → (∀ f ∈ E, e ≠ f → ¬ GeomCrosses p e f) → e ∈ E

variable [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2)) (p : ℕ → P) (n : ℕ)
  (hconv : ∀ a b c, a < b → b < c → c < n → 0 < o.areaForm (p b -ᵥ p a) (p c -ᵥ p a))
include hconv

/-- **Geometric ⇔ combinatorial crossing** for distinct chords, including chords with a common
endpoint (which never cross). -/
theorem geomCrosses_iff {e f : ℕ × ℕ} (he : e.1 < e.2) (hen : e.2 < n) (hf : f.1 < f.2)
    (hfn : f.2 < n) (hef : e ≠ f) : GeomCrosses p e f ↔ Crosses e f := by
  obtain ⟨a, b⟩ := e
  obtain ⟨c, d⟩ := f
  simp only [GeomCrosses, Crosses] at he hen hf hfn ⊢
  have hne : ∀ {i j k : ℕ}, i < n → j < n → k < n → i ≠ j → i ≠ k → j ≠ k →
      o.areaForm (p j -ᵥ p i) (p k -ᵥ p i) ≠ 0 :=
    fun hi hj hk hij hik hjk => areaForm_ne_zero_of_ne o p n hconv hi hj hk hij hik hjk
  rcases eq_or_ne a c with rfl | hac
  · have hbd : b ≠ d := by rintro rfl; exact hef rfl
    refine iff_of_false (not_sbtw_sbtw_of_ne_zero o (hne (by omega) hen hfn (by omega)
      (by omega) hbd)) (by omega)
  rcases eq_or_ne b d with rfl | hbd
  · refine iff_of_false ?_ (by omega)
    rintro ⟨q, h1, h2⟩
    exact not_sbtw_sbtw_of_ne_zero o (hne hen (by omega) (by omega) (by omega) (by omega) hac)
      ⟨q, sbtw_comm.mp h1, sbtw_comm.mp h2⟩
  rcases eq_or_ne b c with rfl | hbc
  · refine iff_of_false ?_ (by omega)
    rintro ⟨q, h1, h2⟩
    exact not_sbtw_sbtw_of_ne_zero o (hne hen (by omega) hfn (by omega) (by omega) (by omega))
      ⟨q, sbtw_comm.mp h1, h2⟩
  rcases eq_or_ne a d with rfl | had
  · refine iff_of_false ?_ (by omega)
    rintro ⟨q, h1, h2⟩
    exact not_sbtw_sbtw_of_ne_zero o (hne (by omega) hen (by omega) (by omega) (by omega)
      (by omega)) ⟨q, h1, sbtw_comm.mp h2⟩
  exact sbtw_inter_iff_interleave o p n hconv he hf hen hfn hac had hbc hbd

/-- Geometric and combinatorial triangulations coincide for points in convex position. -/
theorem isGeomTriangulation_iff {i j : ℕ} (hjn : j < n) {E : Finset (ℕ × ℕ)} :
    IsGeomTriangulation p i j E ↔ IsTriangulation i j E := by
  have key : ∀ e f, IsChord i j e → IsChord i j f → e ≠ f →
      (GeomCrosses p e f ↔ Crosses e f) := fun e f he hf hef =>
    geomCrosses_iff o p n hconv he.2.1 (by have := he.2.2; omega) hf.2.1
      (by have := hf.2.2; omega) hef
  have self : ∀ e : ℕ × ℕ, ¬ Crosses e e := fun ⟨a, b⟩ => by simp only [Crosses]; omega
  constructor
  · intro h
    refine ⟨h.chord, fun e he f hf => ?_, fun e he hnc => h.maximal e he fun f hf hef => ?_⟩
    · by_cases hef : e = f
      · subst hef; exact self e
      · rw [← key e f (h.chord e he) (h.chord f hf) hef]; exact h.noncross e he f hf hef
    · rw [key e f he (h.chord f hf) hef]; exact hnc f hf
  · intro h
    refine ⟨h.chord, fun e he f hf hef => ?_, fun e he hnc => h.maximal e he fun f hf => ?_⟩
    · rw [key e f (h.chord e he) (h.chord f hf) hef]; exact h.noncross e he f hf
    · by_cases hef : e = f
      · subst hef; exact self e
      · rw [← key e f he (h.chord f hf) hef]; exact hnc f hf hef

omit hconv in
/-- **Japanese theorem for convex cyclic polygons, geometric triangulations.** Let
`p 0, …, p (n-1)` be concyclic and in strictly convex counterclockwise position. For any two
maximal sets of chords with pairwise disjoint open segments, the sums of the inradii of the
resulting triangles agree. -/
theorem japanese_polygon_geometric (s : Sphere P) (hn : 2 ≤ n) (hs : ∀ l < n, p l ∈ s)
    (hconv : ∀ a b c, a < b → b < c → c < n → 0 < o.areaForm (p b -ᵥ p a) (p c -ᵥ p a))
    {E E' : Finset (ℕ × ℕ)} (hE : IsGeomTriangulation p 0 (n - 1) E)
    (hE' : IsGeomTriangulation p 0 (n - 1) E') :
    triangleInradiusSum p (triangleSet E) = triangleInradiusSum p (triangleSet E') :=
  japanese_polygon_combinatorial o s p n hn hs hconv
    ((isGeomTriangulation_iff o p n hconv (by omega)).mp hE)
    ((isGeomTriangulation_iff o p n hconv (by omega)).mp hE')

end Triangulations

end Japanese
