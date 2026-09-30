import Japanese.Polygon

/-!
# Combinatorial triangulations of a convex polygon

A *chord* of the convex polygon with vertices `i, i+1, …, j` is a pair `(a, b)` with
`i ≤ a < b ≤ j` (sides, diagonals, and the closing side `(i, j)`). Two chords `(a, b)`, `(c, d)`
*cross* if their endpoints interleave strictly: `a < c < b < d` or `c < a < d < b`.

`IsTriangulation i j E` : `E` is a maximal set of pairwise non-crossing chords of `i..j`.
Sides and `(i, j)` cross nothing, so by maximality they always lie in `E`; `E` minus them is a
maximal set of pairwise non-crossing diagonals. The triangles are read off from `E`
(`triangleSet E`: triples all three of whose sides lie in `E`).
-/

namespace Japanese

/-- `(a, b)` is a chord of the polygon `i..j`. -/
def IsChord (i j : ℕ) (e : ℕ × ℕ) : Prop := i ≤ e.1 ∧ e.1 < e.2 ∧ e.2 ≤ j

/-- Two chords cross (strictly interleaving endpoints). -/
def Crosses (e f : ℕ × ℕ) : Prop :=
  (e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2) ∨ (f.1 < e.1 ∧ e.1 < f.2 ∧ f.2 < e.2)

lemma crosses_comm {e f : ℕ × ℕ} : Crosses e f ↔ Crosses f e := by
  unfold Crosses; tauto

/-- A (combinatorial) triangulation of the convex polygon `i..j`: a maximal set of pairwise
non-crossing chords. -/
structure IsTriangulation (i j : ℕ) (E : Finset (ℕ × ℕ)) : Prop where
  chord : ∀ e ∈ E, IsChord i j e
  noncross : ∀ e ∈ E, ∀ f ∈ E, ¬ Crosses e f
  maximal : ∀ e, IsChord i j e → (∀ f ∈ E, ¬ Crosses e f) → e ∈ E

/-- The triangles `(a, b, c)` of a chord set: all three sides `ab`, `bc`, `ac` belong to `E`. -/
def triangleSet (E : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ × ℕ) :=
  ((E ×ˢ E).filter (fun x => x.1.2 = x.2.1 ∧ (x.1.1, x.2.2) ∈ E)).image
    (fun x => (x.1.1, x.1.2, x.2.2))

lemma mem_triangleSet {E : Finset (ℕ × ℕ)} {t : ℕ × ℕ × ℕ} :
    t ∈ triangleSet E ↔ (t.1, t.2.1) ∈ E ∧ (t.2.1, t.2.2) ∈ E ∧ (t.1, t.2.2) ∈ E := by
  obtain ⟨a, b, c⟩ := t
  simp only [triangleSet, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists,
    Prod.mk.injEq]
  constructor
  · rintro ⟨x, y, z, w, ⟨⟨h1, h2⟩, rfl, h3⟩, rfl, rfl, rfl⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨a, b, b, c, ⟨⟨h1, h2⟩, rfl, h3⟩, rfl, rfl, rfl⟩

namespace Triangulation

/-- All chords (sides, diagonals and the root side) used by a tree triangulation. -/
def chords : {i j : ℕ} → Triangulation i j → Finset (ℕ × ℕ)
  | _, _, edge i => {(i, i + 1)}
  | i, j, node _ _ T₁ T₂ => insert (i, j) (T₁.chords ∪ T₂.chords)

theorem mem_chords_root : {i j : ℕ} → (T : Triangulation i j) → (i, j) ∈ T.chords
  | _, _, edge _ => by simp [chords]
  | _, _, node _ _ _ _ => by simp [chords]

theorem isChord_of_mem_chords : {i j : ℕ} → (T : Triangulation i j) →
    ∀ e ∈ T.chords, IsChord i j e
  | _, _, edge i => by simp [chords, IsChord]
  | _, _, node hik hkj T₁ T₂ => by
    intro e he
    simp only [chords, Finset.mem_insert, Finset.mem_union] at he
    rcases he with rfl | h | h
    · exact ⟨le_rfl, hik.trans hkj, le_rfl⟩
    · have := isChord_of_mem_chords T₁ e h; unfold IsChord at *; omega
    · have := isChord_of_mem_chords T₂ e h; unfold IsChord at *; omega

end Triangulation

lemma not_crosses_root {i j : ℕ} {e : ℕ × ℕ} (he : IsChord i j e) : ¬ Crosses (i, j) e := by
  obtain ⟨a, b⟩ := e
  simp only [IsChord, Crosses] at *
  omega

namespace Triangulation

theorem noncross : {i j : ℕ} → (T : Triangulation i j) →
    ∀ e ∈ T.chords, ∀ f ∈ T.chords, ¬ Crosses e f
  | _, _, edge i => by
    intro e he f hf
    simp only [chords, Finset.mem_singleton] at he hf
    subst he hf
    simp [Crosses]
  | i, j, node (k := k) hik hkj T₁ T₂ => by
    intro e he f hf
    simp only [chords, Finset.mem_insert, Finset.mem_union] at he hf
    obtain ⟨a, b⟩ := e
    obtain ⟨c, d⟩ := f
    rcases he with he | he | he <;> rcases hf with hf | hf | hf
    · simp only [Prod.mk.injEq] at he hf
      simp only [Crosses]; omega
    · have h := isChord_of_mem_chords T₁ _ hf
      simp only [Prod.mk.injEq] at he
      simp only [IsChord, Crosses] at h ⊢; omega
    · have h := isChord_of_mem_chords T₂ _ hf
      simp only [Prod.mk.injEq] at he
      simp only [IsChord, Crosses] at h ⊢; omega
    · have h := isChord_of_mem_chords T₁ _ he
      simp only [Prod.mk.injEq] at hf
      simp only [IsChord, Crosses] at h ⊢; omega
    · exact noncross T₁ _ he _ hf
    · have h := isChord_of_mem_chords T₁ _ he
      have h' := isChord_of_mem_chords T₂ _ hf
      simp only [IsChord, Crosses] at h h' ⊢; omega
    · have h := isChord_of_mem_chords T₂ _ he
      simp only [Prod.mk.injEq] at hf
      simp only [IsChord, Crosses] at h ⊢; omega
    · have h := isChord_of_mem_chords T₂ _ he
      have h' := isChord_of_mem_chords T₁ _ hf
      simp only [IsChord, Crosses] at h h' ⊢; omega
    · exact noncross T₂ _ he _ hf

theorem maximal : {i j : ℕ} → (T : Triangulation i j) →
    ∀ e, IsChord i j e → (∀ f ∈ T.chords, ¬ Crosses e f) → e ∈ T.chords
  | _, _, edge i => by
    rintro ⟨a, b⟩ h _
    simp only [IsChord] at h
    have ha : a = i := by omega
    have hb : b = i + 1 := by omega
    subst ha hb
    simp [chords]
  | i, j, node (k := k) hik hkj T₁ T₂ => by
    rintro ⟨a, b⟩ he hnc
    have h1 : (i, k) ∈ (node hik hkj T₁ T₂).chords := by simp [chords, mem_chords_root T₁]
    have h2 : (k, j) ∈ (node hik hkj T₁ T₂).chords := by simp [chords, mem_chords_root T₂]
    have n1 := hnc _ h1
    have n2 := hnc _ h2
    simp only [Crosses] at n1 n2
    simp only [IsChord] at he
    simp only [chords, Finset.mem_insert, Finset.mem_union, Prod.mk.injEq]
    by_cases hij : a = i ∧ b = j
    · exact Or.inl hij
    by_cases hbk : b ≤ k
    · refine Or.inr (Or.inl (maximal T₁ (a, b) (by simp only [IsChord]; omega) ?_))
      intro f hf
      exact hnc f (by simp [chords, hf])
    · by_cases hak : k ≤ a
      · refine Or.inr (Or.inr (maximal T₂ (a, b) (by simp only [IsChord]; omega) ?_))
        intro f hf
        exact hnc f (by simp [chords, hf])
      · exfalso; omega

/-- Every tree triangulation gives a combinatorial triangulation. -/
theorem isTriangulation {i j : ℕ} (T : Triangulation i j) : IsTriangulation i j T.chords :=
  ⟨T.isChord_of_mem_chords, T.noncross, T.maximal⟩

theorem chords_of_mem_triangles : {i j : ℕ} → (T : Triangulation i j) → ∀ a b c : ℕ,
    (a, b, c) ∈ T.triangles → (a, b) ∈ T.chords ∧ (b, c) ∈ T.chords ∧ (a, c) ∈ T.chords
  | _, _, edge _ => by simp [triangles]
  | i, j, node (k := k) hik hkj T₁ T₂ => by
    intro a b c h
    simp only [triangles, List.mem_cons, List.mem_append] at h
    simp only [chords, Finset.mem_insert, Finset.mem_union]
    rcases h with h | h | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨Or.inr (Or.inl (mem_chords_root T₁)), Or.inr (Or.inr (mem_chords_root T₂)),
        Or.inl rfl⟩
    · obtain ⟨h1, h2, h3⟩ := chords_of_mem_triangles T₁ a b c h
      exact ⟨Or.inr (Or.inl h1), Or.inr (Or.inl h2), Or.inr (Or.inl h3)⟩
    · obtain ⟨h1, h2, h3⟩ := chords_of_mem_triangles T₂ a b c h
      exact ⟨Or.inr (Or.inr h1), Or.inr (Or.inr h2), Or.inr (Or.inr h3)⟩

end Triangulation

namespace Triangulation

section faces

variable {i k j : ℕ} {hik : i < k} {hkj : k < j} {T₁ : Triangulation i k} {T₂ : Triangulation k j}

lemma mem_left {e : ℕ × ℕ} (he : e ∈ (node hik hkj T₁ T₂).chords) (h : e.2 ≤ k) :
    e ∈ T₁.chords := by
  simp only [chords, Finset.mem_insert, Finset.mem_union] at he
  rcases he with rfl | he | he
  · simp at h; omega
  · exact he
  · have := isChord_of_mem_chords T₂ e he; unfold IsChord at this; omega

lemma mem_right {e : ℕ × ℕ} (he : e ∈ (node hik hkj T₁ T₂).chords) (h : k ≤ e.1) :
    e ∈ T₂.chords := by
  simp only [chords, Finset.mem_insert, Finset.mem_union] at he
  rcases he with rfl | he | he
  · simp at h; omega
  · have := isChord_of_mem_chords T₁ e he; unfold IsChord at this; omega
  · exact he

lemma eq_root_of_mem {e : ℕ × ℕ} (he : e ∈ (node hik hkj T₁ T₂).chords) (h1 : e.1 < k)
    (h2 : k < e.2) : e = (i, j) := by
  simp only [chords, Finset.mem_insert, Finset.mem_union] at he
  rcases he with he | he | he
  · exact he
  · have := isChord_of_mem_chords T₁ e he; unfold IsChord at this; omega
  · have := isChord_of_mem_chords T₂ e he; unfold IsChord at this; omega

end faces

/-- Every triple of vertices whose three sides are chords of the triangulation is one of its
triangles (triangles are exactly the faces). -/
theorem mem_triangles_of_chords : {i j : ℕ} → (T : Triangulation i j) → ∀ a b c : ℕ,
    (a, b) ∈ T.chords → (b, c) ∈ T.chords → (a, c) ∈ T.chords → (a, b, c) ∈ T.triangles
  | _, _, edge i => by
    intro a b c h1 h2 _
    simp only [chords, Finset.mem_singleton, Prod.mk.injEq] at h1 h2
    omega
  | i, j, node (k := k) hik hkj T₁ T₂ => by
    intro a b c h1 h2 h3
    have c1 := isChord_of_mem_chords _ _ h1
    have c2 := isChord_of_mem_chords _ _ h2
    unfold IsChord at c1 c2
    simp only at c1 c2
    simp only [triangles, List.mem_cons, List.mem_append]
    by_cases hc : c ≤ k
    · exact Or.inr (Or.inl (mem_triangles_of_chords T₁ a b c (mem_left h1 (by simp; omega))
        (mem_left h2 (by simpa using hc)) (mem_left h3 (by simpa using hc))))
    by_cases ha : k ≤ a
    · exact Or.inr (Or.inr (mem_triangles_of_chords T₂ a b c (mem_right h1 (by simpa using ha))
        (mem_right h2 (by simp; omega)) (mem_right h3 (by simpa using ha))))
    have e3 := eq_root_of_mem h3 (by simp; omega) (by simp; omega)
    simp only [Prod.mk.injEq] at e3
    obtain ⟨rfl, rfl⟩ := e3
    refine Or.inl ?_
    rcases lt_trichotomy b k with hb | rfl | hb
    · have := eq_root_of_mem h2 (by simpa using hb) (by simp; omega)
      simp only [Prod.mk.injEq] at this; omega
    · rfl
    · have := eq_root_of_mem h1 (by simp; omega) (by simpa using hb)
      simp only [Prod.mk.injEq] at this; omega

theorem bounds_of_mem_triangles {i j : ℕ} (T : Triangulation i j) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ T.triangles) : i ≤ t.1 ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 ≤ j := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨h1, h2, -⟩ := chords_of_mem_triangles T a b c ht
  have c1 := isChord_of_mem_chords _ _ h1
  have c2 := isChord_of_mem_chords _ _ h2
  unfold IsChord at c1 c2
  simp only at c1 c2 ⊢
  omega

theorem nodup_triangles : {i j : ℕ} → (T : Triangulation i j) → T.triangles.Nodup
  | _, _, edge _ => by simp [triangles]
  | i, j, node (k := k) hik hkj T₁ T₂ => by
    simp only [triangles, List.nodup_cons, List.mem_append, List.nodup_append]
    refine ⟨?_, nodup_triangles T₁, nodup_triangles T₂, ?_⟩
    · rintro (h | h)
      · have := bounds_of_mem_triangles T₁ h; simp at this; omega
      · have := bounds_of_mem_triangles T₂ h; simp at this; omega
    · rintro t h₁ t' h₂ rfl
      have := bounds_of_mem_triangles T₁ h₁
      have := bounds_of_mem_triangles T₂ h₂
      omega

/-- The triangles of a tree triangulation are exactly the triangles read off from its chords. -/
theorem toFinset_triangles {i j : ℕ} (T : Triangulation i j) :
    T.triangles.toFinset = triangleSet T.chords := by
  ext ⟨a, b, c⟩
  rw [List.mem_toFinset, mem_triangleSet]
  exact ⟨chords_of_mem_triangles T a b c, fun ⟨h1, h2, h3⟩ => mem_triangles_of_chords T a b c h1 h2 h3⟩

theorem card_triangleSet {i j : ℕ} (T : Triangulation i j) :
    (triangleSet T.chords).card = j - i - 1 := by
  rw [← toFinset_triangles, List.toFinset_card_of_nodup (nodup_triangles T), length_triangles]

end Triangulation

namespace IsTriangulation

variable {i j : ℕ} {E : Finset (ℕ × ℕ)}

lemma root_mem (hE : IsTriangulation i j E) (hij : i < j) : (i, j) ∈ E :=
  hE.maximal _ ⟨le_rfl, hij, le_rfl⟩ fun f hf => not_crosses_root (hE.chord f hf)

lemma side_mem (hE : IsTriangulation i j E) {a : ℕ} (h1 : i ≤ a) (h2 : a + 1 ≤ j) :
    (a, a + 1) ∈ E :=
  hE.maximal _ ⟨h1, Nat.lt_succ_self a, h2⟩ fun f _ => by
    obtain ⟨c, d⟩ := f; simp only [Crosses]; omega

/-- The left part `E ∩ chords(i..k)` of a triangulation containing `(i,k)` is a triangulation. -/
lemma left (hE : IsTriangulation i j E) {k : ℕ} (hk : k ≤ j) (hik : (i, k) ∈ E) :
    IsTriangulation i k (E.filter fun e => e.2 ≤ k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rw [Finset.mem_filter] at he
    have := hE.chord e he.1
    unfold IsChord at *; omega
  · intro e he f hf
    exact hE.noncross e (Finset.mem_filter.1 he).1 f (Finset.mem_filter.1 hf).1
  · intro e he hnc
    rw [Finset.mem_filter]
    refine ⟨hE.maximal e (by unfold IsChord at *; omega) ?_, he.2.2⟩
    intro f hf hcr
    by_cases hfk : f.2 ≤ k
    · exact hnc f (Finset.mem_filter.2 ⟨hf, hfk⟩) hcr
    · have := hE.chord f hf
      refine hE.noncross _ hik f hf ?_
      obtain ⟨a, b⟩ := e; obtain ⟨c, d⟩ := f
      simp only [IsChord, Crosses] at *; omega

lemma right (hE : IsTriangulation i j E) {k : ℕ} (hk : i ≤ k) (hkj : (k, j) ∈ E) :
    IsTriangulation k j (E.filter fun e => k ≤ e.1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rw [Finset.mem_filter] at he
    have := hE.chord e he.1
    unfold IsChord at *; omega
  · intro e he f hf
    exact hE.noncross e (Finset.mem_filter.1 he).1 f (Finset.mem_filter.1 hf).1
  · intro e he hnc
    rw [Finset.mem_filter]
    refine ⟨hE.maximal e (by unfold IsChord at *; omega) ?_, he.1⟩
    intro f hf hcr
    by_cases hfk : k ≤ f.1
    · exact hnc f (Finset.mem_filter.2 ⟨hf, hfk⟩) hcr
    · have := hE.chord f hf
      refine hE.noncross _ hkj f hf ?_
      obtain ⟨a, b⟩ := e; obtain ⟨c, d⟩ := f
      simp only [IsChord, Crosses] at *; omega

/-- **The apex of the root side.** In a triangulation of `i..j` with `i + 1 < j`, the side `(i,j)`
lies in a triangle `(i, k, j)`: take `k` maximal with `(i,k) ∈ E`, `k < j`. -/
lemma exists_apex (hE : IsTriangulation i j E) (hij : i + 1 < j) :
    ∃ k, i < k ∧ k < j ∧ (i, k) ∈ E ∧ (k, j) ∈ E ∧
      ∀ e ∈ E, e ≠ (i, j) → e.2 ≤ k ∨ k ≤ e.1 := by
  classical
  set S := (E.filter fun e => e.1 = i ∧ e.2 < j).image Prod.snd with hS
  have hne : S.Nonempty := ⟨i + 1, Finset.mem_image.2 ⟨(i, i + 1),
    Finset.mem_filter.2 ⟨hE.side_mem le_rfl (by omega), rfl, by simp; omega⟩, rfl⟩⟩
  have hkS : S.max' hne ∈ S := S.max'_mem hne
  obtain ⟨⟨a, b⟩, hab, hbk⟩ := Finset.mem_image.1 hkS
  rw [Finset.mem_filter] at hab
  obtain ⟨habE, ha, hbj⟩ := hab
  simp only at hbk ha
  rw [ha] at habE
  have hmax : ∀ b', (i, b') ∈ E → b' < j → b' ≤ b := fun b' hb hbj' => by
    rw [hbk]
    exact S.le_max' b' (Finset.mem_image.2 ⟨(i, b'), Finset.mem_filter.2 ⟨hb, rfl, hbj'⟩, rfl⟩)
  have hck := hE.chord _ habE
  unfold IsChord at hck
  simp only at hck hbj
  have hkj : (b, j) ∈ E := by
    refine hE.maximal _ ⟨by omega, hbj, le_rfl⟩ ?_
    rintro ⟨c, d⟩ hf hcr
    have hcf := hE.chord _ hf
    unfold IsChord at hcf
    simp only [Crosses] at hcr hcf
    rcases hcr with h | h
    · omega
    · rcases Nat.eq_or_lt_of_le hcf.1 with hc | hc
      · subst hc
        have := hmax d hf (by omega)
        omega
      · exact hE.noncross _ habE _ hf (by simp only [Crosses]; omega)
  refine ⟨b, hck.2.1, hbj, habE, hkj, ?_⟩
  rintro ⟨c, d⟩ hf hne'
  have hcf := hE.chord _ hf
  unfold IsChord at hcf
  simp only at hcf ⊢
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  rcases Nat.eq_or_lt_of_le hcf.1 with hc | hc
  · subst hc
    rcases Nat.lt_or_ge d j with hd | hd
    · have := hmax d hf hd
      omega
    · exact hne' (by rw [show d = j by omega])
  · exact hE.noncross _ habE _ hf (by simp only [Crosses]; omega)

end IsTriangulation

/-- **Every combinatorial triangulation comes from a tree.** -/
theorem IsTriangulation.exists_tree : ∀ (n i j : ℕ) (E : Finset (ℕ × ℕ)), j - i = n → i < j →
    IsTriangulation i j E → ∃ T : Triangulation i j, T.chords = E := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i j E hn hij hE
  rcases Nat.lt_or_ge (i + 1) j with h | h
  · obtain ⟨k, hik, hkj, hEik, hEkj, hsplit⟩ := hE.exists_apex h
    obtain ⟨T₁, hT₁⟩ := ih (k - i) (by omega) i k _ rfl hik (hE.left hkj.le hEik)
    obtain ⟨T₂, hT₂⟩ := ih (j - k) (by omega) k j _ rfl hkj (hE.right hik.le hEkj)
    refine ⟨Triangulation.node hik hkj T₁ T₂, ?_⟩
    simp only [Triangulation.chords, hT₁, hT₂]
    ext e
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (rfl | h | h)
      · exact hE.root_mem hij
      · exact h.1
      · exact h.1
    · intro he
      by_cases hr : e = (i, j)
      · exact Or.inl hr
      · rcases hsplit e he hr with h' | h'
        · exact Or.inr (Or.inl ⟨he, h'⟩)
        · exact Or.inr (Or.inr ⟨he, h'⟩)
  · obtain rfl : j = i + 1 := by omega
    refine ⟨Triangulation.edge i, ?_⟩
    ext ⟨a, b⟩
    simp only [Triangulation.chords, Finset.mem_singleton]
    constructor
    · intro h; rw [h]; exact hE.side_mem le_rfl le_rfl
    · intro he
      have := hE.chord _ he
      unfold IsChord at this
      simp only at this
      rw [show a = i by omega, show b = i + 1 by omega]

/-- **Combinatorial triangulations = tree triangulations.** A finite set of chords of `i..j`
(`i < j`) is a maximal non-crossing set iff it is the chord set of a tree triangulation. -/
theorem isTriangulation_iff_exists_tree {i j : ℕ} (hij : i < j) (E : Finset (ℕ × ℕ)) :
    IsTriangulation i j E ↔ ∃ T : Triangulation i j, T.chords = E :=
  ⟨fun hE => IsTriangulation.exists_tree _ i j E rfl hij hE,
    fun ⟨T, hT⟩ => hT ▸ T.isTriangulation⟩

/-- The triangles read off from a combinatorial triangulation are those of a tree. -/
theorem IsTriangulation.exists_tree_triangles {i j : ℕ} {E : Finset (ℕ × ℕ)} (hij : i < j)
    (hE : IsTriangulation i j E) :
    ∃ T : Triangulation i j, T.chords = E ∧ T.triangles.toFinset = triangleSet E := by
  obtain ⟨T, rfl⟩ := IsTriangulation.exists_tree _ i j E rfl hij hE
  exact ⟨T, rfl, T.toFinset_triangles⟩

/-- A combinatorial triangulation of `i..j` has exactly `j - i - 1` triangles. -/
theorem IsTriangulation.card_triangleSet {i j : ℕ} {E : Finset (ℕ × ℕ)} (hij : i < j)
    (hE : IsTriangulation i j E) : (triangleSet E).card = j - i - 1 := by
  obtain ⟨T, rfl⟩ := IsTriangulation.exists_tree _ i j E rfl hij hE
  exact T.card_triangleSet

namespace Triangulation

theorem filter_left {i k j : ℕ} (hik : i < k) (hkj : k < j) (T₁ : Triangulation i k)
    (T₂ : Triangulation k j) : (node hik hkj T₁ T₂).chords.filter (fun e => e.2 ≤ k) = T₁.chords := by
  ext e
  rw [Finset.mem_filter]
  refine ⟨fun h => mem_left h.1 h.2, fun h => ⟨?_, ?_⟩⟩
  · simp [chords, h]
  · have := isChord_of_mem_chords T₁ e h; unfold IsChord at this; omega

theorem filter_right {i k j : ℕ} (hik : i < k) (hkj : k < j) (T₁ : Triangulation i k)
    (T₂ : Triangulation k j) : (node hik hkj T₁ T₂).chords.filter (fun e => k ≤ e.1) = T₂.chords := by
  ext e
  rw [Finset.mem_filter]
  refine ⟨fun h => mem_right h.1 h.2, fun h => ⟨?_, ?_⟩⟩
  · simp [chords, h]
  · have := isChord_of_mem_chords T₂ e h; unfold IsChord at this; omega

/-- A tree triangulation is determined by its chord set, so `Triangulation i j` is in bijection
with the combinatorial triangulations of `i..j`. -/
theorem chords_injective : {i j : ℕ} → (T T' : Triangulation i j) → T.chords = T'.chords → T = T'
  | _, _, edge _, edge _, _ => rfl
  | _, _, edge _, node hik hkj _ _, _ => absurd hkj (by omega)
  | _, _, node hik hkj _ _, edge _, _ => absurd hkj (by omega)
  | i, j, node (k := k) hik hkj T₁ T₂, node (k := k') hik' hkj' T₁' T₂', h => by
    have hk : k = k' := by
      have a1 : (i, k) ∈ (node hik' hkj' T₁' T₂').chords := by
        rw [← h]; simp [chords, mem_chords_root T₁]
      have a2 : (k, j) ∈ (node hik' hkj' T₁' T₂').chords := by
        rw [← h]; simp [chords, mem_chords_root T₂]
      have b1 : (i, k') ∈ (node hik' hkj' T₁' T₂').chords := by simp [chords, mem_chords_root T₁']
      have b2 : (k', j) ∈ (node hik' hkj' T₁' T₂').chords := by simp [chords, mem_chords_root T₂']
      rcases lt_trichotomy k k' with hlt | heq | hgt
      · exact absurd (by simp only [Crosses]; omega) (noncross _ _ a2 _ b1)
      · exact heq
      · exact absurd (by simp only [Crosses]; omega) (noncross _ _ a1 _ b2)
    subst hk
    have h1 : T₁ = T₁' := chords_injective T₁ T₁' (by
      rw [← filter_left hik hkj T₁ T₂, ← filter_left hik' hkj' T₁' T₂', h])
    have h2 : T₂ = T₂' := chords_injective T₂ T₂' (by
      rw [← filter_right hik hkj T₁ T₂, ← filter_right hik' hkj' T₁' T₂', h])
    subst h1 h2
    rfl

end Triangulation

/-- **Bijection** between tree triangulations of `i..j` and combinatorial triangulations
(maximal non-crossing chord sets) of `i..j`, for `i < j`. -/
noncomputable def treeEquiv {i j : ℕ} (hij : i < j) :
    Triangulation i j ≃ {E : Finset (ℕ × ℕ) // IsTriangulation i j E} :=
  Equiv.ofBijective (fun T => ⟨T.chords, T.isTriangulation⟩)
    ⟨fun T T' h => Triangulation.chords_injective T T' (congrArg Subtype.val h),
     fun E => (IsTriangulation.exists_tree _ i j E.1 rfl hij E.2).imp fun _ h => Subtype.ext h⟩

section Geometry

open EuclideanGeometry Module

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- Sum of inradii over a finite set of triangles. -/
noncomputable def triangleInradiusSum (p : ℕ → P) (S : Finset (ℕ × ℕ × ℕ)) : ℝ :=
  ∑ t ∈ S, triInradius (p t.1) (p t.2.1) (p t.2.2)

omit [Fact (finrank ℝ V = 2)] in
theorem inradiusSum_eq_triangleInradiusSum (p : ℕ → P) {i j : ℕ} (T : Triangulation i j) :
    inradiusSum p T = triangleInradiusSum p (triangleSet T.chords) := by
  rw [triangleInradiusSum, ← T.toFinset_triangles,
    List.sum_toFinset _ T.nodup_triangles, inradiusSum]

/-- **Japanese theorem, combinatorial form, explicit value.** For every combinatorial
triangulation `E` of the convex cyclic polygon `p 0, …, p (n-1)` (a maximal set of pairwise
non-crossing chords), the sum of the inradii of its triangles is `∑ d(side) - (n-2) R`. -/
theorem triangleInradiusSum_eq (s : Sphere P) (p : ℕ → P) (n : ℕ) (hn : 2 ≤ n)
    (hs : ∀ l < n, p l ∈ s)
    (hconv : ∀ a b c, a < b → b < c → c < n → 0 < o.areaForm (p b -ᵥ p a) (p c -ᵥ p a))
    {E : Finset (ℕ × ℕ)} (hE : IsTriangulation 0 (n - 1) E) :
    triangleInradiusSum p (triangleSet E) =
      chainDist o s.center p 0 (n - 1) + chordDist o s.center (p (n - 1)) (p 0) -
        ((n - 2 : ℕ) : ℝ) * s.radius := by
  obtain ⟨T, rfl⟩ := IsTriangulation.exists_tree _ 0 (n - 1) E rfl (by omega) hE
  rw [← inradiusSum_eq_triangleInradiusSum, inradiusSum_polygon o s p n hs hconv T]

/-- **Japanese theorem for convex cyclic polygons (combinatorial triangulations).** Any two
triangulations of a convex cyclic polygon by maximal sets of non-crossing diagonals have the same
sum of inradii over their triangles. -/
theorem japanese_polygon_combinatorial (s : Sphere P) (p : ℕ → P) (n : ℕ) (hn : 2 ≤ n)
    (hs : ∀ l < n, p l ∈ s)
    (hconv : ∀ a b c, a < b → b < c → c < n → 0 < o.areaForm (p b -ᵥ p a) (p c -ᵥ p a))
    {E E' : Finset (ℕ × ℕ)} (hE : IsTriangulation 0 (n - 1) E)
    (hE' : IsTriangulation 0 (n - 1) E') :
    triangleInradiusSum p (triangleSet E) = triangleInradiusSum p (triangleSet E') := by
  rw [triangleInradiusSum_eq o s p n hn hs hconv hE, triangleInradiusSum_eq o s p n hn hs hconv hE']

end Geometry

end Japanese
