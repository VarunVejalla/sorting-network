import AKS.Sort.Depth
import AKS.Sort.ZeroOne

def cx (p : ℕ × ℕ) (f : ℕ → Bool) (k : ℕ) : Bool :=
  if k = p.1 then f p.1 && f p.2 else if k = p.2 then f p.1 || f p.2 else f k

def execL (l : List (ℕ × ℕ)) (f : ℕ → Bool) : ℕ → Bool := l.foldl (fun g p ↦ cx p g) f

def toNet (N : ℕ) (l : List (ℕ × ℕ)) : ComparatorNetwork N :=
  ⟨l.flatMap fun p ↦ if h : p.1 < p.2 ∧ p.2 < N then
    [⟨⟨p.1, h.1.trans h.2⟩, ⟨p.2, h.2⟩, h.1⟩] else []⟩

def ext' {N : ℕ} (v : Fin N → Bool) (k : ℕ) : Bool := if h : k < N then v ⟨k, h⟩ else false

theorem ext_exec {N : ℕ} (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < p.2 ∧ p.2 < N)
    (v : Fin N → Bool) : ext' ((toNet N l).exec v) = execL l (ext' v) := by
  induction l generalizing v with
  | nil => rfl
  | cons p l ih =>
    have hp := hl p (by simp)
    have ih' := ih (fun q hq ↦ hl q (by simp [hq]))
    simp only [toNet, ComparatorNetwork.exec, List.flatMap_cons, dif_pos hp, List.cons_append,
      List.nil_append, List.foldl_cons] at ih' ⊢
    rw [ih']
    change execL l _ = execL l _
    congr 1
    funext k
    by_cases hk : k < N
    · simp [ext', cx, Comparator.apply, hk, Fin.ext_iff, show p.1 < N by omega, show p.2 < N by omega]
    · simp [ext', cx, hk, show k ≠ p.1 by omega, show k ≠ p.2 by omega]

theorem execL_append (l₁ l₂ : List (ℕ × ℕ)) (f : ℕ → Bool) :
    execL (l₁ ++ l₂) f = execL l₂ (execL l₁ f) := List.foldl_append ..

abbrev layer (off M : ℕ) : List (ℕ × ℕ) := (List.range M).map fun i ↦ (off + i, off + i + M)

theorem layer_exec (off M f k) : ∀ t, t ≤ M →
    execL ((List.range t).map fun i ↦ (off + i, off + i + M)) f k =
      if off ≤ k ∧ k < off + t then f k && f (k + M)
      else if off + M ≤ k ∧ k < off + M + t then f (k - M) || f k else f k := by
  intro t
  induction t generalizing k with
  | zero => intro _; rw [if_neg (by omega), if_neg (by omega)]; rfl
  | succ t ih =>
    intro ht
    rw [List.range_succ, List.map_append, execL_append]
    change cx _ (execL _ f) k = _
    simp only [cx, ih _ (by omega : t ≤ M)]
    split_ifs <;> first | omega | (simp_all; try omega)

theorem cross_exec (off M f k) : ∀ t, t ≤ M →
    execL ((List.range t).map fun i ↦ (off + i, off + 2 * M - 1 - i)) f k =
      if off ≤ k ∧ k < off + t then f k && f (2 * off + 2 * M - 1 - k)
      else if off + 2 * M ≤ k + t ∧ k < off + 2 * M then f (2 * off + 2 * M - 1 - k) || f k else f k := by
  intro t
  induction t generalizing k with
  | zero => intro _; rw [if_neg (by omega), if_neg (by omega)]; rfl
  | succ t ih =>
    intro ht
    rw [List.range_succ, List.map_append, execL_append]
    change cx _ (execL _ f) k = _
    simp only [cx, ih _ (by omega : t ≤ M)]
    split_ifs <;> first | omega | (congr 2 <;> omega) | (simp_all <;> omega)

def Win (lo hi : ℕ) (l : List (ℕ × ℕ)) : Prop := ∀ p ∈ l, lo ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < hi

theorem Win.out {lo hi l} (h : Win lo hi l) (f : ℕ → Bool) {k} (hk : k < lo ∨ hi ≤ k) :
    execL l f k = f k := by
  induction l generalizing f with
  | nil => rfl
  | cons p l ih =>
    have hp := h p (by simp)
    rw [execL, List.foldl_cons, ← execL, ih (fun q hq ↦ h q (by simp [hq]))]
    rw [cx, if_neg (by omega), if_neg (by omega)]

theorem Win.const {lo hi l} (h : Win lo hi l) (c : Bool) (f : ℕ → Bool)
    (hf : ∀ k, lo ≤ k → k < hi → f k = c) {k} (h1 : lo ≤ k) (h2 : k < hi) : execL l f k = c := by
  induction l generalizing f with
  | nil => exact hf k h1 h2
  | cons p l ih =>
    have hp := h p (by simp)
    refine ih (fun q hq ↦ h q (by simp [hq])) _ (fun j hj1 hj2 ↦ ?_)
    have e1 := hf p.1 (by omega) (by omega)
    have e2 := hf p.2 (by omega) (by omega)
    simp only [cx]; split_ifs <;> simp [e1, e2, hf j hj1 hj2]

def I (lo hi : ℕ) (f : ℕ → Bool) : Prop :=
  ∃ a c, ∀ k, lo ≤ k → k < hi → (f k = true ↔ a ≤ k ∧ k < c)

def Bit (lo hi : ℕ) (f : ℕ → Bool) : Prop := I lo hi f ∨ I lo hi fun k ↦ !f k

theorem union_bit (lo M a c : ℕ) :
    (∃ a' c', ∀ k, lo ≤ k → k < lo + M → (((a ≤ k ∧ k < c) ∨ (a ≤ k + M ∧ k + M < c)) ↔ (a' ≤ k ∧ k < c'))) ∨
    (∃ a' c', ∀ k, lo ≤ k → k < lo + M → (((a ≤ k ∧ k < c) ∨ (a ≤ k + M ∧ k + M < c)) ↔ ¬ (a' ≤ k ∧ k < c'))) := by
  by_cases h1 : c ≤ lo + M
  · exact .inl ⟨a, c, by intro k h1 h2; omega⟩
  by_cases h2 : lo + M ≤ a
  · exact .inl ⟨a - M, c - M, by intro k h1 h2; omega⟩
  by_cases h3 : a ≤ c - M
  · exact .inl ⟨lo, lo + M, by intro k h1 h2; omega⟩
  · exact .inr ⟨c - M, a, by intro k h1 h2; omega⟩

theorem and_bit {lo M f} (h : Bit lo (lo + 2 * M) f) : Bit lo (lo + M) fun k ↦ f k && f (k + M) := by
  rcases h with ⟨a, c, h⟩ | ⟨a, c, h⟩
  · refine Or.inl ⟨a, c - M, fun k h1 h2 ↦ ?_⟩
    have e1 := h k h1 (by omega); have e2 := h (k + M) (by omega) (by omega)
    cases hk : f k <;> cases hl : f (k + M) <;> simp [hk, hl] at e1 e2 ⊢ <;> omega
  · rcases union_bit lo M a c with ⟨a', c', h'⟩ | ⟨a', c', h'⟩
    · refine Or.inr ⟨a', c', fun k h1 h2 ↦ ?_⟩
      have e1 := h k h1 (by omega); have e2 := h (k + M) (by omega) (by omega); have e3 := h' k h1 h2
      cases hk : f k <;> cases hl : f (k + M) <;> simp [hk, hl] at e1 e2 e3 ⊢ <;> omega
    · refine Or.inl ⟨a', c', fun k h1 h2 ↦ ?_⟩
      have e1 := h k h1 (by omega); have e2 := h (k + M) (by omega) (by omega); have e3 := h' k h1 h2
      cases hk : f k <;> cases hl : f (k + M) <;> simp [hk, hl] at e1 e2 e3 ⊢ <;> omega

theorem bit_not {lo hi f} : Bit lo hi (fun k ↦ !f k) ↔ Bit lo hi f := by
  simp [Bit, or_comm]

theorem or_bit {lo M f} (h : Bit lo (lo + 2 * M) f) : Bit lo (lo + M) fun k ↦ f k || f (k + M) := by
  simpa using bit_not.2 (and_bit (f := fun k ↦ !f k) (bit_not.2 h))

abbrev LR (lo M : ℕ) (f : ℕ → Bool) : Prop :=
  (∀ k, lo ≤ k → k < lo + M → (f k && f (k + M)) = false) ∨
  (∀ k, lo ≤ k → k < lo + M → (f k || f (k + M)) = true)

theorem lr_I {lo M f} (h : I lo (lo + 2 * M) f) : LR lo M f := by
  obtain ⟨a, c, h⟩ := h
  by_cases hb : ∃ k, lo ≤ k ∧ k < lo + M ∧ a ≤ k ∧ k + M < c
  · obtain ⟨k0, hb⟩ := hb
    refine Or.inr fun k h1 h2 ↦ ?_
    have e1 := h k h1 (by omega); have e2 := h (k + M) (by omega) (by omega)
    cases hk : f k <;> cases hl : f (k + M) <;> simp [hk, hl] at e1 e2 ⊢ <;> omega
  · push_neg at hb
    refine Or.inl fun k h1 h2 ↦ ?_
    have e1 := h k h1 (by omega); have e2 := h (k + M) (by omega) (by omega)
    have := hb k h1 h2
    cases hk : f k <;> cases hl : f (k + M) <;> simp [hk, hl] at e1 e2 ⊢ <;> omega

theorem lr_bit {lo M f} (h : Bit lo (lo + 2 * M) f) : LR lo M f := by
  rcases h with h | h
  · exact lr_I h
  · rcases lr_I (f := fun k ↦ !f k) h with h' | h'
    · exact Or.inr fun k h1 h2 ↦ by have := h' k h1 h2; dsimp only at this; revert this; cases f k <;> cases f (k + M) <;> simp
    · exact Or.inl fun k h1 h2 ↦ by have := h' k h1 h2; dsimp only at this; revert this; cases f k <;> cases f (k + M) <;> simp


def mergeL : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | k + 1, off => layer off (2 ^ k) ++ (mergeL k off ++ mergeL k (off + 2 ^ k))

theorem mergeL_win : ∀ k off, Win off (off + 2 ^ k) (mergeL k off)
  | 0, off => by simp [mergeL, Win]
  | k + 1, off => by
    have h1 := mergeL_win k off
    have h2 := mergeL_win k (off + 2 ^ k)
    simp only [mergeL, Win, List.mem_append, List.mem_map, List.mem_range, layer, pow_succ] at *
    rintro p (⟨i, hi, rfl⟩ | hp | hp)
    · simp; omega
    · have := h1 p hp; omega
    · have := h2 p hp; omega
theorem bit_congr {lo hi f g} (h : ∀ k, lo ≤ k → k < hi → f k = g k) (hf : Bit lo hi f) :
    Bit lo hi g := by
  rcases hf with ⟨a, c, hf⟩ | ⟨a, c, hf⟩
  · exact Or.inl ⟨a, c, fun k h1 h2 ↦ by rw [← h k h1 h2]; exact hf k h1 h2⟩
  · exact Or.inr ⟨a, c, fun k h1 h2 ↦ by dsimp only; rw [← h k h1 h2]; exact hf k h1 h2⟩

theorem bit_shift {lo hi M f} (hf : Bit lo hi f) :
    Bit (lo + M) (hi + M) fun j ↦ f (j - M) := by
  rcases hf with ⟨a, c, hf⟩ | ⟨a, c, hf⟩
  · exact Or.inl ⟨a + M, c + M, fun k h1 h2 ↦ by
      dsimp only; rw [hf (k - M) (by omega) (by omega)]; omega⟩
  · exact Or.inr ⟨a + M, c + M, fun k h1 h2 ↦ by
      have := hf (k - M) (by omega) (by omega); dsimp only at this ⊢; rw [this]; omega⟩

def Srt (lo hi : ℕ) (f : ℕ → Bool) : Prop := ∃ t, ∀ k, lo ≤ k → k < hi → (f k = true ↔ t ≤ k)

/-- Merging both halves of `w` (each bitonic, left ≤ right) sorts the window. -/
theorem finish (k off : ℕ)
    (ih : ∀ off f, Bit off (off + 2 ^ k) f → Srt off (off + 2 ^ k) (execL (mergeL k off) f))
    (w : ℕ → Bool) (hl : Bit off (off + 2 ^ k) w) (hr : Bit (off + 2 ^ k) (off + 2 ^ k + 2 ^ k) w)
    (hlr : (∀ j, off ≤ j → j < off + 2 ^ k → w j = false) ∨
      (∀ j, off + 2 ^ k ≤ j → j < off + 2 ^ k + 2 ^ k → w j = true)) :
    Srt off (off + 2 ^ k + 2 ^ k) (execL (mergeL k off ++ mergeL k (off + 2 ^ k)) w) := by
  rw [execL_append]
  set u := execL (mergeL k off) w with hu
  have hw1 := mergeL_win k off
  have hw2 := mergeL_win k (off + 2 ^ k)
  have hur : ∀ j, off + 2 ^ k ≤ j → u j = w j := fun j hj ↦ hw1.out w (Or.inr (by omega))
  obtain ⟨t₁, h₁⟩ := ih off w hl
  obtain ⟨t₂, h₂⟩ := ih (off + 2 ^ k) u (bit_congr (fun j hj _ ↦ (hur j hj).symm) hr)
  rcases hlr with h | h
  · refine ⟨max t₂ (off + 2 ^ k), fun j hj1 hj2 ↦ ?_⟩
    by_cases hj : j < off + 2 ^ k
    · rw [hw2.out _ (Or.inl hj), hu, hw1.const false w h hj1 hj]; simp; omega
    · rw [h₂ j (by omega) hj2]; omega
  · refine ⟨min t₁ (off + 2 ^ k), fun j hj1 hj2 ↦ ?_⟩
    by_cases hj : j < off + 2 ^ k
    · rw [hw2.out _ (Or.inl hj), h₁ j hj1 hj]; omega
    · rw [hw2.const true u (fun j hj _ ↦ (hur j hj).trans (h j hj (by omega))) (by omega) hj2]
      simp; omega

theorem merge_srt : ∀ k off f, Bit off (off + 2 ^ k) f → Srt off (off + 2 ^ k) (execL (mergeL k off) f)
  | 0, off, f, _ => ⟨if f off then off else off + 1, fun j h1 h2 ↦ by
      obtain rfl : j = off := by simp at h2; omega
      by_cases h : f j = true <;> simp [h, mergeL, execL]⟩
  | k + 1, off, f, hb => by
    rw [pow_succ'] at hb ⊢
    have hL (k' : ℕ) (h1 : off ≤ k') (h2 : k' < off + 2 ^ k) : execL (layer off (2 ^ k)) f k' = (f k' && f (k' + 2 ^ k)) := by
      rw [layer_exec off _ f k' _ le_rfl, if_pos ⟨h1, h2⟩]
    have hR (k' : ℕ) (h1 : off + 2 ^ k ≤ k') (h2 : k' < off + 2 ^ k + 2 ^ k) : execL (layer off (2 ^ k)) f k' = (f (k' - 2 ^ k) || f (k' - 2 ^ k + 2 ^ k)) := by
      rw [layer_exec off _ f k' _ le_rfl, if_neg (by omega), if_pos ⟨by omega, by omega⟩,
        Nat.sub_add_cancel (by omega)]
    rw [mergeL, execL_append, show off + 2 * 2 ^ k = off + 2 ^ k + 2 ^ k by omega]
    refine finish k off (merge_srt k) _
      (bit_congr (fun j h1 h2 ↦ (hL j h1 h2).symm) (and_bit hb))
      (bit_congr (fun j h1 h2 ↦ (hR j (by omega) h2).symm) (bit_shift (or_bit hb))) ?_
    rcases lr_bit hb with h | h
    · exact Or.inl fun j h1 h2 ↦ by rw [hL j h1 h2]; exact h j h1 h2
    · exact Or.inr fun j h1 h2 ↦ by
        rw [hR j h1 (by omega)]; simpa using h (j - 2 ^ k) (by omega) (by omega)

abbrev cross (off M : ℕ) : List (ℕ × ℕ) := (List.range M).map fun i ↦ (off + i, off + 2 * M - 1 - i)

def sortL : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | k + 1, off => (sortL k off ++ sortL k (off + 2 ^ k)) ++
      (cross off (2 ^ k) ++ (mergeL k off ++ mergeL k (off + 2 ^ k)))

theorem sortL_win : ∀ k off, Win off (off + 2 ^ k) (sortL k off)
  | 0, off => by simp [sortL, Win]
  | k + 1, off => by
    have h1 := sortL_win k off
    have h2 := sortL_win k (off + 2 ^ k)
    have h3 := mergeL_win k off
    have h4 := mergeL_win k (off + 2 ^ k)
    simp only [sortL, Win, List.mem_append, List.mem_map, List.mem_range, cross, pow_succ] at *
    rintro p ((hp | hp) | ⟨i, hi, rfl⟩ | hp | hp)
    · have := h1 p hp; omega
    · have := h2 p hp; omega
    · simp; omega
    · have := h3 p hp; omega
    · have := h4 p hp; omega

theorem sort_srt : ∀ k off f, Srt off (off + 2 ^ k) (execL (sortL k off) f)
  | 0, off, f => ⟨if f off then off else off + 1, fun j h1 h2 ↦ by
      obtain rfl : j = off := by simp at h2; omega
      by_cases h : f j = true <;> simp [h, sortL, execL]⟩
  | k + 1, off, f => by
    obtain ⟨t₁, h₁⟩ := sort_srt k off f
    obtain ⟨t₂, h₂⟩ := sort_srt k (off + 2 ^ k) (execL (sortL k off) f)
    set u := execL (sortL k (off + 2 ^ k)) (execL (sortL k off) f) with hu
    have hl : ∀ j, off ≤ j → j < off + 2 ^ k → (u j = true ↔ t₁ ≤ j) := fun j h1 h2 ↦ by
      rw [hu, (sortL_win k (off + 2 ^ k)).out _ (Or.inl h2)]; exact h₁ j h1 h2
    have hc (j : ℕ) (h1 : off ≤ j) (h2 : j < off + 2 ^ k) :
        execL (cross off (2 ^ k)) u j = (u j && u (2 * off + 2 * 2 ^ k - 1 - j)) := by
      rw [cross_exec off _ u j _ le_rfl, if_pos ⟨h1, h2⟩]
    have hc' (j : ℕ) (h1 : off + 2 ^ k ≤ j) (h2 : j < off + 2 ^ k + 2 ^ k) :
        execL (cross off (2 ^ k)) u j = (u (2 * off + 2 * 2 ^ k - 1 - j) || u j) := by
      rw [cross_exec off _ u j _ le_rfl, if_neg (by omega), if_pos ⟨by omega, by omega⟩]
    rw [pow_succ', sortL, execL_append, execL_append, execL_append (sortL k off),
      show off + 2 * 2 ^ k = off + 2 ^ k + 2 ^ k by omega]
    refine finish k off (merge_srt k) _ ?_ ?_ ?_
    · refine Or.inl ⟨t₁, 2 * off + 2 * 2 ^ k - t₂, fun j h1 h2 ↦ ?_⟩
      rw [hc j h1 h2, Bool.and_eq_true, hl j h1 h2, h₂ (2 * off + 2 * 2 ^ k - 1 - j) (by omega) (by omega)]
      omega
    · refine Or.inr ⟨2 * off + 2 * 2 ^ k - t₁, t₂, fun j h1 h2 ↦ ?_⟩
      dsimp only
      rw [hc' j h1 h2, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.eq_false_iff, Bool.eq_false_iff,
        ne_eq, ne_eq, hl (2 * off + 2 * 2 ^ k - 1 - j) (by omega) (by omega), h₂ j h1 h2]
      omega
    · by_cases hb : ∃ j, off ≤ j ∧ j < off + 2 ^ k ∧ t₁ ≤ j ∧ j + t₂ < 2 * off + 2 * 2 ^ k
      · obtain ⟨j₀, hb⟩ := hb
        refine Or.inr fun j h1 h2 ↦ ?_
        rw [hc' j h1 h2, Bool.or_eq_true, hl (2 * off + 2 * 2 ^ k - 1 - j) (by omega) (by omega), h₂ j h1 h2]
        omega
      · push_neg at hb
        refine Or.inl fun j h1 h2 ↦ ?_
        have := hb j h1 h2
        rw [hc j h1 h2, Bool.and_eq_false_iff, Bool.eq_false_iff, Bool.eq_false_iff, ne_eq, ne_eq, hl j h1 h2,
          h₂ (2 * off + 2 * 2 ^ k - 1 - j) (by omega) (by omega)]
        omega

theorem toNet_mem {N l} {c : Comparator N} (hc : c ∈ (toNet N l).comparators) :
    ∃ p ∈ l, c.i.val = p.1 ∧ c.j.val = p.2 := by
  simp only [toNet, List.mem_flatMap] at hc
  obtain ⟨p, hp, hc⟩ := hc
  split_ifs at hc
  · obtain rfl := List.mem_singleton.1 hc; exact ⟨p, hp, rfl, rfl⟩
  · simp at hc

theorem toNet_disj {N a b c} {l₁ l₂ : List (ℕ × ℕ)} (h₁ : Win a b l₁) (h₂ : Win b c l₂) :
    ∀ c₁ ∈ (toNet N l₁).comparators, ∀ c₂ ∈ (toNet N l₂).comparators,
      (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j) := by
  intro c₁ hc₁ c₂ hc₂
  obtain ⟨p, hp, hp1, hp2⟩ := toNet_mem hc₁
  obtain ⟨q, hq, hq1, hq2⟩ := toNet_mem hc₂
  have := h₁ p hp; have := h₂ q hq
  refine ⟨⟨fun h ↦ ?_, fun h ↦ ?_⟩, fun h ↦ ?_, fun h ↦ ?_⟩ <;> 
    · have := congrArg Fin.val h; omega

theorem depth_par {n} (A B : List (Comparator n)) (d : ℕ) (hA : (⟨A⟩ : ComparatorNetwork n).depth ≤ d)
    (hB : (⟨B⟩ : ComparatorNetwork n).depth ≤ d)
    (h : ∀ c₁ ∈ A, ∀ c₂ ∈ B, (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j)) :
    (⟨A ++ B⟩ : ComparatorNetwork n).depth ≤ d := by
  simpa using depth_flatMap_disjoint [A, B] id d (by simp [hA, hB]) (List.pairwise_pair.2 h)

theorem depth_layer {N} (l : List (ℕ × ℕ))
    (hl : l.Pairwise fun p q ↦ p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) :
    (toNet N l).depth ≤ 1 := by
  refine depth_flatMap_disjoint l _ 1 (fun p _ ↦ ?_) (hl.imp fun {p q} hpq c₁ hc₁ c₂ hc₂ ↦ ?_)
  · split_ifs <;> simp [ComparatorNetwork.depth, depthStep]
  · split_ifs at hc₁ hc₂ <;> simp_all [Fin.ext_iff]

theorem toNet_append (N l₁ l₂) : toNet N (l₁ ++ l₂) =
    ⟨(toNet N l₁).comparators ++ (toNet N l₂).comparators⟩ := by
  simp [toNet, List.flatMap_append]

theorem merge_depth : ∀ k off N, (toNet N (mergeL k off)).depth ≤ k
  | 0, _, _ => by simp [mergeL, toNet, ComparatorNetwork.depth]
  | k + 1, off, N => by
    have h1 : (toNet N (layer off (2 ^ k))).depth ≤ 1 := depth_layer _ <| by
      simp only [layer, List.pairwise_map]
      exact List.pairwise_lt_range.imp_of_mem fun {a b} ha hb hab ↦ by
        simp at ha hb; omega
    have h2 := depth_par (toNet N (mergeL k off)).comparators
      (toNet N (mergeL k (off + 2 ^ k))).comparators k (merge_depth k off N)
      (merge_depth k _ N) (toNet_disj (mergeL_win k off) (mergeL_win k _))
    rw [mergeL, toNet_append, toNet_append]
    exact (depth_append _ _).trans ((Nat.add_le_add h1 h2).trans (by omega))

def bitonicDepthBudget : ℕ → ℕ
  | 0 => 0
  | k + 1 => bitonicDepthBudget k + (k + 1)

theorem bitonicDepthBudget_double (k : ℕ) : 2 * bitonicDepthBudget k = k * (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [bitonicDepthBudget]; nlinarith

theorem bitonicDepthBudget_eq (k : ℕ) : bitonicDepthBudget k = k * (k + 1) / 2 := by
  have := bitonicDepthBudget_double k; omega

theorem bitonicDepthBudget_mono : Monotone bitonicDepthBudget :=
  monotone_nat_of_le_succ fun k ↦ by simp [bitonicDepthBudget]

theorem sort_depth : ∀ k off N, (toNet N (sortL k off)).depth ≤ bitonicDepthBudget k
  | 0, _, _ => by simp [sortL, toNet, ComparatorNetwork.depth]
  | k + 1, off, N => by
    have h1 : (toNet N (cross off (2 ^ k))).depth ≤ 1 := depth_layer _ <| by
      simp only [cross, List.pairwise_map]
      exact List.pairwise_lt_range.imp_of_mem fun {a b} ha hb hab ↦ by
        simp at ha hb; omega
    have h2 := depth_par (toNet N (sortL k off)).comparators
      (toNet N (sortL k (off + 2 ^ k))).comparators _ (sort_depth k off N)
      (sort_depth k _ N) (toNet_disj (sortL_win k off) (sortL_win k _))
    have h3 := depth_par (toNet N (mergeL k off)).comparators
      (toNet N (mergeL k (off + 2 ^ k))).comparators k (merge_depth k off N)
      (merge_depth k _ N) (toNet_disj (mergeL_win k off) (mergeL_win k _))
    have h4 := depth_append (toNet N (cross off (2 ^ k))) ⟨(toNet N (mergeL k off)).comparators ++
      (toNet N (mergeL k (off + 2 ^ k))).comparators⟩
    dsimp only at h4
    rw [sortL, toNet_append, toNet_append, toNet_append, toNet_append]
    refine (depth_append _ _).trans ?_
    simp only [bitonicDepthBudget] 
    omega

def bitonicSort (k : ℕ) : ComparatorNetwork (2 ^ k) := toNet (2 ^ k) (sortL k 0)

theorem bitonicSort_sorts (k : ℕ) : (bitonicSort k).Sorts := zero_one_principle _ fun v i j hij ↦ by
  have hw := sortL_win k 0
  have e (i : Fin (2 ^ k)) : (bitonicSort k).exec v i = execL (sortL k 0) (ext' v) i := by
    have := congrFun (ext_exec (sortL k 0) (fun p hp ↦ ⟨(hw p hp).2.1, by simpa using (hw p hp).2.2⟩) v) i
    simpa [ext'] using this
  obtain ⟨t, ht⟩ := sort_srt k 0 (ext' v)
  rw [e, e]
  exact Bool.le_iff_imp.2 fun hi ↦ (ht j (by omega) (by simpa using j.2)).2
    (le_trans ((ht i (by omega) (by simpa using i.2)).1 hi) hij)
