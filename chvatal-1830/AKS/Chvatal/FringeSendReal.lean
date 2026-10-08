module
/-
  # Fringe send bound for the real network (task H2)

  Source: V. Chvátal, *Lecture Notes on the New AKS Sorting Network*, Rutgers DCS-TR-294 (1992),
  Lemma 4.4 (parent part).  The keys a node `q` sends down to child `b` are outputs of the node
  network on a middle window of cells (`mem_image_downSet_iff`); those outside the address
  interval of `q.ancestor (r-1)` are counted by Property F (`sent_outside_le`) against the
  order-`r` outsiders of `q`.

  Main result: `fringe_send_real`.
-/

public import AKS.Chvatal.NodeKeys
public import AKS.Chvatal.StrangerBounds

@[expose] public section

namespace Chvatal

open Finset

/-! ## Tree facts -/

theorem child_ancestor_eq {d : ℕ} (q : KBag 64 d) (j : ℕ) (hj : j < 64) (hq : q.l < d)
    (r : ℕ) (hr : 1 ≤ r) :
    (q.child j hj hq).ancestor r (by omega) = q.ancestor (r - 1) (by omega) := by
  ext
  · show q.l + 1 - r = q.l - (r - 1); omega
  · show (64 * q.x + j) / 64 ^ r = q.x / 64 ^ (r - 1)
    have h64 : 64 ^ r = 64 * 64 ^ (r - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h64, ← Nat.div_div_eq_div_mul]
    congr 1
    rw [Nat.mul_add_div (by norm_num)]
    rw [Nat.div_eq_of_lt hj]; simp

theorem native_id_iff {d : ℕ} (A : KBag 64 d) (κ : Fin (64 ^ d)) :
    A.Native κ id ↔ A.lo ≤ (κ : ℕ) ∧ (κ : ℕ) < A.hi := by
  have hs : 0 < bagSize 64 d A.l := bagSize_pos (by norm_num) A.hl
  unfold KBag.Native nativeBagIdx KBag.lo KBag.hi KBag.size
  simp only [id]
  have h1 : A.x ≤ (κ : ℕ) / bagSize 64 d A.l ↔ A.x * bagSize 64 d A.l ≤ (κ : ℕ) :=
    Nat.le_div_iff_mul_le hs
  have h2 : (κ : ℕ) / bagSize 64 d A.l < A.x + 1 ↔ (κ : ℕ) < (A.x + 1) * bagSize 64 d A.l :=
    Nat.div_lt_iff_lt_mul hs
  constructor
  · intro h; exact ⟨h1.1 (le_of_eq h.symm), h2.1 (by omega)⟩
  · rintro ⟨a, b⟩; have := h1.2 a; have := h2.2 b; omega

theorem lo_le_hi {d : ℕ} (A : KBag 64 d) : A.lo ≤ A.hi := by
  unfold KBag.lo KBag.hi
  exact Nat.mul_le_mul_right _ (Nat.le_succ _)

theorem strangers_eq_filter {d : ℕ} (q : KBag 64 d) (r : ℕ) (hr : 1 ≤ r)
    (S : Finset (Fin (64 ^ d))) :
    q.strangers r id S = (S.filter fun κ : Fin (64 ^ d) =>
      ¬ ((q.ancestor (r - 1)).lo ≤ (κ : ℕ) ∧ (κ : ℕ) < (q.ancestor (r - 1)).hi)).card := by
  unfold KBag.strangers
  congr 1
  apply Finset.filter_congr
  intro κ _
  unfold KBag.Strange
  rw [native_id_iff]
  constructor
  · rintro (h | h); · omega
    · exact h
  · intro h; exact Or.inr h

theorem strangers_split {N : ℕ} (K : Finset (Fin N)) (Ilo Ihi : ℕ) (h : Ilo ≤ Ihi) :
    (K.filter fun κ : Fin N => ¬ (Ilo ≤ (κ : ℕ) ∧ (κ : ℕ) < Ihi)).card =
      (K.filter fun κ : Fin N => Ihi ≤ (κ : ℕ)).card +
        (K.filter fun κ : Fin N => (κ : ℕ) < Ilo).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext κ
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hk, hn⟩
      by_cases h1 : Ihi ≤ (κ : ℕ)
      · exact Or.inl ⟨hk, h1⟩
      · exact Or.inr ⟨hk, by omega⟩
    · rintro (⟨hk, h1⟩ | ⟨hk, h1⟩)
      · exact ⟨hk, by omega⟩
      · exact ⟨hk, by omega⟩
  · rw [Finset.disjoint_left]
    intro κ h1 h2
    simp only [Finset.mem_filter] at h1 h2
    omega

/-! ## Cells and keys -/

/-- The cell carrying key `κ` (junk `0` if none). -/
noncomputable def cellOf {a N : ℕ} (y : Fin a → Fin N) (κ : Fin N) : ℕ :=
  by classical exact if h : ∃ c, y c = κ then (Classical.choose h).val else 0

theorem cellOf_apply {a N : ℕ} {y : Fin a → Fin N} (hy : Function.Injective y) (c : Fin a) :
    cellOf y (y c) = c.val := by
  classical
  have h : ∃ c', y c' = y c := ⟨c, rfl⟩
  unfold cellOf
  rw [dif_pos h]
  have := hy (Classical.choose_spec h)
  rw [this]

theorem filter_image_cellOf {a N : ℕ} {y : Fin a → Fin N} (hy : Function.Injective y)
    (P : Fin N → ℕ → Prop) [DecidablePred fun κ => ∃ c, y c = κ ∧ P κ (cellOf y κ)]
    [∀ κ n, Decidable (P κ n)] :
    ((Finset.univ.image y).filter fun κ => P κ (cellOf y κ)).card =
      (Finset.univ.filter fun c : Fin a => P (y c) c.val).card := by
  classical
  have : (Finset.univ.image y).filter (fun κ => P κ (cellOf y κ)) =
      (Finset.univ.filter fun c : Fin a => P (y c) c.val).image y := by
    ext κ
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨c, rfl⟩, hP⟩
      exact ⟨c, by rwa [cellOf_apply hy] at hP, rfl⟩
    · rintro ⟨c, hP, rfl⟩
      exact ⟨⟨c, rfl⟩, by rwa [cellOf_apply hy]⟩
  rw [this, Finset.card_image_of_injective _ hy]


/-! ## Lemma 4.4, parent part, for the real network -/

section Real

variable {d tf : ℕ}

theorem parent_child_eq (q : KBag 64 d) (j : ℕ) (hj : j < 64) (hq : q.l < d) :
    (q.child j hj hq).parent (by omega) = q := by
  ext
  · show q.l + 1 - 1 = q.l; omega
  · show (64 * q.x + j) / 64 = q.x
    rw [Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hj]; simp

/-- **Lemma 4.4 (parent part), real network.**  The order-`(r+1)` outsiders among the keys
sent from `q` to its child `b = q.child j` at stage `t` number at most `εF` times the order-`r`
outsiders among the keys on `q`, given the node specification (Property F) and
`strangers ≤ Jmax`. -/
theorem fringe_send_real (F : FlowSizes d tf)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht : t < tf) (q : KBag 64 d) (hq : q.l < d)
    (j : Fin 64) (r : ℕ) (hr : 1 ≤ r) (EB : ℝ) (Jmax : ℕ) (εF : ℝ)
    (ha : (wireSets F t q).card = F.up q.l t + 64 * F.down q.l t)
    (hspec : NodeSpec (wireSets F t q).card (F.up q.l t) (F.down q.l t)
      (nets t q (wireSets F t q).card) EB Jmax εF)
    (hJ : q.strangers r id ((execPlacement F nets v t ht.le).regs q) ≤ Jmax) :
    (((q.child j.val j.isLt hq).strangers (r + 1) id (fromParentK F nets v t
        (q.child j.val j.isLt hq)) : ℕ) : ℝ) ≤
      εF * ((q.strangers r id ((execPlacement F nets v t ht.le).regs q) : ℕ) : ℝ) := by
  classical
  set s := wireSets F t q with hs
  set π := F.up q.l t
  set τ := F.down q.l t
  set xr : Fin s.card → Fin (64 ^ d) :=
    fun i => X F nets v t (s.orderEmbOfFin rfl i) with hxrdef
  have hxr : Function.Injective xr := fun i i' h =>
    (s.orderEmbOfFin rfl).injective (X_injective F nets v t h)
  set y := (nets t q s.card).exec xr with hydef
  have hyinj : Function.Injective y := exec_keySet_injective hxr _
  have hK : (execPlacement F nets v t ht.le).regs q = keySet xr := by
    show s.image (X F nets v t) = _
    ext κ
    simp only [Finset.mem_image, keySet, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨c, rfl⟩ := exists_orderEmb_eq hw
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨_, Finset.orderEmbOfFin_mem _ rfl _, rfl⟩
  have hKy : keySet xr = Finset.univ.image y := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro κ hκ
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hκ
      exact exec_mem_keySet _ c
    · rw [card_keySet hxr, Finset.card_image_of_injective _ hyinj]; simp
  have hcard : (keySet xr).card = s.card := card_keySet hxr
  have hfilt : ∀ (Q : Fin (64 ^ d) → Prop) [DecidablePred Q],
      (keySet xr).filter Q = (Finset.univ.image y).filter Q := fun Q _ => by rw [hKy]
  rw [hK] at hJ ⊢
  set b := q.child j.val j.isLt hq with hb
  set A := q.ancestor (r - 1) with hA
  -- the sent keys
  have hfp : fromParentK F nets v t b = (downSet s π τ j.val).image (X F nets v (t + 1)) := by
    unfold fromParentK
    have hp : b.parent (by omega) = q := parent_child_eq q j.val j.isLt hq
    have hl : b.l - 1 = q.l := by show q.l + 1 - 1 = q.l; omega
    have hx : b.x % 64 = j.val := by
      show (64 * q.x + j.val) % 64 = j.val
      rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt j.isLt
    rw [hp, hl, hx]
  -- strangers of b
  have hbA : b.ancestor (r + 1 - 1) (by omega) = A := by
    rw [Nat.add_sub_cancel]; exact child_ancestor_eq q j.val j.isLt hq r hr |>.trans (by rw [hA])
  have hbs := strangers_eq_filter b (r + 1) (by omega) (fromParentK F nets v t b)
  rw [hbA] at hbs
  have hqs := strangers_eq_filter q r hr (keySet xr)
  have hsplit := strangers_split (keySet xr) A.lo A.hi (lo_le_hi A)
  -- positions
  set pos := cellOf y with hpos
  have hsub : (fromParentK F nets v t b).filter
        (fun κ : Fin (64 ^ d) => ¬ (A.lo ≤ (κ : ℕ) ∧ (κ : ℕ) < A.hi)) ⊆
      (((keySet xr).filter fun κ : Fin (64 ^ d) =>
          π / 2 ≤ pos κ ∧ pos κ < (keySet xr).card - π / 2).filter
        fun κ : Fin (64 ^ d) => ¬ (A.lo ≤ (κ : ℕ) ∧ (κ : ℕ) < A.hi)) := by
    intro κ hκ
    simp only [Finset.mem_filter] at hκ ⊢
    obtain ⟨hκS, hn⟩ := hκ
    rw [hfp, mem_image_downSet_iff F nets v t ht q π τ j.val κ] at hκS
    obtain ⟨c, h1, h2, rfl⟩ := hκS
    have hpc : pos (y c) = c.val := cellOf_apply hyinj c
    refine ⟨⟨exec_mem_keySet _ c, ?_, ?_⟩, hn⟩
    · rw [hpc]; omega
    · rw [hpc, hcard]
      have : (j.val + 1) * τ ≤ 64 * τ := Nat.mul_le_mul_right _ (by have := j.isLt; omega)
      omega
  have hle : (b.strangers (r + 1) id (fromParentK F nets v t b) : ℕ) ≤
      (((keySet xr).filter fun κ : Fin (64 ^ d) =>
          π / 2 ≤ pos κ ∧ pos κ < (keySet xr).card - π / 2).filter
        fun κ : Fin (64 ^ d) => ¬ (A.lo ≤ (κ : ℕ) ∧ (κ : ℕ) < A.hi)).card := by
    rw [hbs]; exact Finset.card_le_card hsub
  have hHhi : ((keySet xr).filter fun κ : Fin (64 ^ d) => A.hi ≤ (κ : ℕ)).card ≤ Jmax := by
    rw [hqs, hsplit] at hJ; omega
  have hHlo : ((keySet xr).filter fun κ : Fin (64 ^ d) => (κ : ℕ) < A.lo).card ≤ Jmax := by
    rw [hqs, hsplit] at hJ; omega
  have hfH : ∀ k, 0 < k → k ≤ Jmax → k ≤ (keySet xr).card →
      (((keySet xr).filter fun (κ : Fin (64 ^ d)) =>
        (keySet xr).card - k ≤ rk (keySet xr) κ ∧ pos κ < (keySet xr).card - π / 2).card : ℝ)
        < εF * k := by
    intro k hk hkJ hkK
    rw [hcard] at hkK ⊢
    have h1 := hspec.fHigh_keys hxr k hk hkJ hkK
    have h2 := filter_image_cellOf hyinj
      (fun κ n => s.card - k ≤ rk (keySet xr) κ ∧ n < s.card - π / 2)
    rw [hfilt]
    simp only [← hydef] at h1
    rw [h2]; exact h1
  have hfL : ∀ k, 0 < k → k ≤ Jmax → k ≤ (keySet xr).card →
      (((keySet xr).filter fun (κ : Fin (64 ^ d)) =>
        rk (keySet xr) κ < k ∧ π / 2 ≤ pos κ).card : ℝ) < εF * k := by
    intro k hk hkJ hkK
    rw [hcard] at hkK
    have h1 := hspec.fLow_keys hxr k hk hkJ hkK
    have h2 := filter_image_cellOf hyinj
      (fun κ n => rk (keySet xr) κ < k ∧ π / 2 ≤ n)
    rw [hfilt]
    simp only [← hydef] at h1
    rw [h2]; exact h1
  have hmain := sent_outside_le (keySet xr) pos π A.lo A.hi Jmax εF hfH hfL hHhi hHlo
  have hcast : ((b.strangers (r + 1) id (fromParentK F nets v t b) : ℕ) : ℝ) ≤
      ((((keySet xr).filter fun κ : Fin (64 ^ d) =>
          π / 2 ≤ pos κ ∧ pos κ < (keySet xr).card - π / 2).filter
        fun κ : Fin (64 ^ d) => ¬ (A.lo ≤ (κ : ℕ) ∧ (κ : ℕ) < A.hi)).card : ℝ) := by
    exact_mod_cast hle
  have hq' : ((q.strangers r id (keySet xr) : ℕ) : ℝ) =
      (((keySet xr).filter fun κ : Fin (64 ^ d) => A.hi ≤ (κ : ℕ)).card : ℝ) +
      (((keySet xr).filter fun κ : Fin (64 ^ d) => (κ : ℕ) < A.lo).card : ℝ) := by
    rw [hqs, hsplit]; push_cast; ring
  rw [hq']
  exact hcast.trans hmain

end Real

end Chvatal
