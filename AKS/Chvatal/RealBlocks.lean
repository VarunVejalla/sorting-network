module

/-
  # Final blocks of the real network

  At the final time `t_f = 3d - 20` only level `d - 6` is occupied, each node holding `64^6`
  wires.  Grouping the 64 children of each level-`(d-7)` bag gives disjoint blocks of `2^42`
  wires covering everything, and rank purity turns each block into a sorted-rank interval.
-/

public import AKS.Chvatal.RealPurity

@[expose] public section

namespace Chvatal

section Blocks

variable (d : ℕ) (hd : 7 ≤ d)

/-- Occupancy at the final time. -/
theorem flowA7_tf (l : ℕ) :
    flowA7 d hd l (tf7 d) = if l = d - 6 then 64 ^ 6 else 0 := by
  by_cases h2 : 2 ≤ tf7 d
  · have ha := levelSchedule7_alpha_tf d hd
    have ho := levelSchedule7_omega_tf d hd
    have hc := capacity_meet7 d hd
    have hf : (levelSchedule7 d hd).tf = tf7 d := rfl
    rw [hf] at ha ho
    simp only [meetLevel7] at ha ho hc
    unfold flowA7
    have h0 : tf7 d ≠ 0 := by omega
    have h1 : tf7 d ≠ 1 := by omega
    simp only [h0, h1, if_false]
    unfold allocation
    have hpar : (d - 6) % 2 = tf7 d % 2 := by
      have := alpha7_parity d (tf7 d)
      rw [alpha7_tf d hd] at this
      simpa [meetLevel7] using this
    rw [ha, ho]
    by_cases hl : l = d - 6
    · subst hl
      have hc' : capacity params7 d (d - 6) (tf7 d) = ((64 ^ 6 : ℕ) : ℚ) := by
        rw [hc]; push_cast; rfl
      rw [if_pos ⟨hf.ge, le_refl _, le_refl _, hpar⟩, if_pos rfl, if_pos rfl, hc']
      simp
    · have hn : ¬ (tf7 d ≤ (levelSchedule7 d hd).tf ∧ d - 6 ≤ l ∧ l ≤ d - 6 ∧
          l % 2 = tf7 d % 2) := fun h => hl (by omega)
      rw [if_neg hn, if_neg hl]
      simp
  · have : d = 7 := by unfold tf7 at h2; omega
    subst this
    have h : tf7 7 = 1 := by unfold tf7; omega
    rw [h]
    simp [flowA7]

/-- Occupancy of the nodes at the final time: empty off the meeting level. -/
theorem wireSets_final_empty (b : KBag 64 d) (hb : b.l ≠ d - 6) :
    wireSets (flowSizes7 d hd) (tf7 d) b = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [wireSets_card (flowSizes7 d hd) le_rfl b]
  show flowA7 d hd b.l (tf7 d) = 0
  rw [flowA7_tf d hd, if_neg hb]

/-- Occupancy of the nodes at the final time: `64^6` wires on the meeting level. -/
theorem wireSets_final_card (b : KBag 64 d) (hb : b.l = d - 6) :
    (wireSets (flowSizes7 d hd) (tf7 d) b).card = 64 ^ 6 := by
  rw [wireSets_card (flowSizes7 d hd) le_rfl b]
  show flowA7 d hd b.l (tf7 d) = _
  rw [flowA7_tf d hd, if_pos hb]

/-- The wires held at the final time by the 64 children of `p`. -/
def blockWires (p : KBag 64 d) : Finset (Fin (64 ^ d)) :=
  if h : p.l < d then
    Finset.univ.biUnion
      (fun j : Fin 64 => wireSets (flowSizes7 d hd) (tf7 d) (p.child j.val j.isLt h))
  else ∅

/-- The final block of a level-`(d-7)` bag; empty for every other bag. -/
def finalS (b : KBag 64 d) : Finset (Fin (64 ^ d)) :=
  if b.l = d - 7 then blockWires d hd b else ∅

theorem finalS_card (b : KBag 64 d) (hb : b.l = d - 7) : (finalS d hd b).card = 2 ^ 42 := by
  have hlt : b.l < d := by omega
  unfold finalS blockWires
  rw [if_pos hb, dif_pos hlt, Finset.card_biUnion]
  · have : ∀ j ∈ (Finset.univ : Finset (Fin 64)),
        (wireSets (flowSizes7 d hd) (tf7 d) (b.child j.val j.isLt hlt)).card = 64 ^ 6 :=
      fun j _ => wireSets_final_card d hd _ (by rw [KBag.child_l]; omega)
    rw [Finset.sum_congr rfl this]
    simp
  · intro j _ j' _ hjj
    apply wireSets_disjoint (flowSizes7 d hd) le_rfl
    intro h
    apply hjj
    exact Fin.ext (KBag.child_inj b _ _ j.isLt j'.isLt hlt h)

theorem finalS_disjoint (b b' : KBag 64 d) (hne : b ≠ b') :
    Disjoint (finalS d hd b) (finalS d hd b') := by
  unfold finalS
  by_cases h1 : b.l = d - 7
  · by_cases h2 : b'.l = d - 7
    · have hlt : b.l < d := by omega
      have hlt' : b'.l < d := by omega
      rw [if_pos h1, if_pos h2]
      unfold blockWires
      rw [dif_pos hlt, dif_pos hlt']
      rw [Finset.disjoint_left]
      intro w hw hw'
      rw [Finset.mem_biUnion] at hw hw'
      obtain ⟨j, _, hj⟩ := hw
      obtain ⟨j', _, hj'⟩ := hw'
      have := Finset.disjoint_left.mp
        (wireSets_disjoint (flowSizes7 d hd) (tf7 d).le_refl
          (b.child j.val j.isLt hlt) (b'.child j'.val j'.isLt hlt') (by
            intro h
            apply hne
            have := congrArg (fun c : KBag 64 d => c.parent) h
            simp only at this
            rwa [KBag.parent_child', KBag.parent_child'] at this)) hj
      exact this hj'
    · rw [if_neg h2]; exact Finset.disjoint_empty_right _
  · rw [if_neg h1]; exact Finset.disjoint_empty_left _

theorem finalS_cover (w : Fin (64 ^ d)) : ∃ b : KBag 64 d, w ∈ finalS d hd b := by
  obtain ⟨q, hq⟩ := wireSets_complete (flowSizes7 d hd) (t := tf7 d) le_rfl w
  have hql : q.l = d - 6 := by
    by_contra h
    rw [wireSets_final_empty d hd q h] at hq
    exact absurd hq (Finset.notMem_empty _)
  have hpl : q.parent.l = d - 7 := by rw [KBag.parent_l]; omega
  have hplt : q.parent.l < d := by omega
  refine ⟨q.parent, ?_⟩
  unfold finalS blockWires
  rw [if_pos hpl, dif_pos hplt, Finset.mem_biUnion]
  refine ⟨⟨q.x % 64, Nat.mod_lt _ (by omega)⟩, Finset.mem_univ _, ?_⟩
  have := KBag.eq_parent_child q (by omega) hplt
  rw [← this]
  exact hq

/-- Rank purity turns the final block of `b` into a sorted-rank interval. -/
theorem finalS_image_sub
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d)))
    (hpur : ∀ b : KBag 64 d, b.l = d - 6 →
      b.strangers 2 id ((execPlacement (flowSizes7 d hd) nets v (tf7 d) le_rfl).regs b)
        (by norm_num : 1 ≤ 64) = 0)
    (b : KBag 64 d) (hb : b.l = d - 7) :
    (finalS d hd b).image (X (flowSizes7 d hd) nets v (tf7 d)) ⊆
      Finset.univ.filter (fun x : Fin (64 ^ d) =>
        b.x * 2 ^ 42 ≤ x.val ∧ x.val < b.x * 2 ^ 42 + 2 ^ 42) := by
  have hlt : b.l < d := by omega
  intro k hk
  rw [Finset.mem_image] at hk
  obtain ⟨w, hw, rfl⟩ := hk
  unfold finalS blockWires at hw
  rw [if_pos hb, dif_pos hlt, Finset.mem_biUnion] at hw
  obtain ⟨j, _, hj⟩ := hw
  set q := b.child j.val j.isLt hlt with hq
  have hql : q.l = d - 6 := by rw [hq, KBag.child_l]; omega
  have hmem : X (flowSizes7 d hd) nets v (tf7 d) w ∈
      (execPlacement (flowSizes7 d hd) nets v (tf7 d) le_rfl).regs q :=
    Finset.mem_image_of_mem _ hj
  have h0 := hpur q hql
  unfold KBag.strangers at h0
  have hnot : ¬ q.Strange 2 (X (flowSizes7 d hd) nets v (tf7 d) w) id (by norm_num : 1 ≤ 64) := by
    intro hs
    have := Finset.card_eq_zero.mp h0
    have hm : X (flowSizes7 d hd) nets v (tf7 d) w ∈
        ((execPlacement (flowSizes7 d hd) nets v (tf7 d) le_rfl).regs q).filter
          (fun r => q.Strange 2 r id (by norm_num : 1 ≤ 64)) :=
      Finset.mem_filter.mpr ⟨hmem, hs⟩
    rw [this] at hm
    exact absurd hm (Finset.notMem_empty _)
  simp only [KBag.Strange, show (2 : ℕ) ≠ 0 by omega, false_or, not_not] at hnot
  have hanc : q.ancestor (2 - 1) (by norm_num : 1 ≤ 64) = b := by
    apply KBag.ext
    · show q.l - (2 - 1) = b.l
      omega
    · show q.x / 64 ^ (2 - 1) = b.x
      show (64 * b.x + j.val) / 64 ^ (2 - 1) = b.x
      have := j.isLt
      norm_num
      omega
  rw [hanc] at hnot
  simp only [KBag.Native, nativeBagIdx, bagSize, id] at hnot
  have hexp : d - b.l = 7 := by omega
  rw [hexp] at hnot
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have h64 : (64 : ℕ) ^ 7 = 2 ^ 42 := by norm_num
  rw [h64] at hnot
  have hpos : 0 < 2 ^ 42 := by positivity
  have h1 := Nat.div_mul_le_self (X (flowSizes7 d hd) nets v (tf7 d) w).val (2 ^ 42)
  have h2 := Nat.lt_div_mul_add (a := (X (flowSizes7 d hd) nets v (tf7 d) w).val) hpos
  rw [hnot] at h1 h2
  exact ⟨h1, h2⟩

theorem finalS_image_level
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d)))
    (hpur : ∀ b : KBag 64 d, b.l = d - 6 →
      b.strangers 2 id ((execPlacement (flowSizes7 d hd) nets v (tf7 d) le_rfl).regs b)
        (by norm_num : 1 ≤ 64) = 0)
    (b : KBag 64 d) (hb : b.l = d - 7) :
    (finalS d hd b).image (X (flowSizes7 d hd) nets v (tf7 d)) =
      Finset.univ.filter (fun x : Fin (64 ^ d) =>
        b.x * 2 ^ 42 ≤ x.val ∧ x.val < b.x * 2 ^ 42 + 2 ^ 42) := by
  apply Finset.eq_of_subset_of_card_le (finalS_image_sub d hd nets v hpur b hb)
  rw [Finset.card_image_of_injective _ (X_injective _ nets v _), finalS_card d hd b hb]
  -- the interval has at most `2^42` points
  have hsub : (Finset.univ.filter (fun x : Fin (64 ^ d) =>
        b.x * 2 ^ 42 ≤ x.val ∧ x.val < b.x * 2 ^ 42 + 2 ^ 42)).map Fin.valEmbedding ⊆
      Finset.Ico (b.x * 2 ^ 42) (b.x * 2 ^ 42 + 2 ^ 42) := by
    intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Finset.mem_filter] at hx
    exact Finset.mem_Ico.mpr hx.2
  have := Finset.card_le_card hsub
  rw [Finset.card_map, Nat.card_Ico] at this
  omega

theorem finalS_image
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d)))
    (hpur : ∀ b : KBag 64 d, b.l = d - 6 →
      b.strangers 2 id ((execPlacement (flowSizes7 d hd) nets v (tf7 d) le_rfl).regs b)
        (by norm_num : 1 ≤ 64) = 0)
    (b : KBag 64 d) :
    (finalS d hd b).image (X (flowSizes7 d hd) nets v (tf7 d)) =
      Finset.univ.filter (fun x : Fin (64 ^ d) =>
        b.x * 2 ^ 42 ≤ x.val ∧ x.val < b.x * 2 ^ 42 + (finalS d hd b).card) := by
  by_cases hb : b.l = d - 7
  · rw [finalS_card d hd b hb]
    exact finalS_image_level d hd nets v hpur b hb
  · have : finalS d hd b = ∅ := by unfold finalS; rw [if_neg hb]
    rw [this]
    ext x
    simp only [Finset.image_empty, Finset.card_empty, Finset.notMem_empty, false_iff, Finset.mem_filter, Finset.mem_univ, true_and, add_zero, not_and, not_lt]
    exact id

end Blocks

/-- Real specialization of the rank-interval statement for the blocks. -/
theorem finalS_image_real {d : ℕ} (hd14 : 14 ≤ d) (v : Equiv.Perm (Fin (64 ^ d)))
    (b : KBag 64 d) :
    (finalS d (by omega) b).image
        (X (flowSizes7 d (by omega)) (realNets d (by omega)) v (tf7 d)) =
      Finset.univ.filter (fun x : Fin (64 ^ d) =>
        b.x * 2 ^ 42 ≤ x.val ∧ x.val < b.x * 2 ^ 42 + (finalS d (by omega) b).card) :=
  finalS_image d (by omega) (realNets d (by omega)) v
    (fun b hb => realNets_purity hd14 v b hb) b

end Chvatal
