module
public import AKS.Chvatal.FlowSizes

@[expose] public section

/-! Input-independent wire sets of the tree network (Chvátal §3): between `t` and `t+1` a node
lists its wires by index; the first and last `up/2` go to the parent, the middle `64 * down` are cut
into 64 blocks of `down`, block `j` going to child `j`. -/

namespace Chvatal

open Finset

/-- Rank of `w` inside `s`: the number of elements of `s` below `w`. -/
def rankIn {n : ℕ} (s : Finset (Fin n)) (w : Fin n) : ℕ := (s.filter (· < w)).card

/-- Elements of `s` whose rank lies in `[lo, hi)`. -/
def blockOf {n : ℕ} (s : Finset (Fin n)) (lo hi : ℕ) : Finset (Fin n) :=
  s.filter (fun w => lo ≤ rankIn s w ∧ rankIn s w < hi)

/-- The fringes: first `π/2` and last `π/2` positions. -/
def upSet {n : ℕ} (s : Finset (Fin n)) (π : ℕ) : Finset (Fin n) :=
  blockOf s 0 (π / 2) ∪ blockOf s (s.card - π / 2) s.card

/-- The `j`-th middle block of `τ` positions. -/
def downSet {n : ℕ} (s : Finset (Fin n)) (π τ j : ℕ) : Finset (Fin n) :=
  blockOf s (π / 2 + j * τ) (π / 2 + (j + 1) * τ)

section Blocks

variable {n : ℕ} {s : Finset (Fin n)} {w w' : Fin n} {r lo hi lo' hi' π τ j j' : ℕ}

theorem mem_blockOf : w ∈ blockOf s lo hi ↔ w ∈ s ∧ lo ≤ rankIn s w ∧ rankIn s w < hi := by
  simp [blockOf]

theorem blockOf_subset : blockOf s lo hi ⊆ s := Finset.filter_subset _ _

theorem upSet_subset : upSet s π ⊆ s := Finset.union_subset blockOf_subset blockOf_subset

theorem downSet_subset : downSet s π τ j ⊆ s := blockOf_subset

theorem rankIn_lt_card (hw : w ∈ s) : rankIn s w < s.card :=
  Finset.card_lt_card (Finset.filter_ssubset.2 ⟨w, hw, by simp⟩)

theorem rankIn_lt_rankIn (hw : w ∈ s) (h : w < w') : rankIn s w < rankIn s w' :=
  Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun x hx => by
    simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans h⟩).2
      ⟨w, by simp [hw, h], by simp⟩)

theorem rankIn_injOn : Set.InjOn (rankIn s) s :=
  StrictMonoOn.injOn fun _ hx _ _ h => rankIn_lt_rankIn hx h

theorem blockOf_card (hh : hi ≤ s.card) : (blockOf s lo hi).card = hi - lo := by
  have himg : s.image (rankIn s) = Finset.range s.card := Finset.eq_of_subset_of_card_le
    (by simp only [Finset.subset_iff, Finset.mem_image, Finset.mem_range]
        rintro _ ⟨w, hw, rfl⟩; exact rankIn_lt_card hw)
    (by simp [Finset.card_image_of_injOn rankIn_injOn])
  rw [← Nat.card_Ico, ← Finset.card_image_of_injOn (f := rankIn s) fun x hx y hy =>
    rankIn_injOn (mem_blockOf.1 hx).1 (mem_blockOf.1 hy).1]
  congr 1; ext r
  simp only [Finset.mem_image, Finset.mem_Ico]
  refine ⟨?_, fun hr => ?_⟩
  · rintro ⟨w, hw, rfl⟩; exact (mem_blockOf.1 hw).2
  · have : r ∈ s.image (rankIn s) := by rw [himg]; simpa using hr.2.trans_le hh
    obtain ⟨w, hw, hrw⟩ := Finset.mem_image.1 this
    exact ⟨w, mem_blockOf.2 ⟨hw, by rw [hrw]; exact hr⟩, hrw⟩

theorem disjoint_blockOf (h : hi ≤ lo') :
    Disjoint (blockOf s lo hi) (blockOf s lo' hi') := by
  rw [Finset.disjoint_left]
  intro w h1 h2
  have := mem_blockOf.1 h1
  have := mem_blockOf.1 h2
  omega

theorem upSet_card (hπ : 2 ∣ π) (hc : π ≤ s.card) : (upSet s π).card = π := by
  unfold upSet
  rw [Finset.card_union_of_disjoint (disjoint_blockOf (by omega)),
    blockOf_card (by omega), blockOf_card (by omega)]
  omega

theorem downSet_card (hs : s.card = π + 64 * τ) (hj : j < 64) : (downSet s π τ j).card = τ := by
  have : (j + 1) * τ ≤ 64 * τ := Nat.mul_le_mul_right _ hj
  unfold downSet
  rw [blockOf_card (by omega), Nat.add_mul, Nat.one_mul]
  omega

theorem disjoint_upSet_downSet (hs : s.card = π + 64 * τ) (hπ : 2 ∣ π) (hj : j < 64) :
    Disjoint (upSet s π) (downSet s π τ j) := by
  have : (j + 1) * τ ≤ 64 * τ := Nat.mul_le_mul_right _ hj
  unfold upSet downSet
  rw [Finset.disjoint_union_left]
  exact ⟨disjoint_blockOf (by omega), (disjoint_blockOf (by omega)).symm⟩

theorem disjoint_downSet (hj : j < j') :
    Disjoint (downSet s π τ j) (downSet s π τ j') := by
  have : (j + 1) * τ ≤ j' * τ := Nat.mul_le_mul_right _ hj
  exact disjoint_blockOf (by omega)

theorem cover (hs : s.card = π + 64 * τ) (hπ : 2 ∣ π) (hw : w ∈ s) :
    w ∈ upSet s π ∨ ∃ j, j < 64 ∧ w ∈ downSet s π τ j := by
  have hr := rankIn_lt_card hw
  unfold upSet downSet
  by_cases h1 : rankIn s w < π / 2
  · exact .inl (Finset.mem_union_left _ (mem_blockOf.2 ⟨hw, by omega, h1⟩))
  by_cases h3 : s.card - π / 2 ≤ rankIn s w
  · exact .inl (Finset.mem_union_right _ (mem_blockOf.2 ⟨hw, h3, hr⟩))
  right
  have hτ : 0 < τ := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have h4 := Nat.div_add_mod (rankIn s w - π / 2) τ
  have h5 := Nat.mod_lt (rankIn s w - π / 2) hτ
  have h6 := Nat.div_mul_le_self (rankIn s w - π / 2) τ
  refine ⟨(rankIn s w - π / 2) / τ, ?_, mem_blockOf.2 ⟨hw, by omega, ?_⟩⟩
  · rw [Nat.div_lt_iff_lt_mul hτ]; omega
  · rw [Nat.add_mul, Nat.one_mul]
    rw [Nat.mul_comm] at h4
    omega

end Blocks

variable {d tf : ℕ}

/-- Wires of `b` at time `t+1` coming from its parent. -/
def parentPart (F : FlowSizes d tf) (S : KBag 64 d → Finset (Fin (64 ^ d))) (t : ℕ)
    (b : KBag 64 d) : Finset (Fin (64 ^ d)) :=
  if 1 ≤ b.l then downSet (S b.parent) (F.up (b.l - 1) t) (F.down (b.l - 1) t) (b.x % 64) else ∅

/-- Wires of `b` at time `t+1` coming from its children. -/
def childPart (F : FlowSizes d tf) (S : KBag 64 d → Finset (Fin (64 ^ d))) (t : ℕ)
    (b : KBag 64 d) : Finset (Fin (64 ^ d)) :=
  if h : b.l < d then
    Finset.univ.biUnion (fun j : Fin 64 => upSet (S (b.child j.val j.isLt h)) (F.up (b.l + 1) t))
  else ∅

/-- The wires held by each node at time `t`, determined by the flow sizes alone. -/
def wireSets (F : FlowSizes d tf) : ℕ → KBag 64 d → Finset (Fin (64 ^ d))
  | 0 => fun b => if b = KBag.root 64 d then Finset.univ else ∅
  | t + 1 => fun b => parentPart F (wireSets F t) t b ∪ childPart F (wireSets F t) t b

theorem wireSets_succ_eq (F : FlowSizes d tf) (t : ℕ) (b : KBag 64 d) :
    wireSets F (t + 1) b = parentPart F (wireSets F t) t b ∪ childPart F (wireSets F t) t b := rfl
theorem KBag.parent_l (b : KBag 64 d) : b.parent.l = b.l - 1 := rfl

theorem KBag.child_l (b : KBag 64 d) (j : ℕ) (hj : j < 64) (h : b.l < d) :
    (b.child j hj h).l = b.l + 1 := rfl

/-- `b` is the `(b.x % 64)`-th child of its parent. -/
theorem KBag.eq_parent_child (b : KBag 64 d) (hb : 1 ≤ b.l) (h : b.parent.l < d) :
    b = b.parent.child (b.x % 64) (Nat.mod_lt _ (by omega)) h :=
  (KBag.parent_child b hb (by omega) h).symm

theorem KBag.child_inj (b : KBag 64 d) (j j' : ℕ) (hj : j < 64) (hj' : j' < 64) (h : b.l < d)
    (he : b.child j hj h = b.child j' hj' h) : j = j' := by
  have := congrArg KBag.x he
  simp only [KBag.child] at this
  omega

theorem KBag.parent_child' (q : KBag 64 d) (j : ℕ) (hj : j < 64) (h : q.l < d) :
    (q.child j hj h).parent = q := KBag.child_parent q j hj h (by omega)

theorem mem_wireSets_succ (F : FlowSizes d tf) (t : ℕ) (b : KBag 64 d) (w : Fin (64 ^ d)) :
    w ∈ wireSets F (t + 1) b ↔
      ∃ q : KBag 64 d, w ∈ wireSets F t q ∧
        ((1 ≤ q.l ∧ b = q.parent ∧ w ∈ upSet (wireSets F t q) (F.up q.l t)) ∨
         (q.l < d ∧ ∃ j : Fin 64, ∃ h : q.l < d, b = q.child j.val j.isLt h ∧
            w ∈ downSet (wireSets F t q) (F.up q.l t) (F.down q.l t) j.val)) := by
  rw [wireSets_succ_eq]
  unfold parentPart childPart
  constructor
  · intro hw
    rcases Finset.mem_union.1 hw with hw | hw
    · by_cases h1 : 1 ≤ b.l
      · rw [if_pos h1] at hw
        have hl : b.parent.l < d := by rw [KBag.parent_l]; have := b.hl; omega
        exact ⟨b.parent, downSet_subset hw, Or.inr ⟨hl, ⟨b.x % 64, Nat.mod_lt _ (by omega)⟩, hl,
          KBag.eq_parent_child b h1 hl, by simpa [KBag.parent_l] using hw⟩⟩
      · simp [h1] at hw
    · by_cases h1 : b.l < d
      · rw [dif_pos h1] at hw
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hw
        obtain ⟨j, hj⟩ := hw
        exact ⟨b.child j.val j.isLt h1, upSet_subset hj, Or.inl ⟨by rw [KBag.child_l]; omega,
          (KBag.parent_child' b j.val j.isLt h1).symm, by simpa [KBag.child_l] using hj⟩⟩
      · simp [h1] at hw
  · rintro ⟨q, hq, (⟨h1, rfl, hw⟩ | ⟨h1, j, h2, rfl, hw⟩)⟩
    · have hl : q.parent.l < d := by rw [KBag.parent_l]; have := q.hl; omega
      refine Finset.mem_union_right _ ?_
      rw [dif_pos hl]
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      refine ⟨⟨q.x % 64, Nat.mod_lt _ (by omega)⟩, ?_⟩
      rw [← KBag.eq_parent_child q h1 hl]
      have : q.parent.l + 1 = q.l := by rw [KBag.parent_l]; omega
      rw [this]; exact hw
    · refine Finset.mem_union_left _ ?_
      have h3 : 1 ≤ (q.child j.val j.isLt h2).l := by rw [KBag.child_l]; omega
      rw [if_pos h3]
      have hx : (q.child j.val j.isLt h2).x % 64 = j.val := by
        show (64 * q.x + j.val) % 64 = j.val
        omega
      simpa only [KBag.parent_child', hx, KBag.child_l, Nat.add_sub_cancel] using hw

theorem KBag.l_pos_of_ne_root {b : KBag 64 d} (h : b ≠ KBag.root 64 d) : 1 ≤ b.l := by
  by_contra hl
  have hl0 : b.l = 0 := by omega
  have := b.hx
  rw [hl0] at this
  exact h (KBag.ext hl0 (by simp at this; show b.x = 0; omega))

theorem wireSets_zero_of_ne (F : FlowSizes d tf) {b : KBag 64 d} (h : b ≠ KBag.root 64 d) :
    wireSets F 0 b = ∅ := by
  simp [wireSets, h]

theorem wireSets_inv (F : FlowSizes d tf) : ∀ t, t ≤ tf →
    (∀ b : KBag 64 d, (wireSets F t b).card = F.a b.l t) ∧
    (∀ b b' : KBag 64 d, b ≠ b' → Disjoint (wireSets F t b) (wireSets F t b')) ∧
    (∀ w : Fin (64 ^ d), ∃ b : KBag 64 d, w ∈ wireSets F t b)
  | 0, _ => by
    have hr : wireSets F 0 (KBag.root 64 d) = Finset.univ := by simp [wireSets]
    refine ⟨fun b => ?_, fun b b' hne => ?_, fun w => ⟨KBag.root 64 d, by simp [hr]⟩⟩
    · by_cases hb : b = KBag.root 64 d
      · subst hb
        rw [hr]; simpa [KBag.root] using F.ha_root.symm
      · rw [wireSets_zero_of_ne F hb, F.ha_init _ (KBag.l_pos_of_ne_root hb)]
        simp
    · by_cases hb : b = KBag.root 64 d
      · rw [wireSets_zero_of_ne F (show b' ≠ KBag.root 64 d from fun h => hne (hb.trans h.symm))]
        exact Finset.disjoint_empty_right _
      · rw [wireSets_zero_of_ne F hb]; exact Finset.disjoint_empty_left _
  | t + 1, ht => by
    obtain ⟨hcard, hdisj, hcomp⟩ := wireSets_inv F t (by omega)
    have ht : t < tf := ht
    have hsp : ∀ q : KBag 64 d, (wireSets F t q).card = F.up q.l t + 64 * F.down q.l t :=
      fun q => by rw [hcard q, F.hsplit q.l t q.hl ht]
    refine ⟨fun b => ?_, fun b b' hne => ?_, fun w => ?_⟩
    · -- sizes
      have hdisj' :
          Disjoint (parentPart F (wireSets F t) t b) (childPart F (wireSets F t) t b) := by
        rw [Finset.disjoint_left]
        intro w hP hC
        unfold parentPart at hP
        unfold childPart at hC
        by_cases h1 : 1 ≤ b.l
        · by_cases h2 : b.l < d
          · rw [if_pos h1] at hP
            rw [dif_pos h2] at hC
            simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hC
            obtain ⟨j, hj⟩ := hC
            have hne : b.parent ≠ b.child j.val j.isLt h2 := fun he => by
              have := congrArg KBag.l he
              rw [KBag.parent_l, KBag.child_l] at this
              omega
            exact Finset.disjoint_left.1 (hdisj _ _ hne) (downSet_subset hP) (upSet_subset hj)
          · rw [dif_neg h2] at hC; simp at hC
        · rw [if_neg h1] at hP; simp at hP
      have hP : (parentPart F (wireSets F t) t b).card =
          if 1 ≤ b.l then F.down (b.l - 1) t else 0 := by
        unfold parentPart
        split_ifs with h1
        · exact downSet_card (hsp b.parent) (Nat.mod_lt _ (by omega))
        · simp
      have hC : (childPart F (wireSets F t) t b).card =
          if b.l < d then 64 * F.up (b.l + 1) t else 0 := by
        unfold childPart
        split_ifs with h1
        · rw [Finset.card_biUnion]
          · rw [Finset.sum_congr rfl (fun j _ => upSet_card (F.hup_even (b.l + 1) t ht)
              (by have := hsp (b.child j.val j.isLt h1); rw [KBag.child_l] at this; omega))]
            simp
          · intro j _ j' _ hne
            refine Disjoint.mono upSet_subset upSet_subset (hdisj _ _ fun he => hne ?_)
            exact Fin.ext (KBag.child_inj b j.val j'.val j.isLt j'.isLt h1 he)
        · simp
      rw [wireSets_succ_eq, Finset.card_union_of_disjoint hdisj', hP, hC, F.hcons b.l t b.hl ht]
    · -- disjointness
      rw [Finset.disjoint_left]
      intro w h1 h2
      rw [mem_wireSets_succ] at h1 h2
      obtain ⟨q, hq, hr⟩ := h1
      obtain ⟨q', hq', hr'⟩ := h2
      obtain rfl : q = q' := by
        by_contra hn
        exact Finset.disjoint_left.1 (hdisj q q' hn) hq hq'
      have hev := F.hup_even q.l t ht
      rcases hr with ⟨_, rfl, hu⟩ | ⟨_, j, hj, rfl, hd⟩ <;>
        rcases hr' with ⟨_, he, hu'⟩ | ⟨_, j', hj', he, hd'⟩
      · exact hne he.symm
      · exact Finset.disjoint_left.1 (disjoint_upSet_downSet (hsp q) hev j'.isLt) hu hd'
      · exact Finset.disjoint_left.1 (disjoint_upSet_downSet (hsp q) hev j.isLt) hu' hd
      · rcases lt_trichotomy j.val j'.val with hl | hl | hl
        · exact Finset.disjoint_left.1 (disjoint_downSet hl) hd hd'
        · obtain rfl : j = j' := Fin.ext hl
          exact hne he.symm
        · exact Finset.disjoint_left.1 (disjoint_downSet hl) hd' hd
    · -- completeness
      obtain ⟨q, hq⟩ := hcomp w
      have hev := F.hup_even q.l t ht
      rcases cover (hsp q) hev hq with hu | ⟨j, hj, hd⟩
      · have h1 : 1 ≤ q.l := by
          by_contra h0
          have hc : (upSet (wireSets F t q) (F.up q.l t)).card = 0 := by
            rw [upSet_card hev (by have := hsp q; omega), show q.l = 0 by omega]; exact F.hup_root t ht
          rw [Finset.card_eq_zero.1 hc] at hu
          simp at hu
        exact ⟨q.parent, (mem_wireSets_succ F t _ w).2 ⟨q, hq, Or.inl ⟨h1, rfl, hu⟩⟩⟩
      · have h1 : q.l < d := by
          by_contra h0
          have hc : (downSet (wireSets F t q) (F.up q.l t) (F.down q.l t) j).card = 0 := by
            rw [downSet_card (hsp q) hj, show q.l = d by have := q.hl; omega]
            exact F.hdown_leaf t ht
          rw [Finset.card_eq_zero.1 hc] at hd
          simp at hd
        exact ⟨q.child j hj h1, (mem_wireSets_succ F t _ w).2
          ⟨q, hq, Or.inr ⟨h1, ⟨j, hj⟩, h1, rfl, hd⟩⟩⟩

theorem wireSets_card (F : FlowSizes d tf) {t : ℕ} (ht : t ≤ tf) (b : KBag 64 d) :
    (wireSets F t b).card = F.a b.l t := (wireSets_inv F t ht).1 b

theorem wireSets_disjoint (F : FlowSizes d tf) {t : ℕ} (ht : t ≤ tf) (b b' : KBag 64 d)
    (hne : b ≠ b') : Disjoint (wireSets F t b) (wireSets F t b') :=
  (wireSets_inv F t ht).2.1 b b' hne

theorem wireSets_complete (F : FlowSizes d tf) {t : ℕ} (ht : t ≤ tf) (w : Fin (64 ^ d)) :
    ∃ b : KBag 64 d, w ∈ wireSets F t b := (wireSets_inv F t ht).2.2 w

end Chvatal
