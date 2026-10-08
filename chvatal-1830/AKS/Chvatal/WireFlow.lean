module
/-
  # Input-independent wire sets of the Chvátal tree network

  Source: V. Chvátal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §3. Given natural flow sizes `F : FlowSizes d tf`, the node `b`
  holds a fixed set `wireSets F t b` of wires at time `t`.  Between `t` and `t+1` the node
  lists its wires in increasing index; the first `up/2` and last `up/2` positions go to the
  parent (fringes), and the middle `64 * down` positions are cut into `64` consecutive
  blocks of `down` positions, block `j` going to the `j`-th child.

  Main results: `blockOf_card` (W1), `upSet_card`/`downSet_card'`/`cover` (W2),
  `mem_wireSets_succ` (W3), `wireSets_card`/`wireSets_disjoint`/`wireSets_complete` (W4),
  `wirePlacement` (W5).
-/

public import AKS.Chvatal.FlowSizes

@[expose] public section

namespace Chvatal

open Finset

/-! **Ranks and blocks** -/

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

theorem upSet_subset : upSet s π ⊆ s :=
  Finset.union_subset blockOf_subset blockOf_subset

theorem downSet_subset : downSet s π τ j ⊆ s := blockOf_subset

theorem rankIn_lt_card (hw : w ∈ s) : rankIn s w < s.card := by
  unfold rankIn
  apply Finset.card_lt_card
  refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
  have := h hw
  simp at this

theorem rankIn_lt_rankIn (hw : w ∈ s) (h : w < w') : rankIn s w < rankIn s w' := by
  unfold rankIn
  apply Finset.card_lt_card
  refine ⟨?_, fun hh => ?_⟩
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 h⟩
  · have := hh (show w ∈ s.filter (· < w') from by simp [hw, h])
    simp at this

theorem rankIn_injOn : Set.InjOn (rankIn s) s := by
  intro x hx y hy hxy
  rcases lt_trichotomy x y with h | h | h
  · exact absurd hxy (rankIn_lt_rankIn hx h).ne
  · exact h
  · exact absurd hxy.symm (rankIn_lt_rankIn hy h).ne

theorem exists_rankIn_eq (hr : r < s.card) : ∃ w ∈ s, rankIn s w = r := by
  have himg : s.image (rankIn s) ⊆ Finset.range s.card := by
    intro r hr
    simp only [Finset.mem_image] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    simpa using rankIn_lt_card hw
  have hc : (s.image (rankIn s)).card = s.card := Finset.card_image_of_injOn rankIn_injOn
  have heq := Finset.eq_of_subset_of_card_le himg (by simp [hc])
  have hr' : r ∈ s.image (rankIn s) := by rw [heq]; simpa using hr
  simpa using hr'

/-- W1. A block of ranks `[lo, hi)` of `s` has exactly `hi - lo` elements. -/
theorem blockOf_card (_hlh : lo ≤ hi) (hh : hi ≤ s.card) :
    (blockOf s lo hi).card = hi - lo := by
  have key : (blockOf s lo hi).card = (Finset.Ico lo hi).card := by
    apply Finset.card_bij (fun w _ => rankIn s w)
    · intro w hw
      rw [mem_blockOf] at hw
      simp only [Finset.mem_Ico]
      exact ⟨hw.2.1, hw.2.2⟩
    · intro a ha b hb h
      exact rankIn_injOn (mem_blockOf.1 ha).1 (mem_blockOf.1 hb).1 h
    · intro r hr
      rw [Finset.mem_Ico] at hr
      obtain ⟨w, hw, hrw⟩ := exists_rankIn_eq (lt_of_lt_of_le hr.2 hh)
      exact ⟨w, mem_blockOf.2 ⟨hw, hrw ▸ hr.1, hrw ▸ hr.2⟩, hrw⟩
  rw [key]; simp

theorem disjoint_blockOf (h : hi ≤ lo') :
    Disjoint (blockOf s lo hi) (blockOf s lo' hi') := by
  rw [Finset.disjoint_left]
  intro w h1 h2
  have := mem_blockOf.1 h1
  have := mem_blockOf.1 h2
  omega

/-- W2 (size of the fringes). -/
theorem upSet_card (hπ : 2 ∣ π) (hc : π ≤ s.card) : (upSet s π).card = π := by
  obtain ⟨k, rfl⟩ := hπ
  have h2 : 2 * k / 2 = k := by omega
  unfold upSet
  rw [h2, Finset.card_union_of_disjoint (disjoint_blockOf (by omega)),
    blockOf_card (by omega) (by omega), blockOf_card (by omega) (by omega)]
  omega

/-- W2 (size of a middle block). -/
theorem downSet_card (hj : π / 2 + (j + 1) * τ ≤ s.card) : (downSet s π τ j).card = τ := by
  unfold downSet
  rw [blockOf_card (by rw [Nat.add_mul, Nat.one_mul]; omega) hj, Nat.add_mul, Nat.one_mul]
  omega

theorem disjoint_upSet_downSet (hs : s.card = π + 64 * τ) (hπ : 2 ∣ π) (hj : j < 64) :
    Disjoint (upSet s π) (downSet s π τ j) := by
  obtain ⟨k, rfl⟩ := hπ
  have h2 : 2 * k / 2 = k := by omega
  have hjτ : (j + 1) * τ ≤ 64 * τ := Nat.mul_le_mul_right _ hj
  unfold upSet downSet
  rw [h2, Finset.disjoint_union_left]
  exact ⟨disjoint_blockOf (by omega), (disjoint_blockOf (by omega)).symm⟩

theorem disjoint_downSet (hj : j < j') :
    Disjoint (downSet s π τ j) (downSet s π τ j') := by
  have : (j + 1) * τ ≤ j' * τ := Nat.mul_le_mul_right _ hj
  exact disjoint_blockOf (by omega)

theorem downSet_card' (hs : s.card = π + 64 * τ) (hj : j < 64) :
    (downSet s π τ j).card = τ := by
  apply downSet_card
  have : (j + 1) * τ ≤ 64 * τ := Nat.mul_le_mul_right _ hj
  omega

/-- W2 (covering): every wire of `s` is in the fringes or in some middle block. -/
theorem cover (hs : s.card = π + 64 * τ) (hπ : 2 ∣ π) (hw : w ∈ s) :
    w ∈ upSet s π ∨ ∃ j, j < 64 ∧ w ∈ downSet s π τ j := by
  obtain ⟨k, rfl⟩ := hπ
  have h2 : 2 * k / 2 = k := by omega
  have hr := rankIn_lt_card hw
  unfold upSet downSet
  rw [h2]
  by_cases h1 : rankIn s w < k
  · left; exact Finset.mem_union_left _ (mem_blockOf.2 ⟨hw, by omega, h1⟩)
  by_cases h3 : s.card - k ≤ rankIn s w
  · left; exact Finset.mem_union_right _ (mem_blockOf.2 ⟨hw, h3, hr⟩)
  right
  have hτ : 0 < τ := by
    rcases Nat.eq_zero_or_pos τ with h | h
    · subst h; omega
    · exact h
  have hm : rankIn s w - k < 64 * τ := by omega
  refine ⟨(rankIn s w - k) / τ, ?_, mem_blockOf.2 ⟨hw, ?_, ?_⟩⟩
  · rw [Nat.div_lt_iff_lt_mul hτ]; omega
  · have := Nat.div_mul_le_self (rankIn s w - k) τ
    omega
  · have h4 := Nat.div_add_mod (rankIn s w - k) τ
    have h5 := Nat.mod_lt (rankIn s w - k) hτ
    rw [Nat.add_mul, Nat.one_mul]
    rw [Nat.mul_comm] at h4
    omega

end Blocks

/-! **Wire sets** -/

variable {d tf : ℕ}

/-- The wires held by each node at time `t`, determined by the flow sizes alone. -/
def wireSets (F : FlowSizes d tf) : ℕ → KBag 64 d → Finset (Fin (64 ^ d))
  | 0, b => if b = KBag.root 64 d then Finset.univ else ∅
  | t + 1, b =>
    (if 1 ≤ b.l then
        downSet (wireSets F t (b.parent)) (F.up (b.l - 1) t) (F.down (b.l - 1) t) (b.x % 64)
      else ∅) ∪
    (if h : b.l < d then
        Finset.univ.biUnion
          (fun j : Fin 64 => upSet (wireSets F t (b.child j.val j.isLt h)) (F.up (b.l + 1) t))
      else ∅)

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

/-- W3: where a wire at time `t+1` came from. -/
theorem mem_wireSets_succ (F : FlowSizes d tf) (t : ℕ) (b : KBag 64 d) (w : Fin (64 ^ d)) :
    w ∈ wireSets F (t + 1) b ↔
      ∃ q : KBag 64 d, w ∈ wireSets F t q ∧
        ((1 ≤ q.l ∧ b = q.parent ∧ w ∈ upSet (wireSets F t q) (F.up q.l t)) ∨
         (q.l < d ∧ ∃ j : Fin 64, ∃ h : q.l < d, b = q.child j.val j.isLt h ∧
            w ∈ downSet (wireSets F t q) (F.up q.l t) (F.down q.l t) j.val)) := by
  constructor
  · intro hw
    rw [wireSets, Finset.mem_union] at hw
    rcases hw with hw | hw
    · by_cases h1 : 1 ≤ b.l
      · rw [if_pos h1] at hw
        have hl : b.parent.l < d := by rw [KBag.parent_l]; have := b.hl; omega
        refine ⟨b.parent, downSet_subset hw, Or.inr ⟨hl, ⟨b.x % 64, Nat.mod_lt _ (by omega)⟩, hl,
          KBag.eq_parent_child b h1 hl, ?_⟩⟩
        simpa [KBag.parent_l] using hw
      · rw [if_neg h1] at hw; simp at hw
    · by_cases h1 : b.l < d
      · rw [dif_pos h1] at hw
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hw
        obtain ⟨j, hj⟩ := hw
        refine ⟨b.child j.val j.isLt h1, upSet_subset hj, Or.inl ⟨?_, ?_, ?_⟩⟩
        · rw [KBag.child_l]; omega
        · exact (KBag.parent_child' b j.val j.isLt h1).symm
        · simpa [KBag.child_l] using hj
      · rw [dif_neg h1] at hw; simp at hw
  · rintro ⟨q, hq, (⟨h1, rfl, hw⟩ | ⟨h1, j, h2, rfl, hw⟩)⟩
    · -- up-route to the parent
      have hl : q.parent.l < d := by rw [KBag.parent_l]; have := q.hl; omega
      rw [wireSets, Finset.mem_union]
      right
      rw [dif_pos hl]
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      refine ⟨⟨q.x % 64, Nat.mod_lt _ (by omega)⟩, ?_⟩
      rw [← KBag.eq_parent_child q h1 hl]
      have : q.parent.l + 1 = q.l := by rw [KBag.parent_l]; omega
      rw [this]; exact hw
    · -- down-route to the child
      rw [wireSets, Finset.mem_union]
      left
      have h3 : 1 ≤ (q.child j.val j.isLt h2).l := by rw [KBag.child_l]; omega
      rw [if_pos h3]
      have hx : (q.child j.val j.isLt h2).x % 64 = j.val := by
        show (64 * q.x + j.val) % 64 = j.val
        omega
      simp only [KBag.parent_child', hx, KBag.child_l, Nat.add_sub_cancel]
      exact hw

/-! **W4: sizes, disjointness and completeness** -/

/-- The part of `wireSets F (t+1) b` coming from the parent. -/
def parentPart (F : FlowSizes d tf) (t : ℕ) (b : KBag 64 d) : Finset (Fin (64 ^ d)) :=
  if 1 ≤ b.l then
    downSet (wireSets F t (b.parent)) (F.up (b.l - 1) t) (F.down (b.l - 1) t) (b.x % 64)
  else ∅

/-- The part of `wireSets F (t+1) b` coming from the children. -/
def childPart (F : FlowSizes d tf) (t : ℕ) (b : KBag 64 d) : Finset (Fin (64 ^ d)) :=
  if h : b.l < d then
    Finset.univ.biUnion
      (fun j : Fin 64 => upSet (wireSets F t (b.child j.val j.isLt h)) (F.up (b.l + 1) t))
  else ∅

theorem wireSets_succ_eq (F : FlowSizes d tf) (t : ℕ) (b : KBag 64 d) :
    wireSets F (t + 1) b = parentPart F t b ∪ childPart F t b := rfl

theorem KBag.l_pos_of_ne_root {b : KBag 64 d} (h : b ≠ KBag.root 64 d) : 1 ≤ b.l := by
  by_contra hl
  apply h
  have hl0 : b.l = 0 := by omega
  apply KBag.ext
  · exact hl0
  · have := b.hx
    rw [hl0] at this
    simp at this
    show b.x = 0
    omega

theorem wireSets_zero_of_ne (F : FlowSizes d tf) {b : KBag 64 d} (h : b ≠ KBag.root 64 d) :
    wireSets F 0 b = ∅ := by
  simp [wireSets, h]

theorem wireSets_zero_root (F : FlowSizes d tf) :
    wireSets F 0 (KBag.root 64 d) = Finset.univ := by
  simp [wireSets]

section Step

variable (F : FlowSizes d tf) {t : ℕ}

theorem card_parentPart (ht : t < tf)
    (hcard : ∀ b : KBag 64 d, (wireSets F t b).card = F.a b.l t) (b : KBag 64 d) :
    (parentPart F t b).card = if 1 ≤ b.l then F.down (b.l - 1) t else 0 := by
  have hsp : ∀ q : KBag 64 d, (wireSets F t q).card = F.up q.l t + 64 * F.down q.l t :=
    fun q => by rw [hcard q, F.hsplit q.l t q.hl ht]
  unfold parentPart
  split_ifs with h1
  · exact downSet_card' (hsp b.parent) (Nat.mod_lt _ (by omega))
  · simp

theorem card_childPart (ht : t < tf)
    (hcard : ∀ b : KBag 64 d, (wireSets F t b).card = F.a b.l t)
    (hdisj : ∀ b b' : KBag 64 d, b ≠ b' → Disjoint (wireSets F t b) (wireSets F t b'))
    (b : KBag 64 d) :
    (childPart F t b).card = if b.l < d then 64 * F.up (b.l + 1) t else 0 := by
  have hsp : ∀ q : KBag 64 d, (wireSets F t q).card = F.up q.l t + 64 * F.down q.l t :=
    fun q => by rw [hcard q, F.hsplit q.l t q.hl ht]
  unfold childPart
  split_ifs with h1
  · rw [Finset.card_biUnion]
    · have hj : ∀ j : Fin 64,
          (upSet (wireSets F t (b.child j.val j.isLt h1)) (F.up (b.l + 1) t)).card
            = F.up (b.l + 1) t := by
        intro j
        have h : (wireSets F t (b.child j.val j.isLt h1)).card
            = F.up (b.l + 1) t + 64 * F.down (b.l + 1) t := hsp _
        exact upSet_card (F.hup_even (b.l + 1) t ht) (by omega)
      rw [Finset.sum_congr rfl (fun j _ => hj j)]
      simp
    · intro j _ j' _ hne
      apply Disjoint.mono upSet_subset upSet_subset
      apply hdisj
      intro he
      exact hne (Fin.ext (KBag.child_inj b j.val j'.val j.isLt j'.isLt h1 he))
  · simp

theorem disjoint_parentPart_childPart (hdisj : ∀ b b' : KBag 64 d, b ≠ b' →
      Disjoint (wireSets F t b) (wireSets F t b')) (b : KBag 64 d) :
    Disjoint (parentPart F t b) (childPart F t b) := by
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
      have hne : b.parent ≠ b.child j.val j.isLt h2 := by
        intro he
        have := congrArg KBag.l he
        rw [KBag.parent_l, KBag.child_l] at this
        omega
      exact Finset.disjoint_left.1 (hdisj _ _ hne) (downSet_subset hP) (upSet_subset hj)
    · rw [dif_neg h2] at hC; simp at hC
  · rw [if_neg h1] at hP; simp at hP

theorem card_succ (ht : t < tf)
    (hcard : ∀ b : KBag 64 d, (wireSets F t b).card = F.a b.l t)
    (hdisj : ∀ b b' : KBag 64 d, b ≠ b' → Disjoint (wireSets F t b) (wireSets F t b'))
    (b : KBag 64 d) : (wireSets F (t + 1) b).card = F.a b.l (t + 1) := by
  rw [wireSets_succ_eq, Finset.card_union_of_disjoint (disjoint_parentPart_childPart F hdisj b),
    card_parentPart F ht hcard, card_childPart F ht hcard hdisj, F.hcons b.l t b.hl ht]

theorem disjoint_succ (ht : t < tf)
    (hcard : ∀ b : KBag 64 d, (wireSets F t b).card = F.a b.l t)
    (hdisj : ∀ b b' : KBag 64 d, b ≠ b' → Disjoint (wireSets F t b) (wireSets F t b'))
    (b b' : KBag 64 d) (hne : b ≠ b') :
    Disjoint (wireSets F (t + 1) b) (wireSets F (t + 1) b') := by
  rw [Finset.disjoint_left]
  intro w h1 h2
  rw [mem_wireSets_succ] at h1 h2
  obtain ⟨q, hq, hr⟩ := h1
  obtain ⟨q', hq', hr'⟩ := h2
  have hqq : q = q' := by
    by_contra hn
    exact Finset.disjoint_left.1 (hdisj q q' hn) hq hq'
  subst hqq
  have hsp : (wireSets F t q).card = F.up q.l t + 64 * F.down q.l t := by
    rw [hcard q, F.hsplit q.l t q.hl ht]
  have hev := F.hup_even q.l t ht
  rcases hr with ⟨_, rfl, hu⟩ | ⟨_, j, hj, rfl, hd⟩ <;>
    rcases hr' with ⟨_, he, hu'⟩ | ⟨_, j', hj', he, hd'⟩
  · exact hne he.symm
  · exact Finset.disjoint_left.1 (disjoint_upSet_downSet hsp hev j'.isLt) hu hd'
  · exact Finset.disjoint_left.1 (disjoint_upSet_downSet hsp hev j.isLt) hu' hd
  · rcases lt_trichotomy j.val j'.val with hl | hl | hl
    · exact Finset.disjoint_left.1 (disjoint_downSet hl) hd hd'
    · have : j = j' := Fin.ext hl
      subst this
      exact hne he.symm
    · exact Finset.disjoint_left.1 (disjoint_downSet hl) hd' hd

theorem complete_succ (ht : t < tf)
    (hcard : ∀ b : KBag 64 d, (wireSets F t b).card = F.a b.l t)
    (hcomp : ∀ w : Fin (64 ^ d), ∃ b : KBag 64 d, w ∈ wireSets F t b)
    (w : Fin (64 ^ d)) : ∃ b : KBag 64 d, w ∈ wireSets F (t + 1) b := by
  obtain ⟨q, hq⟩ := hcomp w
  have hsp : (wireSets F t q).card = F.up q.l t + 64 * F.down q.l t := by
    rw [hcard q, F.hsplit q.l t q.hl ht]
  have hev := F.hup_even q.l t ht
  rcases cover hsp hev hq with hu | ⟨j, hj, hd⟩
  · have h1 : 1 ≤ q.l := by
      by_contra h0
      have h0' : q.l = 0 := by omega
      have hz : F.up q.l t = 0 := by rw [h0']; exact F.hup_root t ht
      have hc : (upSet (wireSets F t q) (F.up q.l t)).card = 0 := by
        rw [upSet_card hev (by omega)]; exact hz
      have := Finset.card_eq_zero.1 hc
      rw [this] at hu
      simp at hu
    exact ⟨q.parent, (mem_wireSets_succ F t _ w).2 ⟨q, hq, Or.inl ⟨h1, rfl, hu⟩⟩⟩
  · have h1 : q.l < d := by
      by_contra h0
      have h0' : q.l = d := by have := q.hl; omega
      have hz : F.down q.l t = 0 := by rw [h0']; exact F.hdown_leaf t ht
      have hc : (downSet (wireSets F t q) (F.up q.l t) (F.down q.l t) j).card = 0 := by
        rw [downSet_card' hsp hj]; exact hz
      have := Finset.card_eq_zero.1 hc
      rw [this] at hd
      simp at hd
    exact ⟨q.child j hj h1, (mem_wireSets_succ F t _ w).2
      ⟨q, hq, Or.inr ⟨h1, ⟨j, hj⟩, h1, rfl, hd⟩⟩⟩

end Step

/-- W4 (main), packaged: all three properties at every time `t ≤ tf`. -/
theorem wireSets_inv (F : FlowSizes d tf) : ∀ t, t ≤ tf →
    (∀ b : KBag 64 d, (wireSets F t b).card = F.a b.l t) ∧
    (∀ b b' : KBag 64 d, b ≠ b' → Disjoint (wireSets F t b) (wireSets F t b')) ∧
    (∀ w : Fin (64 ^ d), ∃ b : KBag 64 d, w ∈ wireSets F t b)
  | 0, _ => by
    refine ⟨fun b => ?_, fun b b' hne => ?_, fun w => ⟨KBag.root 64 d, ?_⟩⟩
    · by_cases hb : b = KBag.root 64 d
      · subst hb
        rw [wireSets_zero_root]
        show (Finset.univ : Finset (Fin (64 ^ d))).card = F.a 0 0
        rw [F.ha_root]; simp
      · rw [wireSets_zero_of_ne F hb, F.ha_init _ (KBag.l_pos_of_ne_root hb)]
        simp
    · by_cases hb : b = KBag.root 64 d
      · rw [wireSets_zero_of_ne F (show b' ≠ KBag.root 64 d from fun h => hne (hb.trans h.symm))]
        exact Finset.disjoint_empty_right _
      · rw [wireSets_zero_of_ne F hb]; exact Finset.disjoint_empty_left _
    · rw [wireSets_zero_root]; exact Finset.mem_univ w
  | t + 1, ht => by
    obtain ⟨h1, h2, h3⟩ := wireSets_inv F t (by omega)
    exact ⟨card_succ F ht h1 h2, disjoint_succ F ht h1 h2, complete_succ F ht h1 h3⟩

/-- W4(a): node sizes. -/
theorem wireSets_card (F : FlowSizes d tf) {t : ℕ} (ht : t ≤ tf) (b : KBag 64 d) :
    (wireSets F t b).card = F.a b.l t := (wireSets_inv F t ht).1 b

/-- W4(b): distinct nodes hold disjoint wire sets. -/
theorem wireSets_disjoint (F : FlowSizes d tf) {t : ℕ} (ht : t ≤ tf) (b b' : KBag 64 d)
    (hne : b ≠ b') : Disjoint (wireSets F t b) (wireSets F t b') :=
  (wireSets_inv F t ht).2.1 b b' hne

/-- W4(c): every wire is somewhere. -/
theorem wireSets_complete (F : FlowSizes d tf) {t : ℕ} (ht : t ≤ tf) (w : Fin (64 ^ d)) :
    ∃ b : KBag 64 d, w ∈ wireSets F t b := (wireSets_inv F t ht).2.2 w



end Chvatal

