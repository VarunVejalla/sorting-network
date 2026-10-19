import AKS.Chvatal.Lemma41Real
import Mathlib.Algebra.BigOperators.Fin

/-! # Per-bag flow tables and wire sets at branching factor 16 (LEAN-PLAN W1, step 2)

Port of UB-12's `FlowTableB` (structure, offsets, deficit, θ, residual) and its generic
`WireFlow` (`../../.claude/worktrees/runaware/.../slackfree-lean`) from `br = 64` to `br = 16`. -/

namespace R1T

open Chvatal (KBag Placement subtreeBags)
open Finset

variable {d tf : ℕ}

/-- Per-bag integer flow table (non-uniform blocks).  Generic; no numerics.

Consumers today (of the per-level `FlowSizes` analogue):
* `ha_root`, `ha_init`: `RealInduction.P_one`, `total_mass` (`Wires31`), `wireSets` at `t = 0`;
* `hup_even`: `WireFlow.upSet_card` (`wireSets_card`), `BadSendReal`;
* `hup_root`, `hdown_leaf`: `WireFlow.wireSets_card`, `total_mass`, `FringeSendReal`;
* `hsplit`: `WireFlow.downSet_card`/`wireSets_card`, `BadSendReal.window_real`, `FringeSendField`;
* `hcons`: `WireFlow.wireSets_card`/`wireSets_inv`, `total_mass`. -/
structure FlowTableB (d tf : ℕ) where
  /-- wires at bag `b` at time `t` -/
  a : ℕ → KBag 16 d → ℕ
  /-- `π_b(t)`: wires sent to the parent (`π′` of the slack-free rule; not Chvátal's exact value) -/
  up : ℕ → KBag 16 d → ℕ
  /-- `τ_{b,j}(t)`: wires sent to child `j` -/
  down : ℕ → KBag 16 d → Fin 16 → ℕ
  ha_root : a 0 (KBag.root 16 d) = 16 ^ d
  ha_init : ∀ b, b ≠ KBag.root 16 d → a 0 b = 0
  hup_even : ∀ t b, t < tf → 2 ∣ up t b
  hup_root : ∀ t, t < tf → up t (KBag.root 16 d) = 0
  hdown_leaf : ∀ t b j, t < tf → b.l = d → down t b j = 0
  hsplit : ∀ t b, t < tf → a t b = up t b + ∑ j, down t b j
  hcons : ∀ t b, t < tf → a (t + 1) b =
    (if 1 ≤ b.l then down t b.parent ⟨b.x % 16, Nat.mod_lt _ (by norm_num)⟩ else 0) +
    (if h : b.l < d then ∑ j : Fin 16, up t (b.child j j.isLt h) else 0)

namespace FlowTableB

variable (F : FlowTableB d tf)

/-- Prefix offsets: child `j` gets the cells `[π/2 + off j, π/2 + off (j+1))` of the middle.
(`WireFlow.downSet`, `ExecPlacement.mem_image_downSet_iff`, `NodeKeys.intruder_keys`,
`BadSendReal`.) -/
def off (t : ℕ) (b : KBag 16 d) (j : ℕ) : ℕ :=
  ∑ i : Fin 16 with i.val < j, F.down t b i

/-- Suffix sum: the total sent to children strictly above `j`
(`NodeKeys.intruder_keys`: the window of child `j` ends at `a − π/2 − sufOff j`). -/
def sufOff (t : ℕ) (b : KBag 16 d) (j : ℕ) : ℕ :=
  ∑ i : Fin 16 with j < i.val, F.down t b i

/-- Deficit `G_b = R_b − W_b` (the Lemma 3.1 quantity): the keys addressed to the subtree of `b`
(`16^(d − b.l)` of them) minus the wires currently held in it.  In `ℚ` so that no sign is needed.
Replaces `hwires7` / `NodeFacts.Δ` (`Lemma41Real.keys_below_child_le`, `BadSendField`). -/
def deficit (t : ℕ) (b : KBag 16 d) : ℚ :=
  (16 : ℚ) ^ (d - b.l) - ∑ z ∈ subtreeBags 16 d (by norm_num) b, (F.a t z : ℚ)

/-- `θ_i = G_{child i} − τ_i` of the `i`-th child of `b` (SLACKFREE §3). -/
def theta (t : ℕ) (b : KBag 16 d) (hb : b.l < d) (i : Fin 16) : ℚ :=
  F.deficit t (b.child i i.isLt hb) - F.down t b i

/-- The one-sided Lemma 4.2 residual of window `j`: the part of the lower (resp. upper) cumulative
deficit that the fringe `π/2` does not absorb.  Replaces `NodeFacts.half`/`slack`. -/
def residAt (t : ℕ) (b : KBag 16 d) (hb : b.l < d) (j : Fin 16) : ℚ :=
  max 0 ((∑ i : Fin 16 with i < j, F.theta t b hb i) - (F.up t b : ℚ) / 2) +
  max 0 ((∑ i : Fin 16 with j < i, F.theta t b hb i) - (F.up t b : ℚ) / 2)

end FlowTableB




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

theorem downSet_card (hs : s.card = π + 16 * τ) (hj : j < 16) : (downSet s π τ j).card = τ := by
  have : (j + 1) * τ ≤ 16 * τ := Nat.mul_le_mul_right _ hj
  unfold downSet
  rw [blockOf_card (by omega), Nat.add_mul, Nat.one_mul]
  omega

theorem disjoint_upSet_downSet (hs : s.card = π + 16 * τ) (hπ : 2 ∣ π) (hj : j < 16) :
    Disjoint (upSet s π) (downSet s π τ j) := by
  have : (j + 1) * τ ≤ 16 * τ := Nat.mul_le_mul_right _ hj
  unfold upSet downSet
  rw [Finset.disjoint_union_left]
  exact ⟨disjoint_blockOf (by omega), (disjoint_blockOf (by omega)).symm⟩

theorem disjoint_downSet (hj : j < j') :
    Disjoint (downSet s π τ j) (downSet s π τ j') := by
  have : (j + 1) * τ ≤ j' * τ := Nat.mul_le_mul_right _ hj
  exact disjoint_blockOf (by omega)

theorem cover (hs : s.card = π + 16 * τ) (hπ : 2 ∣ π) (hw : w ∈ s) :
    w ∈ upSet s π ∨ ∃ j, j < 16 ∧ w ∈ downSet s π τ j := by
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

section Blocks

variable {n : ℕ} {s : Finset (Fin n)} {w : Fin n} {π j j' : ℕ} {off : ℕ → ℕ}

/-- The `j`-th middle block, with cumulative boundaries `π/2 + off j`. -/
def downSetB (s : Finset (Fin n)) (π : ℕ) (off : ℕ → ℕ) (j : ℕ) : Finset (Fin n) :=
  blockOf s (π / 2 + off j) (π / 2 + off (j + 1))

theorem downSetB_subset : downSetB s π off j ⊆ s := blockOf_subset

/-- Equal blocks recover `WireFlow.downSet`. -/
theorem downSetB_uniform (τ : ℕ) : downSetB s π (fun i => i * τ) j = downSet s π τ j := rfl

theorem mem_downSetB : w ∈ downSetB s π off j ↔
    w ∈ s ∧ π / 2 + off j ≤ rankIn s w ∧ rankIn s w < π / 2 + off (j + 1) := mem_blockOf

theorem downSetB_card (hmono : Monotone off) (hs : s.card = π + off 16) (hj : j < 16) :
    (downSetB s π off j).card = off (j + 1) - off j := by
  have h1 : off (j + 1) ≤ off 16 := hmono (by omega)
  unfold downSetB
  rw [blockOf_card (by omega)]
  omega

theorem disjoint_downSetB (hmono : Monotone off) (hj : j < j') :
    Disjoint (downSetB s π off j) (downSetB s π off j') := by
  have : off (j + 1) ≤ off j' := hmono (by omega)
  exact disjoint_blockOf (by omega)

theorem disjoint_upSet_downSetB (hmono : Monotone off) (hs : s.card = π + off 16) (hπ : 2 ∣ π)
    (hj : j < 16) : Disjoint (upSet s π) (downSetB s π off j) := by
  have h1 : off (j + 1) ≤ off 16 := hmono (by omega)
  unfold upSet downSetB
  rw [Finset.disjoint_union_left]
  exact ⟨disjoint_blockOf (by omega), (disjoint_blockOf (by omega)).symm⟩

/-- Every wire is in the fringe or in exactly one (hence some) middle block. -/
theorem cover_B (hoff0 : off 0 = 0) (hs : s.card = π + off 16)
    (hπ : 2 ∣ π) (hw : w ∈ s) :
    w ∈ upSet s π ∨ ∃ j, j < 16 ∧ w ∈ downSetB s π off j := by
  have hr := rankIn_lt_card hw
  unfold upSet
  by_cases h1 : rankIn s w < π / 2
  · exact .inl (Finset.mem_union_left _ (mem_blockOf.2 ⟨hw, by omega, h1⟩))
  by_cases h3 : s.card - π / 2 ≤ rankIn s w
  · exact .inl (Finset.mem_union_right _ (mem_blockOf.2 ⟨hw, h3, hr⟩))
  right
  have e64 : off (15 + 1) = off 16 := rfl
  have hex : ∃ k, rankIn s w - π / 2 < off (k + 1) := ⟨15, by omega⟩
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ 15 := Nat.find_min' hex (by omega)
  have hlo : off (Nat.find hex) ≤ rankIn s w - π / 2 := by
    by_cases h0 : Nat.find hex = 0
    · rw [h0, hoff0]; exact Nat.zero_le _
    · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
      omega
  exact ⟨Nat.find hex, by omega, mem_blockOf.2 ⟨hw, by omega, by omega⟩⟩

end Blocks

namespace FlowTableB

variable {d tf : ℕ} (F : FlowTableB d tf) (t : ℕ) (b : KBag 16 d)

theorem off_zero : F.off t b 0 = 0 := by simp [off]

theorem off_mono : Monotone (F.off t b) := by
  intro j j' hjj
  unfold off
  apply Finset.sum_le_sum_of_subset
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

theorem off_sixteen : F.off t b 16 = ∑ j, F.down t b j := by
  unfold off
  rw [Finset.filter_true_of_mem (fun i _ => i.isLt)]

theorem off_succ {j : ℕ} (hj : j < 16) : F.off t b (j + 1) = F.off t b j + F.down t b ⟨j, hj⟩ := by
  unfold off
  have : (Finset.univ.filter (fun i : Fin 16 => i.val < j + 1)) =
      insert ⟨j, hj⟩ (Finset.univ.filter (fun i : Fin 16 => i.val < j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp), add_comm]

/-- Equal blocks: if every child receives `τ`, the offsets are `j * τ` (`j ≤ 16`). -/
theorem off_const {τ : ℕ} (h : ∀ i, F.down t b i = τ) {j : ℕ} (hj : j ≤ 16) :
    F.off t b j = j * τ := by
  unfold off
  simp only [h, Finset.sum_const, smul_eq_mul]
  congr 1
  have : (Finset.univ.filter fun i : Fin 16 => i.val < j) = (Finset.range j).attachFin
      (fun m hm => by have := Finset.mem_range.1 hm; omega) := by
    ext i; simp
  rw [this, Finset.card_attachFin, Finset.card_range]

/-- Block sizes of the generalized `downSet` for a table: child `j` gets exactly `down t b j`. -/
theorem card_downSetB {n : ℕ} {s : Finset (Fin n)}
    (hs : s.card = F.up t b + ∑ j, F.down t b j) {j : ℕ} (hj : j < 16) :
    (downSetB s (F.up t b) (F.off t b) j).card = F.down t b ⟨j, hj⟩ := by
  rw [downSetB_card (F.off_mono t b) (by rw [F.off_sixteen]; exact hs) hj, F.off_succ t b hj]
  omega

end FlowTableB


/-- Wires of `b` at time `t+1` coming from its parent. -/
def parentPart (F : FlowTableB d tf) (S : KBag 16 d → Finset (Fin (16 ^ d))) (t : ℕ)
    (b : KBag 16 d) : Finset (Fin (16 ^ d)) :=
  if 1 ≤ b.l then
    downSetB (S b.parent) (F.up t b.parent) (F.off t b.parent) (b.x % 16) else ∅

/-- Wires of `b` at time `t+1` coming from its children. -/
def childPart (F : FlowTableB d tf) (S : KBag 16 d → Finset (Fin (16 ^ d))) (t : ℕ)
    (b : KBag 16 d) : Finset (Fin (16 ^ d)) :=
  if h : b.l < d then
    Finset.univ.biUnion (fun j : Fin 16 =>
      upSet (S (b.child j.val j.isLt h)) (F.up t (b.child j.val j.isLt h)))
  else ∅

/-- The wires held by each node at time `t`, determined by the flow sizes alone. -/
def wireSets (F : FlowTableB d tf) : ℕ → KBag 16 d → Finset (Fin (16 ^ d))
  | 0 => fun b => if b = KBag.root 16 d then Finset.univ else ∅
  | t + 1 => fun b => parentPart F (wireSets F t) t b ∪ childPart F (wireSets F t) t b

theorem wireSets_succ_eq (F : FlowTableB d tf) (t : ℕ) (b : KBag 16 d) :
    wireSets F (t + 1) b = parentPart F (wireSets F t) t b ∪ childPart F (wireSets F t) t b := rfl
theorem KBag.parent_l (b : KBag 16 d) : b.parent.l = b.l - 1 := rfl

theorem KBag.child_l (b : KBag 16 d) (j : ℕ) (hj : j < 16) (h : b.l < d) :
    (b.child j hj h).l = b.l + 1 := rfl

/-- `b` is the `(b.x % 16)`-th child of its parent. -/
theorem KBag.eq_parent_child (b : KBag 16 d) (hb : 1 ≤ b.l) (h : b.parent.l < d) :
    b = b.parent.child (b.x % 16) (Nat.mod_lt _ (by omega)) h :=
  (KBag.parent_child b hb (by omega) h).symm

theorem KBag.child_inj (b : KBag 16 d) (j j' : ℕ) (hj : j < 16) (hj' : j' < 16) (h : b.l < d)
    (he : b.child j hj h = b.child j' hj' h) : j = j' := by
  have := congrArg KBag.x he
  simp only [KBag.child] at this
  omega

theorem KBag.parent_child' (q : KBag 16 d) (j : ℕ) (hj : j < 16) (h : q.l < d) :
    (q.child j hj h).parent = q := KBag.child_parent q j hj h (by omega)

theorem mem_wireSets_succ (F : FlowTableB d tf) (t : ℕ) (b : KBag 16 d) (w : Fin (16 ^ d)) :
    w ∈ wireSets F (t + 1) b ↔
      ∃ q : KBag 16 d, w ∈ wireSets F t q ∧
        ((1 ≤ q.l ∧ b = q.parent ∧ w ∈ upSet (wireSets F t q) (F.up t q)) ∨
         (q.l < d ∧ ∃ j : Fin 16, ∃ h : q.l < d, b = q.child j.val j.isLt h ∧
            w ∈ downSetB (wireSets F t q) (F.up t q) (F.off t q) j.val)) := by
  rw [wireSets_succ_eq]
  unfold parentPart childPart
  constructor
  · intro hw
    rcases Finset.mem_union.1 hw with hw | hw
    · by_cases h1 : 1 ≤ b.l
      · rw [if_pos h1] at hw
        have hl : b.parent.l < d := by rw [KBag.parent_l]; have := b.hl; omega
        exact ⟨b.parent, downSetB_subset hw, Or.inr ⟨hl, ⟨b.x % 16, Nat.mod_lt _ (by omega)⟩, hl,
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
      refine ⟨⟨q.x % 16, Nat.mod_lt _ (by omega)⟩, ?_⟩
      rw [← KBag.eq_parent_child q h1 hl]
      exact hw
    · refine Finset.mem_union_left _ ?_
      have h3 : 1 ≤ (q.child j.val j.isLt h2).l := by rw [KBag.child_l]; omega
      rw [if_pos h3]
      have hx : (q.child j.val j.isLt h2).x % 16 = j.val := by
        show (16 * q.x + j.val) % 16 = j.val
        omega
      simpa only [KBag.parent_child', hx, KBag.child_l, Nat.add_sub_cancel] using hw

theorem KBag.l_pos_of_ne_root {b : KBag 16 d} (h : b ≠ KBag.root 16 d) : 1 ≤ b.l := by
  by_contra hl
  have hl0 : b.l = 0 := by omega
  have := b.hx
  rw [hl0] at this
  exact h (KBag.ext hl0 (by simp at this; show b.x = 0; omega))

theorem wireSets_zero_of_ne (F : FlowTableB d tf) {b : KBag 16 d} (h : b ≠ KBag.root 16 d) :
    wireSets F 0 b = ∅ := by
  simp [wireSets, h]

theorem wireSets_inv (F : FlowTableB d tf) : ∀ t, t ≤ tf →
    (∀ b : KBag 16 d, (wireSets F t b).card = F.a t b) ∧
    (∀ b b' : KBag 16 d, b ≠ b' → Disjoint (wireSets F t b) (wireSets F t b')) ∧
    (∀ w : Fin (16 ^ d), ∃ b : KBag 16 d, w ∈ wireSets F t b)
  | 0, _ => by
    have hr : wireSets F 0 (KBag.root 16 d) = Finset.univ := by simp [wireSets]
    refine ⟨fun b => ?_, fun b b' hne => ?_, fun w => ⟨KBag.root 16 d, by simp [hr]⟩⟩
    · by_cases hb : b = KBag.root 16 d
      · subst hb
        rw [hr]; simpa [KBag.root] using F.ha_root.symm
      · rw [wireSets_zero_of_ne F hb, F.ha_init b hb]
        simp
    · by_cases hb : b = KBag.root 16 d
      · rw [wireSets_zero_of_ne F (show b' ≠ KBag.root 16 d from fun h => hne (hb.trans h.symm))]
        exact Finset.disjoint_empty_right _
      · rw [wireSets_zero_of_ne F hb]; exact Finset.disjoint_empty_left _
  | t + 1, ht => by
    obtain ⟨hcard, hdisj, hcomp⟩ := wireSets_inv F t (by omega)
    have ht : t < tf := ht
    have hsp : ∀ q : KBag 16 d, (wireSets F t q).card = F.up t q + ∑ j, F.down t q j :=
      fun q => by rw [hcard q, F.hsplit t q ht]
    have hs64 : ∀ q : KBag 16 d, (wireSets F t q).card = F.up t q + F.off t q 16 :=
      fun q => by rw [hsp q, F.off_sixteen]
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
            exact Finset.disjoint_left.1 (hdisj _ _ hne) (downSetB_subset hP) (upSet_subset hj)
          · rw [dif_neg h2] at hC; simp at hC
        · rw [if_neg h1] at hP; simp at hP
      have hP : (parentPart F (wireSets F t) t b).card =
          if 1 ≤ b.l then F.down t b.parent ⟨b.x % 16, Nat.mod_lt _ (by norm_num)⟩ else 0 := by
        unfold parentPart
        split_ifs with h1
        · exact F.card_downSetB t b.parent (hsp b.parent) (Nat.mod_lt _ (by norm_num))
        · simp
      have hC : (childPart F (wireSets F t) t b).card =
          if h : b.l < d then ∑ j : Fin 16, F.up t (b.child j j.isLt h) else 0 := by
        unfold childPart
        split_ifs with h1
        · rw [Finset.card_biUnion]
          · rw [Finset.sum_congr rfl (fun j _ => upSet_card (F.hup_even t _ ht)
              (by have := hsp (b.child j.val j.isLt h1); omega))]
          · intro j _ j' _ hne
            refine Disjoint.mono upSet_subset upSet_subset (hdisj _ _ fun he => hne ?_)
            exact Fin.ext (KBag.child_inj b j.val j'.val j.isLt j'.isLt h1 he)
        · simp
      rw [wireSets_succ_eq, Finset.card_union_of_disjoint hdisj', hP, hC, F.hcons t b ht]
    · -- disjointness
      rw [Finset.disjoint_left]
      intro w h1 h2
      rw [mem_wireSets_succ] at h1 h2
      obtain ⟨q, hq, hr⟩ := h1
      obtain ⟨q', hq', hr'⟩ := h2
      obtain rfl : q = q' := by
        by_contra hn
        exact Finset.disjoint_left.1 (hdisj q q' hn) hq hq'
      have hev := F.hup_even t q ht
      rcases hr with ⟨_, rfl, hu⟩ | ⟨_, j, hj, rfl, hd⟩ <;>
        rcases hr' with ⟨_, he, hu'⟩ | ⟨_, j', hj', he, hd'⟩
      · exact hne he.symm
      · exact Finset.disjoint_left.1 (disjoint_upSet_downSetB (F.off_mono t q) (hs64 q) hev j'.isLt) hu hd'
      · exact Finset.disjoint_left.1 (disjoint_upSet_downSetB (F.off_mono t q) (hs64 q) hev j.isLt) hu' hd
      · rcases lt_trichotomy j.val j'.val with hl | hl | hl
        · exact Finset.disjoint_left.1 (disjoint_downSetB (F.off_mono t q) hl) hd hd'
        · obtain rfl : j = j' := Fin.ext hl
          exact hne he.symm
        · exact Finset.disjoint_left.1 (disjoint_downSetB (F.off_mono t q) hl) hd' hd
    · -- completeness
      obtain ⟨q, hq⟩ := hcomp w
      have hev := F.hup_even t q ht
      rcases cover_B (F.off_zero t q) (hs64 q) hev hq with hu | ⟨j, hj, hd⟩
      · have h1 : 1 ≤ q.l := by
          by_contra h0
          have hc : (upSet (wireSets F t q) (F.up t q)).card = 0 := by
            rw [upSet_card hev (by have := hsp q; omega), show q = KBag.root 16 d from by
              by_contra hne; exact h0 (KBag.l_pos_of_ne_root hne)]
            exact F.hup_root t ht
          rw [Finset.card_eq_zero.1 hc] at hu
          simp at hu
        exact ⟨q.parent, (mem_wireSets_succ F t _ w).2 ⟨q, hq, Or.inl ⟨h1, rfl, hu⟩⟩⟩
      · have h1 : q.l < d := by
          by_contra h0
          have hc : (downSetB (wireSets F t q) (F.up t q) (F.off t q) j).card = 0 := by
            rw [F.card_downSetB t q (hsp q) hj]
            exact F.hdown_leaf t q ⟨j, hj⟩ ht (by have := q.hl; omega)
          rw [Finset.card_eq_zero.1 hc] at hd
          simp at hd
        exact ⟨q.child j hj h1, (mem_wireSets_succ F t _ w).2
          ⟨q, hq, Or.inr ⟨h1, ⟨j, hj⟩, h1, rfl, hd⟩⟩⟩

theorem wireSets_card (F : FlowTableB d tf) {t : ℕ} (ht : t ≤ tf) (b : KBag 16 d) :
    (wireSets F t b).card = F.a t b := (wireSets_inv F t ht).1 b

theorem wireSets_disjoint (F : FlowTableB d tf) {t : ℕ} (ht : t ≤ tf) (b b' : KBag 16 d)
    (hne : b ≠ b') : Disjoint (wireSets F t b) (wireSets F t b') :=
  (wireSets_inv F t ht).2.1 b b' hne

theorem wireSets_complete (F : FlowTableB d tf) {t : ℕ} (ht : t ≤ tf) (w : Fin (16 ^ d)) :
    ∃ b : KBag 16 d, w ∈ wireSets F t b := (wireSets_inv F t ht).2.2 w


end R1T
