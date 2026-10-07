module

/-
  # Chvátal Lemma 4.1, real (counting form)

  Source: V. Chvátal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §4 Lemma 4.1.

  Keys are their own addresses (`perm := id`); a key `κ` is addressed below `w` iff
  `w.Native κ id`.  A node `u` at an occupied level holds fewer than
  `(1/k + μ·siblingFactor)·c(i,t)` keys addressed below any one child `w`.  The proof counts the
  `k^(d-i-1)` keys addressed below `w`: those sitting in the subtree of `w` number at least
  `|subtreeKeys w|` minus the strangers (bounded by invariant `P` and a geometric series), and
  `|subtreeKeys w|` is the Lemma 3.1 wire count below `w`.  This file replaces the scalar
  `stageCounts_algebraic` by an actual count on a `Placement`.
-/

public import AKS.Chvatal.StageNet
public import AKS.Chvatal.OutsiderInvariant
public import AKS.Chvatal.SchedulerLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Chvatal

open Finset

section Counting

variable {br d : ℕ}

theorem KBag.hi_le_pow (w : KBag br d) : w.hi ≤ br ^ d := by
  have hx : w.x + 1 ≤ br ^ w.l := w.hx
  calc w.hi = (w.x + 1) * bagSize br d w.l := rfl
    _ ≤ br ^ w.l * bagSize br d w.l := Nat.mul_le_mul_right _ hx
    _ = br ^ d := by
      simp only [bagSize]; rw [← pow_add]; congr 1; have := w.hl; omega

/-- **L1.** The keys addressed below a bag `w` number `br^(d - w.l)`. -/
theorem native_card (hbr : 1 ≤ br) (w : KBag br d) :
    (Finset.univ.filter fun κ : Fin (br ^ d) => w.Native κ id).card = br ^ (d - w.l) := by
  have hs : w.size = br ^ (d - w.l) := rfl
  have hhi := KBag.hi_le_pow w
  have hhs := KBag.hi_eq_lo_add_size w
  rw [← Finset.card_range (br ^ (d - w.l))]
  apply Finset.card_bij (fun κ _ => κ.val - w.lo)
  · intro κ hκ
    have := (KBag.native_iff w κ id hbr).mp (Finset.mem_filter.mp hκ).2
    simp only [id_eq] at this
    rw [Finset.mem_range, ← hs]; omega
  · intro κ hκ κ' hκ' h
    have h1 := (KBag.native_iff w κ id hbr).mp (Finset.mem_filter.mp hκ).2
    have h2 := (KBag.native_iff w κ' id hbr).mp (Finset.mem_filter.mp hκ').2
    simp only [id_eq] at h1 h2
    exact Fin.ext (by omega)
  · intro y hy
    rw [Finset.mem_range, ← hs] at hy
    refine ⟨⟨w.lo + y, by omega⟩, ?_, by simp⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [KBag.native_iff w _ id hbr]
    simp only [id_eq]; omega

variable (br d) in
/-- Bags at depth `h` below `w`: level `w.l + h` with ancestor `h` equal to `w`. -/
def descendants (hbr : 1 ≤ br) (w : KBag br d) (h : ℕ) : Finset (KBag br d) :=
  Finset.univ.filter fun z => z.l = w.l + h ∧ z.ancestor h hbr = w

theorem mem_descendants (hbr : 1 ≤ br) (w : KBag br d) (h : ℕ) (z : KBag br d) :
    z ∈ descendants br d hbr w h ↔ z.l = w.l + h ∧ z.x / br ^ h = w.x := by
  unfold descendants
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, hl, ha⟩
    refine ⟨hl, ?_⟩
    have := congrArg KBag.x ha
    simpa [KBag.ancestor] using this
  · rintro ⟨hl, hx⟩
    refine ⟨Finset.mem_univ _, hl, ?_⟩
    apply KBag.ext
    · show z.l - h = w.l; omega
    · exact hx

/-- **L2 (count).** There are `br^h` bags `h` levels below `w`. -/
theorem descendants_card (hbr : 1 ≤ br) (w : KBag br d) (h : ℕ) (hh : w.l + h ≤ d) :
    (descendants br d hbr w h).card = br ^ h := by
  have hB : 0 < br ^ h := Nat.pow_pos hbr
  rw [← Finset.card_range (br ^ h)]
  apply Finset.card_bij (fun z _ => z.x - br ^ h * w.x)
  · intro z hz
    rw [mem_descendants] at hz
    have e1 := Nat.div_add_mod z.x (br ^ h)
    rw [hz.2] at e1
    have e2 := Nat.mod_lt z.x hB
    rw [Finset.mem_range]
    generalize br ^ h * w.x = m at *
    omega
  · intro z hz z' hz' e
    rw [mem_descendants] at hz hz'
    have e1 := Nat.div_add_mod z.x (br ^ h)
    have e2 := Nat.div_add_mod z'.x (br ^ h)
    rw [hz.2] at e1; rw [hz'.2] at e2
    simp only at e
    apply KBag.ext
    · omega
    · generalize z.x % br ^ h = r1 at *
      generalize z'.x % br ^ h = r2 at *
      generalize br ^ h * w.x = m at *
      omega
  · intro y hy
    rw [Finset.mem_range] at hy
    have hxlt : br ^ h * w.x + y < br ^ (w.l + h) := by
      have hx : w.x + 1 ≤ br ^ w.l := w.hx
      calc br ^ h * w.x + y < br ^ h * w.x + br ^ h := by omega
        _ = br ^ h * (w.x + 1) := by ring
        _ ≤ br ^ h * br ^ w.l := Nat.mul_le_mul_left _ hx
        _ = br ^ (w.l + h) := by rw [← pow_add, Nat.add_comm]
    refine ⟨⟨w.l + h, br ^ h * w.x + y, hh, hxlt⟩, ?_, ?_⟩
    · rw [mem_descendants]
      refine ⟨rfl, ?_⟩
      show (br ^ h * w.x + y) / br ^ h = w.x
      rw [Nat.mul_add_div hB, Nat.div_eq_of_lt hy, add_zero]
    · show br ^ h * w.x + y - br ^ h * w.x = y
      omega

theorem descendants_disjoint (hbr : 1 ≤ br) (w : KBag br d) {h h' : ℕ} (hne : h ≠ h') :
    Disjoint (descendants br d hbr w h) (descendants br d hbr w h') := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [mem_descendants] at hz hz'
  omega

variable (br d) in
/-- All bags in the subtree of `w` (levels `w.l, …, d`). -/
def subtreeBags (hbr : 1 ≤ br) (w : KBag br d) : Finset (KBag br d) :=
  (Finset.range (d - w.l + 1)).biUnion (descendants br d hbr w)

variable (br d) in
/-- All keys sitting at some node of the subtree of `w`. -/
def subtreeKeys (pl : Placement br d) (hbr : 1 ≤ br) (w : KBag br d) :
    Finset (Fin (br ^ d)) :=
  (subtreeBags br d hbr w).biUnion pl.regs

theorem mem_subtreeBags (hbr : 1 ≤ br) (w : KBag br d) (z : KBag br d) :
    z ∈ subtreeBags br d hbr w ↔ ∃ h, h < d - w.l + 1 ∧ z.l = w.l + h ∧ z.x / br ^ h = w.x := by
  unfold subtreeBags
  simp only [Finset.mem_biUnion, Finset.mem_range, mem_descendants]

theorem subtreeBags_l_ge (hbr : 1 ≤ br) (w z : KBag br d) (hz : z ∈ subtreeBags br d hbr w) :
    w.l ≤ z.l := by
  obtain ⟨h, -, hl, -⟩ := (mem_subtreeBags hbr w z).mp hz
  omega

/-- **L2 (disjointness and union).** The registers on the bags of a subtree are pairwise
disjoint; `subtreeKeys` is their union, so its size is `∑_h br^h · a(w.l + h)`. -/
theorem card_subtreeKeys (hbr : 1 ≤ br) (pl : Placement br d) (w : KBag br d) (a : ℕ → ℕ)
    (hcard : ∀ b : KBag br d, (pl.regs b).card = a b.l) :
    (subtreeKeys br d pl hbr w).card =
      ∑ h ∈ Finset.range (d - w.l + 1), br ^ h * a (w.l + h) := by
  unfold subtreeKeys subtreeBags
  rw [Finset.card_biUnion (fun z _ z' _ hne => pl.disjoint z z' hne)]
  rw [Finset.sum_biUnion (fun h _ h' _ hne => descendants_disjoint hbr w hne)]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mem_range] at hh
  have hc := descendants_card hbr w h (by have := w.hl; omega)
  calc ∑ z ∈ descendants br d hbr w h, (pl.regs z).card
      = ∑ z ∈ descendants br d hbr w h, a (w.l + h) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hcard z, ((mem_descendants hbr w h z).mp hz).1]
    _ = br ^ h * a (w.l + h) := by rw [Finset.sum_const, hc, smul_eq_mul]

/-- A key on a node `z` at depth `h` below `w` that is not addressed below `w` is a stranger of
order `h + 1` of `z`. -/
theorem bad_card_le_strangers (hbr : 1 ≤ br) (w z : KBag br d) (h : ℕ)
    (hz : z ∈ descendants br d hbr w h) (S : Finset (Fin (br ^ d))) :
    (S.filter fun κ => ¬ w.Native κ id).card ≤ z.strangers (h + 1) id S hbr := by
  unfold KBag.strangers
  apply Finset.card_le_card
  intro κ hκ
  rw [Finset.mem_filter] at hκ ⊢
  refine ⟨hκ.1, ?_⟩
  have hanc : z.ancestor h hbr = w := ((Finset.mem_filter.mp hz).2).2
  right
  simpa [hanc] using hκ.2

end Counting

section Lemma41

variable (p : ScheduleParams) (ip : InvariantParams) (d : ℕ) (sched : LevelSchedule p d)
  (t : ℕ)

/-- **L3 (strangers in a subtree).** The keys of `subtreeKeys w` not addressed below `w` number at
most `∑_h k^h · min(μ δ^h c(w.l+h,t), a(w.l+h))`. -/
theorem subtree_bad_le (pl : Placement p.br d) (a : ℕ → ℕ)
    (hcard : ∀ b : KBag p.br d, (pl.regs b).card = a b.l)
    (hP : OutsiderBound p ip d sched t pl id) (w : KBag p.br d) :
    (((subtreeKeys p.br d pl (br_ge_one p) w).filter fun κ => ¬ w.Native κ id).card : ℚ) ≤
      ∑ h ∈ Finset.range (d - w.l + 1), (p.br : ℚ) ^ h *
        min (ip.mu * ip.delta ^ h * capacity p d (w.l + h) t) (a (w.l + h) : ℚ) := by
  have hbr := br_ge_one p
  unfold subtreeKeys subtreeBags
  rw [Finset.filter_biUnion]
  rw [Finset.card_biUnion (fun z _ z' _ hne =>
    Finset.disjoint_filter_filter (pl.disjoint z z' hne))]
  rw [Finset.sum_biUnion (fun h _ h' _ hne => descendants_disjoint hbr w hne)]
  push_cast
  apply Finset.sum_le_sum
  intro h hh
  rw [Finset.mem_range] at hh
  have hc := descendants_card hbr w h (by have := w.hl; omega)
  calc ∑ z ∈ descendants p.br d hbr w h,
        (((pl.regs z).filter fun κ => ¬ w.Native κ id).card : ℚ)
      ≤ ∑ z ∈ descendants p.br d hbr w h,
        min (ip.mu * ip.delta ^ h * capacity p d (w.l + h) t) (a (w.l + h) : ℚ) := by
        apply Finset.sum_le_sum
        intro z hz
        have hzl := ((mem_descendants hbr w h z).mp hz).1
        apply le_min
        · have h1 := bad_card_le_strangers hbr w z h hz (pl.regs z)
          have h2 := hP z h (by omega)
          have h3 : (((pl.regs z).filter fun κ => ¬ w.Native κ id).card : ℚ) ≤
              (z.strangers (h + 1) id (pl.regs z) hbr : ℚ) := by exact_mod_cast h1
          rw [hzl] at h2
          linarith
        · have : ((pl.regs z).filter fun κ => ¬ w.Native κ id).card ≤ a (w.l + h) := by
            rw [← hzl, ← hcard z]; exact Finset.card_filter_le _ _
          exact_mod_cast this
    _ = (p.br : ℚ) ^ h *
        min (ip.mu * ip.delta ^ h * capacity p d (w.l + h) t) (a (w.l + h) : ℚ) := by
        rw [Finset.sum_const, hc, nsmul_eq_mul]; push_cast; ring

/-- **L3 (parity form).** If levels of the wrong parity are empty, only `h` with
`(w.l + h) % 2 = t % 2` contribute. -/
theorem subtree_bad_le_parity (pl : Placement p.br d) (a : ℕ → ℕ)
    (hcard : ∀ b : KBag p.br d, (pl.regs b).card = a b.l)
    (hpar : ∀ l, l % 2 ≠ t % 2 → a l = 0)
    (hP : OutsiderBound p ip d sched t pl id) (w : KBag p.br d) :
    (((subtreeKeys p.br d pl (br_ge_one p) w).filter fun κ => ¬ w.Native κ id).card : ℚ) ≤
      ∑ h ∈ (Finset.range (d - w.l + 1)).filter (fun h => (w.l + h) % 2 = t % 2),
        (p.br : ℚ) ^ h * (ip.mu * ip.delta ^ h * capacity p d (w.l + h) t) := by
  refine (subtree_bad_le p ip d sched t pl a hcard hP w).trans ?_
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro h _
  have hk : (0 : ℚ) ≤ (p.br : ℚ) ^ h := by positivity
  have hb : 0 ≤ ip.mu * ip.delta ^ h * capacity p d (w.l + h) t :=
    mul_nonneg (mul_nonneg ip.mu_nonneg (pow_nonneg ip.delta_nonneg _))
      (capacity_pos p d _ t).le
  split_ifs with hh
  · exact mul_le_mul_of_nonneg_left (min_le_left _ _) hk
  · have := hpar (w.l + h) hh
    have h0 : min (ip.mu * ip.delta ^ h * capacity p d (w.l + h) t) (a (w.l + h) : ℚ) ≤ 0 := by
      refine (min_le_right _ _).trans ?_
      rw [this]; simp
    nlinarith

theorem capacity_add (m i : ℕ) :
    capacity p d (i + m) t = p.A ^ m * capacity p d i t := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, capacity_succ_level, ih]; ring

end Lemma41

section Geometric

theorem odd_sum_reindex (x : ℚ) (n : ℕ) :
    ∑ h ∈ Finset.range (2 * n), (if h % 2 = 1 then x ^ h else 0) =
      ∑ m ∈ Finset.range n, x ^ (2 * m + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    have h1 : (2 * n) % 2 ≠ 1 := by omega
    have h2 : (2 * n + 1) % 2 = 1 := by omega
    simp [h2]

/-- Partial sums of the odd-power series are bounded by the infinite series
`x / (1 - x²)`. -/
theorem odd_geom_le (x : ℚ) (hx0 : 0 ≤ x) (hx : x ^ 2 < 1) (M : ℕ) :
    ∑ h ∈ (Finset.range M).filter (fun h => h % 2 = 1), x ^ h ≤ x / (1 - x ^ 2) := by
  have h1 : 0 < 1 - x ^ 2 := by linarith
  rw [Finset.sum_filter]
  calc ∑ h ∈ Finset.range M, (if h % 2 = 1 then x ^ h else 0)
      ≤ ∑ h ∈ Finset.range (2 * M), (if h % 2 = 1 then x ^ h else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro h hh; rw [Finset.mem_range] at hh ⊢; omega
        · intro h _ _; split_ifs <;> positivity
    _ = ∑ m ∈ Finset.range M, x ^ (2 * m + 1) := odd_sum_reindex x M
    _ = x * ∑ m ∈ Finset.range M, (x ^ 2) ^ m := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        rw [← pow_mul]; ring
    _ ≤ x / (1 - x ^ 2) := by
        have hg := geom_sum_mul_neg (x ^ 2) M
        have hpow : 0 ≤ (x ^ 2) ^ M := by positivity
        have hS : ∑ m ∈ Finset.range M, (x ^ 2) ^ m ≤ 1 / (1 - x ^ 2) := by
          rw [le_div_iff₀ h1]; linarith
        calc x * ∑ m ∈ Finset.range M, (x ^ 2) ^ m ≤ x * (1 / (1 - x ^ 2)) :=
              mul_le_mul_of_nonneg_left hS hx0
          _ = x / (1 - x ^ 2) := by ring

end Geometric

section Lemma41b

variable (p : ScheduleParams) (ip : InvariantParams) (d : ℕ) (sched : LevelSchedule p d)
  (t : ℕ)

/-- **L4 (geometric sum).** With `c(i+m,t) = A^m c(i,t)` and `(δ k A)² < 1`, the odd-depth
stranger series below a child is at most `μ · siblingFactor · c(i,t)`. -/
theorem sibling_sum_le (hδ : ip.delta ^ 2 * (p.br : ℚ) ^ 2 * p.A ^ 2 < 1) (i M : ℕ) :
    ∑ h ∈ (Finset.range M).filter (fun h => h % 2 = 1),
        (p.br : ℚ) ^ h * (ip.mu * ip.delta ^ h * capacity p d (i + 1 + h) t) ≤
      ip.mu * siblingFactor p ip * capacity p d i t := by
  set x : ℚ := ip.delta * (p.br : ℚ) * p.A with hx
  have hx0 : 0 ≤ x := by
    have := p.A_pos; have := p.br_cast_pos; have := ip.hdelta_pos
    positivity
  have hx2 : x ^ 2 = ip.delta ^ 2 * (p.br : ℚ) ^ 2 * p.A ^ 2 := by rw [hx]; ring
  have hxlt : x ^ 2 < 1 := by rw [hx2]; exact hδ
  have hterm : ∀ h : ℕ, (p.br : ℚ) ^ h * (ip.mu * ip.delta ^ h * capacity p d (i + 1 + h) t) =
      (ip.mu * p.A * capacity p d i t) * x ^ h := by
    intro h
    rw [show i + 1 + h = i + (1 + h) by ring, capacity_add, hx]; ring
  rw [Finset.sum_congr rfl (fun h _ => hterm h), ← Finset.mul_sum]
  have hc := capacity_pos p d i t
  have hmu := ip.hmu_pos
  have hA := p.A_pos
  calc (ip.mu * p.A * capacity p d i t) *
        ∑ h ∈ (Finset.range M).filter (fun h => h % 2 = 1), x ^ h
      ≤ (ip.mu * p.A * capacity p d i t) * (x / (1 - x ^ 2)) :=
        mul_le_mul_of_nonneg_left (odd_geom_le x hx0 hxlt M) (by positivity)
    _ = ip.mu * siblingFactor p ip * capacity p d i t := by
        unfold siblingFactor
        rw [hx2, hx]; ring

/-- Reindexing of the Lemma 3.1 wire sum below `u`. -/
theorem wires_reindex (a : ℕ → ℕ) (c : ℕ) (n : ℕ) (hc : c < n) (r : ℚ) :
    (∑ l ∈ Finset.Ioc c n, r ^ (l - c - 1) * (a l : ℚ)) =
      ∑ h ∈ Finset.range (n - (c + 1) + 1), r ^ h * (a (c + 1 + h) : ℚ) := by
  apply Finset.sum_nbij' (fun l => l - c - 1) (fun h => c + 1 + h)
  · intro l hl; simp only [Finset.mem_Ioc] at hl; simp only [Finset.mem_range]; omega
  · intro h hh
    simp only [Finset.mem_range] at hh
    simp only [Finset.mem_Ioc]; omega
  · intro l hl; simp only [Finset.mem_Ioc] at hl; omega
  · intro h _; omega
  · intro l hl
    simp only [Finset.mem_Ioc] at hl
    have : c + 1 + (l - c - 1) = l := by omega
    rw [this]

/-- Keys of `u` addressed below its child `w` number at most `k^(d-u.l-1)` (L1). -/
theorem keys_below_child_le_pow (pl : Placement p.br d) (u : KBag p.br d) (hul : u.l < d)
    (j : Fin p.br) :
    ((pl.regs u).filter fun κ => (u.child j.val j.isLt hul).Native κ id).card ≤
      p.br ^ (d - u.l - 1) := by
  have hbr := br_ge_one p
  have h1 := native_card hbr (u.child j.val j.isLt hul)
  have hl : (u.child j.val j.isLt hul).l = u.l + 1 := rfl
  rw [hl, show d - (u.l + 1) = d - u.l - 1 by omega] at h1
  rw [← h1]
  apply Finset.card_le_card
  intro κ hκ
  rw [Finset.mem_filter] at hκ ⊢
  exact ⟨Finset.mem_univ _, hκ.2⟩

/-- **L6.** If `u` has no occupied descendants, the keys of `u` addressed below `w` number at most
`k^(d-u.l-1)` (this is just L1; the emptiness hypothesis is not needed). -/
theorem keys_below_child_le_bottom (pl : Placement p.br d) (a : ℕ → ℕ)
    (_hcard : ∀ b : KBag p.br d, (pl.regs b).card = a b.l) (u : KBag p.br d) (hul : u.l < d)
    (_hempty : ∀ l, u.l < l → a l = 0) (j : Fin p.br) :
    ((pl.regs u).filter fun κ => (u.child j.val j.isLt hul).Native κ id).card ≤
      p.br ^ (d - u.l - 1) :=
  keys_below_child_le_pow p d pl u hul j

/-- **L5 (Lemma 4.1, real).**  A node `u` on an occupied level (`u.l % 2 = t % 2`) holds at most
`c/k + μ · siblingFactor · c` keys addressed below any one child `w`, where `c = c(u.l, t)`,
under invariant `P` for the actual placement and the Lemma 3.1 wire count below `u`. -/
theorem keys_below_child_le (pl : Placement p.br d) (a : ℕ → ℕ)
    (hcard : ∀ b : KBag p.br d, (pl.regs b).card = a b.l)
    (hpar : ∀ l, l % 2 ≠ t % 2 → a l = 0)
    (hP : OutsiderBound p ip d sched t pl id)
    (hδ : ip.delta ^ 2 * (p.br : ℚ) ^ 2 * p.A ^ 2 < 1)
    (u : KBag p.br d) (hul : u.l < d) (j : Fin p.br)
    (hwires : (∑ l ∈ Finset.Ioc u.l d, (p.br : ℚ) ^ (l - u.l - 1) * (a l : ℚ)) =
      ((p.br : ℚ) ^ d / (p.br : ℚ) ^ u.l - capacity p d u.l t) / p.br)
    (hu : u.l % 2 = t % 2) :
    (((pl.regs u).filter fun κ => (u.child j.val j.isLt hul).Native κ id).card : ℚ) ≤
      capacity p d u.l t / p.br + ip.mu * siblingFactor p ip * capacity p d u.l t := by
  have hbr := br_ge_one p
  set w : KBag p.br d := u.child j.val j.isLt hul with hw
  have hwl : w.l = u.l + 1 := rfl
  set S := subtreeKeys p.br d pl hbr w with hS
  set X := (pl.regs u).filter fun κ => w.Native κ id with hX
  set A := (Finset.univ : Finset (Fin (p.br ^ d))).filter fun κ => w.Native κ id with hA
  have hAcard : A.card = p.br ^ (d - u.l - 1) := by
    have h1 := native_card hbr w
    rw [hwl, show d - (u.l + 1) = d - u.l - 1 by omega] at h1
    exact h1
  have hXA : X ⊆ A := by
    intro κ hκ
    rw [hX, Finset.mem_filter] at hκ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hκ.2⟩
  have hSA : S.filter (fun κ => w.Native κ id) ⊆ A := by
    intro κ hκ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hκ).2⟩
  have hdisjS : Disjoint (pl.regs u) S := by
    rw [hS, subtreeKeys, Finset.disjoint_biUnion_right]
    intro z hz
    refine pl.disjoint u z ?_
    intro e
    have := subtreeBags_l_ge hbr w z hz
    rw [← e] at this
    omega
  have hdisj : Disjoint X (S.filter fun κ => w.Native κ id) :=
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hdisjS)
  have hcardXS : X.card + (S.filter fun κ => w.Native κ id).card ≤ A.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.union_subset hXA hSA)
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun κ => w.Native κ id)
  have hScard : (S.card : ℚ) =
      ((p.br : ℚ) ^ d / (p.br : ℚ) ^ u.l - capacity p d u.l t) / p.br := by
    rw [← hwires, hS, card_subtreeKeys hbr pl w a hcard, wires_reindex a u.l d hul (p.br : ℚ)]
    push_cast
    rw [hwl]
  -- the strangers bound
  have hbad := subtree_bad_le_parity p ip d sched t pl a hcard hpar hP w
  have hfilt : (Finset.range (d - w.l + 1)).filter (fun h => (w.l + h) % 2 = t % 2) =
      (Finset.range (d - w.l + 1)).filter (fun h => h % 2 = 1) :=
    Finset.filter_congr (fun h _ => by rw [hwl]; omega)
  have hbad' : (((S.filter fun κ => ¬ w.Native κ id).card : ℕ) : ℚ) ≤
      ip.mu * siblingFactor p ip * capacity p d u.l t := by
    refine hbad.trans ?_
    rw [hfilt, hwl]
    exact sibling_sum_le p ip d t hδ u.l _
  -- arithmetic
  have hAq : ((A.card : ℕ) : ℚ) = (p.br : ℚ) ^ d / (p.br : ℚ) ^ u.l / p.br := by
    rw [hAcard]
    have hk := p.br_cast_pos
    have hpow : (p.br : ℚ) ^ d = (p.br : ℚ) ^ (d - u.l - 1) * p.br * (p.br : ℚ) ^ u.l := by
      rw [← pow_succ, ← pow_add]; congr 1; omega
    push_cast
    rw [hpow]
    field_simp
  have c1 : ((X.card + (S.filter fun κ => w.Native κ id).card : ℕ) : ℚ) ≤ A.card := by
    exact_mod_cast hcardXS
  have c2 : (((S.filter fun κ => w.Native κ id).card + (S.filter fun κ => ¬ w.Native κ id).card
      : ℕ) : ℚ) = S.card := by exact_mod_cast hsplit
  push_cast at c1 c2
  have hk := p.br_cast_pos
  have hid : capacity p d u.l t / p.br =
      (p.br : ℚ) ^ d / (p.br : ℚ) ^ u.l / p.br -
        ((p.br : ℚ) ^ d / (p.br : ℚ) ^ u.l - capacity p d u.l t) / p.br := by ring
  push_cast at hbad' hAq
  linarith

end Lemma41b

end Chvatal
