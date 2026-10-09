module

public import AKS.Chvatal.StageNet
public import AKS.Chvatal.OutsiderInduction
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! Chvátal Lemma 4.1, counting form (keys are their own addresses, `perm := id`): a node on an
occupied level holds at most `(1/k + μ·siblingFactor)·c(i,t)` keys addressed below any one child
`w`.  We count the `k^(d-i-1)` keys addressed below `w` via the subtree of `w`, invariant `P` and
the Lemma 3.1 wire count. -/

namespace Chvatal

open Finset
open scoped Classical

section Counting

variable {br d : ℕ}

theorem KBag.hi_le_pow (w : KBag br d) : w.hi ≤ br ^ d :=
  calc w.hi = (w.x + 1) * bagSize br d w.l := rfl
    _ ≤ br ^ w.l * bagSize br d w.l := Nat.mul_le_mul_right _ w.hx
    _ = br ^ d := by simp only [bagSize]; rw [← pow_add]; congr 1; have := w.hl; omega

/-- The keys addressed below a bag `w` number `br^(d - w.l)`. -/
theorem native_card (hbr : 1 ≤ br) (w : KBag br d) :
    (Finset.univ.filter fun κ : Fin (br ^ d) => w.Native κ id).card = br ^ (d - w.l) := by
  have hs : w.size = br ^ (d - w.l) := rfl
  have hhi := KBag.hi_le_pow w
  have hhs := KBag.hi_eq_lo_add_size w
  have hn := fun κ : Fin (br ^ d) => KBag.native_iff w κ id hbr
  simp only [id_eq] at hn
  rw [← Finset.card_range (br ^ (d - w.l))]
  apply Finset.card_bij (fun κ _ => κ.val - w.lo)
  · intro κ hκ
    have := (hn κ).1 (mem_filter.1 hκ).2
    rw [mem_range, ← hs]; omega
  · intro κ hκ κ' hκ' h
    have := (hn κ).1 (mem_filter.1 hκ).2
    have := (hn κ').1 (mem_filter.1 hκ').2
    exact Fin.ext (by omega)
  · intro y hy
    rw [mem_range, ← hs] at hy
    exact ⟨⟨w.lo + y, by omega⟩, mem_filter.2 ⟨mem_univ _, (hn _).2 (by simp; omega)⟩, by simp⟩

variable (br d) in
/-- Bags at depth `h` below `w`. -/
def descendants (hbr : 1 ≤ br) (w : KBag br d) (h : ℕ) : Finset (KBag br d) :=
  Finset.univ.filter fun z => z.l = w.l + h ∧ z.ancestor h hbr = w

theorem mem_descendants (hbr : 1 ≤ br) (w : KBag br d) (h : ℕ) (z : KBag br d) :
    z ∈ descendants br d hbr w h ↔ z.l = w.l + h ∧ z.x / br ^ h = w.x := by
  unfold descendants
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, hl, ha⟩
    exact ⟨hl, by simpa [KBag.ancestor] using congrArg KBag.x ha⟩
  · rintro ⟨hl, hx⟩
    exact ⟨mem_univ _, hl, KBag.ext (by show z.l - h = w.l; omega) hx⟩

/-- There are `br^h` bags `h` levels below `w`. -/
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
    have hxlt : br ^ h * w.x + y < br ^ (w.l + h) :=
      calc br ^ h * w.x + y < br ^ h * (w.x + 1) := by rw [mul_add_one]; omega
        _ ≤ br ^ h * br ^ w.l := Nat.mul_le_mul_left _ w.hx
        _ = br ^ (w.l + h) := by rw [← pow_add, Nat.add_comm]
    refine ⟨⟨w.l + h, br ^ h * w.x + y, hh, hxlt⟩, ?_, by show br ^ h * w.x + y - br ^ h * w.x = y; omega⟩
    rw [mem_descendants]
    exact ⟨rfl, by show (br ^ h * w.x + y) / br ^ h = w.x; rw [Nat.mul_add_div hB, Nat.div_eq_of_lt hy, add_zero]⟩

theorem descendants_disjoint (hbr : 1 ≤ br) (w : KBag br d) {h h' : ℕ} (hne : h ≠ h') :
    Disjoint (descendants br d hbr w h) (descendants br d hbr w h') := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [mem_descendants] at hz hz'
  omega

variable (br d) in
/-- All bags in the subtree of `w`. -/
def subtreeBags (hbr : 1 ≤ br) (w : KBag br d) : Finset (KBag br d) :=
  (Finset.range (d - w.l + 1)).biUnion (descendants br d hbr w)

variable (br d) in
/-- All keys sitting at some node of the subtree of `w`. -/
def subtreeKeys (pl : Placement br d) (hbr : 1 ≤ br) (w : KBag br d) : Finset (Fin (br ^ d)) :=
  (subtreeBags br d hbr w).biUnion pl.regs

theorem subtreeBags_l_ge (hbr : 1 ≤ br) (w z : KBag br d) (hz : z ∈ subtreeBags br d hbr w) :
    w.l ≤ z.l := by
  obtain ⟨h, -, hz⟩ := Finset.mem_biUnion.1 hz
  have := ((mem_descendants hbr w h z).1 hz).1
  omega

/-- `subtreeKeys` is the disjoint union of the node registers, of size `∑_h br^h · a(w.l + h)`. -/
theorem card_subtreeKeys (hbr : 1 ≤ br) (pl : Placement br d) (w : KBag br d) (a : ℕ → ℕ)
    (hcard : ∀ b : KBag br d, (pl.regs b).card = a b.l) :
    (subtreeKeys br d pl hbr w).card =
      ∑ h ∈ Finset.range (d - w.l + 1), br ^ h * a (w.l + h) := by
  unfold subtreeKeys subtreeBags
  rw [Finset.card_biUnion (fun z _ z' _ hne => pl.disjoint z z' hne),
    Finset.sum_biUnion (fun h _ h' _ hne => descendants_disjoint hbr w hne)]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.mem_range] at hh
  rw [← descendants_card hbr w h (by have := w.hl; omega), ← smul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_congr rfl fun z hz => by
    rw [hcard z, ((mem_descendants hbr w h z).mp hz).1]

end Counting

section Lemma41

variable (p : ScheduleParams) (ip : InvariantParams) (d : ℕ) (sched : LevelSchedule p d)
  (t : ℕ)

/-- Strangers in a subtree: the keys of `subtreeKeys w` not addressed below `w` number at
most `∑_h k^h · min(μ δ^h c(w.l+h,t), a(w.l+h))`. -/
theorem subtree_bad_le (pl : Placement p.br d) (a : ℕ → ℕ)
    (hcard : ∀ b : KBag p.br d, (pl.regs b).card = a b.l)
    (hP : OutsiderBoundLe p ip d sched t pl id) (w : KBag p.br d) :
    (((subtreeKeys p.br d pl (br_ge_one p) w).filter fun κ => ¬ w.Native κ id).card : ℚ) ≤
      ∑ h ∈ Finset.range (d - w.l + 1), (p.br : ℚ) ^ h *
        min (ip.mu * ip.delta ^ h * capacity p d (w.l + h) t) (a (w.l + h) : ℚ) := by
  have hbr := br_ge_one p
  unfold subtreeKeys subtreeBags
  rw [Finset.filter_biUnion, Finset.card_biUnion (fun z _ z' _ hne =>
    Finset.disjoint_filter_filter (pl.disjoint z z' hne)),
    Finset.sum_biUnion (fun h _ h' _ hne => descendants_disjoint hbr w hne)]
  push_cast
  refine Finset.sum_le_sum fun h hh => ?_
  rw [Finset.mem_range] at hh
  have hc := descendants_card hbr w h (by have := w.hl; omega)
  rw [show (p.br : ℚ) ^ h = ((descendants p.br d hbr w h).card : ℚ) by rw [hc]; push_cast; rfl,
    ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun z hz => le_min ?_ ?_
  · have hzl := ((mem_descendants hbr w h z).mp hz).1
    have h1 : ((pl.regs z).filter fun κ => ¬ w.Native κ id).card ≤ z.strangers (h + 1) id (pl.regs z) hbr := by
      unfold KBag.strangers
      refine Finset.card_le_card fun κ hκ => ?_
      rw [Finset.mem_filter] at hκ ⊢
      refine ⟨hκ.1, Or.inr ?_⟩
      simpa [((Finset.mem_filter.mp hz).2).2] using hκ.2
    have h2 := hP z h (by omega)
    rw [hzl] at h2
    exact le_trans (by exact_mod_cast h1) h2
  · rw [← ((mem_descendants hbr w h z).mp hz).1, ← hcard z]
    exact_mod_cast Finset.card_filter_le _ _

/-- Parity form: if levels of the wrong parity are empty, only `h` with `(w.l + h) % 2 = t % 2`
contribute. -/
theorem subtree_bad_le_parity (pl : Placement p.br d) (a : ℕ → ℕ)
    (hcard : ∀ b : KBag p.br d, (pl.regs b).card = a b.l)
    (hpar : ∀ l, l % 2 ≠ t % 2 → a l = 0)
    (hP : OutsiderBoundLe p ip d sched t pl id) (w : KBag p.br d) :
    (((subtreeKeys p.br d pl (br_ge_one p) w).filter fun κ => ¬ w.Native κ id).card : ℚ) ≤
      ∑ h ∈ (Finset.range (d - w.l + 1)).filter (fun h => (w.l + h) % 2 = t % 2),
        (p.br : ℚ) ^ h * (ip.mu * ip.delta ^ h * capacity p d (w.l + h) t) := by
  refine (subtree_bad_le p ip d sched t pl a hcard hP w).trans ?_
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum fun h _ => ?_
  have hk : (0 : ℚ) ≤ (p.br : ℚ) ^ h := by positivity
  split_ifs with hh
  · exact mul_le_mul_of_nonneg_left (min_le_left _ _) hk
  · have := hpar (w.l + h) hh
    have h0 : min (ip.mu * ip.delta ^ h * capacity p d (w.l + h) t) (a (w.l + h) : ℚ) ≤ 0 :=
      (min_le_right _ _).trans (by rw [this]; simp)
    nlinarith

theorem capacity_add (m i : ℕ) :
    capacity p d (i + m) t = p.A ^ m * capacity p d i t := by
  induction m with
  | zero => simp
  | succ m ih => rw [← add_assoc, capacity_succ_level, ih]; ring

end Lemma41

/-- Partial sums of the odd-power series are bounded by `x / (1 - x²)`. -/
theorem odd_geom_le (x : ℚ) (hx0 : 0 ≤ x) (hx : x ^ 2 < 1) (M : ℕ) :
    ∑ h ∈ (Finset.range M).filter (fun h => h % 2 = 1), x ^ h ≤ x / (1 - x ^ 2) := by
  have h1 : 0 < 1 - x ^ 2 := by linarith
  have hS : ∑ m ∈ Finset.range M, (x ^ 2) ^ m ≤ 1 / (1 - x ^ 2) := by
    have hg := geom_sum_mul_neg (x ^ 2) M
    have hpow : 0 ≤ (x ^ 2) ^ M := by positivity
    rw [le_div_iff₀ h1]; linarith
  have hodd : ∀ n : ℕ, ∑ h ∈ Finset.range (2 * n), (if h % 2 = 1 then x ^ h else 0) =
      ∑ m ∈ Finset.range n, x ^ (2 * m + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, ih]
      have h2 : (2 * n + 1) % 2 = 1 := by omega
      simp [h2]
  rw [Finset.sum_filter]
  calc ∑ h ∈ Finset.range M, (if h % 2 = 1 then x ^ h else 0)
      ≤ ∑ h ∈ Finset.range (2 * M), (if h % 2 = 1 then x ^ h else 0) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun h _ _ => by split_ifs <;> positivity
        intro h hh; rw [Finset.mem_range] at hh ⊢; omega
    _ = x * ∑ m ∈ Finset.range M, (x ^ 2) ^ m := by
        rw [hodd, Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by rw [← pow_mul]; ring
    _ ≤ x * (1 / (1 - x ^ 2)) := mul_le_mul_of_nonneg_left hS hx0
    _ = x / (1 - x ^ 2) := by ring

section Lemma41b

variable (p : ScheduleParams) (ip : InvariantParams) (d : ℕ) (sched : LevelSchedule p d)
  (t : ℕ)

/-- Geometric sum: with `c(i+m,t) = A^m c(i,t)` and `(δ k A)² < 1`, the odd-depth stranger series
below a child is at most `μ · siblingFactor · c(i,t)`. -/
theorem sibling_sum_le (hδ : ip.delta ^ 2 * (p.br : ℚ) ^ 2 * p.A ^ 2 < 1) (i M : ℕ) :
    ∑ h ∈ (Finset.range M).filter (fun h => h % 2 = 1),
        (p.br : ℚ) ^ h * (ip.mu * ip.delta ^ h * capacity p d (i + 1 + h) t) ≤
      ip.mu * siblingFactor p ip * capacity p d i t := by
  set x : ℚ := ip.delta * (p.br : ℚ) * p.A with hx
  have hmu := ip.hmu_pos
  have hA := p.A_pos
  have hc := capacity_pos p d i t
  have hx0 : 0 ≤ x := by
    have := p.br_cast_pos; have := ip.hdelta_pos
    positivity
  have hx2 : x ^ 2 = ip.delta ^ 2 * (p.br : ℚ) ^ 2 * p.A ^ 2 := by rw [hx]; ring
  have hterm : ∀ h : ℕ, (p.br : ℚ) ^ h * (ip.mu * ip.delta ^ h * capacity p d (i + 1 + h) t) =
      (ip.mu * p.A * capacity p d i t) * x ^ h := by
    intro h
    rw [show i + 1 + h = i + (1 + h) by ring, capacity_add, hx]; ring
  rw [Finset.sum_congr rfl (fun h _ => hterm h), ← Finset.mul_sum]
  calc (ip.mu * p.A * capacity p d i t) *
        ∑ h ∈ (Finset.range M).filter (fun h => h % 2 = 1), x ^ h
      ≤ (ip.mu * p.A * capacity p d i t) * (x / (1 - x ^ 2)) :=
        mul_le_mul_of_nonneg_left (odd_geom_le x hx0 (hx2 ▸ hδ) M) (by positivity)
    _ = ip.mu * siblingFactor p ip * capacity p d i t := by
        unfold siblingFactor
        rw [hx2, hx]; ring

/-- Reindexing of the Lemma 3.1 wire sum below `u`. -/
theorem wires_reindex (a : ℕ → ℕ) (c : ℕ) (n : ℕ) (hc : c < n) (r : ℚ) :
    (∑ l ∈ Finset.Ioc c n, r ^ (l - c - 1) * (a l : ℚ)) =
      ∑ h ∈ Finset.range (n - (c + 1) + 1), r ^ h * (a (c + 1 + h) : ℚ) := by
  apply Finset.sum_nbij' (fun l => l - c - 1) (fun h => c + 1 + h)
  · intro l hl; simp only [Finset.mem_Ioc] at hl; simp only [Finset.mem_range]; omega
  · intro h hh; simp only [Finset.mem_range] at hh; simp only [Finset.mem_Ioc]; omega
  · intro l hl; simp only [Finset.mem_Ioc] at hl; omega
  · intro h _; omega
  · intro l hl
    simp only [Finset.mem_Ioc] at hl
    rw [show c + 1 + (l - c - 1) = l by omega]

/-- Keys of `u` addressed below its child `w` number at most `k^(d-u.l-1)`. -/
theorem keys_below_child_le_pow (pl : Placement p.br d) (u : KBag p.br d) (hul : u.l < d)
    (j : Fin p.br) :
    ((pl.regs u).filter fun κ => (u.child j.val j.isLt hul).Native κ id).card ≤
      p.br ^ (d - u.l - 1) := by
  have h1 := native_card (br_ge_one p) (u.child j.val j.isLt hul)
  rw [show (u.child j.val j.isLt hul).l = u.l + 1 from rfl,
    show d - (u.l + 1) = d - u.l - 1 by omega] at h1
  rw [← h1]
  exact Finset.card_le_card fun κ hκ => by
    rw [Finset.mem_filter] at hκ ⊢
    exact ⟨mem_univ _, hκ.2⟩

/-- **Lemma 4.1 (real).**  A node `u` on an occupied level (`u.l % 2 = t % 2`) holds at most
`c/k + μ · siblingFactor · c` keys addressed below any one child `w`, where `c = c(u.l, t)`,
under invariant `P` for the actual placement and the Lemma 3.1 wire count below `u`. -/
theorem keys_below_child_le (pl : Placement p.br d) (a : ℕ → ℕ)
    (hcard : ∀ b : KBag p.br d, (pl.regs b).card = a b.l)
    (hpar : ∀ l, l % 2 ≠ t % 2 → a l = 0)
    (hP : OutsiderBoundLe p ip d sched t pl id)
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
  set Y := S.filter fun κ => w.Native κ id with hY
  set A := (Finset.univ : Finset (Fin (p.br ^ d))).filter fun κ => w.Native κ id with hA
  have hAcard : A.card = p.br ^ (d - u.l - 1) := by
    have h1 := native_card hbr w
    rwa [hwl, show d - (u.l + 1) = d - u.l - 1 by omega] at h1
  have hdisjS : Disjoint (pl.regs u) S := by
    rw [hS, subtreeKeys, Finset.disjoint_biUnion_right]
    intro z hz
    refine pl.disjoint u z fun e => ?_
    have := subtreeBags_l_ge hbr w z hz
    rw [← e] at this
    omega
  have hcardXY : X.card + Y.card ≤ A.card := by
    rw [← Finset.card_union_of_disjoint
      (Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hdisjS))]
    refine Finset.card_le_card (Finset.union_subset ?_ ?_) <;>
      exact fun κ hκ => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hκ).2⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun κ => w.Native κ id)
  have hScard : (S.card : ℚ) =
      ((p.br : ℚ) ^ d / (p.br : ℚ) ^ u.l - capacity p d u.l t) / p.br := by
    rw [← hwires, hS, card_subtreeKeys hbr pl w a hcard, wires_reindex a u.l d hul (p.br : ℚ)]
    push_cast
    rw [hwl]
  have hbad : (((S.filter fun κ => ¬ w.Native κ id).card : ℕ) : ℚ) ≤
      ip.mu * siblingFactor p ip * capacity p d u.l t := by
    refine (subtree_bad_le_parity p ip d sched t pl a hcard hpar hP w).trans ?_
    rw [Finset.filter_congr (fun h _ => by rw [hwl]; omega : ∀ h ∈ Finset.range (d - w.l + 1),
      (w.l + h) % 2 = t % 2 ↔ h % 2 = 1), hwl]
    exact sibling_sum_le p ip d t hδ u.l _
  have hk := p.br_cast_pos
  have hAq : ((A.card : ℕ) : ℚ) = (p.br : ℚ) ^ d / (p.br : ℚ) ^ u.l / p.br := by
    rw [hAcard]
    have hpow : (p.br : ℚ) ^ d = (p.br : ℚ) ^ (d - u.l - 1) * p.br * (p.br : ℚ) ^ u.l := by
      rw [← pow_succ, ← pow_add]; congr 1; omega
    push_cast
    rw [hpow]
    field_simp
  have c1 : ((X.card + Y.card : ℕ) : ℚ) ≤ A.card := by exact_mod_cast hcardXY
  have c2 : ((Y.card + (S.filter fun κ => ¬ w.Native κ id).card : ℕ) : ℚ) = S.card := by
    exact_mod_cast hsplit
  push_cast at c1 c2 hbad hAq
  have hid : capacity p d u.l t / p.br =
      (p.br : ℚ) ^ d / (p.br : ℚ) ^ u.l / p.br -
        ((p.br : ℚ) ^ d / (p.br : ℚ) ^ u.l - capacity p d u.l t) / p.br := by ring
  linarith

end Lemma41b

end Chvatal
