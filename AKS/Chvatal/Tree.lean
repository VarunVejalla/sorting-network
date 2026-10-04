module
/-
  # Chvátal k-ary bag tree

  Source: V. Chvátal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §2–3. Checked in as `docs/dcs-tr-294.pdf`.

  Status: structural API only. Mirrors `AKS/Bags/Defs.lean` for branching
  factor `br` (paper `k`) and height `d` with `N = br^d` wires. No network
  construction, capacity schedule, or outsider invariant lives here.
-/

public import AKS.Sort.Defs

@[expose] public section

namespace Chvatal

open Finset

/-! **Native intervals** -/

/-- Size of each bag's native interval at level `l`: `br^(d - l)`. -/
def bagSize (br d l : ℕ) : ℕ := br ^ (d - l)

/-- Native bag index of sorted rank `r` at level `l`. -/
def nativeBagIdx (br d l : ℕ) (r : ℕ) : ℕ := r / bagSize br d l

/-! **Bags** -/

/-- A bag in the complete `br`-ary tree of height `d` on `br^d` wires. -/
@[ext]
structure KBag (br d : ℕ) where
  l : ℕ
  x : ℕ
  hl : l ≤ d
  hx : x < br ^ l
  deriving DecidableEq

variable {br d : ℕ}

/-- Native interval size for this bag. -/
def KBag.size (b : KBag br d) : ℕ := bagSize br d b.l

/-- Parent bag (one level up). Requires `1 ≤ br` so that `x / br < br^(l-1)`. -/
def KBag.parent (b : KBag br d) (hbr : 1 ≤ br := by omega) : KBag br d :=
  ⟨b.l - 1, b.x / br, Nat.le_trans (Nat.sub_le b.l 1) b.hl, by
    by_cases hl0 : b.l = 0
    · have := b.hx
      simp only [hl0, Nat.zero_sub, pow_zero] at this ⊢
      exact Nat.div_lt_of_lt_mul (by omega)
    · have hpow : br * br ^ (b.l - 1) = br ^ b.l := by
        rw [Nat.mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega)]
      exact Nat.div_lt_of_lt_mul (by
        have := b.hx
        omega)⟩

/-- The `j`-th child (`j < br`). -/
def KBag.child (b : KBag br d) (j : ℕ) (hj : j < br)
    (h : b.l < d := by omega) : KBag br d :=
  ⟨b.l + 1, br * b.x + j, by omega, by
    have hx := b.hx
    have hbr : 0 < br := Nat.zero_lt_of_lt hj
    calc br * b.x + j
        < br * b.x + br := Nat.add_lt_add_left hj _
      _ = br * (b.x + 1) := by ring
      _ ≤ br * br ^ b.l := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hx)
      _ = br ^ b.l * br := Nat.mul_comm _ _
      _ = br ^ (b.l + 1) := (pow_succ br b.l).symm⟩

/-- The root bag. -/
def KBag.root (br d : ℕ) : KBag br d :=
  ⟨0, 0, Nat.zero_le d, by simp [pow_zero]⟩

/-- Lower bound of the native rank interval. -/
def KBag.lo (b : KBag br d) : ℕ := b.x * b.size

/-- Exclusive upper bound of the native rank interval. -/
def KBag.hi (b : KBag br d) : ℕ := (b.x + 1) * b.size

/-! **Placement** -/

/-- Assignment of registers to bags on `br^d` wires. -/
structure Placement (br d : ℕ) where
  regs : KBag br d → Finset (Fin (br ^ d))
  disjoint : ∀ (a b : KBag br d), a ≠ b → Disjoint (regs a) (regs b)
  complete : ∀ (i : Fin (br ^ d)), ∃ (b : KBag br d), i ∈ regs b

/-! **Ancestry, nativeness, outsiders** -/

/-- Ancestor `j` levels up. -/
def KBag.ancestor (b : KBag br d) (j : ℕ) (hbr : 1 ≤ br := by omega) : KBag br d :=
  ⟨b.l - j, b.x / br ^ j, Nat.le_trans (Nat.sub_le b.l j) b.hl, by
    by_cases hjl : j ≤ b.l
    · exact Nat.div_lt_of_lt_mul (by
        rw [← pow_add, show j + (b.l - j) = b.l from by omega]
        exact b.hx)
    · push_neg at hjl
      rw [Nat.sub_eq_zero_of_le hjl.le, pow_zero]
      have h1 : b.x < br ^ j :=
        Nat.lt_of_lt_of_le b.hx (Nat.pow_le_pow_right hbr hjl.le)
      rw [Nat.div_eq_of_lt h1]
      omega⟩

/-- Register `r` is native to bag `b` under permutation `perm`. -/
def KBag.Native (b : KBag br d) (r : Fin (br ^ d))
    (perm : Fin (br ^ d) → Fin (br ^ d)) : Prop :=
  nativeBagIdx br d b.l (perm r).val = b.x

instance KBag.instDecidableNative (b : KBag br d) (r : Fin (br ^ d))
    (perm : Fin (br ^ d) → Fin (br ^ d)) : Decidable (b.Native r perm) :=
  inferInstanceAs (Decidable (nativeBagIdx br d b.l (perm r).val = b.x))

/-- Order-`j` outsider (Chvátal §4; Seiferas `j`-stranger).
    `j = 0` is trivial; `j ≥ 1` means not native to `b.ancestor (j-1)`. -/
def KBag.Strange (b : KBag br d) (j : ℕ) (r : Fin (br ^ d))
    (perm : Fin (br ^ d) → Fin (br ^ d)) (hbr : 1 ≤ br := by omega) : Prop :=
  j = 0 ∨ ¬(b.ancestor (j - 1) hbr).Native r perm

instance KBag.instDecidableStrange (b : KBag br d) (j : ℕ) (r : Fin (br ^ d))
    (perm : Fin (br ^ d) → Fin (br ^ d)) (hbr : 1 ≤ br) :
    Decidable (b.Strange j r perm hbr) :=
  inferInstanceAs
    (Decidable (j = 0 ∨ ¬(b.ancestor (j - 1) hbr).Native r perm))

/-- Count of order-`j` outsiders among registers `S`. -/
def KBag.strangers (b : KBag br d) (j : ℕ)
    (perm : Fin (br ^ d) → Fin (br ^ d)) (S : Finset (Fin (br ^ d)))
    (hbr : 1 ≤ br := by omega) : ℕ :=
  (S.filter (fun r ↦ b.Strange j r perm hbr)).card

theorem KBag.strangers_mono (b : KBag br d) (j : ℕ)
    (perm : Fin (br ^ d) → Fin (br ^ d)) {S T : Finset (Fin (br ^ d))}
    (h : S ⊆ T) (hbr : 1 ≤ br := by omega) :
    b.strangers j perm S hbr ≤ b.strangers j perm T hbr :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem KBag.strangers_union_le (b : KBag br d) (j : ℕ)
    (perm : Fin (br ^ d) → Fin (br ^ d)) (S T : Finset (Fin (br ^ d)))
    (hbr : 1 ≤ br := by omega) :
    b.strangers j perm (S ∪ T) hbr ≤
      b.strangers j perm S hbr + b.strangers j perm T hbr := by
  simp only [KBag.strangers, Finset.filter_union]
  exact Finset.card_union_le _ _

@[simp] theorem KBag.strangers_empty (b : KBag br d) (j : ℕ)
    (perm : Fin (br ^ d) → Fin (br ^ d)) (hbr : 1 ≤ br := by omega) :
    b.strangers j perm ∅ hbr = 0 := by
  simp [KBag.strangers]

/-! **Basic size lemmas** -/

@[simp] theorem bagSize_zero (br d : ℕ) : bagSize br d 0 = br ^ d := by
  simp [bagSize]

theorem bagSize_pos {br d l : ℕ} (hbr : 1 ≤ br) (_h : l ≤ d) :
    0 < bagSize br d l := by
  unfold bagSize
  exact Nat.pow_pos (Nat.succ_le_iff.mp hbr)

theorem bagSize_succ_mul {br d ℓ : ℕ} (_hbr : 1 ≤ br) (h : ℓ + 1 ≤ d) :
    bagSize br d (ℓ + 1) * br = bagSize br d ℓ := by
  simp only [bagSize]
  have h1 : d - (ℓ + 1) + 1 = d - ℓ := by omega
  rw [← pow_succ, h1]

theorem nativeBagIdx_div {br d ℓ r : ℕ} (hbr : 1 ≤ br) (h : ℓ + 1 ≤ d) :
    nativeBagIdx br d (ℓ + 1) r / br = nativeBagIdx br d ℓ r := by
  simp only [nativeBagIdx]
  rw [Nat.div_div_eq_div_mul, bagSize_succ_mul hbr h]

/-! **Bag API** -/

theorem KBag.size_pos (b : KBag br d) (hbr : 1 ≤ br) : 0 < b.size :=
  bagSize_pos hbr b.hl

@[simp] theorem KBag.size_root :
    (KBag.root br d).size = br ^ d :=
  bagSize_zero br d

theorem KBag.hi_eq_lo_add_size (b : KBag br d) : b.hi = b.lo + b.size := by
  simp [KBag.hi, KBag.lo, Nat.add_mul]

theorem KBag.lo_lt_hi (b : KBag br d) (hbr : 1 ≤ br) : b.lo < b.hi := by
  simp only [KBag.hi, KBag.lo, Nat.add_mul, Nat.one_mul]
  exact Nat.lt_add_of_pos_right (b.size_pos hbr)

theorem KBag.native_iff (b : KBag br d) (r : Fin (br ^ d))
    (perm : Fin (br ^ d) → Fin (br ^ d)) (hbr : 1 ≤ br) :
    b.Native r perm ↔ b.lo ≤ (perm r).val ∧ (perm r).val < b.hi := by
  simp only [KBag.Native, KBag.lo, KBag.hi, KBag.size, nativeBagIdx]
  constructor
  · intro h
    constructor
    · rw [← h]; exact Nat.div_mul_le_self _ _
    · rw [← h, Nat.add_mul, Nat.one_mul]
      exact Nat.lt_div_mul_add (bagSize_pos hbr b.hl)
  · intro ⟨hlo, hhi⟩
    have hpos := bagSize_pos hbr b.hl
    have h1 : b.x ≤ (perm r).val / bagSize br d b.l :=
      (Nat.le_div_iff_mul_le hpos).mpr hlo
    have h2 : (perm r).val / bagSize br d b.l < b.x + 1 :=
      (Nat.div_lt_iff_lt_mul hpos).mpr hhi
    omega

theorem KBag.native_root (r : Fin (br ^ d))
    (perm : Fin (br ^ d) → Fin (br ^ d)) :
    (KBag.root br d).Native r perm := by
  simp only [KBag.Native, KBag.root, nativeBagIdx, bagSize_zero]
  exact Nat.div_eq_of_lt (perm r).isLt

/-! **Tree structure** -/

theorem KBag.child_parent (b : KBag br d) (j : ℕ) (hj : j < br)
    (h : b.l < d) (hbr : 1 ≤ br) :
    ((b.child j hj h).parent hbr) = b := by
  apply KBag.ext
  · show b.l + 1 - 1 = b.l; omega
  · show (br * b.x + j) / br = b.x
    have hbrpos : 0 < br := Nat.zero_lt_of_lt hj
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hbrpos, Nat.div_eq_of_lt hj,
      zero_add]

theorem KBag.parent_child (c : KBag br d) (hcl : 1 ≤ c.l) (hbr : 1 ≤ br)
    (h : (c.parent hbr).l < d := by
      have := c.hl; unfold KBag.parent; simp; omega) :
    (c.parent hbr).child (c.x % br) (Nat.mod_lt _ (Nat.succ_le_iff.mp hbr)) h = c := by
  apply KBag.ext
  · show c.l - 1 + 1 = c.l; omega
  · show br * (c.x / br) + c.x % br = c.x
    exact Nat.div_add_mod c.x br

/-- Level shift: order-`j` outsiders at the parent equal order-`(j+1)` outsiders
    at the child (`j ≥ 1`, non-root). -/
theorem KBag.strangers_parent_eq (b : KBag br d) (j : ℕ) (hj : 1 ≤ j)
    (_hl : 1 ≤ b.l) (perm : Fin (br ^ d) → Fin (br ^ d))
    (S : Finset (Fin (br ^ d))) (hbr : 1 ≤ br) :
    (b.parent hbr).strangers j perm S hbr = b.strangers (j + 1) perm S hbr := by
  simp only [KBag.strangers]
  congr 1; ext r
  simp only [Finset.mem_filter]
  constructor
  · intro ⟨hmem, hns⟩
    refine ⟨hmem, ?_⟩
    show b.Strange (j + 1) r perm hbr
    simp only [KBag.Strange, show j + 1 ≠ 0 by omega, false_or,
      show j + 1 - 1 = j by omega]
    have hns' : ¬((b.parent hbr).ancestor (j - 1) hbr).Native r perm := by
      simp only [KBag.Strange, show j ≠ 0 by omega, false_or] at hns
      exact hns
    have heq : (b.parent hbr).ancestor (j - 1) hbr = b.ancestor j hbr := by
      ext
      · show b.l - 1 - (j - 1) = b.l - j; omega
      · show (b.x / br) / br ^ (j - 1) = b.x / br ^ j
        rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← pow_succ,
          Nat.sub_add_cancel hj]
    rwa [← heq]
  · intro ⟨hmem, hns⟩
    refine ⟨hmem, ?_⟩
    show (b.parent hbr).Strange j r perm hbr
    simp only [KBag.Strange, show j ≠ 0 by omega, false_or]
    have hns' : ¬(b.ancestor j hbr).Native r perm := by
      simp only [KBag.Strange, show j + 1 ≠ 0 by omega, false_or,
        show j + 1 - 1 = j by omega] at hns
      exact hns
    have heq : (b.parent hbr).ancestor (j - 1) hbr = b.ancestor j hbr := by
      ext
      · show b.l - 1 - (j - 1) = b.l - j; omega
      · show (b.x / br) / br ^ (j - 1) = b.x / br ^ j
        rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← pow_succ,
          Nat.sub_add_cancel hj]
    rwa [heq]

/-- If `r` is native to `b`, then it is native to `b.parent`. -/
theorem KBag.Native.parent {b : KBag br d} {r : Fin (br ^ d)}
    {perm : Fin (br ^ d) → Fin (br ^ d)} (h : b.Native r perm)
    (hl : 1 ≤ b.l) (hbr : 1 ≤ br) :
    (b.parent hbr).Native r perm := by
  simp only [KBag.Native, KBag.parent] at *
  show nativeBagIdx br d (b.l - 1) (perm r).val = b.x / br
  have hlk : (b.l - 1) + 1 ≤ d := by have := b.hl; omega
  have hbl : (b.l - 1) + 1 = b.l := by omega
  rw [← nativeBagIdx_div hbr hlk, hbl, h]

/-! **Enumeration** -/

/-- All bags in the height-`d` `br`-ary tree. -/
def allBags (br d : ℕ) : List (KBag br d) :=
  ((List.range (d + 1)).attach).flatMap fun ⟨l, hl⟩ ↦
    let hl' : l ≤ d := by rw [List.mem_range] at hl; omega
    ((List.range (br ^ l)).attach).map fun ⟨x, hx⟩ ↦
      ⟨l, x, hl', by rwa [List.mem_range] at hx⟩

theorem KBag.mem_allBags (b : KBag br d) : b ∈ allBags br d := by
  simp only [allBags, List.mem_flatMap, List.mem_attach, true_and, List.mem_map,
    List.mem_range, Subtype.exists]
  exact ⟨b.l, by have := b.hl; omega, b.x, b.hx, by ext <;> rfl⟩

end Chvatal
