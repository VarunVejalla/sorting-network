import D2StaticWireSets

namespace Chvatal.D2NativePathIntervals

open Chvatal.D2Reserve
open Chvatal.D2StaticWireSets

private theorem gapCross_implies_parent_cross
    {wireCount cursor stop cut : Nat} (holes : List (Nat × Nat))
    (hcross : (∃ a ∈ staticWireInterval (n := wireCount) cursor stop \
        staticHoleUnion holes, a.val < cut) ∧
      (∃ b ∈ staticWireInterval (n := wireCount) cursor stop \
        staticHoleUnion holes, cut ≤ b.val)) :
    cursor < cut ∧ cut < stop := by
  rcases hcross with ⟨⟨a, ha, hacut⟩, ⟨b, hb, hbcut⟩⟩
  have ha' := (Finset.mem_sdiff.mp ha).1
  have hb' := (Finset.mem_sdiff.mp hb).1
  simp only [staticWireInterval, Finset.mem_filter, Finset.mem_univ,
    true_and] at ha' hb'
  exact ⟨by omega, by omega⟩

/-- The base-eight address of a node path, with the first edge as the most
significant digit. -/
def pathIndex : (n : Nat) → D2FlowPath n → Nat
  | 0, .nil => 0
  | n + 1, .cons j tail => j.val * 8 ^ n + pathIndex n tail

/-- Fixed native interval occupied by a subtree path, independent of the
dynamic deficit values in the flow state. -/
def nativePathStart (scale remaining : Nat) {n : Nat}
    (path : D2FlowPath n) : Nat :=
  scale * (pathIndex n path * 8 ^ remaining)

def nativePathStop (scale remaining : Nat) {n : Nat}
    (path : D2FlowPath n) : Nat :=
  scale * ((pathIndex n path + 1) * 8 ^ remaining)

/-- The interval of a node is eight times the native child width. This is the
address identity matching a flow node's eight child slots. -/
theorem nativePathStop_succ_eq (scale childHeight : Nat) {n : Nat}
    (path : D2FlowPath n) :
    nativePathStop scale (childHeight + 1) path =
      nativePathStart scale (childHeight + 1) path +
        8 * (scale * 8 ^ childHeight) := by
  unfold nativePathStop nativePathStart
  rw [pow_succ]
  ring

/-- The concrete ordinary-sender gap `[base+left, base+8*childWidth-right)`
lies inside its fixed native path interval when `base` is the path start and
`childWidth` is the native size of one of its eight children. -/
theorem ordinaryGap_within_nativePath
    (scale childHeight : Nat) {n : Nat} (path : D2FlowPath n)
    (base left right : Nat)
    (hbase : base = nativePathStart scale (childHeight + 1) path) :
    nativePathStart scale (childHeight + 1) path ≤ base + left ∧
      base + 8 * (scale * 8 ^ childHeight) - right ≤
        nativePathStop scale (childHeight + 1) path := by
  rw [hbase, ← nativePathStop_succ_eq]
  constructor <;> omega

theorem pathIndex_lt (n : Nat) (path : D2FlowPath n) :
    pathIndex n path < 8 ^ n := by
  induction path with
  | nil => simp [pathIndex]
  | @cons n j tail ih =>
      let B := 8 ^ n
      have hbase : j.val * B + B = (j.val + 1) * B := by
        simp [B, Nat.add_mul]
      have htop : (j.val + 1) * B ≤ 8 * B := by
        exact Nat.mul_le_mul_right B (by omega)
      have htop' : (j.val + 1) * B ≤ B * 8 := by
        simpa [Nat.mul_comm] using htop
      rw [pathIndex, pow_succ]
      calc
        j.val * B + pathIndex n tail < j.val * B + B := by omega
        _ = (j.val + 1) * B := hbase
        _ ≤ B * 8 := htop'

/-- At a fixed depth, distinct paths have distinct base-eight addresses. -/
theorem pathIndex_injective :
    ∀ n (p q : D2FlowPath n), pathIndex n p = pathIndex n q → p = q := by
  intro n
  induction n with
  | zero =>
      intro p q h
      cases p
      cases q
      rfl
  | succ n ih =>
      intro p q h
      cases p with
      | cons a pt =>
        cases q with
        | cons b qt =>
          have hpt : pathIndex n pt < 8 ^ n := pathIndex_lt n pt
          have hqt : pathIndex n qt < 8 ^ n := pathIndex_lt n qt
          have hab : a.val = b.val := by
            by_contra hne
            rcases lt_or_gt_of_ne hne with hab | hba
            · have hmul : (a.val + 1) * 8 ^ n <= b.val * 8 ^ n :=
                Nat.mul_le_mul_right _ (by omega)
              have hleft : a.val * 8 ^ n + pathIndex n pt <
                  (a.val + 1) * 8 ^ n := by
                have hbase : a.val * 8 ^ n + 8 ^ n =
                    (a.val + 1) * 8 ^ n := by
                  simp [Nat.add_mul]
                omega
              rw [pathIndex, pathIndex] at h
              have hright : b.val * 8 ^ n <= b.val * 8 ^ n + pathIndex n qt := by omega
              omega
            · have hmul : (b.val + 1) * 8 ^ n <= a.val * 8 ^ n :=
                Nat.mul_le_mul_right _ (by omega)
              have hleft : b.val * 8 ^ n + pathIndex n qt <
                  (b.val + 1) * 8 ^ n := by
                have hbase : b.val * 8 ^ n + 8 ^ n =
                    (b.val + 1) * 8 ^ n := by
                  simp [Nat.add_mul]
                omega
              rw [pathIndex, pathIndex] at h
              have hright : a.val * 8 ^ n <= a.val * 8 ^ n + pathIndex n pt := by omega
              omega
          have habFin : a = b := Fin.ext hab
          subst b
          have htail : pathIndex n pt = pathIndex n qt := by
            rw [pathIndex, pathIndex] at h
            omega
          have hpq : pt = qt := ih pt qt htail
          subst qt
          rfl

/-- Equal-depth native address intervals are pairwise disjoint. The interval
width is the full native size of the subtree selected by each path. -/
theorem nativePathIntervals_disjoint
    (remaining scale : Nat) {n : Nat}
    (p q : D2FlowPath n) (hpq : p ≠ q) :
    scale * ((pathIndex n p + 1) * 8 ^ remaining) <=
        scale * (pathIndex n q * 8 ^ remaining) ∨
      scale * ((pathIndex n q + 1) * 8 ^ remaining) <=
        scale * (pathIndex n p * 8 ^ remaining) := by
  have hne : pathIndex n p ≠ pathIndex n q := by
    intro h
    exact hpq (pathIndex_injective n p q h)
  rcases Nat.lt_or_gt_of_ne hne with hpq' | hqp'
  · left
    have hmul : (pathIndex n p + 1) * 8 ^ remaining <=
        pathIndex n q * 8 ^ remaining :=
      Nat.mul_le_mul_right _ (by omega)
    exact Nat.mul_le_mul_left scale hmul
  · right
    have hmul : (pathIndex n q + 1) * 8 ^ remaining <=
        pathIndex n p * 8 ^ remaining :=
      Nat.mul_le_mul_right _ (by omega)
    exact Nat.mul_le_mul_left scale hmul

/-- At a fixed path depth, at most one static-gap sender contained in its
native subtree interval can straddle a fixed global prefix cut. This is the
actual tree-level uniqueness statement needed by the boundary-error budget. -/
theorem nativePathGap_crossing_unique
    (wireCount scale remaining cut : Nat) {n : Nat}
    (cursor stop : D2FlowPath n → Nat)
    (holes : D2FlowPath n → List (Nat × Nat))
    (hcontained : ∀ p, nativePathStart scale remaining p ≤ cursor p ∧
      stop p ≤ nativePathStop scale remaining p)
    {p q : D2FlowPath n}
    (hcrossP : (∃ a ∈ staticWireInterval (n := wireCount) (cursor p) (stop p) \
        staticHoleUnion (holes p), a.val < cut) ∧
      (∃ b ∈ staticWireInterval (n := wireCount) (cursor p) (stop p) \
        staticHoleUnion (holes p), cut ≤ b.val))
    (hcrossQ : (∃ a ∈ staticWireInterval (n := wireCount) (cursor q) (stop q) \
        staticHoleUnion (holes q), a.val < cut) ∧
      (∃ b ∈ staticWireInterval (n := wireCount) (cursor q) (stop q) \
        staticHoleUnion (holes q), cut ≤ b.val)) :
    p = q := by
  by_contra hpq
  have hparentP := gapCross_implies_parent_cross (holes p) hcrossP
  have hparentQ := gapCross_implies_parent_cross (holes q) hcrossQ
  have hnativeP : nativePathStart scale remaining p < cut ∧
      cut < nativePathStop scale remaining p := by
    rcases hcontained p with ⟨hlo, hhi⟩
    exact ⟨by omega, by omega⟩
  have hnativeQ : nativePathStart scale remaining q < cut ∧
      cut < nativePathStop scale remaining q := by
    rcases hcontained q with ⟨hlo, hhi⟩
    exact ⟨by omega, by omega⟩
  rcases nativePathIntervals_disjoint remaining scale p q hpq with hdisj | hdisj
  · change nativePathStop scale remaining p ≤ nativePathStart scale remaining q at hdisj
    rcases hnativeP with ⟨hpl, hpr⟩
    rcases hnativeQ with ⟨hql, hqr⟩
    omega
  · change nativePathStop scale remaining q ≤ nativePathStart scale remaining p at hdisj
    rcases hnativeP with ⟨hpl, hpr⟩
    rcases hnativeQ with ⟨hql, hqr⟩
    omega

/-- The same crossing uniqueness specialized to D2's ordinary sender gap:
the left and right fronts trim the native parent interval, whose eight
equal-height child slots have width `scale * 8^childHeight`. -/
theorem ordinaryPathGap_crossing_unique
    (wireCount scale childHeight cut : Nat) {n : Nat}
    (base left right : D2FlowPath n → Nat)
    (holes : D2FlowPath n → List (Nat × Nat))
    (hbase : ∀ p, base p = nativePathStart scale (childHeight + 1) p)
    {p q : D2FlowPath n}
    (hcrossP : (∃ a ∈ staticWireInterval (n := wireCount)
        (base p + left p)
        (base p + 8 * (scale * 8 ^ childHeight) - right p) \
        staticHoleUnion (holes p), a.val < cut) ∧
      (∃ b ∈ staticWireInterval (n := wireCount)
        (base p + left p)
        (base p + 8 * (scale * 8 ^ childHeight) - right p) \
        staticHoleUnion (holes p), cut ≤ b.val))
    (hcrossQ : (∃ a ∈ staticWireInterval (n := wireCount)
        (base q + left q)
        (base q + 8 * (scale * 8 ^ childHeight) - right q) \
        staticHoleUnion (holes q), a.val < cut) ∧
      (∃ b ∈ staticWireInterval (n := wireCount)
        (base q + left q)
        (base q + 8 * (scale * 8 ^ childHeight) - right q) \
        staticHoleUnion (holes q), cut ≤ b.val)) :
    p = q := by
  let cursor : D2FlowPath n → Nat := fun p => base p + left p
  let stop : D2FlowPath n → Nat := fun p =>
    base p + 8 * (scale * 8 ^ childHeight) - right p
  have hcontained : ∀ r,
      nativePathStart scale (childHeight + 1) r ≤ cursor r ∧
      stop r ≤ nativePathStop scale (childHeight + 1) r := by
    intro r
    dsimp [cursor, stop]
    simpa [hbase r] using ordinaryGap_within_nativePath scale childHeight r
      (base r) (left r) (right r) (hbase r)
  apply nativePathGap_crossing_unique wireCount scale (childHeight + 1)
    cut cursor stop holes hcontained
  · simpa [cursor, stop] using hcrossP
  · simpa [cursor, stop] using hcrossQ

/-- Any finite family of same-depth path senders has at most one member whose
static-gap wires straddle a fixed cut, provided each sender lies in its own
native interval. -/
theorem nativePathGap_crossers_card_le_one
    (wireCount scale remaining cut : Nat) {n : Nat}
    (senders : Finset (D2FlowPath n))
    (cursor stop : D2FlowPath n → Nat)
    (holes : D2FlowPath n → List (Nat × Nat))
    (hcontained : ∀ p, nativePathStart scale remaining p ≤ cursor p ∧
      stop p ≤ nativePathStop scale remaining p) :
    (senders.filter fun p =>
      (∃ a ∈ staticWireInterval (n := wireCount) (cursor p) (stop p) \
          staticHoleUnion (holes p), a.val < cut) ∧
      (∃ b ∈ staticWireInterval (n := wireCount) (cursor p) (stop p) \
          staticHoleUnion (holes p), cut ≤ b.val)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  simp only [Finset.mem_filter] at hp hq
  exact nativePathGap_crossing_unique wireCount scale remaining cut
    cursor stop holes hcontained hp.2 hq.2

/-- Summing the local 896 boundary charge over all senders at one path depth
costs at most 896, regardless of how many disjoint senders are present. -/
theorem sum_nativePathGap_boundary_error_le_896
    (wireCount scale remaining cut : Nat) {n : Nat}
    (senders : Finset (D2FlowPath n))
    (cursor stop : D2FlowPath n → Nat)
    (holes : D2FlowPath n → List (Nat × Nat))
    (hcontained : ∀ p, nativePathStart scale remaining p ≤ cursor p ∧
      stop p ≤ nativePathStop scale remaining p)
    (error : D2FlowPath n → Nat)
    (herror : ∀ p, error p ≤
      if (∃ a ∈ staticWireInterval (n := wireCount) (cursor p) (stop p) \
            staticHoleUnion (holes p), a.val < cut) ∧
         (∃ b ∈ staticWireInterval (n := wireCount) (cursor p) (stop p) \
            staticHoleUnion (holes p), cut ≤ b.val) then 896 else 0) :
    (senders.sum fun p => error p) ≤ 896 := by
  classical
  let crosses : D2FlowPath n → Prop := fun p =>
    (∃ a ∈ staticWireInterval (n := wireCount) (cursor p) (stop p) \
        staticHoleUnion (holes p), a.val < cut) ∧
    (∃ b ∈ staticWireInterval (n := wireCount) (cursor p) (stop p) \
        staticHoleUnion (holes p), cut ≤ b.val)
  have hcount : (senders.filter crosses).card ≤ 1 := by
    simpa [crosses] using nativePathGap_crossers_card_le_one
      wireCount scale remaining cut senders cursor stop holes hcontained
  calc
    _ ≤ senders.sum fun p => if crosses p then 896 else 0 :=
      Finset.sum_le_sum fun p hp => by
        simpa [crosses] using herror p
    _ = (senders.filter crosses).card * 896 := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ 1 * 896 := Nat.mul_le_mul_right 896 hcount
    _ = 896 := by omega

/-- Summed across every native path depth in a depth-`d` tree, the fresh
boundary charge is at most 896 per level. This is the full spatial part of
the proposed per-stage `O(d)` prefix-defect recurrence. -/
theorem sum_allNativePath_boundary_error_le_896_mul_succ
    (wireCount scale depth cut : Nat)
    (senders : (n : Nat) → Finset (D2FlowPath n))
    (cursor stop : (n : Nat) → D2FlowPath n → Nat)
    (holes : (n : Nat) → D2FlowPath n → List (Nat × Nat))
    (error : (n : Nat) → D2FlowPath n → Nat)
    (hcontained : ∀ n, n ≤ depth → ∀ p,
      nativePathStart scale (depth - n) p ≤ cursor n p ∧
      stop n p ≤ nativePathStop scale (depth - n) p)
    (herror : ∀ n, n ≤ depth → ∀ p, error n p ≤
      if (∃ a ∈ staticWireInterval (n := wireCount) (cursor n p) (stop n p) \
            staticHoleUnion (holes n p), a.val < cut) ∧
         (∃ b ∈ staticWireInterval (n := wireCount) (cursor n p) (stop n p) \
            staticHoleUnion (holes n p), cut ≤ b.val) then 896 else 0) :
    ((Finset.range (depth + 1)).sum fun n =>
      (senders n).sum fun p => error n p) ≤ 896 * (depth + 1) := by
  calc
    _ ≤ (Finset.range (depth + 1)).sum fun _ => 896 := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' : n ≤ depth := by simp at hn; omega
      simpa using sum_nativePathGap_boundary_error_le_896
        wireCount scale (depth - n) cut (senders n) (cursor n) (stop n)
        (holes n) (hcontained n hn') (error n) (herror n hn')
    _ = 896 * (depth + 1) := by simp [Nat.mul_comm]

end Chvatal.D2NativePathIntervals
