import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option maxHeartbeats 1000000

/-! Finite-set and count identities for converting per-bag outsider and
alignment budgets into global threshold error. This is independent of the D2
routing model: a later bridge must instantiate the bags in its actual state
and prove the required transfer bounds.
-/

namespace Chvatal.D2RankAlignment

open scoped BigOperators

variable {α : Type*} [LinearOrder α] [DecidableEq α]

/-- Number of keys below a fixed threshold in a finite set. -/
def thresholdMass (Q : α) (S : Finset α) : ℕ :=
  (S.filter fun x => x < Q).card

/-- Number of positions from the prefix `[0,H)` that lie in a fixed interval
`[u,v)`. This form also covers ragged child intervals. -/
def prefixIntervalMass (H u v : ℕ) : ℕ := min (H - u) (v - u)

/-- Number of rows of one column whose row-major flattened address precedes a
given boundary. -/
def flatBoundaryColumnCut (rows columns boundary column : ℕ) : ℕ :=
  ((Finset.range rows).filter fun r => r * columns + column < boundary).card

/-- Number of wires of a given column before a position in an arbitrary
ordered list of live wires. This also represents fixed masks with holes. -/
def orderedColumnCut (columnOf : ℕ → ℕ) (column boundary : ℕ) : ℕ :=
  ((Finset.range boundary).filter fun i => columnOf i = column).card

/-- The flat boundary at zero cuts no rows from any column. -/
theorem flatBoundaryColumnCut_zero (rows columns column : ℕ) :
    flatBoundaryColumnCut rows columns 0 column = 0 := by
  simp [flatBoundaryColumnCut]

/-- At the end of a rectangular row-major layout, each column cut is at its
full row height. -/
theorem flatBoundaryColumnCut_full (rows columns column : ℕ)
    (hcolumn : column < columns) :
    flatBoundaryColumnCut rows columns (rows * columns) column = rows := by
  unfold flatBoundaryColumnCut
  have hfilter :
      (Finset.range rows).filter (fun r => r * columns + column < rows * columns) =
        Finset.range rows := by
    apply Finset.filter_eq_self.mpr
    intro r hr
    have hr' : r + 1 ≤ rows := Nat.succ_le_of_lt (Finset.mem_range.mp hr)
    calc
      r * columns + column < r * columns + columns := by omega
      _ = (r + 1) * columns := by ring
      _ ≤ rows * columns := Nat.mul_le_mul_right columns hr'
  rw [hfilter]
  simp

/-- Moving a flat row-major boundary forward can only advance each column's
cut. -/
theorem flatBoundaryColumnCut_mono
    (rows columns left right column : ℕ) (h : left ≤ right) :
    flatBoundaryColumnCut rows columns left column ≤
      flatBoundaryColumnCut rows columns right column := by
  unfold flatBoundaryColumnCut
  apply Finset.card_le_card
  intro r hr
  rcases Finset.mem_filter.mp hr with ⟨hrange, hleft⟩
  exact Finset.mem_filter.mpr ⟨hrange, lt_of_lt_of_le hleft h⟩

/-- Ordered-column prefix counts are monotone in the global boundary. -/
theorem orderedColumnCut_mono (columnOf : ℕ → ℕ)
    (column left right : ℕ) (h : left ≤ right) :
    orderedColumnCut columnOf column left ≤
      orderedColumnCut columnOf column right := by
  unfold orderedColumnCut
  apply Finset.card_le_card
  intro i hi
  rcases Finset.mem_filter.mp hi with ⟨hirange, hcol⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_lt_of_le
    (Finset.mem_range.mp hirange) h), hcol⟩

/-- Any contiguous partition of an ordered live-wire list induces complete
monotone partitions of the ranks in every column, regardless of holes in the
underlying physical mask. -/
theorem ordered_column_cuts_partition
    (columnOf : ℕ → ℕ) (total ports : ℕ) (boundary : ℕ → ℕ)
    (hboundary_zero : boundary 0 = 0)
    (hboundary_end : boundary ports = total)
    (hboundary_mono : ∀ i < ports, boundary i ≤ boundary (i + 1)) :
    ∀ column,
      orderedColumnCut columnOf column (boundary 0) = 0 ∧
      orderedColumnCut columnOf column (boundary ports) =
        orderedColumnCut columnOf column total ∧
      (∀ i < ports,
        orderedColumnCut columnOf column (boundary i) ≤
          orderedColumnCut columnOf column (boundary (i + 1))) := by
  intro column
  constructor
  · rw [hboundary_zero]
    simp [orderedColumnCut]
  constructor
  · rw [hboundary_end]
  · intro i hi
    exact orderedColumnCut_mono columnOf column (boundary i)
      (boundary (i + 1)) (hboundary_mono i hi)

/-- A partition of the flattened row-major sender induces a complete
monotone interval partition in every column, including ragged port widths. -/
theorem flat_boundary_column_cuts_partition
    (rows columns ports : ℕ) (boundary : ℕ → ℕ)
    (hboundary_zero : boundary 0 = 0)
    (hboundary_end : boundary ports = rows * columns)
    (hboundary_mono : ∀ i < ports, boundary i ≤ boundary (i + 1)) :
    ∀ column < columns,
      flatBoundaryColumnCut rows columns (boundary 0) column = 0 ∧
      flatBoundaryColumnCut rows columns (boundary ports) column = rows ∧
      (∀ i < ports,
        flatBoundaryColumnCut rows columns (boundary i) column ≤
          flatBoundaryColumnCut rows columns (boundary (i + 1)) column) := by
  intro column hcolumn
  constructor
  · rw [hboundary_zero]
    exact flatBoundaryColumnCut_zero rows columns column
  constructor
  · rw [hboundary_end]
    exact flatBoundaryColumnCut_full rows columns column hcolumn
  · intro i hi
    exact flatBoundaryColumnCut_mono rows columns (boundary i)
      (boundary (i + 1)) column (hboundary_mono i hi)

/-- Splitting a complete prefix interval at one interior boundary conserves
its reference mass. Iterating this identity gives the reference-count
partition law needed to charge parent-prefix displacement only once. -/
theorem prefixIntervalMass_split (H u a : ℕ) (hua : u ≤ a) :
    prefixIntervalMass H 0 u + prefixIntervalMass H u a =
      prefixIntervalMass H 0 a := by
  by_cases hHu : H ≤ u
  · have hHa : H ≤ a := le_trans hHu hua
    simp [prefixIntervalMass, Nat.min_eq_left hHu,
      Nat.sub_eq_zero_of_le hHu, Nat.min_eq_left hHa]
  · have huH : u ≤ H := Nat.le_of_not_ge hHu
    by_cases hHa : H ≤ a
    · have htail : H - u ≤ a - u := Nat.sub_le_sub_right hHa u
      simp [prefixIntervalMass, Nat.min_eq_right huH,
        Nat.min_eq_left htail, Nat.min_eq_left hHa]
      omega
    · have haH : a ≤ H := Nat.le_of_not_ge hHa
      have htail : a - u ≤ H - u := Nat.sub_le_sub_right haH u
      simp [prefixIntervalMass, Nat.min_eq_right huH,
        Nat.min_eq_right htail, Nat.min_eq_right haH]
      omega

/-- A finite increasing chain of interval boundaries partitions the parent
prefix mass exactly. -/
theorem prefixIntervalMass_partition (H : ℕ) (cuts : ℕ → ℕ)
    (n a : ℕ) (hzero : cuts 0 = 0) (hend : cuts n = a)
    (hmono : ∀ i < n, cuts i ≤ cuts (i + 1)) :
    ∑ i ∈ Finset.range n,
      prefixIntervalMass H (cuts i) (cuts (i + 1)) =
        prefixIntervalMass H 0 a := by
  induction n generalizing a with
  | zero =>
      have ha : a = 0 := by simpa using hend.symm.trans hzero
      subst a
      simp [prefixIntervalMass, hzero]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hprev := ih (cuts n) rfl (by
        intro i hi
        exact hmono i (by omega))
      rw [hprev]
      rw [show cuts (n + 1) = a by exact hend]
      have hlast : cuts n ≤ a := by
        rw [← hend]
        exact hmono n (by omega)
      exact prefixIntervalMass_split H (cuts n) a hlast

/-- The reference mass in a fixed interval is monotone in the prefix length. -/
theorem prefixIntervalMass_mono {H K u v : ℕ} (hHK : H ≤ K) :
    prefixIntervalMass H u v ≤ prefixIntervalMass K u v := by
  unfold prefixIntervalMass
  exact min_le_min (Nat.sub_le_sub_right hHK u) le_rfl

/-- Increasing a prefix by `K-H` can add at most that many positions to any
fixed interval, regardless of its width or its location. -/
theorem prefixIntervalMass_le_add_delta {H K u v : ℕ}
    (huv : u ≤ v) (hHK : H ≤ K) :
    prefixIntervalMass K u v ≤ prefixIntervalMass H u v + (K - H) := by
  unfold prefixIntervalMass
  by_cases hsat : v - u ≤ H - u
  · rw [Nat.min_eq_right hsat]
    have hsatK : v - u ≤ K - u := by omega
    rw [Nat.min_eq_right hsatK]
    omega
  · have hunsat : H - u ≤ v - u := Nat.le_of_lt (lt_of_not_ge hsat)
    rw [Nat.min_eq_left hunsat]
    by_cases hsatK : v - u ≤ K - u
    · rw [Nat.min_eq_right hsatK]
      omega
    · have hunsatK : K - u ≤ v - u := Nat.le_of_lt (lt_of_not_ge hsatK)
      rw [Nat.min_eq_left hunsatK]
      omega

/-- For any two prefix lengths, a fixed ragged child interval's reference
count changes by no more than the change in the parent count. -/
theorem prefixIntervalMass_count_change (H K u v : ℕ) (huv : u ≤ v) :
    prefixIntervalMass H u v ≤ prefixIntervalMass K u v + (H - K) + (K - H) ∧
    prefixIntervalMass K u v ≤ prefixIntervalMass H u v + (H - K) + (K - H) := by
  by_cases hHK : H ≤ K
  · have hmono := prefixIntervalMass_mono (u := u) (v := v) hHK
    have hdelta := prefixIntervalMass_le_add_delta (u := u) (v := v) huv hHK
    constructor <;> omega
  · have hKH : K ≤ H := Nat.le_of_not_ge hHK
    have hmono := prefixIntervalMass_mono (u := u) (v := v) hKH
    have hdelta := prefixIntervalMass_le_add_delta (u := u) (v := v) huv hKH
    constructor <;> omega

/-- A bag's keys that do not belong to its target rank interval. -/
def outsiderCount (S I : Finset α) : ℕ := (S \ I).card

/-- A bag's positive excess of below-threshold mass is paid for by its outsiders.
No equal-cardinality hypothesis is needed for this one-sided estimate. -/
theorem threshold_excess_le_outsiders (Q : α) (S I : Finset α) :
    thresholdMass Q S - thresholdMass Q I ≤ outsiderCount S I := by
  let A := S.filter fun x => x < Q
  let B := I.filter fun x => x < Q
  have hsub : A \ B ⊆ S \ I := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxA, hxnotB⟩
    have hxS : x ∈ S := (Finset.mem_filter.mp hxA).1
    have hnotI : x ∉ I := by
      intro hxI
      apply hxnotB
      exact Finset.mem_filter.mpr ⟨hxI, (Finset.mem_filter.mp hxA).2⟩
    exact Finset.mem_sdiff.mpr ⟨hxS, hnotI⟩
  have hcard : (A \ B).card ≤ (S \ I).card := Finset.card_le_card hsub
  have hsplit : (A \ B).card + (A ∩ B).card = A.card :=
    Finset.card_sdiff_add_card_inter A B
  have hinter : (A ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
  dsimp [thresholdMass, outsiderCount]
  change A.card - B.card ≤ (S \ I).card
  omega

/-- If the current bags contain exactly `q` keys below `Q`, their total
threshold alignment `q - sum min(actual,target)` is at most their total
outsider count. This is the cap needed to transfer a separator guarantee to
the coupled rank-flow state. -/
theorem threshold_alignment_le_outsiders {ι : Type*} [Fintype ι]
    (Q : α) (q : ℕ) (S I : ι → Finset α)
    (hq : q = ∑ i : ι, thresholdMass Q (S i)) :
    q - ∑ i : ι, min (thresholdMass Q (S i)) (thresholdMass Q (I i)) ≤
      ∑ i : ι, outsiderCount (S i) (I i) := by
  have hterm (i : ι) :
      (thresholdMass Q (S i) -
        min (thresholdMass Q (S i)) (thresholdMass Q (I i))) +
        min (thresholdMass Q (S i)) (thresholdMass Q (I i)) =
          thresholdMass Q (S i) := by
    exact Nat.sub_add_cancel (Nat.min_le_left _ _)
  have hsum :
      (∑ i : ι,
        ((thresholdMass Q (S i) -
          min (thresholdMass Q (S i)) (thresholdMass Q (I i))) +
          min (thresholdMass Q (S i)) (thresholdMass Q (I i)))) =
        ∑ i : ι, thresholdMass Q (S i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hterm i
  rw [Finset.sum_add_distrib] at hsum
  calc
    q - ∑ i : ι, min (thresholdMass Q (S i)) (thresholdMass Q (I i)) =
        ∑ i : ι, (thresholdMass Q (S i) -
          min (thresholdMass Q (S i)) (thresholdMass Q (I i))) := by
      rw [hq]
      omega
    _ ≤ ∑ i : ι, outsiderCount (S i) (I i) := by
      exact Finset.sum_le_sum fun i _ => by
        let hs := thresholdMass Q (S i)
        let hi := thresholdMass Q (I i)
        change hs - min hs hi ≤ outsiderCount (S i) (I i)
        by_cases h : hs ≤ hi
        · simp [Nat.min_eq_left h]
        · rw [Nat.min_eq_right (Nat.le_of_lt (lt_of_not_ge h))]
          exact threshold_excess_le_outsiders Q (S i) (I i)

/-- For two partitions of the same q keys, twice their total overlap plus
their total absolute mass displacement is exactly 2q. This identity turns
the local overlap term in the coupled D2 potential into alignment. -/
theorem twice_overlap_add_alignment_eq {ι : Type*} [Fintype ι]
    (q : Nat) (actual target : ι → Nat)
    (hactual : (Finset.univ.sum fun i : ι => actual i) = q)
    (htarget : (Finset.univ.sum fun i : ι => target i) = q) :
    2 * (Finset.univ.sum fun i : ι => min (actual i) (target i)) +
      (Finset.univ.sum fun i : ι =>
        actual i - target i + (target i - actual i)) = 2 * q := by
  have hpoint (i : ι) :
      2 * min (actual i) (target i) +
        (actual i - target i + (target i - actual i)) =
          actual i + target i := by
    by_cases h : actual i <= target i
    · rw [Nat.min_eq_left h, Nat.sub_eq_zero_of_le h]
      omega
    · have h' : target i <= actual i := Nat.le_of_not_ge h
      rw [Nat.min_eq_right h', Nat.sub_eq_zero_of_le h']
      omega
  calc
    2 * (Finset.univ.sum fun i : ι => min (actual i) (target i)) +
        (Finset.univ.sum fun i : ι =>
          actual i - target i + (target i - actual i)) =
      (Finset.univ.sum fun i : ι => 2 * min (actual i) (target i)) +
        (Finset.univ.sum fun i : ι =>
          actual i - target i + (target i - actual i)) := by
            rw [Finset.mul_sum]
    _ = (Finset.univ.sum fun i : ι =>
          2 * min (actual i) (target i) +
            (actual i - target i + (target i - actual i))) := by
          simp only [Finset.sum_add_distrib]
    _ = (Finset.univ.sum fun i : ι => actual i + target i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hpoint i
    _ = (Finset.univ.sum fun i : ι => actual i) +
          (Finset.univ.sum fun i : ι => target i) := by
          rw [Finset.sum_add_distrib]
    _ = 2 * q := by rw [hactual, htarget]; omega

/-- If `z` is the number of threshold keys already in the global target
prefix, the local defect `overlap-z` and the unweighted alignment split its
prefix defect exactly: `2*prefixDefect = alignment + 2*localDefect`. -/
theorem alignment_add_twice_local_defect_eq_twice_prefix_defect
    (q z overlap alignment : Nat)
    (hoverlap : 2 * overlap + alignment = 2 * q)
    (hz : z <= overlap) :
    alignment + 2 * (overlap - z) = 2 * (q - z) := by
  omega

/-- A prefix takes at most the whole mass of a bag and at most the number of
target-prefix slots assigned to that bag. Summing shows the local defect
`sum min(actual,target)-sum prefix` is nonnegative. -/
theorem sum_prefix_le_sum_min {ι : Type*} [Fintype ι]
    (actual target part : ι → Nat)
    (hactual : ∀ i, part i <= actual i)
    (htarget : ∀ i, part i <= target i) :
    (Finset.univ.sum fun i : ι => part i) <=
      (Finset.univ.sum fun i : ι => min (actual i) (target i)) := by
  apply Finset.sum_le_sum
  intro i hi
  exact (Nat.le_min).2 ⟨hactual i, htarget i⟩

/-- A child's threshold-count error is at most its parent's error plus the
local error in the reference-port transfer.  The four directional bounds
are stated explicitly so callers can instantiate the lemma without relying
on a choice of absolute-difference API. -/
theorem child_count_error_le_parent_add_transfer
    (actualChild referenceChild idealChild transferError parentError : ℕ)
    (hTransferUpper : actualChild ≤ referenceChild + transferError)
    (hTransferLower : referenceChild ≤ actualChild + transferError)
    (hReferenceUpper : referenceChild ≤ idealChild + parentError)
    (hReferenceLower : idealChild ≤ referenceChild + parentError) :
    actualChild ≤ idealChild + (transferError + parentError) ∧
      idealChild ≤ actualChild + (transferError + parentError) := by
  constructor <;> omega

/-- If the parent's count error is within `c/512` and the local transfer
error is strictly below `c/512`, then after capacity doubles the child's
error is within the same normalized `1/512` allowance. -/
theorem child_count_error_preserves_doubled_capacity
    (transferError parentError capacity : ℕ)
    (hTransfer : 512 * transferError < capacity)
    (hParent : 512 * parentError ≤ capacity) :
    512 * (transferError + parentError) ≤ 2 * capacity := by
  omega

/-- Symmetric absolute difference on natural-valued counts, written without
coercions so it can be summed over finite bag partitions. -/
def countDistance (a b : ℕ) : ℕ := a - b + (b - a)

/-- The suffix of a fixed interval above a threshold. -/
def suffixIntervalMass (H u v : ℕ) : ℕ :=
  (v - u) - prefixIntervalMass H u v

/-- If inherited keys occupy a low prefix and a high suffix of a parent rank
interval, an ordered partition transports the two frontiers to its children
without multiplying either count by the number of children. This is the
arithmetic interface needed to turn prefix-sidedness into child rank targets. -/
theorem low_high_frontier_partition
    (total low high : ℕ) (cuts : ℕ → ℕ) (n : ℕ)
    (hzero : cuts 0 = 0) (hend : cuts n = total)
    (hmono : ∀ i < n, cuts i ≤ cuts (i + 1))
    (hlow : low ≤ total) (hhigh : high ≤ total)
    (hfronts : low ≤ total - high) :
    (∑ i ∈ Finset.range n,
      (prefixIntervalMass low (cuts i) (cuts (i + 1)) +
        suffixIntervalMass (total - high) (cuts i) (cuts (i + 1)))) =
      low + high ∧
    (∀ i < n, prefixIntervalMass low (cuts i) (cuts (i + 1)) +
        suffixIntervalMass (total - high) (cuts i) (cuts (i + 1)) ≤
          cuts (i + 1) - cuts i) := by
  have hlowPart := prefixIntervalMass_partition low cuts n total hzero hend hmono
  have hmiddlePart := prefixIntervalMass_partition (total - high) cuts n total
    hzero hend hmono
  have htotalPart := prefixIntervalMass_partition total cuts n total hzero hend hmono
  have hlowSum : (∑ i ∈ Finset.range n,
      prefixIntervalMass low (cuts i) (cuts (i + 1))) = low := by
    rw [hlowPart]
    simp [prefixIntervalMass, Nat.min_eq_left hlow]
  have hmiddleSum : (∑ i ∈ Finset.range n,
      prefixIntervalMass (total - high) (cuts i) (cuts (i + 1))) = total - high := by
    rw [hmiddlePart]
    simp [prefixIntervalMass]
  have htotalSum : (∑ i ∈ Finset.range n,
      prefixIntervalMass total (cuts i) (cuts (i + 1))) = total := by
    rw [htotalPart]
    simp [prefixIntervalMass]
  have hleEnd : ∀ d i, i + d = n → cuts i ≤ cuts n := by
    intro d
    induction d with
    | zero =>
        intro i hi
        have heq : i = n := by omega
        subst i
        exact le_rfl
    | succ d ih =>
        intro i hi
        have hstep : cuts i ≤ cuts (i + 1) := hmono i (by omega)
        have hrest : cuts (i + 1) ≤ cuts n := ih (i + 1) (by omega)
        exact hstep.trans hrest
  have hwidth (H : ℕ) (hH : H ≤ total) (i : ℕ)
      (hi : i ∈ Finset.range n) :
      prefixIntervalMass total (cuts i) (cuts (i + 1)) =
        (cuts (i + 1) - cuts i) := by
    have hi' : i < n := Finset.mem_range.mp hi
    have hcut := hleEnd (n - (i + 1)) (i + 1) (by omega)
    rw [hend] at hcut
    unfold prefixIntervalMass
    rw [Nat.min_eq_right]
    omega
  have hdecomp (H : ℕ) (hH : H ≤ total) (i : ℕ)
      (hi : i ∈ Finset.range n) :
      prefixIntervalMass H (cuts i) (cuts (i + 1)) +
        suffixIntervalMass H (cuts i) (cuts (i + 1)) =
          prefixIntervalMass total (cuts i) (cuts (i + 1)) := by
    have hw := hwidth H hH i hi
    unfold suffixIntervalMass
    rw [hw]
    unfold prefixIntervalMass
    omega
  have hmiddleAndSuffix : (∑ i ∈ Finset.range n,
      (prefixIntervalMass (total - high) (cuts i) (cuts (i + 1)) +
        suffixIntervalMass (total - high) (cuts i) (cuts (i + 1)))) = total := by
    calc
      _ = ∑ i ∈ Finset.range n,
          prefixIntervalMass total (cuts i) (cuts (i + 1)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hdecomp (total - high) (Nat.sub_le total high) i hi
      _ = total := htotalSum
  have hsuffix : (∑ i ∈ Finset.range n,
      suffixIntervalMass (total - high) (cuts i) (cuts (i + 1))) = high := by
    rw [Finset.sum_add_distrib, hmiddleSum] at hmiddleAndSuffix
    omega
  constructor
  · rw [Finset.sum_add_distrib, hlowSum, hsuffix]
  · intro i hi
    have hcut := hleEnd (n - (i + 1)) (i + 1) (by omega)
    rw [hend] at hcut
    have hstep := hmono i hi
    have hprefix : prefixIntervalMass low (cuts i) (cuts (i + 1)) ≤
        prefixIntervalMass (total - high) (cuts i) (cuts (i + 1)) := by
      unfold prefixIntervalMass
      exact min_le_min (Nat.sub_le_sub_right hfronts (cuts i)) le_rfl
    have hdecomp : prefixIntervalMass (total - high) (cuts i) (cuts (i + 1)) +
        suffixIntervalMass (total - high) (cuts i) (cuts (i + 1)) =
          cuts (i + 1) - cuts i := by
      unfold suffixIntervalMass
      have hle : prefixIntervalMass (total - high) (cuts i) (cuts (i + 1)) ≤
          cuts (i + 1) - cuts i := min_le_right _ _
      omega
    omega

/-- Prefix mass in `[pos,pos+size)` is exactly the left-front overlap used by
the concrete D2 cut. -/
theorem prefixIntervalMass_eq_left_front_overlap
    (pos size left : ℕ) :
    prefixIntervalMass left pos (pos + size) = min (pos + size) left - pos := by
  unfold prefixIntervalMass
  omega

/-- Suffix mass in `[pos,pos+size)` is exactly the right-front overlap used
by the concrete D2 cut. -/
theorem suffixIntervalMass_eq_right_front_overlap
    (pos size right : ℕ) :
    suffixIntervalMass right pos (pos + size) =
      pos + size - max pos right := by
  unfold suffixIntervalMass prefixIntervalMass
  omega

/-- Triangle inequality for count distance. -/
theorem countDistance_triangle (a b c : ℕ) :
    countDistance a b ≤ countDistance a c + countDistance c b := by
  unfold countDistance
  omega

/-- Positive and negative parts of the clipped boundary displacement. -/
def clippedBoundaryPos (H x y : ℕ) : ℕ := min x H - min y H
def clippedBoundaryNeg (H x y : ℕ) : ℕ := min y H - min x H

/-- One-step potential inequality for clipping two increasing boundaries at
the same threshold. The boundary discrepancy `x-y` and clipped discrepancy
`min(x,H)-min(y,H)` need not change by the same amount at this step, but the
absolute-value potential pays for the clipping change. Summing this inequality
along a complete path telescopes to the variation contraction. -/
theorem clipped_boundary_step_variation
    (H x y x' y' : ℕ) (hx : x ≤ x') (hy : y ≤ y') :
    countDistance
        (clippedBoundaryPos H x' y' + clippedBoundaryNeg H x y)
        (clippedBoundaryNeg H x' y' + clippedBoundaryPos H x y) +
      countDistance (min x' H) (min y' H) + countDistance x y ≤
    countDistance (x' + y) (y' + x) + countDistance x' y' +
      countDistance (min x H) (min y H) := by
  unfold clippedBoundaryPos clippedBoundaryNeg countDistance
  omega

/-- If two finite port profiles conserve the same total mass, their total
positive leakage equals their total negative leakage. Thus an aggregate l1
port bound can be charged separately to the low and high sides of a cut. -/
theorem balanced_port_leakage_equal
    {I : Type*} [Fintype I]
    (actual reference : I → ℕ)
    (hTotal : (∑ i : I, actual i) = ∑ i : I, reference i) :
    (Finset.univ.sum fun i : I => actual i - reference i) =
      (Finset.univ.sum fun i : I => reference i - actual i) := by
  have hActual :
      (∑ i : I, min (actual i) (reference i)) +
          (Finset.univ.sum fun i : I => actual i - reference i) =
        ∑ i : I, actual i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    omega
  have hReference :
      (∑ i : I, min (actual i) (reference i)) +
          (Finset.univ.sum fun i : I => reference i - actual i) =
        ∑ i : I, reference i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    omega
  omega

/-- For balanced port profiles, each direction of leakage is exactly half
the total l1 error. This is the form needed to compare a summed port provider
with separate low/high flow reserves. -/
theorem balanced_port_directional_leakage
    {I : Type*} [Fintype I]
    (actual reference : I → ℕ) (budget : ℕ)
    (hTotal : (∑ i : I, actual i) = ∑ i : I, reference i)
    (hL1 : (∑ i : I, countDistance (actual i) (reference i)) ≤ budget) :
    2 * (Finset.univ.sum fun i : I => actual i - reference i) ≤ budget ∧
      2 * (Finset.univ.sum fun i : I => reference i - actual i) ≤ budget := by
  have hBalance := balanced_port_leakage_equal actual reference hTotal
  have hL1eq :
      (∑ i : I, countDistance (actual i) (reference i)) =
        2 * (Finset.univ.sum fun i : I => actual i - reference i) := by
    calc
      (∑ i : I, countDistance (actual i) (reference i)) =
          (∑ i : I,
            ((actual i - reference i) + (reference i - actual i))) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [countDistance]
      _ = (Finset.univ.sum fun i : I => actual i - reference i) +
          (Finset.univ.sum fun i : I => reference i - actual i) := by
            rw [Finset.sum_add_distrib]
      _ = 2 * (Finset.univ.sum fun i : I => actual i - reference i) := by omega
  have hForward :
      2 * (Finset.univ.sum fun i : I => actual i - reference i) ≤ budget := by
    rw [← hL1eq]
    exact hL1
  constructor
  · exact hForward
  · rw [← hBalance]
    exact hForward

/-- Across a complete interval partition, the l1 distance between the two
reference port vectors is exactly the change in clipped parent-prefix mass,
and hence no larger than the parent-prefix displacement. -/
theorem prefixIntervalMass_partition_distance
    (H K : ℕ) (cuts : ℕ → ℕ) (n a : ℕ)
    (hzero : cuts 0 = 0) (hend : cuts n = a)
    (hmono : ∀ i < n, cuts i ≤ cuts (i + 1)) :
    (∑ i ∈ Finset.range n,
      countDistance (prefixIntervalMass H (cuts i) (cuts (i + 1)))
        (prefixIntervalMass K (cuts i) (cuts (i + 1)))) ≤
      countDistance H K := by
  have hforward (X Y : ℕ) (hXY : X ≤ Y) :
      (∑ i ∈ Finset.range n,
        countDistance (prefixIntervalMass X (cuts i) (cuts (i + 1)))
          (prefixIntervalMass Y (cuts i) (cuts (i + 1)))) ≤
        countDistance X Y := by
    have hsumX := prefixIntervalMass_partition X cuts n a hzero hend hmono
    have hsumY := prefixIntervalMass_partition Y cuts n a hzero hend hmono
    have hport (i : ℕ) (hi : i ∈ Finset.range n) :
        prefixIntervalMass X (cuts i) (cuts (i + 1)) ≤
          prefixIntervalMass Y (cuts i) (cuts (i + 1)) :=
      prefixIntervalMass_mono hXY
    have hdiff :
        (∑ i ∈ Finset.range n,
          (prefixIntervalMass Y (cuts i) (cuts (i + 1)) -
            prefixIntervalMass X (cuts i) (cuts (i + 1)))) +
          (∑ i ∈ Finset.range n,
            prefixIntervalMass X (cuts i) (cuts (i + 1))) =
        ∑ i ∈ Finset.range n,
          prefixIntervalMass Y (cuts i) (cuts (i + 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      exact Nat.sub_add_cancel (hport i hi)
    have hclip : min X a ≤ min Y a := min_le_min hXY le_rfl
    have hdelta : min Y a - min X a ≤ Y - X := by
      have h := prefixIntervalMass_le_add_delta (H := X) (K := Y)
        (u := 0) (v := a) (by omega) hXY
      have h' : min Y a ≤ min X a + (Y - X) := by
        simpa [prefixIntervalMass] using h
      omega
    have hdiff' :
        (∑ i ∈ Finset.range n,
          (prefixIntervalMass Y (cuts i) (cuts (i + 1)) -
            prefixIntervalMass X (cuts i) (cuts (i + 1)))) = min Y a - min X a := by
      have hsumX' :
          (∑ i ∈ Finset.range n,
            prefixIntervalMass X (cuts i) (cuts (i + 1))) = min X a := by
        simpa [prefixIntervalMass] using hsumX
      have hsumY' :
          (∑ i ∈ Finset.range n,
            prefixIntervalMass Y (cuts i) (cuts (i + 1))) = min Y a := by
        simpa [prefixIntervalMass] using hsumY
      rw [hsumX', hsumY'] at hdiff
      omega
    have hdist :
        (∑ i ∈ Finset.range n,
          countDistance (prefixIntervalMass X (cuts i) (cuts (i + 1)))
            (prefixIntervalMass Y (cuts i) (cuts (i + 1)))) =
        ∑ i ∈ Finset.range n,
          (prefixIntervalMass Y (cuts i) (cuts (i + 1)) -
            prefixIntervalMass X (cuts i) (cuts (i + 1))) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hp := hport i hi
      simp [countDistance, Nat.sub_eq_zero_of_le hp]
    calc
      _ = min Y a - min X a := hdist.trans hdiff'
      _ ≤ Y - X := hdelta
      _ = countDistance X Y := by
        unfold countDistance
        rw [Nat.sub_eq_zero_of_le hXY]
        omega
  by_cases hHK : H ≤ K
  · exact hforward H K hHK
  · have hKH : K ≤ H := Nat.le_of_not_ge hHK
    have hrev := hforward K H hKH
    have hcomm (x y : ℕ) : countDistance x y = countDistance y x := by
      unfold countDistance
      omega
    have hsumcomm :
        (∑ i ∈ Finset.range n,
          countDistance (prefixIntervalMass H (cuts i) (cuts (i + 1)))
            (prefixIntervalMass K (cuts i) (cuts (i + 1)))) =
        (∑ i ∈ Finset.range n,
          countDistance (prefixIntervalMass K (cuts i) (cuts (i + 1)))
            (prefixIntervalMass H (cuts i) (cuts (i + 1)))) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hcomm _ _
    rw [hsumcomm, hcomm H K]
    exact hrev

theorem countDistance_interval_delta_eq_cross
    {a b c d : ℕ} (hac : a ≤ c) (hbd : b ≤ d) :
    countDistance (c - a) (d - b) =
      countDistance ((c - d) + (b - a)) ((d - c) + (a - b)) := by
  unfold countDistance
  omega

/-- Shift an indexed finite sum by one position; the boundary terms are the
only difference. -/
theorem sum_range_shift_add_boundary (f : ℕ → ℕ) (n : ℕ) :
    (∑ i ∈ Finset.range n, f (i + 1)) + f 0 =
      (∑ i ∈ Finset.range n, f i) + f n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      omega

/-- Clipping both cumulative-boundary paths at one threshold cannot increase
the l1 distance between their child prefix-count profiles, provided the
partitions have common endpoints. This is the moving-partition version of
`prefixIntervalMass_partition_distance`. -/
theorem prefixProfile_moving_partition_distance
    (H : ℕ) (cuts cuts' : ℕ → ℕ) (n a : ℕ)
    (hzero : cuts 0 = 0) (hzero' : cuts' 0 = 0)
    (hend : cuts n = a) (hend' : cuts' n = a)
    (hmono : ∀ i < n, cuts i ≤ cuts (i + 1))
    (hmono' : ∀ i < n, cuts' i ≤ cuts' (i + 1)) :
    (∑ i ∈ Finset.range n,
      countDistance (prefixIntervalMass H (cuts i) (cuts (i + 1)))
        (prefixIntervalMass H (cuts' i) (cuts' (i + 1)))) ≤
    ∑ i ∈ Finset.range n,
      countDistance (cuts (i + 1) - cuts i)
        (cuts' (i + 1) - cuts' i) := by
  let delta : ℕ → ℕ := fun i =>
    countDistance (min (cuts i) H) (min (cuts' i) H)
  let edge : ℕ → ℕ := fun i => countDistance (cuts i) (cuts' i)
  have hstep (i : ℕ) (hi : i < n) :
      countDistance (prefixIntervalMass H (cuts i) (cuts (i + 1)))
        (prefixIntervalMass H (cuts' i) (cuts' (i + 1))) +
        delta (i + 1) + edge i ≤
      countDistance (cuts (i + 1) - cuts i)
        (cuts' (i + 1) - cuts' i) + edge (i + 1) + delta i := by
    have hcut := hmono i hi
    have hcut' := hmono' i hi
    have hlocal := clipped_boundary_step_variation H (cuts i) (cuts' i)
      (cuts (i + 1)) (cuts' (i + 1)) hcut hcut'
    unfold clippedBoundaryPos clippedBoundaryNeg at hlocal
    have hminMono : min (cuts i) H ≤ min (cuts (i + 1)) H :=
      min_le_min hcut le_rfl
    have hminMono' : min (cuts' i) H ≤ min (cuts' (i + 1)) H :=
      min_le_min hcut' le_rfl
    have hprefix :
        prefixIntervalMass H (cuts i) (cuts (i + 1)) =
          min (cuts (i + 1)) H - min (cuts i) H := by
      unfold prefixIntervalMass
      omega
    have hprefix' :
        prefixIntervalMass H (cuts' i) (cuts' (i + 1)) =
          min (cuts' (i + 1)) H - min (cuts' i) H := by
      unfold prefixIntervalMass
      omega
    have hedge :
        countDistance (cuts (i + 1) - cuts i)
          (cuts' (i + 1) - cuts' i) =
        countDistance (cuts (i + 1) + cuts' i)
          (cuts' (i + 1) + cuts i) := by
      unfold countDistance
      omega
    have hmassDistance :
        countDistance (min (cuts (i + 1)) H - min (cuts i) H)
          (min (cuts' (i + 1)) H - min (cuts' i) H) =
        countDistance
          ((min (cuts (i + 1)) H - min (cuts' (i + 1)) H) +
            (min (cuts' i) H - min (cuts i) H))
          ((min (cuts' (i + 1)) H - min (cuts (i + 1)) H) +
            (min (cuts i) H - min (cuts' i) H)) := by
      exact countDistance_interval_delta_eq_cross hminMono hminMono'
    rw [hprefix, hprefix', hedge]
    rw [hmassDistance]
    simpa [delta, edge] using hlocal
  have hsum := Finset.sum_le_sum (s := Finset.range n)
    (fun i hi => hstep i (Finset.mem_range.mp hi))
  have hshiftDelta := sum_range_shift_add_boundary delta n
  have hshiftEdge := sum_range_shift_add_boundary edge n
  have hdelta0 : delta 0 = 0 := by
    simp [delta, hzero, hzero', countDistance]
  have hdeltaN : delta n = 0 := by
    simp [delta, hend, hend', countDistance]
  have hedge0 : edge 0 = 0 := by simp [edge, hzero, hzero', countDistance]
  have hedgeN : edge n = 0 := by simp [edge, hend, hend', countDistance]
  have hdeltaShift :
      (∑ i ∈ Finset.range n, delta (i + 1)) =
        (∑ i ∈ Finset.range n, delta i) := by
    have h := hshiftDelta
    omega
  have hedgeShift :
      (∑ i ∈ Finset.range n, edge (i + 1)) =
        (∑ i ∈ Finset.range n, edge i) := by
    have h := hshiftEdge
    omega
  rw [Finset.sum_add_distrib] at hsum
  rw [Finset.sum_add_distrib] at hsum
  rw [Finset.sum_add_distrib] at hsum
  rw [Finset.sum_add_distrib] at hsum
  rw [hdeltaShift, hedgeShift] at hsum
  omega

/-- A suffix interval is a reflected prefix interval. -/
theorem suffixIntervalMass_reflect (R u v a : ℕ)
    (huv : u ≤ v) (hva : v ≤ a) :
    suffixIntervalMass R u v =
      prefixIntervalMass (a - R) (a - v) (a - u) := by
  unfold suffixIntervalMass prefixIntervalMass
  by_cases hRu : R ≤ u
  · have hRuv : R - u = 0 := Nat.sub_eq_zero_of_le hRu
    have hfirst : v - u ≤ (a - R) - (a - v) := by omega
    have hsecond : v - u = (a - u) - (a - v) := by omega
    rw [hRuv, Nat.min_eq_left (Nat.zero_le (v - u)), Nat.sub_zero]
    rw [← hsecond, Nat.min_eq_right hfirst]
  · have huR : u ≤ R := Nat.le_of_not_ge hRu
    by_cases hRv : R ≤ v
    · have hleft : R - u ≤ v - u := by omega
      have hright : v - R ≤ v - u := by omega
      have hRdiff : v - R = (a - R) - (a - v) := by omega
      have hUdiff : v - u = (a - u) - (a - v) := by omega
      rw [Nat.min_eq_left hleft, ← hRdiff, ← hUdiff,
        Nat.min_eq_left hright]
      omega
    · have hvR : v ≤ R := Nat.le_of_not_ge hRv
      have hRuv : v - u ≤ R - u := by omega
      have hfirst : (a - R) - (a - v) = 0 := by omega
      rw [Nat.min_eq_right hRuv, Nat.sub_self, hfirst]
      simp

/-- The suffix counterpart of `prefixProfile_moving_partition_distance`,
obtained by reflecting the complete child partition. -/
theorem suffixProfile_moving_partition_distance
    (R : ℕ) (cuts cuts' : ℕ → ℕ) (n a : ℕ)
    (hzero : cuts 0 = 0) (hzero' : cuts' 0 = 0)
    (hend : cuts n = a) (hend' : cuts' n = a)
    (hmono : ∀ i < n, cuts i ≤ cuts (i + 1))
    (hmono' : ∀ i < n, cuts' i ≤ cuts' (i + 1)) :
    (∑ i ∈ Finset.range n,
      countDistance (suffixIntervalMass R (cuts i) (cuts (i + 1)))
        (suffixIntervalMass R (cuts' i) (cuts' (i + 1)))) ≤
    ∑ i ∈ Finset.range n,
      countDistance (cuts (i + 1) - cuts i)
        (cuts' (i + 1) - cuts' i) := by
  let rc : ℕ → ℕ := fun i => a - cuts (n - i)
  let rc' : ℕ → ℕ := fun i => a - cuts' (n - i)
  have hzeroR : rc 0 = 0 := by simp [rc, hend]
  have hzeroR' : rc' 0 = 0 := by simp [rc', hend']
  have hendR : rc n = a := by simp [rc, hzero]
  have hendR' : rc' n = a := by simp [rc', hzero']
  have hcutsToEnd : ∀ {j k : ℕ}, j ≤ k → k ≤ n → cuts j ≤ cuts k := by
    intro j k hjk hkn
    induction hjk with
    | refl => exact le_rfl
    | @step k hjk ih =>
        exact le_trans (ih (by omega)) (hmono k (by omega))
  have hcutsToEnd' : ∀ {j k : ℕ}, j ≤ k → k ≤ n → cuts' j ≤ cuts' k := by
    intro j k hjk hkn
    induction hjk with
    | refl => exact le_rfl
    | @step k hjk ih =>
        exact le_trans (ih (by omega)) (hmono' k (by omega))
  have hmonoR : ∀ i < n, rc i ≤ rc (i + 1) := by
    intro i hi
    have hidx : n - i = n - (i + 1) + 1 := by omega
    have hstep := hmono (n - (i + 1)) (by omega)
    dsimp [rc]
    rw [hidx]
    omega
  have hmonoR' : ∀ i < n, rc' i ≤ rc' (i + 1) := by
    intro i hi
    have hidx : n - i = n - (i + 1) + 1 := by omega
    have hstep := hmono' (n - (i + 1)) (by omega)
    dsimp [rc']
    rw [hidx]
    omega
  have hprefix := prefixProfile_moving_partition_distance (a - R)
    rc rc' n a hzeroR hzeroR' hendR hendR' hmonoR hmonoR'
  let prefErr : ℕ → ℕ := fun i =>
    countDistance (prefixIntervalMass (a - R) (rc i) (rc (i + 1)))
      (prefixIntervalMass (a - R) (rc' i) (rc' (i + 1)))
  let widthErr : ℕ → ℕ := fun i =>
    countDistance (rc (i + 1) - rc i) (rc' (i + 1) - rc' i)
  have hleft :
      (∑ i ∈ Finset.range n,
        countDistance (suffixIntervalMass R (cuts i) (cuts (i + 1)))
          (suffixIntervalMass R (cuts' i) (cuts' (i + 1)))) =
      ∑ i ∈ Finset.range n, prefErr i := by
    rw [← Finset.sum_range_reflect prefErr n]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have hidx : n - (n - 1 - i) = i + 1 := by omega
    have hidx' : n - (n - 1 - i + 1) = i := by omega
    dsimp [prefErr, rc, rc']
    rw [hidx, hidx']
    rw [suffixIntervalMass_reflect R (cuts i) (cuts (i + 1)) a
      (hmono i hi') (by rw [← hend]; exact hcutsToEnd (by omega) (by omega))]
    rw [suffixIntervalMass_reflect R (cuts' i) (cuts' (i + 1)) a
      (hmono' i hi') (by rw [← hend']; exact hcutsToEnd' (by omega) (by omega))]
  have hright :
      (∑ i ∈ Finset.range n,
        countDistance (rc (i + 1) - rc i) (rc' (i + 1) - rc' i)) =
      ∑ i ∈ Finset.range n,
        countDistance (cuts (i + 1) - cuts i) (cuts' (i + 1) - cuts' i) := by
    rw [← Finset.sum_range_reflect
      (fun i => countDistance (cuts (i + 1) - cuts i)
        (cuts' (i + 1) - cuts' i)) n]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have hidx : n - i = n - (i + 1) + 1 := by omega
    have hidx' : n - (i + 1) = n - 1 - i := by omega
    have hcut := hmono (n - (i + 1)) (by omega)
    have hcap : cuts (n - (i + 1) + 1) ≤ a := by
      rw [← hend]
      exact hcutsToEnd (j := n - (i + 1) + 1) (k := n) (by omega) (by omega)
    have hcut' := hmono' (n - (i + 1)) (by omega)
    have hcap' : cuts' (n - (i + 1) + 1) ≤ a := by
      rw [← hend']
      exact hcutsToEnd' (j := n - (i + 1) + 1) (k := n) (by omega) (by omega)
    have hstartVal : cuts (n - (i + 1)) = cuts (n - 1 - i) :=
      congrArg cuts hidx'
    have hendVal : cuts (n - (i + 1) + 1) = cuts (n - 1 - i + 1) :=
      congrArg (fun j => cuts (j + 1)) hidx'
    have hstartVal' : cuts' (n - (i + 1)) = cuts' (n - 1 - i) :=
      congrArg cuts' hidx'
    have hendVal' : cuts' (n - (i + 1) + 1) = cuts' (n - 1 - i + 1) :=
      congrArg (fun j => cuts' (j + 1)) hidx'
    have hrevWidth :
        rc (i + 1) - rc i =
          cuts (n - 1 - i + 1) - cuts (n - 1 - i) := by
      dsimp [rc]
      rw [hidx, hidx']
      omega
    have hrevWidth' :
        rc' (i + 1) - rc' i =
          cuts' (n - 1 - i + 1) - cuts' (n - 1 - i) := by
      dsimp [rc']
      rw [hidx, hidx']
      omega
    rw [hrevWidth, hrevWidth']
  rw [← hleft] at hprefix
  rw [hright] at hprefix
  exact hprefix

/-- The distance between two finite sums is at most the sum of their
termwise count distances. -/
/- For a complete partition, changing the two cut-front thresholds changes
the aggregate child deficit profile by at most the sum of the two front
displacements. Each child receives the prefix below `left` and the suffix
above `right`; this is the local stability statement needed to pass rank
errors through one D2 cut. -/
theorem aggregate_two_front_profile_distance
    (left left' right right' : ℕ) (cuts : ℕ → ℕ) (n a : ℕ)
    (hzero : cuts 0 = 0) (hend : cuts n = a)
    (hmono : ∀ i < n, cuts i ≤ cuts (i + 1)) :
    (∑ i ∈ Finset.range n,
      countDistance
        (prefixIntervalMass left (cuts i) (cuts (i + 1)) +
          suffixIntervalMass right (cuts i) (cuts (i + 1)))
        (prefixIntervalMass left' (cuts i) (cuts (i + 1)) +
          suffixIntervalMass right' (cuts i) (cuts (i + 1)))) ≤
      countDistance left left' + countDistance right right' := by
  have hprefix := prefixIntervalMass_partition_distance
    left left' cuts n a hzero hend hmono
  have hright := prefixIntervalMass_partition_distance
    right right' cuts n a hzero hend hmono
  have hwidth (H u v : ℕ) (huv : u ≤ v) :
      prefixIntervalMass H u v ≤ v - u := by
    unfold prefixIntervalMass
    omega
  have hlocal (i : ℕ) (hi : i ∈ Finset.range n) :
      countDistance
        (prefixIntervalMass left (cuts i) (cuts (i + 1)) +
          suffixIntervalMass right (cuts i) (cuts (i + 1)))
        (prefixIntervalMass left' (cuts i) (cuts (i + 1)) +
          suffixIntervalMass right' (cuts i) (cuts (i + 1))) ≤
      countDistance (prefixIntervalMass left (cuts i) (cuts (i + 1)))
        (prefixIntervalMass left' (cuts i) (cuts (i + 1))) +
      countDistance (prefixIntervalMass right (cuts i) (cuts (i + 1)))
        (prefixIntervalMass right' (cuts i) (cuts (i + 1))) := by
    have hi' : i < n := Finset.mem_range.mp hi
    have hmono' := hmono i hi'
    have hw1 := hwidth left (cuts i) (cuts (i + 1)) hmono'
    have hw2 := hwidth left' (cuts i) (cuts (i + 1)) hmono'
    have hw3 := hwidth right (cuts i) (cuts (i + 1)) hmono'
    have hw4 := hwidth right' (cuts i) (cuts (i + 1)) hmono'
    have hcomp :
        countDistance (suffixIntervalMass right (cuts i) (cuts (i + 1)))
          (suffixIntervalMass right' (cuts i) (cuts (i + 1))) =
        countDistance (prefixIntervalMass right (cuts i) (cuts (i + 1)))
          (prefixIntervalMass right' (cuts i) (cuts (i + 1))) := by
      unfold suffixIntervalMass countDistance
      omega
    unfold countDistance suffixIntervalMass at hcomp ⊢
    omega
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (countDistance (prefixIntervalMass left (cuts i) (cuts (i + 1)))
          (prefixIntervalMass left' (cuts i) (cuts (i + 1))) +
         countDistance (prefixIntervalMass right (cuts i) (cuts (i + 1)))
          (prefixIntervalMass right' (cuts i) (cuts (i + 1)))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hlocal i hi
    _ = (∑ i ∈ Finset.range n,
          countDistance (prefixIntervalMass left (cuts i) (cuts (i + 1)))
            (prefixIntervalMass left' (cuts i) (cuts (i + 1)))) +
        (∑ i ∈ Finset.range n,
          countDistance (prefixIntervalMass right (cuts i) (cuts (i + 1)))
            (prefixIntervalMass right' (cuts i) (cuts (i + 1)))) := by
      rw [Finset.sum_add_distrib]
    _ ≤ countDistance left left' + countDistance right right' :=
      add_le_add hprefix hright

/-- Changing both a complete child partition and the two cut fronts costs at
most the two front displacements plus twice the l1 change in child widths.
The partition term is the sum of the independently clipped prefix and suffix
profiles; the factor two is sharp for l1 (see
`moving_partition_two_front_counterexample`). -/
theorem aggregate_moving_partition_two_front_profile_distance
    (left left' right right' : ℕ) (cuts cuts' : ℕ → ℕ) (n a : ℕ)
    (hzero : cuts 0 = 0) (hzero' : cuts' 0 = 0)
    (hend : cuts n = a) (hend' : cuts' n = a)
    (hmono : ∀ i < n, cuts i ≤ cuts (i + 1))
    (hmono' : ∀ i < n, cuts' i ≤ cuts' (i + 1)) :
    (∑ i ∈ Finset.range n,
      countDistance
        (prefixIntervalMass left (cuts i) (cuts (i + 1)) +
          suffixIntervalMass right (cuts i) (cuts (i + 1)))
        (prefixIntervalMass left' (cuts' i) (cuts' (i + 1)) +
          suffixIntervalMass right' (cuts' i) (cuts' (i + 1)))) ≤
      countDistance left left' + countDistance right right' +
        2 * (∑ i ∈ Finset.range n,
          countDistance (cuts (i + 1) - cuts i)
            (cuts' (i + 1) - cuts' i)) := by
  have hprefix := prefixProfile_moving_partition_distance
    left cuts cuts' n a hzero hzero' hend hend' hmono hmono'
  have hsuffix := suffixProfile_moving_partition_distance
    right cuts cuts' n a hzero hzero' hend hend' hmono hmono'
  have hfront := aggregate_two_front_profile_distance
    left left' right right' cuts' n a hzero' hend' hmono'
  let prof (l r : ℕ) (cs : ℕ → ℕ) (i : ℕ) :=
    prefixIntervalMass l (cs i) (cs (i + 1)) +
      suffixIntervalMass r (cs i) (cs (i + 1))
  have hpartLocal (i : ℕ) :
      countDistance (prof left right cuts i) (prof left right cuts' i) ≤
        countDistance (prefixIntervalMass left (cuts i) (cuts (i + 1)))
          (prefixIntervalMass left (cuts' i) (cuts' (i + 1))) +
        countDistance (suffixIntervalMass right (cuts i) (cuts (i + 1)))
          (suffixIntervalMass right (cuts' i) (cuts' (i + 1))) := by
    dsimp [prof]
    unfold countDistance suffixIntervalMass
    omega
  have htri (i : ℕ) :
      countDistance (prof left right cuts i) (prof left' right' cuts' i) ≤
        countDistance (prof left right cuts i) (prof left right cuts' i) +
        countDistance (prof left right cuts' i) (prof left' right' cuts' i) :=
    countDistance_triangle _ _ _
  have hsum := Finset.sum_le_sum (s := Finset.range n)
    (fun i _ => htri i)
  have hpart := Finset.sum_le_sum (s := Finset.range n)
    (fun i _ => hpartLocal i)
  have hsumPart :
      (∑ i ∈ Finset.range n, countDistance (prof left right cuts i)
        (prof left right cuts' i)) ≤
        2 * (∑ i ∈ Finset.range n,
          countDistance (cuts (i + 1) - cuts i)
            (cuts' (i + 1) - cuts' i)) := by
    rw [Finset.sum_add_distrib] at hpart
    have hp := hprefix
    have hs := hsuffix
    dsimp [prof] at *
    omega
  have hsumFront :
      (∑ i ∈ Finset.range n, countDistance (prof left right cuts' i)
        (prof left' right' cuts' i)) ≤
        countDistance left left' + countDistance right right' := by
    simpa [prof] using hfront
  have hsum' := hsum
  dsimp [prof] at hsum'
  rw [Finset.sum_add_distrib] at hsum'
  calc
    (∑ i ∈ Finset.range n, countDistance
      (prefixIntervalMass left (cuts i) (cuts (i + 1)) +
        suffixIntervalMass right (cuts i) (cuts (i + 1)))
      (prefixIntervalMass left' (cuts' i) (cuts' (i + 1)) +
        suffixIntervalMass right' (cuts' i) (cuts' (i + 1))))
      ≤ (∑ i ∈ Finset.range n, countDistance (prof left right cuts i)
          (prof left right cuts' i)) +
        (∑ i ∈ Finset.range n, countDistance (prof left right cuts' i)
          (prof left' right' cuts' i)) := by
            simpa [prof] using hsum'
    _ ≤ 2 * (∑ i ∈ Finset.range n,
          countDistance (cuts (i + 1) - cuts i)
            (cuts' (i + 1) - cuts' i)) +
        (countDistance left left' + countDistance right right') :=
      Nat.add_le_add hsumPart hsumFront
    _ = countDistance left left' + countDistance right right' +
        2 * (∑ i ∈ Finset.range n,
          countDistance (cuts (i + 1) - cuts i)
            (cuts' (i + 1) - cuts' i)) := by omega

/-- With fixed low/high fronts, moving a complete child partition creates at
most one-sided leakage equal to the l1 change in child widths. The symmetric
l1 profile error can be twice as large; conservation of the total inherited
mass removes that factor for the directional quantity used by the D2
endpoint reserves. -/
theorem fixed_front_moving_partition_directional_leakage
    (left right : ℕ) (cuts cuts' : ℕ → ℕ) (n a : ℕ)
    (hzero : cuts 0 = 0) (hzero' : cuts' 0 = 0)
    (hend : cuts n = a) (hend' : cuts' n = a)
    (hmono : ∀ i < n, cuts i ≤ cuts (i + 1))
    (hmono' : ∀ i < n, cuts' i ≤ cuts' (i + 1))
    (hleft : left ≤ right) (hright : right ≤ a) :
    (∑ i : Fin n,
      ((prefixIntervalMass left (cuts i.val) (cuts (i.val + 1)) +
        suffixIntervalMass right (cuts i.val) (cuts (i.val + 1))) -
       (prefixIntervalMass left (cuts' i.val) (cuts' (i.val + 1)) +
        suffixIntervalMass right (cuts' i.val) (cuts' (i.val + 1))))) ≤
        (∑ i ∈ Finset.range n,
          countDistance (cuts (i + 1) - cuts i)
            (cuts' (i + 1) - cuts' i)) ∧
    (∑ i : Fin n,
      ((prefixIntervalMass left (cuts' i.val) (cuts' (i.val + 1)) +
        suffixIntervalMass right (cuts' i.val) (cuts' (i.val + 1))) -
       (prefixIntervalMass left (cuts i.val) (cuts (i.val + 1)) +
        suffixIntervalMass right (cuts i.val) (cuts (i.val + 1))))) ≤
        (∑ i ∈ Finset.range n,
          countDistance (cuts (i + 1) - cuts i)
            (cuts' (i + 1) - cuts' i)) := by
  let profile (cs : ℕ → ℕ) (i : ℕ) :=
    prefixIntervalMass left (cs i) (cs (i + 1)) +
      suffixIntervalMass right (cs i) (cs (i + 1))
  let actual : Fin n → ℕ := fun i => profile cuts i.val
  let reference : Fin n → ℕ := fun i => profile cuts' i.val
  let widthError : ℕ := ∑ i ∈ Finset.range n,
    countDistance (cuts (i + 1) - cuts i) (cuts' (i + 1) - cuts' i)
  have hprofileSum (cs : ℕ → ℕ) (hz : cs 0 = 0) (he : cs n = a)
      (hm : ∀ i < n, cs i ≤ cs (i + 1)) :
      (∑ i ∈ Finset.range n, profile cs i) = left + (a - right) := by
    have hp := prefixIntervalMass_partition left cs n a hz he hm
    have hp' : (∑ i ∈ Finset.range n,
        prefixIntervalMass left (cs i) (cs (i + 1))) = left := by
      rw [hp]
      simp [prefixIntervalMass, Nat.min_eq_left (le_trans hleft hright)]
    have hs := low_high_frontier_partition a 0 (a - right) cs n hz he hm
      (by omega) (by omega) (by omega)
    have hcomp : a - (a - right) = right := by omega
    rw [hcomp] at hs
    have hs' : (∑ i ∈ Finset.range n,
        suffixIntervalMass right (cs i) (cs (i + 1))) = a - right := by
      simpa [prefixIntervalMass] using hs.1
    dsimp [profile]
    rw [Finset.sum_add_distrib, hp', hs']
  have hactualSum : (∑ i : Fin n, actual i) = left + (a - right) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => profile cuts i)]
    simpa [actual, profile] using hprofileSum cuts hzero hend hmono
  have hreferenceSum : (∑ i : Fin n, reference i) = left + (a - right) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => profile cuts' i)]
    simpa [reference, profile] using hprofileSum cuts' hzero' hend' hmono'
  have hbalanced : (∑ i : Fin n, actual i) = ∑ i : Fin n, reference i :=
    hactualSum.trans hreferenceSum.symm
  have hprofileL1Range : (∑ i ∈ Finset.range n,
      countDistance (profile cuts i) (profile cuts' i)) ≤ 2 * widthError := by
    have h := aggregate_moving_partition_two_front_profile_distance
      left left right right cuts cuts' n a hzero hzero' hend hend' hmono hmono'
    dsimp [widthError] at *
    simpa [profile, countDistance] using h
  have hprofileL1 : (∑ i : Fin n,
      countDistance (actual i) (reference i)) ≤ 2 * widthError := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      countDistance (profile cuts i) (profile cuts' i))]
    simpa [actual, reference, profile] using hprofileL1Range
  have hdirections := balanced_port_directional_leakage
    actual reference (2 * widthError) hbalanced hprofileL1
  have hpositive : (∑ i ∈ Finset.range n,
      (profile cuts i - profile cuts' i)) ≤ widthError := by
    have h := hdirections.1
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => profile cuts i - profile cuts' i)] at h
    dsimp [widthError] at h
    omega
  have hnegative : (∑ i ∈ Finset.range n,
      (profile cuts' i - profile cuts i)) ≤ widthError := by
    have h := hdirections.2
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => profile cuts' i - profile cuts i)] at h
    dsimp [widthError] at h
    omega
  constructor
  · rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      profile cuts i - profile cuts' i)]
    simpa [profile, widthError] using hpositive
  · rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      profile cuts' i - profile cuts i)]
    simpa [profile, widthError] using hnegative

/-- For moving fronts and moving child boundaries, each direction of leakage
is bounded by one copy of the child-width variation plus the two front
displacements. This is sharper than the symmetric l1 estimate, which charges
twice the width variation. -/
theorem moving_two_front_partition_directional_leakage
    (left left' right right' : ℕ) (cuts cuts' : ℕ → ℕ) (n a : ℕ)
    (hzero : cuts 0 = 0) (hzero' : cuts' 0 = 0)
    (hend : cuts n = a) (hend' : cuts' n = a)
    (hmono : ∀ i < n, cuts i ≤ cuts (i + 1))
    (hmono' : ∀ i < n, cuts' i ≤ cuts' (i + 1))
    (hleft : left ≤ right) (hright : right ≤ a) :
    (∑ i : Fin n,
      ((prefixIntervalMass left (cuts i.val) (cuts (i.val + 1)) +
        suffixIntervalMass right (cuts i.val) (cuts (i.val + 1))) -
       (prefixIntervalMass left' (cuts' i.val) (cuts' (i.val + 1)) +
        suffixIntervalMass right' (cuts' i.val) (cuts' (i.val + 1))))) ≤
        (∑ i ∈ Finset.range n,
          countDistance (cuts (i + 1) - cuts i)
            (cuts' (i + 1) - cuts' i)) +
          (countDistance left left' + countDistance right right') ∧
    (∑ i : Fin n,
      ((prefixIntervalMass left' (cuts' i.val) (cuts' (i.val + 1)) +
        suffixIntervalMass right' (cuts' i.val) (cuts' (i.val + 1))) -
       (prefixIntervalMass left (cuts i.val) (cuts (i.val + 1)) +
        suffixIntervalMass right (cuts i.val) (cuts (i.val + 1))))) ≤
        (∑ i ∈ Finset.range n,
          countDistance (cuts (i + 1) - cuts i)
            (cuts' (i + 1) - cuts' i)) +
          (countDistance left left' + countDistance right right') := by
  let profile (l r : ℕ) (cs : ℕ → ℕ) (i : ℕ) :=
    prefixIntervalMass l (cs i) (cs (i + 1)) +
      suffixIntervalMass r (cs i) (cs (i + 1))
  let actual : Fin n → ℕ := fun i => profile left right cuts i.val
  let intermediate : Fin n → ℕ := fun i => profile left right cuts' i.val
  let target : Fin n → ℕ := fun i => profile left' right' cuts' i.val
  let widthError : ℕ := ∑ i ∈ Finset.range n,
    countDistance (cuts (i + 1) - cuts i) (cuts' (i + 1) - cuts' i)
  let frontError : ℕ := countDistance left left' + countDistance right right'
  have hfixed := fixed_front_moving_partition_directional_leakage
    left right cuts cuts' n a hzero hzero' hend hend' hmono hmono' hleft hright
  have hfrontRange : (∑ i ∈ Finset.range n,
      countDistance (profile left right cuts' i)
        (profile left' right' cuts' i)) ≤ frontError := by
    have h := aggregate_two_front_profile_distance
      left left' right right' cuts' n a hzero' hend' hmono'
    simpa [profile, frontError] using h
  have hfrontFin : (∑ i : Fin n, countDistance (intermediate i) (target i)) ≤
      frontError := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      countDistance (profile left right cuts' i)
        (profile left' right' cuts' i))]
    simpa [intermediate, target, profile] using hfrontRange
  have hfixedPos : (∑ i : Fin n, (actual i - intermediate i)) ≤ widthError := by
    simpa [actual, intermediate, profile, widthError] using hfixed.1
  have hfixedNeg : (∑ i : Fin n, (intermediate i - actual i)) ≤ widthError := by
    simpa [actual, intermediate, profile, widthError] using hfixed.2
  have hposTerm (i : Fin n) : actual i - target i ≤
      (actual i - intermediate i) + countDistance (intermediate i) (target i) := by
    unfold countDistance
    omega
  have hnegTerm (i : Fin n) : target i - actual i ≤
      (intermediate i - actual i) + countDistance (intermediate i) (target i) := by
    unfold countDistance
    omega
  have hpos : (∑ i : Fin n, (actual i - target i)) ≤ widthError + frontError := by
    calc
      _ ≤ ∑ i : Fin n,
          (((actual i - intermediate i) +
            countDistance (intermediate i) (target i))) :=
              Finset.sum_le_sum (fun i _ => hposTerm i)
      _ = (∑ i : Fin n, (actual i - intermediate i)) +
          (∑ i : Fin n, countDistance (intermediate i) (target i)) :=
            Finset.sum_add_distrib
      _ ≤ widthError + frontError := Nat.add_le_add hfixedPos hfrontFin
  have hneg : (∑ i : Fin n, (target i - actual i)) ≤ widthError + frontError := by
    calc
      _ ≤ ∑ i : Fin n,
          (((intermediate i - actual i) +
            countDistance (intermediate i) (target i))) :=
              Finset.sum_le_sum (fun i _ => hnegTerm i)
      _ = (∑ i : Fin n, (intermediate i - actual i)) +
          (∑ i : Fin n, countDistance (intermediate i) (target i)) :=
            Finset.sum_add_distrib
      _ ≤ widthError + frontError := Nat.add_le_add hfixedNeg hfrontFin
  constructor
  · simpa [actual, target, profile, widthError, frontError] using hpos
  · simpa [actual, target, profile, widthError, frontError] using hneg

theorem countDistance_sum_le {I : Type*} (s : Finset I) (f g : I → ℕ) :
    countDistance (∑ i ∈ s, f i) (∑ i ∈ s, g i) ≤
      ∑ i ∈ s, countDistance (f i) (g i) := by
  have hfg (i : I) : f i ≤ g i + countDistance (f i) (g i) := by
    by_cases h : f i ≤ g i
    · unfold countDistance
      rw [Nat.sub_eq_zero_of_le h]
      omega
    · have h' : g i ≤ f i := Nat.le_of_not_ge h
      unfold countDistance
      rw [Nat.sub_eq_zero_of_le h']
      omega
  have hgf (i : I) : g i ≤ f i + countDistance (f i) (g i) := by
    by_cases h : g i ≤ f i
    · unfold countDistance
      rw [Nat.sub_eq_zero_of_le h]
      omega
    · have h' : f i ≤ g i := Nat.le_of_not_ge h
      unfold countDistance
      rw [Nat.sub_eq_zero_of_le h']
      omega
  have hsumfg :
      (∑ i ∈ s, f i) ≤ (∑ i ∈ s, g i) +
        ∑ i ∈ s, countDistance (f i) (g i) := by
    calc
      (∑ i ∈ s, f i) ≤
          ∑ i ∈ s, (g i + countDistance (f i) (g i)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hfg i
      _ = _ := Finset.sum_add_distrib
  have hsumgf :
      (∑ i ∈ s, g i) ≤ (∑ i ∈ s, f i) +
        ∑ i ∈ s, countDistance (f i) (g i) := by
    calc
      (∑ i ∈ s, g i) ≤
          ∑ i ∈ s, (f i + countDistance (f i) (g i)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hgf i
      _ = _ := Finset.sum_add_distrib
  by_cases h : (∑ i ∈ s, f i) ≤ (∑ i ∈ s, g i)
  · change ((∑ i ∈ s, f i) - (∑ i ∈ s, g i)) +
      ((∑ i ∈ s, g i) - (∑ i ∈ s, f i)) ≤
      ∑ i ∈ s, countDistance (f i) (g i)
    rw [Nat.sub_eq_zero_of_le h, Nat.zero_add]
    omega
  · have h' : (∑ i ∈ s, g i) ≤ (∑ i ∈ s, f i) := Nat.le_of_not_ge h
    change ((∑ i ∈ s, f i) - (∑ i ∈ s, g i)) +
      ((∑ i ∈ s, g i) - (∑ i ∈ s, f i)) ≤
      ∑ i ∈ s, countDistance (f i) (g i)
    rw [Nat.sub_eq_zero_of_le h', Nat.add_zero]
    omega

/-- For ragged columnwise ports, aggregate l1 displacement across all ports
is at most the sum of the parent-prefix displacements across columns. Each
port may be a different row interval in each column; only completeness and
monotonicity of each column's cut partition are required. -/
theorem ragged_column_port_partition_distance
    (columns ports : ℕ) (cuts : ℕ → ℕ → ℕ) (height : ℕ → ℕ)
    (actualPrefix idealPrefix : ℕ → ℕ)
    (hzero : ∀ c < columns, cuts c 0 = 0)
    (hend : ∀ c < columns, cuts c ports = height c)
    (hmono : ∀ c < columns, ∀ i < ports, cuts c i ≤ cuts c (i + 1)) :
    (∑ i ∈ Finset.range ports,
      countDistance
        (∑ c ∈ Finset.range columns,
          prefixIntervalMass (actualPrefix c) (cuts c i) (cuts c (i + 1)))
        (∑ c ∈ Finset.range columns,
          prefixIntervalMass (idealPrefix c) (cuts c i) (cuts c (i + 1)))) ≤
      ∑ c ∈ Finset.range columns,
        countDistance (actualPrefix c) (idealPrefix c) := by
  calc
    _ ≤ ∑ i ∈ Finset.range ports,
        ∑ c ∈ Finset.range columns,
          countDistance
            (prefixIntervalMass (actualPrefix c) (cuts c i) (cuts c (i + 1)))
            (prefixIntervalMass (idealPrefix c) (cuts c i) (cuts c (i + 1))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact countDistance_sum_le (Finset.range columns)
        (fun c => prefixIntervalMass (actualPrefix c) (cuts c i) (cuts c (i + 1)))
        (fun c => prefixIntervalMass (idealPrefix c) (cuts c i) (cuts c (i + 1)))
    _ = ∑ c ∈ Finset.range columns,
        ∑ i ∈ Finset.range ports,
          countDistance
            (prefixIntervalMass (actualPrefix c) (cuts c i) (cuts c (i + 1)))
            (prefixIntervalMass (idealPrefix c) (cuts c i) (cuts c (i + 1))) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ c ∈ Finset.range columns,
        countDistance (actualPrefix c) (idealPrefix c) := by
      apply Finset.sum_le_sum
      intro c hc
      exact prefixIntervalMass_partition_distance
        (actualPrefix c) (idealPrefix c) (cuts c) ports (height c)
        (hzero c (Finset.mem_range.mp hc))
        (hend c (Finset.mem_range.mp hc))
        (fun i hi => hmono c (Finset.mem_range.mp hc) i hi)

/-- Aggregate child transfer error over an arbitrary finite index set,
without multiplying parent displacement by the number of children. -/
theorem aggregate_child_count_error_over_finset
    {I : Type*} (s : Finset I)
    (actual reference ideal transfer : I → ℕ) (parentError : ℕ)
    (hTransferUpper : ∀ i ∈ s, actual i ≤ reference i + transfer i)
    (hTransferLower : ∀ i ∈ s, reference i ≤ actual i + transfer i)
    (hParent : ∑ i ∈ s, countDistance (reference i) (ideal i) ≤ parentError) :
    ∑ i ∈ s, countDistance (actual i) (ideal i) ≤
      parentError + ∑ i ∈ s, transfer i := by
  have hlocal (i : I) (hi : i ∈ s) :
      countDistance (actual i) (reference i) ≤ transfer i := by
    by_cases h : actual i ≤ reference i
    · unfold countDistance
      rw [Nat.sub_eq_zero_of_le h]
      have ht := hTransferLower i hi
      omega
    · have h' : reference i ≤ actual i := Nat.le_of_not_ge h
      unfold countDistance
      rw [Nat.sub_eq_zero_of_le h']
      have ht := hTransferUpper i hi
      omega
  calc
    ∑ i ∈ s, countDistance (actual i) (ideal i) ≤
        ∑ i ∈ s,
          (countDistance (actual i) (reference i) +
            countDistance (reference i) (ideal i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact countDistance_triangle (actual i) (ideal i) (reference i)
    _ = (∑ i ∈ s, countDistance (actual i) (reference i)) +
        (∑ i ∈ s, countDistance (reference i) (ideal i)) :=
      Finset.sum_add_distrib
    _ ≤ parentError + ∑ i ∈ s, transfer i := by
      have hlocalSum :
          (∑ i ∈ s, countDistance (actual i) (reference i)) ≤
            ∑ i ∈ s, transfer i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hlocal i hi
      omega

/-- Ragged columnwise port errors aggregate to the parent-prefix errors plus
the summed local transfers. The port reference is allowed a different row
interval in every column. -/
theorem aggregate_ragged_column_port_error_le_parent_add_transfer
    (columns ports : ℕ) (cuts : ℕ → ℕ → ℕ) (height : ℕ → ℕ)
    (actualPrefix idealPrefix : ℕ → ℕ)
    (actualPort transfer : ℕ → ℕ)
    (hzero : ∀ c < columns, cuts c 0 = 0)
    (hend : ∀ c < columns, cuts c ports = height c)
    (hmono : ∀ c < columns, ∀ i < ports, cuts c i ≤ cuts c (i + 1))
    (hTransferUpper : ∀ i < ports,
      actualPort i ≤
        (∑ c ∈ Finset.range columns,
          prefixIntervalMass (actualPrefix c) (cuts c i) (cuts c (i + 1))) + transfer i)
    (hTransferLower : ∀ i < ports,
      (∑ c ∈ Finset.range columns,
        prefixIntervalMass (actualPrefix c) (cuts c i) (cuts c (i + 1))) ≤
          actualPort i + transfer i) :
    (∑ i ∈ Finset.range ports,
      countDistance (actualPort i)
        (∑ c ∈ Finset.range columns,
          prefixIntervalMass (idealPrefix c) (cuts c i) (cuts c (i + 1)))) ≤
      (∑ c ∈ Finset.range columns,
        countDistance (actualPrefix c) (idealPrefix c)) +
        ∑ i ∈ Finset.range ports, transfer i := by
  apply aggregate_child_count_error_over_finset (Finset.range ports)
    actualPort
    (fun i => ∑ c ∈ Finset.range columns,
      prefixIntervalMass (actualPrefix c) (cuts c i) (cuts c (i + 1)))
    (fun i => ∑ c ∈ Finset.range columns,
      prefixIntervalMass (idealPrefix c) (cuts c i) (cuts c (i + 1)))
    transfer
    (∑ c ∈ Finset.range columns,
      countDistance (actualPrefix c) (idealPrefix c))
  · intro i hi
    exact hTransferUpper i (Finset.mem_range.mp hi)
  · intro i hi
    exact hTransferLower i (Finset.mem_range.mp hi)
  · exact ragged_column_port_partition_distance columns ports cuts height
      actualPrefix idealPrefix hzero hend hmono

/-- Direct row-major form of the ragged port transfer theorem. A complete
partition of the flattened sender ranks induces its column cuts internally,
so callers need only provide the local two-sided transfer bounds. -/
theorem aggregate_flat_row_major_port_error_le_parent_add_transfer
    (rows columns ports : ℕ) (boundary : ℕ → ℕ)
    (actualPrefix idealPrefix actualPort transfer : ℕ → ℕ)
    (hboundary_zero : boundary 0 = 0)
    (hboundary_end : boundary ports = rows * columns)
    (hboundary_mono : ∀ i < ports, boundary i ≤ boundary (i + 1))
    (hTransferUpper : ∀ i < ports,
      actualPort i ≤
        (∑ c ∈ Finset.range columns,
          prefixIntervalMass (actualPrefix c)
            (flatBoundaryColumnCut rows columns (boundary i) c)
            (flatBoundaryColumnCut rows columns (boundary (i + 1)) c)) + transfer i)
    (hTransferLower : ∀ i < ports,
      (∑ c ∈ Finset.range columns,
        prefixIntervalMass (actualPrefix c)
          (flatBoundaryColumnCut rows columns (boundary i) c)
          (flatBoundaryColumnCut rows columns (boundary (i + 1)) c)) ≤
            actualPort i + transfer i) :
    (∑ i ∈ Finset.range ports,
      countDistance (actualPort i)
        (∑ c ∈ Finset.range columns,
          prefixIntervalMass (idealPrefix c)
            (flatBoundaryColumnCut rows columns (boundary i) c)
            (flatBoundaryColumnCut rows columns (boundary (i + 1)) c))) ≤
      (∑ c ∈ Finset.range columns,
        countDistance (actualPrefix c) (idealPrefix c)) +
        ∑ i ∈ Finset.range ports, transfer i := by
  have hcuts := flat_boundary_column_cuts_partition rows columns ports boundary
    hboundary_zero hboundary_end hboundary_mono
  apply aggregate_ragged_column_port_error_le_parent_add_transfer
    columns ports
    (fun c i => flatBoundaryColumnCut rows columns (boundary i) c)
    (fun _ => rows) actualPrefix idealPrefix actualPort transfer
  · intro c hc
    exact (hcuts c hc).1
  · intro c hc
    exact (hcuts c hc).2.1
  · intro c hc i hi
    exact (hcuts c hc).2.2 i hi
  · exact hTransferUpper
  · exact hTransferLower

/-- Direct fixed-mask form of aggregate port transfer. The static sender is
any ordered list of live wires, and `columnOf` records the column of each
address; no rectangular or contiguous physical-mask assumption is needed. -/
theorem aggregate_ordered_mask_port_error_le_parent_add_transfer
    (columns total ports : ℕ) (columnOf boundary : ℕ → ℕ)
    (actualPrefix idealPrefix actualPort transfer : ℕ → ℕ)
    (hboundary_zero : boundary 0 = 0)
    (hboundary_end : boundary ports = total)
    (hboundary_mono : ∀ i < ports, boundary i ≤ boundary (i + 1))
    (hTransferUpper : ∀ i < ports,
      actualPort i ≤
        (∑ c ∈ Finset.range columns,
          prefixIntervalMass (actualPrefix c)
            (orderedColumnCut columnOf c (boundary i))
            (orderedColumnCut columnOf c (boundary (i + 1)))) + transfer i)
    (hTransferLower : ∀ i < ports,
      (∑ c ∈ Finset.range columns,
        prefixIntervalMass (actualPrefix c)
          (orderedColumnCut columnOf c (boundary i))
          (orderedColumnCut columnOf c (boundary (i + 1)))) ≤
            actualPort i + transfer i) :
    (∑ i ∈ Finset.range ports,
      countDistance (actualPort i)
        (∑ c ∈ Finset.range columns,
          prefixIntervalMass (idealPrefix c)
            (orderedColumnCut columnOf c (boundary i))
            (orderedColumnCut columnOf c (boundary (i + 1))))) ≤
      (∑ c ∈ Finset.range columns,
        countDistance (actualPrefix c) (idealPrefix c)) +
        ∑ i ∈ Finset.range ports, transfer i := by
  have hcuts := ordered_column_cuts_partition columnOf total ports boundary
    hboundary_zero hboundary_end hboundary_mono
  apply aggregate_ragged_column_port_error_le_parent_add_transfer
    columns ports (fun c i => orderedColumnCut columnOf c (boundary i))
    (fun c => orderedColumnCut columnOf c total)
    actualPrefix idealPrefix actualPort transfer
  · intro c hc
    exact (hcuts c).1
  · intro c hc
    rw [hboundary_end]
  · intro c hc i hi
    exact (hcuts c).2.2 i hi
  · exact hTransferUpper
  · exact hTransferLower

/-- If the signed interval errors in one column all point in the direction of
the total column deviation, their absolute values sum exactly to that
deviation's absolute value. The fixed-mask interval proof can establish this
from nesting plus conservation. -/
theorem column_port_abs_error_eq_total_deviation
    {P : Type*} [Fintype P]
    (portError : P → ℚ) (columnDeviation : ℚ)
    (hTotal : (∑ p : P, portError p) = columnDeviation)
    (hSameSign : ∀ p, if 0 ≤ columnDeviation then 0 ≤ portError p
      else portError p ≤ 0) :
    (∑ p : P, |portError p|) = |columnDeviation| := by
  by_cases hnonneg : 0 ≤ columnDeviation
  · have hsign (p : P) : 0 ≤ portError p := by
      simpa [hnonneg] using hSameSign p
    calc
      (∑ p : P, |portError p|) = ∑ p : P, portError p := by
        apply Finset.sum_congr rfl
        intro p hp
        exact abs_of_nonneg (hsign p)
      _ = columnDeviation := hTotal
      _ = |columnDeviation| := (abs_of_nonneg hnonneg).symm
  · have hneg : columnDeviation < 0 := lt_of_not_ge hnonneg
    have hsign (p : P) : portError p ≤ 0 := by
      simpa [hnonneg] using hSameSign p
    calc
      (∑ p : P, |portError p|) = ∑ p : P, -portError p := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [abs_of_nonpos (hsign p)]
      _ = -(∑ p : P, portError p) := by simp
      _ = |columnDeviation| := by rw [hTotal, abs_of_neg hneg]

/-- Rational mass of a prefix of height `h` inside the interval `[u,v)`. -/
def ratPrefixIntervalMass (h u v : ℚ) : ℚ := min (max (h - u) 0) (v - u)

/-- The natural-number interval count is the difference of cumulative
prefix counts at its two boundaries. -/
theorem prefixIntervalMass_eq_cumulative_diff_nat
    (H u v : ℕ) (huv : u ≤ v) :
    prefixIntervalMass H u v = min H v - min H u := by
  by_cases hHu : H ≤ u
  · have hHv : H ≤ v := le_trans hHu huv
    simp [prefixIntervalMass, Nat.sub_eq_zero_of_le hHu,
      Nat.min_eq_left hHv, Nat.min_eq_left hHu]
  · have huH : u ≤ H := le_of_not_ge hHu
    by_cases hHv : H ≤ v
    · have htail : H - u ≤ v - u := Nat.sub_le_sub_right hHv u
      rw [prefixIntervalMass, Nat.min_eq_left htail,
        Nat.min_eq_left hHv, Nat.min_eq_right huH]
    · have hvH : v ≤ H := le_of_not_ge hHv
      have htail : v - u ≤ H - u := Nat.sub_le_sub_right hvH u
      rw [prefixIntervalMass, Nat.min_eq_right htail,
        Nat.min_eq_right hvH, Nat.min_eq_right huH]

/-- The signed error of a rank interval is exactly the difference of its
endpoint prefix defects. This is the local algebraic form needed to transport
spatial rank error through port cuts. -/
theorem prefixIntervalMass_signed_error_eq_endpoint_defects
    (actual ideal u v : ℕ) (huv : u ≤ v) :
    ((prefixIntervalMass actual u v : ℚ) -
        (prefixIntervalMass ideal u v : ℚ)) =
      (((min actual v : ℕ) : ℚ) - ((min ideal v : ℕ) : ℚ)) -
        (((min actual u : ℕ) : ℚ) - ((min ideal u : ℕ) : ℚ)) := by
  have hactual := prefixIntervalMass_eq_cumulative_diff_nat actual u v huv
  have hideal := prefixIntervalMass_eq_cumulative_diff_nat ideal u v huv
  have hactualMono : min actual u ≤ min actual v := min_le_min le_rfl huv
  have hidealMono : min ideal u ≤ min ideal v := min_le_min le_rfl huv
  rw [hactual, hideal]
  rw [Nat.cast_sub hactualMono, Nat.cast_sub hidealMono]
  ring

/-- Discrete integration by parts for signed prefix defects. It converts a
weighted sum of port errors into endpoint terms plus changes in the spatial
weights; this is the algebraic shape needed for a distance-moment recurrence. -/
theorem sum_weighted_prefix_increments_by_parts
    (weight defect : ℕ → ℚ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      weight i * (defect (i + 1) - defect i)) =
      weight n * defect (n + 1) - weight 0 * defect 0 +
        ∑ i ∈ Finset.range n,
          (weight i - weight (i + 1)) * defect (i + 1) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

/-- The clamped interval mass is the difference of the cumulative prefix
counts at its boundaries. -/
theorem ratPrefixIntervalMass_eq_cumulative_diff
    (h u v : ℚ) (huv : u ≤ v) :
    ratPrefixIntervalMass h u v = min h v - min h u := by
  by_cases hhu : h ≤ u
  · have hhv : h ≤ v := le_trans hhu huv
    have huv0 : 0 ≤ v - u := sub_nonneg.mpr huv
    simp [ratPrefixIntervalMass, max_eq_right (sub_nonpos.mpr hhu),
      min_eq_left huv0, min_eq_left hhv, min_eq_left hhu]
  · have huh : u < h := lt_of_not_ge hhu
    by_cases hhv : h ≤ v
    · have hhu0 : 0 ≤ h - u := sub_nonneg.mpr huh.le
      have htail : h - u ≤ v - u := sub_le_sub_right hhv u
      simp [ratPrefixIntervalMass, max_eq_left hhu0, min_eq_left htail,
        min_eq_left hhv, min_eq_right huh.le]
    · have hvh : v < h := lt_of_not_ge hhv
      have huv0 : 0 ≤ v - u := sub_nonneg.mpr huv
      have htail : v - u ≤ h - u := sub_le_sub_right hvh.le u
      simp [ratPrefixIntervalMass, max_eq_left (sub_nonneg.mpr huh.le),
        min_eq_right htail, min_eq_right hvh.le, min_eq_right huh.le]

/-- Rational interval mass agrees with the natural wire count at integer
prefix heights and integer boundaries. -/
theorem ratPrefixIntervalMass_nat_eq
    (H u v : ℕ) (huv : u ≤ v) :
    (prefixIntervalMass H u v : ℚ) =
      ratPrefixIntervalMass (H : ℚ) (u : ℚ) (v : ℚ) := by
  have huvQ : (u : ℚ) ≤ (v : ℚ) := Nat.cast_le.mpr huv
  rw [ratPrefixIntervalMass_eq_cumulative_diff _ _ _ huvQ,
    prefixIntervalMass_eq_cumulative_diff_nat H u v huv]
  have hmin : min H u ≤ min H v := min_le_min le_rfl huv
  rw [Nat.cast_sub hmin]
  norm_cast

/-- Increasing the prefix height cannot decrease the mass in a fixed
interval. -/
theorem ratPrefixIntervalMass_mono {h k u v : ℚ} (hhk : h ≤ k) :
    ratPrefixIntervalMass h u v ≤ ratPrefixIntervalMass k u v := by
  unfold ratPrefixIntervalMass
  exact min_le_min (max_le_max_right 0 (sub_le_sub_right hhk u)) le_rfl

/-- Telescoping sum of successive cumulative differences. -/
theorem sum_range_cumulative_diff (g : ℕ → ℚ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (g (i + 1) - g i)) = g n - g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- A complete rational interval partition contains exactly the prefix mass,
including when the final interval boundary is ragged. -/
theorem ratPrefixIntervalMass_partition
    (h : ℚ) (cuts : ℕ → ℚ) (n : ℕ) (width : ℚ)
    (hzero : cuts 0 = 0) (hend : cuts n = width)
    (hmono : ∀ i < n, cuts i ≤ cuts (i + 1))
    (hh : 0 ≤ h) (hwidth : h ≤ width) :
    (∑ i ∈ Finset.range n, ratPrefixIntervalMass h (cuts i) (cuts (i + 1))) = h := by
  calc
    (∑ i ∈ Finset.range n, ratPrefixIntervalMass h (cuts i) (cuts (i + 1))) =
        ∑ i ∈ Finset.range n,
          (min h (cuts (i + 1)) - min h (cuts i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply ratPrefixIntervalMass_eq_cumulative_diff h (cuts i) (cuts (i + 1))
        (hmono i (Finset.mem_range.mp hi))
    _ = min h (cuts n) - min h (cuts 0) :=
      sum_range_cumulative_diff (fun i => min h (cuts i)) n
    _ = h := by rw [hzero, hend, min_eq_left hwidth, min_eq_right hh]; ring

/-- For two prefix heights, the signed errors over a complete interval
partition all have one sign and their sum is the height difference. Their l1
sum is therefore exactly that difference in absolute value. -/
theorem rational_prefix_port_error_partition
    (actual reference : ℚ) (cuts : ℕ → ℚ) (ports : ℕ) (width : ℚ)
    (hzero : cuts 0 = 0) (hend : cuts ports = width)
    (hmono : ∀ i < ports, cuts i ≤ cuts (i + 1))
    (hactual : 0 ≤ actual) (href : 0 ≤ reference)
    (hactual_width : actual ≤ width) (href_width : reference ≤ width) :
    (∑ i ∈ Finset.range ports,
      |ratPrefixIntervalMass actual (cuts i) (cuts (i + 1)) -
        ratPrefixIntervalMass reference (cuts i) (cuts (i + 1))|) =
      |actual - reference| := by
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    |ratPrefixIntervalMass actual (cuts i) (cuts (i + 1)) -
      ratPrefixIntervalMass reference (cuts i) (cuts (i + 1))|)]
  apply column_port_abs_error_eq_total_deviation
  · have hactual_part := ratPrefixIntervalMass_partition actual cuts ports width
      hzero hend hmono hactual hactual_width
    have href_part := ratPrefixIntervalMass_partition reference cuts ports width
      hzero hend hmono href href_width
    have hactual_partFin :
        (∑ i : Fin ports,
          ratPrefixIntervalMass actual (cuts i.val) (cuts (i.val + 1))) = actual := by
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
        ratPrefixIntervalMass actual (cuts i) (cuts (i + 1)))]
      exact hactual_part
    have href_partFin :
        (∑ i : Fin ports,
          ratPrefixIntervalMass reference (cuts i.val) (cuts (i.val + 1))) = reference := by
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
        ratPrefixIntervalMass reference (cuts i) (cuts (i + 1)))]
      exact href_part
    simp only [Finset.sum_sub_distrib]
    rw [hactual_partFin, href_partFin]
  · intro i
    by_cases h : reference ≤ actual
    · have hd : 0 ≤ actual - reference := sub_nonneg.mpr h
      simp [hd]
      exact ratPrefixIntervalMass_mono h
    · have hstrict : actual < reference := lt_of_not_ge h
      have hd : ¬ 0 ≤ actual - reference := by linarith
      simp [hd]
      exact ratPrefixIntervalMass_mono hstrict.le

/-- Integer actual column counts and rational ideal heights satisfy the same
complete-partition l1 identity. This is the concrete arithmetic premise used
by the variance-to-port aggregation theorem. -/
theorem nat_actual_rational_reference_port_partition
    (actual : ℕ) (reference : ℚ) (cuts : ℕ → ℕ) (ports : ℕ)
    (hzero : cuts 0 = 0) (width : ℕ) (hend : cuts ports = width)
    (hmono : ∀ i < ports, cuts i ≤ cuts (i + 1))
    (hactual_width : actual ≤ width) (href : reference ≤ (width : ℚ))
    (href_nonneg : 0 ≤ reference) :
    (∑ i ∈ Finset.range ports,
      |(prefixIntervalMass actual (cuts i) (cuts (i + 1)) : ℚ) -
        ratPrefixIntervalMass reference (cuts i) (cuts (i + 1))|) =
      |(actual : ℚ) - reference| := by
  calc
    (∑ i ∈ Finset.range ports,
      |(prefixIntervalMass actual (cuts i) (cuts (i + 1)) : ℚ) -
        ratPrefixIntervalMass reference (cuts i) (cuts (i + 1))|) =
      ∑ i ∈ Finset.range ports,
        |ratPrefixIntervalMass (actual : ℚ) (cuts i) (cuts (i + 1)) -
          ratPrefixIntervalMass reference (cuts i) (cuts (i + 1))| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ratPrefixIntervalMass_nat_eq actual (cuts i) (cuts (i + 1))
        (hmono i (Finset.mem_range.mp hi))]
    _ = |(actual : ℚ) - reference| := by
      apply rational_prefix_port_error_partition (actual : ℚ) reference
        (fun i => (cuts i : ℚ)) ports (width : ℚ)
      · simp [hzero]
      · exact_mod_cast hend
      · intro i hi
        exact_mod_cast hmono i hi
      · exact_mod_cast Nat.zero_le actual
      · exact href_nonneg
      · exact_mod_cast hactual_width
      · exact href

/-- If each sender column's signed port errors partition its total column
deviation without cancellation, then the aggregate port l1 error is bounded
by Cauchy--Schwarz in terms of the sum of squared column deviations. This is
the algebraic variance-to-port interface; the concrete interval geometry
must still establish `hColumn`. -/
theorem aggregate_port_l1_sq_le_columns_mul_deviation_sq
    {C P : Type*} [Fintype C] [Fintype P]
    (portError : C → P → ℚ) (columnDeviation : C → ℚ)
    (hColumn : ∀ c, (∑ p : P, |portError c p|) = |columnDeviation c|) :
    (∑ p : P, |∑ c : C, portError c p|) ^ 2 ≤
      (Fintype.card C : ℚ) * ∑ c : C, columnDeviation c ^ 2 := by
  have hL1 :
      (∑ p : P, |∑ c : C, portError c p|) ≤
        ∑ c : C, |columnDeviation c| := by
    calc
      (∑ p : P, |∑ c : C, portError c p|) ≤
          ∑ p : P, ∑ c : C, |portError c p| := by
        apply Finset.sum_le_sum
        intro p hp
        exact Finset.abs_sum_le_sum_abs (fun c => portError c p)
          (Finset.univ : Finset C)
      _ = ∑ c : C, ∑ p : P, |portError c p| := by
        rw [Finset.sum_comm]
      _ = ∑ c : C, |columnDeviation c| := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hColumn c
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset C) (fun _ : C => (1 : ℚ))
      (fun c => |columnDeviation c|)
  have hCauchy' :
      (∑ c : C, |columnDeviation c|) ^ 2 ≤
        (Fintype.card C : ℚ) * ∑ c : C, columnDeviation c ^ 2 := by
    simpa using hCauchy
  have hnonneg : 0 ≤ ∑ p : P, |∑ c : C, portError c p| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  nlinarith [hL1, hCauchy']

/-- For a ragged sender whose sorted column prefixes are split into complete
interval partitions, the squared aggregate port l1 error is bounded by the
number of columns times the sum of squared deviations from any uniform
density `theta`. This is the variance-to-port transfer in the form needed by
the D2 fixed-mask interface. -/
theorem ragged_nat_rational_port_variance_bound
    {C : Type*} [Fintype C]
    (actual width : C → ℕ) (cuts : C → ℕ → ℕ) (ports : ℕ) (theta : ℚ)
    (hzero : ∀ c, cuts c 0 = 0)
    (hend : ∀ c, cuts c ports = width c)
    (hmono : ∀ c i, i < ports → cuts c i ≤ cuts c (i + 1))
    (hactual : ∀ c, actual c ≤ width c)
    (htheta_nonneg : 0 ≤ theta) (htheta_le_one : theta ≤ 1) :
    (∑ p : Fin ports,
      |∑ c : C,
        ((prefixIntervalMass (actual c) (cuts c p.val) (cuts c (p.val + 1)) : ℚ) -
          ratPrefixIntervalMass (theta * (width c : ℚ))
            (cuts c p.val) (cuts c (p.val + 1)))|) ^ 2 ≤
      (Fintype.card C : ℚ) *
        ∑ c : C, ((actual c : ℚ) - theta * (width c : ℚ)) ^ 2 := by
  let portError : C → Fin ports → ℚ := fun c p =>
    (prefixIntervalMass (actual c) (cuts c p.val) (cuts c (p.val + 1)) : ℚ) -
      ratPrefixIntervalMass (theta * (width c : ℚ))
        (cuts c p.val) (cuts c (p.val + 1))
  let columnDeviation : C → ℚ := fun c =>
    (actual c : ℚ) - theta * (width c : ℚ)
  have hColumn (c : C) :
      (∑ p : Fin ports, |portError c p|) = |columnDeviation c| := by
    dsimp [portError, columnDeviation]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      |(prefixIntervalMass (actual c) (cuts c i) (cuts c (i + 1)) : ℚ) -
        ratPrefixIntervalMass (theta * (width c : ℚ))
          (cuts c i) (cuts c (i + 1))|)]
    apply nat_actual_rational_reference_port_partition
      (actual c) (theta * (width c : ℚ)) (cuts c) ports
      (hzero c) (width c) (hend c) (hmono c) (hactual c)
    · have hwidth_nonneg : 0 ≤ (width c : ℚ) := Nat.cast_nonneg _
      nlinarith [htheta_le_one]
    · positivity
  simpa [portError, columnDeviation] using
    aggregate_port_l1_sq_le_columns_mul_deviation_sq portError columnDeviation hColumn

/-- Fixed-mask version of the ragged variance-to-port bound. An arbitrary
static ordered list of live wires induces the complete column interval cuts;
no rectangular layout assumption is needed. The actual column-prefix heights
must still come from the physical column sorts. -/
theorem ordered_mask_rational_port_variance_bound
    (columns total ports : ℕ) (columnOf boundary : ℕ → ℕ)
    (actual : Fin columns → ℕ) (theta : ℚ)
    (hboundary_zero : boundary 0 = 0)
    (hboundary_end : boundary ports = total)
    (hboundary_mono : ∀ i < ports, boundary i ≤ boundary (i + 1))
    (hactual : ∀ c : Fin columns,
      actual c ≤ orderedColumnCut columnOf c.val total)
    (htheta_nonneg : 0 ≤ theta) (htheta_le_one : theta ≤ 1) :
    (∑ p : Fin ports,
      |∑ c : Fin columns,
        ((prefixIntervalMass (actual c)
            (orderedColumnCut columnOf c.val (boundary p.val))
            (orderedColumnCut columnOf c.val (boundary (p.val + 1))) : ℚ) -
          ratPrefixIntervalMass
            (theta * (orderedColumnCut columnOf c.val total : ℚ))
            (orderedColumnCut columnOf c.val (boundary p.val))
            (orderedColumnCut columnOf c.val (boundary (p.val + 1))))|) ^ 2 ≤
      (Fintype.card (Fin columns) : ℚ) *
        ∑ c : Fin columns,
          ((actual c : ℚ) -
            theta * (orderedColumnCut columnOf c.val total : ℚ)) ^ 2 := by
  let width : Fin columns → ℕ := fun c => orderedColumnCut columnOf c.val total
  let cuts : Fin columns → ℕ → ℕ := fun c i =>
    orderedColumnCut columnOf c.val (boundary i)
  have hcuts := ordered_column_cuts_partition columnOf total ports boundary
    hboundary_zero hboundary_end hboundary_mono
  have hzero : ∀ c : Fin columns, cuts c 0 = 0 := by
    intro c
    dsimp [cuts]
    rw [hboundary_zero]
    simp [orderedColumnCut]
  have hend : ∀ c : Fin columns, cuts c ports = width c := by
    intro c
    dsimp [cuts, width]
    rw [hboundary_end]
  have hmono : ∀ c i, i < ports → cuts c i ≤ cuts c (i + 1) := by
    intro c i hi
    exact (hcuts c.val).2.2 i hi
  have hactual' : ∀ c : Fin columns, actual c ≤ width c := hactual
  simpa [width, cuts] using
    ragged_nat_rational_port_variance_bound actual width cuts ports theta
      hzero hend hmono hactual' htheta_nonneg htheta_le_one

/-- Aggregate child error is bounded by the sum of local port errors plus
the parent-prefix displacement, provided the reference and ideal child
counts form a partition whose total displacement is charged only once.

This is the useful non-expansive interface for rank transfer: unlike the
per-child triangle bound, it does not multiply the parent error by the number
of children. The concrete interval-partition identity must be supplied by the
flow bridge. -/
theorem aggregate_child_count_error_le_parent_add_transfer
    {I : Type*} [Fintype I]
    (actual reference ideal transfer : I → ℕ) (parentError : ℕ)
    (hTransferUpper : ∀ i, actual i ≤ reference i + transfer i)
    (hTransferLower : ∀ i, reference i ≤ actual i + transfer i)
    (hParent : ∑ i : I, countDistance (reference i) (ideal i) ≤ parentError) :
    (∑ i : I, countDistance (actual i) (ideal i)) ≤
      parentError + ∑ i : I, transfer i := by
  have hlocal (i : I) :
      countDistance (actual i) (reference i) ≤ transfer i := by
    by_cases h : actual i ≤ reference i
    · unfold countDistance
      rw [Nat.sub_eq_zero_of_le h]
      have hi := hTransferLower i
      omega
    · have h' : reference i ≤ actual i := Nat.le_of_not_ge h
      unfold countDistance
      rw [Nat.sub_eq_zero_of_le h']
      have hi := hTransferUpper i
      omega
  calc
    (∑ i : I, countDistance (actual i) (ideal i)) ≤
        ∑ i : I,
          (countDistance (actual i) (reference i) +
            countDistance (reference i) (ideal i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact countDistance_triangle (actual i) (ideal i) (reference i)
    _ = (∑ i : I, countDistance (actual i) (reference i)) +
        (∑ i : I, countDistance (reference i) (ideal i)) :=
      Finset.sum_add_distrib
    _ ≤ parentError + ∑ i : I, transfer i := by
      have hlocalSum :
          (∑ i : I, countDistance (actual i) (reference i)) ≤
            ∑ i : I, transfer i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hlocal i
      omega

/-- After normalizing each child by twice the parent capacity, the aggregate
sibling rank error pays the parent's error only once. This is the weighted
form needed when the D2 schedule doubles the per-child capacity. -/
theorem aggregate_child_normalized_error_le_parent_add_transfer
    {I : Type*} [Fintype I]
    (actual reference ideal transfer : I → ℕ) (parentError capacity : ℕ)
    (hTransferUpper : ∀ i, actual i ≤ reference i + transfer i)
    (hTransferLower : ∀ i, reference i ≤ actual i + transfer i)
    (hParent : ∑ i : I, countDistance (reference i) (ideal i) ≤ parentError)
    (hCapacity : 0 < capacity) :
    (∑ i : I,
      (countDistance (actual i) (ideal i) : ℚ) / (2 * (capacity : ℚ))) ≤
      (parentError : ℚ) / (2 * (capacity : ℚ)) +
        (∑ i : I, (transfer i : ℚ)) / (2 * (capacity : ℚ)) := by
  have hAggregate := aggregate_child_count_error_le_parent_add_transfer
    actual reference ideal transfer parentError
    hTransferUpper hTransferLower hParent
  have hAggregateQ :
      (∑ i : I, (countDistance (actual i) (ideal i) : ℚ)) ≤
        (parentError : ℚ) + ∑ i : I, (transfer i : ℚ) := by
    exact_mod_cast hAggregate
  have hden : 0 < 2 * (capacity : ℚ) := by positivity
  calc
    (∑ i : I,
      (countDistance (actual i) (ideal i) : ℚ) / (2 * (capacity : ℚ))) =
      (∑ i : I, (countDistance (actual i) (ideal i) : ℚ)) /
        (2 * (capacity : ℚ)) := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
    _ ≤
      ((parentError : ℚ) + ∑ i : I, (transfer i : ℚ)) /
        (2 * (capacity : ℚ)) :=
      div_le_div_of_nonneg_right hAggregateQ (le_of_lt hden)
    _ = (parentError : ℚ) / (2 * (capacity : ℚ)) +
        (∑ i : I, (transfer i : ℚ)) / (2 * (capacity : ℚ)) := by
      rw [add_div]

/-- If both the parent error and total local transfer are at most one
`1/512`-capacity budget, then the sum of sibling errors, normalized by their
doubled capacities, is again at most `1/512`. -/
theorem aggregate_child_normalized_error_le_one_over_512
    {I : Type*} [Fintype I]
    (actual reference ideal transfer : I → ℕ) (parentError capacity : ℕ)
    (hTransferUpper : ∀ i, actual i ≤ reference i + transfer i)
    (hTransferLower : ∀ i, reference i ≤ actual i + transfer i)
    (hParent : ∑ i : I, countDistance (reference i) (ideal i) ≤ parentError)
    (hParentBudget : 512 * parentError ≤ capacity)
    (hTransferBudget : 512 * (∑ i : I, transfer i) ≤ capacity)
    (hCapacity : 0 < capacity) :
    (∑ i : I,
      (countDistance (actual i) (ideal i) : ℚ) / (2 * (capacity : ℚ))) ≤
        (1 : ℚ) / 512 := by
  have hAggregate := aggregate_child_count_error_le_parent_add_transfer
    actual reference ideal transfer parentError
    hTransferUpper hTransferLower hParent
  have hsum : 512 * (parentError + (∑ i : I, transfer i)) ≤ 2 * capacity := by
    omega
  have hAggregateBudget :
      512 * (∑ i : I, countDistance (actual i) (ideal i) : ℕ) ≤
        2 * capacity := by
    omega
  have hAggregateBudgetQ :
      512 * (∑ i : I, (countDistance (actual i) (ideal i) : ℚ)) ≤
        2 * (capacity : ℚ) := by
    exact_mod_cast hAggregateBudget
  have hden : 0 < 2 * (capacity : ℚ) := by positivity
  calc
    (∑ i : I,
      (countDistance (actual i) (ideal i) : ℚ) / (2 * (capacity : ℚ))) =
      (∑ i : I, (countDistance (actual i) (ideal i) : ℚ)) /
        (2 * (capacity : ℚ)) := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
    _ ≤ (1 : ℚ) / 512 := by
      apply (div_le_iff₀ hden).2
      nlinarith [hAggregateBudgetQ]

/-- The rectangular row-major Gamma=48 transfer bound leaves enough room for
the D2 sender allocation factor `279/256`: if the error/allocation ratio is
at most `21/16384` and allocation/capacity is at most `279/256`, the normalized
transfer is strictly below `1/512`. -/
theorem d2_row_major_port_transfer_budget
    (errorPerAllocation allocationPerCapacity : ℚ)
    (herror : errorPerAllocation ≤ (21 : ℚ) / 16384)
    (hallocation_nonneg : 0 ≤ allocationPerCapacity)
    (hallocation : allocationPerCapacity ≤ (279 : ℚ) / 256) :
    errorPerAllocation * allocationPerCapacity < (1 : ℚ) / 512 := by
  have hproduct := mul_le_mul herror hallocation hallocation_nonneg (by norm_num)
  have hnumeric :
      (21 : ℚ) / 16384 * ((279 : ℚ) / 256) < (1 : ℚ) / 512 := by norm_num
  exact lt_of_le_of_lt hproduct hnumeric

/-- A complete interval partition instantiates the aggregate child-error
bound: parent-prefix displacement is paid once, plus the sum of local port
transfer errors. -/
theorem aggregate_interval_count_error_le_parent_add_transfer
    (n a parentPrefix idealPrefix : ℕ) (cuts : ℕ → ℕ)
    (actual transfer : Fin n → ℕ)
    (hzero : cuts 0 = 0) (hend : cuts n = a)
    (hmono : ∀ i < n, cuts i ≤ cuts (i + 1))
    (hTransferUpper : ∀ i : Fin n,
      actual i ≤ prefixIntervalMass parentPrefix (cuts i.val) (cuts (i.val + 1)) + transfer i)
    (hTransferLower : ∀ i : Fin n,
      prefixIntervalMass parentPrefix (cuts i.val) (cuts (i.val + 1)) ≤ actual i + transfer i) :
    (∑ i : Fin n,
      countDistance (actual i)
        (prefixIntervalMass idealPrefix (cuts i.val) (cuts (i.val + 1)))) ≤
      countDistance parentPrefix idealPrefix + ∑ i : Fin n, transfer i := by
  have hParentRange := prefixIntervalMass_partition_distance
    parentPrefix idealPrefix cuts n a hzero hend hmono
  have hParent :
      (∑ i : Fin n,
        countDistance
          (prefixIntervalMass parentPrefix (cuts i.val) (cuts (i.val + 1)))
          (prefixIntervalMass idealPrefix (cuts i.val) (cuts (i.val + 1)))) ≤
        countDistance parentPrefix idealPrefix := by
    rw [Fin.sum_univ_eq_sum_range (fun i =>
      countDistance (prefixIntervalMass parentPrefix (cuts i) (cuts (i + 1)))
        (prefixIntervalMass idealPrefix (cuts i) (cuts (i + 1))))]
    exact hParentRange
  exact aggregate_child_count_error_le_parent_add_transfer
    actual
    (fun i => prefixIntervalMass parentPrefix (cuts i.val) (cuts (i.val + 1)))
    (fun i => prefixIntervalMass idealPrefix (cuts i.val) (cuts (i.val + 1)))
    transfer (countDistance parentPrefix idealPrefix)
    hTransferUpper hTransferLower hParent

/-- A concrete ragged child count inherits the parent prefix error plus its
local transfer error, provided the actual count is within `transferError` of
the reference prefix/interval overlap. -/
theorem ragged_child_count_error_le_parent_add_transfer
    (actualChild parentPrefix idealPrefix u v transferError : ℕ)
    (huv : u ≤ v)
    (hTransferUpper : actualChild ≤
      prefixIntervalMass parentPrefix u v + transferError)
    (hTransferLower : prefixIntervalMass parentPrefix u v ≤
      actualChild + transferError) :
    actualChild ≤ prefixIntervalMass idealPrefix u v +
        (transferError + (parentPrefix - idealPrefix) +
          (idealPrefix - parentPrefix)) ∧
      prefixIntervalMass idealPrefix u v ≤ actualChild +
        (transferError + (parentPrefix - idealPrefix) +
          (idealPrefix - parentPrefix)) := by
  have hreference := prefixIntervalMass_count_change
    parentPrefix idealPrefix u v huv
  constructor <;> omega

/-- Integer rank-count error under the normalized `1/512` allowance is
exactly zero once the node's integer capacity is below 512. -/
theorem exact_count_of_small_capacity
    (actual ideal error capacity : ℕ)
    (hUpper : actual ≤ ideal + error)
    (hLower : ideal ≤ actual + error)
    (hError : 512 * error ≤ capacity)
    (hSmall : capacity < 512) :
    actual = ideal := by
  have hzero : error = 0 := by omega
  omega

/-- A bijection of the cyclic row indices has exactly one preimage of the
last index. -/
theorem equiv_last_index_filter_card_eq_one
    {n : ℕ} (hn : 0 < n) (e : Fin n ≃ Fin n) :
    (Finset.univ.filter fun c : Fin n => (e c).val + 1 = n).card = 1 := by
  let last : Fin n := ⟨n - 1, by omega⟩
  let c₀ : Fin n := e.symm last
  have hlast : last.val + 1 = n := by dsimp [last]; omega
  have hc₀ : (e c₀).val + 1 = n := by
    simpa [c₀, last] using hlast
  have hfilter :
      (Finset.univ.filter fun c : Fin n => (e c).val + 1 = n) = {c₀} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hc
      have hec : e c = last := by
        apply Fin.ext
        dsimp [last]
        omega
      calc
        c = e.symm (e c) := (e.symm_apply_apply c).symm
        _ = c₀ := by simp [c₀, hec]
    · intro hc
      subst c
      exact hc₀
  rw [hfilter]
  simp

/-- Advancing every row threshold by one cyclically can increase the number
of selected prefix hits by at most one. This is the exact one-sided profile
step used after a cyclic row shuffle: all nonwrapping indicators decrease,
and the unique wrapping threshold is the only possible new hit. -/
theorem cyclic_successor_indicator_count_le
    (n : ℕ) (height previousRow : Fin n → ℕ)
    (nextRow : Fin n → ℕ)
    (hrow_lt : ∀ c, previousRow c < n)
    (hnext : ∀ c, nextRow c = (previousRow c + 1) % n)
    (hwrap : (Finset.univ.filter fun c : Fin n => previousRow c + 1 = n).card = 1) :
    (∑ c : Fin n, if nextRow c < height c then 1 else 0) ≤
      (∑ c : Fin n, if previousRow c < height c then 1 else 0) + 1 := by
  have hpoint (c : Fin n) :
      (if nextRow c < height c then 1 else 0) ≤
        (if previousRow c < height c then 1 else 0) +
          (if previousRow c + 1 = n then 1 else 0) := by
    by_cases hw : previousRow c + 1 = n
    · have hnrow : nextRow c = 0 := by
        rw [hnext c, hw]
        simp
      by_cases hpos : 0 < height c <;> simp [hw, hnrow, hpos]
    · have hprev := hrow_lt c
      have hlt : previousRow c + 1 < n := by omega
      have hnrow : nextRow c = previousRow c + 1 := by
        rw [hnext c, Nat.mod_eq_of_lt hlt]
      by_cases hhit : previousRow c < height c
      · by_cases hnextHit : previousRow c + 1 < height c <;>
          simp [hw, hhit, hnextHit, hnrow]
      · have hnextFalse : ¬ previousRow c + 1 < height c := by omega
        simp [hw, hhit, hnextFalse, hnrow]
  calc
    (∑ c : Fin n, if nextRow c < height c then 1 else 0) ≤
        ∑ c : Fin n,
          ((if previousRow c < height c then 1 else 0) +
            (if previousRow c + 1 = n then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro c hc
      exact hpoint c
    _ = (∑ c : Fin n, if previousRow c < height c then 1 else 0) +
        (∑ c : Fin n, if previousRow c + 1 = n then 1 else 0) :=
      Finset.sum_add_distrib
    _ = (∑ c : Fin n, if previousRow c < height c then 1 else 0) + 1 := by
      rw [Finset.sum_boole]
      simp [hwrap]

/-- The cyclic hit-count bound with its unique-wrap condition discharged by
an equivalence of row indices. -/
theorem cyclic_successor_indicator_count_le_equiv
    (n : ℕ) (hn : 0 < n) (height : Fin n → ℕ)
    (rowEquiv : Fin n ≃ Fin n) (nextRow : Fin n → ℕ)
    (hnext : ∀ c, nextRow c = ((rowEquiv c).val + 1) % n) :
    (∑ c : Fin n, if nextRow c < height c then 1 else 0) ≤
      (∑ c : Fin n, if (rowEquiv c).val < height c then 1 else 0) + 1 := by
  apply cyclic_successor_indicator_count_le n height
    (fun c => (rowEquiv c).val) nextRow
  · intro c
    exact (rowEquiv c).isLt
  · exact hnext
  · exact equiv_last_index_filter_card_eq_one hn rowEquiv

/-- Row threshold for source column `c` at destination `d` under the
slope-35 shuffle modulo 64. -/
def slope35RowAt (d c : Fin 64) : Fin 64 :=
  ⟨(11 * ((d.val + 64 - c.val) % 64)) % 64,
    Nat.mod_lt _ (by norm_num)⟩

/-- Destination immediately preceding `d` in a slope-35 row shift. -/
def slope35PrevDestination (d : Fin 64) : Fin 64 :=
  ⟨(d.val + 64 - 35) % 64, Nat.mod_lt _ (by norm_num)⟩

theorem slope35RowAt_injective (d : Fin 64) :
    Function.Injective (slope35RowAt d) := by
  intro a b hab
  apply Fin.ext
  have hval := congrArg Fin.val hab
  dsimp [slope35RowAt] at hval
  omega

/-- The slope-35 row-index map is an equivalence for each destination. -/
noncomputable def slope35RowEquiv (d : Fin 64) : Fin 64 ≃ Fin 64 :=
  Equiv.ofBijective (slope35RowAt d)
    (Finite.injective_iff_bijective.1 (slope35RowAt_injective d))

/-- Adjacent output columns have row thresholds related by cyclic successor. -/
theorem slope35_adjacent_row_relation_all (d c : Fin 64) :
    (slope35RowAt d c).val =
      ((slope35RowAt (slope35PrevDestination d) c).val + 1) % 64 := by
  dsimp [slope35RowAt, slope35PrevDestination]
  omega

/-- A single slope-35 cyclic shuffle has one-sided adjacent-column height
gradient at most one, for every input height profile and every destination. -/
theorem slope35_adjacent_height_difference_le_one
    (height : Fin 64 → ℕ) (d : Fin 64) :
    (∑ c : Fin 64,
      if (slope35RowAt d c).val < height c then 1 else 0) ≤
    (∑ c : Fin 64,
      if (slope35RowAt (slope35PrevDestination d) c).val < height c
        then 1 else 0) + 1 := by
  apply cyclic_successor_indicator_count_le_equiv 64 (by norm_num)
    height (slope35RowEquiv (slope35PrevDestination d))
    (fun c => (slope35RowAt d c).val)
  intro c
  exact slope35_adjacent_row_relation_all d c

/-- Number of rows below height `x` whose residue modulo 64 is `r`. -/
def residueHits64 (x r : ℕ) : ℕ :=
  ((Finset.range x).filter fun i => i % 64 = r).card

/-- The residue-hit count is its common full-cycle quotient plus one exactly
when the residue lies in the final partial cycle. -/
theorem residueHits64_eq (x r : ℕ) (hr : r < 64) :
    residueHits64 x r = x / 64 + if r < x % 64 then 1 else 0 := by
  let q := x / 64
  let s := x % 64
  let k := q + if r < s then 1 else 0
  have hx : s + 64 * q = x := by
    dsimp [s, q]
    exact Nat.mod_add_div x 64
  have hx' : x % 64 + 64 * (x / 64) = x := Nat.mod_add_div x 64
  unfold residueHits64
  calc
    ((Finset.range x).filter fun i => i % 64 = r).card =
        (Finset.range k).card := by
      apply Finset.card_bij (fun i _ => i / 64)
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        rcases hi with ⟨hiLt, hiMod⟩
        have hiDecomp : i % 64 + 64 * (i / 64) = i := Nat.mod_add_div i 64
        dsimp [q, s, k]
        by_cases hrx : r < x % 64 <;> simp [hrx] <;> omega
      · intro a ha b hb hab
        simp only [Finset.mem_filter, Finset.mem_range] at ha hb
        rcases ha with ⟨haLt, haMod⟩
        rcases hb with ⟨hbLt, hbMod⟩
        have haDecomp : a % 64 + 64 * (a / 64) = a := Nat.mod_add_div a 64
        have hbDecomp : b % 64 + 64 * (b / 64) = b := Nat.mod_add_div b 64
        omega
      · intro j hj
        simp only [Finset.mem_range] at hj
        have hiLt : 64 * j + r < x := by
          by_cases hrx : r < x % 64
          · have hj' : j < x / 64 + 1 := by simpa [q, s, k, hrx] using hj
            omega
          · have hj' : j < x / 64 := by simpa [q, s, k, hrx] using hj
            omega
        have hiMod : (64 * j + r) % 64 = r := by omega
        refine ⟨64 * j + r, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨hiLt, hiMod⟩
        · omega
    _ = k := Finset.card_range k
    _ = x / 64 + if r < x % 64 then 1 else 0 := by
      dsimp [k, q, s]

/-- A source row lands at destination `d` in the slope-35 shuffle exactly
when its row residue is the inverse-affine threshold `slope35RowAt d c`. -/
theorem slope35_row_destination_iff_residue
    (c d : Fin 64) (row : ℕ) :
    (c.val + 35 * row) % 64 = d.val ↔
      row % 64 = (slope35RowAt d c).val := by
  have hc := c.isLt
  have hd := d.isLt
  dsimp [slope35RowAt]
  omega

/-- The exact number of source-`c` rows below a height that land at `d` is the
residue-hit count for the corresponding inverse-affine row threshold. -/
theorem slope35_source_hits_eq_residue
    (height : ℕ) (c d : Fin 64) :
    ((Finset.range height).filter fun row =>
      (c.val + 35 * row) % 64 = d.val).card =
        residueHits64 height (slope35RowAt d c).val := by
  unfold residueHits64
  congr 1
  ext row
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact ⟨h.1, (slope35_row_destination_iff_residue c d row).mp h.2⟩
  · intro h
    exact ⟨h.1, (slope35_row_destination_iff_residue c d row).mpr h.2⟩

/-- Physical output-column height of the cyclic slope-35 row shuffle: each
source column contributes one output wire for each occupied row sent to `d`.
-/
def slope35PhysicalOutputHeight
    (inputHeight : Fin 64 → ℕ) (d : Fin 64) : ℕ :=
  ∑ c : Fin 64,
    ((Finset.range (inputHeight c)).filter fun row =>
      (c.val + 35 * row) % 64 = d.val).card

/-- Exact quotient/residue formula for the physical slope-35 output height. -/
theorem slope35PhysicalOutputHeight_eq
    (inputHeight : Fin 64 → ℕ) (d : Fin 64) :
    slope35PhysicalOutputHeight inputHeight d =
      ∑ c : Fin 64,
        (inputHeight c / 64 +
          if (slope35RowAt d c).val < inputHeight c % 64 then 1 else 0) := by
  unfold slope35PhysicalOutputHeight
  apply Finset.sum_congr rfl
  intro c hc
  rw [slope35_source_hits_eq_residue]
  exact residueHits64_eq (inputHeight c) (slope35RowAt d c).val
    (slope35RowAt d c).isLt

/-- For arbitrary input column heights, one physical slope-35 cyclic shuffle
has one-sided adjacent output-height difference at most one. This includes
the shared full-cycle quotient, which cancels exactly. -/
theorem slope35PhysicalOutputHeight_gradient
    (inputHeight : Fin 64 → ℕ) (d : Fin 64) :
    slope35PhysicalOutputHeight inputHeight d ≤
      slope35PhysicalOutputHeight inputHeight (slope35PrevDestination d) + 1 := by
  let Q := ∑ c : Fin 64, inputHeight c / 64
  let currentHits := fun c : Fin 64 =>
    if (slope35RowAt d c).val < inputHeight c % 64 then 1 else 0
  let previousHits := fun c : Fin 64 =>
    if (slope35RowAt (slope35PrevDestination d) c).val <
        inputHeight c % 64 then 1 else 0
  have hcurrent := slope35PhysicalOutputHeight_eq inputHeight d
  have hprevious := slope35PhysicalOutputHeight_eq inputHeight
    (slope35PrevDestination d)
  have hres := slope35_adjacent_height_difference_le_one
    (fun c => inputHeight c % 64) d
  have hsumCurrent :
      (∑ c : Fin 64,
        (inputHeight c / 64 + currentHits c)) =
        Q + (∑ c : Fin 64, currentHits c) := by
    dsimp [Q]
    exact Finset.sum_add_distrib
  have hsumPrevious :
      (∑ c : Fin 64,
        (inputHeight c / 64 + previousHits c)) =
        Q + (∑ c : Fin 64, previousHits c) := by
    dsimp [Q]
    exact Finset.sum_add_distrib
  calc
    slope35PhysicalOutputHeight inputHeight d =
        ∑ c : Fin 64, (inputHeight c / 64 + currentHits c) := by
      simpa [currentHits] using hcurrent
    _ = Q + (∑ c : Fin 64, currentHits c) := hsumCurrent
    _ ≤ Q + ((∑ c : Fin 64,
          previousHits c) + 1) :=
      Nat.add_le_add_left hres Q
    _ = (Q + (∑ c : Fin 64,
          previousHits c)) + 1 := by omega
    _ = (∑ c : Fin 64,
          (inputHeight c / 64 + previousHits c)) + 1 := by
      rw [hsumPrevious]
    _ = slope35PhysicalOutputHeight inputHeight
          (slope35PrevDestination d) + 1 := by rw [hprevious]

/-- Popoviciu's finite variance bound in the form used by the cyclic core:
if `theta` is the exact mean of `n` rational values in an interval of width
`R`, then half their squared deviation from the mean is at most `n*R^2/8`.
The factor one-half matches the D2 area convention. -/
theorem half_variance_le_range_sq_div_eight
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℚ) (theta lo hi : ℚ)
    (hmean : (∑ i : Fin n, (x i - theta)) = 0)
    (hlo : ∀ i, lo ≤ x i) (hhi : ∀ i, x i ≤ hi) :
    (1 / 2 : ℚ) * (∑ i : Fin n, (x i - theta) ^ 2) ≤
      (n : ℚ) * (hi - lo) ^ 2 / 8 := by
  let mid : ℚ := (lo + hi) / 2
  have hpoint (i : Fin n) :
      (x i - mid) ^ 2 = (x i - theta) ^ 2 +
        2 * (x i - theta) * (theta - mid) + (theta - mid) ^ 2 := by
    dsimp [mid]
    ring
  have hvariance :
      (∑ i : Fin n, (x i - mid) ^ 2) =
        (∑ i : Fin n, (x i - theta) ^ 2) +
          (n : ℚ) * (theta - mid) ^ 2 := by
    have hcross :
        (∑ i : Fin n, 2 * (x i - theta) * (theta - mid)) =
          2 * (theta - mid) * (∑ i : Fin n, (x i - theta)) := by
      calc
        (∑ i : Fin n, 2 * (x i - theta) * (theta - mid)) =
            ∑ i : Fin n, (2 * (theta - mid)) * (x i - theta) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = 2 * (theta - mid) * (∑ i : Fin n, (x i - theta)) := by
          rw [Finset.mul_sum]
    have hconst :
        (∑ _i : Fin n, (theta - mid) ^ 2) =
          (n : ℚ) * (theta - mid) ^ 2 := by simp
    calc
      (∑ i : Fin n, (x i - mid) ^ 2) =
          ∑ i : Fin n,
            ((x i - theta) ^ 2 +
              2 * (x i - theta) * (theta - mid) + (theta - mid) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hpoint i
      _ = (∑ i : Fin n, (x i - theta) ^ 2) +
          2 * (theta - mid) * (∑ i : Fin n, (x i - theta)) +
            (n : ℚ) * (theta - mid) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hcross, hconst]
      _ = (∑ i : Fin n, (x i - theta) ^ 2) +
          (n : ℚ) * (theta - mid) ^ 2 := by rw [hmean]; ring
  have hmidbound (i : Fin n) :
      (x i - mid) ^ 2 ≤ (hi - lo) ^ 2 / 4 := by
    have hleft : -(hi - lo) / 2 ≤ x i - mid := by
      dsimp [mid]
      nlinarith [hlo i]
    have hright : x i - mid ≤ (hi - lo) / 2 := by
      dsimp [mid]
      nlinarith [hhi i]
    nlinarith [sq_nonneg (x i - mid), sq_nonneg (hi - lo)]
  have hsum_bound :
      (∑ i : Fin n, (x i - mid) ^ 2) ≤
        (n : ℚ) * ((hi - lo) ^ 2 / 4) := by
    calc
      (∑ i : Fin n, (x i - mid) ^ 2) ≤
          ∑ _i : Fin n, ((hi - lo) ^ 2 / 4) := by
        apply Finset.sum_le_sum
        intro i hi'
        exact hmidbound i
      _ = (n : ℚ) * ((hi - lo) ^ 2 / 4) := by simp
  have hnonneg : 0 ≤ (n : ℚ) * (theta - mid) ^ 2 := by positivity
  rw [hvariance] at hsum_bound
  nlinarith

/-- A range-15 profile on the 64 cyclic columns has D2 area at most
`28.125` per column, provided `theta` is its exact mean. This is the numeric
consequence needed by the fixed-width candidate; it does not establish the
range premise for the sorting network. -/
theorem half_variance_64_le_225_over_eight
    (x : Fin 64 → ℚ) (theta lo hi : ℚ)
    (hmean : (∑ i : Fin 64, (x i - theta)) = 0)
    (hlo : ∀ i, lo ≤ x i) (hhi : ∀ i, x i ≤ hi)
    (hrange : hi - lo ≤ 15) :
    (1 / 2 : ℚ) * (∑ i : Fin 64, (x i - theta) ^ 2) / 64 ≤ 225 / 8 := by
  have hbase := half_variance_le_range_sq_div_eight
    (n := 64) (by norm_num) x theta lo hi hmean hlo hhi
  have hwidth_nonneg : 0 ≤ hi - lo := by
    have h0lo := hlo ⟨0, by norm_num⟩
    have h0hi := hhi ⟨0, by norm_num⟩
    linarith
  have hwidthsq : (hi - lo) ^ 2 ≤ (15 : ℚ) ^ 2 := by
    nlinarith [sq_nonneg (hi - lo)]
  have hscaled :
      (1 / 2 : ℚ) * (∑ i : Fin 64, (x i - theta) ^ 2) ≤ 1800 := by
    nlinarith [hbase, hwidthsq]
  norm_num at hscaled ⊢
  nlinarith

/-- Natural-valued 64-column version: once total mass and a range-15 bound
are supplied, the centering value is definitionally the exact mean needed by
the variance-to-area estimate. -/
theorem nat_half_variance_64_le_225_over_eight
    (x : Fin 64 → ℕ) (total lo hi : ℕ)
    (htotal : (∑ i : Fin 64, x i) = total)
    (hlo : ∀ i, lo ≤ x i) (hhi : ∀ i, x i ≤ hi)
    (hrange : hi - lo ≤ 15) :
    (1 / 2 : ℚ) *
      (∑ i : Fin 64, ((x i : ℚ) - (total : ℚ) / 64) ^ 2) / 64 ≤
        225 / 8 := by
  apply half_variance_64_le_225_over_eight
    (fun i => (x i : ℚ)) ((total : ℚ) / 64) (lo : ℚ) (hi : ℚ)
  · have htotalQ : (∑ i : Fin 64, (x i : ℚ)) = (total : ℚ) := by
      exact_mod_cast htotal
    rw [Finset.sum_sub_distrib, htotalQ]
    simp only [Finset.sum_const, Finset.card_fin]
    field_simp
    ring
  · intro i
    exact_mod_cast hlo i
  · intro i
    exact_mod_cast hhi i
  · have hle : lo ≤ hi := le_trans (hlo ⟨0, by norm_num⟩)
      (hhi ⟨0, by norm_num⟩)
    exact_mod_cast hrange

/- A sparse-bottom sender has a tight observed endpoint reserve of
`21/2048` of capacity. A one-sided port leakage of at most `1/1024` of
capacity still leaves the `1/128` endpoint gate. This is only the numerical
margin: the physical network must still identify leakage with reserve loss. -/
theorem d2_sparse_botDesc_leakage_preserves_endpoint_gate
    (reserve leakage capacity : Rat)
    (hreserve : (21 : Rat) / 2048 * capacity <= reserve)
    (hleakage : leakage <= capacity / 1024)
    (hcapacity : 0 <= capacity) :
    capacity / 128 <= reserve - leakage := by
  have hmargin : (1 : Rat) / 128 + 1 / 1024 <= (21 : Rat) / 2048 := by
    norm_num
  linarith

/-- A strict scheduled D2 deficit plus one full `1/512` normalized rank-error
budget fits the tolerant `23/4096` sender-deficit gate. This is the scalar
budget needed to absorb rank misalignment into the D2 input contract. -/
theorem d2_strict_deficit_plus_rank_error_fits_tolerant_budget
    (deficit rankError capacity : Rat)
    (hdeficit : deficit <= (15 : Rat) / 8192 * capacity)
    (hrank : rankError <= capacity / 512)
    (hcapacity : 0 <= capacity) :
    deficit + rankError <= (23 : Rat) / 4096 * capacity := by
  have hcoeff : (15 : Rat) / 8192 + 1 / 512 <= (23 : Rat) / 4096 := by
    norm_num
  nlinarith

/-- A two-tail cut can double l1 error when the child partition itself moves.
The two size profiles `(0,1,1,1)` and `(1,1,1,0)` differ by 2, while their
child deficit profiles for fronts `[0,1)` and `[2,3)` differ by 4. Thus the
fixed-partition stability theorem cannot be applied across changed child
boundaries without an additional one-sided structure argument. -/
def fourPortOffset (sizes : Fin 4 → ℕ) (i : Fin 4) : ℕ :=
  (Finset.univ.filter fun j : Fin 4 => j.val < i.val).sum sizes

def fourPortTwoTailMass (sizes : Fin 4 → ℕ) (i : Fin 4) : ℕ :=
  prefixIntervalMass 1 (fourPortOffset sizes i)
    (fourPortOffset sizes i + sizes i) +
  suffixIntervalMass 2 (fourPortOffset sizes i)
    (fourPortOffset sizes i + sizes i)

def fourPortExampleS : Fin 4 → ℕ := ![0, 1, 1, 1]
def fourPortExampleT : Fin 4 → ℕ := ![1, 1, 1, 0]

theorem moving_partition_two_front_counterexample :
    (∑ i : Fin 4, countDistance (fourPortTwoTailMass fourPortExampleS i)
      (fourPortTwoTailMass fourPortExampleT i)) = 4 ∧
    (∑ i : Fin 4, countDistance (fourPortExampleS i) (fourPortExampleT i)) = 2 := by
  decide

end Chvatal.D2RankAlignment
