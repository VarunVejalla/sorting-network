import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Interval.Finset.Fin

/-! Exact sorting inside contiguous blocks preserves a uniform rank-displacement
bound. This is the combinatorial interface behind the block-sorting reduction
in `D2-MARGIN-TAIL-TRANSFER.md`.
-/

namespace Chvatal.D2BlockSortDisplacement

/-- Under a pointwise rank-displacement envelope, an inversion `i,j` with
`v j < v i` cannot have `j` more than `2 * E` positions to the right of `i`.
For the usual ordered pair `i < j`, this bounds the inversion span. -/
theorem inversion_span_le_twice_error
    {N E : Nat} (v : Fin N → Fin N)
    (hdisp : ∀ p, (v p).val ≤ p.val + E ∧ p.val ≤ (v p).val + E)
    (i j : Fin N) (hinv : (v j).val < (v i).val) :
    j.val ≤ i.val + 2 * E := by
  obtain ⟨_, hlower⟩ := hdisp i
  obtain ⟨_, hposLower⟩ := hdisp j
  omega

/-- If every thresholded output has its wrong zeroes and ones confined to a
width-`W` band around that threshold, then each key's output position is
within `W` of its rank. For a key of rank `r` at position `p`, use threshold
`r` when it moved left and `r+1` when it moved right. -/
theorem localized_threshold_errors_give_pointwise_rank_displacement
    {N W : Nat} (out : Fin N → Fin N)
    (hwrongOne : ∀ (q : Nat) (p : Fin N),
      p.val < q → q ≤ (out p).val → q ≤ p.val + W)
    (hwrongZero : ∀ (q : Nat) (p : Fin N),
      q ≤ p.val → (out p).val < q → p.val < q + W) :
    ∀ p, (out p).val ≤ p.val + W ∧ p.val ≤ (out p).val + W := by
  intro p
  by_cases hout : p.val ≤ (out p).val
  · constructor
    · by_cases hstrict : p.val < (out p).val
      · have h := hwrongOne (out p).val p hstrict (by omega)
        omega
      · omega
    · omega
  · have hleft : (out p).val ≤ p.val := by omega
    constructor
    · omega
    · have h := hwrongZero ((out p).val + 1) p (by omega) (by omega)
      omega

def inBlock {N : Nat} (left right : Nat) (p : Fin N) : Prop :=
  left <= p.val /\ p.val < right

private theorem interval_positions_card {N left right : Nat}
    (hright : right <= N) (hle : left <= right) :
    (Finset.univ.filter fun p : Fin N => left <= p.val /\ p.val < right).card =
      right - left := by
  classical
  calc
    (Finset.univ.filter fun p : Fin N => left <= p.val /\ p.val < right).card =
        (Finset.range (right - left)).card := by
      apply Finset.card_bij (fun p _ => p.val - left)
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact Finset.mem_range.mpr (by omega)
      · intro p hp q hq heq
        apply Fin.ext
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
        omega
      · intro x hx
        have hx' := Finset.mem_range.mp hx
        let p : Fin N := ⟨x + left, by omega⟩
        refine ⟨p, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · simp [p]
          · simp [p]
            omega
        · simp [p]
    _ = right - left := Finset.card_range _

/-- If a permutation keeps each position in its rank interval and the resulting
rank sequence is increasing on that interval, sorting the interval cannot
increase an input pointwise rank-error bound. -/
theorem blockwise_sorted_preserves_displacement
    {N E left right : Nat} (hright : right <= N)
    (f h : Fin N -> Fin N) (hh : Function.Injective h)
    (hblock : forall p, inBlock left right p -> inBlock left right (h p))
    (hdisp : forall p, (f p).val <= p.val + E /\ p.val <= (f p).val + E)
    (hsorted : forall p q, inBlock left right p -> inBlock left right q ->
      p.val <= q.val -> (f (h p)).val <= (f (h q)).val) :
    forall p, inBlock left right p ->
      (f (h p)).val <= p.val + E /\ p.val <= (f (h p)).val + E := by
  classical
  intro p hp
  constructor
  · by_contra hupper
    have hpbad : p.val + E < (f (h p)).val := by omega
    let A := Finset.univ.filter fun q : Fin N => p.val <= q.val /\ q.val < right
    let B := Finset.univ.filter fun q : Fin N => p.val < q.val /\ q.val < right
    have hmap : Set.MapsTo h A B := by
      intro q hq
      have hq' : p.val <= q.val /\ q.val < right := by
        simpa [A] using hq
      have hqBlock : inBlock left right q := ⟨le_trans hp.1 hq'.1, hq'.2⟩
      have hqSorted := hsorted p q hp hqBlock hq'.1
      have hqDisp := hdisp (h q)
      have hqInBlock := hblock q hqBlock
      have htoB : p.val < (h q).val /\ (h q).val < right := by
        constructor
        · have hmono : (f (h p)).val <= (f (h q)).val := hqSorted
          omega
        · exact hqInBlock.2
      simpa [B] using htoB
    have hinj : (A : Set (Fin N)).InjOn h := hh.injOn
    have hcard := Finset.card_le_card_of_injOn h hmap hinj
    have hcardA : A.card = right - p.val := by
      dsimp [A]
      exact interval_positions_card (N := N) (left := p.val)
        (right := right) hright (Nat.le_of_lt hp.2)
    have hcardB : B.card = right - (p.val + 1) := by
      dsimp [B]
      exact interval_positions_card (N := N) (left := p.val + 1)
        (right := right) hright (Nat.succ_le_of_lt hp.2)
    rw [hcardA, hcardB] at hcard
    have hpr : p.val < right := hp.2
    omega
  · by_contra hlower
    have hpbad : (f (h p)).val + E < p.val := by omega
    let A := Finset.univ.filter fun q : Fin N => left <= q.val /\ q.val <= p.val
    let B := Finset.univ.filter fun q : Fin N => left <= q.val /\ q.val < p.val
    have hmap : Set.MapsTo h A B := by
      intro q hq
      have hq' : left <= q.val /\ q.val <= p.val := by
        simpa [A] using hq
      have hqBlock : inBlock left right q := ⟨hq'.1, lt_of_le_of_lt hq'.2 hp.2⟩
      have hqSorted := hsorted q p hqBlock hp hq'.2
      have hqDisp := hdisp (h q)
      have hqInBlock := hblock q hqBlock
      have htoB : left <= (h q).val /\ (h q).val < p.val := by
        constructor
        · exact hqInBlock.1
        · have hmono : (f (h q)).val <= (f (h p)).val := hqSorted
          omega
      simpa [B] using htoB
    have hinj : (A : Set (Fin N)).InjOn h := hh.injOn
    have hcard := Finset.card_le_card_of_injOn h hmap hinj
    have hcardA : A.card = p.val + 1 - left := by
      have hcard' := interval_positions_card (N := N)
        (left := left) (right := p.val + 1)
        (Nat.succ_le_of_lt (lt_of_lt_of_le hp.2 hright))
        (Nat.le_trans hp.1 (Nat.le_succ _))
      have hset : A = Finset.univ.filter fun q : Fin N =>
          left <= q.val /\ q.val < p.val + 1 := by
        ext q
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [hset]
      exact hcard'
    have hcardB : B.card = p.val - left := by
      dsimp [B]
      exact interval_positions_card (N := N) (left := left)
        (right := p.val) (Nat.le_trans (Nat.le_of_lt hp.2) hright) hp.1
    rw [hcardA, hcardB] at hcard
    have hpl : left <= p.val := hp.1
    omega

/-- An approximate block sorter with pointwise rank error `D` adds at most
`D` to the incoming global displacement bound. -/
theorem approximate_block_sort_adds_error
    {N E D left right : Nat} (hright : right <= N)
    (f h g : Fin N -> Fin N) (hh : Function.Injective h)
    (hblock : forall p, inBlock left right p -> inBlock left right (h p))
    (hdisp : forall p, (f p).val <= p.val + E /\ p.val <= (f p).val + E)
    (hsorted : forall p q, inBlock left right p -> inBlock left right q ->
      p.val <= q.val -> (f (h p)).val <= (f (h q)).val)
    (happrox : forall p, (g p).val <= (f (h p)).val + D /\
      (f (h p)).val <= (g p).val + D) :
    forall p, inBlock left right p ->
      (g p).val <= p.val + E + D /\ p.val <= (g p).val + E + D := by
  intro p hp
  have hsortedBound := blockwise_sorted_preserves_displacement
    hright f h hh hblock hdisp hsorted p hp
  obtain ⟨hgd, hdg⟩ := happrox p
  obtain ⟨hsu, hus⟩ := hsortedBound
  constructor <;> omega

/-- The same argument works for a noncontiguous sender set. `addr` lists its
physical wires in increasing order, `h` is a local permutation, and the local
output ranks are sorted in sender order. Thus exact local sorting preserves a
global displacement bound even when other senders' wires are interleaved. -/
theorem ordered_sender_sort_preserves_displacement
    {M N E : Nat} (addr : Fin M → Fin N) (h : Fin M → Fin M)
    (f : Fin N → Fin N) (haddr : StrictMono addr)
    (hh : Function.Injective h)
    (hdisp : ∀ p, (f p).val ≤ p.val + E ∧ p.val ≤ (f p).val + E)
    (hsorted : ∀ i j, i ≤ j →
      (f (addr (h i))).val ≤ (f (addr (h j))).val) :
    ∀ i, (f (addr (h i))).val ≤ (addr i).val + E ∧
      (addr i).val ≤ (f (addr (h i))).val + E := by
  classical
  intro i
  constructor
  · by_contra hupper
    have hbad : (addr i).val + E < (f (addr (h i))).val := by omega
    let A : Finset (Fin M) := Finset.Ici i
    let B : Finset (Fin M) := Finset.Ioi i
    have hmap : Set.MapsTo h A B := by
      intro j hj
      have hjle : i.val ≤ j.val := Fin.le_iff_val_le_val.mp (by simpa [A] using hj)
      have hsort := hsorted i j (Fin.le_iff_val_le_val.mpr hjle)
      have hdispj := hdisp (addr (h j))
      have haddrgt : (addr i).val < (addr (h j)).val := by omega
      have hjgt : i.val < (h j).val := by
        by_contra hn
        have hjle' : (h j).val ≤ i.val := Nat.le_of_not_gt hn
        have haddrle := haddr.monotone (Fin.le_iff_val_le_val.mpr hjle')
        have haddrle' := Fin.le_iff_val_le_val.mp haddrle
        omega
      change h j ∈ B
      simp only [B, Finset.mem_Ioi]
      exact Fin.lt_def.mpr hjgt
    have hcard := Finset.card_le_card_of_injOn h hmap hh.injOn
    simp only [A, B, Fin.card_Ici, Fin.card_Ioi] at hcard
    omega
  · by_contra hlower
    have hbad : (f (addr (h i))).val + E < (addr i).val := by omega
    let A : Finset (Fin M) := Finset.Iic i
    let B : Finset (Fin M) := Finset.Iio i
    have hmap : Set.MapsTo h A B := by
      intro j hj
      have hjle : j.val ≤ i.val := Fin.le_iff_val_le_val.mp (by simpa [A] using hj)
      have hsort := hsorted j i (Fin.le_iff_val_le_val.mpr hjle)
      have hdispj := hdisp (addr (h j))
      have hjlt : (h j).val < i.val := by
        by_contra hn
        have hile : i.val ≤ (h j).val := Nat.le_of_not_gt hn
        have haddrle := haddr.monotone (Fin.le_iff_val_le_val.mpr hile)
        have haddrle' := Fin.le_iff_val_le_val.mp haddrle
        omega
      change h j ∈ B
      simp only [B, Finset.mem_Iio]
      exact Fin.lt_def.mpr hjlt
    have hcard := Finset.card_le_card_of_injOn h hmap hh.injOn
    simp only [A, B, Fin.card_Iic, Fin.card_Iio] at hcard
    omega

/-- Approximate sorting of an arbitrary sender set adds only its local
pointwise rank error to the incoming global displacement envelope. -/
theorem ordered_sender_approximate_sort_adds_error
    {M N E D : Nat} (addr : Fin M → Fin N) (h : Fin M → Fin M)
    (f : Fin N → Fin N) (g : Fin M → Fin N)
    (haddr : StrictMono addr) (hh : Function.Injective h)
    (hdisp : ∀ p, (f p).val ≤ p.val + E ∧ p.val ≤ (f p).val + E)
    (hsorted : ∀ i j, i ≤ j →
      (f (addr (h i))).val ≤ (f (addr (h j))).val)
    (happrox : ∀ i, (g i).val ≤ (f (addr (h i))).val + D ∧
      (f (addr (h i))).val ≤ (g i).val + D) :
    ∀ i, (g i).val ≤ (addr i).val + E + D ∧
      (addr i).val ≤ (g i).val + E + D := by
  intro i
  have hexact := ordered_sender_sort_preserves_displacement
    addr h f haddr hh hdisp hsorted i
  obtain ⟨hgi, hig⟩ := happrox i
  obtain ⟨hei, hie⟩ := hexact
  constructor <;> omega

/-- A family of sender-local sorts combines into one global stage without
paying for the reassignment of each existing wire to its next-stage owner.
`owner` and `slot` decode each physical wire in the current sender partition;
the local output stays on that wire, while the next schedule may use a new
owner map in the next application of this theorem. -/
theorem partitioned_sender_stage_adds_error
    {N E D : Nat} {J : Type*} (size : J → Nat)
    (addr : ∀ j, Fin (size j) → Fin N)
    (owner : Fin N → J)
    (slot : ∀ p, Fin (size (owner p)))
    (decode : ∀ p, addr (owner p) (slot p) = p)
    (perm : ∀ j, Fin (size j) → Fin (size j))
    (haddr : ∀ j, StrictMono (addr j))
    (hperm : ∀ j, Function.Injective (perm j))
    (f : Fin N → Fin N)
    (hdisp : ∀ p, (f p).val ≤ p.val + E ∧ p.val ≤ (f p).val + E)
    (hsorted : ∀ j i k, i ≤ k →
      (f (addr j (perm j i))).val ≤ (f (addr j (perm j k))).val)
    (localOut : ∀ j, Fin (size j) → Fin N)
    (happrox : ∀ j i,
      (localOut j i).val ≤ (f (addr j (perm j i))).val + D ∧
      (f (addr j (perm j i))).val ≤ (localOut j i).val + D)
    (stageOut : Fin N → Fin N)
    (hstage : ∀ p, stageOut p = localOut (owner p) (slot p)) :
    ∀ p, (stageOut p).val ≤ p.val + E + D ∧
      p.val ≤ (stageOut p).val + E + D := by
  intro p
  have hlocal := ordered_sender_approximate_sort_adds_error
    (addr (owner p)) (perm (owner p)) f (localOut (owner p))
    (haddr (owner p)) (hperm (owner p)) hdisp
    (hsorted (owner p)) (happrox (owner p)) (slot p)
  simpa only [hstage p, decode p] using hlocal

/-- Convert local rank-slot error into global rank displacement. The address
map may have holes, but its increase across any local index interval is at
most `G` per slot. A local sorter moving a key by at most `C` slots then adds
at most `G*C` to the already established global displacement envelope. -/
theorem local_rank_displacement_with_address_gaps
    {M N E C G : Nat} (addr : Fin M → Fin N)
    (exactSorted actual : Fin M → Fin N) (localRank : Fin M → Fin M)
    (haddrMono : Monotone addr)
    (hgap : ∀ i j, i.val ≤ j.val →
      (addr j).val ≤ (addr i).val + G * (j.val - i.val))
    (hexact : ∀ i, (exactSorted i).val ≤ (addr i).val + E ∧
      (addr i).val ≤ (exactSorted i).val + E)
    (hlocal : ∀ i, (localRank i).val ≤ i.val + C ∧
      i.val ≤ (localRank i).val + C)
    (hactual : ∀ i, actual i = exactSorted (localRank i)) :
    ∀ i, (actual i).val ≤ (addr i).val + E + G * C ∧
      (addr i).val ≤ (actual i).val + E + G * C := by
  intro i
  have hslot := hlocal i
  have hexact' := hexact (localRank i)
  have hact : actual i = exactSorted (localRank i) := hactual i
  have haddrUpper : (addr (localRank i)).val ≤ (addr i).val + G * C := by
    by_cases hforward : i.val ≤ (localRank i).val
    · have h := hgap i (localRank i) hforward
      have hdist : (localRank i).val - i.val ≤ C := by omega
      have hmul := Nat.mul_le_mul_left G hdist
      exact h.trans (Nat.add_le_add_left hmul (addr i).val)
    · have hback : (localRank i).val ≤ i.val := Nat.le_of_not_ge hforward
      have hmono := haddrMono (Fin.le_iff_val_le_val.mpr hback)
      exact le_trans (Fin.le_iff_val_le_val.mp hmono) (by omega)
  have haddrLower : (addr i).val ≤ (addr (localRank i)).val + G * C := by
    by_cases hback : (localRank i).val ≤ i.val
    · have h := hgap (localRank i) i hback
      have hdist : i.val - (localRank i).val ≤ C := by omega
      have hmul := Nat.mul_le_mul_left G hdist
      exact h.trans (Nat.add_le_add_left hmul (addr (localRank i)).val)
    · have hforward : i.val ≤ (localRank i).val := Nat.le_of_not_ge hback
      have hmono := haddrMono (Fin.le_iff_val_le_val.mpr hforward)
      exact le_trans (Fin.le_iff_val_le_val.mp hmono) (by omega)
  rw [hact]
  constructor <;> omega

end Chvatal.D2BlockSortDisplacement
