import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Exact consequences of a per-threshold terminal bag-count bound.

This file isolates a possible terminal interface for the D2 route. It assumes
the bag has already been sorted and that its threshold counts stay within E
of the ideal rank interval. It does not construct the terminal cleanup.
-/

namespace Chvatal.D2TerminalProfile

open scoped BigOperators

def prefixCount (S : Finset Nat) (q : Nat) : Nat :=
  (S.filter fun r => r < q).card

def idealPrefixCount (L a q : Nat) : Nat := min a (q - L)

def profileClose (S : Finset Nat) (L a E : Nat) : Prop :=
  ∀ q, prefixCount S q ≤ idealPrefixCount L a q + E ∧
    idealPrefixCount L a q ≤ prefixCount S q + E

/-- On an in-interval rank, the threshold profile controls its local position
to within E. The local position is the number of bag ranks below it. -/
theorem in_interval_position_close
    (S : Finset Nat) (L a E r : Nat)
    (hprofile : profileClose S L a E)
    (hrange : L ≤ r ∧ r < L + a) :
    prefixCount S r ≤ (r - L) + E ∧
      (r - L) ≤ prefixCount S r + E := by
  have h := hprofile r
  have hideal : idealPrefixCount L a r = r - L := by
    simp [idealPrefixCount]
    omega
  simpa [hideal] using h

/-- At most E bag ranks lie below the target interval. -/
theorem below_interval_count_le
    (S : Finset Nat) (L a E : Nat)
    (hprofile : profileClose S L a E) :
    prefixCount S L ≤ E := by
  have h := (hprofile L).1
  simpa [idealPrefixCount, prefixCount] using h

/-- For a bag of the target size, at most E ranks lie at or above the target
interval's upper endpoint. -/
theorem above_interval_count_le
    (S : Finset Nat) (L a E : Nat)
    (hsize : S.card = a)
    (hprofile : profileClose S L a E) :
    a - prefixCount S (L + a) ≤ E := by
  have h := (hprofile (L + a)).2
  have hideal : idealPrefixCount L a (L + a) = a := by
    simp [idealPrefixCount]
  rw [hideal] at h
  have hcount : prefixCount S (L + a) ≤ a := by
    unfold prefixCount
    calc
      (S.filter fun r => r < L + a).card ≤ S.card := Finset.card_filter_le _ _
      _ = a := hsize
  omega

/-- A sorted terminal bag has at most `2E` keys whose ranks lie outside its
target interval; at most E can lie on either side. -/
theorem total_outside_interval_count_le
    (S : Finset Nat) (L a E : Nat)
    (hsize : S.card = a)
    (hprofile : profileClose S L a E) :
    prefixCount S L + (a - prefixCount S (L + a)) ≤ 2 * E := by
  have hlow := below_interval_count_le S L a E hprofile
  have hhigh := above_interval_count_le S L a E hsize hprofile
  omega

/-- A key occupying a position at least `E` from either end of a sorted bag
must belong to the bag's target interval. -/
theorem middle_position_in_interval
    (S : Finset Nat) (L a E r : Nat)
    (hsize : S.card = a)
    (hprofile : profileClose S L a E)
    (hr : r ∈ S)
    (hleft : E ≤ prefixCount S r)
    (hright : prefixCount S r + E < a) :
    L ≤ r ∧ r < L + a := by
  have hlow := below_interval_count_le S L a E hprofile
  have hhigh := above_interval_count_le S L a E hsize hprofile
  have hnotlow : ¬ r < L := by
    intro hrl
    have hstrict : prefixCount S r < prefixCount S L := by
      unfold prefixCount
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hxS, hxr⟩
        exact Finset.mem_filter.mpr ⟨hxS, lt_trans hxr hrl⟩
      · intro hEq
        have hrL : r ∈ S.filter (fun x => x < L) :=
          Finset.mem_filter.mpr ⟨hr, hrl⟩
        have hrR : r ∈ S.filter (fun x => x < r) := by
          rw [← hEq] at hrL
          exact hrL
        exact (Nat.lt_irrefl r) (Finset.mem_filter.mp hrR).2
    omega
  have hnotHigh : ¬ L + a ≤ r := by
    intro hend
    have hmono : prefixCount S (L + a) ≤ prefixCount S r := by
      unfold prefixCount
      apply Finset.card_le_card
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxS, hxe⟩
      exact Finset.mem_filter.mpr ⟨hxS, lt_of_lt_of_le hxe hend⟩
    omega
  exact ⟨le_of_not_gt hnotlow, lt_of_not_ge hnotHigh⟩

/-- In a sorted bag, an in-interval key at an interior local position is
within `E` ranks of the corresponding position in its target interval. -/
theorem middle_position_rank_close
    (S : Finset Nat) (L a E r : Nat)
    (hsize : S.card = a)
    (hprofile : profileClose S L a E)
    (hr : r ∈ S)
    (hleft : E ≤ prefixCount S r)
    (hright : prefixCount S r + E < a) :
    prefixCount S r ≤ (r - L) + E ∧
      (r - L) ≤ prefixCount S r + E := by
  have hrange := middle_position_in_interval S L a E r
    hsize hprofile hr hleft hright
  exact in_interval_position_close S L a E r hprofile hrange

/-- Corresponding middle positions in adjacent sorted bags are already in
strict rank order when the target interval width exceeds twice the profile
error. Thus only the first and last `E` positions per bag can disrupt a
vertical lane through the block sequence. -/
theorem adjacent_middle_positions_strict
    (S T : Finset Nat) (L a E q r s : Nat)
    (hSsize : S.card = a) (hTsize : T.card = a)
    (hSprofile : profileClose S L a E)
    (hTprofile : profileClose T (L + a) a E)
    (hr : r ∈ S) (hs : s ∈ T)
    (hposR : prefixCount S r = q)
    (hposS : prefixCount T s = q)
    (hleft : E ≤ q) (hright : q + E < a)
    (hwidth : 2 * E < a) : r < s := by
  have hR := middle_position_rank_close S L a E r
    hSsize hSprofile hr (by simpa [hposR] using hleft)
    (by simpa [hposR] using hright)
  have hS := middle_position_rank_close T (L + a) a E s
    hTsize hTprofile hs (by simpa [hposS] using hleft)
    (by simpa [hposS] using hright)
  have hRrange := middle_position_in_interval S L a E r
    hSsize hSprofile hr (by simpa [hposR] using hleft)
    (by simpa [hposR] using hright)
  have hSrange := middle_position_in_interval T (L + a) a E s
    hTsize hTprofile hs (by simpa [hposS] using hleft)
    (by simpa [hposS] using hright)
  have hRupper : r ≤ L + q + E := by omega
  have hSoffset : q ≤ (s - (L + a)) + E := by simpa [hposS] using hS.1
  have hSdecomp : L + a + (s - (L + a)) = s := Nat.add_sub_of_le hSrange.1
  have hSlower : L + a + q - E ≤ s := by omega
  omega

/-- Any two retained core keys in adjacent bags are in global rank order.
Unlike `adjacent_middle_positions_strict`, the local positions need not agree:
the `E`-wide rank margins alone separate the retained cores. -/
theorem adjacent_core_positions_strict
    (S T : Finset Nat) (L a E r s : Nat)
    (hSsize : S.card = a) (hTsize : T.card = a)
    (hSprofile : profileClose S L a E)
    (hTprofile : profileClose T (L + a) a E)
    (hr : r ∈ S) (hs : s ∈ T)
    (hrcore : E ≤ prefixCount S r ∧ prefixCount S r + E < a)
    (hscore : E ≤ prefixCount T s ∧ prefixCount T s + E < a) :
    r < s := by
  have hR := middle_position_rank_close S L a E r
    hSsize hSprofile hr hrcore.1 hrcore.2
  have hS := middle_position_rank_close T (L + a) a E s
    hTsize hTprofile hs hscore.1 hscore.2
  have hRrange := middle_position_in_interval S L a E r
    hSsize hSprofile hr hrcore.1 hrcore.2
  have hSrange := middle_position_in_interval T (L + a) a E s
    hTsize hTprofile hs hscore.1 hscore.2
  have hrupper : r ≤ L + prefixCount S r + E := by
    have := hR.2
    omega
  have hslower : L + a ≤ s := by
    have := hS.1
    have hsdecomp : L + a + (s - (L + a)) = s := Nat.add_sub_of_le hSrange.1
    omega
  have hrcap : L + prefixCount S r + E < L + a := by omega
  omega

end Chvatal.D2TerminalProfile
