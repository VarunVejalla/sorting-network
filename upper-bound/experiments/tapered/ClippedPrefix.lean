import RaggedWireOwnership

namespace Tapered945

open Chvatal

/-! Exact finite counting for UB-24. Counts concern physical output positions,
not an assumed uniform distribution of native keys. A single deficit is used
at each endpoint, so adjacent ports cancel before any error estimate. -/

def wirePrefixCount {n : Nat} (s : Finset (Fin n))
    (good : Fin n → Prop) [DecidablePred good] (p : Nat) : Nat :=
  ((blockOf s 0 p).filter good).card

def wireBlockCount {n : Nat} (s : Finset (Fin n))
    (good : Fin n → Prop) [DecidablePred good] (p q : Nat) : Nat :=
  ((blockOf s p q).filter good).card

def wirePrefixDeficit {n : Nat} (s : Finset (Fin n))
    (good : Fin n → Prop) [DecidablePred good] (p : Nat) : Nat :=
  min (s.filter good).card p - wirePrefixCount s good p

theorem wirePrefixCount_le {n : Nat} (s : Finset (Fin n))
    (good : Fin n → Prop) [DecidablePred good] (p : Nat) (hp : p ≤ s.card) :
    wirePrefixCount s good p ≤ min (s.filter good).card p := by
  apply le_min
  · exact Finset.card_le_card (Finset.filter_subset_filter good blockOf_subset)
  · unfold wirePrefixCount
    exact (Finset.card_filter_le _ _).trans (by rw [blockOf_card hp]; omega)

theorem wirePrefixCount_add_deficit {n : Nat} (s : Finset (Fin n))
    (good : Fin n → Prop) [DecidablePred good] (p : Nat) (hp : p ≤ s.card) :
    wirePrefixCount s good p + wirePrefixDeficit s good p =
      min (s.filter good).card p := by
  have h := wirePrefixCount_le s good p hp
  unfold wirePrefixDeficit
  omega

theorem wireBlockCount_add_prefix {n : Nat} (s : Finset (Fin n))
    (good : Fin n → Prop) [DecidablePred good] (p q : Nat) (hpq : p ≤ q) :
    wireBlockCount s good p q + wirePrefixCount s good p =
      wirePrefixCount s good q := by
  have heq : (blockOf s 0 q).filter good =
      (blockOf s p q).filter good ∪ (blockOf s 0 p).filter good := by
    ext w
    by_cases hg : good w <;> by_cases hs : w ∈ s <;>
      simp [Finset.mem_filter, mem_blockOf, hg, hs] <;> omega
  have hd : Disjoint ((blockOf s p q).filter good) ((blockOf s 0 p).filter good) :=
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
        (disjoint_blockOf (le_refl p)).symm)
  simpa only [wireBlockCount, wirePrefixCount, heq] using
    (Finset.card_union_of_disjoint hd).symm

/-- The signed port formula retains the two shared endpoint deficits. -/
theorem wireBlockCount_eq_clipped {n : Nat} (s : Finset (Fin n))
    (good : Fin n → Prop) [DecidablePred good] (p q : Nat)
    (hpq : p ≤ q) (hq : q ≤ s.card) :
    (wireBlockCount s good p q : Int) =
      Int.ofNat (min (s.filter good).card q) - Int.ofNat (min (s.filter good).card p) +
        (wirePrefixDeficit s good p : Int) - (wirePrefixDeficit s good q : Int) := by
  have hblock := wireBlockCount_add_prefix s good p q hpq
  have hlo := wirePrefixCount_add_deficit s good p (hpq.trans hq)
  have hhi := wirePrefixCount_add_deficit s good q hq
  simp only [Int.ofNat_eq_natCast]
  omega

/-- Adjacent ports have exactly one shared endpoint. There is no charge for
the internal cut, even if its own crossing error is large. -/
theorem wireBlockCount_append {n : Nat} (s : Finset (Fin n))
    (good : Fin n → Prop) [DecidablePred good] (p q r : Nat)
    (hpq : p ≤ q) (hqr : q ≤ r) :
    wireBlockCount s good p q + wireBlockCount s good q r =
      wireBlockCount s good p r := by
  have h₁ := wireBlockCount_add_prefix s good p q hpq
  have h₂ := wireBlockCount_add_prefix s good q r hqr
  have h₃ := wireBlockCount_add_prefix s good p r (hpq.trans hqr)
  omega

@[simp] theorem wirePrefixDeficit_zero {n : Nat} (s : Finset (Fin n))
    (good : Fin n → Prop) [DecidablePred good] : wirePrefixDeficit s good 0 = 0 := by
  simp [wirePrefixDeficit]

@[simp] theorem wirePrefixCount_full {n : Nat} (s : Finset (Fin n))
    (good : Fin n → Prop) [DecidablePred good] :
    wirePrefixCount s good s.card = (s.filter good).card := by
  have heq : blockOf s 0 s.card = s := by
    ext w
    simp only [mem_blockOf]
    exact ⟨fun h => h.1, fun h => ⟨h, Nat.zero_le _, rankIn_lt_card h⟩⟩
  simp [wirePrefixCount, heq]

@[simp] theorem wirePrefixDeficit_full {n : Nat} (s : Finset (Fin n))
    (good : Fin n → Prop) [DecidablePred good] :
    wirePrefixDeficit s good s.card = 0 := by
  have h := Finset.card_filter_le s good
  simp [wirePrefixDeficit, Nat.min_eq_left h]

/-- Both disconnected up fringes keep their own cut errors. The full-bag
endpoint has deficit zero, leaving the signed difference of the two inner
endpoints rather than an independent error for every key. -/
theorem wireUpCount_eq_clipped {n : Nat} {s : Finset (Fin n)}
    (split : RaggedWireSplit s) (good : Fin n → Prop) [DecidablePred good] :
    (((upSet s split.up).filter good).card : Int) =
      Int.ofNat (min (s.filter good).card (split.up / 2)) + Int.ofNat (s.filter good).card -
        Int.ofNat (min (s.filter good).card (s.card - split.up / 2)) -
        (wirePrefixDeficit s good (split.up / 2) : Int) +
        (wirePrefixDeficit s good (s.card - split.up / 2) : Int) := by
  have ht := split.conservation
  have he := split.up_even
  have hu : split.up / 2 ≤ s.card - split.up / 2 := by omega
  have hcard : ((upSet s split.up).filter good).card =
      wireBlockCount s good 0 (split.up / 2) +
        wireBlockCount s good (s.card - split.up / 2) s.card := by
    unfold upSet wireBlockCount
    rw [Finset.filter_union, Finset.card_union_of_disjoint]
    exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (disjoint_blockOf hu))
  have hl := wireBlockCount_eq_clipped s good 0 (split.up / 2) (Nat.zero_le _) (by omega)
  have hr := wireBlockCount_eq_clipped s good (s.card - split.up / 2) s.card
    (Nat.sub_le _ _) (le_refl _)
  have hb := Finset.card_filter_le s good
  simp only [Int.ofNat_eq_natCast] at hl hr ⊢
  simp only [wirePrefixDeficit_zero, wirePrefixDeficit_full, Nat.min_zero,
    Nat.min_eq_left hb, Nat.cast_zero] at hl hr
  omega

/-- Exact sorted output is the zero-deficit case. This is an explicit local
rank premise, not a claim that sorting a bag imports its missing native keys. -/
theorem wirePrefixCount_of_ordered {n : Nat} (s : Finset (Fin n))
    (good : Fin n → Prop) [DecidablePred good] (p : Nat) (hp : p ≤ s.card)
    (hordered : ∀ w ∈ s, good w ↔ rankIn s w < (s.filter good).card) :
    wirePrefixCount s good p = min (s.filter good).card p := by
  have heq : (blockOf s 0 p).filter good =
      blockOf s 0 (min (s.filter good).card p) := by
    ext w
    simp only [Finset.mem_filter, mem_blockOf, lt_min_iff]
    constructor
    · rintro ⟨⟨hw, hzero, hwp⟩, hg⟩
      exact ⟨hw, hzero, (hordered w hw).mp hg, hwp⟩
    · rintro ⟨hw, hzero, hwH, hwp⟩
      exact ⟨⟨hw, hzero, hwp⟩, (hordered w hw).mpr hwH⟩
  unfold wirePrefixCount
  rw [heq, blockOf_card ((min_le_right _ _).trans hp)]
  omega

/-- A deficit for any threshold is bounded by the appropriate rank crossing
at the *port cut*. This uses the low crossing when the threshold population
is smaller than the prefix capacity. -/
theorem wirePrefixDeficit_le_low_crossing {n : Nat} (s : Finset (Fin n))
    (good : Fin n → Prop) [DecidablePred good] (rank : Fin n → Nat)
    (p : Nat) (hp : p ≤ s.card) (hH : (s.filter good).card ≤ p)
    (hrank : ∀ w ∈ s, good w ↔ rank w < (s.filter good).card) :
    wirePrefixDeficit s good p ≤
      (s.filter fun w => rank w < p ∧ p ≤ rankIn s w).card := by
  have ht := wireBlockCount_add_prefix s good p s.card hp
  have hfull := wirePrefixCount_full s good
  have hdef := wirePrefixCount_add_deficit s good p hp
  rw [Nat.min_eq_left hH] at hdef
  have heq : wirePrefixDeficit s good p = wireBlockCount s good p s.card := by omega
  rw [heq]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨hblock, hg⟩ := Finset.mem_filter.mp hw
  obtain ⟨hw, hlo, hhi⟩ := mem_blockOf.mp hblock
  exact Finset.mem_filter.mpr ⟨hw, (hrank w hw).mp hg |>.trans_le hH, hlo⟩

/-- Dual crossing bound when the prefix capacity is smaller than the
threshold population. No independence between endpoint errors is assumed. -/
theorem wirePrefixDeficit_le_high_crossing {n : Nat} (s : Finset (Fin n))
    (good : Fin n → Prop) [DecidablePred good] (rank : Fin n → Nat)
    (p : Nat) (hp : p ≤ s.card) (hH : p ≤ (s.filter good).card)
    (hrank : ∀ w ∈ s, good w ↔ rank w < (s.filter good).card) :
    wirePrefixDeficit s good p ≤
      (s.filter fun w => p ≤ rank w ∧ rankIn s w < p).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := blockOf s 0 p) good
  have hcells := blockOf_card (s := s) (lo := 0) hp
  have hdef := wirePrefixCount_add_deficit s good p hp
  rw [Nat.min_eq_right hH] at hdef
  have heq : wirePrefixDeficit s good p =
      ((blockOf s 0 p).filter fun w => ¬good w).card := by
    change wirePrefixCount s good p + _ = _ at hsplit
    omega
  rw [heq]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨hblock, hg⟩ := Finset.mem_filter.mp hw
  obtain ⟨hw, hlo, hhi⟩ := mem_blockOf.mp hblock
  have hr : ¬ rank w < (s.filter good).card := fun h => hg ((hrank w hw).mpr h)
  exact Finset.mem_filter.mpr ⟨hw, by omega, hhi⟩

/-- An actual two-sided separator bound controls the same deficit for every
global threshold. The error is `E`, not the sum of both crossing bounds. -/
theorem wirePrefixDeficit_le_of_crossings {n : Nat} (s : Finset (Fin n))
    (good : Fin n → Prop) [DecidablePred good] (rank : Fin n → Nat)
    (p : Nat) (hp : p ≤ s.card) (E : Rat)
    (hrank : ∀ w ∈ s, good w ↔ rank w < (s.filter good).card)
    (hlo : ((s.filter fun w => rank w < p ∧ p ≤ rankIn s w).card : Rat) ≤ E)
    (hhi : ((s.filter fun w => p ≤ rank w ∧ rankIn s w < p).card : Rat) ≤ E) :
    (wirePrefixDeficit s good p : Rat) ≤ E := by
  by_cases hH : (s.filter good).card ≤ p
  · exact le_trans (by exact_mod_cast
      wirePrefixDeficit_le_low_crossing s good rank p hp hH hrank) hlo
  · exact le_trans (by exact_mod_cast
      wirePrefixDeficit_le_high_crossing s good rank p hp (by omega) hrank) hhi

/-- Native interval counts are differences of two threshold counts. Keeping
the four signed endpoint deficits avoids replacing deterministic frontier
mass by an outsider error. -/
theorem wireBlock_interval_eq_clipped {n : Nat} (s : Finset (Fin n))
    (keys : Fin n → Nat) (lo hi p q : Nat) (hlohi : lo ≤ hi)
    (hpq : p ≤ q) (hq : q ≤ s.card) :
    (((blockOf s p q).filter fun w => lo ≤ keys w ∧ keys w < hi).card : Int) =
      ((min (s.filter fun w => keys w < hi).card q : Int) -
        (min (s.filter fun w => keys w < hi).card p : Int)) -
      ((min (s.filter fun w => keys w < lo).card q : Int) -
        (min (s.filter fun w => keys w < lo).card p : Int)) +
      (wirePrefixDeficit s (fun w => keys w < hi) p : Int) -
      (wirePrefixDeficit s (fun w => keys w < hi) q : Int) -
      (wirePrefixDeficit s (fun w => keys w < lo) p : Int) +
      (wirePrefixDeficit s (fun w => keys w < lo) q : Int) := by
  have hs := Finset.card_filter_add_card_filter_not
    (s := (blockOf s p q).filter fun w => keys w < hi) (fun w => keys w < lo)
  have hlo : ((blockOf s p q).filter fun w => keys w < hi).filter
      (fun w => keys w < lo) = (blockOf s p q).filter (fun w => keys w < lo) := by
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hw, _⟩, hlo⟩
      exact ⟨hw, hlo⟩
    · rintro ⟨hw, hlo⟩
      exact ⟨⟨hw, hlo.trans_le hlohi⟩, hlo⟩
  have hmid : ((blockOf s p q).filter fun w => keys w < hi).filter
      (fun w => ¬keys w < lo) =
        (blockOf s p q).filter (fun w => lo ≤ keys w ∧ keys w < hi) := by
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hw, hhi⟩, hlo⟩
      exact ⟨hw, by omega, hhi⟩
    · rintro ⟨hw, hlo, hhi⟩
      exact ⟨⟨hw, hhi⟩, by omega⟩
  rw [hlo, hmid] at hs
  have h₁ := wireBlockCount_eq_clipped s (fun w => keys w < hi) p q hpq hq
  have h₂ := wireBlockCount_eq_clipped s (fun w => keys w < lo) p q hpq hq
  unfold wireBlockCount at h₁ h₂
  simp only [Int.ofNat_eq_natCast] at h₁ h₂
  omega

/-- Actual key rank in a physical source register. -/
def wireKeyRank {n : Nat} (s : Finset (Fin n)) (keys : Fin n → Nat) (w : Fin n) : Nat :=
  (s.filter fun z => keys z < keys w).card

/-- A global threshold is an initial segment of the source's local key
ranks. Its segment length is the actual threshold population in that source,
not the size of any presumed native interval. -/
theorem wireKeyRank_threshold_iff {n : Nat} (s : Finset (Fin n))
    (keys : Fin n → Nat) (cut : Nat) (w : Fin n) (hw : w ∈ s) :
    keys w < cut ↔ wireKeyRank s keys w < (s.filter fun z => keys z < cut).card := by
  constructor
  · intro hcut
    apply Finset.card_lt_card
    apply (Finset.ssubset_iff_of_subset (show
      (s.filter fun z => keys z < keys w) ⊆ s.filter (fun z => keys z < cut) from by
        intro z hz
        obtain ⟨hz, hzw⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hz, hzw.trans hcut⟩)).mpr
    exact ⟨w, Finset.mem_filter.mpr ⟨hw, hcut⟩, by simp⟩
  · intro hr
    by_contra hcut
    have hsub : (s.filter fun z => keys z < cut) ⊆
        s.filter (fun z => keys z < keys w) := by
      intro z hz
      obtain ⟨hz, hzc⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hz, by omega⟩
    have hle := Finset.card_le_card hsub
    change wireKeyRank s keys w < _ at hr
    unfold wireKeyRank at hr
    omega

theorem wireThresholdDeficit_le_of_crossings {n : Nat} (s : Finset (Fin n))
    (keys : Fin n → Nat) (cut p : Nat) (hp : p ≤ s.card) (E : Rat)
    (hlo : ((s.filter fun w => wireKeyRank s keys w < p ∧ p ≤ rankIn s w).card : Rat) ≤ E)
    (hhi : ((s.filter fun w => p ≤ wireKeyRank s keys w ∧ rankIn s w < p).card : Rat) ≤ E) :
    (wirePrefixDeficit s (fun w => keys w < cut) p : Rat) ≤ E := by
  exact wirePrefixDeficit_le_of_crossings s (fun w => keys w < cut)
    (wireKeyRank s keys) p hp E (fun w hw => wireKeyRank_threshold_iff s keys cut w hw) hlo hhi

/-- Full-sort interval counts are monotone and 1-Lipschitz in the input
threshold population. This alone does not control a sum of many sources. -/
theorem clipped_interval_monotone_lipschitz (H K p q : Nat) (hHK : H ≤ K) (hpq : p ≤ q) :
    0 ≤ (min K q : Int) - (min K p : Int) - ((min H q : Int) - (min H p : Int)) ∧
    (min K q : Int) - (min K p : Int) - ((min H q : Int) - (min H p : Int)) ≤
      (K : Int) - H := by
  omega

/-- Re-sorting a pool of ordered native cohorts returns each cohort to its
own port when the port width equals the cohort's exact cardinality. `before`
and `after` retain the concentrated fringe mass from the other sources. -/
theorem clipped_pooled_cohort_recovery (before here after offset width : Nat)
    (hbefore : before ≤ offset) (hhere : here ≤ width)
    (hleft : 0 < here → before = offset)
    (hright : here < width → after = 0) :
    min (before + here + after) (offset + width) -
      min (before + here + after) offset = here := by
  by_cases hzero : here = 0
  · by_cases hwidth : width = 0 <;> simp_all <;> omega
  · have h := hleft (by omega)
    by_cases hfull : here = width <;> simp_all <;> omega

end Tapered945
