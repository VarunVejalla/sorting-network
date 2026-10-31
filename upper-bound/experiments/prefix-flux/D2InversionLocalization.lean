import D2RankAlignment

namespace Chvatal.D2InversionLocalization

def inversionPairs {N : Nat} (v : Fin N -> Bool) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun ij => ij.1.val < ij.2.val ∧
    v ij.1 = true ∧ v ij.2 = false

def zeroPositions {N : Nat} (v : Fin N -> Bool) : Finset (Fin N) :=
  Finset.univ.filter fun i => v i = false

def zerosBefore {N : Nat} (v : Fin N -> Bool) (p : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun i => i.val < p.val ∧ v i = false

def zerosAfter {N : Nat} (v : Fin N -> Bool) (p : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun i => p.val < i.val ∧ v i = false

def onesBefore {N : Nat} (v : Fin N -> Bool) (p : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun i => i.val < p.val ∧ v i = true

def inversionCount {N : Nat} (v : Fin N -> Bool) : Nat :=
  (inversionPairs v).card

/-- Ones before a proposed cut and zeros at or after it. -/
def cutWrongOnes {N : Nat} (v : Fin N -> Bool) (q : Nat) : Finset (Fin N) :=
  Finset.univ.filter fun i => i.val < q ∧ v i = true

def cutWrongZeros {N : Nat} (v : Fin N -> Bool) (q : Nat) : Finset (Fin N) :=
  Finset.univ.filter fun i => q <= i.val ∧ v i = false

def cutZerosBefore {N : Nat} (v : Fin N -> Bool) (q : Nat) : Finset (Fin N) :=
  Finset.univ.filter fun i => i.val < q ∧ v i = false

/-- The order-s distance moment of the misplaced wires around cut q. -/
def cutDistanceMoment {N : Nat} (v : Fin N -> Bool) (q s : Nat) : Nat :=
  ((cutWrongOnes v q).sum fun i => (q - i.val) ^ s) +
    ((cutWrongZeros v q).sum fun i => (i.val - q) ^ s)

/-- Every pair consisting of a one before the cut and a zero at or after it
is a distinct inversion. This is the quadratic support bound used to price
terminal repair. -/
theorem cut_wrong_pair_count_le_inversions {N : Nat} (v : Fin N -> Bool)
    (q : Nat) :
    (cutWrongOnes v q).card * (cutWrongZeros v q).card <= inversionCount v := by
  classical
  have hsubset :
      (cutWrongOnes v q ×ˢ cutWrongZeros v q) ⊆ inversionPairs v := by
    intro ij hij
    rcases Finset.mem_product.mp hij with ⟨hi, hj⟩
    simp only [cutWrongOnes, cutWrongZeros, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi hj
    simp only [inversionPairs, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨by omega, hi.2, hj.2⟩
  calc
    (cutWrongOnes v q).card * (cutWrongZeros v q).card =
        (cutWrongOnes v q ×ˢ cutWrongZeros v q).card := by
      rw [Finset.card_product]
    _ <= (inversionPairs v).card := Finset.card_le_card hsubset
    _ = inversionCount v := rfl

def zeroCount {N : Nat} (v : Fin N -> Bool) : Nat :=
  (zeroPositions v).card

private theorem card_prefix_nat {N q : Nat} (hq : q <= N) :
    (Finset.univ.filter fun i : Fin N => i.val < q).card = q := by
  classical
  calc
    (Finset.univ.filter fun i : Fin N => i.val < q).card =
        (Finset.range q).card := by
      apply Finset.card_bij (fun i _ => i.val)
      · intro i hi
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
      · intro a ha b hb hab
        exact Fin.ext hab
      · intro a ha
        have ha' := Finset.mem_range.mp ha
        exact ⟨⟨a, lt_of_lt_of_le ha' hq⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha'⟩, rfl⟩
    _ = q := Finset.card_range _

/-- At the true zero-count cut, the number of ones on the left equals the
number of zeros on the right. -/
theorem wrong_populations_equal {N : Nat} (v : Fin N -> Bool) :
    (cutWrongOnes v (zeroCount v)).card =
      (cutWrongZeros v (zeroCount v)).card := by
  classical
  let q := zeroCount v
  have hqN : q <= N := by
    dsimp [q, zeroCount]
    calc
      _ <= Finset.univ.card := Finset.card_le_univ _
      _ = N := Finset.card_fin _
  let pref := Finset.univ.filter (fun i : Fin N => i.val < q)
  have hprefix : pref.card = q := by
    exact card_prefix_nat hqN
  have hprefixSplit := Finset.card_filter_add_card_filter_not
    (s := pref) (p := fun i : Fin N => v i = true)
  have hprefixOnes : pref.filter (fun i : Fin N => v i = true) =
      cutWrongOnes v q := by
    ext i
    simp [pref, cutWrongOnes]
  have hprefixZeros : pref.filter (fun i : Fin N => ¬ v i = true) =
      cutZerosBefore v q := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      pref, cutZerosBefore]
    constructor
    · rintro ⟨hi, hv⟩
      exact ⟨hi, by cases h : v i <;> simp_all⟩
    · rintro ⟨hi, hv⟩
      exact ⟨hi, by simp [hv]⟩
  have hzerosSplit := Finset.card_filter_add_card_filter_not
    (s := zeroPositions v) (p := fun i : Fin N => i.val < q)
  have hzeroBefore : (zeroPositions v).filter (fun i : Fin N => i.val < q) =
      cutZerosBefore v q := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      zeroPositions, cutZerosBefore]
    exact and_comm
  have hzeroAfter : (zeroPositions v).filter (fun i : Fin N => ¬ i.val < q) =
      cutWrongZeros v q := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      zeroPositions, cutWrongZeros]
    constructor
    · rintro ⟨hv, hnlt⟩
      exact ⟨by omega, hv⟩
    · rintro ⟨hle, hv⟩
      exact ⟨hv, by omega⟩
  rw [hprefixOnes, hprefixZeros, hprefix] at hprefixSplit
  rw [hzeroBefore, hzeroAfter] at hzerosSplit
  have hqDef : q = (zeroPositions v).card := rfl
  rw [← hqDef] at hzerosSplit
  have h1 : (cutWrongOnes v (zeroCount v)).card +
      (cutZerosBefore v (zeroCount v)).card = zeroCount v := by
    simpa [q] using hprefixSplit
  have h2 : (cutZerosBefore v (zeroCount v)).card +
      (cutWrongZeros v (zeroCount v)).card = zeroCount v := by
    simpa [q, zeroCount, zeroPositions] using hzerosSplit
  omega

/-- The number of misplaced ones at the exact zero-count cut has square at
most the total inversion count. -/
theorem wrong_population_square_le_inversions {N : Nat} (v : Fin N -> Bool) :
    (cutWrongOnes v (zeroCount v)).card ^ 2 <= inversionCount v := by
  have h := cut_wrong_pair_count_le_inversions v (zeroCount v)
  rw [← wrong_populations_equal v] at h
  simpa [pow_two] using h

/-- Every misplaced one contributes its distance power to the global moment. -/
theorem misplaced_one_power_le_cutDistanceMoment {N : Nat} (v : Fin N -> Bool)
    (s : Nat) (p : Fin N) (hp : v p = true) (hpq : p.val < zeroCount v) :
    (zeroCount v - p.val) ^ s <= cutDistanceMoment v (zeroCount v) s := by
  classical
  let q := zeroCount v
  have hmem : p ∈ cutWrongOnes v q := by
    simp [cutWrongOnes, q, hp, hpq]
  have hnonneg : ∀ i ∈ cutWrongOnes v q, 0 <= (q - i.val) ^ s := by
    intro i hi
    exact Nat.zero_le _
  have hsum := Finset.single_le_sum hnonneg hmem
  have hleft : (q - p.val) ^ s <=
      (cutWrongOnes v q).sum fun i => (q - i.val) ^ s := by
    exact hsum
  have hleft' : (zeroCount v - p.val) ^ s <=
      (cutWrongOnes v (zeroCount v)).sum fun i =>
        (zeroCount v - i.val) ^ s := by
    simpa [q] using hleft
  dsimp [cutDistanceMoment]
  have hright : 0 <= (cutWrongZeros v q).sum fun i => (i.val - q) ^ s :=
    Nat.zero_le _
  omega

/-- Every misplaced zero contributes its distance power to the global moment. -/
theorem misplaced_zero_power_le_cutDistanceMoment {N : Nat} (v : Fin N -> Bool)
    (s : Nat) (p : Fin N) (hp : v p = false) (hpq : zeroCount v <= p.val) :
    (p.val - zeroCount v) ^ s <= cutDistanceMoment v (zeroCount v) s := by
  classical
  let q := zeroCount v
  have hmem : p ∈ cutWrongZeros v q := by
    simp [cutWrongZeros, q, hp, hpq]
  have hnonneg : ∀ i ∈ cutWrongZeros v q, 0 <= (i.val - q) ^ s := by
    intro i hi
    exact Nat.zero_le _
  have hsum := Finset.single_le_sum hnonneg hmem
  have hright : (p.val - q) ^ s <=
      (cutWrongZeros v q).sum fun i => (i.val - q) ^ s := by
    exact hsum
  have hright' : (p.val - zeroCount v) ^ s <=
      (cutWrongZeros v (zeroCount v)).sum fun i =>
        (i.val - zeroCount v) ^ s := by
    simpa [q] using hright
  dsimp [cutDistanceMoment]
  have hleft : 0 <= (cutWrongOnes v q).sum fun i => (q - i.val) ^ s :=
    Nat.zero_le _
  omega

private theorem card_positions_before {N : Nat} (p : Fin N) :
    (Finset.univ.filter fun i : Fin N => i.val < p.val).card = p.val := by
  classical
  calc
    (Finset.univ.filter fun i : Fin N => i.val < p.val).card =
        (Finset.range p.val).card := by
      apply Finset.card_bij (fun i _ => i.val)
      · intro i hi
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
      · intro a ha b hb hab
        exact Fin.ext hab
      · intro a ha
        have ha' := Finset.mem_range.mp ha
        exact ⟨⟨a, Nat.lt_trans ha' p.isLt⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha'⟩, rfl⟩
    _ = p.val := Finset.card_range _

private theorem zeros_split_at_true {N : Nat} (v : Fin N -> Bool) (p : Fin N)
    (hp : v p = true) :
    zeroPositions v = zerosBefore v p ∪ zerosAfter v p := by
  ext i
  simp only [zeroPositions, zerosBefore, zerosAfter, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro hi
    have hne : i ≠ p := by
      intro heq
      subst i
      simp [hp] at hi
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨hlt, hi⟩
    · exact Or.inr ⟨hgt, hi⟩
  · rintro (⟨hlt, hi⟩ | ⟨hgt, hi⟩)
    · exact hi
    · exact hi

private theorem zeros_split_at_false {N : Nat} (v : Fin N -> Bool) (p : Fin N)
    (hp : v p = false) :
    zeroPositions v = (zerosBefore v p ∪ {p}) ∪ zerosAfter v p := by
  ext i
  simp only [zeroPositions, zerosBefore, zerosAfter, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton]
  constructor
  · intro hi
    by_cases heq : i = p
    · exact Or.inl (Or.inr heq)
    · rcases lt_or_gt_of_ne heq with hlt | hgt
      · exact Or.inl (Or.inl ⟨hlt, hi⟩)
      · exact Or.inr ⟨hgt, hi⟩
  · rintro ((⟨_, h⟩ | h) | ⟨_, h⟩)
    · exact h
    · subst i
      exact hp
    · exact h

private theorem ones_zeros_partition_before {N : Nat} (v : Fin N -> Bool) (p : Fin N) :
    (Finset.univ.filter fun i : Fin N => i.val < p.val) =
      onesBefore v p ∪ zerosBefore v p := by
  ext i
  simp only [onesBefore, zerosBefore, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_union]
  constructor
  · intro hi
    cases h : v i
    · exact Or.inr ⟨hi, rfl⟩
    · exact Or.inl ⟨hi, rfl⟩
  · rintro (⟨hlt, _⟩ | ⟨hlt, _⟩) <;> exact hlt

private theorem inversionCount_ge_zerosAfter {N : Nat} (v : Fin N -> Bool)
    (p : Fin N) (hp : v p = true) :
    (zerosAfter v p).card <= inversionCount v := by
  classical
  let pairMap : Fin N -> Fin N × Fin N := fun j => (p, j)
  have hinj : Set.InjOn pairMap (zerosAfter v p : Set (Fin N)) := by
    intro a ha b hb hab
    exact congrArg Prod.snd hab
  have hsubset : (zerosAfter v p).image pairMap ⊆ inversionPairs v := by
    intro ij hij
    rcases Finset.mem_image.mp hij with ⟨j, hj, rfl⟩
    simp only [inversionPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      pairMap]
    simp only [zerosAfter, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨hj.1, hp, hj.2⟩
  calc
    (zerosAfter v p).card =
        (Finset.image pairMap (zerosAfter v p)).card := by
      rw [← Finset.card_image_of_injOn (f := pairMap)
        (s := zerosAfter v p) hinj]
    _ <= (inversionPairs v).card := Finset.card_le_card hsubset
    _ = inversionCount v := rfl

private theorem inversionCount_ge_onesBefore {N : Nat} (v : Fin N -> Bool)
    (p : Fin N) (hp : v p = false) :
    (onesBefore v p).card <= inversionCount v := by
  classical
  let pairMap : Fin N -> Fin N × Fin N := fun i => (i, p)
  have hinj : Set.InjOn pairMap (onesBefore v p : Set (Fin N)) := by
    intro a ha b hb hab
    exact congrArg Prod.fst hab
  have hsubset : (onesBefore v p).image pairMap ⊆ inversionPairs v := by
    intro ij hij
    rcases Finset.mem_image.mp hij with ⟨i, hi, rfl⟩
    simp only [inversionPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      pairMap]
    simp only [onesBefore, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨hi.1, hi.2, hp⟩
  calc
    (onesBefore v p).card =
        (Finset.image pairMap (onesBefore v p)).card := by
      rw [← Finset.card_image_of_injOn (f := pairMap)
        (s := onesBefore v p) hinj]
    _ <= (inversionPairs v).card := Finset.card_le_card hsubset
    _ = inversionCount v := rfl

/-- Every false key at or beyond the sorted cut creates at least its distance
from the cut (plus one) inversions. -/
theorem misplaced_zero_distance_le_inversions {N : Nat} (v : Fin N -> Bool)
    (p : Fin N) (hp : v p = false) (hq : p.val >= zeroCount v) :
    p.val - zeroCount v + 1 <= inversionCount v := by
  classical
  let q := zeroCount v
  have hqp : q <= p.val := by simpa [q] using hq
  have hbeforeSub : zerosBefore v p ⊆
      Finset.univ.filter (fun i : Fin N => i.val < p.val) := by
    intro i hi
    simp only [zerosBefore, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.1⟩
  have hbeforele : (zerosBefore v p).card <= p.val := by
    calc
      _ <= (Finset.univ.filter (fun i : Fin N => i.val < p.val)).card :=
        Finset.card_le_card hbeforeSub
      _ = p.val := card_positions_before p
  have hpSplit := zeros_split_at_false v p hp
  have hdisj1 : Disjoint (zerosBefore v p) {p} := by
    rw [Finset.disjoint_singleton_right]
    simp [zerosBefore]
  have hdisj2 : Disjoint (zerosBefore v p ∪ {p}) (zerosAfter v p) := by
    rw [Finset.disjoint_left]
    intro i hiBefore hiAfter
    simp only [zerosAfter, Finset.mem_filter, Finset.mem_univ, true_and] at hiAfter
    rcases Finset.mem_union.mp hiBefore with hbefore | hp'
    · simp only [zerosBefore, Finset.mem_filter, Finset.mem_univ, true_and] at hbefore
      exact (not_lt_of_ge (le_of_lt hiAfter.1)) hbefore.1
    · have : i = p := Finset.mem_singleton.mp hp'
      subst i
      exact (lt_irrefl p.val) hiAfter.1
  have hcard := congrArg Finset.card hpSplit
  rw [Finset.card_union_of_disjoint hdisj2,
    Finset.card_union_of_disjoint hdisj1, Finset.card_singleton] at hcard
  have hqeq : q = (zerosBefore v p).card + 1 + (zerosAfter v p).card := by
    simpa [q, zeroCount] using hcard
  have hqPos : 0 < q := by omega
  have hbeforeq : (zerosBefore v p).card <= q - 1 := by omega
  have hprefix := ones_zeros_partition_before v p
  have hprefixCard := congrArg Finset.card hprefix
  have hdisjPrefix : Disjoint (onesBefore v p) (zerosBefore v p) := by
    rw [Finset.disjoint_left]
    intro i hone hzero
    simp only [onesBefore, zerosBefore, Finset.mem_filter, Finset.mem_univ,
      true_and] at hone hzero
    have ht := hone.2
    have hf := hzero.2
    cases h : v i <;> simp_all
  rw [Finset.card_union_of_disjoint hdisjPrefix] at hprefixCard
  have hprefixSize := card_positions_before p
  rw [hprefixSize] at hprefixCard
  have honeLower : p.val - q + 1 <= (onesBefore v p).card := by
    have hsum : p.val = (onesBefore v p).card + (zerosBefore v p).card := by
      simpa only [hprefixSize] using hprefixCard
    have honeEq : (onesBefore v p).card =
        p.val - (zerosBefore v p).card := by omega
    have hsub : p.val - q + 1 <=
        p.val - (zerosBefore v p).card := by
      calc
        p.val - q + 1 = p.val - (q - 1) := by omega
        _ <= p.val - (zerosBefore v p).card :=
          Nat.sub_le_sub_left hbeforeq p.val
    rw [honeEq]
    exact hsub
  simpa [q] using honeLower.trans (inversionCount_ge_onesBefore v p hp)

/-- Every true key before the sorted cut creates at least its distance from
the cut inversions. -/
theorem misplaced_one_distance_le_inversions {N : Nat} (v : Fin N -> Bool)
    (p : Fin N) (hp : v p = true) (hpq : p.val < zeroCount v) :
    zeroCount v - p.val <= inversionCount v := by
  classical
  let q := zeroCount v
  have hpq' : p.val < q := by simpa [q] using hpq
  have hpartition := ones_zeros_partition_before v p
  have hcard := congrArg Finset.card hpartition
  have hdisj : Disjoint (onesBefore v p) (zerosBefore v p) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have hv1 := (Finset.mem_filter.mp hi1).2
    have hv2 := (Finset.mem_filter.mp hi2).2
    cases h : v i <;> simp_all
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  have hprefix := card_positions_before p
  have hbeforele : (zerosBefore v p).card <= p.val := by
    calc
      _ <= (Finset.univ.filter (fun i : Fin N => i.val < p.val)).card :=
        Finset.card_le_card (by
          intro i hi
          simp only [zerosBefore, Finset.mem_filter, Finset.mem_univ,
            true_and] at hi
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hi.1⟩)
      _ = p.val := hprefix
  have hzeros : (zerosBefore v p).card <= q - 1 := by
    omega
  have hone : (onesBefore v p).card = p.val - (zerosBefore v p).card := by
    rw [hprefix] at hcard
    omega
  have hafter : (zerosAfter v p).card = q - (zerosBefore v p).card := by
    have hsplit := zeros_split_at_true v p hp
    have hsplitCard := congrArg Finset.card hsplit
    have hdisj' : Disjoint (zerosBefore v p) (zerosAfter v p) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      simp only [zerosBefore, zerosAfter, Finset.mem_filter, Finset.mem_univ,
        true_and] at hi1 hi2
      exact (not_lt_of_ge (le_of_lt hi2.1)) hi1.1
    rw [Finset.card_union_of_disjoint hdisj'] at hsplitCard
    have hqeq : q = (zerosBefore v p).card + (zerosAfter v p).card := by
      simpa [q, zeroCount] using hsplitCard
    omega
  have hafterLower : q - p.val <= (zerosAfter v p).card := by
    rw [hafter]
    omega
  exact hafterLower.trans (inversionCount_ge_zerosAfter v p hp)

/-- An inversion bound localizes every misplaced bit to a band around the
true sorted cut. Zeros cannot lie more than I ranks to its right, and ones
cannot lie more than I ranks to its left. -/
theorem misplaced_bits_lie_near_cut {N : Nat} (v : Fin N -> Bool)
    (I : Nat) (hinv : inversionCount v <= I) :
    (forall p : Fin N, v p = false -> zeroCount v <= p.val ->
      p.val < zeroCount v + I) /\
    (forall p : Fin N, v p = true -> p.val < zeroCount v ->
      zeroCount v <= p.val + I) := by
  constructor
  · intro p hp hq
    have hdist := misplaced_zero_distance_le_inversions v p hp hq
    omega
  · intro p hp hpq
    have hdist := misplaced_one_distance_le_inversions v p hp hpq
    omega

end Chvatal.D2InversionLocalization
