module
/-
  # Paterson's Restricted Halvers

  Paterson's sorting construction uses `(ε, α)`-halvers: the error guarantee
  is required only for extreme sets of size at most `α * m`, where the network
  has `2 * m` wires. Keeping `α` in the interface is essential; the depth
  improvement in Paterson's separator comes from using different supported
  fractions at different levels.

  This file defines the restricted-halver interface, models one random
  bipartite matching as a comparator layer, and converts bounded matching
  sequences into uniformly depth-bounded families. The probabilistic existence
  theorem and the separator construction are subsequent milestones.
-/

public import AKS.Halver.Defs
public import AKS.Sort.Depth

@[expose] public section

open Finset BigOperators

/-! **Finite union bound**

The probabilistic existence argument reduces to showing that the union of all
bad events occupies fewer points than the finite sample space. This lemma
isolates that last step so the event-counting estimates can be proved and
checked independently.
-/

/-- If a finite union of bad-event sets has cardinality strictly below the
sample space, there is a sample point outside every bad event. -/
theorem exists_outside_finset_union {Ω ι : Type*} [DecidableEq Ω]
    (samples : Finset Ω) (events : Finset ι) (bad : ι → Finset Ω)
    (hsmall : (events.biUnion bad).card < samples.card) :
    ∃ x ∈ samples, ∀ i ∈ events, x ∉ bad i := by
  have hnot_subset : ¬ samples ⊆ events.biUnion bad := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    omega
  obtain ⟨x, hx, hnot⟩ := Finset.not_subset.mp hnot_subset
  refine ⟨x, hx, ?_⟩
  intro i hi hxi
  exact hnot (Finset.mem_biUnion.mpr ⟨i, hi, hxi⟩)

/-- A convenient union-bound form: bounding the sum of event cardinalities by
less than the sample-space cardinality guarantees a sample avoiding all
events. -/
theorem exists_outside_finset_events_of_sum_card_lt {Ω ι : Type*}
    [DecidableEq Ω] [DecidableEq ι] (samples : Finset Ω) (events : Finset ι)
    (bad : ι → Finset Ω)
    (hsmall : (∑ i ∈ events, (bad i).card) < samples.card) :
    ∃ x ∈ samples, ∀ i ∈ events, x ∉ bad i := by
  apply exists_outside_finset_union samples events bad
  exact lt_of_le_of_lt Finset.card_biUnion_le hsmall

/-- The usual normalized union bound. If each bad event has relative size at
most `weight i` and the total weight is strictly below one, some sample avoids
all events. This is the form needed after Paterson's per-event counting
estimate has been established. -/
theorem exists_outside_finset_events_of_density {Ω ι : Type*}
    [DecidableEq Ω] [DecidableEq ι] (samples : Finset Ω) (events : Finset ι)
    (bad : ι → Finset Ω) (weight : ι → ℚ)
    (hsamples : 0 < samples.card)
    (hevent : ∀ i ∈ events, ((bad i).card : ℚ) ≤ weight i * samples.card)
    (hweight : (∑ i ∈ events, weight i) < 1) :
    ∃ x ∈ samples, ∀ i ∈ events, x ∉ bad i := by
  apply exists_outside_finset_events_of_sum_card_lt samples events bad
  have hsum : (∑ i ∈ events, ((bad i).card : ℚ)) ≤
      (∑ i ∈ events, weight i * samples.card) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hevent i hi
  have hfactor : (∑ i ∈ events, weight i * samples.card) =
      (∑ i ∈ events, weight i) * samples.card := by
    rw [Finset.sum_mul]
  have hlt : (∑ i ∈ events, ((bad i).card : ℚ)) < samples.card := by
    rw [hfactor] at hsum
    have hsamplesQ : (0 : ℚ) < samples.card := by exact_mod_cast hsamples
    have hprod := mul_lt_mul_of_pos_right hweight hsamplesQ
    exact lt_of_le_of_lt hsum (by simpa using hprod)
  exact_mod_cast hlt

/-! **Restricted halver property** -/

/-- Both directional error bounds for a restricted halver.

    On `2 * m` wires, at most `ε * k` of the `k` smallest elements may land in
    the right output half, and at most `ε * k` of the `k` largest may land in
    the left output half. Unlike `IsEpsilonHalver`, these bounds are required
    only when `k ≤ α * m` (interpreted as a real inequality). -/
def IsEpsilonAlphaHalver {m : ℕ} (net : ComparatorNetwork (2 * m))
    (ε α : ℚ) : Prop :=
  ∀ v : Equiv.Perm (Fin (2 * m)),
    (∀ k : ℕ, (k : ℝ) ≤ (α : ℝ) * m →
      ((Finset.univ.filter (fun pos : Fin (2 * m) =>
        m ≤ pos.val ∧ (net.exec v pos).val < k)).card : ℝ) ≤ (ε : ℝ) * k) ∧
    (∀ k : ℕ, (k : ℝ) ≤ (α : ℝ) * m →
      ((Finset.univ.filter (fun pos : Fin (2 * m) =>
        pos.val < m ∧ 2 * m - k ≤ (net.exec v pos).val)).card : ℝ) ≤ (ε : ℝ) * k)

/-- A uniformly depth-bounded family of Paterson `(ε, α)`-halvers at every
    arity. The side conditions match the range in Paterson's existence theorem.
    This family is intentionally distinct from `HalverFamily`: when `α < 1`,
    its guarantee is weaker and cannot be passed to the existing full-range
    halver-to-separator proof. -/
structure AlphaHalverFamily (ε α : ℚ) where
  hε_pos : 0 < ε
  hε_lt_half : ε < 1 / 2
  hα_pos : 0 < α
  hα_le_one : α ≤ 1
  depth : ℕ
  net : (m : ℕ) → ComparatorNetwork (2 * m)
  isHalver : ∀ m, IsEpsilonAlphaHalver (net m) ε α
  depth_le : ∀ m, (net m).depth ≤ depth

/-- An ordinary full-range halver also satisfies every valid restricted
    `(ε, α)` contract. -/
theorem IsEpsilonHalver.toAlphaHalver {m : ℕ}
    {net : ComparatorNetwork (2 * m)} {ε α : ℚ}
    (hα : α ≤ 1) (h : IsEpsilonHalver net (ε : ℝ)) :
    IsEpsilonAlphaHalver net ε α := by
  intro v
  have hbase := h v
  have hαR : (α : ℝ) ≤ 1 := by exact_mod_cast hα
  constructor
  · intro k hk
    have hkR : (k : ℝ) ≤ (m : ℝ) := by
      calc
        (k : ℝ) ≤ (α : ℝ) * m := hk
        _ ≤ 1 * m := mul_le_mul_of_nonneg_right hαR
          (Nat.cast_nonneg m)
        _ = (m : ℝ) := by ring
    have hkNat : k ≤ m := by exact_mod_cast hkR
    have hkNat' : k ≤ Fintype.card (Fin (2 * m)) / 2 := by
      simp only [Fintype.card_fin]
      omega
    have hbound := hbase.1 k hkNat'
    simpa only [EpsilonInitialHalved, Fintype.card_fin, rank_fin_val,
      show 2 * m / 2 = m from by omega] using hbound
  · intro k hk
    have hkR : (k : ℝ) ≤ (m : ℝ) := by
      calc
        (k : ℝ) ≤ (α : ℝ) * m := hk
        _ ≤ 1 * m := mul_le_mul_of_nonneg_right hαR
          (Nat.cast_nonneg m)
        _ = (m : ℝ) := by ring
    have hkNat : k ≤ m := by exact_mod_cast hkR
    exact hbase.2.val_bound k hkNat

/-- Restrict an existing ordinary `HalverFamily` to any supported fraction
    `α ≤ 1`. This bridge is useful for reusing current halvers, though it does
    not obtain Paterson's improved depth because the full-range guarantee is
    stronger than needed. -/
def AlphaHalverFamily.ofFullRange {ε α : ℚ}
    (family : HalverFamily ε) (hε_pos : 0 < ε) (hε_lt_half : ε < 1 / 2)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1) : AlphaHalverFamily ε α where
  hε_pos := hε_pos
  hε_lt_half := hε_lt_half
  hα_pos := hα_pos
  hα_le_one := hα_le_one
  depth := family.depth
  net := family.net
  isHalver m := (family.isHalver m).toAlphaHalver hα_le_one
  depth_le := family.depth_le

/-! **Random matching layer model** -/

/-- The comparator matching associated with a bijection from the left half of
    the wires to the right half. -/
def patersonMatchingComparator {m : ℕ} (g : Equiv.Perm (Fin m))
    (i : Fin m) : Comparator (2 * m) where
  i := ⟨i.val, by omega⟩
  j := ⟨m + (g i).val, by have := (g i).isLt; omega⟩
  h := by
    calc
      i.val < m := i.isLt
      _ ≤ m + (g i).val := Nat.le_add_right m _

/-- One comparison layer from Paterson's probabilistic construction. -/
def patersonMatchingLayer {m : ℕ} (g : Equiv.Perm (Fin m)) : ComparatorNetwork (2 * m) :=
  ⟨List.ofFn (patersonMatchingComparator g)⟩

/-- The comparators in a matching layer are pairwise wire-disjoint. -/
theorem patersonMatchingLayer_parallel {m : ℕ} (g : Equiv.Perm (Fin m)) :
    IsParallelLayer (patersonMatchingLayer g).comparators := by
  change (List.ofFn (patersonMatchingComparator g)).Pairwise _
  rw [List.pairwise_ofFn]
  intro i j hij
  have hijval : i.val < j.val := Fin.mk_lt_mk.mp hij
  have hleft : (patersonMatchingComparator g i).i ≠
      (patersonMatchingComparator g j).i := by
    intro h
    have hv := congrArg Fin.val h
    simp [patersonMatchingComparator] at hv
    omega
  have hleftRight : (patersonMatchingComparator g i).i ≠
      (patersonMatchingComparator g j).j := by
    intro h
    have hv := congrArg Fin.val h
    simp [patersonMatchingComparator] at hv
    have hi := i.isLt
    omega
  have hrightLeft : (patersonMatchingComparator g i).j ≠
      (patersonMatchingComparator g j).i := by
    intro h
    have hv := congrArg Fin.val h
    simp [patersonMatchingComparator] at hv
    have hj := j.isLt
    omega
  have hright : (patersonMatchingComparator g i).j ≠
      (patersonMatchingComparator g j).j := by
    intro h
    have hv := congrArg Fin.val h
    simp [patersonMatchingComparator] at hv
    have hgeq : (g i).val = (g j).val := by omega
    have hgeq' : g i = g j := Fin.ext hgeq
    have hij' : i = j := g.injective hgeq'
    exact (ne_of_lt hijval) (congrArg Fin.val hij')
  change ¬ Comparator.overlaps (patersonMatchingComparator g i)
    (patersonMatchingComparator g j)
  simp [Comparator.overlaps, hleft, hleftRight, hrightLeft, hright]

/-- Concatenate a sequence of Paterson matching layers. -/
def patersonMatchingNetwork {m : ℕ} (gs : List (Equiv.Perm (Fin m))) :
    ComparatorNetwork (2 * m) :=
  ⟨gs.flatMap fun g => (patersonMatchingLayer g).comparators⟩

/-- The zero-wire case of the restricted-halver theorem needs no matching
layers. It is kept separate because the probabilistic density uses `1 / m`. -/
theorem patersonZeroHalver (ε α : ℚ) :
    IsEpsilonAlphaHalver
      (patersonMatchingNetwork ([] : List (Equiv.Perm (Fin 0)))) ε α := by
  intro v
  constructor <;> intro k hk
  · have hk0 : k = 0 := by
      have h : (k : ℝ) ≤ 0 := by simpa using hk
      have hnat : k ≤ 0 := by exact_mod_cast h
      omega
    subst k
    simp
  · have hk0 : k = 0 := by
      have h : (k : ℝ) ≤ 0 := by simpa using hk
      have hnat : k ≤ 0 := by exact_mod_cast h
      omega
    subst k
    simp

/-- A sequence of `c` matching layers has network depth at most `c`. -/
theorem patersonMatchingNetwork_depth_le {m : ℕ}
    (gs : List (Equiv.Perm (Fin m))) :
    (patersonMatchingNetwork gs).depth ≤ gs.length := by
  calc
    (patersonMatchingNetwork gs).depth ≤
        (gs.map fun g => (patersonMatchingLayer g).comparators).length :=
      depth_le_of_decomposition (patersonMatchingNetwork gs)
        (gs.map fun g => (patersonMatchingLayer g).comparators) ⟨by
          intro layer hlayer
          simp only [List.mem_map] at hlayer
          obtain ⟨g, _, rfl⟩ := hlayer
          exact patersonMatchingLayer_parallel g,
        by
          induction gs with
          | nil => rfl
          | cons g gs ih =>
              change ((patersonMatchingLayer g).comparators ++
                (List.map (fun h => (patersonMatchingLayer h).comparators) gs).flatten) =
                (g :: gs).flatMap fun h => (patersonMatchingLayer h).comparators
              change (List.map (fun h => (patersonMatchingLayer h).comparators) gs).flatten =
                gs.flatMap fun h => (patersonMatchingLayer h).comparators at ih
              rw [List.flatMap_cons, ← ih]⟩
    _ = gs.length := by simp

/-- Each matching layer has exactly one comparator per wire in a half. -/
theorem patersonMatchingNetwork_size {m : ℕ}
    (gs : List (Equiv.Perm (Fin m))) :
    (patersonMatchingNetwork gs).size = m * gs.length := by
  induction gs with
  | nil => simp [patersonMatchingNetwork, ComparatorNetwork.size]
  | cons g gs ih =>
      simp [patersonMatchingNetwork, ComparatorNetwork.size, patersonMatchingLayer,
        List.length_flatMap, List.length_ofFn, Nat.mul_succ]
      rw [Nat.mul_comm gs.length m]
      exact Nat.add_comm _ _

/-- Convert an all-arities probabilistic existence theorem into an
    `AlphaHalverFamily`. The construction uses classical choice, reflecting
    that Paterson's proof establishes existence but does not give an explicit
    matching sequence. A later finite-search argument could replace this
    noncomputable adapter if desired. -/
noncomputable def alphaHalverFamilyOfExists {ε α : ℚ} (d : ℕ)
    (hε_pos : 0 < ε) (hε_lt_half : ε < 1 / 2)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hexists : ∀ m, ∃ gs : List (Equiv.Perm (Fin m)),
      gs.length ≤ d ∧ IsEpsilonAlphaHalver (patersonMatchingNetwork gs) ε α) :
    AlphaHalverFamily ε α where
  hε_pos := hε_pos
  hε_lt_half := hε_lt_half
  hα_pos := hα_pos
  hα_le_one := hα_le_one
  depth := d
  net m := patersonMatchingNetwork (Classical.choose (hexists m))
  isHalver m := (Classical.choose_spec (hexists m)).2
  depth_le m := by
    exact (patersonMatchingNetwork_depth_le (Classical.choose (hexists m))).trans
      (Classical.choose_spec (hexists m)).1

/-- Increasing the error tolerance preserves a restricted-halver guarantee. -/
theorem IsEpsilonAlphaHalver.mono_ε {m : ℕ}
    {net : ComparatorNetwork (2 * m)} {ε₁ ε₂ α : ℚ}
    (h : IsEpsilonAlphaHalver net ε₁ α) (hle : ε₁ ≤ ε₂) :
    IsEpsilonAlphaHalver net ε₂ α := by
  intro v
  obtain ⟨hleft, hright⟩ := h v
  constructor
  · intro k hk
    calc
      ((Finset.univ.filter (fun pos : Fin (2 * m) =>
        m ≤ pos.val ∧ (net.exec v pos).val < k)).card : ℝ)
          ≤ (ε₁ : ℝ) * k := hleft k hk
      _ ≤ (ε₂ : ℝ) * k := by
          exact mul_le_mul_of_nonneg_right (Rat.cast_le.mpr hle) (Nat.cast_nonneg k)
  · intro k hk
    calc
      ((Finset.univ.filter (fun pos : Fin (2 * m) =>
        pos.val < m ∧ 2 * m - k ≤ (net.exec v pos).val)).card : ℝ)
          ≤ (ε₁ : ℝ) * k := hright k hk
      _ ≤ (ε₂ : ℝ) * k := by
          exact mul_le_mul_of_nonneg_right (Rat.cast_le.mpr hle) (Nat.cast_nonneg k)

end
