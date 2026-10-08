module
/-
  # ε-Halver Theory

  Defines ε-halvers and supporting infrastructure.

  Key definitions:
  • `countOnes`, `sortedVersion`: Boolean sequence sorting infrastructure
  • `EpsilonInitialHalved`, `EpsilonHalved`, `IsEpsilonHalver`: permutation-based
    halver definitions (AKS Section 3). Uses `rank` from `Fin.lean`.
  • `epsHalverMerge`: iterated halver composition
  • `IsEpsilonSorted`, `Monotone.bool_pattern`: sortedness infrastructure

  The proof that expanders yield ε-halvers is in `FromExpander.lean`.
-/

public import AKS.Sort.Defs
public import AKS.Sort.Depth
public import AKS.Misc.Fin

@[expose] public section


open Finset BigOperators


/-! **Sorted Version and Counting** -/









/-! **ε-Halvers (Permutation-Based Definition)** -/

/-- Initial-segment halver property (AKS Section 3, permutation-based):
    for each initial segment `{0,...,k-1}` with `k ≤ n/2`, the number of
    positions from the bottom half (`rank pos ≥ n/2`) whose output element
    has rank < k is at most `ε · k`. -/
def EpsilonInitialHalved {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (ε : ℝ) : Prop :=
  let n := Fintype.card α
  ∀ k : ℕ, k ≤ n / 2 →
    ((Finset.univ.filter (fun pos : α ↦
        n / 2 ≤ rank pos ∧ rank (w pos) < k)).card : ℝ) ≤ ε * k

/-- End-segment halver property: dual of `EpsilonInitialHalved` via order reversal. -/
def EpsilonFinalHalved {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (ε : ℝ) : Prop :=
  EpsilonInitialHalved (α := αᵒᵈ) w ε


/-- A function is ε-halved if it satisfies both initial and final segment bounds. -/
def EpsilonHalved {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (ε : ℝ) : Prop :=
  EpsilonInitialHalved w ε ∧ EpsilonFinalHalved w ε

/-- A comparator network is an ε-halver if for every permutation input,
    the output is ε-halved.

    (AKS Section 3) This tracks labeled elements via permutations rather than
    0-1 values, which is essential for the segment-wise bounds — in the 0-1 case,
    same-valued elements are indistinguishable, making segment-wise counting
    impossible. -/
def IsEpsilonHalver {n : ℕ} (net : ComparatorNetwork n) (ε : ℝ) : Prop :=
  ∀ (v : Equiv.Perm (Fin n)),
    EpsilonHalved (net.exec v) ε

/-- `EpsilonInitialHalved` is monotone in ε: larger ε is weaker. -/
theorem EpsilonInitialHalved.mono {α : Type*} [Fintype α] [LinearOrder α]
    {w : α → α} {ε₁ ε₂ : ℝ} (h : EpsilonInitialHalved w ε₁) (hle : ε₁ ≤ ε₂) :
    EpsilonInitialHalved w ε₂ := by
  intro k hk
  calc ((Finset.univ.filter _).card : ℝ) ≤ ε₁ * k := h k hk
    _ ≤ ε₂ * k := by exact mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg k)

/-- `EpsilonHalved` is monotone in ε. -/
theorem EpsilonHalved.mono {α : Type*} [Fintype α] [LinearOrder α]
    {w : α → α} {ε₁ ε₂ : ℝ} (h : EpsilonHalved w ε₁) (hle : ε₁ ≤ ε₂) :
    EpsilonHalved w ε₂ :=
  ⟨h.1.mono hle, h.2.mono hle⟩

/-- `IsEpsilonHalver` is monotone in ε: a halver with error ε₁ is also
    a halver with any larger error ε₂ ≥ ε₁. -/
theorem IsEpsilonHalver.mono {n : ℕ} {net : ComparatorNetwork n}
    {ε₁ ε₂ : ℝ} (h : IsEpsilonHalver net ε₁) (hle : ε₁ ≤ ε₂) :
    IsEpsilonHalver net ε₂ :=
  fun v ↦ (h v).mono hle



/-! **Top/Bottom Half Partitioning** -/







/-! **Halver Composition** -/

/-- An ε-sorted vector: at most εn elements are not in their
    correct sorted position. -/
def IsEpsilonSorted {n : ℕ} (v : Fin n → Bool) (ε : ℝ) : Prop :=
  ∃ (w : Fin n → Bool), Monotone w ∧
    ((Finset.univ.filter (fun i ↦ v i ≠ w i)).card : ℝ) ≤ ε * n

/-! **Basic Properties of IsEpsilonSorted** -/


/-- The false-set cardinality is a `0*1*` witness for a monotone Boolean sequence. -/
lemma Monotone.bool_pattern_at_card {n : ℕ} (w : Fin n → Bool) (hw : Monotone w) :
    let k := (Finset.univ.filter (fun i : Fin n ↦ w i = false)).card
    (∀ i : Fin n, (i : ℕ) < k → w i = false) ∧
      (∀ i : Fin n, k ≤ (i : ℕ) → w i = true) := by
  dsimp only
  set k := (Finset.univ.filter (fun i : Fin n ↦ w i = false)).card
  constructor
  · -- For i.val < k: w i = false
    intro ⟨i, hi⟩ h_lt
    by_contra h_not
    have h_true : w ⟨i, hi⟩ = true := by
      match h : w ⟨i, hi⟩ with
      | true => rfl
      | false => exact absurd h h_not
    -- Every j ≥ i has w j = true (by monotonicity)
    have h_above : ∀ j : Fin n, i ≤ j.val → w j = true := by
      intro ⟨j, hj⟩ h_ij
      have := hw (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from h_ij)
      rw [h_true] at this
      match h : w ⟨j, hj⟩ with
      | true => rfl
      | false => rw [h] at this; exact absurd this (by decide)
    -- So false set ⊆ {j | j.val < i}
    have h_sub : Finset.univ.filter (fun j : Fin n ↦ w j = false) ⊆
        Finset.Iio ⟨i, hi⟩ := by
      intro ⟨j, hj⟩ hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      simp only [Finset.mem_Iio, Fin.lt_def]
      by_contra h_ge; push_neg at h_ge
      exact absurd (h_above ⟨j, hj⟩ h_ge) (by simp [hm])
    -- Card of false set ≤ card of Iio = i
    have := Finset.card_le_card h_sub
    rw [Fin.card_Iio] at this; omega
  · -- For k ≤ i.val: w i = true
    intro ⟨i, hi⟩ h_ge
    by_contra h_not
    have h_false : w ⟨i, hi⟩ = false := by
      match h : w ⟨i, hi⟩ with
      | false => rfl
      | true => exact absurd h h_not
    -- Every j ≤ i has w j = false (by monotonicity)
    have h_below : ∀ j : Fin n, j.val ≤ i → w j = false := by
      intro ⟨j, hj⟩ h_ji
      have := hw (show (⟨j, hj⟩ : Fin n) ≤ ⟨i, hi⟩ from h_ji)
      rw [h_false] at this
      match h : w ⟨j, hj⟩ with
      | false => rfl
      | true => rw [h] at this; exact absurd this (by decide)
    -- So Iic ⟨i, hi⟩ ⊆ false set
    have h_sub : Finset.Iic ⟨i, hi⟩ ⊆
        Finset.univ.filter (fun j : Fin n ↦ w j = false) := by
      intro ⟨j, hj⟩ hm
      simp only [Finset.mem_Iic, Fin.le_iff_val_le_val] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h_below ⟨j, hj⟩ hm
    -- Card of Iic = i + 1 ≤ card of false set = k
    have := Finset.card_le_card h_sub
    rw [Fin.card_Iic] at this; omega


/-- Relaxation: if ε₁ ≤ ε₂, then ε₁-sorted implies ε₂-sorted -/
lemma IsEpsilonSorted.mono {n : ℕ} {v : Fin n → Bool} {ε₁ ε₂ : ℝ}
    (h : IsEpsilonSorted v ε₁) (hle : ε₁ ≤ ε₂) :
    IsEpsilonSorted v ε₂ := by
  obtain ⟨w, hw_mono, hw_card⟩ := h
  refine ⟨w, hw_mono, ?_⟩
  calc ((Finset.univ.filter (fun i ↦ v i ≠ w i)).card : ℝ)
      ≤ ε₁ * n := hw_card
    _ ≤ ε₂ * n := by apply mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)



/-! **Halver Family** -/

/-- A family of ε-halver networks at all even sizes, with bounded depth.
    The network `net m` operates on `2 * m` wires, covering sizes 0, 2, 4, 6, ...
    At `m = 0` the network operates on 0 wires (trivially halved by any network).

    The depth bound is fundamental: size ≤ m · depth follows from depth_le
    (each of depth rounds has ≤ m comparators on 2*m bipartite wires). -/
structure HalverFamily (ε : ℚ) where
  /-- Uniform depth bound for all networks in the family. -/
  depth : ℕ
  /-- The halver network for each index `m`. Operates on `2 * m` wires. -/
  net : (m : ℕ) → ComparatorNetwork (2 * m)
  /-- Each network is an ε-halver. -/
  isHalver : ∀ m, IsEpsilonHalver (net m) ↑ε
  /-- Each network has depth at most `depth`. -/
  depth_le : ∀ m, (net m).depth ≤ depth



/-! **Network Cast** -/

/-- Cast a comparator network to a different wire count via an equality proof. -/
def ComparatorNetwork.cast {n m : ℕ} (net : ComparatorNetwork n) (h : n = m) :
    ComparatorNetwork m :=
  h ▸ net



end
