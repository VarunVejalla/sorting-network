module

/-
  # Chvátal Lemma 6.2, claim (ii): counting distinct tops

  Source: V. Chvátal, DCS-TR-294 (1992), §6, proof of Lemma 6.2, claim (ii).

  A monotone 0/1 matrix is determined by its column sums `s : Fin n → ℕ`; its *top*
  (the matrix without its bottom `h = f/2` rows) is determined by `t c = s c - h`.
  Writing `tops h n j` for the set of tops of all `s` with `Σ s ≤ j`, we prove

    `(tops h n j).card ≤ Σ_{k ≤ n} C(n,k) · C(j - h·k, k)`.

  The proof is an induction on the number of columns: peel off column `0`; either its
  top is `0` (tops of the remaining columns with the same budget), or its top is
  `a - h ≥ 1` (remaining columns with budget `j - a`). A hockey-stick estimate
  identifies the resulting recursion with the closed form.
-/

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Chvatal

open Finset

/-- Column-sum vectors with total at most `j`. -/
def sset (n j : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (j + 1)).filter fun s => ∑ c, s c ≤ j

/-- Tops (column sums with the bottom `h` rows removed) of vectors with total at most `j`. -/
def tops (h n j : ℕ) : Finset (Fin n → ℕ) :=
  (sset n j).image fun s c => s c - h

/-- Prepend a column value (non-dependent `Fin.cons`). -/
def consN {n : ℕ} (a : ℕ) (t : Fin n → ℕ) : Fin (n + 1) → ℕ := Fin.cons a t

/-- Recursive bound: first column has top `0`, or top `a - h ≥ 1` with budget `j - a`. -/
def topBound (h : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, j => topBound h n j + ∑ a ∈ Finset.Icc (h + 1) j, topBound h n (j - a)

theorem mem_sset {n j : ℕ} {s : Fin n → ℕ} : s ∈ sset n j ↔ ∑ c, s c ≤ j := by
  unfold sset
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro hs
    refine ⟨fun c => ?_, hs⟩
    have : s c ≤ ∑ c, s c := Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ c)
    omega

theorem tops_card_le_topBound (h n : ℕ) : ∀ j, (tops h n j).card ≤ topBound h n j := by
  induction n with
  | zero =>
    intro j
    simp only [topBound]
    exact Finset.card_le_one_of_subsingleton _
  | succ n ih =>
    intro j
    have hsub : tops h (n + 1) j ⊆
        (tops h n j).image (consN 0) ∪
        (Finset.Icc (h + 1) j).biUnion fun a =>
          (tops h n (j - a)).image (consN (a - h)) := by
      intro t ht
      unfold tops at ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      rw [mem_sset, Fin.sum_univ_succ] at hs
      have htail : (fun c : Fin n => s c.succ) ∈ sset n (j - s 0) := by
        rw [mem_sset]; omega
      have hcons : (fun c => s c - h) =
          consN (s 0 - h) (fun c : Fin n => s c.succ - h) := by
        funext c
        refine Fin.cases ?_ (fun i => ?_) c <;> simp [consN]
      rw [Finset.mem_union]
      by_cases ha : s 0 ≤ h
      · left
        rw [Finset.mem_image]
        refine ⟨fun c : Fin n => s c.succ - h, ?_, ?_⟩
        · unfold tops
          rw [Finset.mem_image]
          refine ⟨fun c : Fin n => s c.succ, ?_, rfl⟩
          rw [mem_sset]; omega
        · rw [hcons, Nat.sub_eq_zero_of_le ha]
      · right
        rw [Finset.mem_biUnion]
        refine ⟨s 0, ?_, ?_⟩
        · rw [Finset.mem_Icc]; omega
        · rw [Finset.mem_image]
          refine ⟨fun c : Fin n => s c.succ - h, ?_, hcons.symm⟩
          unfold tops
          rw [Finset.mem_image]
          exact ⟨fun c : Fin n => s c.succ, htail, rfl⟩
    calc (tops h (n + 1) j).card
        ≤ ((tops h n j).image (consN 0) ∪
          (Finset.Icc (h + 1) j).biUnion fun a =>
            (tops h n (j - a)).image
              (consN (a - h))).card :=
          Finset.card_le_card hsub
      _ ≤ ((tops h n j).image (consN 0)).card +
          ((Finset.Icc (h + 1) j).biUnion fun a =>
            (tops h n (j - a)).image
              (consN (a - h))).card :=
          Finset.card_union_le _ _
      _ ≤ (tops h n j).card +
          ∑ a ∈ Finset.Icc (h + 1) j, ((tops h n (j - a)).image
              (consN (a - h))).card := by
          gcongr
          · exact Finset.card_image_le
          · exact Finset.card_biUnion_le
      _ ≤ topBound h n j + ∑ a ∈ Finset.Icc (h + 1) j, topBound h n (j - a) := by
          gcongr with a ha
          · exact ih j
          · exact Finset.card_image_le.trans (ih (j - a))


/-! ## Closed form -/

/-- Reflection: sum over `a ∈ [h+1, j]` of `F (j - a)` is a sum over `m < j - h`. -/
theorem sum_Icc_reflect (h j : ℕ) (F : ℕ → ℕ) :
    ∑ a ∈ Finset.Icc (h + 1) j, F (j - a) = ∑ m ∈ Finset.range (j - h), F m := by
  refine Finset.sum_nbij' (fun a => j - a) (fun m => j - m) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Icc] at ha; simp only [Finset.mem_range]; omega
  · intro m hm; simp only [Finset.mem_range] at hm; simp only [Finset.mem_Icc]; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; show j - (j - a) = a; omega
  · intro m hm; simp only [Finset.mem_range] at hm; show j - (j - m) = m; omega
  · intro a _; rfl

/-- Hockey stick with a shifted argument. -/
theorem sum_range_choose_shift_le (h k : ℕ) :
    ∀ M, ∑ m ∈ Finset.range M, Nat.choose (m - h * k) k ≤ Nat.choose (M - h * k) (k + 1) := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    by_cases hM : h * k ≤ M
    · have e : M + 1 - h * k = (M - h * k) + 1 := by omega
      have hp : Nat.choose ((M - h * k) + 1) (k + 1) =
          Nat.choose (M - h * k) k + Nat.choose (M - h * k) (k + 1) :=
        Nat.choose_succ_succ' _ _
      rw [e, hp]
      omega
    · have hk : k ≠ 0 := by
        rintro rfl; simp at hM
      have h0 : M - h * k = 0 := by omega
      have h1 : Nat.choose (M - h * k) k = 0 := by
        rw [h0]; exact Nat.choose_eq_zero_of_lt (by omega)
      have h2 : Nat.choose (M - h * k) (k + 1) = 0 := by
        rw [h0]; exact Nat.choose_eq_zero_of_lt (by omega)
      omega

theorem sum_Icc_choose_le (h k j : ℕ) :
    ∑ a ∈ Finset.Icc (h + 1) j, Nat.choose (j - a - h * k) k ≤
      Nat.choose (j - h * (k + 1)) (k + 1) := by
  have := sum_Icc_reflect h j (fun m => Nat.choose (m - h * k) k)
  simp only at this
  rw [this]
  refine (sum_range_choose_shift_le h k (j - h)).trans ?_
  have e : j - h - h * k = j - h * (k + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
  rw [e]

/-- Closed-form bound of claim (ii). -/
def topClosed (h n j : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.choose n k * Nat.choose (j - h * k) k

theorem topClosed_succ (h n j : ℕ) :
    topClosed h (n + 1) j = topClosed h n j +
      ∑ k ∈ Finset.range (n + 1), Nat.choose n k * Nat.choose (j - h * (k + 1)) (k + 1) := by
  have A : ∑ k ∈ Finset.range (n + 1), Nat.choose n (k + 1) * Nat.choose (j - h * (k + 1)) (k + 1)
      = ∑ k ∈ Finset.range n, Nat.choose n (k + 1) * Nat.choose (j - h * (k + 1)) (k + 1) := by
    rw [Finset.sum_range_succ]; simp [Nat.choose_succ_self]
  have B : topClosed h n j =
      ∑ k ∈ Finset.range n, Nat.choose n (k + 1) * Nat.choose (j - h * (k + 1)) (k + 1) + 1 := by
    unfold topClosed
    rw [Finset.sum_range_succ' _ n]; simp
  unfold topClosed
  rw [Finset.sum_range_succ' _ (n + 1)]
  simp_rw [Nat.choose_succ_succ', add_mul]
  rw [Finset.sum_add_distrib, A]
  unfold topClosed at B
  rw [B]
  simp
  ring

theorem topBound_le_topClosed (h n : ℕ) : ∀ j, topBound h n j ≤ topClosed h n j := by
  induction n with
  | zero => intro j; simp [topBound, topClosed]
  | succ n ih =>
    intro j
    rw [topClosed_succ]
    simp only [topBound]
    have h1 : ∑ a ∈ Finset.Icc (h + 1) j, topBound h n (j - a) ≤
        ∑ k ∈ Finset.range (n + 1), Nat.choose n k * Nat.choose (j - h * (k + 1)) (k + 1) := by
      calc ∑ a ∈ Finset.Icc (h + 1) j, topBound h n (j - a)
          ≤ ∑ a ∈ Finset.Icc (h + 1) j, topClosed h n (j - a) :=
            Finset.sum_le_sum fun a _ => ih _
        _ = ∑ a ∈ Finset.Icc (h + 1) j, ∑ k ∈ Finset.range (n + 1),
              Nat.choose n k * Nat.choose (j - a - h * k) k := rfl
        _ = ∑ k ∈ Finset.range (n + 1), Nat.choose n k *
              ∑ a ∈ Finset.Icc (h + 1) j, Nat.choose (j - a - h * k) k := by
            rw [Finset.sum_comm]
            simp_rw [Finset.mul_sum]
        _ ≤ _ := Finset.sum_le_sum fun k _ =>
            Nat.mul_le_mul_left _ (sum_Icc_choose_le h k j)
    have := ih j
    omega

/-- **Claim (ii)** (Chvátal Lemma 6.2): the number of distinct tops of monotone matrices
    with at most `j` ones is at most `Σ_k C(n,k) · C(j - h·k, k)`. -/
theorem tops_card_le (h n j : ℕ) :
    (tops h n j).card ≤ ∑ k ∈ Finset.range (n + 1), Nat.choose n k * Nat.choose (j - h * k) k :=
  (tops_card_le_topBound h n j).trans (topBound_le_topClosed h n j)

end Chvatal
