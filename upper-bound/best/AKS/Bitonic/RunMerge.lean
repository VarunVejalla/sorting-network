module
/-
  # Merging sorted runs: the bitonic sorter started at run length `2^l` (UB-39)

  `runMerge l k` on `2^(l+k)` wires is `bitonicSort` with its first `l` levels removed: the base case
  `k = 0` is the empty network, because the input already consists of sorted aligned runs of length
  `2^l`. Then
  - `runMerge l (k+1) = par (runMerge l k) (runMerge l k) ; layer revPerm ; par (bitonicMerge _) (bitonicMerge _)`,
  - depth `≤ (l+1) + ⋯ + (l+k) = bitonicDepthBudget (l+k) - bitonicDepthBudget l`,
  - it sorts every input whose aligned blocks of length `2^l` are sorted (`RunSorted`), for any
    linear order (a 0-1 principle restricted to run-sorted inputs).
-/

public import AKS.Bitonic.Sorts
public import AKS.Bitonic.Shrink

@[expose] public section

open ComparatorNetwork

namespace Bitonic

/-- Every aligned block `[b 2^l, (b+1) 2^l)` of `v` is sorted. -/
def RunSorted (l : ℕ) {m : ℕ} {α : Type*} [Preorder α] (v : Fin m → α) : Prop :=
  ∀ i j : Fin m, i ≤ j → i.val / 2 ^ l = j.val / 2 ^ l → v i ≤ v j

/-- Merge tree from sorted runs of length `2^l` up to `2^(l+k)` wires. -/
def runMerge (l : ℕ) : (k : ℕ) → ComparatorNetwork (2 ^ (l + k))
  | 0 => ⟨[]⟩
  | k + 1 => (par (two_pow_succ' (l + k)) (runMerge l k) (runMerge l k)).append
      ((layer (two_pow_succ' (l + k)) Fin.revPerm).append
        (par (two_pow_succ' (l + k)) (bitonicMerge (l + k)) (bitonicMerge (l + k))))

theorem runMerge_depth_le (l : ℕ) :
    ∀ k, (runMerge l k).depth + bitonicDepthBudget l ≤ bitonicDepthBudget (l + k)
  | 0 => by simp [runMerge, depth_nil]
  | k + 1 => by
    have h1 := depth_par (two_pow_succ' (l + k)) (runMerge l k) (runMerge l k) _ le_rfl le_rfl
    have h2 := layer_depth_le (two_pow_succ' (l + k)) Fin.revPerm
    have h3 := depth_par (two_pow_succ' (l + k)) (bitonicMerge (l + k)) (bitonicMerge (l + k))
      (l + k) (bitonicMerge_depth_le _) (bitonicMerge_depth_le _)
    have h4 := depth_append_le (par (two_pow_succ' (l + k)) (runMerge l k) (runMerge l k))
      ((layer (two_pow_succ' (l + k)) Fin.revPerm).append
        (par (two_pow_succ' (l + k)) (bitonicMerge (l + k)) (bitonicMerge (l + k))))
    have h5 := depth_append_le (layer (two_pow_succ' (l + k)) Fin.revPerm)
      (par (two_pow_succ' (l + k)) (bitonicMerge (l + k)) (bitonicMerge (l + k)))
    have ih := runMerge_depth_le l k
    show (runMerge l (k + 1)).depth + bitonicDepthBudget l ≤ bitonicDepthBudget (l + k) + (l + k + 1)
    simp only [runMerge]
    omega

/-- The halves of a run-sorted vector on `2^(l+k) + 2^(l+k)` wires are run-sorted. -/
theorem runSorted_halves {l k n : ℕ} {α : Type*} [Preorder α] (hn : 2 ^ (l + k) + 2 ^ (l + k) = n)
    (v : Fin n → α) (hv : RunSorted l v) :
    RunSorted l (lowH hn v) ∧ RunSorted l (upH hn v) := by
  have hdvd : 2 ^ l ∣ 2 ^ (l + k) := pow_dvd_pow 2 (Nat.le_add_right l k)
  obtain ⟨c, hc⟩ := hdvd
  have hpos : 0 < 2 ^ l := by positivity
  have key : ∀ a : ℕ, (2 ^ (l + k) + a) / 2 ^ l = c + a / 2 ^ l := fun a => by
    rw [hc]; exact Nat.mul_add_div hpos c a
  refine ⟨fun i j hij hb => hv _ _ hij hb, fun i j hij hb => hv _ _ ?_ ?_⟩
  · show 2 ^ (l + k) + i.val ≤ 2 ^ (l + k) + j.val
    have : i.val ≤ j.val := hij
    omega
  · show (2 ^ (l + k) + i.val) / 2 ^ l = (2 ^ (l + k) + j.val) / 2 ^ l
    have hb' : i.val / 2 ^ l = j.val / 2 ^ l := hb
    rw [key, key, hb']

theorem runMerge_sorts_bool (l : ℕ) : ∀ (k : ℕ) (v : Fin (2 ^ (l + k)) → Bool),
    RunSorted l v → Monotone ((runMerge l k).exec v)
  | 0, v, hv => by
    show Monotone ((⟨[]⟩ : ComparatorNetwork (2 ^ (l + 0))).exec v)
    have he : (⟨[]⟩ : ComparatorNetwork (2 ^ (l + 0))).exec v = v := rfl
    rw [he]
    intro i j hij
    apply hv i j hij
    have hi := i.2; have hj := j.2
    simp only [Nat.add_zero] at hi hj
    rw [Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hj]
  | k + 1, v, hv => by
    have hn := two_pow_succ' (l + k)
    obtain ⟨s0, s1⟩ := runSorted_halves (k := k) hn v hv
    obtain ⟨q1, q2⟩ := par_exec hn (runMerge l k) (runMerge l k) v
    obtain ⟨hl, hu, hord⟩ := cross_props hn _ (by rw [q1]; exact runMerge_sorts_bool l k _ s0)
      (by rw [q2]; exact runMerge_sorts_bool l k _ s1)
    obtain ⟨r1, r2⟩ := par_exec hn (bitonicMerge (l + k)) (bitonicMerge (l + k))
      ((layer hn Fin.revPerm).exec ((par hn (runMerge l k) (runMerge l k)).exec v))
    rw [show (runMerge l (k + 1)).exec v = (par hn (bitonicMerge (l + k)) (bitonicMerge (l + k))).exec
      ((layer hn Fin.revPerm).exec ((par hn (runMerge l k) (runMerge l k)).exec v)) from
      (exec_append _ _ v).trans (exec_append _ _ _)]
    refine glue hn _ (by rw [r1]; exact bitonicMerge_sorts _ _ hl)
      (by rw [r2]; exact bitonicMerge_sorts _ _ hu) ?_
    rcases hord with h | h
    · left; rw [r1, h]; exact ((bitonicMerge (l + k)).exec_eq_of_monotone monotone_const)
    · right; rw [r2, h]; exact ((bitonicMerge (l + k)).exec_eq_of_monotone monotone_const)

/-- **Run merge sorts run-sorted inputs** (any linear order; the 0-1 argument restricted to run-sorted
inputs, since a monotone threshold of a run-sorted vector is run-sorted). -/
theorem runMerge_sorts (l k : ℕ) {α : Type*} [LinearOrder α] (v : Fin (2 ^ (l + k)) → α)
    (hv : RunSorted l v) : Monotone ((runMerge l k).exec v) := by
  by_contra h_not_mono
  simp only [Monotone, not_forall, not_le] at h_not_mono
  obtain ⟨i, j, hij, hlt⟩ := h_not_mono
  have hf : Monotone fun x : α ↦ decide (((runMerge l k).exec v) j < x) := fun a b hab ↦ by
    by_cases ha : ((runMerge l k).exec v) j < a
    · simp [ha, lt_of_lt_of_le ha hab]
    · simp [ha]
  have hb : RunSorted l ((fun x : α ↦ decide (((runMerge l k).exec v) j < x)) ∘ v) :=
    fun a b hab hblk => hf (hv a b hab hblk)
  have h_sorted := runMerge_sorts_bool l k _ hb hij
  have hcomm := congr_fun ((runMerge l k).exec_comp_monotone hf v)
  simp only [Function.comp] at hcomm
  rw [← hcomm i, ← hcomm j] at h_sorted
  simp [hlt] at h_sorted
  exact absurd h_sorted (by decide)

/-- Run merge on any number `m` of wires: `runMerge l k` on `2^(l+k) ≥ m` wires, restricted to `m`
(extra wires padded with `true`, which keeps every aligned block sorted). -/
def runMergeNetwork (l m : ℕ) : ComparatorNetwork m :=
  (runMerge l (Nat.clog 2 m - l)).restrictWires m
    ((Nat.le_pow_clog (by omega) m).trans (Nat.pow_le_pow_right (by omega) (by omega)))

theorem runMergeNetwork_depth_le (l m : ℕ) :
    (runMergeNetwork l m).depth + bitonicDepthBudget l ≤ bitonicDepthBudget (l + (Nat.clog 2 m - l)) :=
  (Nat.add_le_add_right (restrictWires_depth_le _ _ _) _).trans (runMerge_depth_le l _)

theorem runMergeNetwork_sorts_bool (l m : ℕ) (v : Fin m → Bool) (hv : RunSorted l v) :
    Monotone ((runMergeNetwork l m).exec v) := by
  intro i j hij
  unfold runMergeNetwork
  rw [restrictWires_exec_pad, restrictWires_exec_pad]
  refine runMerge_sorts_bool l _ _ ?_ (show (⟨i.val, _⟩ : Fin _) ≤ ⟨j.val, _⟩ from hij)
  intro a b hab hblk
  have hab' : a.val ≤ b.val := hab
  by_cases hb : b.val < m
  · have ha : a.val < m := lt_of_le_of_lt hab' hb
    simp only [ha, hb, dite_true]
    exact hv ⟨a.val, ha⟩ ⟨b.val, hb⟩ hab hblk
  · simp only [hb, dite_false]
    exact Bool.le_true _

/-- **Run merge sorts run-sorted inputs on any number of wires** (any linear order). -/
theorem runMergeNetwork_sorts (l m : ℕ) {α : Type*} [LinearOrder α] (v : Fin m → α)
    (hv : RunSorted l v) : Monotone ((runMergeNetwork l m).exec v) := by
  by_contra h_not_mono
  simp only [Monotone, not_forall, not_le] at h_not_mono
  obtain ⟨i, j, hij, hlt⟩ := h_not_mono
  have hf : Monotone fun x : α ↦ decide (((runMergeNetwork l m).exec v) j < x) := fun a b hab ↦ by
    by_cases ha : ((runMergeNetwork l m).exec v) j < a
    · simp [ha, lt_of_lt_of_le ha hab]
    · simp [ha]
  have hb : RunSorted l ((fun x : α ↦ decide (((runMergeNetwork l m).exec v) j < x)) ∘ v) :=
    fun a b hab hblk => hf (hv a b hab hblk)
  have h_sorted := runMergeNetwork_sorts_bool l m _ hb hij
  have hcomm := congr_fun ((runMergeNetwork l m).exec_comp_monotone hf v)
  simp only [Function.comp] at hcomm
  rw [← hcomm i, ← hcomm j] at h_sorted
  simp [hlt] at h_sorted
  exact absurd h_sorted (by decide)

end Bitonic

end
