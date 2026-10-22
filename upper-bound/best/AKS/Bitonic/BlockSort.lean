module
/-
  # Disjoint block sorts (band repair, UB-32)

  `blockSort b k` on `2^(b+k)` wires sorts every aligned block `[j 2^b, (j+1) 2^b)` independently: it is
  `2^k` copies of `bitonicSort b` side by side. Depth `≤ bitonicDepthBudget b`. Its output is
  `RunSorted b` for every input (any linear order). `blockSortNetwork b m` restricts it to `m` wires.
  This is the band repair of `experiments/sub500-screen/PROOFS-L3-L4.md` (L3 step 4: disjoint bands).
-/

public import AKS.Bitonic.RunMerge

@[expose] public section

open ComparatorNetwork

namespace Bitonic

/-- `2^k` independent bitonic sorts of the aligned `2^b` blocks of `2^(b+k)` wires. -/
def blockSort (b : ℕ) : (k : ℕ) → ComparatorNetwork (2 ^ (b + k))
  | 0 => bitonicSort b
  | k + 1 => par (two_pow_succ' (b + k)) (blockSort b k) (blockSort b k)

theorem blockSort_depth_le (b : ℕ) : ∀ k, (blockSort b k).depth ≤ bitonicDepthBudget b
  | 0 => bitonicSort_depth_le_budget b
  | k + 1 => depth_par (two_pow_succ' (b + k)) _ _ _ (blockSort_depth_le b k) (blockSort_depth_le b k)

/-- Two run-sorted halves (aligned at a multiple of `2^b`) make a run-sorted whole. -/
theorem runSorted_of_halves {b k n : ℕ} {α : Type*} [Preorder α] (hn : 2 ^ (b + k) + 2 ^ (b + k) = n)
    (v : Fin n → α) (h0 : RunSorted b (lowH hn v)) (h1 : RunSorted b (upH hn v)) : RunSorted b v := by
  obtain ⟨c, hc⟩ : 2 ^ b ∣ 2 ^ (b + k) := pow_dvd_pow 2 (Nat.le_add_right b k)
  have hpos : 0 < 2 ^ b := by positivity
  have key : ∀ x : ℕ, (2 ^ (b + k) + x) / 2 ^ b = c + x / 2 ^ b := fun x => by
    rw [hc]; exact Nat.mul_add_div hpos c x
  have hN : 2 ^ (b + k) / 2 ^ b = c := by rw [hc, Nat.mul_div_cancel_left _ hpos]
  intro i j hij hblk
  have hij' : i.val ≤ j.val := hij
  have hi := i.2; have hj := j.2
  by_cases hiN : i.val < 2 ^ (b + k)
  · by_cases hjN : j.val < 2 ^ (b + k)
    · exact h0 ⟨i.val, hiN⟩ ⟨j.val, hjN⟩ hij hblk
    · -- i in the low half, j in the high half: same block is impossible
      exfalso
      have h1' : i.val / 2 ^ b < c := by
        rw [← hN]; exact Nat.div_lt_div_of_lt_of_dvd ⟨c, hc⟩ hiN
      have h2' : c ≤ j.val / 2 ^ b := by
        rw [← hN]; exact Nat.div_le_div_right (by omega)
      have hb' : i.val / 2 ^ b = j.val / 2 ^ b := hblk
      omega
  · have hjN : ¬ j.val < 2 ^ (b + k) := by omega
    have e1 := h1 ⟨i.val - 2 ^ (b + k), by omega⟩ ⟨j.val - 2 ^ (b + k), by omega⟩
      (show (⟨i.val - 2 ^ (b + k), _⟩ : Fin _) ≤ ⟨j.val - 2 ^ (b + k), _⟩ from Fin.mk_le_mk.2 (by omega))
      (by
        have hb' : i.val / 2 ^ b = j.val / 2 ^ b := hblk
        have ki := key (i.val - 2 ^ (b + k)); have kj := key (j.val - 2 ^ (b + k))
        rw [show 2 ^ (b + k) + (i.val - 2 ^ (b + k)) = i.val by omega] at ki
        rw [show 2 ^ (b + k) + (j.val - 2 ^ (b + k)) = j.val by omega] at kj
        show (i.val - 2 ^ (b + k)) / 2 ^ b = (j.val - 2 ^ (b + k)) / 2 ^ b
        omega)
    have ei : (⟨2 ^ (b + k) + (i.val - 2 ^ (b + k)), by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
    have ej : (⟨2 ^ (b + k) + (j.val - 2 ^ (b + k)), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
    simpa [upH, ei, ej] using e1

/-- **Disjoint block sorts make every aligned `2^b` block sorted**, for every input. -/
theorem blockSort_runSorted (b : ℕ) {α : Type*} [LinearOrder α] :
    ∀ (k : ℕ) (v : Fin (2 ^ (b + k)) → α), RunSorted b ((blockSort b k).exec v)
  | 0, v => fun i j hij _ => (bitonicSort_sorts b) α v hij
  | k + 1, v => by
    have hn := two_pow_succ' (b + k)
    obtain ⟨p1, p2⟩ := par_exec hn (blockSort b k) (blockSort b k) v
    show RunSorted b ((par hn (blockSort b k) (blockSort b k)).exec v)
    exact runSorted_of_halves (k := k) hn _ (by rw [p1]; exact blockSort_runSorted b k _)
      (by rw [p2]; exact blockSort_runSorted b k _)

/-- Disjoint block sorts on any number `m` of wires (padding with `true` keeps blocks sorted). -/
def blockSortNetwork (b m : ℕ) : ComparatorNetwork m :=
  (blockSort b (Nat.clog 2 m - b)).restrictWires m
    ((Nat.le_pow_clog (by omega) m).trans (Nat.pow_le_pow_right (by omega) (by omega)))

theorem blockSortNetwork_depth_le (b m : ℕ) : (blockSortNetwork b m).depth ≤ bitonicDepthBudget b :=
  (restrictWires_depth_le _ _ _).trans (blockSort_depth_le b _)

theorem blockSortNetwork_runSorted_bool (b m : ℕ) (v : Fin m → Bool) :
    RunSorted b ((blockSortNetwork b m).exec v) := by
  intro i j hij hblk
  unfold blockSortNetwork
  rw [restrictWires_exec_pad, restrictWires_exec_pad]
  exact blockSort_runSorted b _ _ _ _ (show (⟨i.val, _⟩ : Fin _) ≤ ⟨j.val, _⟩ from hij) hblk

/-- **Every aligned `2^b` block of the output is sorted**, any linear order. -/
theorem blockSortNetwork_runSorted (b m : ℕ) {α : Type*} [LinearOrder α] (v : Fin m → α) :
    RunSorted b ((blockSortNetwork b m).exec v) := by
  intro i j hij hblk
  by_contra hlt
  push_neg at hlt
  have hf : Monotone fun x : α ↦ decide (((blockSortNetwork b m).exec v) j < x) := fun a c hac ↦ by
    by_cases ha : ((blockSortNetwork b m).exec v) j < a
    · simp [ha, lt_of_lt_of_le ha hac]
    · simp [ha]
  have h_sorted := blockSortNetwork_runSorted_bool b m
    ((fun x : α ↦ decide (((blockSortNetwork b m).exec v) j < x)) ∘ v) i j hij hblk
  have hcomm := congr_fun ((blockSortNetwork b m).exec_comp_monotone hf v)
  simp only [Function.comp] at hcomm
  rw [← hcomm i, ← hcomm j] at h_sorted
  simp [hlt] at h_sorted
  exact absurd h_sorted (by decide)

end Bitonic

end
