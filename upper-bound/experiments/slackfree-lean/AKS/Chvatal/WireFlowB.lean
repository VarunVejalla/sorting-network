module

public import AKS.Chvatal.WireFlow
public import AKS.Chvatal.FlowTableB

@[expose] public section

/-! # Generalized `downSet` (Stage 1b, first item)

Child `j` of a node holding `s` takes the ranks `[π/2 + off j, π/2 + off (j+1))` of `s`, where
`off j = Σ_{i<j} τ_i` is a monotone prefix-sum function.  With `off j = j * τ` this is the
current `WireFlow.downSet` (`downSetB_uniform`).  `downSetB_card`, `disjoint_downSetB`,
`disjoint_upSet_downSetB` and `cover_B` are the analogues of `downSet_card`, `disjoint_downSet`,
`disjoint_upSet_downSet`, `cover` of `WireFlow`.  The `FlowTableB` offsets `F.off t b` satisfy the
hypotheses (`FlowTableB.off_mono`, `off_zero`, `off_succ`, `off_sixtyfour`). -/

namespace Chvatal

open Finset

section Blocks

variable {n : ℕ} {s : Finset (Fin n)} {w : Fin n} {π j j' : ℕ} {off : ℕ → ℕ}

/-- The `j`-th middle block, with cumulative boundaries `π/2 + off j`. -/
def downSetB (s : Finset (Fin n)) (π : ℕ) (off : ℕ → ℕ) (j : ℕ) : Finset (Fin n) :=
  blockOf s (π / 2 + off j) (π / 2 + off (j + 1))

theorem downSetB_subset : downSetB s π off j ⊆ s := blockOf_subset

/-- Equal blocks recover `WireFlow.downSet`. -/
theorem downSetB_uniform (τ : ℕ) : downSetB s π (fun i => i * τ) j = downSet s π τ j := rfl

theorem mem_downSetB : w ∈ downSetB s π off j ↔
    w ∈ s ∧ π / 2 + off j ≤ rankIn s w ∧ rankIn s w < π / 2 + off (j + 1) := mem_blockOf

theorem downSetB_card (hmono : Monotone off) (hs : s.card = π + off 64) (hj : j < 64) :
    (downSetB s π off j).card = off (j + 1) - off j := by
  have h1 : off (j + 1) ≤ off 64 := hmono (by omega)
  unfold downSetB
  rw [blockOf_card (by omega)]
  omega

theorem disjoint_downSetB (hmono : Monotone off) (hj : j < j') :
    Disjoint (downSetB s π off j) (downSetB s π off j') := by
  have : off (j + 1) ≤ off j' := hmono (by omega)
  exact disjoint_blockOf (by omega)

theorem disjoint_upSet_downSetB (hmono : Monotone off) (hs : s.card = π + off 64) (hπ : 2 ∣ π)
    (hj : j < 64) : Disjoint (upSet s π) (downSetB s π off j) := by
  have h1 : off (j + 1) ≤ off 64 := hmono (by omega)
  unfold upSet downSetB
  rw [Finset.disjoint_union_left]
  exact ⟨disjoint_blockOf (by omega), (disjoint_blockOf (by omega)).symm⟩

/-- Every wire is in the fringe or in exactly one (hence some) middle block. -/
theorem cover_B (hoff0 : off 0 = 0) (hs : s.card = π + off 64)
    (hπ : 2 ∣ π) (hw : w ∈ s) :
    w ∈ upSet s π ∨ ∃ j, j < 64 ∧ w ∈ downSetB s π off j := by
  have hr := rankIn_lt_card hw
  unfold upSet
  by_cases h1 : rankIn s w < π / 2
  · exact .inl (Finset.mem_union_left _ (mem_blockOf.2 ⟨hw, by omega, h1⟩))
  by_cases h3 : s.card - π / 2 ≤ rankIn s w
  · exact .inl (Finset.mem_union_right _ (mem_blockOf.2 ⟨hw, h3, hr⟩))
  right
  have e64 : off (63 + 1) = off 64 := rfl
  have hex : ∃ k, rankIn s w - π / 2 < off (k + 1) := ⟨63, by omega⟩
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ 63 := Nat.find_min' hex (by omega)
  have hlo : off (Nat.find hex) ≤ rankIn s w - π / 2 := by
    by_cases h0 : Nat.find hex = 0
    · rw [h0, hoff0]; exact Nat.zero_le _
    · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
      omega
  exact ⟨Nat.find hex, by omega, mem_blockOf.2 ⟨hw, by omega, by omega⟩⟩

end Blocks

namespace FlowTableB

variable {d tf : ℕ} (F : FlowTableB d tf) (t : ℕ) (b : KBag 64 d)

theorem off_zero : F.off t b 0 = 0 := by simp [off]

theorem off_mono : Monotone (F.off t b) := by
  intro j j' hjj
  unfold off
  apply Finset.sum_le_sum_of_subset
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

theorem off_sixtyfour : F.off t b 64 = ∑ j, F.down t b j := by
  unfold off
  rw [Finset.filter_true_of_mem (fun i _ => i.isLt)]

theorem off_succ {j : ℕ} (hj : j < 64) : F.off t b (j + 1) = F.off t b j + F.down t b ⟨j, hj⟩ := by
  unfold off
  have : (Finset.univ.filter (fun i : Fin 64 => i.val < j + 1)) =
      insert ⟨j, hj⟩ (Finset.univ.filter (fun i : Fin 64 => i.val < j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp), add_comm]

/-- Block sizes of the generalized `downSet` for a table: child `j` gets exactly `down t b j`. -/
theorem card_downSetB {n : ℕ} {s : Finset (Fin n)}
    (hs : s.card = F.up t b + ∑ j, F.down t b j) {j : ℕ} (hj : j < 64) :
    (downSetB s (F.up t b) (F.off t b) j).card = F.down t b ⟨j, hj⟩ := by
  rw [downSetB_card (F.off_mono t b) (by rw [F.off_sixtyfour]; exact hs) hj, F.off_succ t b hj]
  omega

end FlowTableB

end Chvatal
