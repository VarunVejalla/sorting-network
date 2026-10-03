module

public import AKS.Separator.PatersonOdd
public import AKS.Bitonic.Defs

/-! # Wire reversal and order duality for odd Paterson blocks -/

@[expose] public section

namespace Paterson

def reverseDual {n : ℕ} {α : Type*} (w : Fin n → α) :
    Fin n → αᵒᵈ := fun i ↦ OrderDual.toDual (w i.rev)

private theorem flip_apply_reverseDual {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (w : Fin n → α) :
    (⟨c.j.rev, c.i.rev, Fin.rev_lt_rev.mpr c.h⟩ : Comparator n).apply
      (reverseDual w) = reverseDual (c.apply w) := by
  funext k
  by_cases hj : k = c.j.rev
  · subst k
    simp only [Comparator.apply, reverseDual]
    have hne : c.j ≠ c.i := ne_of_gt c.h
    simp [Fin.rev_rev, hne]
    exact min_comm _ _
  by_cases hi : k = c.i.rev
  · subst k
    simp only [Comparator.apply, reverseDual]
    simp [Fin.rev_rev, hj]
    exact max_comm _ _
  · simp only [Comparator.apply, reverseDual]
    have hki : k.rev ≠ c.i := by
      intro heq
      exact hi (by simpa using congrArg Fin.rev heq)
    have hkj : k.rev ≠ c.j := by
      intro heq
      exact hj (by simpa using congrArg Fin.rev heq)
    simp [hi, hj, hki, hkj]

/-- Reversing the wires while dualizing values commutes with network
execution. In particular, initial/left bounds can be reused as final/right
bounds after flipping the comparator network. -/
theorem flip_exec_reverseDual {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) (w : Fin n → α) :
    net.flip.exec (reverseDual w) = reverseDual (net.exec w) := by
  unfold ComparatorNetwork.flip ComparatorNetwork.exec
  induction net.comparators generalizing w with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [flip_apply_reverseDual c w]
    exact ih (c.apply w)

/-- Reverse positions and complement finite ranks. This is an involution. -/
def reverseFin {wires values : ℕ} (w : Fin wires → Fin values) :
    Fin wires → Fin values := fun i ↦ (w i.rev).rev

theorem reverseFin_reverseFin {wires values : ℕ}
    (w : Fin wires → Fin values) : reverseFin (reverseFin w) = w := by
  funext i
  simp [reverseFin]

theorem flip_exec_reverseFin {wires values : ℕ}
    (net : ComparatorNetwork wires) (w : Fin wires → Fin values) :
    net.flip.exec (reverseFin w) = reverseFin (net.exec w) := by
  let g : (Fin values)ᵒᵈ → Fin values := fun x ↦ (OrderDual.ofDual x).rev
  have hg : Monotone g := by
    intro x y hxy
    exact Fin.rev_le_rev.mpr hxy
  have hw : reverseFin w = g ∘ reverseDual w := by
    funext i
    rfl
  calc
    net.flip.exec (reverseFin w) = net.flip.exec (g ∘ reverseDual w) := by rw [hw]
    _ = g ∘ net.flip.exec (reverseDual w) :=
      ComparatorNetwork.exec_comp_mono _ hg _
    _ = g ∘ reverseDual (net.exec w) := by rw [flip_exec_reverseDual]
    _ = reverseFin (net.exec w) := rfl

private theorem reverseFin_initial_count_eq_final (m k : ℕ)
    (w : Fin (2 * m) → Fin (2 * m)) :
    (Finset.univ.filter (fun pos : Fin (2 * m) ↦
      m ≤ pos.val ∧ (reverseFin w pos).val < k)).card =
    (Finset.univ.filter (fun pos : Fin (2 * m) ↦
      pos.val < m ∧ 2 * m - k ≤ (w pos).val)).card := by
  apply Finset.card_nbij' Fin.rev Fin.rev
  · intro pos hpos
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
    rcases hpos with ⟨hpos, hval⟩
    simp only [reverseFin, Fin.val_rev] at hval ⊢
    constructor <;> omega
  · intro pos hpos
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
    rcases hpos with ⟨hpos, hval⟩
    simp only [reverseFin, Fin.rev_rev, Fin.val_rev] at hval ⊢
    constructor <;> omega
  · intro pos _; simp
  · intro pos _; simp

private theorem reverseFin_final_count_eq_initial (m k : ℕ)
    (w : Fin (2 * m) → Fin (2 * m)) :
    (Finset.univ.filter (fun pos : Fin (2 * m) ↦
      pos.val < m ∧ 2 * m - k ≤ (reverseFin w pos).val)).card =
    (Finset.univ.filter (fun pos : Fin (2 * m) ↦
      m ≤ pos.val ∧ (w pos).val < k)).card := by
  apply Finset.card_nbij' Fin.rev Fin.rev
  · intro pos hpos
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
    rcases hpos with ⟨hpos, hval⟩
    simp only [reverseFin, Fin.val_rev] at hval ⊢
    constructor <;> omega
  · intro pos hpos
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
    rcases hpos with ⟨hpos, hval⟩
    simp only [reverseFin, Fin.rev_rev, Fin.val_rev] at hval ⊢
    constructor <;> omega
  · intro pos _; simp
  · intro pos _; simp

/-- Flipping a two-sided restricted halver preserves both of its error
guarantees, exchanging the initial and final directions. -/
theorem flip_isEpsilonAlphaHalver {m : ℕ} {ε α : ℚ}
    {net : ComparatorNetwork (2 * m)}
    (hnet : IsEpsilonAlphaHalver net ε α) :
    IsEpsilonAlphaHalver net.flip ε α := by
  intro v
  let w : Equiv.Perm (Fin (2 * m)) :=
    (Fin.revPerm.trans v).trans Fin.revPerm
  have hw : (w : Fin (2 * m) → Fin (2 * m)) = reverseFin v := by
    funext i
    rfl
  have hflip : net.flip.exec v = reverseFin (net.exec w) := by
    have h := flip_exec_reverseFin net (w : Fin (2 * m) → Fin (2 * m))
    rw [hw, reverseFin_reverseFin] at h
    exact h
  obtain ⟨hinit, hfinal⟩ := hnet w
  constructor
  · intro k hk
    rw [hflip]
    rw [reverseFin_initial_count_eq_final]
    exact hfinal k hk
  · intro k hk
    rw [hflip]
    rw [reverseFin_final_count_eq_initial]
    exact hinit k hk

end Paterson
