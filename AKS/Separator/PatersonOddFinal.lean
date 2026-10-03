module

public import AKS.Separator.PatersonFlip
public import AKS.Bitonic.Depth

/-! # Odd restricted halvers via a virtual minimum -/

@[expose] public section

namespace Paterson

/-- Mirror the virtual-maximum construction. The missing first wire acts as
a virtual minimum, leaving `2*m-1` real wires. -/
def oddFinalHalver {m : ℕ} (net : ComparatorNetwork (2 * m))
    (hm : 0 < m) : ComparatorNetwork (2 * m - 1) :=
  (oddInitialHalver net.flip hm).flip

theorem oddFinalHalver_depth_le {m : ℕ} (net : ComparatorNetwork (2 * m))
    (hm : 0 < m) : (oddFinalHalver net hm).depth ≤ net.depth := by
  exact (flip_depth_le (oddInitialHalver net.flip hm)).trans
    ((oddInitialHalver_depth_le net.flip hm).trans (flip_depth_le net))

private theorem odd_reverseFin_input_count (m n k : ℕ)
    (u : Fin (2 * m - 1) → Fin n) :
    (Finset.univ.filter (fun i : Fin (2 * m - 1) ↦
      (reverseFin u i).val < k)).card =
    (Finset.univ.filter (fun i : Fin (2 * m - 1) ↦
      n - k ≤ (u i).val)).card := by
  apply Finset.card_nbij' Fin.rev Fin.rev
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simp only [reverseFin, Fin.val_rev] at hi
    have := (u i.rev).isLt
    omega
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simp only [reverseFin, Fin.rev_rev, Fin.val_rev]
    have := (u i).isLt
    omega
  · intro i _; simp
  · intro i _; simp

private theorem odd_reverseFin_output_count (m n k : ℕ) (hm : 0 < m)
    (w : Fin (2 * m - 1) → Fin n) :
    (Finset.univ.filter (fun pos : Fin (2 * m - 1) ↦
      pos.val < m - 1 ∧ n - k ≤ (reverseFin w pos).val)).card =
    (Finset.univ.filter (fun pos : Fin (2 * m - 1) ↦
      m ≤ pos.val ∧ (w pos).val < k)).card := by
  apply Finset.card_nbij' Fin.rev Fin.rev
  · intro pos hpos
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
    rcases hpos with ⟨hpos, hval⟩
    simp only [reverseFin, Fin.val_rev] at hval ⊢
    have := pos.isLt
    have := (w pos.rev).isLt
    constructor <;> omega
  · intro pos hpos
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
    rcases hpos with ⟨hpos, hval⟩
    simp only [reverseFin, Fin.rev_rev, Fin.val_rev] at hval ⊢
    have := pos.isLt
    have := (w pos).isLt
    constructor <;> omega
  · intro pos _; simp
  · intro pos _; simp

/-- The right-side counterpart of `oddInitialHalver_injective`: a virtual
minimum yields the final-cohort estimate without an additive error. -/
theorem oddFinalHalver_injective {m n : ℕ} {ε α : ℚ}
    (hm : 0 < m) {net : ComparatorNetwork (2 * m)}
    (hnet : IsEpsilonAlphaHalver net ε α)
    (u : Fin (2 * m - 1) → Fin n) (hu : Function.Injective u)
    (k : ℕ) (hk_n : k ≤ n)
    (hk : ((Finset.univ.filter (fun i : Fin (2 * m - 1) ↦
        n - k ≤ (u i).val)).card : ℝ) ≤ (α : ℝ) * m) :
    ((Finset.univ.filter (fun pos : Fin (2 * m - 1) ↦
        pos.val < m - 1 ∧ n - k ≤ ((oddFinalHalver net hm).exec u pos).val)).card : ℝ) ≤
      (ε : ℝ) * ↑(Finset.univ.filter (fun i : Fin (2 * m - 1) ↦
        n - k ≤ (u i).val)).card := by
  let uRev := reverseFin u
  have huRev : Function.Injective uRev := by
    intro i j hij
    have hval : u i.rev = u j.rev := Fin.rev_injective hij
    exact Fin.rev_injective (hu hval)
  have hinput := odd_reverseFin_input_count m n k u
  have hlocal := oddInitialHalver_injective hm
    (flip_isEpsilonAlphaHalver hnet) uRev huRev k hk_n (by
      simpa only [uRev, hinput] using hk)
  have hexec : (oddFinalHalver net hm).exec u =
      reverseFin ((oddInitialHalver net.flip hm).exec uRev) := by
    have h := flip_exec_reverseFin (oddInitialHalver net.flip hm) uRev
    rw [show reverseFin uRev = u by simp [uRev, reverseFin_reverseFin]] at h
    exact h
  rw [hexec]
  rw [odd_reverseFin_output_count m n k hm]
  rw [← hinput]
  exact hlocal

/-- The selected stage network with a virtual minimum on an odd right-side
block. -/
noncomputable def oddStageFinal (level m : ℕ) (hm : 0 < m) :
    ComparatorNetwork (2 * m - 1) :=
  oddFinalHalver (stageNetwork level m) hm

theorem oddStageFinal_depth_le (level m : ℕ) (hm : 0 < m) :
    (oddStageFinal level m hm).depth ≤ stageDepth level :=
  (oddFinalHalver_depth_le (stageNetwork level m) hm).trans
    (stageNetwork_depth_le level m)

theorem oddStageFinal_bound (level m n : ℕ) (hm : 0 < m)
    (hle : level < 5)
    (u : Fin (2 * m - 1) → Fin n) (hu : Function.Injective u)
    (k : ℕ) (hk_n : k ≤ n)
    (hk : ((Finset.univ.filter (fun i : Fin (2 * m - 1) ↦
        n - k ≤ (u i).val)).card : ℝ) ≤ (stageAlpha level : ℝ) * m) :
    ((Finset.univ.filter (fun pos : Fin (2 * m - 1) ↦
        pos.val < m - 1 ∧ n - k ≤ ((oddStageFinal level m hm).exec u pos).val)).card : ℝ) ≤
      (stageErrorQ level : ℝ) *
        ↑(Finset.univ.filter (fun i : Fin (2 * m - 1) ↦
          n - k ≤ (u i).val)).card :=
  oddFinalHalver_injective hm (stageNetwork_halver level m hle)
    u hu k hk_n hk

end Paterson
