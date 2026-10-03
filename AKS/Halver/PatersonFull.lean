module

public import AKS.Halver.PatersonTail
public import AKS.Bags.PatersonNumerics

/-! # Full-support Paterson halvers for the Seiferas scheduler -/

@[expose] public section

namespace Paterson

theorem full_support_isHalver {m : ℕ} {ε : ℚ} {net : ComparatorNetwork (2 * m)}
    (h : IsEpsilonAlphaHalver net ε 1) : IsEpsilonHalver net ε := by
  intro v
  obtain ⟨hl, hr⟩ := h v
  let w : Fin (2 * m) → Fin (2 * m) := net.exec (v : Fin (2 * m) → Fin (2 * m))
  change EpsilonHalved w ε
  constructor
  · intro k hk
    simp only [Fintype.card_fin, rank_fin_val, show 2 * m / 2 = m by omega] at hk ⊢
    exact hl k (by norm_num; exact_mod_cast hk)
  · intro k hk
    simp only [Fintype.card_orderDual, Fintype.card_fin,
      show 2 * m / 2 = m by omega] at hk ⊢
    have hb := hr k (by norm_num; exact_mod_cast hk)
    have heq :
        (Finset.univ.filter (fun pos : (Fin (2 * m))ᵒᵈ ↦
          m ≤ @rank (Fin (2 * m))ᵒᵈ (OrderDual.fintype _) (OrderDual.instLinearOrder _) pos ∧
            @rank (Fin (2 * m))ᵒᵈ (OrderDual.fintype _) (OrderDual.instLinearOrder _)
              (w pos) < k)).card =
        (Finset.univ.filter (fun pos : Fin (2 * m) ↦
          pos.val < m ∧ 2 * m - k ≤ (w pos).val)).card := by
      apply Finset.card_nbij'
        (fun x : (Fin (2 * m))ᵒᵈ ↦ OrderDual.ofDual x)
        (fun x : Fin (2 * m) ↦ OrderDual.toDual x)
      · intro pos hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
          true_and, rank_fin_od] at hp ⊢
        change pos.val < m ∧ 2 * m - k ≤ (w pos).val
        have hi := pos.isLt
        have hv := (w pos).isLt
        constructor <;> omega
      · intro pos hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
          true_and, rank_fin_od] at hp ⊢
        change m ≤ 2 * m - 1 - pos.val ∧ 2 * m - 1 - (w pos).val < k
        have hi := pos.isLt
        have hv := (w pos).isLt
        constructor <;> omega
      · intro _ _; rfl
      · intro _ _; rfl
    rw [heq]
    exact hb

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
theorem full_depth_bound : patersonHalverDepthBound 1 (89 / 35000) ≤ 5490 := by
  unfold patersonHalverDepthBound
  apply entropy_depth_le _ _ 5490 8 0 0 8
  all_goals norm_num [logLower, logUpper, logApprox, logError, Finset.sum_range_succ]

theorem exists_full_halver (m : ℕ) :
    ∃ net : ComparatorNetwork (2 * m),
      IsEpsilonHalver net (89 / 35000 : ℚ) ∧ net.depth ≤ 5490 := by
  obtain ⟨net, hn, hd⟩ := exists_paterson_halver_all_arities (m := m)
    (a := 1) (e := 89 / 35000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨net, full_support_isHalver hn, hd.trans ?_⟩
  exact (Nat.ceil_le).mpr (by exact_mod_cast full_depth_bound)

noncomputable def fullFamily : HalverFamily (89 / 35000) where
  depth := 5490
  net m := Classical.choose (exists_full_halver m)
  isHalver m := (Classical.choose_spec (exists_full_halver m)).1
  depth_le m := (Classical.choose_spec (exists_full_halver m)).2

end Paterson
