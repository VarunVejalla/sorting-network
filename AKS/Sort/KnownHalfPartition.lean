module

public import AKS.Sort.ParallelExecution
public import AKS.Sort.SubsetPermutation
public import AKS.Halver.PatersonCorrectness
public import AKS.Paterson.RankCohorts

/-! One matching layer partitions a known rank permutation into its two halves.
The matching depends only on that fixed permutation, not on subsequent inputs. -/

@[expose] public section

open Finset

namespace Paterson

open Bags

theorem exists_known_half_partition (m : ℕ) (w : Fin (2 * m) → Fin (2 * m))
    (hw : Function.Injective w) :
    ∃ net : ComparatorNetwork (2 * m), net.depth ≤ 1 ∧
      (∀ i : Fin m, (net.exec w ⟨i.val, by omega⟩).val < m) ∧
      (∀ i : Fin m, m ≤ (net.exec w ⟨m + i.val, by omega⟩).val) := by
  classical
  let L : Fin m → Fin (2 * m) := fun i ↦ ⟨i.val, by omega⟩
  let R : Fin m → Fin (2 * m) := fun i ↦ ⟨m + i.val, by omega⟩
  let bad := univ.filter (fun i : Fin m ↦ ¬(w (L i)).val < m)
  let low := univ.filter (fun i : Fin m ↦ (w (R i)).val < m)
  have ht : (univ.filter (fun i ↦ (w i).val < m)).card = m := by
    rw [bijection_count_val_lt w hw, card_filter_val_lt _ _ (by omega)]
  have hs := card_filter_fin_double (fun i ↦ (w i).val < m)
  have hc := card_filter_add_card_filter_not (fun i : Fin m ↦ (w (L i)).val < m)
    (s := univ)
  have he : bad.card = low.card := by
    rw [ht] at hs
    simp only [card_univ, Fintype.card_fin] at hc
    change _ + bad.card = m at hc
    change m = (univ.filter (fun i : Fin m ↦ (w (L i)).val < m)).card + low.card at hs
    omega
  obtain ⟨g, hg⟩ := exists_perm_subset_transport bad low he
  have hclass (i : Fin m) : ¬(w (L i)).val < m ↔ (w (R (g i))).val < m := by
    simpa only [bad, low, mem_filter, mem_univ, true_and] using hg i
  let net := patersonMatchingLayer g
  have hex (i : Fin m) :
      net.exec w (L i) = min (w (L i)) (w (R (g i))) ∧
      net.exec w (R (g i)) = max (w (L i)) (w (R (g i))) := by
    exact parallel_layer_exec_endpoints _ (patersonMatchingLayer_parallel g)
      (patersonMatchingComparator g i) (List.mem_ofFn.mpr ⟨i, rfl⟩) w
  refine ⟨net, ?_, ?_, ?_⟩
  · apply le_trans (depth_le_of_decomposition net [net.comparators] ?_) (by simp)
    exact ⟨by simpa using patersonMatchingLayer_parallel g, by simp⟩
  · intro i
    rw [(hex i).1]
    by_cases hi : (w (L i)).val < m
    · exact lt_of_le_of_lt (Fin.le_def.mp (min_le_left _ _)) hi
    · exact lt_of_le_of_lt (Fin.le_def.mp (min_le_right _ _)) ((hclass i).mp hi)
  · intro j
    have hx := (hex (g.symm j)).2
    simp only [g.apply_symm_apply] at hx
    rw [hx]
    by_cases hi : (w (L (g.symm j))).val < m
    · have hr : m ≤ (w (R j)).val := by
        have hn : ¬(w (R (g (g.symm j)))).val < m := fun h ↦ ((hclass _).mpr h) hi
        simpa only [g.apply_symm_apply, not_lt] using hn
      exact le_trans hr (Fin.le_def.mp (le_max_right _ _))
    · exact le_trans (Nat.le_of_not_lt hi) (Fin.le_def.mp (le_max_left _ _))

end Paterson
