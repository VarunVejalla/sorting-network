module

public import AKS.Paterson.SortedBins

/-! # A sorted injective rank input has the unique identity output -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem monotone_injective_rank_identity {n : ℕ} (w : Fin n → Fin n)
    (hm : Monotone w) (hi : Function.Injective w) : w = id := by
  funext i
  have hcount (q : ℕ) (hq : q ≤ n) :
      (univ.filter (fun j ↦ (w j).val < q)).card = q := by
    rw [bijection_count_val_lt w hi, card_filter_val_lt _ _ hq]
  have hlo := sorted_threshold_prefix w hm (w i).val i
  have hhi := sorted_threshold_prefix w hm ((w i).val + 1) i
  rw [hcount _ (w i).isLt.le] at hlo
  rw [hcount _ (w i).isLt] at hhi
  apply Fin.ext
  change (w i).val = i.val
  omega

theorem sorted_network_rank_identity {n : ℕ} (net : ComparatorNetwork n)
    (hs : ComparatorNetwork.Sorts.{0} net) (w : Fin n → Fin n) (hw : Function.Injective w) :
    net.exec w = id :=
  monotone_injective_rank_identity _ (hs _ w) (ComparatorNetwork.exec_injective net hw)

end Paterson.Bags
