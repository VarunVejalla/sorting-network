import AKS.Chvatal.Lemma41Real

/-!
Scratch generalization of the descendant-counting part of Lemma 4.1.
Unlike `subtree_bad_le`, this theorem accepts an arbitrary per-bag,
per-rank outsider profile instead of `OutsiderBoundLe`.
-/

namespace Chvatal

open Finset
open scoped Classical

theorem subtree_bad_le_profile
    (d : Nat)
    (pl : Placement 64 d) (a : Nat -> Nat)
    (hcard : forall b : KBag 64 d, (pl.regs b).card = a b.l)
    (profile : KBag 64 d -> Nat -> Rat)
    (hprofile : forall (z : KBag 64 d) (r : Nat), r <= d ->
      ((z.strangers (r + 1) id (pl.regs z) : Nat) : Rat) <= profile z r)
    (w : KBag 64 d) :
    (((subtreeKeys 64 d pl (by norm_num) w).filter
      fun k => not (w.Native k id)).card : Rat) <=
      Finset.sum (Finset.range (d - w.l + 1)) (fun h =>
        Finset.sum (descendants 64 d (by norm_num) w h) (fun z =>
          min (profile z h) (a z.l : Rat))) := by
  have hbr : 1 <= 64 := by norm_num
  unfold subtreeKeys subtreeBags
  rw [Finset.filter_biUnion,
    Finset.card_biUnion (fun z _ z' _ hne =>
      Finset.disjoint_filter_filter (pl.disjoint z z' hne)),
    Finset.sum_biUnion (fun h _ h' _ hne => descendants_disjoint hbr w hne)]
  push_cast
  refine Finset.sum_le_sum fun h hh => ?_
  rw [Finset.mem_range] at hh
  refine Finset.sum_le_sum fun z hz => le_min ?_ ?_
  · have hzl := ((mem_descendants hbr w h z).mp hz).1
    have h1 : ((pl.regs z).filter fun k => not (w.Native k id)).card <=
        z.strangers (h + 1) id (pl.regs z) hbr := by
      unfold KBag.strangers
      refine Finset.card_le_card fun k hk => ?_
      rw [Finset.mem_filter] at hk ⊢
      refine ⟨hk.1, Or.inr ?_⟩
      simpa [((Finset.mem_filter.mp hz).2).2] using hk.2
    have hhd : h <= d := by have := z.hl; rw [hzl] at this; omega
    have h2 := hprofile z h hhd
    exact le_trans (by exact_mod_cast h1) h2
  · rw [← hcard z]
    exact_mod_cast Finset.card_filter_le _ _

end Chvatal
