import AKS.Chvatal.NodeKeys
import D2BlockSortDisplacement

namespace Chvatal.D2SenderRankBridge

open Chvatal
open Chvatal.D2BlockSortDisplacement

private theorem rk_strict_of_lt {a M : Nat} (x : Fin a → Fin M)
    (u v : Fin M) (hu : u ∈ keySet x) (huv : u < v) :
    rk (keySet x) u < rk (keySet x) v := by
  let A := (keySet x).filter (· < u)
  let B := (keySet x).filter (· < v)
  have hsub : A ⊆ B := by
    intro z hz
    simp only [A, B, Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, lt_trans hz.2 huv⟩
  have huB : u ∈ B := by simp [B, hu, huv]
  have huA : u ∉ A := by simp [A]
  have hne : A ≠ B := by
    intro heq
    have huA' : u ∈ A := heq.symm ▸ huB
    exact huA huA'
  have hcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  exact hcard

theorem rankPerm_inverse_sorted
    {a M : Nat} (x : Fin a → Fin M) (hx : Function.Injective x) :
    ∀ i j : Fin a, i ≤ j → x ((rankPerm hx).symm i) ≤ x ((rankPerm hx).symm j) := by
  let rp := rankPerm hx
  have hrank (i : Fin a) : rk (keySet x) (x (rp.symm i)) = i.val := by
    have h := congrArg Fin.val (rp.apply_symm_apply i)
    change (rankFun hx (rp.symm i)).val = i.val at h
    simpa [rankFun] using h
  intro i j hij
  apply Fin.le_iff_val_le_val.mpr
  by_contra h
  have hlt : x (rp.symm j) < x (rp.symm i) :=
    Fin.lt_iff_val_lt_val.mpr (Nat.lt_of_not_ge h)
  have hm := rk_strict_of_lt x (x (rp.symm j)) (x (rp.symm i))
    (mem_keySet x (rp.symm j)) hlt
  rw [hrank j, hrank i] at hm
  have hijv : i.val ≤ j.val := Fin.le_iff_val_le_val.mp hij
  omega

theorem network_sender_displacement_of_rank_bound
    {a M E G L : Nat} (net : ComparatorNetwork a)
    (addr : Fin a → Fin M) (f : Fin M → Fin M)
    (haddr : StrictMono addr)
    (hgap : ∀ i j, i.val ≤ j.val →
      (addr j).val ≤ (addr i).val + G * (j.val - i.val))
    (hfInjective : Function.Injective f)
    (hfdisp : ∀ p, (f p).val ≤ p.val + E ∧ p.val ≤ (f p).val + E)
    (hrank : ∀ v : Fin a → Fin a, Function.Bijective v → ∀ w,
      (net.exec v w).val ≤ w.val + L ∧ w.val ≤ (net.exec v w).val + L) :
    ∀ i, (net.exec (f ∘ addr) i).val ≤ (addr i).val + E + G * L ∧
      (addr i).val ≤ (net.exec (f ∘ addr) i).val + E + G * L := by
  let x : Fin a → Fin M := f ∘ addr
  have hx : Function.Injective x := hfInjective.comp haddr.injective
  let rp : Equiv.Perm (Fin a) := rankPerm hx
  let localRank : Fin a → Fin a := fun i => net.exec (rp : Fin a → Fin a) i
  let exactSorted : Fin a → Fin M := fun j => x (rp.symm j)
  let actual : Fin a → Fin M := fun i => net.exec x i
  have hnorm (i : Fin a) :
      (localRank i).val = rk (keySet x) (net.exec x i) := by
    dsimp [localRank, rp]
    exact exec_rankPerm hx net i
  obtain ⟨ρ, hρ⟩ := ComparatorNetwork.exec_eq_comp_perm net x
  have hρfun (i : Fin a) : net.exec x i = x (ρ i) := by
    have h := congrFun hρ i
    change net.exec x i = (x ∘ (ρ : Fin a → Fin a)) i at h
    simpa only [Function.comp_apply] using h
  have hactual (i : Fin a) : actual i = exactSorted (localRank i) := by
    have hslot : rp (ρ i) = localRank i := by
      apply Fin.ext
      change rk (keySet x) (x (ρ i)) = (localRank i).val
      rw [hnorm i]
      exact (congrArg (rk (keySet x)) (hρfun i)).symm
    calc
      actual i = x (ρ i) := by
        dsimp [actual]
        exact congrFun hρ i
      _ = exactSorted (localRank i) := by
        dsimp [exactSorted]
        rw [← hslot]
        simp
  have hsorted : ∀ i j, i ≤ j →
      (f (addr (rp.symm i))).val ≤ (f (addr (rp.symm j))).val := by
    intro i j hij
    have h := rankPerm_inverse_sorted x hx i j hij
    exact Fin.le_iff_val_le_val.mp (by simpa [x] using h)
  have hexact : ∀ i, (exactSorted i).val ≤ (addr i).val + E ∧
      (addr i).val ≤ (exactSorted i).val + E := by
    have h := ordered_sender_sort_preserves_displacement
      addr rp.symm f haddr rp.symm.injective hfdisp hsorted
    simpa [exactSorted, x] using h
  have hlocal : ∀ i, (localRank i).val ≤ i.val + L ∧
      i.val ≤ (localRank i).val + L := by
    intro i
    exact hrank (rp : Fin a → Fin a) rp.bijective i
  exact local_rank_displacement_with_address_gaps
    addr exactSorted actual localRank haddr.monotone hgap hexact hlocal hactual

end Chvatal.D2SenderRankBridge
