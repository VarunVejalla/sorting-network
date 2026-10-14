import AKS.Chvatal.Tree
import Mathlib.Tactic

namespace Tapered945

open Chvatal

variable {d : Nat}

set_option maxRecDepth 4096

/-- The native keys of a bag. -/
def nativeKeys {d : Nat} (b : KBag 64 d) : Finset (Fin (64 ^ d)) :=
  Finset.univ.filter (fun κ => b.Native κ id)

private theorem pow_sub_succ (d l : Nat) (hl : l < d) :
    (64 : Nat) ^ (d - l) = 64 * 64 ^ (d - l - 1) := by
  rw [← Nat.pow_succ']
  congr 1
  omega

/-- Native membership in child `j` is the corresponding equal-width
subinterval of the parent's native interval. -/
theorem native_child_interval (q : KBag 64 d) (hq : q.l < d)
    (j : Nat) (hj : j < 64) (κ : Fin (64 ^ d)) :
    (q.child j hj hq).Native κ id ↔
      q.x * 64 ^ (d - q.l) + j * 64 ^ (d - q.l - 1) ≤ κ.val ∧
        κ.val < q.x * 64 ^ (d - q.l) + (j + 1) * 64 ^ (d - q.l - 1) := by
  rw [KBag.native_iff _ _ _ (by norm_num)]
  have e := pow_sub_succ d q.l hq
  have e2 : d - (q.l + 1) = d - q.l - 1 := by omega
  simp only [KBag.lo, KBag.hi, KBag.size, bagSize, KBag.child, id, e2]
  have h1 : (64 * q.x + j) * 64 ^ (d - q.l - 1) =
      q.x * 64 ^ (d - q.l) + j * 64 ^ (d - q.l - 1) := by rw [e]; ring
  have h2 : (64 * q.x + j + 1) * 64 ^ (d - q.l - 1) =
      q.x * 64 ^ (d - q.l) + (j + 1) * 64 ^ (d - q.l - 1) := by rw [e]; ring
  rw [h1, h2]

private theorem native_parent_interval (q : KBag 64 d) (hq : q.l < d)
    (κ : Fin (64 ^ d)) :
    q.Native κ id ↔ q.x * 64 ^ (d - q.l) ≤ κ.val ∧
      κ.val < q.x * 64 ^ (d - q.l) + 64 * 64 ^ (d - q.l - 1) := by
  rw [KBag.native_iff _ _ _ (by norm_num)]
  have e := pow_sub_succ d q.l hq
  simp only [KBag.lo, KBag.hi, KBag.size, bagSize, id]
  have h2 : (q.x + 1) * 64 ^ (d - q.l) =
      q.x * 64 ^ (d - q.l) + 64 * 64 ^ (d - q.l - 1) := by rw [← e]; ring
  rw [h2]

/-- Each key native to a parent is native to exactly one of its 64 children;
the child intervals cover the parent interval. -/
theorem native_children_cover (q : KBag 64 d) (hq : q.l < d) :
    (Finset.univ : Finset (Fin 64)).biUnion
      (fun j => nativeKeys (q.child j.val j.isLt hq)) = nativeKeys q := by
  classical
  ext κ
  constructor
  · intro h
    obtain ⟨j, _, hκ⟩ := Finset.mem_biUnion.mp h
    have hκ := (Finset.mem_filter.mp hκ).2
    rw [native_child_interval q hq j.val j.isLt κ] at hκ
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · rw [native_parent_interval q hq]
      constructor
      · exact le_trans (Nat.le_add_right _ _) hκ.1
      · calc
          κ.val < q.x * 64 ^ (d - q.l) + (j.val + 1) * 64 ^ (d - q.l - 1) := hκ.2
          _ ≤ q.x * 64 ^ (d - q.l) + 64 * 64 ^ (d - q.l - 1) := by
            gcongr
            exact Nat.succ_le_of_lt j.isLt
  · intro hparent
    have hparent := (Finset.mem_filter.mp hparent).2
    rw [native_parent_interval q hq] at hparent
    have e := pow_sub_succ d q.l hq
    let S := 64 ^ (d - q.l - 1)
    let U := q.x * 64 ^ (d - q.l)
    have hS : 0 < S := by dsimp [S]; positivity
    have hparentU : U ≤ κ.val ∧ κ.val < U + 64 * S := by
      simpa [U, S, e] using hparent
    have hdiff_lt : κ.val - U < 64 * S := by
      omega
    let jval := (κ.val - U) / S
    have hjval : jval < 64 := by
      apply (Nat.div_lt_iff_lt_mul hS).2
      simpa [jval] using hdiff_lt
    let j : Fin 64 := ⟨jval, hjval⟩
    have hmul_le : jval * S ≤ κ.val - U := by
      dsimp [jval]
      exact Nat.div_mul_le_self _ _
    have hmod : (κ.val - U) % S < S := Nat.mod_lt _ hS
    have hdecomp : (κ.val - U) % S + jval * S = κ.val - U := by
      dsimp [jval]
      simpa [Nat.mul_comm] using Nat.mod_add_div (κ.val - U) S
    have hslotlow : U + jval * S ≤ κ.val := by omega
    have hslothigh : κ.val < U + (jval + 1) * S := by
      have htmp : κ.val - U < jval * S + S := by omega
      have hmul : jval * S + S = (jval + 1) * S := by ring
      omega
    have hchild : (q.child j.val j.isLt hq).Native κ id := by
      rw [native_child_interval q hq j.val j.isLt κ]
      change U + jval * S ≤ κ.val ∧ κ.val < U + (jval + 1) * S
      exact ⟨hslotlow, hslothigh⟩
    have hchildMem : κ ∈ nativeKeys (q.child j.val j.isLt hq) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hchild⟩
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hchildMem⟩

/-- Distinct children have disjoint native-key sets. -/
theorem native_children_disjoint (q : KBag 64 d) (hq : q.l < d)
    {i j : Fin 64} (hij : i ≠ j) :
    Disjoint (nativeKeys (q.child i.val i.isLt hq))
      (nativeKeys (q.child j.val j.isLt hq)) := by
  classical
  rw [Finset.disjoint_left]
  intro κ hi hj
  change κ ∈ Finset.univ.filter (fun x => (q.child i.val i.isLt hq).Native x id) at hi
  change κ ∈ Finset.univ.filter (fun x => (q.child j.val j.isLt hq).Native x id) at hj
  have hi := (Finset.mem_filter.mp hi).2
  have hj := (Finset.mem_filter.mp hj).2
  rw [native_child_interval q hq i.val i.isLt κ] at hi
  rw [native_child_interval q hq j.val j.isLt κ] at hj
  rcases lt_or_gt_of_ne (fun he => hij (Fin.ext he)) with hlt | hgt
  · have hmul := Nat.mul_le_mul_right (64 ^ (d - q.l - 1)) (Nat.succ_le_of_lt hlt)
    dsimp at hmul
    omega
  · have hmul := Nat.mul_le_mul_right (64 ^ (d - q.l - 1)) (Nat.succ_le_of_lt hgt)
    dsimp at hmul
    omega

end Tapered945
