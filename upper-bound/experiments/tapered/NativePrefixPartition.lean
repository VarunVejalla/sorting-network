import NativeChildrenPartition
import AKS.Chvatal.Lemma41Real
import Mathlib.Tactic

set_option maxRecDepth 4096

namespace Tapered945

open Chvatal

/-- Every cut in a radix-64 interval splits into a prefix of whole blocks and
one residual cut inside the next block. The quotient bound is what makes this
usable recursively down the native-child tree. -/
theorem prefix_radix64_address (lo cut block : Nat) (hblock : 0 < block)
    (hlo : lo ≤ cut) (hcut : cut ≤ lo + 64 * block) :
    ∃ j r, j ≤ 64 ∧ r < block ∧ cut = lo + j * block + r := by
  let j := (cut - lo) / block
  let r := (cut - lo) % block
  have hr : r < block := by
    dsimp [r]
    exact Nat.mod_lt _ hblock
  have hdecomp : r + j * block = cut - lo := by
    dsimp [r, j]
    simpa only [Nat.mul_comm] using Nat.mod_add_div (cut - lo) block
  have hj : j ≤ 64 := by
    by_contra hj
    have hj' : 64 < j := by omega
    have hmul : 64 * block < j * block :=
      Nat.mul_lt_mul_of_pos_right hj' hblock
    omega
  refine ⟨j, r, hj, hr, ?_⟩
  omega

/-- A nonterminal cut has a residual block with index strictly below 64. -/
theorem prefix_radix64_nonterminal (lo cut block : Nat) (hblock : 0 < block)
    (hlo : lo ≤ cut) (hcut : cut < lo + 64 * block) :
    ∃ j r, j < 64 ∧ r < block ∧ cut = lo + j * block + r := by
  obtain ⟨j, r, hj, hr, hsplit⟩ :=
    prefix_radix64_address lo cut block hblock hlo hcut.le
  refine ⟨j, r, ?_, hr, hsplit⟩
  by_contra hj'
  have hj64 : j = 64 := by omega
  rw [hj64] at hsplit
  omega

/-- Native keys in the first `j` child intervals of `q`. -/
def nativeChildPrefix {d : Nat} (q : KBag 64 d) (hq : q.l < d) (j : Nat) :
    Finset (Fin (64 ^ d)) :=
  (Finset.univ.filter (fun i : Fin 64 => i.val < j)).biUnion
    (fun i => nativeKeys (q.child i.val i.isLt hq))

/-- Keys whose values lie in a half-open rank interval. -/
def keyValueInterval {d : Nat} (lo hi : Nat) : Finset (Fin (64 ^ d)) :=
  Finset.univ.filter (fun k => lo ≤ k.val ∧ k.val < hi)

theorem keyValueInterval_append {d : Nat} (lo mid hi : Nat)
    (hlo : lo ≤ mid) (hmid : mid ≤ hi) :
    keyValueInterval (d := d) lo hi =
      keyValueInterval (d := d) lo mid ∪ keyValueInterval (d := d) mid hi := by
  ext k
  simp only [keyValueInterval, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union]
  omega

/-- The first `j` native child intervals are exactly the corresponding prefix
of the parent's native interval. -/
theorem native_child_prefix_eq_interval {d : Nat}
    (q : KBag 64 d) (hq : q.l < d) (j : Nat) (hj : j ≤ 64) :
    nativeChildPrefix q hq j =
      Finset.univ.filter (fun k : Fin (64 ^ d) =>
        q.lo ≤ k.val ∧ k.val < q.lo + j * 64 ^ (d - q.l - 1)) := by
  classical
  let S := 64 ^ (d - q.l - 1)
  ext k
  constructor
  · intro hk
    obtain ⟨i, hi, hki⟩ := Finset.mem_biUnion.mp hk
    have hij : i.val < j := (Finset.mem_filter.mp hi).2
    have hchild := (Finset.mem_filter.mp hki).2
    rw [native_child_interval q hq i.val i.isLt k] at hchild
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · refine ⟨?_, ?_⟩
      · dsimp [KBag.lo, KBag.size, bagSize]
        exact le_trans (Nat.le_add_right _ _) hchild.1
      · have hmul : (i.val + 1) * S ≤ j * S :=
          Nat.mul_le_mul_right S (by omega)
        dsimp [S] at hmul ⊢
        dsimp [KBag.lo, KBag.size, bagSize]
        omega
  · intro hk
    have hk := (Finset.mem_filter.mp hk).2
    have hparent : q.Native k id := by
      apply (KBag.native_iff q k id (by norm_num)).2
      constructor
      · exact hk.1
      · have hmul : j * S ≤ 64 * S := Nat.mul_le_mul_right S hj
        have hpow : 64 * S = 64 ^ (d - q.l) := by
          dsimp [S]
          have hn : 1 ≤ d - q.l := by omega
          calc
            64 * 64 ^ (d - q.l - 1) = 64 ^ (d - q.l - 1) * 64 := by omega
            _ = 64 ^ ((d - q.l - 1) + 1) := by rw [pow_succ]
            _ = 64 ^ (d - q.l) := by rw [Nat.sub_add_cancel hn]
        have hhi : q.hi = q.lo + 64 * S := by
          dsimp [KBag.hi, KBag.lo, KBag.size, bagSize]
          rw [hpow]
          ring
        rw [hhi]
        dsimp [S] at hmul ⊢
        omega
    have hparentMem : k ∈ nativeKeys q :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hparent⟩
    have hparentKids : k ∈
        (Finset.univ : Finset (Fin 64)).biUnion
          (fun i => nativeKeys (q.child i.val i.isLt hq)) := by
      rw [native_children_cover q hq]
      exact hparentMem
    have hchildCover := Finset.mem_biUnion.mpr
      (show ∃ i ∈ Finset.univ.filter (fun i : Fin 64 => i.val < j),
        k ∈ nativeKeys (q.child i.val i.isLt hq) from by
          obtain ⟨i, hi, hki⟩ := Finset.mem_biUnion.mp hparentKids
          have hchild := (Finset.mem_filter.mp hki).2
          rw [native_child_interval q hq i.val i.isLt k] at hchild
          have hij : i.val < j := by
            by_contra hn
            have hjle : j ≤ i.val := by omega
            have hmul : j * S ≤ i.val * S := Nat.mul_le_mul_right S hjle
            dsimp [S] at hmul hchild hk ⊢
            dsimp [KBag.lo, KBag.size, bagSize] at hchild hk
            omega
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, hki⟩)
    exact hchildCover

/-- One recursive step of the exact prefix decomposition: complete native
child intervals plus a remainder wholly inside the next child interval. -/
theorem native_prefix_one_child_decomposition {d : Nat}
    (q : KBag 64 d) (hq : q.l < d) (cut : Nat)
    (hcutLo : q.lo ≤ cut) (hcutHi : cut < q.hi) :
    ∃ j r, j < 64 ∧ r < 64 ^ (d - q.l - 1) ∧
      keyValueInterval q.lo cut =
        nativeChildPrefix q hq j ∪
          keyValueInterval (q.lo + j * 64 ^ (d - q.l - 1)) cut := by
  let block := 64 ^ (d - q.l - 1)
  have hblock : 0 < block := by positivity
  have hpow : 64 * block = 64 ^ (d - q.l) := by
    dsimp [block]
    have hn : 1 ≤ d - q.l := by omega
    calc
      64 * 64 ^ (d - q.l - 1) = 64 ^ (d - q.l - 1) * 64 := by omega
      _ = 64 ^ ((d - q.l - 1) + 1) := by rw [pow_succ]
      _ = 64 ^ (d - q.l) := by rw [Nat.sub_add_cancel hn]
  have hhi : q.hi = q.lo + 64 * block := by
    dsimp [KBag.hi, KBag.lo, KBag.size, bagSize]
    rw [hpow]
    ring
  obtain ⟨j, r, hj, hr, hdecomp⟩ :=
    prefix_radix64_nonterminal q.lo cut block hblock hcutLo (by rw [hhi] at hcutHi; exact hcutHi)
  have hjle : j ≤ 64 := by omega
  have hmid : q.lo + j * block ≤ cut := by omega
  have hloMid : q.lo ≤ q.lo + j * block := by omega
  have hfirst : nativeChildPrefix q hq j = keyValueInterval q.lo (q.lo + j * block) := by
    simpa [keyValueInterval, block] using native_child_prefix_eq_interval q hq j hjle
  refine ⟨j, r, hj, ?_, ?_⟩
  · exact hr
  · rw [hfirst]
    exact keyValueInterval_append (d := d) q.lo (q.lo + j * block) cut hloMid hmid

end Tapered945
