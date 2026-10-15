import OddEvenMerge64
import PacketAlignment
import AKS.Chvatal.StageNet

/-! Fixed-label repair of two separated ascending half-packets, using
Batcher's six-layer odd-even merge. This file uses the best package's
comparator-network model; `check-lean.ps1` builds the scratch imports. -/

namespace Chvatal.PacketAlignment

open Classical

/-- Concatenate the increasing enumerations of two physically separated
32-wire supports. The placement depends only on the supports. -/
noncomputable def orderedHalfPairEmbedding {N : Nat}
    (A B : Finset (Fin N)) (hA : A.card = 32) (hB : B.card = 32)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, a < b) : Fin 64 ↪o Fin N :=
  OrderEmbedding.ofStrictMono
    (fun i : Fin 64 => Fin.addCases (fun a : Fin 32 => A.orderEmbOfFin hA a)
      (fun b : Fin 32 => B.orderEmbOfFin hB b) i) (by
      intro i j hij
      rcases hi : (finSumFinEquiv : Fin 32 ⊕ Fin 32 ≃ Fin 64).symm i with a | a <;>
        rcases hj : (finSumFinEquiv : Fin 32 ⊕ Fin 32 ≃ Fin 64).symm j with b | b
      · have hie : i = Fin.castAdd 32 a := by
          simpa only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] using (congrArg (finSumFinEquiv : Fin 32 ⊕ Fin 32 ≃ Fin 64) hi)
        have hje : j = Fin.castAdd 32 b := by
          simpa only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] using (congrArg (finSumFinEquiv : Fin 32 ⊕ Fin 32 ≃ Fin 64) hj)
        rw [hie, hje] at hij ⊢
        simp only [Fin.addCases_left]
        exact (A.orderEmbOfFin hA).strictMono (by simpa using hij)
      · have hie : i = Fin.castAdd 32 a := by
          simpa only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] using (congrArg (finSumFinEquiv : Fin 32 ⊕ Fin 32 ≃ Fin 64) hi)
        have hje : j = Fin.natAdd 32 b := by
          simpa only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] using (congrArg (finSumFinEquiv : Fin 32 ⊕ Fin 32 ≃ Fin 64) hj)
        rw [hie, hje]
        simp only [Fin.addCases_left, Fin.addCases_right]
        exact hsep _ (A.orderEmbOfFin_mem hA a) _ (B.orderEmbOfFin_mem hB b)
      · have hie : i = Fin.natAdd 32 a := by
          simpa only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] using (congrArg (finSumFinEquiv : Fin 32 ⊕ Fin 32 ≃ Fin 64) hi)
        have hje : j = Fin.castAdd 32 b := by
          simpa only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] using (congrArg (finSumFinEquiv : Fin 32 ⊕ Fin 32 ≃ Fin 64) hj)
        have hv := Fin.lt_def.mp hij
        rw [hie, hje] at hv
        have ha := a.isLt
        have hb := b.isLt
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
        omega
      · have hie : i = Fin.natAdd 32 a := by
          simpa only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] using (congrArg (finSumFinEquiv : Fin 32 ⊕ Fin 32 ≃ Fin 64) hi)
        have hje : j = Fin.natAdd 32 b := by
          simpa only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] using (congrArg (finSumFinEquiv : Fin 32 ⊕ Fin 32 ≃ Fin 64) hj)
        rw [hie, hje] at hij ⊢
        simp only [Fin.addCases_right]
        apply (B.orderEmbOfFin hB).strictMono
        have hv := Fin.lt_def.mp hij
        apply Fin.mk_lt_mk.mpr
        simp only [Fin.val_natAdd] at hv
        omega)

@[simp] theorem orderedHalfPairEmbedding_left {N : Nat}
    (A B : Finset (Fin N)) (hA : A.card = 32) (hB : B.card = 32)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, a < b) (i : Fin 32) :
    orderedHalfPairEmbedding A B hA hB hsep (Fin.castAdd 32 i) =
      A.orderEmbOfFin hA i := by
  simp [orderedHalfPairEmbedding]

@[simp] theorem orderedHalfPairEmbedding_right {N : Nat}
    (A B : Finset (Fin N)) (hA : A.card = 32) (hB : B.card = 32)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, a < b) (i : Fin 32) :
    orderedHalfPairEmbedding A B hA hB hsep (Fin.natAdd 32 i) =
      B.orderEmbOfFin hB i := by
  change @Fin.addCases 32 32 (fun _ => Fin N) (fun a => A.orderEmbOfFin hA a)
    (fun b => B.orderEmbOfFin hB b) (Fin.natAdd 32 i) = B.orderEmbOfFin hB i
  rw [Fin.addCases_right]

theorem orderedHalfPairEmbedding_range {N : Nat}
    (A B : Finset (Fin N)) (hA : A.card = 32) (hB : B.card = 32)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    Set.range (orderedHalfPairEmbedding A B hA hB hsep) =
      {w | w ∈ A ∪ B} := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    change orderedHalfPairEmbedding A B hA hB hsep i ∈ A ∪ B
    refine Fin.addCases (m := 32) (n := 32) (fun a => ?_) (fun b => ?_) i
    · rw [orderedHalfPairEmbedding_left]
      exact Finset.mem_union_left _ (A.orderEmbOfFin_mem hA a)
    · rw [orderedHalfPairEmbedding_right]
      exact Finset.mem_union_right _ (B.orderEmbOfFin_mem hB b)
  · intro hw
    rcases Finset.mem_union.mp hw with ha | hb
    · let a := (A.orderIsoOfFin hA).symm ⟨w, ha⟩
      refine ⟨Fin.castAdd 32 a, ?_⟩
      rw [orderedHalfPairEmbedding_left]
      change ↑(A.orderIsoOfFin hA ((A.orderIsoOfFin hA).symm ⟨w, ha⟩)) = w
      simp
    · let b := (B.orderIsoOfFin hB).symm ⟨w, hb⟩
      refine ⟨Fin.natAdd 32 b, ?_⟩
      rw [orderedHalfPairEmbedding_right]
      change ↑(B.orderIsoOfFin hB ((B.orderIsoOfFin hB).symm ⟨w, hb⟩)) = w
      simp

/-- A fixed comparator network on the union of two separated half-packets. -/
noncomputable def repairOrderedHalfPair {N : Nat}
    (A B : Finset (Fin N)) (hA : A.card = 32) (hB : B.card = 32)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, a < b) : ComparatorNetwork N :=
  (oddEvenMergeNet 6).scatterEmbed N (orderedHalfPairEmbedding A B hA hB hsep)

theorem repairOrderedHalfPair_depth_le {N : Nat}
    (A B : Finset (Fin N)) (hA : A.card = 32) (hB : B.card = 32)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    (repairOrderedHalfPair A B hA hB hsep).depth ≤ 6 :=
  oddEvenMergeNet64_scatter_depth_le _

theorem repairOrderedHalfPair_sorts {N : Nat} {α : Type} [LinearOrder α]
    (A B : Finset (Fin N)) (hA : A.card = 32) (hB : B.card = 32)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, a < b) (v : Fin N → α)
    (hsA : RankSortedOn A v) (hsB : RankSortedOn B v) :
    RankSortedOn (A ∪ B) ((repairOrderedHalfPair A B hA hB hsep).exec v) := by
  let e := orderedHalfPairEmbedding A B hA hB hsep
  have ha : Monotone (fun i : Fin 32 => v (e (Fin.castAdd 32 i))) := by
    intro i j hij
    simp only [e, orderedHalfPairEmbedding_left]
    apply hsA (A.orderEmbOfFin_mem hA i) (A.orderEmbOfFin_mem hA j)
    exact Fin.le_def.mp ((A.orderEmbOfFin hA).monotone hij)
  have hb : Monotone (fun i : Fin 32 => v (e (Fin.natAdd 32 i))) := by
    intro i j hij
    simp only [e, orderedHalfPairEmbedding_right]
    apply hsB (B.orderEmbOfFin_mem hB i) (B.orderEmbOfFin_mem hB j)
    exact Fin.le_def.mp ((B.orderEmbOfFin hB).monotone hij)
  have hs := oddEvenMergeNet64_scatter_sorts e v ha hb
  intro x y hx hy hxy
  have hx' : x ∈ Set.range e := by
    rw [show Set.range e = {w | w ∈ A ∪ B} from orderedHalfPairEmbedding_range A B hA hB hsep]
    exact hx
  have hy' : y ∈ Set.range e := by
    rw [show Set.range e = {w | w ∈ A ∪ B} from orderedHalfPairEmbedding_range A B hA hB hsep]
    exact hy
  obtain ⟨i, rfl⟩ := hx'
  obtain ⟨j, rfl⟩ := hy'
  exact hs (e.le_iff_le.mp (Fin.le_def.mpr hxy))

theorem repairOrderedHalfPair_exec_outside {N : Nat} {α : Type} [LinearOrder α]
    (A B : Finset (Fin N)) (hA : A.card = 32) (hB : B.card = 32)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, a < b) (v : Fin N → α)
    (w : Fin N) (hw : w ∉ A ∪ B) :
    (repairOrderedHalfPair A B hA hB hsep).exec v w = v w := by
  exact ComparatorNetwork.scatterEmbed_exec_outside (oddEvenMergeNet 6) N
    (orderedHalfPairEmbedding A B hA hB hsep) v w (by
      rw [orderedHalfPairEmbedding_range]
      exact hw)

/-- The packet invariant only orders values inside each 64-rank cell of a
support. It imposes no value order between different packets. -/
def PacketSortedOn {N : Nat} {α : Type} [Preorder α]
    (s : Finset (Fin N)) (v : Fin N → α) : Prop :=
  ∀ p : Nat, RankSortedOn (Chvatal.blockOf s (64 * p) (64 * (p + 1))) v

/-- Either aligned half of one packet is an ascending run under the packet
invariant; sorting the whole sender bag is unnecessary. -/
theorem packetSortedOn_halfPacket {N : Nat} {α : Type} [Preorder α]
    (s : Finset (Fin N)) (v : Fin N → α) (hpack : PacketSortedOn s v)
    (lo : Nat) (hres : lo % 64 = 0 ∨ lo % 64 = 32) :
    RankSortedOn (Chvatal.blockOf s lo (lo + 32)) v := by
  apply rankSortedOn_subset (s := Chvatal.blockOf s
    (64 * (lo / 64)) (64 * (lo / 64 + 1))) ?_ (hpack (lo / 64))
  intro w hw
  have h := Chvatal.mem_blockOf.mp hw
  apply Chvatal.mem_blockOf.mpr
  have hdiv := Nat.mod_add_div lo 64
  rcases hres with hres | hres <;> rw [hres] at hdiv <;>
    exact ⟨h.1, by omega, by omega⟩

/-- The actual two half-packet ends of a shifted down-cut are sorted even
when the sender's packets have unrelated value ranges. -/
theorem packetSortedOn_rankInterval_endpoints {N : Nat} {α : Type} [Preorder α]
    (s : Finset (Fin N)) (v : Fin N → α) (hpack : PacketSortedOn s v)
    (lo hi : Nat) (hspan : 64 ≤ hi - lo)
    (hlo : lo % 64 = 32) (hhi : hi % 64 = 32) :
    RankSortedOn (Chvatal.blockOf s lo (lo + 32)) v ∧
      RankSortedOn (Chvatal.blockOf s (hi - 32) hi) v := by
  constructor
  · exact packetSortedOn_halfPacket s v hpack lo (Or.inr hlo)
  · have hhi32 : 32 ≤ hi := by omega
    have hres : (hi - 32) % 64 = 0 := by omega
    have heq : hi - 32 + 32 = hi := by omega
    simpa only [heq] using
      packetSortedOn_halfPacket s v hpack (hi - 32) (Or.inl hres)

/-- There is one input-independent six-layer repair for these two separated
half-packets. Its correctness assumes sorted packets, not a sorted bag. -/
theorem rankInterval_endpoint_repair_exists {N : Nat}
    (s : Finset (Fin N)) (lo hi : Nat) (hspan : 64 ≤ hi - lo)
    (hcard : hi ≤ s.card) (hlo : lo % 64 = 32) (hhi : hi % 64 = 32) :
    ∃ net : ComparatorNetwork N, net.depth ≤ 6 ∧
      ∀ {α : Type} [LinearOrder α] (v : Fin N → α), PacketSortedOn s v →
        RankSortedOn (Chvatal.blockOf s lo (lo + 32) ∪
          Chvatal.blockOf s (hi - 32) hi) (net.exec v) := by
  let A := Chvatal.blockOf s lo (lo + 32)
  let B := Chvatal.blockOf s (hi - 32) hi
  have hc := rankInterval_endpoint_pair s lo hi hspan hcard
  have hA : A.card = 32 := hc.2.1
  have hB : B.card = 32 := hc.2.2.1
  have hsep : ∀ a ∈ A, ∀ b ∈ B, a < b := by
    intro a ha b hb
    exact rankInterval_endpoint_pair_ordered s lo hi hspan ha hb
  refine ⟨repairOrderedHalfPair A B hA hB hsep,
    repairOrderedHalfPair_depth_le A B hA hB hsep, ?_⟩
  intro α _ v hp
  obtain ⟨hsA, hsB⟩ := packetSortedOn_rankInterval_endpoints s v hp lo hi hspan hlo hhi
  exact repairOrderedHalfPair_sorts A B hA hB hsep v hsA hsB

/-- The two half-packets at the ends of child cut `j` in a shifted parent
down-port. The cut has length `τ`; the two 32-wire fragments are its first
and last halves. -/
def downSetEndpointLeft {N : Nat} (s : Finset (Fin N)) (π τ : Nat)
    (j : Fin 64) : Finset (Fin N) :=
  Chvatal.blockOf s (π / 2 + j.val * τ) (π / 2 + j.val * τ + 32)

def downSetEndpointRight {N : Nat} (s : Finset (Fin N)) (π τ : Nat)
    (j : Fin 64) : Finset (Fin N) :=
  Chvatal.blockOf s
    (π / 2 + (j.val + 1) * τ - 32) (π / 2 + (j.val + 1) * τ)

/-- An untouched full packet in the interior of a down-cut whose 32-wire
grid shift occurs only at the two ends. -/
def downSetInteriorCell {N : Nat} (s : Finset (Fin N)) (π τ : Nat)
    (j : Fin 64) (m : Nat) (k : Fin m) : Finset (Fin N) :=
  Chvatal.blockOf s
    (π / 2 + j.val * τ + 32 + 64 * k.val)
    (π / 2 + j.val * τ + 32 + 64 * (k.val + 1))

/-- The endpoint pair plus the aligned interior 64-cells exactly partitions
one down-cut. Here `τ=64*(m+1)`, so there is one repaired endpoint packet and
`m` unchanged complete packets. -/
theorem downSetEndpoint_partition {N : Nat} (s : Finset (Fin N))
    (π τ : Nat) (j : Fin 64) (m : Nat) (hτ : τ = 64 * (m + 1)) :
    Chvatal.downSet s π τ j =
      (downSetEndpointLeft s π τ j ∪ downSetEndpointRight s π τ j) ∪
        Finset.univ.biUnion (fun k : Fin m => downSetInteriorCell s π τ j m k) := by
  classical
  let lo := π / 2 + j.val * τ
  let hi := π / 2 + (j.val + 1) * τ
  have hhi : hi = lo + 64 * (m + 1) := by
    dsimp [hi, lo]
    rw [hτ, Nat.add_mul, Nat.one_mul]
    omega
  have hmid : hi - 32 = lo + 32 + 64 * m := by
    rw [hhi]
    omega
  ext w
  simp only [Chvatal.downSet, downSetEndpointLeft, downSetEndpointRight,
    downSetInteriorCell, Chvatal.mem_blockOf, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  change (w ∈ s ∧ lo ≤ Chvatal.rankIn s w ∧ Chvatal.rankIn s w < hi) ↔ _
  constructor
  · rintro ⟨hw, hlo, hlt⟩
    by_cases hleft : Chvatal.rankIn s w < lo + 32
    · exact Or.inl (Or.inl ⟨hw, hlo, hleft⟩)
    · by_cases hright : lo + 32 + 64 * m ≤ Chvatal.rankIn s w
      · have hmid' : π / 2 + (j.val + 1) * τ - 32 = lo + 32 + 64 * m := by
          simpa [hi] using hmid
        exact Or.inl (Or.inr ⟨hw, by rw [hmid']; exact hright, hlt⟩)
      · right
        have hspan : Chvatal.rankIn s w - (lo + 32) < 64 * m := by omega
        let k : Nat := (Chvatal.rankIn s w - (lo + 32)) / 64
        have hk : k < m := by
          dsimp [k]
          apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 64)).2
          omega
        let ki : Fin m := ⟨k, hk⟩
        refine ⟨ki, hw, ?_, ?_⟩
        · have hdecomp := Nat.mod_add_div (Chvatal.rankIn s w - (lo + 32)) 64
          dsimp [ki, k]
          omega
        · have hdecomp := Nat.mod_add_div (Chvatal.rankIn s w - (lo + 32)) 64
          dsimp [ki, k]
          omega
  · rintro ((⟨hw, hlo, hlt⟩ | ⟨hw, hlo, hlt⟩) | ⟨k, hw, hlo, hlt⟩)
    · exact ⟨hw, hlo, by omega⟩
    · exact ⟨hw, by rw [hmid] at hlo; omega, hlt⟩
    · have hk := k.isLt
      exact ⟨hw, by omega, by rw [hhi]; omega⟩

/-- Every interior cell in that partition is an original packet-grid cell,
so packet-sortedness carries through it without any comparator. -/
theorem downSetInteriorCell_sorted {N : Nat} {α : Type} [Preorder α]
    (s : Finset (Fin N)) (π τ : Nat) (j : Fin 64) (m : Nat)
    (hτ : 64 ∣ τ) (hbase : (π / 2) % 64 = 32)
    (v : Fin N → α) (hpack : PacketSortedOn s v) (k : Fin m) :
    RankSortedOn (downSetInteriorCell s π τ j m k) v := by
  let lo := π / 2 + j.val * τ
  let cellLo := lo + 32 + 64 * k.val
  let cellHi := lo + 32 + 64 * (k.val + 1)
  have hlo : lo % 64 = 32 := by
    dsimp [lo]
    rw [(downSet_cut_residues (π := π) (τ := τ) (j := j.val) hτ).1, hbase]
  have hdiv := Nat.mod_add_div lo 64
  rw [hlo] at hdiv
  let p := lo / 64 + k.val + 1
  have hcellLo : cellLo = 64 * p := by
    dsimp [cellLo, p]
    omega
  have hcellHi : cellHi = 64 * (p + 1) := by
    dsimp [cellHi, cellLo, p]
    omega
  unfold downSetInteriorCell
  change RankSortedOn (Chvatal.blockOf s cellLo cellHi) v
  rw [hcellLo, hcellHi]
  exact hpack p

theorem downSetInteriorCell_bounds {N : Nat} (s : Finset (Fin N))
    (π τ : Nat) (j : Fin 64) (m : Nat) (hτ : τ = 64 * (m + 1))
    (k : Fin m) (w : Fin N)
    (hw : w ∈ downSetInteriorCell s π τ j m k) :
    π / 2 + j.val * τ + 32 ≤ Chvatal.rankIn s w ∧
      Chvatal.rankIn s w < π / 2 + (j.val + 1) * τ - 32 := by
  have hstep : (j.val + 1) * τ = j.val * τ + τ := by
    rw [Nat.add_mul, Nat.one_mul]
  have hmid : π / 2 + (j.val + 1) * τ - 32 =
      π / 2 + j.val * τ + 32 + 64 * m := by
    rw [hstep, hτ]
    omega
  have hr := Chvatal.mem_blockOf.mp hw
  have hk := k.isLt
  constructor
  · have hstart : π / 2 + j.val * τ + 32 + 64 * k.val =
        π / 2 + j.val * τ + 32 + 64 * k.val := rfl
    omega
  · calc
      Chvatal.rankIn s w < π / 2 + j.val * τ + 32 + 64 * (k.val + 1) := hr.2.2
      _ ≤ π / 2 + j.val * τ + 32 + 64 * m := by gcongr <;> omega
      _ = π / 2 + (j.val + 1) * τ - 32 := hmid.symm

/-- One endpoint correction sorts its new 64-wire packet and leaves every
aligned interior packet sorted and unchanged. Together with
`downSetEndpoint_partition`, this gives a complete sorted-packet partition of
one child down-cut. -/
theorem downSetEndpointRepair_preserves_interiors {N : Nat} {α : Type}
    [LinearOrder α] (s : Finset (Fin N)) (π τ : Nat) (j : Fin 64)
    (m : Nat) (hτ : τ = 64 * (m + 1))
    (hbase : (π / 2) % 64 = 32) (hhiCard : π / 2 + (j.val + 1) * τ ≤ s.card)
    (v : Fin N → α) (hpack : PacketSortedOn s v) :
    ∃ net : ComparatorNetwork N, net.depth ≤ 6 ∧
      RankSortedOn
        (downSetEndpointLeft s π τ j ∪ downSetEndpointRight s π τ j)
        (net.exec v) ∧
      ∀ k : Fin m, RankSortedOn (downSetInteriorCell s π τ j m k) (net.exec v) := by
  let lo := π / 2 + j.val * τ
  let hi := π / 2 + (j.val + 1) * τ
  let A := downSetEndpointLeft s π τ j
  let B := downSetEndpointRight s π τ j
  have hτdiv : 64 ∣ τ := by rw [hτ]; exact ⟨m + 1, rfl⟩
  have hstep : (j.val + 1) * τ = j.val * τ + τ := by
    rw [Nat.add_mul, Nat.one_mul]
  have hspan : 64 ≤ hi - lo := by
    dsimp [hi, lo]
    rw [hstep, hτ]
    omega
  have hlo : lo % 64 = 32 := by
    dsimp [lo]
    rw [(downSet_cut_residues (π := π) (τ := τ) (j := j.val) hτdiv).1, hbase]
  have hhi : hi % 64 = 32 := by
    dsimp [hi]
    rw [(downSet_cut_residues (π := π) (τ := τ) (j := j.val) hτdiv).2, hbase]
  have hpair := rankInterval_endpoint_pair s lo hi hspan hhiCard
  have hA : A.card = 32 := by simpa [A, downSetEndpointLeft, lo] using hpair.2.1
  have hB : B.card = 32 := by simpa [B, downSetEndpointRight, hi] using hpair.2.2.1
  have hsep : ∀ a ∈ A, ∀ b ∈ B, a < b := by
    intro a ha b hb
    exact rankInterval_endpoint_pair_ordered s lo hi hspan ha hb
  obtain ⟨hsA, hsB⟩ :=
    packetSortedOn_rankInterval_endpoints s v hpack lo hi hspan hlo hhi
  let net := repairOrderedHalfPair A B hA hB hsep
  have hmid : hi - 32 = lo + 32 + 64 * m := by
    dsimp [hi, lo]
    rw [hstep, hτ]
    omega
  refine ⟨net, repairOrderedHalfPair_depth_le A B hA hB hsep, ?_, ?_⟩
  · exact repairOrderedHalfPair_sorts A B hA hB hsep v hsA hsB
  · intro k
    have hsCell := downSetInteriorCell_sorted s π τ j m hτdiv hbase v hpack k
    intro x y hx hy hxy
    have hxBounds : lo + 32 ≤ Chvatal.rankIn s x ∧
        Chvatal.rankIn s x < hi - 32 := by
      have hr := Chvatal.mem_blockOf.mp hx
      have hk := k.isLt
      have hloCell : π / 2 + j.val * τ + 32 + 64 * k.val =
          lo + 32 + 64 * k.val := by simp [lo]
      have hhiCell : π / 2 + j.val * τ + 32 + 64 * (k.val + 1) =
          lo + 32 + 64 * (k.val + 1) := by simp [lo]
      rw [hloCell, hhiCell] at hr
      constructor
      · omega
      · calc
          Chvatal.rankIn s x < lo + 32 + 64 * (k.val + 1) := hr.2.2
          _ ≤ lo + 32 + 64 * m := by gcongr <;> omega
          _ = hi - 32 := hmid.symm
    have hyBounds : lo + 32 ≤ Chvatal.rankIn s y ∧
        Chvatal.rankIn s y < hi - 32 := by
      have hr := Chvatal.mem_blockOf.mp hy
      have hk := k.isLt
      have hloCell : π / 2 + j.val * τ + 32 + 64 * k.val =
          lo + 32 + 64 * k.val := by simp [lo]
      have hhiCell : π / 2 + j.val * τ + 32 + 64 * (k.val + 1) =
          lo + 32 + 64 * (k.val + 1) := by simp [lo]
      rw [hloCell, hhiCell] at hr
      constructor
      · omega
      · calc
          Chvatal.rankIn s y < lo + 32 + 64 * (k.val + 1) := hr.2.2
          _ ≤ lo + 32 + 64 * m := by gcongr <;> omega
          _ = hi - 32 := hmid.symm
    have hxOutside : x ∉ A ∪ B := by
      intro hxmem
      rcases Finset.mem_union.mp hxmem with hA' | hB'
      ·
        change x ∈ Chvatal.blockOf s lo (lo + 32) at hA'
        have hr := Chvatal.mem_blockOf.mp hA'
        omega
      ·
        change x ∈ Chvatal.blockOf s (hi - 32) hi at hB'
        have hr := Chvatal.mem_blockOf.mp hB'
        omega
    have hyOutside : y ∉ A ∪ B := by
      intro hymem
      rcases Finset.mem_union.mp hymem with hA' | hB'
      · change y ∈ Chvatal.blockOf s lo (lo + 32) at hA'
        have hr := Chvatal.mem_blockOf.mp hA'
        omega
      · change y ∈ Chvatal.blockOf s (hi - 32) hi at hB'
        have hr := Chvatal.mem_blockOf.mp hB'
        omega
    rw [repairOrderedHalfPair_exec_outside A B hA hB hsep v x hxOutside,
      repairOrderedHalfPair_exec_outside A B hA hB hsep v y hyOutside]
    exact hsCell hx hy hxy

theorem downSetEndpointLeft_card {N : Nat} (s : Finset (Fin N)) (π τ : Nat)
    (j : Fin 64) (hτlarge : 64 ≤ τ)
    (hwithin : π / 2 + 64 * τ ≤ s.card) :
    (downSetEndpointLeft s π τ j).card = 32 := by
  unfold downSetEndpointLeft
  have hj : j.val ≤ 63 := by omega
  have hmul : j.val * τ ≤ 63 * τ := Nat.mul_le_mul_right τ hj
  rw [Chvatal.blockOf_card (by
    omega)]
  omega

theorem downSetEndpointRight_card {N : Nat} (s : Finset (Fin N)) (π τ : Nat)
    (j : Fin 64) (hτ : 64 ∣ τ)
    (hbase : (π / 2) % 64 = 32)
    (hwithin : π / 2 + 64 * τ ≤ s.card) :
    (downSetEndpointRight s π τ j).card = 32 := by
  unfold downSetEndpointRight
  have hres : (π / 2 + (j.val + 1) * τ) % 64 = 32 :=
    by rw [(downSet_cut_residues (π := π) (τ := τ) (j := j.val) hτ).2, hbase]
  have hresLower :
      (π / 2 + (j.val + 1) * τ - 32) % 64 = 0 := by
    have hmod := Nat.mod_add_div (π / 2 + (j.val + 1) * τ) 64
    rw [hres] at hmod
    omega
  have hj : j.val + 1 ≤ 64 := by omega
  have hmul : (j.val + 1) * τ ≤ 64 * τ := Nat.mul_le_mul_right τ hj
  have hend : π / 2 + (j.val + 1) * τ ≤ s.card := by omega
  rw [Chvatal.blockOf_card (by omega)]
  omega

theorem downSetEndpoint_separated {N : Nat} (s : Finset (Fin N)) (π τ : Nat)
    (j : Fin 64) (hτlarge : 64 ≤ τ) :
    ∀ x ∈ downSetEndpointLeft s π τ j,
      ∀ y ∈ downSetEndpointRight s π τ j, x < y := by
  intro x hx y hy
  have hstep : (j.val + 1) * τ = j.val * τ + τ := by
    rw [Nat.add_mul, Nat.one_mul]
  unfold downSetEndpointLeft at hx
  unfold downSetEndpointRight at hy
  apply blockOf_lt_of_separated s
    (by omega : π / 2 + j.val * τ + 32 ≤ π / 2 + (j.val + 1) * τ - 32)
    hx hy

theorem downSetEndpointSupport_subset {N : Nat} (s : Finset (Fin N))
    (π τ : Nat) (i : Fin 64) (hτlarge : 64 ≤ τ) :
    downSetEndpointLeft s π τ i ∪ downSetEndpointRight s π τ i ⊆
      Chvatal.downSet s π τ i.val := by
  intro w hw
  have hstep : (i.val + 1) * τ = i.val * τ + τ := by
    rw [Nat.add_mul, Nat.one_mul]
  rcases Finset.mem_union.mp hw with hl | hr
  · unfold downSetEndpointLeft at hl
    unfold Chvatal.downSet
    apply Finset.mem_filter.mpr
    have h := Chvatal.mem_blockOf.mp hl
    refine ⟨h.1, h.2.1, ?_⟩
    have hi := i.isLt
    omega
  · unfold downSetEndpointRight at hr
    unfold Chvatal.downSet
    apply Finset.mem_filter.mpr
    have h := Chvatal.mem_blockOf.mp hr
    refine ⟨h.1, ?_, h.2.2⟩
    have hi := i.isLt
    omega

theorem downSetEndpointSupport_disjoint {N : Nat} (s : Finset (Fin N))
    (π τ : Nat) (j k : Fin 64) (hτlarge : 64 ≤ τ) (hjk : j ≠ k) :
    Disjoint
      (downSetEndpointLeft s π τ j ∪ downSetEndpointRight s π τ j)
      (downSetEndpointLeft s π τ k ∪ downSetEndpointRight s π τ k) := by
  have hsub (i : Fin 64) :
      downSetEndpointLeft s π τ i ∪ downSetEndpointRight s π τ i ⊆
        Chvatal.downSet s π τ i.val := by
    exact downSetEndpointSupport_subset s π τ i hτlarge
  have hneq : j.val ≠ k.val := by intro h; apply hjk; exact Fin.ext h
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · exact (Chvatal.disjoint_downSet (s := s) (π := π) (τ := τ)
      (j := j.val) (j' := k.val) hlt).mono
      (hsub j) (hsub k)
  · exact (Chvatal.disjoint_downSet (s := s) (π := π) (τ := τ)
      (j := k.val) (j' := j.val) hgt).symm.mono
      (hsub j) (hsub k)

/-- Both halves chosen by the actual shifted up-fringe lie within individual
source packets. The source packet invariant therefore sorts both runs. -/
theorem packetSortedOn_upFringe_endpoints {N : Nat} {α : Type} [Preorder α]
    (s : Finset (Fin N)) (v : Fin N → α) (hpack : PacketSortedOn s v)
    (π : Nat) (hcard64 : 64 ∣ s.card) (hhalf32 : (π / 2) % 64 = 32)
    (hπcard : π ≤ s.card) :
    RankSortedOn (Chvatal.blockOf s (π / 2 - 32) (π / 2)) v ∧
      RankSortedOn (Chvatal.blockOf s (s.card - π / 2) (s.card - π / 2 + 32)) v := by
  have hhalf : 32 ≤ π / 2 := by omega
  have hc0 : s.card % 64 = 0 := Nat.mod_eq_zero_of_dvd hcard64
  have hresA : (π / 2 - 32) % 64 = 0 := by omega
  have hresB : (s.card - π / 2) % 64 = 32 := by omega
  constructor
  · have heq : π / 2 - 32 + 32 = π / 2 := by omega
    simpa only [heq] using
      packetSortedOn_halfPacket s v hpack (π / 2 - 32) (Or.inl hresA)
  · exact packetSortedOn_halfPacket s v hpack (s.card - π / 2) (Or.inr hresB)

/-- The shifted up-fringe has a single fixed six-layer repair of its two
boundary half-packets. Values outside the pair support are unchanged. -/
theorem upFringe_endpoint_repair_exists {N : Nat}
    (s : Finset (Fin N)) (π : Nat) (hπeven : 2 ∣ π) (hcard64 : 64 ∣ s.card)
    (hhalf32 : (π / 2) % 64 = 32) (hπcard : π ≤ s.card) :
    ∃ net : ComparatorNetwork N, net.depth ≤ 6 ∧
      (∀ {α : Type} [LinearOrder α] (v : Fin N → α), PacketSortedOn s v →
        RankSortedOn (upFringePairSupport s π) (net.exec v)) ∧
      (∀ {α : Type} [LinearOrder α] (v : Fin N → α) (w : Fin N),
        w ∉ upFringePairSupport s π → net.exec v w = v w) := by
  let A := Chvatal.blockOf s (π / 2 - 32) (π / 2)
  let B := Chvatal.blockOf s (s.card - π / 2) (s.card - π / 2 + 32)
  have hc := upFringe_endpoint_pair s π hπeven hcard64 hhalf32 hπcard
  have hA : A.card = 32 := hc.2.1
  have hB : B.card = 32 := hc.2.2.1
  have hsep : ∀ a ∈ A, ∀ b ∈ B, a < b := by
    intro a ha b hb
    exact upFringe_endpoint_pair_ordered s π hπeven hhalf32 hπcard ha hb
  refine ⟨repairOrderedHalfPair A B hA hB hsep,
    repairOrderedHalfPair_depth_le A B hA hB hsep, ?_, ?_⟩
  · intro α _ v hp
    obtain ⟨hsA, hsB⟩ := packetSortedOn_upFringe_endpoints s v hp π hcard64 hhalf32 hπcard
    exact repairOrderedHalfPair_sorts A B hA hB hsep v hsA hsB
  · intro α _ v w hw
    exact repairOrderedHalfPair_exec_outside A B hA hB hsep v w hw

/-- All pair repairs can be listed sequentially while their disjoint wire
supports make the greedy network depth equal to at most six layers. -/
noncomputable def parallelHalfPairRepair {ι : Type} {N : Nat}
    (ids : List ι) (A B : ι → Finset (Fin N))
    (hA : ∀ a, (A a).card = 32) (hB : ∀ a, (B a).card = 32)
    (hsep : ∀ a, ∀ x ∈ A a, ∀ y ∈ B a, x < y) : ComparatorNetwork N :=
  ⟨ids.flatMap fun a => (repairOrderedHalfPair (A a) (B a) (hA a) (hB a) (hsep a)).comparators⟩

private theorem pairEmbedding_mem {N : Nat}
    (A B : Finset (Fin N)) (hA : A.card = 32) (hB : B.card = 32)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, a < b) (i : Fin 64) :
    orderedHalfPairEmbedding A B hA hB hsep i ∈ A ∪ B := by
  have hi : orderedHalfPairEmbedding A B hA hB hsep i ∈
      Set.range (orderedHalfPairEmbedding A B hA hB hsep) := ⟨i, rfl⟩
  rwa [orderedHalfPairEmbedding_range] at hi

theorem parallelHalfPairRepair_depth_le {ι : Type} {N : Nat}
    (ids : List ι) (hids : ids.Nodup) (A B : ι → Finset (Fin N))
    (hA : ∀ a, (A a).card = 32) (hB : ∀ a, (B a).card = 32)
    (hsep : ∀ a, ∀ x ∈ A a, ∀ y ∈ B a, x < y)
    (hdis : ∀ a ∈ ids, ∀ b ∈ ids, a ≠ b → Disjoint (A a ∪ B a) (A b ∪ B b)) :
    (parallelHalfPairRepair ids A B hA hB hsep).depth ≤ 6 := by
  apply depth_flatMap_disjoint ids
    (fun a => (repairOrderedHalfPair (A a) (B a) (hA a) (hB a) (hsep a)).comparators) 6
  · intro a _
    exact repairOrderedHalfPair_depth_le _ _ _ _ _
  · have hp := (List.nodup_iff_pairwise_ne).mp hids
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hne : ids[i] ≠ ids[j] := List.pairwise_iff_getElem.mp hp i j hi hj hij
    have hd := hdis ids[i] (List.getElem_mem hi) ids[j] (List.getElem_mem hj) hne
    intro c hc d hd'
    obtain ⟨c', _, rfl⟩ := List.mem_map.mp hc
    obtain ⟨d', _, rfl⟩ := List.mem_map.mp hd'
    have hn : ∀ x y,
        orderedHalfPairEmbedding (A ids[i]) (B ids[i]) (hA ids[i]) (hB ids[i]) (hsep ids[i]) x ≠
          orderedHalfPairEmbedding (A ids[j]) (B ids[j]) (hA ids[j]) (hB ids[j]) (hsep ids[j]) y := by
      intro x y heq
      exact Finset.disjoint_left.mp hd (pairEmbedding_mem _ _ _ _ _ x)
        (heq ▸ pairEmbedding_mem _ _ _ _ _ y)
    exact ⟨⟨hn _ _, hn _ _⟩, ⟨hn _ _, hn _ _⟩⟩

theorem parallelHalfPairRepair_exec_inside {ι : Type} [DecidableEq ι]
    {N : Nat} {α : Type} [LinearOrder α]
    (ids : List ι) (hids : ids.Nodup) (A B : ι → Finset (Fin N))
    (hA : ∀ a, (A a).card = 32) (hB : ∀ a, (B a).card = 32)
    (hsep : ∀ a, ∀ x ∈ A a, ∀ y ∈ B a, x < y)
    (hdis : ∀ a ∈ ids, ∀ b ∈ ids, a ≠ b → Disjoint (A a ∪ B a) (A b ∪ B b))
    (v : Fin N → α) (a : ι) (ha : a ∈ ids) (i : Fin 64) :
    (parallelHalfPairRepair ids A B hA hB hsep).exec v
        (orderedHalfPairEmbedding (A a) (B a) (hA a) (hB a) (hsep a) i) =
      (oddEvenMergeNet 6).exec
        (v ∘ orderedHalfPairEmbedding (A a) (B a) (hA a) (hB a) (hsep a)) i := by
  unfold parallelHalfPairRepair repairOrderedHalfPair
  rw [ComparatorNetwork.exec_flatMap]
  apply Chvatal.flatMap_scatter_exec_inside (m := fun _ : ι => 64)
    (fun a => orderedHalfPairEmbedding (A a) (B a) (hA a) (hB a) (hsep a))
    (fun _ => oddEvenMergeNet 6) ids v hids ?_ a ha i
  intro x hx y hy hne p q heq
  exact Finset.disjoint_left.mp (hdis x hx y hy hne) (pairEmbedding_mem _ _ _ _ _ p)
    (heq ▸ pairEmbedding_mem _ _ _ _ _ q)

theorem parallelHalfPairRepair_exec_outside {ι : Type} {N : Nat}
    {α : Type} [LinearOrder α]
    (ids : List ι) (A B : ι → Finset (Fin N))
    (hA : ∀ a, (A a).card = 32) (hB : ∀ a, (B a).card = 32)
    (hsep : ∀ a, ∀ x ∈ A a, ∀ y ∈ B a, x < y)
    (v : Fin N → α) (w : Fin N)
    (hw : ∀ a ∈ ids, w ∉ A a ∪ B a) :
    (parallelHalfPairRepair ids A B hA hB hsep).exec v w = v w := by
  unfold parallelHalfPairRepair repairOrderedHalfPair
  rw [ComparatorNetwork.exec_flatMap]
  apply ComparatorNetwork.foldl_exec_outside ids
    (fun a => (oddEvenMergeNet 6).scatterEmbed N
      (orderedHalfPairEmbedding (A a) (B a) (hA a) (hB a) (hsep a))) v w
  intro a ha c hc
  have hnot : w ∉ Set.range
      (orderedHalfPairEmbedding (A a) (B a) (hA a) (hB a) (hsep a) : Fin 64 ↪o Fin N) := by
    rw [orderedHalfPairEmbedding_range]
    exact hw a ha
  exact ComparatorNetwork.scatterEmbed_comparators_outside _ _ _ w hnot c hc

theorem parallelHalfPairRepair_sorts_pair {ι : Type} [DecidableEq ι]
    {N : Nat} {α : Type} [LinearOrder α]
    (ids : List ι) (hids : ids.Nodup) (A B : ι → Finset (Fin N))
    (hA : ∀ a, (A a).card = 32) (hB : ∀ a, (B a).card = 32)
    (hsep : ∀ a, ∀ x ∈ A a, ∀ y ∈ B a, x < y)
    (hdis : ∀ a ∈ ids, ∀ b ∈ ids, a ≠ b → Disjoint (A a ∪ B a) (A b ∪ B b))
    (v : Fin N → α) (a : ι) (ha : a ∈ ids)
    (hsA : RankSortedOn (A a) v) (hsB : RankSortedOn (B a) v) :
    RankSortedOn (A a ∪ B a) ((parallelHalfPairRepair ids A B hA hB hsep).exec v) := by
  have hs := repairOrderedHalfPair_sorts (A a) (B a) (hA a) (hB a) (hsep a) v hsA hsB
  have heq : ∀ w ∈ A a ∪ B a,
      (parallelHalfPairRepair ids A B hA hB hsep).exec v w =
        (repairOrderedHalfPair (A a) (B a) (hA a) (hB a) (hsep a)).exec v w := by
    intro w hw
    have hw' : w ∈ Set.range (orderedHalfPairEmbedding (A a) (B a) (hA a) (hB a) (hsep a)) := by
      rw [orderedHalfPairEmbedding_range]
      exact hw
    obtain ⟨i, rfl⟩ := hw'
    rw [parallelHalfPairRepair_exec_inside ids hids A B hA hB hsep hdis v a ha i]
    exact (ComparatorNetwork.scatterEmbed_exec_inside _ _ _ _ _).symm
  intro x y hx hy hxy
  rw [heq x hx, heq y hy]
  exact hs hx hy hxy

/-- A whole disjoint cohort of shifted sender up-fringes can repair its
endpoint half-packets in parallel. Each sender contributes one pair; no
physical order between different senders is needed. -/
theorem parallelUpFringeEndpointRepair_exists {ι : Type} [DecidableEq ι]
    {N : Nat} {α : Type} [LinearOrder α]
    (ids : List ι) (hids : ids.Nodup) (s : ι → Finset (Fin N)) (π : Nat)
    (hcard : ∀ i, 64 ∣ (s i).card)
    (heven : 2 ∣ π) (hhalf : (π / 2) % 64 = 32)
    (hπcard : ∀ i, π ≤ (s i).card)
    (hsourceDisjoint : ∀ i ∈ ids, ∀ j ∈ ids, i ≠ j → Disjoint (s i) (s j)) :
    ∃ net : ComparatorNetwork N, net.depth ≤ 6 ∧
      ∀ v : Fin N → α, (∀ i ∈ ids, PacketSortedOn (s i) v) →
        ∀ i ∈ ids,
          RankSortedOn (upFringePairSupport (s i) π) (net.exec v) := by
  let A (i : ι) := Chvatal.blockOf (s i) (π / 2 - 32) (π / 2)
  let B (i : ι) := Chvatal.blockOf (s i) ((s i).card - π / 2)
    ((s i).card - π / 2 + 32)
  have hA : ∀ i, (A i).card = 32 := by
    intro i
    have hp := upFringe_endpoint_pair (s i) π heven (hcard i) hhalf (hπcard i)
    simpa [A] using hp.2.1
  have hB : ∀ i, (B i).card = 32 := by
    intro i
    have hp := upFringe_endpoint_pair (s i) π heven (hcard i) hhalf (hπcard i)
    simpa [B] using hp.2.2.1
  have hsep : ∀ i, ∀ x ∈ A i, ∀ y ∈ B i, x < y := by
    intro i x hx y hy
    exact upFringe_endpoint_pair_ordered (s i) π heven hhalf (hπcard i) hx hy
  have hdis : ∀ i ∈ ids, ∀ j ∈ ids, i ≠ j →
      Disjoint (A i ∪ B i) (A j ∪ B j) := by
    intro i hi j hj hne
    exact (hsourceDisjoint i hi j hj hne).mono
      (by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact Chvatal.blockOf_subset hw
        · exact Chvatal.blockOf_subset hw)
      (by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact Chvatal.blockOf_subset hw
        · exact Chvatal.blockOf_subset hw)
  refine ⟨parallelHalfPairRepair ids A B hA hB hsep, ?_, ?_⟩
  · exact parallelHalfPairRepair_depth_le ids hids A B hA hB hsep hdis
  · intro v hsorted i hi
    apply parallelHalfPairRepair_sorts_pair ids hids A B hA hB hsep hdis v i hi
    · exact (packetSortedOn_upFringe_endpoints (s i) v (hsorted i hi) π
        (hcard i) hhalf (hπcard i)).1
    · exact (packetSortedOn_upFringe_endpoints (s i) v (hsorted i hi) π
        (hcard i) hhalf (hπcard i)).2

/-- All 64 child cuts of a shifted parent can repair their endpoint
half-packets concurrently. The supports are disjoint, the depth is six, and
each repaired support is sorted whenever the parent packets were sorted. -/
theorem parallelDownSetEndpointRepair_exists {N : Nat} {α : Type}
    [LinearOrder α] (s : Finset (Fin N)) (π τ : Nat)
    (hτ : 64 ∣ τ) (hτlarge : 64 ≤ τ)
    (hbase : (π / 2) % 64 = 32)
    (hwithin : π / 2 + 64 * τ ≤ s.card) :
    ∃ net : ComparatorNetwork N, net.depth ≤ 6 ∧
      ∀ v : Fin N → α, PacketSortedOn s v → ∀ j : Fin 64,
        RankSortedOn
          (downSetEndpointLeft s π τ j ∪ downSetEndpointRight s π τ j)
          (net.exec v) := by
  let A := downSetEndpointLeft s π τ
  let B := downSetEndpointRight s π τ
  have hA : ∀ j : Fin 64, (A j).card = 32 := by
    intro j
    exact downSetEndpointLeft_card s π τ j hτlarge hwithin
  have hB : ∀ j : Fin 64, (B j).card = 32 := by
    intro j
    exact downSetEndpointRight_card s π τ j hτ hbase hwithin
  have hsep : ∀ j : Fin 64, ∀ x ∈ A j, ∀ y ∈ B j, x < y := by
    intro j
    exact downSetEndpoint_separated s π τ j hτlarge
  have hdis : ∀ j ∈ List.finRange 64, ∀ k ∈ List.finRange 64,
      j ≠ k → Disjoint (A j ∪ B j) (A k ∪ B k) := by
    intro j hj k hk hjk
    exact downSetEndpointSupport_disjoint s π τ j k hτlarge hjk
  refine ⟨parallelHalfPairRepair (List.finRange 64) A B hA hB hsep, ?_, ?_⟩
  · exact parallelHalfPairRepair_depth_le (List.finRange 64)
      (List.nodup_finRange 64) A B hA hB hsep hdis
  · intro v hpack j
    apply parallelHalfPairRepair_sorts_pair (List.finRange 64)
      (List.nodup_finRange 64) A B hA hB hsep hdis v j (by simp)
    · have hlo := (downSet_cut_residues (π := π) (τ := τ) (j := j.val) hτ).1
      rw [hbase] at hlo
      have hruns := packetSortedOn_rankInterval_endpoints s v hpack
        (π / 2 + j.val * τ) (π / 2 + (j.val + 1) * τ)
        (by
          have hstep : (j.val + 1) * τ = j.val * τ + τ := by
            rw [Nat.add_mul, Nat.one_mul]
          omega) hlo (by
            have hhi := (downSet_cut_residues
              (π := π) (τ := τ) (j := j.val) hτ).2
            rw [hbase] at hhi
            exact hhi)
      simpa [A, downSetEndpointLeft] using hruns.1
    · have hhi := (downSet_cut_residues (π := π) (τ := τ) (j := j.val) hτ).2
      rw [hbase] at hhi
      have hruns := packetSortedOn_rankInterval_endpoints s v hpack
        (π / 2 + j.val * τ) (π / 2 + (j.val + 1) * τ)
        (by
          have hstep : (j.val + 1) * τ = j.val * τ + τ := by
            rw [Nat.add_mul, Nat.one_mul]
          omega)
        (by
          have hlo := (downSet_cut_residues
            (π := π) (τ := τ) (j := j.val) hτ).1
          rw [hbase] at hlo
          exact hlo) hhi
      simpa [B, downSetEndpointRight] using hruns.2

/-- The full 64-cut repair leaves each parent down-port partitioned into
sorted 64-wire packets: one repaired endpoint pair and all original interior
cells. This is the local packet-layout induction step for a shifted sender. -/
theorem parallelDownSetEndpointRepair_packetLayout {N : Nat} {α : Type}
    [LinearOrder α] (s : Finset (Fin N)) (π τ : Nat) (m : Nat)
    (hτ : τ = 64 * (m + 1)) (hbase : (π / 2) % 64 = 32)
    (hwithin : π / 2 + 64 * τ ≤ s.card) :
    ∃ net : ComparatorNetwork N, net.depth ≤ 6 ∧
      ∀ v : Fin N → α, PacketSortedOn s v → ∀ j : Fin 64,
        RankSortedOn
          (downSetEndpointLeft s π τ j ∪ downSetEndpointRight s π τ j)
          (net.exec v) ∧
        ∀ k : Fin m,
          RankSortedOn (downSetInteriorCell s π τ j m k) (net.exec v) := by
  classical
  let A := downSetEndpointLeft s π τ
  let B := downSetEndpointRight s π τ
  have hτdiv : 64 ∣ τ := by rw [hτ]; exact ⟨m + 1, rfl⟩
  have hτlarge : 64 ≤ τ := by rw [hτ]; omega
  have hA : ∀ j : Fin 64, (A j).card = 32 := by
    intro j
    exact downSetEndpointLeft_card s π τ j hτlarge hwithin
  have hB : ∀ j : Fin 64, (B j).card = 32 := by
    intro j
    exact downSetEndpointRight_card s π τ j hτdiv hbase hwithin
  have hsep : ∀ j : Fin 64, ∀ x ∈ A j, ∀ y ∈ B j, x < y := by
    intro j
    exact downSetEndpoint_separated s π τ j hτlarge
  have hdis : ∀ j ∈ List.finRange 64, ∀ k ∈ List.finRange 64,
      j ≠ k → Disjoint (A j ∪ B j) (A k ∪ B k) := by
    intro j hj k hk hjk
    exact downSetEndpointSupport_disjoint s π τ j k hτlarge hjk
  let net := parallelHalfPairRepair (List.finRange 64) A B hA hB hsep
  have hdepth : net.depth ≤ 6 := by
    exact parallelHalfPairRepair_depth_le (List.finRange 64)
      (List.nodup_finRange 64) A B hA hB hsep hdis
  refine ⟨net, hdepth, ?_⟩
  intro v hpack j
  have hendpoint : RankSortedOn (A j ∪ B j) (net.exec v) := by
    apply parallelHalfPairRepair_sorts_pair (List.finRange 64)
      (List.nodup_finRange 64) A B hA hB hsep hdis v j (by simp)
    · have hlo := (downSet_cut_residues (π := π) (τ := τ) (j := j.val) hτdiv).1
      rw [hbase] at hlo
      have hhi := (downSet_cut_residues (π := π) (τ := τ) (j := j.val) hτdiv).2
      rw [hbase] at hhi
      have hstep : (j.val + 1) * τ = j.val * τ + τ := by
        rw [Nat.add_mul, Nat.one_mul]
      have hspan : 64 ≤ (π / 2 + (j.val + 1) * τ) - (π / 2 + j.val * τ) := by
        rw [hstep, hτ]
        omega
      have hruns := packetSortedOn_rankInterval_endpoints s v hpack
        (π / 2 + j.val * τ) (π / 2 + (j.val + 1) * τ) hspan hlo hhi
      simpa [A, downSetEndpointLeft] using hruns.1
    · have hlo := (downSet_cut_residues (π := π) (τ := τ) (j := j.val) hτdiv).1
      rw [hbase] at hlo
      have hhi := (downSet_cut_residues (π := π) (τ := τ) (j := j.val) hτdiv).2
      rw [hbase] at hhi
      have hstep : (j.val + 1) * τ = j.val * τ + τ := by
        rw [Nat.add_mul, Nat.one_mul]
      have hspan : 64 ≤ (π / 2 + (j.val + 1) * τ) - (π / 2 + j.val * τ) := by
        rw [hstep, hτ]
        omega
      have hruns := packetSortedOn_rankInterval_endpoints s v hpack
        (π / 2 + j.val * τ) (π / 2 + (j.val + 1) * τ) hspan hlo hhi
      simpa [B, downSetEndpointRight] using hruns.2
  refine ⟨by simpa [A, B] using hendpoint, ?_⟩
  intro k
  have hsCell := downSetInteriorCell_sorted s π τ j m hτdiv hbase v hpack k
  have hwDown (w : Fin N) (hw : w ∈ downSetInteriorCell s π τ j m k) :
      w ∈ Chvatal.downSet s π τ j.val := by
    rw [downSetEndpoint_partition s π τ j m hτ]
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hw⟩
  have houtside (w : Fin N) (hw : w ∈ downSetInteriorCell s π τ j m k) :
      ∀ i ∈ List.finRange 64, w ∉ A i ∪ B i := by
    intro i hi hmem
    by_cases hij : i = j
    · subst i
      rcases Finset.mem_union.mp hmem with hA' | hB'
      · have hb := downSetInteriorCell_bounds s π τ j m hτ k w hw
        change w ∈ Chvatal.blockOf s (π / 2 + j.val * τ)
          (π / 2 + j.val * τ + 32) at hA'
        have hr := Chvatal.mem_blockOf.mp hA'
        omega
      · have hb := downSetInteriorCell_bounds s π τ j m hτ k w hw
        change w ∈ Chvatal.blockOf s
          (π / 2 + (j.val + 1) * τ - 32) (π / 2 + (j.val + 1) * τ) at hB'
        have hr := Chvatal.mem_blockOf.mp hB'
        omega
    · have hdisj : Disjoint (Chvatal.downSet s π τ j.val)
        (Chvatal.downSet s π τ i.val) := by
        have hne : j.val ≠ i.val := by intro h; apply hij; exact Fin.ext h.symm
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact Chvatal.disjoint_downSet (j := j.val) (j' := i.val) hlt
        · exact (Chvatal.disjoint_downSet (j := i.val) (j' := j.val) hgt).symm
      exact (Finset.disjoint_left.mp hdisj (hwDown w hw)
        (downSetEndpointSupport_subset s π τ i hτlarge hmem))
  intro x y hx hy hxy
  have hxEq := parallelHalfPairRepair_exec_outside
    (List.finRange 64) A B hA hB hsep v x (houtside x hx)
  have hyEq := parallelHalfPairRepair_exec_outside
    (List.finRange 64) A B hA hB hsep v y (houtside y hy)
  rw [hxEq, hyEq]
  exact hsCell hx hy hxy

/-- Instantiate the parent-cut correction on an actual ordinary `FlowSizes7`
sender. The refined node classification supplies packet divisibility of the
child flow; `hsplit` supplies the exact sender capacity. -/
theorem flowA7_scheduled_parent_endpoint_repair {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d)
    (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (q : KBag 64 d) (hτpos : 0 < flowDown7 d hd q.l t)
    (hbad : HalfMisaligned (flowUp7 d hd q.l t)) :
    ∃ net : ComparatorNetwork (64 ^ d), net.depth ≤ 6 ∧
      ∀ v : Fin (64 ^ d) → α, PacketSortedOn (wireSets (flowSizes7 d hd) t q) v →
        ∀ j : Fin 64,
          RankSortedOn
            (downSetEndpointLeft (wireSets (flowSizes7 d hd) t q)
                (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j ∪
              downSetEndpointRight (wireSets (flowSizes7 d hd) t q)
                (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j)
            (net.exec v) := by
  let F := flowSizes7 d hd
  let s := wireSets F t q
  let π := flowUp7 d hd q.l t
  let τ := flowDown7 d hd q.l t
  have hshape := node_shape_refined d hd t q.l ht2 ht
  have hres := refined_packet_residues hd ht2 ht hshape
  have hτ : 64 ∣ τ := by
    dsimp [τ]
    exact hres.2.1
  have hτlarge : 64 ≤ τ := Nat.le_of_dvd (by simpa [τ] using hτpos) hτ
  have hbase : (π / 2) % 64 = 32 := hbad.2
  have hsize : s.card = π + 64 * τ := by
    dsimp [s, F, π, τ]
    rw [wireSets_card _ (Nat.le_of_lt ht) q]
    exact F.hsplit q.l t q.hl ht
  have hwithin : π / 2 + 64 * τ ≤ s.card := by
    rw [hsize]
    omega
  exact parallelDownSetEndpointRepair_exists s π τ hτ hτlarge hbase hwithin

/-- Actual scheduled version of `parallelDownSetEndpointRepair_packetLayout`:
all 64 child down-ports of a shifted ordinary sender become partitions into
sorted 64-wire packets after one six-layer correction. -/
theorem flowA7_scheduled_parent_endpoint_packetLayout {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d)
    (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (q : KBag 64 d) (hτpos : 0 < flowDown7 d hd q.l t)
    (hbad : HalfMisaligned (flowUp7 d hd q.l t)) :
    ∃ net : ComparatorNetwork (64 ^ d), net.depth ≤ 6 ∧
      ∀ v : Fin (64 ^ d) → α, PacketSortedOn (wireSets (flowSizes7 d hd) t q) v →
        ∀ j : Fin 64,
          RankSortedOn
            (downSetEndpointLeft (wireSets (flowSizes7 d hd) t q)
                (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j ∪
              downSetEndpointRight (wireSets (flowSizes7 d hd) t q)
                (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j)
            (net.exec v) ∧
          ∀ k : Fin (flowDown7 d hd q.l t / 64 - 1),
            RankSortedOn
              (downSetInteriorCell (wireSets (flowSizes7 d hd) t q)
                (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j
                (flowDown7 d hd q.l t / 64 - 1) k) (net.exec v) := by
  let F := flowSizes7 d hd
  let s := wireSets F t q
  let π := flowUp7 d hd q.l t
  let τ := flowDown7 d hd q.l t
  have hshape := node_shape_refined d hd t q.l ht2 ht
  have hres := refined_packet_residues hd ht2 ht hshape
  have hτdiv : 64 ∣ τ := by dsimp [τ]; exact hres.2.1
  have hτlarge : 64 ≤ τ := Nat.le_of_dvd (by simpa [τ] using hτpos) hτdiv
  let m := τ / 64 - 1
  have hτeq : τ = 64 * (m + 1) := by
    have hmod := Nat.mod_add_div τ 64
    have hrem : τ % 64 = 0 := Nat.mod_eq_zero_of_dvd hτdiv
    rw [hrem] at hmod
    dsimp [m]
    omega
  have hbase : (π / 2) % 64 = 32 := hbad.2
  have hsize : s.card = π + 64 * τ := by
    dsimp [s, F, π, τ]
    rw [wireSets_card _ (Nat.le_of_lt ht) q]
    exact F.hsplit q.l t q.hl ht
  have hwithin : π / 2 + 64 * τ ≤ s.card := by rw [hsize]; omega
  obtain ⟨net, hdepth, hlayout⟩ :=
    parallelDownSetEndpointRepair_packetLayout (α := α) s π τ m hτeq hbase hwithin
  refine ⟨net, hdepth, ?_⟩
  intro v hv j
  have h := hlayout v hv j
  simpa [s, π, τ, m] using h

/-- At an actual receiver, the 64 child senders' shifted up-fringe endpoint
repairs are also one six-layer disjoint family. The packet divisibility,
fringe parity, capacity, and sender disjointness all come from the checked
`FlowSizes7` invariants. -/
theorem flowA7_receiver_child_up_endpoint_repair {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d) (hchild : b.l < d)
    (hbad : HalfMisaligned (flowUp7 d hd (b.l + 1) t)) :
    ∃ net : ComparatorNetwork (64 ^ d), net.depth ≤ 6 ∧
      ∀ v : Fin (64 ^ d) → α,
        (∀ j : Fin 64,
          PacketSortedOn
            (wireSets (flowSizes7 d hd) t (b.child j.val j.isLt hchild)) v) →
        ∀ j : Fin 64,
          RankSortedOn
            (upFringePairSupport
              (wireSets (flowSizes7 d hd) t (b.child j.val j.isLt hchild))
              (flowUp7 d hd (b.l + 1) t)) (net.exec v) := by
  let F := flowSizes7 d hd
  let s (j : Fin 64) := wireSets F t (b.child j.val j.isLt hchild)
  let π := flowUp7 d hd (b.l + 1) t
  have hcard : ∀ j : Fin 64, 64 ∣ (s j).card := by
    intro j
    have hshape := node_shape_refined d hd t (b.l + 1) ht2 ht
    have hres := refined_packet_residues hd ht2 ht hshape
    rw [wireSets_card F (Nat.le_of_lt ht)]
    dsimp [s, F, flowSizes7]
    exact hres.1
  have heven : 2 ∣ π := by
    dsimp [π]
    exact F.hup_even (b.l + 1) t ht
  have hπcard : ∀ j : Fin 64, π ≤ (s j).card := by
    intro j
    have hsize : (s j).card = π + 64 * flowDown7 d hd (b.l + 1) t := by
      dsimp [s, F, π]
      rw [wireSets_card F (Nat.le_of_lt ht)]
      exact F.hsplit (b.child j.val j.isLt hchild).l t
        (b.child j.val j.isLt hchild).hl ht
    omega
  have hdis : ∀ j ∈ List.finRange 64, ∀ k ∈ List.finRange 64,
      j ≠ k → Disjoint (s j) (s k) := by
    intro j hj k hk hne
    apply wireSets_disjoint F (Nat.le_of_lt ht)
    intro heq
    apply hne
    exact Fin.ext (KBag.child_inj b j.val k.val j.isLt k.isLt hchild heq)
  have hhalf : (π / 2) % 64 = 32 := hbad.2
  obtain ⟨net, hdepth, hsort⟩ :=
    parallelUpFringeEndpointRepair_exists (α := α) (List.finRange 64)
      (List.nodup_finRange 64) s π hcard heven hhalf hπcard hdis
  refine ⟨net, hdepth, ?_⟩
  intro v hv j
  have hsorted : ∀ i ∈ List.finRange 64, PacketSortedOn (s i) v := by
    intro i hi
    simpa [s] using hv i
  have h := hsort v hsorted j (by simp)
  simpa [upFringePairSupport, s, π] using h

end Chvatal.PacketAlignment
