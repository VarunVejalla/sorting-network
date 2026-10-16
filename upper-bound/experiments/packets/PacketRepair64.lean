import OddEvenMerge64
import PacketAlignment
import AKS.Chvatal.StageNet
import AKS.Chvatal.ExecPlacement

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

/-- Packet sortedness on physical wires is the same invariant in the bag's
rank-order register coordinates. -/
theorem PacketSortedOn_orderEmb {N : Nat} {α : Type} [Preorder α]
    (s : Finset (Fin N)) (v : Fin N → α)
    (hpack : PacketSortedOn s v) :
    PacketSortedOn (Finset.univ : Finset (Fin s.card))
      (fun i => v (s.orderEmbOfFin rfl i)) := by
  intro p x y hx hy hxy
  rw [Chvatal.mem_blockOf] at hx hy
  have hxrank : Chvatal.rankIn (Finset.univ : Finset (Fin s.card)) x = x.val := by
    change ((Finset.univ : Finset (Fin s.card)).filter (fun z => z < x)).card = x.val
    have hfilter : (Finset.univ : Finset (Fin s.card)).filter (fun z => z < x) = Finset.Iio x := by
      ext z
      simp
    rw [hfilter]
    exact Fin.card_Iio x
  have hyrank : Chvatal.rankIn (Finset.univ : Finset (Fin s.card)) y = y.val := by
    change ((Finset.univ : Finset (Fin s.card)).filter (fun z => z < y)).card = y.val
    have hfilter : (Finset.univ : Finset (Fin s.card)).filter (fun z => z < y) = Finset.Iio y := by
      ext z
      simp
    rw [hfilter]
    exact Fin.card_Iio y
  rw [hxrank] at hx
  rw [hyrank] at hy
  have hxlo : 64 * p ≤ x.val := hx.2.1
  have hxhi : x.val < 64 * (p + 1) := hx.2.2
  have hylo : 64 * p ≤ y.val := hy.2.1
  have hyhi : y.val < 64 * (p + 1) := hy.2.2
  have hxe : s.orderEmbOfFin rfl x ∈ Chvatal.blockOf s (64 * p) (64 * (p + 1)) := by
    rw [Chvatal.mem_blockOf, Chvatal.rankIn_orderEmb]
    exact ⟨Finset.orderEmbOfFin_mem s rfl x, hxlo, hxhi⟩
  have hye : s.orderEmbOfFin rfl y ∈ Chvatal.blockOf s (64 * p) (64 * (p + 1)) := by
    rw [Chvatal.mem_blockOf, Chvatal.rankIn_orderEmb]
    exact ⟨Finset.orderEmbOfFin_mem s rfl y, hylo, hyhi⟩
  have hxy' : (s.orderEmbOfFin rfl x).val ≤ (s.orderEmbOfFin rfl y).val := by
    exact Fin.le_def.mp ((s.orderEmbOfFin rfl).monotone (Fin.le_def.mpr hxy))
  exact hpack p hxe hye hxy'

/-- Register-coordinate packet sortedness when the register size is given by
a proved cardinality equality. -/
theorem PacketSortedOn_orderEmb_of_card_eq {N n : Nat} {α : Type}
    [Preorder α] (s : Finset (Fin N)) (v : Fin N → α)
    (hpack : PacketSortedOn s v) (hn : s.card = n) :
    PacketSortedOn (Finset.univ : Finset (Fin n))
      (fun i => v (s.orderEmbOfFin hn i)) := by
  cases hn
  exact PacketSortedOn_orderEmb s v hpack

theorem rankIn_univ_eq_val {n : Nat} (i : Fin n) :
    Chvatal.rankIn (Finset.univ : Finset (Fin n)) i = i.val := by
  change ((Finset.univ : Finset (Fin n)).filter (fun z => z < i)).card = i.val
  have hfilter : (Finset.univ : Finset (Fin n)).filter (fun z => z < i) =
      Finset.Iio i := by
    ext z
    simp
  rw [hfilter]
  exact Fin.card_Iio i

/-- A register rank interval maps to the matching physical `WireFlow` rank
block under the bag's increasing enumeration. -/
theorem blockOf_register_image {N n : Nat} (s : Finset (Fin N))
    (hn : s.card = n) (lo hi : Nat) :
    (Chvatal.blockOf (Finset.univ : Finset (Fin n)) lo hi).image
      (s.orderEmbOfFin hn) = Chvatal.blockOf s lo hi := by
  cases hn
  ext w
  simp only [Finset.mem_image, Chvatal.mem_blockOf]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases hi with ⟨_, hlo, hhi⟩
    rw [rankIn_univ_eq_val] at hlo hhi
    rw [Chvatal.rankIn_orderEmb]
    exact ⟨Finset.orderEmbOfFin_mem s rfl i, hlo, hhi⟩
  · rintro ⟨hw, hlo, hhi⟩
    obtain ⟨i, rfl⟩ : w ∈ Set.range (s.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hw
    refine ⟨i, ?_, rfl⟩
    rw [Chvatal.rankIn_orderEmb] at hlo hhi
    exact ⟨Finset.mem_univ _, by simpa [rankIn_univ_eq_val] using hlo,
      by simpa [rankIn_univ_eq_val] using hhi⟩

/-- A linear-order sortedness claim follows if every lower-threshold Boolean
profile is sorted. -/
theorem rankSortedOn_of_thresholds {N : Nat} {α : Type} [LinearOrder α]
    (A : Finset (Fin N)) (v : Fin N → α)
    (hthreshold : ∀ t : α,
      RankSortedOn A (fun w => decide (t ≤ v w))) : RankSortedOn A v := by
  intro x y hx hy hxy
  by_contra hnot
  have hyx : v y < v x := lt_of_not_ge hnot
  have hbool := hthreshold (v x) (x := x) (y := y) hx hy hxy
  have hxBool : decide (v x ≤ v x) = true := decide_eq_true le_rfl
  have hyBool : decide (v x ≤ v y) = false := decide_eq_false (not_le_of_gt hyx)
  have hcontra : (true : Bool) ≤ false := by
    simpa only [hxBool, hyBool] using hbool
  exact (by decide : ¬ ((true : Bool) ≤ false)) hcontra

/-- A sorted register support stays sorted when `stageNet` embeds the node
network along the bag's increasing rank-order map. -/
theorem stageNet_rankSortedOn_image {d : Nat} {α : Type} [LinearOrder α]
    (S : KBag 64 d → Finset (Fin (64 ^ d)))
    (hS : ∀ b b', b ≠ b' → Disjoint (S b) (S b'))
    (nodeNet : (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Fin (64 ^ d) → α) (b : KBag 64 d)
    (A : Finset (Fin (S b).card))
    (hsorted : RankSortedOn A
      ((nodeNet b (S b).card).exec (fun i => v ((S b).orderEmbOfFin rfl i)))) :
    RankSortedOn (A.image ((S b).orderEmbOfFin rfl))
      ((stageNet S nodeNet).exec v) := by
  intro x y hx hy hxy
  rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
  have hij : i.val ≤ j.val := by
    by_contra hnot
    have hji : j < i := Fin.lt_def.mpr (by omega)
    have hstrict := (S b).orderEmbOfFin rfl |>.strictMono hji
    have hnotle : ¬ (S b).orderEmbOfFin rfl i ≤ (S b).orderEmbOfFin rfl j :=
      not_le_of_gt hstrict
    exact hnotle (Fin.le_def.mpr hxy)
  rw [stageNet_exec_inside S hS nodeNet v b i,
    stageNet_exec_inside S hS nodeNet v b j]
  exact hsorted hi hj hij

/-- The same transport works when a node network is specified at an index
`n` propositionally equal to the bag cardinality. -/
theorem stageNet_rankSortedOn_image_of_card_eq {d : Nat} {α : Type}
    [LinearOrder α] (S : KBag 64 d → Finset (Fin (64 ^ d)))
    (hS : ∀ b b', b ≠ b' → Disjoint (S b) (S b'))
    (nodeNet : (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Fin (64 ^ d) → α) (b : KBag 64 d) (n : Nat)
    (hn : (S b).card = n) (A : Finset (Fin n))
    (hsorted : RankSortedOn A
      ((nodeNet b n).exec (fun i => v ((S b).orderEmbOfFin hn i)))) :
    RankSortedOn (A.image ((S b).orderEmbOfFin hn))
      ((stageNet S nodeNet).exec v) := by
  cases hn
  exact stageNet_rankSortedOn_image S hS nodeNet v b A hsorted

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

/-- The rank interval `[lo, lo + 64*q)` is the disjoint union of its
consecutive 64-wire cells. -/
def rankPacketCell {N : Nat} (s : Finset (Fin N)) (lo : Nat)
    {q : Nat} (k : Fin q) : Finset (Fin N) :=
  Chvatal.blockOf s (lo + 64 * k.val) (lo + 64 * (k.val + 1))

theorem blockOf_packetCell_partition {N : Nat} (s : Finset (Fin N))
    (lo q : Nat) :
    Chvatal.blockOf s lo (lo + 64 * q) =
      Finset.univ.biUnion (fun k : Fin q => rankPacketCell s lo k) := by
  classical
  ext w
  simp only [Chvatal.blockOf, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_univ, true_and, rankPacketCell]
  constructor
  · rintro ⟨hw, hlo, hhi⟩
    let k := (Chvatal.rankIn s w - lo) / 64
    have hk : k < q := by
      dsimp [k]
      apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 64)).2
      omega
    refine ⟨⟨k, hk⟩, hw, ?_, ?_⟩
    · have hdecomp := Nat.mod_add_div (Chvatal.rankIn s w - lo) 64
      dsimp [k]
      omega
    · have hdecomp := Nat.mod_add_div (Chvatal.rankIn s w - lo) 64
      dsimp [k]
      omega
  · rintro ⟨k, hw, hlo, hhi⟩
    have hk := k.isLt
    exact ⟨hw, by omega, by omega⟩

def upSetPrefixCell {N : Nat} (s : Finset (Fin N)) {q : Nat}
    (k : Fin q) : Finset (Fin N) := rankPacketCell s 0 k

def upSetSuffixCell {N : Nat} (s : Finset (Fin N)) (π : Nat) {q : Nat}
    (k : Fin q) : Finset (Fin N) := rankPacketCell s (s.card - π / 2 + 32) k

/-- A shifted up-fringe consists of the endpoint pair together with the
complete aligned cells in the two middle portions of its prefix and suffix. -/
theorem upSetEndpoint_partition {N : Nat} (s : Finset (Fin N))
    (π q C : Nat) (hπ : π = 64 * (2 * q + 1))
    (hcard : s.card = 64 * C) (hπcard : π ≤ s.card) :
    Chvatal.upSet s π =
      upFringePairSupport s π ∪
        ((Finset.univ.biUnion (fun k : Fin q => upSetPrefixCell s k)) ∪
          Finset.univ.biUnion (fun k : Fin q => upSetSuffixCell s π k)) := by
  classical
  have hhalf : π / 2 = 64 * q + 32 := by rw [hπ]; omega
  have hprefix : π / 2 - 32 = 64 * q := by rw [hhalf]; omega
  have hsuffix : s.card - π / 2 + 32 + 64 * q = s.card := by
    rw [hcard, hhalf]
    omega
  have hinterval : Chvatal.upSet s π =
      upFringePairSupport s π ∪
        (Chvatal.blockOf s 0 (π / 2 - 32) ∪
          Chvatal.blockOf s (s.card - π / 2 + 32) s.card) := by
    ext w
    simp only [Chvatal.upSet, upFringePairSupport, Chvatal.blockOf,
      Finset.mem_union, Finset.mem_filter]
    change (w ∈ s ∧ 0 ≤ Chvatal.rankIn s w ∧ Chvatal.rankIn s w < π / 2 ∨
        w ∈ s ∧ s.card - π / 2 ≤ Chvatal.rankIn s w ∧ Chvatal.rankIn s w < s.card) ↔ _
    constructor
    · rintro (⟨hw, _, hr⟩ | ⟨hw, hlo, hhi⟩)
      · by_cases hleft : Chvatal.rankIn s w < π / 2 - 32
        · exact Or.inr (Or.inl ⟨hw, by omega, hleft⟩)
        · exact Or.inl (Or.inl ⟨hw, by omega, hr⟩)
      · by_cases hright : Chvatal.rankIn s w < s.card - π / 2 + 32
        · exact Or.inl (Or.inr ⟨hw, hlo, hright⟩)
        · exact Or.inr (Or.inr ⟨hw, by omega, hhi⟩)
    · rintro (⟨⟨hw, hlo, hhi⟩ | ⟨hw, hlo, hhi⟩⟩ |
        ⟨⟨hw, hlo, hhi⟩ | ⟨hw, hlo, hhi⟩⟩)
      · exact Or.inl ⟨hw, by omega, by omega⟩
      · exact Or.inr ⟨hw, hlo, by omega⟩
      · exact Or.inl ⟨hw, by omega, by omega⟩
      · exact Or.inr ⟨hw, by omega, hhi⟩
  have hpre : Chvatal.blockOf s 0 (π / 2 - 32) =
      Finset.univ.biUnion (fun k : Fin q => upSetPrefixCell s k) := by
    rw [hprefix]
    simpa [upSetPrefixCell] using blockOf_packetCell_partition s 0 q
  have hsuf : Chvatal.blockOf s (s.card - π / 2 + 32) s.card =
      Finset.univ.biUnion (fun k : Fin q => upSetSuffixCell s π k) := by
    calc
      Chvatal.blockOf s (s.card - π / 2 + 32) s.card =
          Chvatal.blockOf s (s.card - π / 2 + 32)
            (s.card - π / 2 + 32 + 64 * q) := by congr 1 <;> omega
      _ = Finset.univ.biUnion (fun k : Fin q => upSetSuffixCell s π k) := by
        simpa [upSetSuffixCell] using
          blockOf_packetCell_partition s (s.card - π / 2 + 32) q
  rw [hinterval, hpre, hsuf]

/-- A cell on an aligned 64-wire rank interval is one of the original
packet cells and is therefore already sorted under `PacketSortedOn`. -/
theorem rankPacketCell_sorted {N : Nat} {α : Type} [Preorder α]
    (s : Finset (Fin N)) (v : Fin N → α) (hpack : PacketSortedOn s v)
    (lo : Nat) (hlo : lo % 64 = 0) {q : Nat} (k : Fin q) :
    RankSortedOn (rankPacketCell s lo k) v := by
  let p := lo / 64 + k.val
  have hdiv := Nat.mod_add_div lo 64
  rw [hlo] at hdiv
  have hstart : lo + 64 * k.val = 64 * p := by
    dsimp [p]
    omega
  have hend : lo + 64 * (k.val + 1) = 64 * (p + 1) := by
    dsimp [p]
    omega
  unfold rankPacketCell
  rw [hstart, hend]
  exact hpack p

theorem rankPacketCell_bounds {N : Nat} (s : Finset (Fin N)) (lo : Nat)
    {q : Nat} (k : Fin q) {w : Fin N}
    (hw : w ∈ rankPacketCell s lo k) :
    lo + 64 * k.val ≤ Chvatal.rankIn s w ∧
      Chvatal.rankIn s w < lo + 64 * (k.val + 1) := by
  exact Chvatal.mem_blockOf.mp hw |>.2

theorem upSetPrefixCell_disjoint_endpoints {N : Nat} (s : Finset (Fin N))
    (π q C : Nat) (hπ : π = 64 * (2 * q + 1))
    (hcard : s.card = 64 * C) (hπcard : π ≤ s.card)
    {k : Fin q} {w : Fin N} (hw : w ∈ upSetPrefixCell s k) :
    w ∉ upFringePairSupport s π := by
  have hb := rankPacketCell_bounds s 0 k hw
  have hk := k.isLt
  have hhalf : π / 2 = 64 * q + 32 := by rw [hπ]; omega
  have hcardLower : 64 * (2 * q + 1) ≤ s.card := by rw [← hπ]; exact hπcard
  intro hmem
  rcases Finset.mem_union.mp hmem with hA | hB
  · have hr := Chvatal.mem_blockOf.mp hA
    rw [hhalf] at hr
    omega
  · have hr := Chvatal.mem_blockOf.mp hB
    rw [hcard, hhalf] at hr
    omega

theorem upSetSuffixCell_disjoint_endpoints {N : Nat} (s : Finset (Fin N))
    (π q C : Nat) (hπ : π = 64 * (2 * q + 1))
    (hcard : s.card = 64 * C) (hπcard : π ≤ s.card)
    {k : Fin q} {w : Fin N} (hw : w ∈ upSetSuffixCell s π k) :
    w ∉ upFringePairSupport s π := by
  have hb := rankPacketCell_bounds s (s.card - π / 2 + 32) k hw
  have hk := k.isLt
  have hhalf : π / 2 = 64 * q + 32 := by rw [hπ]; omega
  have hC : 2 * q + 1 ≤ C := by rw [hπ, hcard] at hπcard; omega
  have hlo : s.card - π / 2 + 32 = 64 * (C - q) := by
    rw [hcard, hhalf]
    omega
  intro hmem
  rcases Finset.mem_union.mp hmem with hA | hB
  · have hr := Chvatal.mem_blockOf.mp hA
    rw [hlo] at hb
    rw [hhalf] at hr
    omega
  · have hr := Chvatal.mem_blockOf.mp hB
    rw [hlo] at hb
    rw [hcard, hhalf] at hr
    omega

theorem downSetEndpointSupport_rank_bounds {N : Nat}
    (s : Finset (Fin N)) (π τ : Nat) (j : Fin 64)
    (hτlarge : 64 ≤ τ) {w : Fin N}
    (hw : w ∈ downSetEndpointLeft s π τ j ∪ downSetEndpointRight s π τ j) :
    π / 2 ≤ Chvatal.rankIn s w ∧
      Chvatal.rankIn s w < π / 2 + 64 * τ := by
  rcases Finset.mem_union.mp hw with hleft | hright
  · have hj := j.isLt
    have hj1 : j.val + 1 ≤ 64 := by omega
    have hmul : (j.val + 1) * τ ≤ 64 * τ := Nat.mul_le_mul_right τ hj1
    change w ∈ Chvatal.blockOf s (π / 2 + j.val * τ)
      (π / 2 + j.val * τ + 32) at hleft
    have hr := Chvatal.mem_blockOf.mp hleft
    constructor
    · omega
    · have hstep : (j.val + 1) * τ = j.val * τ + τ := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
  · change w ∈ Chvatal.blockOf s
      (π / 2 + (j.val + 1) * τ - 32) (π / 2 + (j.val + 1) * τ) at hright
    have hr := Chvatal.mem_blockOf.mp hright
    have hj := j.isLt
    have hj1 : j.val + 1 ≤ 64 := by omega
    have hmul : (j.val + 1) * τ ≤ 64 * τ := Nat.mul_le_mul_right τ hj1
    constructor
    · have hjpos : 1 ≤ j.val + 1 := by omega
      have hlow := Nat.mul_le_mul_right τ hjpos
      simp only [Nat.one_mul] at hlow
      omega
    · omega

theorem downSetEndpointSupport_disjoint_upFringe {N : Nat}
    (s : Finset (Fin N)) (π τ : Nat) (j : Fin 64)
    (hτlarge : 64 ≤ τ) (heven : 2 ∣ π) (hcapacity : π + 64 * τ ≤ s.card)
    {w : Fin N}
    (hdown : w ∈ downSetEndpointLeft s π τ j ∪ downSetEndpointRight s π τ j)
    (hup : w ∈ upFringePairSupport s π) : False := by
  have hd := downSetEndpointSupport_rank_bounds s π τ j hτlarge hdown
  rcases Finset.mem_union.mp hup with hup | hup
  · have hu := Chvatal.mem_blockOf.mp hup
    omega
  · have hu := Chvatal.mem_blockOf.mp hup
    have hrem := Nat.mod_add_div π 2
    have hzero := Nat.mod_eq_zero_of_dvd heven
    rw [hzero] at hrem
    have hpieq : π = 2 * (π / 2) := by omega
    have hcap := hcapacity
    rw [hpieq] at hcap
    have hgap : π / 2 + 64 * τ ≤ s.card - π / 2 := by omega
    omega

theorem downSet_disjoint_upSet_of_capacity {N : Nat}
    (s : Finset (Fin N)) (π τ j : Nat) (hj : j < 64)
    (heven : 2 ∣ π) (hcapacity : π + 64 * τ ≤ s.card)
    {w : Fin N} (hd : w ∈ Chvatal.downSet s π τ j)
    (hu : w ∈ Chvatal.upSet s π) : False := by
  have hd' := downSet_rank_cut s π τ j hd
  have hu' := upSet_rank_cut s π hu
  have hrem := Nat.mod_add_div π 2
  have hzero := Nat.mod_eq_zero_of_dvd heven
  rw [hzero] at hrem
  have hpieq : π = 2 * (π / 2) := by omega
  have hcap := hcapacity
  rw [hpieq] at hcap
  have hgap : π / 2 + 64 * τ ≤ s.card - π / 2 := by omega
  rcases hu' with ⟨_, huLt⟩ | ⟨_, huLo, _⟩
  · omega
  · have hmul : (j + 1) * τ ≤ 64 * τ := Nat.mul_le_mul_right τ (by omega)
    omega

theorem upFringePairSupport_subset_upSet {N : Nat} (s : Finset (Fin N)) (π : Nat)
    (hπlarge : 32 ≤ π / 2) (hπcard : π ≤ s.card) :
    upFringePairSupport s π ⊆ Chvatal.upSet s π := by
  intro w hw
  rcases Finset.mem_union.mp hw with hleft | hright
  · have hr := Chvatal.mem_blockOf.mp hleft
    apply Finset.mem_union_left
    apply Chvatal.mem_blockOf.mpr
    exact ⟨hr.1, by omega, hr.2.2⟩
  · have hr := Chvatal.mem_blockOf.mp hright
    apply Finset.mem_union_right
    apply Chvatal.mem_blockOf.mpr
    exact ⟨hr.1, hr.2.1, by omega⟩

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

/-- The indexed packet family on a shifted down-cut consists of one repaired
endpoint pair and the unmodified aligned interior cells. -/
def downSetRepairPacket {N : Nat} (s : Finset (Fin N)) (π τ : Nat)
    (j : Fin 64) (m : Nat) : Unit ⊕ Fin m → Finset (Fin N) := fun a =>
  match a with
  | Sum.inl _ => downSetEndpointLeft s π τ j ∪ downSetEndpointRight s π τ j
  | Sum.inr k => downSetInteriorCell s π τ j m k

theorem downSetRepairPacket_union {N : Nat} (s : Finset (Fin N))
    (π τ : Nat) (j : Fin 64) (m : Nat)
    (hτ : τ = 64 * (m + 1)) :
    Finset.univ.biUnion (downSetRepairPacket s π τ j m) =
      Chvatal.downSet s π τ j.val := by
  rw [downSetEndpoint_partition s π τ j m hτ]
  ext w
  simp [downSetRepairPacket]
  tauto

private theorem downSetRepairPacket_endpoint_interior_disjoint {N : Nat}
    (s : Finset (Fin N)) (π τ : Nat) (j : Fin 64) (m : Nat)
    (hτ : τ = 64 * (m + 1)) (k : Fin m) :
    Disjoint
      (downSetEndpointLeft s π τ j ∪ downSetEndpointRight s π τ j)
      (downSetInteriorCell s π τ j m k) := by
  apply Finset.disjoint_left.mpr
  intro w hwe hwi
  have hi := downSetInteriorCell_bounds s π τ j m hτ k w hwi
  rcases Finset.mem_union.mp hwe with hl | hr
  · change w ∈ Chvatal.blockOf s (π / 2 + j.val * τ)
      (π / 2 + j.val * τ + 32) at hl
    have he := Chvatal.mem_blockOf.mp hl
    omega
  · change w ∈ Chvatal.blockOf s
      (π / 2 + (j.val + 1) * τ - 32) (π / 2 + (j.val + 1) * τ) at hr
    have he := Chvatal.mem_blockOf.mp hr
    omega

theorem downSetRepairPacket_pairwise_disjoint {N : Nat}
    (s : Finset (Fin N)) (π τ : Nat) (j : Fin 64) (m : Nat)
    (hτ : τ = 64 * (m + 1)) :
    ∀ a b : Unit ⊕ Fin m, a ≠ b →
      Disjoint (downSetRepairPacket s π τ j m a)
        (downSetRepairPacket s π τ j m b) := by
  intro a b hab
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      cases u
      cases v
      exact (hab rfl).elim
    | inr k =>
      cases u
      exact downSetRepairPacket_endpoint_interior_disjoint s π τ j m hτ k
  | inr k =>
    cases b with
    | inl u =>
      cases u
      exact (downSetRepairPacket_endpoint_interior_disjoint s π τ j m hτ k).symm
    | inr l =>
      have hkl : k.val ≠ l.val := by
        intro h
        apply hab
        exact congrArg Sum.inr (Fin.ext h)
      apply Finset.disjoint_left.mpr
      intro w hwk hwl
      have hk := Chvatal.mem_blockOf.mp hwk
      have hl := Chvatal.mem_blockOf.mp hwl
      by_cases hkl' : k.val < l.val
      · omega
      · have hlk' : l.val < k.val := by omega
        omega

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

theorem downSetRepairPacket_card_eq_64 {N : Nat}
    (s : Finset (Fin N)) (π τ : Nat) (j : Fin 64) (m : Nat)
    (hτ : τ = 64 * (m + 1)) (hbase : (π / 2) % 64 = 32)
    (hwithin : π / 2 + 64 * τ ≤ s.card) :
    ∀ a : Unit ⊕ Fin m, (downSetRepairPacket s π τ j m a).card = 64 := by
  intro a
  cases a with
  | inl u =>
    cases u
    have hτlarge : 64 ≤ τ := by rw [hτ]; omega
    have hleft := downSetEndpointLeft_card s π τ j hτlarge hwithin
    have hdiv : 64 ∣ τ := by rw [hτ]; exact ⟨m + 1, rfl⟩
    have hright := downSetEndpointRight_card s π τ j hdiv hbase hwithin
    have hdj : Disjoint (downSetEndpointLeft s π τ j)
        (downSetEndpointRight s π τ j) := by
      apply Finset.disjoint_left.mpr
      intro w hwL hwR
      change w ∈ Chvatal.blockOf s (π / 2 + j.val * τ)
        (π / 2 + j.val * τ + 32) at hwL
      change w ∈ Chvatal.blockOf s
        (π / 2 + (j.val + 1) * τ - 32)
        (π / 2 + (j.val + 1) * τ) at hwR
      have hl := Chvatal.mem_blockOf.mp hwL
      have hr := Chvatal.mem_blockOf.mp hwR
      have hstep : (j.val + 1) * τ = j.val * τ + τ := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [hstep] at hr
      omega
    simp [downSetRepairPacket, Finset.card_union_of_disjoint hdj, hleft, hright]
  | inr k =>
    have hmul : (j.val + 1) * τ ≤ 64 * τ :=
      Nat.mul_le_mul_right τ (by omega)
    have hhi : π / 2 + (j.val + 1) * τ ≤ s.card := by omega
    have hstep : (j.val + 1) * τ = j.val * τ + τ := by
      rw [Nat.add_mul, Nat.one_mul]
    have hend : π / 2 + j.val * τ + 32 + 64 * (k.val + 1) ≤ s.card := by
      have hlt : k.val < m := k.isLt
      have hle : π / 2 + j.val * τ + 32 + 64 * (k.val + 1) ≤
          π / 2 + (j.val + 1) * τ := by rw [hstep, hτ]; omega
      exact hle.trans hhi
    rw [downSetRepairPacket, downSetInteriorCell,
      Chvatal.blockOf_card hend]
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

/-- After the child-fringe endpoint repairs, every full aligned cell in each
up-port remains sorted, so the whole up-port is a sorted 64-packet layout. -/
theorem parallelUpFringeEndpointRepair_packetLayout {ι : Type} [DecidableEq ι]
    {N : Nat} {α : Type} [LinearOrder α]
    (ids : List ι) (hids : ids.Nodup) (s : ι → Finset (Fin N))
    (π q : Nat) (C : ι → Nat) (hπ : π = 64 * (2 * q + 1))
    (hcard : ∀ i, (s i).card = 64 * C i)
    (hπcard : ∀ i, π ≤ (s i).card)
    (hsourceDisjoint : ∀ i ∈ ids, ∀ j ∈ ids, i ≠ j → Disjoint (s i) (s j)) :
    ∃ net : ComparatorNetwork N, net.depth ≤ 6 ∧
      ∀ v : Fin N → α, (∀ i ∈ ids, PacketSortedOn (s i) v) →
        ∀ i ∈ ids,
          RankSortedOn (upFringePairSupport (s i) π) (net.exec v) ∧
          (∀ k : Fin q, RankSortedOn (upSetPrefixCell (s i) k) (net.exec v)) ∧
          (∀ k : Fin q, RankSortedOn (upSetSuffixCell (s i) π k) (net.exec v)) := by
  classical
  have hcard64 : ∀ i, 64 ∣ (s i).card := by
    intro i
    rw [hcard i]
    exact ⟨C i, rfl⟩
  have heven : 2 ∣ π := by
    refine ⟨32 * (2 * q + 1), ?_⟩
    rw [hπ]
    omega
  have hhalf : (π / 2) % 64 = 32 := by rw [hπ]; omega
  let A (i : ι) := Chvatal.blockOf (s i) (π / 2 - 32) (π / 2)
  let B (i : ι) := Chvatal.blockOf (s i) ((s i).card - π / 2)
    ((s i).card - π / 2 + 32)
  have hA : ∀ i, (A i).card = 32 := by
    intro i
    exact (upFringe_endpoint_pair (s i) π heven (hcard64 i) hhalf (hπcard i)).2.1
  have hB : ∀ i, (B i).card = 32 := by
    intro i
    exact (upFringe_endpoint_pair (s i) π heven (hcard64 i) hhalf (hπcard i)).2.2.1
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
  let net := parallelHalfPairRepair ids A B hA hB hsep
  have hdepth : net.depth ≤ 6 := by
    exact parallelHalfPairRepair_depth_le ids hids A B hA hB hsep hdis
  have hsort : ∀ v : Fin N → α, (∀ i ∈ ids, PacketSortedOn (s i) v) →
      ∀ i ∈ ids, RankSortedOn (upFringePairSupport (s i) π) (net.exec v) := by
    intro v hsorted i hi
    have hsPair := parallelHalfPairRepair_sorts_pair ids hids A B hA hB hsep
      hdis v i hi
    have hsA := (packetSortedOn_upFringe_endpoints (s i) v (hsorted i hi) π
      (hcard64 i) hhalf (hπcard i)).1
    have hsB := (packetSortedOn_upFringe_endpoints (s i) v (hsorted i hi) π
      (hcard64 i) hhalf (hπcard i)).2
    have h := hsPair hsA hsB
    simpa [net, A, B, upFringePairSupport] using h
  refine ⟨net, hdepth, ?_⟩
  intro v hpack i hi
  have hsorted : ∀ j ∈ ids, PacketSortedOn (s j) v := hpack
  have hendpoint : RankSortedOn (upFringePairSupport (s i) π) (net.exec v) :=
    hsort v hsorted i hi
  refine ⟨hendpoint, ?_, ?_⟩
  · intro k
    have hsCell := rankPacketCell_sorted (s i) v (hpack i hi) 0 (by rfl) k
    have houtside : ∀ w ∈ upSetPrefixCell (s i) k, ∀ j ∈ ids,
        w ∉ A j ∪ B j := by
      intro w hw j hj hmem
      by_cases hij : i = j
      · subst j
        exact upSetPrefixCell_disjoint_endpoints (s i) π q (C i) hπ
          (hcard i) (hπcard i) hw (by simpa [A, B, upFringePairSupport] using hmem)
      · have hwi : w ∈ s i := Chvatal.blockOf_subset hw
        have hwj : w ∈ s j := by
          rcases Finset.mem_union.mp hmem with hmem | hmem
          · exact Chvatal.blockOf_subset hmem
          · exact Chvatal.blockOf_subset hmem
        exact (Finset.disjoint_left.mp (hsourceDisjoint i hi j hj hij)) hwi hwj
    intro x y hx hy hxy
    have hxEq := parallelHalfPairRepair_exec_outside ids A B hA hB hsep v x
      (houtside x hx)
    have hyEq := parallelHalfPairRepair_exec_outside ids A B hA hB hsep v y
      (houtside y hy)
    change (parallelHalfPairRepair ids A B hA hB hsep).exec v x ≤
      (parallelHalfPairRepair ids A B hA hB hsep).exec v y
    rw [hxEq, hyEq]
    exact hsCell hx hy hxy
  · intro k
    have hC : 2 * q + 1 ≤ C i := by
      have hcap := hπcard i
      rw [hπ, hcard i] at hcap
      omega
    have hstart : (s i).card - π / 2 + 32 = 64 * (C i - q) := by
      rw [hcard i, hπ]
      omega
    have hstartAligned : ((s i).card - π / 2 + 32) % 64 = 0 := by
      rw [hstart]
      omega
    have hsCell := rankPacketCell_sorted (s i) v (hpack i hi)
      ((s i).card - π / 2 + 32) hstartAligned k
    have houtside : ∀ w ∈ upSetSuffixCell (s i) π k, ∀ j ∈ ids,
        w ∉ A j ∪ B j := by
      intro w hw j hj hmem
      by_cases hij : i = j
      · subst j
        exact upSetSuffixCell_disjoint_endpoints (s i) π q (C i) hπ
          (hcard i) (hπcard i) hw (by simpa [A, B, upFringePairSupport] using hmem)
      · have hwi : w ∈ s i := Chvatal.blockOf_subset hw
        have hwj : w ∈ s j := by
          rcases Finset.mem_union.mp hmem with hmem | hmem
          · exact Chvatal.blockOf_subset hmem
          · exact Chvatal.blockOf_subset hmem
        exact (Finset.disjoint_left.mp (hsourceDisjoint i hi j hj hij)) hwi hwj
    intro x y hx hy hxy
    have hxEq := parallelHalfPairRepair_exec_outside ids A B hA hB hsep v x
      (houtside x hx)
    have hyEq := parallelHalfPairRepair_exec_outside ids A B hA hB hsep v y
      (houtside y hy)
    change (parallelHalfPairRepair ids A B hA hB hsep).exec v x ≤
      (parallelHalfPairRepair ids A B hA hB hsep).exec v y
    rw [hxEq, hyEq]
    exact hsCell hx hy hxy

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

/-- One six-layer cohort repairs both kinds of shifted endpoint support on a
sender: its 64 outgoing down-cut pairs and its own incoming up-fringe pair.
All 65 pairs are disjoint because the down region is the middle interval
between the two up-fringe intervals. -/
theorem parallelSourcePortPacketLayout {N : Nat} {α : Type}
    [LinearOrder α] (s : Finset (Fin N)) (π τ m q C : Nat)
    (hτeq : τ = 64 * (m + 1)) (hπeq : π = 64 * (2 * q + 1))
    (hcardEq : s.card = 64 * C)
    (hτ : 64 ∣ τ) (hτlarge : 64 ≤ τ)
    (hbase : (π / 2) % 64 = 32) (heven : 2 ∣ π)
    (hcard64 : 64 ∣ s.card) (hπcard : π ≤ s.card)
    (hwithin : π / 2 + 64 * τ ≤ s.card)
    (hcapacity : π + 64 * τ ≤ s.card) :
    ∃ net : ComparatorNetwork N, net.depth ≤ 6 ∧
      ∀ v : Fin N → α, PacketSortedOn s v →
        (∀ j : Fin 64,
          RankSortedOn
            (downSetEndpointLeft s π τ j ∪ downSetEndpointRight s π τ j)
            (net.exec v)) ∧
        (∀ j : Fin 64, ∀ k : Fin m,
          RankSortedOn (downSetInteriorCell s π τ j m k) (net.exec v)) ∧
        RankSortedOn (upFringePairSupport s π) (net.exec v) ∧
        (∀ k : Fin q, RankSortedOn (upSetPrefixCell s k) (net.exec v)) ∧
        (∀ k : Fin q, RankSortedOn (upSetSuffixCell s π k) (net.exec v)) := by
  classical
  let Id := Fin 64 ⊕ Unit
  let ids : List Id :=
    (List.finRange 64).map (fun j : Fin 64 => (Sum.inl j : Id)) ++ [Sum.inr ()]
  let A (i : Id) : Finset (Fin N) := match i with
    | .inl j => downSetEndpointLeft s π τ j
    | .inr _ => Chvatal.blockOf s (π / 2 - 32) (π / 2)
  let B (i : Id) : Finset (Fin N) := match i with
    | .inl j => downSetEndpointRight s π τ j
    | .inr _ => Chvatal.blockOf s (s.card - π / 2) (s.card - π / 2 + 32)
  have hids : ids.Nodup := by
    apply List.Nodup.append
    · exact (List.nodup_finRange 64).map Sum.inl_injective
    · simp
    · simp
  have hA : ∀ i, (A i).card = 32 := by
    intro i
    cases i with
    | inl j => exact downSetEndpointLeft_card s π τ j hτlarge hwithin
    | inr u => cases u; exact (upFringe_endpoint_pair s π heven hcard64 hbase hπcard).2.1
  have hB : ∀ i, (B i).card = 32 := by
    intro i
    cases i with
    | inl j => exact downSetEndpointRight_card s π τ j hτ hbase hwithin
    | inr u => cases u; exact (upFringe_endpoint_pair s π heven hcard64 hbase hπcard).2.2.1
  have hsep : ∀ i, ∀ x ∈ A i, ∀ y ∈ B i, x < y := by
    intro i x hx y hy
    cases i with
    | inl j => exact downSetEndpoint_separated s π τ j hτlarge x hx y hy
    | inr u =>
      cases u
      · exact upFringe_endpoint_pair_ordered s π heven hbase hπcard
          (a := x) (b := y) hx hy
  have hdis : ∀ i ∈ ids, ∀ j ∈ ids, i ≠ j →
      Disjoint (A i ∪ B i) (A j ∪ B j) := by
    intro i hi j hj hne
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        exact downSetEndpointSupport_disjoint s π τ i j hτlarge (by
          intro h
          apply hne
          exact congrArg Sum.inl h)
      | inr u =>
        cases u
        apply Finset.disjoint_left.mpr
        intro w hwDown hwUp
        change w ∈ upFringePairSupport s π at hwUp
        rcases Finset.mem_union.mp hwDown with hleft | hright
        · exact downSetEndpointSupport_disjoint_upFringe s π τ i hτlarge heven
            hcapacity (Finset.mem_union_left _ hleft) hwUp
        · exact downSetEndpointSupport_disjoint_upFringe s π τ i hτlarge heven
            hcapacity (Finset.mem_union_right _ hright) hwUp
    | inr u =>
      cases u
      cases j with
      | inl j =>
        apply Finset.disjoint_left.mpr
        intro w hwUp hwDown
        change w ∈ upFringePairSupport s π at hwUp
        rcases Finset.mem_union.mp hwDown with hleft | hright
        · exact downSetEndpointSupport_disjoint_upFringe s π τ j hτlarge heven
            hcapacity (Finset.mem_union_left _ hleft) hwUp
        · exact downSetEndpointSupport_disjoint_upFringe s π τ j hτlarge heven
            hcapacity (Finset.mem_union_right _ hright) hwUp
      | inr u => cases u; exact (hne rfl).elim
  let net := parallelHalfPairRepair ids A B hA hB hsep
  have hdepth : net.depth ≤ 6 :=
    parallelHalfPairRepair_depth_le ids hids A B hA hB hsep hdis
  refine ⟨net, hdepth, ?_⟩
  intro v hpack
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have hlo := (downSet_cut_residues (π := π) (τ := τ) (j := j.val) hτ).1
    rw [hbase] at hlo
    have hhi := (downSet_cut_residues (π := π) (τ := τ) (j := j.val) hτ).2
    rw [hbase] at hhi
    have hstep : (j.val + 1) * τ = j.val * τ + τ := by
      rw [Nat.add_mul, Nat.one_mul]
    have hspan : 64 ≤ (π / 2 + (j.val + 1) * τ) - (π / 2 + j.val * τ) := by
      rw [hstep]
      omega
    have hruns := packetSortedOn_rankInterval_endpoints s v hpack
      (π / 2 + j.val * τ) (π / 2 + (j.val + 1) * τ) hspan hlo hhi
    have hsA : RankSortedOn (A (Sum.inl j)) v := by
      simpa [A, downSetEndpointLeft] using hruns.1
    have hsB : RankSortedOn (B (Sum.inl j)) v := by
      simpa [B, downSetEndpointRight] using hruns.2
    have hsort := parallelHalfPairRepair_sorts_pair ids hids A B hA hB hsep hdis
      v (Sum.inl j) (by simp [ids]) hsA hsB
    simpa [net, A, B] using hsort
  · intro j k
    have hsCell := downSetInteriorCell_sorted s π τ j m hτ hbase v hpack k
    have hwDown (w : Fin N) (hw : w ∈ downSetInteriorCell s π τ j m k) :
        w ∈ Chvatal.downSet s π τ j.val := by
      rw [downSetEndpoint_partition s π τ j m hτeq]
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hw⟩
    have houtside (w : Fin N) (hw : w ∈ downSetInteriorCell s π τ j m k) :
        ∀ i ∈ ids, w ∉ A i ∪ B i := by
      intro i hi hmem
      cases i with
      | inl i =>
        by_cases hij : i = j
        · subst i
          rcases Finset.mem_union.mp hmem with hleft | hright
          · have hb := downSetInteriorCell_bounds s π τ j m hτeq k w hw
            change w ∈ Chvatal.blockOf s (π / 2 + j.val * τ)
              (π / 2 + j.val * τ + 32) at hleft
            have hr := Chvatal.mem_blockOf.mp hleft
            omega
          · have hb := downSetInteriorCell_bounds s π τ j m hτeq k w hw
            change w ∈ Chvatal.blockOf s
              (π / 2 + (j.val + 1) * τ - 32) (π / 2 + (j.val + 1) * τ) at hright
            have hr := Chvatal.mem_blockOf.mp hright
            omega
        · have hdisj : Disjoint (Chvatal.downSet s π τ j.val)
            (Chvatal.downSet s π τ i.val) := by
            have hne : j.val ≠ i.val := by
              intro h
              apply hij
              exact Fin.ext h.symm
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact Chvatal.disjoint_downSet (j := j.val) (j' := i.val) hlt
            · exact (Chvatal.disjoint_downSet (j := i.val) (j' := j.val) hgt).symm
          have hsupport := downSetEndpointSupport_subset s π τ i hτlarge hmem
          exact (Finset.disjoint_left.mp hdisj (hwDown w hw)) hsupport
      | inr u =>
        cases u
        change w ∈ upFringePairSupport s π at hmem
        have hUp := upFringePairSupport_subset_upSet s π (by rw [hπeq]; omega) hπcard
        exact downSet_disjoint_upSet_of_capacity s π τ j.val j.isLt heven hcapacity
          (hwDown w hw) (hUp hmem)
    intro x y hx hy hxy
    have hxEq := parallelHalfPairRepair_exec_outside ids A B hA hB hsep v x
      (houtside x hx)
    have hyEq := parallelHalfPairRepair_exec_outside ids A B hA hB hsep v y
      (houtside y hy)
    change (parallelHalfPairRepair ids A B hA hB hsep).exec v x ≤
      (parallelHalfPairRepair ids A B hA hB hsep).exec v y
    rw [hxEq, hyEq]
    exact hsCell hx hy hxy
  · have hsUp := packetSortedOn_upFringe_endpoints s v hpack π hcard64 hbase hπcard
    have hsA : RankSortedOn (A (Sum.inr ())) v := by simpa [A] using hsUp.1
    have hsB : RankSortedOn (B (Sum.inr ())) v := by simpa [B] using hsUp.2
    have hsort := parallelHalfPairRepair_sorts_pair ids hids A B hA hB hsep hdis
      v (Sum.inr ()) (by simp [ids]) hsA hsB
    simpa [net, A, B, upFringePairSupport] using hsort
  · intro k
    have hsCell := rankPacketCell_sorted s v hpack 0 (by rfl) k
    have hpart := upSetEndpoint_partition s π q C hπeq hcardEq hπcard
    have hwUp (w : Fin N) (hw : w ∈ upSetPrefixCell s k) :
        w ∈ Chvatal.upSet s π := by
      rw [hpart]
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hw⟩
    have houtside (w : Fin N) (hw : w ∈ upSetPrefixCell s k) :
        ∀ i ∈ ids, w ∉ A i ∪ B i := by
      intro i hi hmem
      cases i with
      | inl j =>
        have hdown := downSetEndpointSupport_subset s π τ j hτlarge hmem
        exact downSet_disjoint_upSet_of_capacity s π τ j.val j.isLt heven hcapacity
          hdown (hwUp w hw)
      | inr u =>
        cases u
        change w ∈ upFringePairSupport s π at hmem
        exact upSetPrefixCell_disjoint_endpoints s π q C hπeq hcardEq hπcard hw hmem
    intro x y hx hy hxy
    have hxEq := parallelHalfPairRepair_exec_outside ids A B hA hB hsep v x
      (houtside x hx)
    have hyEq := parallelHalfPairRepair_exec_outside ids A B hA hB hsep v y
      (houtside y hy)
    change (parallelHalfPairRepair ids A B hA hB hsep).exec v x ≤
      (parallelHalfPairRepair ids A B hA hB hsep).exec v y
    rw [hxEq, hyEq]
    exact hsCell hx hy hxy
  · intro k
    have hstart : s.card - π / 2 + 32 = 64 * (C - q) := by
      rw [hcardEq, hπeq]
      omega
    have hstartAligned : (s.card - π / 2 + 32) % 64 = 0 := by
      rw [hstart]
      omega
    have hsCell := rankPacketCell_sorted s v hpack
      (s.card - π / 2 + 32) hstartAligned k
    have hpart := upSetEndpoint_partition s π q C hπeq hcardEq hπcard
    have hwUp (w : Fin N) (hw : w ∈ upSetSuffixCell s π k) :
        w ∈ Chvatal.upSet s π := by
      rw [hpart]
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hw⟩
    have houtside (w : Fin N) (hw : w ∈ upSetSuffixCell s π k) :
        ∀ i ∈ ids, w ∉ A i ∪ B i := by
      intro i hi hmem
      cases i with
      | inl j =>
        have hdown := downSetEndpointSupport_subset s π τ j hτlarge hmem
        exact downSet_disjoint_upSet_of_capacity s π τ j.val j.isLt heven hcapacity
          hdown (hwUp w hw)
      | inr u =>
        cases u
        change w ∈ upFringePairSupport s π at hmem
        exact upSetSuffixCell_disjoint_endpoints s π q C hπeq hcardEq hπcard hw hmem
    intro x y hx hy hxy
    have hxEq := parallelHalfPairRepair_exec_outside ids A B hA hB hsep v x
      (houtside x hx)
    have hyEq := parallelHalfPairRepair_exec_outside ids A B hA hB hsep v y
      (houtside y hy)
    change (parallelHalfPairRepair ids A B hA hB hsep).exec v x ≤
      (parallelHalfPairRepair ids A B hA hB hsep).exec v y
    rw [hxEq, hyEq]
    exact hsCell hx hy hxy

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

/-- Scheduled local packet-layout induction step: one six-layer repair on a
shifted sender simultaneously sorts all 64 outgoing down-port packets and
its incoming up-port packets, preserving their aligned interior cells. -/
theorem flowA7_scheduled_source_port_packetLayout {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (q : KBag 64 d)
    (hτpos : 0 < flowDown7 d hd q.l t)
    (hbad : HalfMisaligned (flowUp7 d hd q.l t)) :
    ∃ net : ComparatorNetwork (64 ^ d), net.depth ≤ 6 ∧
      ∀ v : Fin (64 ^ d) → α,
        PacketSortedOn (wireSets (flowSizes7 d hd) t q) v →
        (∀ j : Fin 64,
          RankSortedOn
            (downSetEndpointLeft (wireSets (flowSizes7 d hd) t q)
              (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j ∪
             downSetEndpointRight (wireSets (flowSizes7 d hd) t q)
              (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j)
            (net.exec v) ∧
          (∀ k : Fin (flowDown7 d hd q.l t / 64 - 1),
            RankSortedOn
              (downSetInteriorCell (wireSets (flowSizes7 d hd) t q)
                (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j
                (flowDown7 d hd q.l t / 64 - 1) k) (net.exec v))) ∧
        RankSortedOn (upFringePairSupport (wireSets (flowSizes7 d hd) t q)
          (flowUp7 d hd q.l t)) (net.exec v) ∧
        (∀ k : Fin ((flowUp7 d hd q.l t / 2) / 64),
          RankSortedOn
            (upSetPrefixCell (wireSets (flowSizes7 d hd) t q) k) (net.exec v)) ∧
        (∀ k : Fin ((flowUp7 d hd q.l t / 2) / 64),
          RankSortedOn
            (upSetSuffixCell (wireSets (flowSizes7 d hd) t q)
              (flowUp7 d hd q.l t) k) (net.exec v)) := by
  let F := flowSizes7 d hd
  let s := wireSets F t q
  let π := flowUp7 d hd q.l t
  let τ := flowDown7 d hd q.l t
  have hshape := node_shape_refined d hd t q.l ht2 ht
  have hres := refined_packet_residues hd ht2 ht hshape
  have hτdiv : 64 ∣ τ := by dsimp [τ]; exact hres.2.1
  have hτlarge : 64 ≤ τ := Nat.le_of_dvd (by simpa [τ] using hτpos) hτdiv
  have hbase : (π / 2) % 64 = 32 := hbad.2
  have heven : 2 ∣ π := by dsimp [π]; exact F.hup_even q.l t ht
  have hcard64 : 64 ∣ s.card := by
    dsimp [s, F]
    rw [wireSets_card _ (Nat.le_of_lt ht)]
    exact hres.1
  have hsize : s.card = π + 64 * τ := by
    dsimp [s, F, π, τ]
    rw [wireSets_card _ (Nat.le_of_lt ht) q]
    exact F.hsplit q.l t q.hl ht
  have hwithin : π / 2 + 64 * τ ≤ s.card := by rw [hsize]; omega
  have hcapacity : π + 64 * τ ≤ s.card := by rw [hsize]
  have hπcard : π ≤ s.card := by rw [hsize]; omega
  let m := τ / 64 - 1
  have hτeq : τ = 64 * (m + 1) := by
    have hmod := Nat.mod_add_div τ 64
    have hrem : τ % 64 = 0 := Nat.mod_eq_zero_of_dvd hτdiv
    rw [hrem] at hmod
    dsimp [m]
    omega
  let r := (π / 2) / 64
  have hhalfEq : π / 2 = 64 * r + 32 := by
    have hmod := Nat.mod_add_div (π / 2) 64
    rw [hbase] at hmod
    dsimp [r]
    omega
  have hpiTwice : π = 2 * (π / 2) := by
    have hmod := Nat.mod_add_div π 2
    have hrem : π % 2 = 0 := Nat.mod_eq_zero_of_dvd heven
    rw [hrem] at hmod
    omega
  have hπeq : π = 64 * (2 * r + 1) := by rw [hpiTwice, hhalfEq]; omega
  let C := 2 * r + 1 + τ
  have hcardEq : s.card = 64 * C := by rw [hsize, hπeq]; dsimp [C]; omega
  obtain ⟨net, hdepth, hlayout⟩ :=
    parallelSourcePortPacketLayout (α := α) s π τ m r C hτeq hπeq hcardEq
      hτdiv hτlarge hbase heven hcard64 hπcard hwithin hcapacity
  refine ⟨net, hdepth, ?_⟩
  intro v hpack
  have h := hlayout v hpack
  refine ⟨?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  intro j
  exact ⟨h.1 j, h.2.1 j⟩

/-- The same checked sender repair expressed on its local register indices,
ready to be embedded by `stageNet` through the bag's rank-order embedding. -/
theorem flowA7_source_port_packetLayout_register {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (q : KBag 64 d)
    (hτpos : 0 < flowDown7 d hd q.l t)
    (hbad : HalfMisaligned (flowUp7 d hd q.l t)) :
    ∃ net : ComparatorNetwork ((flowSizes7 d hd).a q.l t), net.depth ≤ 6 ∧
      ∀ v : Fin ((flowSizes7 d hd).a q.l t) → α,
        PacketSortedOn (Finset.univ : Finset (Fin ((flowSizes7 d hd).a q.l t))) v →
        (∀ j : Fin 64,
          RankSortedOn
            (downSetEndpointLeft (Finset.univ : Finset (Fin ((flowSizes7 d hd).a q.l t)))
              (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j ∪
             downSetEndpointRight (Finset.univ : Finset (Fin ((flowSizes7 d hd).a q.l t)))
              (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j)
            (net.exec v) ∧
          (∀ k : Fin (flowDown7 d hd q.l t / 64 - 1),
            RankSortedOn
              (downSetInteriorCell (Finset.univ : Finset (Fin ((flowSizes7 d hd).a q.l t)))
                (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j
                (flowDown7 d hd q.l t / 64 - 1) k) (net.exec v))) ∧
        RankSortedOn (upFringePairSupport
          (Finset.univ : Finset (Fin ((flowSizes7 d hd).a q.l t)))
          (flowUp7 d hd q.l t)) (net.exec v) ∧
        (∀ k : Fin ((flowUp7 d hd q.l t / 2) / 64),
          RankSortedOn
            (upSetPrefixCell (Finset.univ : Finset (Fin ((flowSizes7 d hd).a q.l t))) k)
            (net.exec v)) ∧
        (∀ k : Fin ((flowUp7 d hd q.l t / 2) / 64),
          RankSortedOn
            (upSetSuffixCell (Finset.univ : Finset (Fin ((flowSizes7 d hd).a q.l t)))
              (flowUp7 d hd q.l t) k) (net.exec v)) := by
  let F := flowSizes7 d hd
  let π := flowUp7 d hd q.l t
  let τ := flowDown7 d hd q.l t
  let m := τ / 64 - 1
  let r := (π / 2) / 64
  let C := 2 * r + 1 + τ
  have hshape := node_shape_refined d hd t q.l ht2 ht
  have hres := refined_packet_residues hd ht2 ht hshape
  have hτdiv : 64 ∣ τ := by dsimp [τ]; exact hres.2.1
  have hτlarge : 64 ≤ τ := Nat.le_of_dvd (by simpa [τ] using hτpos) hτdiv
  have hbase : (π / 2) % 64 = 32 := hbad.2
  have heven : 2 ∣ π := by dsimp [π]; exact F.hup_even q.l t ht
  have hsize : F.a q.l t = π + 64 * τ := by
    dsimp [F, π, τ]
    exact (flowSizes7 d hd).hsplit q.l t q.hl ht
  have hτeq : τ = 64 * (m + 1) := by
    have hmod := Nat.mod_add_div τ 64
    have hrem : τ % 64 = 0 := Nat.mod_eq_zero_of_dvd hτdiv
    rw [hrem] at hmod
    dsimp [m]
    omega
  have hhalfEq : π / 2 = 64 * r + 32 := by
    have hmod := Nat.mod_add_div (π / 2) 64
    rw [hbase] at hmod
    dsimp [r]
    omega
  have hpiTwice : π = 2 * (π / 2) := by
    have hmod := Nat.mod_add_div π 2
    have hrem : π % 2 = 0 := Nat.mod_eq_zero_of_dvd heven
    rw [hrem] at hmod
    omega
  have hπeq : π = 64 * (2 * r + 1) := by rw [hpiTwice, hhalfEq]; omega
  have hncard : (Finset.univ : Finset (Fin (F.a q.l t))).card = 64 * C := by
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [hsize, hπeq]
    dsimp [C]
    omega
  have hcard64 : 64 ∣ (Finset.univ : Finset (Fin (F.a q.l t))).card := by
    rw [hncard]
    exact ⟨C, rfl⟩
  have hπcard : π ≤ (Finset.univ : Finset (Fin (F.a q.l t))).card := by
    rw [hncard, hπeq]
    dsimp [C]
    omega
  have hwithin : π / 2 + 64 * τ ≤ (Finset.univ : Finset (Fin (F.a q.l t))).card := by
    rw [hncard]
    dsimp [C]
    rw [hhalfEq]
    omega
  have hcapacity : π + 64 * τ ≤ (Finset.univ : Finset (Fin (F.a q.l t))).card := by
    rw [hncard, hπeq]
    dsimp [C]
    omega
  obtain ⟨net, hdepth, hlayout⟩ :=
    parallelSourcePortPacketLayout (α := α)
      (Finset.univ : Finset (Fin (F.a q.l t))) π τ m r C hτeq hπeq hncard
      hτdiv hτlarge hbase heven hcard64 hπcard hwithin hcapacity
  refine ⟨net, hdepth, ?_⟩
  intro v hpack
  have h := hlayout v hpack
  refine ⟨?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  intro j
  exact ⟨h.1 j, h.2.1 j⟩

/-- Choose the checked local shared-port correction at every shifted ordinary
sender; all other senders run the empty network. -/
noncomputable def flowA7_sourcePortRepairNet {d : Nat}
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (q : KBag 64 d) :
    ComparatorNetwork ((flowSizes7 d hd).a q.l t) := by
  classical
  by_cases hdown : 0 < flowDown7 d hd q.l t
  · by_cases hbad : HalfMisaligned (flowUp7 d hd q.l t)
    · exact Classical.choose
        (flowA7_source_port_packetLayout_register (α := Bool) hd t ht2 ht q hdown hbad)
    · exact ⟨[]⟩
  · exact ⟨[]⟩

theorem flowA7_sourcePortRepairNet_depth_le {d : Nat}
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (q : KBag 64 d) :
    (flowA7_sourcePortRepairNet hd t ht2 ht q).depth ≤ 6 := by
  classical
  unfold flowA7_sourcePortRepairNet
  split
  · rename_i hdown
    split
    · rename_i hbad
      exact (Classical.choose_spec
        (flowA7_source_port_packetLayout_register (α := Bool) hd t ht2 ht q hdown hbad)).1
    · simp [ComparatorNetwork.depth]
  · simp [ComparatorNetwork.depth]

/-- The Bool-chosen repair network has the same sorted-packet layout for every
linear order: apply its Boolean contract to every threshold. -/
theorem flowA7_sourcePortRepairNet_layout {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (q : KBag 64 d)
    (hdown : 0 < flowDown7 d hd q.l t)
    (hbad : HalfMisaligned (flowUp7 d hd q.l t))
    (v : Fin ((flowSizes7 d hd).a q.l t) → α)
    (hpack : PacketSortedOn
      (Finset.univ : Finset (Fin ((flowSizes7 d hd).a q.l t))) v) :
    (∀ j : Fin 64,
      RankSortedOn
        (downSetEndpointLeft (Finset.univ : Finset (Fin ((flowSizes7 d hd).a q.l t)))
          (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j ∪
         downSetEndpointRight (Finset.univ : Finset (Fin ((flowSizes7 d hd).a q.l t)))
          (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j)
        ((flowA7_sourcePortRepairNet hd t ht2 ht q).exec v) ∧
      (∀ k : Fin (flowDown7 d hd q.l t / 64 - 1),
        RankSortedOn
          (downSetInteriorCell (Finset.univ : Finset (Fin ((flowSizes7 d hd).a q.l t)))
            (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j
            (flowDown7 d hd q.l t / 64 - 1) k)
          ((flowA7_sourcePortRepairNet hd t ht2 ht q).exec v))) ∧
    RankSortedOn (upFringePairSupport
      (Finset.univ : Finset (Fin ((flowSizes7 d hd).a q.l t)))
      (flowUp7 d hd q.l t)) ((flowA7_sourcePortRepairNet hd t ht2 ht q).exec v) ∧
    (∀ k : Fin ((flowUp7 d hd q.l t / 2) / 64),
      RankSortedOn
        (upSetPrefixCell (Finset.univ : Finset (Fin ((flowSizes7 d hd).a q.l t))) k)
        ((flowA7_sourcePortRepairNet hd t ht2 ht q).exec v)) ∧
    (∀ k : Fin ((flowUp7 d hd q.l t / 2) / 64),
      RankSortedOn
        (upSetSuffixCell (Finset.univ : Finset (Fin ((flowSizes7 d hd).a q.l t)))
          (flowUp7 d hd q.l t) k)
        ((flowA7_sourcePortRepairNet hd t ht2 ht q).exec v)) := by
  classical
  let P := flowA7_source_port_packetLayout_register (α := Bool) hd t ht2 ht q hdown hbad
  let net := Classical.choose P
  have hnet : flowA7_sourcePortRepairNet hd t ht2 ht q = net := by
    simp [flowA7_sourcePortRepairNet, hdown, hbad, net]
  rw [hnet]
  have hbool (θ : α) := (Classical.choose_spec P).2
    (fun i => decide (θ ≤ v i)) (by
      have hm : Monotone (fun z : α => decide (θ ≤ z)) := by
        intro a b hab
        by_cases ha : θ ≤ a
        · have hb : θ ≤ b := ha.trans hab
          simp [ha, hb]
        · simp [ha]
      intro p x y hx hy hxy
      exact hm (hpack p hx hy hxy))
  have lift {A : Finset (Fin ((flowSizes7 d hd).a q.l t))}
      (hA : ∀ θ : α,
        RankSortedOn A (fun i => decide (θ ≤ net.exec v i))) :
      RankSortedOn A (net.exec v) := by
    apply rankSortedOn_of_thresholds
    intro θ
    exact hA θ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    constructor
    · apply lift
      intro θ
      have h := (hbool θ).1 j
      rw [exec_threshold] at h
      exact h.1
    · intro k
      apply lift
      intro θ
      have h := (hbool θ).1 j
      rw [exec_threshold] at h
      exact h.2 k
  · apply lift
    intro θ
    have h := (hbool θ).2.1
    rw [exec_threshold] at h
    exact h
  · intro k
    apply lift
    intro θ
    have h := (hbool θ).2.2.1 k
    rw [exec_threshold] at h
    exact h
  · intro k
    apply lift
    intro θ
    have h := (hbool θ).2.2.2 k
    rw [exec_threshold] at h
    exact h

/-- Reindex the selected register network to the size parameter used by
`stageNet`; at unrelated sizes this is the empty network. -/
noncomputable def flowA7_sourcePortRepairNetAt {d : Nat}
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (q : KBag 64 d) (n : Nat) : ComparatorNetwork n := by
  classical
  by_cases hsize : n = (flowSizes7 d hd).a q.l t
  · exact hsize.symm ▸ flowA7_sourcePortRepairNet hd t ht2 ht q
  · exact ⟨[]⟩

theorem flowA7_sourcePortRepairNetAt_depth_le {d : Nat}
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (q : KBag 64 d) (n : Nat) :
    (flowA7_sourcePortRepairNetAt hd t ht2 ht q n).depth ≤ 6 := by
  classical
  unfold flowA7_sourcePortRepairNetAt
  split
  · rename_i hsize
    cases hsize
    exact flowA7_sourcePortRepairNet_depth_le hd t ht2 ht q
  · simp [ComparatorNetwork.depth]

/-- The local correction choices form one global stage of depth at most six.
`stageNet` places them on the actual disjoint `WireFlow` bags. -/
noncomputable def flowA7_sourcePortRepairStage {d : Nat}
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d) :
    ComparatorNetwork (64 ^ d) :=
  stageNet (wireSets (flowSizes7 d hd) t)
    (fun q n => flowA7_sourcePortRepairNetAt hd t ht2 ht q n)

theorem flowA7_sourcePortRepairStage_depth_le {d : Nat}
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d) :
    (flowA7_sourcePortRepairStage hd t ht2 ht).depth ≤ 6 := by
  exact stageNet_depth_le (wireSets (flowSizes7 d hd) t)
    (wireSets_disjoint (flowSizes7 d hd) (Nat.le_of_lt ht))
    (fun q n => flowA7_sourcePortRepairNetAt hd t ht2 ht q n)
    (fun q => by
      have hsize := wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) q
      simpa [hsize] using flowA7_sourcePortRepairNetAt_depth_le
        hd t ht2 ht q (wireSets (flowSizes7 d hd) t q).card)

/-- Transport any sorted support of an eligible source repair from its
register coordinates to the physical wires after the globally scheduled
correction stage. -/
theorem flowA7_sourcePortRepairStage_transport {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (q : KBag 64 d)
    (hdown : 0 < flowDown7 d hd q.l t)
    (hbad : HalfMisaligned (flowUp7 d hd q.l t))
    (v : Fin (64 ^ d) → α)
    (A : Finset (Fin ((flowSizes7 d hd).a q.l t)))
    (hlocal : RankSortedOn A
      ((flowA7_sourcePortRepairNet hd t ht2 ht q).exec
        (fun i => v (((wireSets (flowSizes7 d hd) t q).orderEmbOfFin
          (wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) q)) i)))) :
    RankSortedOn
      (A.image ((wireSets (flowSizes7 d hd) t q).orderEmbOfFin
        (wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) q)))
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) := by
  let S := wireSets (flowSizes7 d hd) t
  let nodeNet := fun b n => flowA7_sourcePortRepairNetAt hd t ht2 ht b n
  have hS : ∀ b b', b ≠ b' → Disjoint (S b) (S b') := by
    intro b b' hne
    exact wireSets_disjoint (flowSizes7 d hd) (Nat.le_of_lt ht) b b' hne
  have hsize : (S q).card = (flowSizes7 d hd).a q.l t :=
    wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) q
  have hAt : nodeNet q ((flowSizes7 d hd).a q.l t) =
      flowA7_sourcePortRepairNet hd t ht2 ht q := by
    unfold nodeNet flowA7_sourcePortRepairNetAt
    simp [hsize]
  have hlocal' : RankSortedOn A
      ((nodeNet q ((flowSizes7 d hd).a q.l t)).exec
        (fun i => v ((S q).orderEmbOfFin hsize i))) := by
    rw [hAt]
    exact hlocal
  change RankSortedOn (A.image ((S q).orderEmbOfFin hsize))
    ((stageNet S nodeNet).exec v)
  exact stageNet_rankSortedOn_image_of_card_eq S hS nodeNet v q _ hsize A hlocal'

/-- The selected source repair turns packet-sorted physical input into the
full family of endpoint, interior, and fringe rank-sorted supports on the
actual physical wires. -/
theorem flowA7_sourcePortRepairStage_layout {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (q : KBag 64 d)
    (hdown : 0 < flowDown7 d hd q.l t)
    (hbad : HalfMisaligned (flowUp7 d hd q.l t))
    (v : Fin (64 ^ d) → α)
    (hpack : PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    (∀ j : Fin 64,
      RankSortedOn
        ((downSetEndpointLeft (Finset.univ : Finset
          (Fin ((flowSizes7 d hd).a q.l t)))
          (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j ∪
         downSetEndpointRight (Finset.univ : Finset
          (Fin ((flowSizes7 d hd).a q.l t)))
          (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j).image
          ((wireSets (flowSizes7 d hd) t q).orderEmbOfFin
            (wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) q)))
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) ∧
      (∀ k : Fin (flowDown7 d hd q.l t / 64 - 1),
        RankSortedOn
          ((downSetInteriorCell (Finset.univ : Finset
            (Fin ((flowSizes7 d hd).a q.l t)))
            (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j
            (flowDown7 d hd q.l t / 64 - 1) k).image
            ((wireSets (flowSizes7 d hd) t q).orderEmbOfFin
              (wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) q)))
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v))) ∧
    RankSortedOn
      ((upFringePairSupport (Finset.univ : Finset
        (Fin ((flowSizes7 d hd).a q.l t))) (flowUp7 d hd q.l t)).image
        ((wireSets (flowSizes7 d hd) t q).orderEmbOfFin
          (wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) q)))
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) ∧
    (∀ k : Fin ((flowUp7 d hd q.l t / 2) / 64),
      RankSortedOn
        ((upSetPrefixCell (Finset.univ : Finset
          (Fin ((flowSizes7 d hd).a q.l t))) k).image
          ((wireSets (flowSizes7 d hd) t q).orderEmbOfFin
            (wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) q)))
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)) ∧
    (∀ k : Fin ((flowUp7 d hd q.l t / 2) / 64),
      RankSortedOn
        ((upSetSuffixCell (Finset.univ : Finset
          (Fin ((flowSizes7 d hd).a q.l t)))
          (flowUp7 d hd q.l t) k).image
          ((wireSets (flowSizes7 d hd) t q).orderEmbOfFin
            (wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) q)))
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)) := by
  let S := wireSets (flowSizes7 d hd) t
  let e := (S q).orderEmbOfFin
    (wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) q)
  have hreg := PacketSortedOn_orderEmb_of_card_eq (S q) v hpack
    (wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) q)
  have hlayout := flowA7_sourcePortRepairNet_layout hd t ht2 ht q hdown hbad
    (fun i => v (e i)) hreg
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    constructor
    · exact flowA7_sourcePortRepairStage_transport hd t ht2 ht q hdown hbad
        v _ (hlayout.1 j).1
    · intro k
      exact flowA7_sourcePortRepairStage_transport hd t ht2 ht q hdown hbad
        v _ ((hlayout.1 j).2 k)
  · exact flowA7_sourcePortRepairStage_transport hd t ht2 ht q hdown hbad
      v _ hlayout.2.1
  · intro k
    exact flowA7_sourcePortRepairStage_transport hd t ht2 ht q hdown hbad
      v _ (hlayout.2.2.1 k)
  · intro k
    exact flowA7_sourcePortRepairStage_transport hd t ht2 ht q hdown hbad
      v _ (hlayout.2.2.2 k)

/-- Each actual shifted child down-port is partitioned after correction into
pairwise-disjoint, sorted 64-wire supports ready for a matching round. -/
theorem flowA7_sourcePortRepairStage_downCutFamily {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (q : KBag 64 d)
    (hdown : 0 < flowDown7 d hd q.l t)
    (hbad : HalfMisaligned (flowUp7 d hd q.l t))
    (v : Fin (64 ^ d) → α)
    (hpack : PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∀ j : Fin 64,
      (∀ a : Unit ⊕ Fin (flowDown7 d hd q.l t / 64 - 1),
        RankSortedOn
          (downSetRepairPacket (wireSets (flowSizes7 d hd) t q)
            (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j
            (flowDown7 d hd q.l t / 64 - 1) a)
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)) ∧
      Finset.univ.biUnion (downSetRepairPacket (wireSets (flowSizes7 d hd) t q)
        (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j
        (flowDown7 d hd q.l t / 64 - 1)) =
        Chvatal.downSet (wireSets (flowSizes7 d hd) t q)
          (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j.val ∧
      (∀ a b : Unit ⊕ Fin (flowDown7 d hd q.l t / 64 - 1), a ≠ b →
        Disjoint
          (downSetRepairPacket (wireSets (flowSizes7 d hd) t q)
            (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j
            (flowDown7 d hd q.l t / 64 - 1) a)
          (downSetRepairPacket (wireSets (flowSizes7 d hd) t q)
            (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j
            (flowDown7 d hd q.l t / 64 - 1) b)) ∧
      (∀ a : Unit ⊕ Fin (flowDown7 d hd q.l t / 64 - 1),
        (downSetRepairPacket (wireSets (flowSizes7 d hd) t q)
          (flowUp7 d hd q.l t) (flowDown7 d hd q.l t) j
          (flowDown7 d hd q.l t / 64 - 1) a).card = 64) := by
  let S := wireSets (flowSizes7 d hd) t q
  let π := flowUp7 d hd q.l t
  let τ := flowDown7 d hd q.l t
  let m := τ / 64 - 1
  have hshape := node_shape_refined d hd t q.l ht2 ht
  have hres := refined_packet_residues hd ht2 ht hshape
  have hτdiv : 64 ∣ τ := by dsimp [τ]; exact hres.2.1
  have hτeq : τ = 64 * (m + 1) := by
    have hmod := Nat.mod_add_div τ 64
    have hrem : τ % 64 = 0 := Nat.mod_eq_zero_of_dvd hτdiv
    rw [hrem] at hmod
    dsimp [m]
    omega
  have hbase : (π / 2) % 64 = 32 := hbad.2
  have hbag : S.card = π + 64 * τ := by
    dsimp [S, π, τ]
    rw [wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) q]
    exact (flowSizes7 d hd).hsplit q.l t q.hl ht
  have hwithin : π / 2 + 64 * τ ≤ S.card := by rw [hbag]; omega
  have hlayout := flowA7_sourcePortRepairStage_layout hd t ht2 ht q hdown hbad v hpack
  intro j
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    cases a with
    | inl u =>
      cases u
      have hs := (hlayout.1 j).1
      simp only [downSetEndpointLeft, downSetEndpointRight,
        Finset.image_union] at hs
      rw [blockOf_register_image, blockOf_register_image] at hs
      simpa [S, π, τ, m, downSetRepairPacket, downSetEndpointLeft,
        downSetEndpointRight] using hs
    | inr k =>
      have hs := (hlayout.1 j).2 k
      simp only [downSetInteriorCell] at hs
      rw [blockOf_register_image] at hs
      simpa [S, π, τ, m, downSetRepairPacket, downSetInteriorCell] using hs
  · exact downSetRepairPacket_union S π τ j m hτeq
  · exact downSetRepairPacket_pairwise_disjoint S π τ j m hτeq
  · exact downSetRepairPacket_card_eq_64 S π τ j m hτeq hbase hwithin

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

/-- Scheduled child-up endpoint repair with the untouched interior cells
included: all 64 child up-ports become sorted packet layouts in six layers. -/
theorem flowA7_receiver_child_up_packetLayout {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d) (hchild : b.l < d)
    (hbad : HalfMisaligned (flowUp7 d hd (b.l + 1) t)) :
    ∃ q : Nat, flowUp7 d hd (b.l + 1) t = 64 * (2 * q + 1) ∧
      ∃ net : ComparatorNetwork (64 ^ d), net.depth ≤ 6 ∧
        ∀ v : Fin (64 ^ d) → α,
          (∀ j : Fin 64, PacketSortedOn
            (wireSets (flowSizes7 d hd) t (b.child j.val j.isLt hchild)) v) →
          ∀ j : Fin 64,
            RankSortedOn (upFringePairSupport
              (wireSets (flowSizes7 d hd) t (b.child j.val j.isLt hchild))
              (flowUp7 d hd (b.l + 1) t)) (net.exec v) ∧
            (∀ k : Fin q, RankSortedOn
              (upSetPrefixCell
                (wireSets (flowSizes7 d hd) t (b.child j.val j.isLt hchild)) k)
              (net.exec v)) ∧
            (∀ k : Fin q, RankSortedOn
              (upSetSuffixCell
                (wireSets (flowSizes7 d hd) t (b.child j.val j.isLt hchild))
                (flowUp7 d hd (b.l + 1) t) k) (net.exec v)) := by
  let F := flowSizes7 d hd
  let s (j : Fin 64) := wireSets F t (b.child j.val j.isLt hchild)
  let π := flowUp7 d hd (b.l + 1) t
  let τ := flowDown7 d hd (b.l + 1) t
  have hshape := node_shape_refined d hd t (b.l + 1) ht2 ht
  have hres := refined_packet_residues hd ht2 ht hshape
  have hcard64 : ∀ j : Fin 64, 64 ∣ (s j).card := by
    intro j
    rw [wireSets_card F (Nat.le_of_lt ht)]
    dsimp [s, F, flowSizes7]
    exact hres.1
  have heven : 2 ∣ π := by dsimp [π]; exact F.hup_even (b.l + 1) t ht
  have hhalf : (π / 2) % 64 = 32 := hbad.2
  let q := (π / 2) / 64
  have hhalfEq : π / 2 = 64 * q + 32 := by
    have hdecomp := Nat.mod_add_div (π / 2) 64
    rw [hhalf] at hdecomp
    dsimp [q]
    omega
  have hpiTwice : π = 2 * (π / 2) := by
    have hrem := Nat.mod_add_div π 2
    have hzero : π % 2 = 0 := Nat.mod_eq_zero_of_dvd heven
    rw [hzero] at hrem
    omega
  have hπ : π = 64 * (2 * q + 1) := by
    rw [hpiTwice, hhalfEq]
    dsimp [q]
    omega
  have hsize : ∀ j : Fin 64, (s j).card = π + 64 * τ := by
    intro j
    dsimp [s, F, π, τ]
    rw [wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht)]
    exact (flowSizes7 d hd).hsplit
      (b.child j.val j.isLt hchild).l t
      (b.child j.val j.isLt hchild).hl ht
  have hcard : ∀ j : Fin 64, (s j).card = 64 * (2 * q + 1 + τ) := by
    intro j
    rw [hsize j, hπ]
    omega
  have hπcard : ∀ j : Fin 64, π ≤ (s j).card := by
    intro j
    rw [hsize j]
    omega
  have hdis : ∀ j ∈ List.finRange 64, ∀ k ∈ List.finRange 64,
      j ≠ k → Disjoint (s j) (s k) := by
    intro j hj k hk hne
    apply wireSets_disjoint F (Nat.le_of_lt ht)
    intro heq
    apply hne
    exact Fin.ext (KBag.child_inj b j.val k.val j.isLt k.isLt hchild heq)
  obtain ⟨net, hdepth, hlayout⟩ :=
    parallelUpFringeEndpointRepair_packetLayout (α := α)
      (List.finRange 64) (List.nodup_finRange 64) s π q
      (fun _ => 2 * q + 1 + τ) hπ hcard hπcard hdis
  refine ⟨q, ?_, net, hdepth, ?_⟩
  · simpa [π] using hπ
  · intro v hv j
    have hsorted : ∀ i ∈ List.finRange 64, PacketSortedOn (s i) v := by
      intro i hi
      simpa [s] using hv i
    have h := hlayout v hsorted j (by simp)
    simpa [s, π, upFringePairSupport] using h

end Chvatal.PacketAlignment
