import RaggedExecution
import SignedReserve
import AKS.Chvatal.FinalSorts
import Mathlib.Tactic

namespace Tapered945
open Chvatal

def terminalGroups {d : Nat} (P : RaggedWirePartition d) (c : KBag 64 d) : Finset (Fin (64^d)) :=
  Finset.univ.biUnion (fun b => if b.parent = c then P.sets b else ∅)

theorem mem_terminalGroups {d : Nat} (P : RaggedWirePartition d) (c : KBag 64 d)
    (w : Fin (64^d)) : w ∈ terminalGroups P c ↔ ∃ b, b.parent = c ∧ w ∈ P.sets b := by
  simp only [terminalGroups, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b, hb⟩
    split_ifs at hb with he
    · exact ⟨b, he, hb⟩
    · simp at hb
  · rintro ⟨b, he, hb⟩
    exact ⟨b, by simpa only [if_pos he] using hb⟩

theorem terminalGroups_disjoint {d : Nat} (P : RaggedWirePartition d)
    (c e : KBag 64 d) (hne : c ≠ e) : Disjoint (terminalGroups P c) (terminalGroups P e) := by
  rw [Finset.disjoint_left]
  intro w hw hw'
  obtain ⟨b, hb, hwb⟩ := (mem_terminalGroups P c w).mp hw
  obtain ⟨b', hb', hwb'⟩ := (mem_terminalGroups P e w).mp hw'
  have he : b = b' := by
    by_contra h
    exact Finset.disjoint_left.mp (P.disjoint b b' h) hwb hwb'
  exact hne (hb.symm.trans (he ▸ hb'))

theorem terminalGroups_cover {d : Nat} (P : RaggedWirePartition d) (w : Fin (64^d)) :
    ∃ c, w ∈ terminalGroups P c := by
  obtain ⟨b,hb⟩ := P.complete w
  exact ⟨b.parent, (mem_terminalGroups P b.parent w).mpr ⟨b,rfl,hb⟩⟩

private theorem fin_interval_card (N base size : Nat) (h : base+size ≤ N) :
    (Finset.univ.filter (fun x : Fin N => base ≤ x.val ∧ x.val < base+size)).card = size := by
  have he : (Finset.univ.filter (fun x : Fin N => base ≤ x.val ∧ x.val < base+size)).map Fin.valEmbedding =
      Finset.Ico base (base+size) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hy
      exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hx).2
    · intro hy
      obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hy
      exact Finset.mem_map.mpr ⟨⟨y,by omega⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlo,hhi⟩,rfl⟩
  have hc := congrArg Finset.card he
  simpa only [Finset.card_map, Nat.card_Ico, Nat.add_sub_cancel_left] using hc

private theorem parent_interval_bounds {d : Nat} (hd : 7 ≤ d) (c : KBag 64 d)
    (hc : c.l = d-7) : c.size = 2^42 ∧ c.lo+c.size ≤ 64^d := by
  have hs : c.size = 2^42 := by
    simp only [KBag.size, bagSize, hc, show d-(d-7)=7 by omega]
    norm_num
  refine ⟨hs, ?_⟩
  have hx : c.x+1 ≤ 64^c.l := Nat.succ_le_of_lt c.hx
  have hp : 64^c.l*c.size = 64^d := by
    simp only [KBag.size, bagSize]
    rw [← pow_add, Nat.add_sub_of_le c.hl]
  have hm := Nat.mul_le_mul_right c.size hx
  rw [hp] at hm
  simpa only [KBag.lo, Nat.add_mul, one_mul] using hm

/-- Parent-native purity forces full parent intervals after grouping. It
does not require exact individual terminal occupancy or own-bag purity. -/
theorem terminalGroups_image {d : Nat} (hd : 7 ≤ d) (P : RaggedWirePartition d)
    (hlevel : ∀ b w, w ∈ P.sets b → b.l = d-6)
    (A : ComparatorNetwork (64^d))
    (hpure : ∀ (p : Equiv.Perm (Fin (64^d))) b w, w ∈ P.sets b →
      b.parent.Native w (A.exec p))
    (p : Equiv.Perm (Fin (64^d))) (c : KBag 64 d) :
    (terminalGroups P c).image (A.exec p) =
      Finset.univ.filter (fun x : Fin (64^d) => c.lo ≤ x.val ∧ x.val < c.lo+(terminalGroups P c).card) := by
  classical
  by_cases hc : c.l = d-7
  · have hnative : (terminalGroups P c).image (A.exec p) =
        Finset.univ.filter (fun x : Fin (64^d) => c.lo ≤ x.val ∧ x.val < c.lo+c.size) := by
      ext key
      constructor
      · intro hk
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hk
        obtain ⟨b, hb, hwb⟩ := (mem_terminalGroups P c w).mp hw
        have hn := hpure p b w hwb
        rw [hb] at hn
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
          have hi := (c.native_iff w (A.exec p) (by norm_num)).mp hn
          rwa [KBag.hi_eq_lo_add_size] at hi⟩
      · intro hk
        have hknative : c.Native key id := by
          apply (c.native_iff key id (by norm_num)).mpr
          simpa only [id_eq, KBag.hi_eq_lo_add_size] using (Finset.mem_filter.mp hk).2
        obtain ⟨ρ, hρ⟩ := ComparatorNetwork.exec_eq_comp_perm A (p : Fin (64^d) → Fin (64^d))
        let w := ρ.symm (p.symm key)
        have hwkey : A.exec p w = key := by rw [hρ]; simp [w]
        obtain ⟨b,hwb⟩ := P.complete w
        have hn := hpure p b w hwb
        have hbl := hlevel b w hwb
        have hbe : b.parent = c := by
          apply KBag.ext
          · simp only [KBag.parent]
            omega
          · have hbNative : nativeBagIdx 64 d b.parent.l key.val = b.parent.x := by
              simpa only [KBag.Native, hwkey] using hn
            have hcNative : nativeBagIdx 64 d c.l key.val = c.x := hknative
            have hpl : b.parent.l = c.l := by simp only [KBag.parent]; omega
            rw [hpl] at hbNative
            exact hbNative.symm.trans hcNative
        exact Finset.mem_image.mpr ⟨w,(mem_terminalGroups P c w).mpr ⟨b,hbe,hwb⟩,hwkey⟩
    have hinj : Function.Injective (A.exec p) := by
      obtain ⟨ρ,hρ⟩ := ComparatorNetwork.exec_eq_comp_perm A (p : Fin (64^d) → Fin (64^d))
      rw [hρ]
      exact p.injective.comp ρ.injective
    have hcard : (terminalGroups P c).card = c.size := by
      have he := congrArg Finset.card hnative
      rw [Finset.card_image_of_injective _ hinj,
        fin_interval_card _ _ _ (parent_interval_bounds hd c hc).2] at he
      exact he
    rw [hcard]
    exact hnative
  · have he : terminalGroups P c = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨b,hb,hwb⟩ := (mem_terminalGroups P c w).mp hw
      have hl := hlevel b w hwb
      have hp := congrArg KBag.l hb
      simp only [KBag.parent] at hp
      omega
    rw [he]
    ext key
    simp

theorem terminalGroups_card_le {d : Nat} (hd : 7 ≤ d) (P : RaggedWirePartition d)
    (hlevel : ∀ b w, w ∈ P.sets b → b.l = d-6)
    (A : ComparatorNetwork (64^d))
    (hpure : ∀ (p : Equiv.Perm (Fin (64^d))) b w, w ∈ P.sets b →
      b.parent.Native w (A.exec p)) (c : KBag 64 d) :
    (terminalGroups P c).card ≤ 2^42 := by
  classical
  by_cases hc : c.l = d-7
  · let p : Equiv.Perm (Fin (64^d)) := 1
    have hinj : Function.Injective (A.exec p) := by
      obtain ⟨ρ,hρ⟩ := ComparatorNetwork.exec_eq_comp_perm A (p : Fin (64^d) → Fin (64^d))
      rw [hρ]
      exact p.injective.comp ρ.injective
    have hsub : (terminalGroups P c).image (A.exec p) ⊆
        Finset.univ.filter (fun x : Fin (64^d) => c.lo ≤ x.val ∧ x.val < c.lo+c.size) := by
      intro key hk
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨b,hb,hwb⟩ := (mem_terminalGroups P c w).mp hw
      have hn := hpure p b w hwb
      rw [hb] at hn
      have hh := (c.native_iff w (A.exec p) (by norm_num)).mp hn
      rw [KBag.hi_eq_lo_add_size] at hh
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj,
      fin_interval_card _ _ _ (parent_interval_bounds hd c hc).2,
      (parent_interval_bounds hd c hc).1] at hcard
    exact hcard
  · have he : terminalGroups P c = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨b,hb,hwb⟩ := (mem_terminalGroups P c w).mp hw
      have hl := hlevel b w hwb
      have hp := congrArg KBag.l hb
      simp only [KBag.parent] at hp
      omega
    simp [he]

/-- Conditional exact finishing sorter; the prefix need only place every key
inside the native interval of its terminal bag's parent. -/
theorem terminal_sorter_of_parent_native {d : Nat} (hd : 7 ≤ d) (P : RaggedWirePartition d)
    (hlevel : ∀ b w, w ∈ P.sets b → b.l = d-6)
    (A : ComparatorNetwork (64^d))
    (hpure : ∀ (p : Equiv.Perm (Fin (64^d))) b w, w ∈ P.sets b →
      b.parent.Native w (A.exec p)) :
    ∃ T : ComparatorNetwork (64^d), ComparatorNetwork.Sorts.{0} T ∧ T.depth ≤ A.depth+903 := by
  obtain ⟨T,hTd,hTs⟩ := final_layer_sorts (terminalGroups P) (terminalGroups_disjoint P)
    (terminalGroups_cover P) (fun c => c.lo) A (terminalGroups_image hd P hlevel A hpure)
  refine ⟨T,hTs,hTd.trans ?_⟩
  have hf : (stageNet (terminalGroups P) (fun _ n => bitonicNetwork n)).depth ≤ 903 := by
    apply stageNet_depth_le (terminalGroups P) (terminalGroups_disjoint P)
    intro c
    have hcard := terminalGroups_card_le hd P hlevel A hpure c
    have hlog := Nat.clog_mono_right 2 hcard
    rw [Nat.clog_pow 2 42 (by norm_num)] at hlog
    have hh := (bitonicNetwork_depth_le_budget (terminalGroups P c).card).trans (bitonicDepthBudget_mono hlog)
    norm_num [bitonicDepthBudget_eq] at hh
    exact hh
  omega

theorem terminal_order_two_budget_lt_one :
    ((mu*delta*(2^36) : Rat) : Real) < 1 := by norm_num [mu,delta]

/-- The integer stranger count vanishes at the meeting capacity. -/
theorem terminal_parent_native_of_order_two {d : Nat} (P : RaggedWirePartition d)
    (A : ComparatorNetwork (64^d))
    (hbudget : ∀ (p : Equiv.Perm (Fin (64^d))) (b : KBag 64 d),
      (b.strangers 2 (A.exec p) (P.sets b) : Real) ≤ ((mu*delta*(2^36) : Rat) : Real)) :
    ∀ (p : Equiv.Perm (Fin (64^d))) b w, w ∈ P.sets b → b.parent.Native w (A.exec p) := by
  intro p b w hw
  have hb : (b.strangers 2 (A.exec p) (P.sets b) : Real) < 1 :=
    (hbudget p b).trans_lt terminal_order_two_budget_lt_one
  have hn : b.strangers 2 (A.exec p) (P.sets b) < 1 := by exact_mod_cast hb
  have hz : b.strangers 2 (A.exec p) (P.sets b) = 0 := by omega
  have ha : b.ancestor (2-1) = b.parent := by
    apply KBag.ext <;> simp [KBag.ancestor,KBag.parent]
  have he : (P.sets b).filter (fun r => b.Strange 2 r (A.exec p)) = ∅ :=
    Finset.card_eq_zero.mp hz
  have hnot := Finset.filter_eq_empty_iff.mp he hw
  simpa only [KBag.Strange, show (2 : Nat) ≠ 0 by omega, false_or, ha, not_not] using hnot

/-- Scheduler-independent terminal gate from its numerical order-two budget. -/
theorem terminal_sorter_of_order_two {d : Nat} (hd : 7 ≤ d) (P : RaggedWirePartition d)
    (hlevel : ∀ b w, w ∈ P.sets b → b.l = d-6)
    (A : ComparatorNetwork (64^d))
    (hbudget : ∀ (p : Equiv.Perm (Fin (64^d))) (b : KBag 64 d),
      (b.strangers 2 (A.exec p) (P.sets b) : Real) ≤ ((mu*delta*(2^36) : Rat) : Real)) :
    ∃ T : ComparatorNetwork (64^d), ComparatorNetwork.Sorts.{0} T ∧ T.depth ≤ A.depth+903 :=
  terminal_sorter_of_parent_native hd P hlevel A (terminal_parent_native_of_order_two P A hbudget)

end Tapered945
