import CandidateSeed
import RaggedFlowContract
import RaggedBootstrapFlow
import AddressDebt
import BootstrapTailSlack
import VariableWindow
import Mathlib.Tactic

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

set_option maxRecDepth 1000

namespace Tapered945

open Chvatal

/-
Stage-one rank audit.

CandidateSeed's placement theorem fixes the cardinality/ownership of each bag,
and RaggedFlowContract certifies row-aligned separator boundaries. Neither
theorem states where the keys in a stage-one bag lie in the parent's value
order. The lemmas below isolate the exact extra input-tail premises needed to
obtain hL/hR. They use only the elementary interval-count estimate.
-/

/-- Moving a lower cut right by `delta` can add at most `delta` keys.
This is the usable hL interface when the base left outsider tail is known. -/
theorem input_left_tail_of_cut
    (K : Finset ℕ) (base cut : ℕ) (OL : ℝ)
    (hbase : ((K.filter (· < base)).card : ℝ) ≤ OL)
    (hcut : base ≤ cut) :
    ((K.filter (· < cut)).card : ℝ) ≤ OL + (cut - base : ℝ) := by
  have hc := Chvatal.BW.prefix_count_le_of_cut K base cut hcut
  have hnat : (K.filter (· < cut)).card ≤
      (K.filter (· < base)).card + (cut - base) := hc
  have hcast : ((K.filter (· < cut)).card : ℝ) ≤
      ((K.filter (· < base)).card : ℝ) + (cut - base : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- Moving an upper cut left by `delta` can add at most `delta` keys.
This is the corresponding hR interface. -/
theorem input_right_tail_of_cut
    (K : Finset ℕ) (cut base : ℕ) (OR : ℝ)
    (hbase : ((K.filter (base ≤ ·)).card : ℝ) ≤ OR)
    (hcut : cut ≤ base) :
    ((K.filter (cut ≤ ·)).card : ℝ) ≤ OR + (base - cut : ℝ) := by
  have hc := Chvatal.BW.suffix_count_le_of_cut K cut base hcut
  have hnat : (K.filter (cut ≤ ·)).card ≤
      (base - cut) + (K.filter (base ≤ ·)).card := hc
  have hcast : ((K.filter (cut ≤ ·)).card : ℝ) ≤
      (base - cut : ℝ) + ((K.filter (base ≤ ·)).card : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- Candidate placement supplies the parent bag's exact population. It does
not supply either tail premise needed by the preceding cut lemmas. -/
theorem candidate_seed_stage_one_bag_card
    (d : ℕ) (hd : 14 ≤ d) (q : KBag 64 d) :
    ((candidateSeedPlacement d hd 1 (by omega)).regs q).card =
      (candidateSeedFlowSizes d hd).a q.l 1 :=
  candidateSeedPlacement_card d hd 1 (by omega) q

/-- Keys below a bag's native interval are among its order-one strangers. -/
theorem native_left_tail_le_strangers {d : ℕ} (q : KBag 64 d)
    (hq : q.l < d) (K : Finset (Fin (64 ^ d))) :
    ((K.image Fin.val).filter (· < q.x * 64 ^ (d - q.l))).card ≤
      q.strangers 1 id K := by
  rw [Chvatal.card_filter_val]
  rw [Chvatal.strangers_one_eq]
  apply Finset.card_le_card
  intro κ hκ
  simp only [Finset.mem_filter] at hκ ⊢
  refine ⟨hκ.1, ?_⟩
  intro hn
  have hn' := (Chvatal.native_self_iff q hq κ).mp hn
  omega

/-- Keys above a bag's native interval are among its order-one strangers. -/
theorem native_right_tail_le_strangers {d : ℕ} (q : KBag 64 d)
    (hq : q.l < d) (K : Finset (Fin (64 ^ d))) :
    ((K.image Fin.val).filter
      (q.x * 64 ^ (d - q.l) + 64 * 64 ^ (d - q.l - 1) ≤ ·)).card ≤
      q.strangers 1 id K := by
  rw [Chvatal.card_filter_val]
  rw [Chvatal.strangers_one_eq]
  apply Finset.card_le_card
  intro κ hκ
  simp only [Finset.mem_filter] at hκ ⊢
  refine ⟨hκ.1, ?_⟩
  intro hn
  have hn' := (Chvatal.native_self_iff q hq κ).mp hn
  omega

/-- At the first initialized stage, a level-one register consists only of
the root's down-flow: all level-two registers were empty before stage zero,
so their up-flow contributes no keys. -/
theorem candidate_seed_stage_one_exec_register_eq_fromParent
    (d : ℕ) (hd : 14 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (j : Fin 64) :
    let F := candidateSeedFlowSizes d hd
    let q := (KBag.root 64 d).child j.val j.isLt (by simp [KBag.root]; omega)
    (Chvatal.execPlacement F nets v 1 (by omega)).regs q =
      Chvatal.fromParentK F nets v 0 q := by
  dsimp
  let F := candidateSeedFlowSizes d hd
  let q := (KBag.root 64 d).child j.val j.isLt (by simp [KBag.root]; omega)
  have hq : q.l = 1 := by simp [q, KBag.root, KBag.child_l]
  have hqtop : q.l < d := by rw [hq]; omega
  have hchildren : Chvatal.fromChildrenK F nets v 0 q = ∅ := by
    unfold Chvatal.fromChildrenK
    simp only [dif_pos hqtop]
    ext κ
    constructor
    · intro hmem
      obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hmem
      have hne : q.child k.val k.isLt hqtop ≠ KBag.root 64 d := by
        intro heq
        have hl := congrArg KBag.l heq
        simp [KBag.child_l, hq, KBag.root] at hl
      have hwire := Chvatal.wireSets_zero_of_ne F hne
      have hup : Chvatal.upSet (∅ : Finset (Fin (64 ^ d)))
          (F.up (q.l + 1) 0) = ∅ := by
        simp [Chvatal.upSet, Chvatal.blockOf, Chvatal.rankIn]
      rw [hwire, hup] at hk
      have : False := by simpa using hk
      exact this.elim
    · intro hk
      simp at hk
  have hstep := Chvatal.execPlacement_succ_regs F nets v 0 (by omega) q
    (by omega)
  rw [hchildren, Finset.union_empty] at hstep
  exact hstep

/-! The root outsider estimate establishes the base hL/hR tails for the
actual level-one bag input: a left- or right-external key is necessarily an
order-one stranger. This adapter does not identify later ragged child cuts
or prove the transition itself. -/
theorem candidate_seed_root_child_native_input_tails
    (d : ℕ) (hd : 14 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d)))
    (hspec : NodeSpec (seedRootInput d) 0 (seedRootDown d)
      (nets 0 (KBag.root 64 d) (seedRootInput d))
      (specEB 0 (seedRootInput d)) (specJmax 0) eps)
    (j : Fin 64) :
    let q := (KBag.root 64 d).child j.val j.isLt (by simp [KBag.root]; omega)
    let K := (Chvatal.execPlacement (candidateSeedFlowSizes d hd) nets v 1 (by omega)).regs q
    (((K.image Fin.val).filter (· < q.x * 64 ^ (d - q.l))).card : ℝ) ≤
        paperRootEpsB * (64 : ℝ) ^ d ∧
      (((K.image Fin.val).filter
        (q.x * 64 ^ (d - q.l) + 64 * 64 ^ (d - q.l - 1) ≤ ·)).card : ℝ) ≤
        paperRootEpsB * (64 : ℝ) ^ d := by
  dsimp
  let q := (KBag.root 64 d).child j.val j.isLt (by simp [KBag.root]; omega)
  let F := candidateSeedFlowSizes d hd
  let K := (Chvatal.execPlacement F nets v 1 (by omega)).regs q
  have hK : K = Chvatal.fromParentK F nets v 0 q := by
    simpa [K, F] using candidate_seed_stage_one_exec_register_eq_fromParent d hd nets v j
  have hq : q.l < d := by
    change (KBag.root 64 d).l + 1 < d
    simp [KBag.root]
    omega
  have hstr : (q.strangers 1 id K : ℝ) ≤ paperRootEpsB * (64 : ℝ) ^ d := by
    simpa [q, K, hK] using
      candidateSeed_root_child_outsider_bound d hd nets v hspec j
  have hleft := native_left_tail_le_strangers q hq K
  have hright := native_right_tail_le_strangers q hq K
  constructor
  · have hcast : ((K.image Fin.val).filter
        (· < q.x * 64 ^ (d - q.l))).card ≤ q.strangers 1 id K := hleft
    have hcastR : (((K.image Fin.val).filter
        (· < q.x * 64 ^ (d - q.l))).card : ℝ) ≤ (q.strangers 1 id K : ℝ) := by
      exact_mod_cast hcast
    simpa [q, K] using hcastR.trans hstr
  · have hcast : ((K.image Fin.val).filter
        (q.x * 64 ^ (d - q.l) + 64 * 64 ^ (d - q.l - 1) ≤ ·)).card ≤
        q.strangers 1 id K := hright
    have hcastR : (((K.image Fin.val).filter
        (q.x * 64 ^ (d - q.l) + 64 * 64 ^ (d - q.l - 1) ≤ ·)).card : ℝ) ≤
        (q.strangers 1 id K : ℝ) := by
      exact_mod_cast hcast
    simpa [q, K] using hcastR.trans hstr

/-- The integer bootstrap slot widths and half-fringe exactly realize the
signed address profile used by the cumulative prefix/suffix estimates. -/
theorem bootstrap_stage_one_signed_slack
    {d : ℕ} (hd : 14 ≤ d) (b : KBag 64 d) (hb : b.l = 1)
    (j : ℕ) (hj1 : 1 ≤ j) (hj62 : j ≤ 62) :
    let C : Rat := seedRootDown d
    let p : ℕ := bootstrapUpRows b.x * bootstrapColumns d / 2
    let pre : ℕ := ∑ i ∈ Finset.range j,
      bootstrapSlotRows b.x i * bootstrapColumns d
    let tau : ℕ := bootstrapSlotRows b.x j * bootstrapColumns d
    let post : ℕ := ∑ i ∈ Finset.Ioc j 63,
      bootstrapSlotRows b.x i * bootstrapColumns d
    (j : Rat) * C / 64 ≤ (pre : Rat) + (p : Rat) + C / (2 * cap) +
        (32 - j : Rat) * bagAddressDebt b * C / 64 ∧
      (63 - j : ℕ) * C / 64 ≤ (post : Rat) + (p : Rat) + C / (2 * cap) +
        (j - 31 : Rat) * bagAddressDebt b * C / 64 := by
  dsimp
  let C : Rat := seedRootDown d
  let p : Nat := bootstrapUpRows b.x * bootstrapColumns d / 2
  let pre : Nat := ∑ i ∈ Finset.range j,
    bootstrapSlotRows b.x i * bootstrapColumns d
  let tau : Nat := bootstrapSlotRows b.x j * bootstrapColumns d
  let post : Nat := ∑ i ∈ Finset.Ioc j 63,
    bootstrapSlotRows b.x i * bootstrapColumns d
  have hx : b.x < 64 := by
    have h := b.hx
    rw [hb] at h
    norm_num at h ⊢
    exact h
  have hdebt : bagAddressDebt b = firstAddressDebt b.x := by
    unfold bagAddressDebt firstAddressDebt
    rw [hb]
    have hrec : addressDebt 1 b.x = addressQ b.x / 64 := by
      simp [addressDebt, debtStep, Nat.mod_eq_of_lt hx]
    rw [hrec]
    simp [addressQ, bootstrapAddressQ, isEndAddress]
  have hhalf : (p : Rat) = bootstrapHalfUpWires d b.x := by
    obtain ⟨k, hk⟩ := bootstrap_up_rows_even b.x
    have hrows : bootstrapUpRows b.x = k + k := hk
    have hleft : bootstrapUpRows b.x * bootstrapColumns d / 2 =
        k * bootstrapColumns d := by
      rw [hrows, Nat.add_mul]
      omega
    have hright : bootstrapUpRows b.x / 2 * bootstrapColumns d =
        k * bootstrapColumns d := by
      rw [hrows]
      have hdiv : (k + k) / 2 = k := by omega
      rw [hdiv]
    dsimp [p, bootstrapHalfUpWires]
    rw [hleft, hright]
  have hpre : (pre : Rat) = bootstrapPrefixWires d b.x j := by
    dsimp [pre, bootstrapPrefixWires]
  have hpost : (post : Rat) = bootstrapSuffixWires d b.x j := by
    dsimp [post, bootstrapSuffixWires]
  have hleft := bootstrap_prefix_tail_slack d hd b.x j hj1 (by omega)
  have hright := bootstrap_suffix_tail_slack d hd b.x j hj1 hj62
  rw [← hpre, ← hhalf, ← hdebt] at hleft
  rw [← hpost, ← hhalf, ← hdebt] at hright
  have hres : 0 ≤ (seedRootDown d : Rat) / (2 * cap) := by
    have hc : 0 < cap := by norm_num [cap]
    positivity
  constructor
  · have hnorm : (j : Rat) * (seedRootDown d : Rat) / 64 =
        (j : Rat) * ((seedRootDown d : Rat) / 64) := by ring
    rw [hnorm]
    rw [hleft]
    linarith [hres]
  · have hnorm : ((63 - j : ℕ) : Rat) * (seedRootDown d : Rat) / 64 =
        ((63 - j : ℕ) : Rat) * ((seedRootDown d : Rat) / 64) := by ring
    rw [hnorm]
    rw [hright]
    linarith [hres]
/-- Actual level-one input tails at the native child cuts. The uniform
native child has width `C/64`, while `pre`/`post` use the address-dependent
integer slot widths. The signed slack lemma bridges exactly these two
quantities. This proves the input hL/hR obligations, not network output
correctness. -/
theorem candidate_bootstrap_stage_one_input_tails
    (d : ℕ) (hd : 14 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d)))
    (hspec : NodeSpec (seedRootInput d) 0 (seedRootDown d)
      (nets 0 (KBag.root 64 d) (seedRootInput d))
      (specEB 0 (seedRootInput d)) (specJmax 0) eps)
    (a : Fin 64) (j : ℕ) (hj1 : 1 ≤ j) (hj62 : j ≤ 62) :
    let b := (KBag.root 64 d).child a.val a.isLt (by simp [KBag.root]; omega)
    let K := ((Chvatal.execPlacement (candidateSeedFlowSizes d hd)
      nets v 1 (by omega)).regs b).image Fin.val
    let p := bootstrapUpRows b.x * bootstrapColumns d / 2
    let pre := ∑ i ∈ Finset.range j, bootstrapSlotRows b.x i * bootstrapColumns d
    let post := ∑ i ∈ Finset.Ioc j 63,
      bootstrapSlotRows b.x i * bootstrapColumns d
    let U := b.x * 64 ^ (d - b.l)
    let S := 64 ^ (d - b.l - 1)
    let lo := U + j * S
    let hi := U + (j + 1) * S
    let OL := ((K.filter (· < U)).card : ℝ)
    let OR := ((K.filter (U + 64 * S ≤ ·)).card : ℝ)
    ((K.filter (· < lo)).card : ℝ) ≤
        OL + (pre : ℝ) + (p : ℝ) +
        (((seedRootDown d : Rat) / (2 * cap) +
            (32 - j : Rat) * bagAddressDebt b * seedRootDown d / 64 : Rat) : ℝ) ∧
      ((K.filter (hi ≤ ·)).card : ℝ) ≤
        OR + (post : ℝ) + (p : ℝ) +
          (((seedRootDown d : Rat) / (2 * cap) +
            (j - 31 : Rat) * bagAddressDebt b * seedRootDown d / 64 : Rat) : ℝ) ∧
      OL ≤ Chvatal.paperRootEpsB * (64 : ℝ) ^ d ∧
      OR ≤ Chvatal.paperRootEpsB * (64 : ℝ) ^ d := by
  dsimp
  let b := (KBag.root 64 d).child a.val a.isLt (by simp [KBag.root]; omega)
  let K := ((Chvatal.execPlacement (candidateSeedFlowSizes d hd)
      nets v 1 (by omega)).regs b).image Fin.val
  let p := bootstrapUpRows b.x * bootstrapColumns d / 2
  let pre := ∑ i ∈ Finset.range j, bootstrapSlotRows b.x i * bootstrapColumns d
  let post := ∑ i ∈ Finset.Ioc j 63,
      bootstrapSlotRows b.x i * bootstrapColumns d
  let U := b.x * 64 ^ (d - b.l)
  let S := 64 ^ (d - b.l - 1)
  let lo := U + j * S
  let hi := U + (j + 1) * S
  let OL : ℝ := ((K.filter (· < U)).card : ℝ)
  let OR : ℝ := ((K.filter (U + 64 * S ≤ ·)).card : ℝ)
  have hb : b.l = 1 := by simp [b, KBag.root, KBag.child_l]
  have hq : b.l < d := by rw [hb]; omega
  have hKbase := candidate_seed_root_child_native_input_tails d hd nets v hspec a
  have hbaseL : ((K.filter (· < U)).card : ℝ) ≤ OL := le_of_eq rfl
  have hbaseR : ((K.filter (U + 64 * S ≤ ·)).card : ℝ) ≤ OR := le_of_eq rfl
  have hcutL := input_left_tail_of_cut K U lo OL hbaseL (by dsimp [lo]; omega)
  have hcutR := input_right_tail_of_cut K hi (U + 64 * S) OR hbaseR (by
    dsimp [hi, U, S]
    have hj64 : j + 1 ≤ 64 := by omega
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj64) _)
  have hS : 64 * S = seedRootDown d := by
    dsimp [S]
    rw [hb]
    unfold seedRootDown
    change 64 * 64 ^ (d - 2) = 2 ^ (6 * d - 6)
    calc
      64 * 64 ^ (d - 2) = 64 ^ (d - 2) * 64 := by ring
      _ = 64 ^ (d - 1) := by rw [← pow_succ]; congr 1 <;> omega
      _ = (2 ^ 6) ^ (d - 1) := by rw [show (64 : ℕ) = 2 ^ 6 by norm_num]
      _ = 2 ^ (6 * (d - 1)) := by rw [pow_mul]
      _ = 2 ^ (6 * d - 6) := by congr 1 <;> omega
  have hgapL : (lo - U : ℕ) = j * S := by dsimp [lo]; omega
  have hgapR : (U + 64 * S - hi : ℕ) = (63 - j) * S := by
    dsimp [hi]
    have hjmul : (j + 1) * S = j * S + S := by rw [Nat.add_mul]; simp
    rw [hjmul]
    calc
      U + 64 * S - (U + (j * S + S)) = 64 * S - (j * S + S) := by omega
      _ = (64 - (j + 1)) * S := by rw [← hjmul, ← Nat.sub_mul]
      _ = (63 - j) * S := by congr 1 <;> omega
  have hbudget := bootstrap_stage_one_signed_slack hd b hb j hj1 hj62
  have hleftRat : (j : Rat) * seedRootDown d / 64 ≤
      (pre : Rat) + (p : Rat) + seedRootDown d / (2 * cap) +
        (32 - j : Rat) * bagAddressDebt b * seedRootDown d / 64 := hbudget.1
  have hrightRat : (63 - j : ℕ) * seedRootDown d / 64 ≤
      (post : Rat) + (p : Rat) + seedRootDown d / (2 * cap) +
        (j - 31 : Rat) * bagAddressDebt b * seedRootDown d / 64 := hbudget.2
  have hgapLReal : ((lo - U : ℕ) : ℝ) ≤
      (pre : ℝ) + (p : ℝ) +
        (((seedRootDown d : Rat) / (2 * cap) +
          (32 - j : Rat) * bagAddressDebt b * seedRootDown d / 64 : Rat) : ℝ) := by
    rw [hgapL]
    have hscale : (seedRootDown d : Rat) / 64 = (S : Rat) := by
      have hSrat : (64 : Rat) * (S : Rat) = seedRootDown d := by
        exact_mod_cast hS
      rw [← hSrat]
      norm_num
    have hcast : ((j * S : ℕ) : Rat) =
        (j : Rat) * seedRootDown d / 64 := by
      push_cast
      calc
        (j : Rat) * (S : Rat) = (j : Rat) * ((seedRootDown d : Rat) / 64) := by
          rw [hscale]
        _ = (j : Rat) * seedRootDown d / 64 := by ring
    have hreal : ((j * S : ℕ) : Rat) ≤
        (pre : Rat) + (p : Rat) + seedRootDown d / (2 * cap) +
          (32 - j : Rat) * bagAddressDebt b * seedRootDown d / 64 := by
      rw [hcast]
      exact hleftRat
    have hrealR' : ((j * S : ℕ) : ℝ) ≤
        ((pre + p : ℕ) : ℝ) +
          ((seedRootDown d : Rat) / (2 * cap) : ℝ) +
          (((32 - j : Rat) * bagAddressDebt b * seedRootDown d / 64 : Rat) : ℝ) := by
      exact_mod_cast hreal
    have hpreadd : ((pre + p : ℕ) : ℝ) = (pre : ℝ) + (p : ℝ) := by norm_cast
    rw [hpreadd] at hrealR'
    calc
      ((j * S : ℕ) : ℝ) ≤ (pre : ℝ) + (p : ℝ) +
          ((seedRootDown d : Rat) / (2 * cap) : ℝ) +
          (((32 - j : Rat) * bagAddressDebt b * seedRootDown d / 64 : Rat) : ℝ) := hrealR'
      _ = (pre : ℝ) + (p : ℝ) +
          (((seedRootDown d : Rat) / (2 * cap) +
            (32 - j : Rat) * bagAddressDebt b * seedRootDown d / 64 : Rat) : ℝ) := by push_cast; ring
  have hgapRReal : ((U + 64 * S - hi : ℕ) : ℝ) ≤
      (post : ℝ) + (p : ℝ) +
        (((seedRootDown d : Rat) / (2 * cap) +
          (j - 31 : Rat) * bagAddressDebt b * seedRootDown d / 64 : Rat) : ℝ) := by
    rw [hgapR]
    have hscale : (seedRootDown d : Rat) / 64 = (S : Rat) := by
      have hSrat : (64 : Rat) * (S : Rat) = seedRootDown d := by
        exact_mod_cast hS
      rw [← hSrat]
      norm_num
    have hcast : (((63 - j) * S : ℕ) : Rat) =
        ((63 - j : ℕ) : Rat) * seedRootDown d / 64 := by
      push_cast
      calc
        ((63 - j : ℕ) : Rat) * (S : Rat) =
            ((63 - j : ℕ) : Rat) * ((seedRootDown d : Rat) / 64) := by
          rw [hscale]
        _ = ((63 - j : ℕ) : Rat) * seedRootDown d / 64 := by ring
    have hreal : (((63 - j) * S : ℕ) : Rat) ≤
        (post : Rat) + (p : Rat) + seedRootDown d / (2 * cap) +
          (j - 31 : Rat) * bagAddressDebt b * seedRootDown d / 64 := by
      rw [hcast]
      exact hrightRat
    have hrealR' : (((63 - j) * S : ℕ) : ℝ) ≤
        ((post + p : ℕ) : ℝ) +
          ((seedRootDown d : Rat) / (2 * cap) : ℝ) +
          (((j - 31 : Rat) * bagAddressDebt b * seedRootDown d / 64 : Rat) : ℝ) := by
      exact_mod_cast hreal
    have hpostadd : ((post + p : ℕ) : ℝ) = (post : ℝ) + (p : ℝ) := by norm_cast
    rw [hpostadd] at hrealR'
    calc
      (((63 - j) * S : ℕ) : ℝ) ≤ (post : ℝ) + (p : ℝ) +
          ((seedRootDown d : Rat) / (2 * cap) : ℝ) +
          (((j - 31 : Rat) * bagAddressDebt b * seedRootDown d / 64 : Rat) : ℝ) := hrealR'
      _ = (post : ℝ) + (p : ℝ) +
          (((seedRootDown d : Rat) / (2 * cap) +
            (j - 31 : Rat) * bagAddressDebt b * seedRootDown d / 64 : Rat) : ℝ) := by push_cast; ring
  constructor
  · calc
      ((K.filter (· < lo)).card : ℝ) ≤ OL + ((lo - U : ℕ) : ℝ) := by
        have h := hcutL
        have hle : U ≤ lo := by dsimp [lo, U]; omega
        rw [← Nat.cast_sub hle] at h
        simpa [OL] using h
      _ ≤ OL + (pre : ℝ) + (p : ℝ) +
          (((seedRootDown d : Rat) / (2 * cap) +
            (32 - j : Rat) * bagAddressDebt b * seedRootDown d / 64 : Rat) : ℝ) := by
        linarith [hgapLReal]
  · constructor
    · have hcutR' : ((K.filter (hi ≤ ·)).card : ℝ) ≤
          OR + (((U + 64 * S - hi : ℕ) : ℝ)) := by
        have htmp := hcutR
        have hle : hi ≤ U + 64 * S := by
          dsimp [hi, U]
          exact Nat.add_le_add_left
            (Nat.mul_le_mul_right S (by omega : j + 1 ≤ 64)) U
        rw [← Nat.cast_sub hle] at htmp
        exact htmp
      calc
        ((K.filter (hi ≤ ·)).card : ℝ) ≤
            OR + (((U + 64 * S - hi : ℕ) : ℝ)) := hcutR'
        _ ≤ OR + (post : ℝ) + (p : ℝ) +
            (((seedRootDown d : Rat) / (2 * cap) +
              (j - 31 : Rat) * bagAddressDebt b * seedRootDown d / 64 : Rat) : ℝ) := by
          linarith [hgapRReal]
    · have hbase := candidate_seed_root_child_native_input_tails d hd nets v hspec a
      constructor
      · simpa [OL, K, U, b] using hbase.1
      · simpa [OR, K, U, S, b, hS, seedRootDown] using hbase.2

set_option maxRecDepth 1000

/-- A precise conditional hL/hR interface for one variable-width child.

Here `nativeLo` and `nativeHi` are the parent's native interval endpoints;
`childLo` and `childHi` are the two cumulative row cuts supplied by a
RaggedFlowContract (after conversion to key coordinates by the caller).
The missing mathematical content is exactly `hbaseL` and `hbaseR`: bounds
on the key tails of the *input bag*. Separator crossing guarantees alone do
not establish them. -/
theorem variable_child_input_tails
    (K : Finset ℕ) (nativeLo childLo childHi nativeHi : ℕ)
    (OL OR : ℝ)
    (hbaseL : ((K.filter (· < nativeLo)).card : ℝ) ≤ OL)
    (hbaseR : ((K.filter (nativeHi ≤ ·)).card : ℝ) ≤ OR)
    (hleft : nativeLo ≤ childLo)
    (hright : childHi ≤ nativeHi) :
    ((K.filter (· < childLo)).card : ℝ) ≤
        OL + (childLo - nativeLo : ℝ) ∧
      ((K.filter (childHi ≤ ·)).card : ℝ) ≤
        OR + (nativeHi - childHi : ℝ) := by
  exact ⟨input_left_tail_of_cut K nativeLo childLo OL hbaseL hleft,
    input_right_tail_of_cut K childHi nativeHi OR hbaseR hright⟩

/-- The row-coordinate cuts of a ragged profile are ordered as expected.
This is the geometric fact available from RaggedFlowContract; translating it
to key indices also requires the common positive column count `n`. -/
theorem ragged_child_cut_order
    {m : ℕ} (profile : RaggedFlowContract m)
    (j : ℕ) (hj : j ≤ 64) :
    profile.start ≤ profile.start + raggedPrefixRows profile.width j ∧
      profile.start + raggedPrefixRows profile.width j ≤
        profile.start + raggedPrefixRows profile.width 64 ∧
      profile.start + raggedPrefixRows profile.width 64 ≤ m := by
  have hmono : raggedPrefixRows profile.width j ≤
      raggedPrefixRows profile.width 64 := by
    unfold raggedPrefixRows
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono hj) (by intro i hi hnot; exact Nat.zero_le _)
  have hlast := profile.prefix_bound 64 (by omega)
  exact ⟨Nat.le_add_right _ _, Nat.add_le_add_left hmono _,
    hlast.trans (Nat.sub_le _ _)⟩

/-- The fully instantiated cut-count interface for a ragged child block.
The bounds are stated in key coordinates: one row contains `n` keys, the
profile starts after `profile.start` rows, and the parent extends to row `m`.
The profile certificate proves these cuts lie in the parent interval. The
input-tail hypotheses remain explicit because neither placement counts nor
separator crossing estimates establish them. -/
theorem ragged_profile_input_tails
    {m n : ℕ} (hn : 0 < n) (profile : RaggedFlowContract m)
    (K : Finset ℕ) (nativeLo : ℕ) (OL OR : ℝ)
    (hbaseL : ((K.filter (· < nativeLo)).card : ℝ) ≤ OL)
    (hbaseR : ((K.filter (nativeLo + m * n ≤ ·)).card : ℝ) ≤ OR)
    (j : ℕ) (hj : j < 64) :
    ((K.filter (· < nativeLo +
        (profile.start + raggedPrefixRows profile.width j) * n)).card : ℝ) ≤
        OL + ((profile.start + raggedPrefixRows profile.width j) * n : ℝ) ∧
      ((K.filter (nativeLo +
        (profile.start + raggedPrefixRows profile.width (j + 1)) * n ≤ ·)).card : ℝ) ≤
        OR + ((((m - (profile.start + raggedPrefixRows profile.width (j + 1))) * n : ℕ) : ℝ)) := by
  have hleft : nativeLo ≤ nativeLo +
      (profile.start + raggedPrefixRows profile.width j) * n := by omega
  have hprefix := profile.prefix_bound (j + 1) (by omega)
  have hrows : profile.start + raggedPrefixRows profile.width (j + 1) ≤ m :=
    hprefix.trans (Nat.sub_le _ _)
  have hright : nativeLo +
      (profile.start + raggedPrefixRows profile.width (j + 1)) * n ≤ nativeLo + m * n := by
    exact Nat.add_le_add_left (Nat.mul_le_mul_right n hrows) nativeLo
  have hL := input_left_tail_of_cut K nativeLo
    (nativeLo + (profile.start + raggedPrefixRows profile.width j) * n) OL hbaseL hleft
  have hR := input_right_tail_of_cut K
    (nativeLo + (profile.start + raggedPrefixRows profile.width (j + 1)) * n)
    (nativeLo + m * n) OR hbaseR hright
  constructor
  · have hdiff : nativeLo + (profile.start + raggedPrefixRows profile.width j) * n - nativeLo =
        (profile.start + raggedPrefixRows profile.width j) * n := by omega
    simpa [hdiff] using hL
  · have hdiff : nativeLo + m * n -
        (nativeLo + (profile.start + raggedPrefixRows profile.width (j + 1)) * n) =
        (m - (profile.start + raggedPrefixRows profile.width (j + 1))) * n := by
      have hcancel : nativeLo + m * n -
          (nativeLo + (profile.start + raggedPrefixRows profile.width (j + 1)) * n) =
          m * n - (profile.start + raggedPrefixRows profile.width (j + 1)) * n := by omega
      rw [hcancel, ← Nat.sub_mul]
    have hdiffR :
        ((nativeLo + m * n -
          (nativeLo + (profile.start + raggedPrefixRows profile.width (j + 1)) * n) : ℕ) : ℝ) =
        (((m - (profile.start + raggedPrefixRows profile.width (j + 1))) * n : ℕ) : ℝ) := by
      exact_mod_cast hdiff
    calc
      _ ≤ OR + (((nativeLo + m * n : ℕ) : ℝ) -
          ((nativeLo + (profile.start + raggedPrefixRows profile.width (j + 1)) * n : ℕ) : ℝ)) := by
        convert hR using 1 <;> ring
      _ = OR + (((m - (profile.start + raggedPrefixRows profile.width (j + 1))) * n : ℕ) : ℝ) := by
        rw [← Nat.cast_sub hright, hdiffR]

/-
What is still needed to turn this interface into the desired stage-1→2
instance:

1. A precise identification of the input set K for each stage-one sender with
   a CandidateSeed placement register (the current placement is count-only).
2. Bounds hbaseL/hbaseR for that K relative to the parent's native interval.
   No current CandidateSeed placement theorem implies these: an arbitrary
   permutation of the owned keys preserves all its stated facts.
3. A theorem translating each address-dependent child width/cumulative count
   into the key-coordinate cuts childLo/childHi, with the relevant conversion
   factor and endpoint fringe accounted for.
4. A transition theorem showing the scheduler's assigned ranks/keys after the
   local network realize those child intervals. RaggedFlowContract only gives
   admissible separator cuts and crossing bounds, not this assignment.
-/

end Tapered945

