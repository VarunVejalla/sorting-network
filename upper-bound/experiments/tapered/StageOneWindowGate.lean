import RaggedStageOneRank
import Mathlib.Tactic

namespace Tapered945

open Chvatal

set_option maxHeartbeats 1000000

private theorem bootstrap_slot_sum_split (d x j : Nat) (hj : j < 64) :
    (∑ i ∈ Finset.range j, bootstrapSlotRows x i * bootstrapColumns d) +
      bootstrapSlotRows x j * bootstrapColumns d +
      (∑ i ∈ Finset.Ioc j 63, bootstrapSlotRows x i * bootstrapColumns d) =
        ∑ i ∈ Finset.range 64, bootstrapSlotRows x i * bootstrapColumns d := by
  let f : Nat → Nat := fun i => bootstrapSlotRows x i * bootstrapColumns d
  let A := Finset.range j
  let B : Finset Nat := {j}
  let C := Finset.Ioc j 63
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hi hbi
    simp [A, B] at hi hbi
    omega
  have hABC : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro i hi hci
    simp only [Finset.mem_union] at hi
    simp [A, B, C] at hi hci
    rcases hi with h | h <;> omega
  have hunion : Finset.range 64 = A ∪ B ∪ C := by
    ext i
    simp [A, B, C]
    omega
  rw [hunion, Finset.sum_union hABC, Finset.sum_union hAB]
  simp [A, B, C, f]

/-- Exact population split for the actual initialized level-one register into
its up-fringe, address-prefix, current address-slot, and address-suffix. -/
theorem candidate_bootstrap_stage_one_card_split
    (d : Nat) (hd : 14 ≤ d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (a : Fin 64)
    (j : Nat) (hj1 : 1 ≤ j) (hj62 : j ≤ 62) :
    let b := (KBag.root 64 d).child a.val a.isLt (by simp [KBag.root]; omega)
    let K := ((execPlacement (candidateSeedFlowSizes d hd) nets v 1 (by omega)).regs b).image Fin.val
    let p := bootstrapUpRows b.x * bootstrapColumns d / 2
    let pre := ∑ i ∈ Finset.range j, bootstrapSlotRows b.x i * bootstrapColumns d
    let tau := bootstrapSlotRows b.x j * bootstrapColumns d
    let post := ∑ i ∈ Finset.Ioc j 63, bootstrapSlotRows b.x i * bootstrapColumns d
    K.card = 2 * p + pre + tau + post := by
  dsimp
  let b := (KBag.root 64 d).child a.val a.isLt (by simp [KBag.root]; omega)
  let K := ((execPlacement (candidateSeedFlowSizes d hd) nets v 1 (by omega)).regs b).image Fin.val
  let p := bootstrapUpRows b.x * bootstrapColumns d / 2
  let pre := ∑ i ∈ Finset.range j, bootstrapSlotRows b.x i * bootstrapColumns d
  let tau := bootstrapSlotRows b.x j * bootstrapColumns d
  let post := ∑ i ∈ Finset.Ioc j 63, bootstrapSlotRows b.x i * bootstrapColumns d
  have hb : b.l = 1 := by simp [b, KBag.root, KBag.child_l]
  have hK : K.card = seedRootDown d := by
    dsimp [K]
    rw [Finset.card_image_of_injective _ Fin.val_injective]
    rw [execPlacement_card]
    simp [candidateSeedFlowSizes, seedNodeSize, b, hb, seedRootDown]
  obtain ⟨hEven, hUpLe, hblocks, hUpExact, hblockExact⟩ :=
    bootstrap_integer_split_exact d b.x hd
  have hsplit : pre + tau + post =
      seedRootDown d - bootstrapUpRows b.x * bootstrapColumns d := by
    have hsum := bootstrap_slot_sum_split d b.x j (by omega)
    have hfin :
        (∑ i ∈ Finset.range 64, bootstrapSlotRows b.x i * bootstrapColumns d) =
          ∑ i : Fin 64, bootstrapSlotRows b.x i.val * bootstrapColumns d := by
      rw [← Fin.sum_univ_eq_sum_range]
    dsimp [pre, tau, post]
    rw [hsum, hfin]
    exact hblocks
  have h2p : 2 * p = bootstrapUpRows b.x * bootstrapColumns d := by
    obtain ⟨k, hk⟩ := hEven
    dsimp [p]
    rw [hk]
    omega
  calc
    K.card = seedRootDown d := hK
    _ = (bootstrapUpRows b.x * bootstrapColumns d) +
          (seedRootDown d - bootstrapUpRows b.x * bootstrapColumns d) := by omega
    _ = 2 * p + (pre + tau + post) := by rw [h2p, hsplit]
    _ = 2 * p + pre + tau + post := by omega

/-- Compose signed tails without unfolding the actual register representation. -/
theorem bootstrap_window_of_tails
    (K : Finset Nat) (p pre tau post lo hi j x : Nat) (OL OR B : Real) (C : Rat)
    (hcard : K.card = 2 * p + pre + tau + post) (hC : 0 ≤ C)
    (hOL : 0 ≤ OL) (hOR : 0 ≤ OR) (hbudget : OL + OR ≤ B)
    (hj1 : 1 ≤ j) (hj62 : j ≤ 62)
    (hL : ((K.filter (· < lo)).card : Real) ≤ OL + pre + p +
      ((C / (2 * cap) + ((32 : Rat) - j) * debtPath [addressQ x] * C / 64 : Rat) : Real))
    (hR : ((K.filter (hi ≤ ·)).card : Real) ≤ OR + post + p +
      ((C / (2 * cap) + ((j : Rat) - 31) * debtPath [addressQ x] * C / 64 : Rat) : Real)) :
    ((K.filter fun κ => p + pre ≤ BW.rankN K κ ∧
      BW.rankN K κ < p + pre + tau ∧ ¬ (lo ≤ κ ∧ κ < hi)).card : Real) ≤
      B + ((reserve * C : Rat) : Real) := by
  have hq : ∀ q ∈ [addressQ x], qEnd ≤ q ∧ q ≤ qMid := by
    intro q hq
    simp only [List.mem_singleton] at hq
    subst q
    exact addressQ_bounds x
  have hL' : ((K.filter (· < lo)).card : Real) ≤ OL + pre + j * (0 : Real) + p +
      ((C / (2 * cap) + ((32 : Rat) - j) * debtPath [addressQ x] * C / 64 : Rat) : Real) := by
    simpa only [mul_zero, add_zero] using hL
  have hR' : ((K.filter (hi ≤ ·)).card : Real) ≤ OR + post + (63 - j) * (0 : Real) + p +
      ((C / (2 * cap) + ((j : Rat) - 31) * debtPath [addressQ x] * C / 64 : Rat) : Real) := by
    simpa only [mul_zero, add_zero] using hR
  have hw := BW.variable_window_wrong_le_signed_path K p pre tau post lo hi
    OL OR 0 C j [addressQ x] hcard hC hOL hOR (le_refl 0) hj1 hj62 hq hL' hR'
  simp only [mul_zero, add_zero] at hw
  exact hw.trans (add_le_add hbudget (le_refl _))

/-- Wrong ranks in an internal address slot of the actual stage-one input.
This is an input estimate, before the ragged separator executes. -/
theorem candidate_bootstrap_stage_one_wrong_rank_bound
    (d : Nat) (hd : 14 ≤ d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d)))
    (hspec : NodeSpec (seedRootInput d) 0 (seedRootDown d)
      (nets 0 (KBag.root 64 d) (seedRootInput d))
      (specEB 0 (seedRootInput d)) (specJmax 0) eps)
    (a : Fin 64) (j : Nat) (hj1 : 1 ≤ j) (hj62 : j ≤ 62) :
    let b := (KBag.root 64 d).child a.val a.isLt (by simp [KBag.root]; omega)
    let K := ((execPlacement (candidateSeedFlowSizes d hd) nets v 1 (by omega)).regs b).image Fin.val
    let p := bootstrapUpRows b.x * bootstrapColumns d / 2
    let pre := ∑ i ∈ Finset.range j, bootstrapSlotRows b.x i * bootstrapColumns d
    let tau := bootstrapSlotRows b.x j * bootstrapColumns d
    let post := ∑ i ∈ Finset.Ioc j 63, bootstrapSlotRows b.x i * bootstrapColumns d
    let U := b.x * 64 ^ (d - b.l)
    let S := 64 ^ (d - b.l - 1)
    ((K.filter fun κ => p + pre ≤ BW.rankN K κ ∧
      BW.rankN K κ < p + pre + tau ∧ ¬ (U + j * S ≤ κ ∧ κ < U + (j + 1) * S)).card : Real) ≤
      2 * paperRootEpsB * (64 : Real) ^ d + ((reserve * seedRootDown d : Rat) : Real) := by
  intro b K p pre tau post U S
  let OL : Real := (K.filter (· < U)).card
  let OR : Real := (K.filter (U + 64 * S ≤ ·)).card
  have hb : b.l = 1 := by simp [b, KBag.root, KBag.child_l]
  have hx : b.x < 64 := by simpa [b, KBag.child, KBag.root] using a.isLt
  have hdebt : bagAddressDebt b = debtPath [addressQ b.x] := by
    simp [bagAddressDebt, addressDebt, debtPath, debtStep, hb, Nat.mod_eq_of_lt hx]
  obtain ⟨hL, hR, hOL, hOR⟩ :=
    candidate_bootstrap_stage_one_input_tails d hd nets v hspec a j hj1 hj62
  have hL' : ((K.filter (· < U + j * S)).card : Real) ≤ OL + pre + p +
      (((seedRootDown d : Rat) / (2 * cap) + ((32 : Rat) - j) *
        debtPath [addressQ b.x] * seedRootDown d / 64 : Rat) : Real) := by
    rw [← hdebt]
    exact hL
  have hR' : ((K.filter (U + (j + 1) * S ≤ ·)).card : Real) ≤ OR + post + p +
      (((seedRootDown d : Rat) / (2 * cap) + ((j : Rat) - 31) *
        debtPath [addressQ b.x] * seedRootDown d / 64 : Rat) : Real) := by
    rw [← hdebt]
    exact hR
  apply bootstrap_window_of_tails K p pre tau post (U + j * S) (U + (j + 1) * S)
    j b.x OL OR (2 * paperRootEpsB * (64 : Real) ^ d) (seedRootDown d)
    (candidate_bootstrap_stage_one_card_split d hd nets v a j hj1 hj62)
    (by positivity) (by positivity) (by positivity) _ hj1 hj62 hL' hR'
  change OL ≤ paperRootEpsB * (64 : Real) ^ d at hOL
  change OR ≤ paperRootEpsB * (64 : Real) ^ d at hOR
  linarith

end Tapered945
