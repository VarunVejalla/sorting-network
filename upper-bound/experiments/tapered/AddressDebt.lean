import AKS.Chvatal.Tree
import IntegerRounding
import Mathlib.Tactic

namespace Tapered945

/-- The two end addresses use the smaller down-flow coefficient; all other
child addresses use the middle coefficient. -/
def addressQ (j : Nat) : Rat :=
  if j = 0 ∨ j = 63 then qEnd else qMid

def addressDownCoeff (j : Nat) : Rat :=
  if j = 0 ∨ j = 63 then rEnd else rMid

/-- Normalized signed debt at address `x` on level `l`. The final base-64
digit is the most recent edge in the debt recurrence. -/
def addressDebt : Nat → Nat → Rat
  | 0, _ => 0
  | l + 1, x => debtStep (addressQ (x % 64)) (addressDebt l (x / 64))

theorem addressQ_bounds (j : Nat) :
    qEnd ≤ addressQ j ∧ addressQ j ≤ qMid := by
  by_cases h : j = 0 ∨ j = 63
  · simp [addressQ, h]
    unfold qEnd qMid
    norm_num
  · simp [addressQ, h]
    unfold qEnd qMid
    norm_num

theorem addressDownCoeff_cases (j : Nat) :
    addressDownCoeff j = rEnd ∨ addressDownCoeff j = rMid := by
  by_cases h : j = 0 ∨ j = 63
  · left
    simp [addressDownCoeff, h]
  · right
    simp [addressDownCoeff, h]

theorem addressDownCoeff_centered (j : Nat) :
    addressDownCoeff j - addressQ j = rBar := by
  by_cases h : j = 0 ∨ j = 63
  · have hEnd := candidate_centered_flows.1
    simp [addressDownCoeff, addressQ, h]
    unfold rEnd rBar qEnd at hEnd ⊢
    linarith
  · have hMid := candidate_centered_flows.2.1
    simp [addressDownCoeff, addressQ, h]
    unfold rMid rBar qMid at hMid ⊢
    linarith

theorem addressQ_sum_zero :
    (∑ j : Fin 64, addressQ j.val) = 0 := by
  norm_num [addressQ, Fin.sum_univ_succ, qEnd, qMid]

theorem addressDownCoeff_sum :
    (∑ j : Fin 64, addressDownCoeff j.val) = 64 * rBar := by
  calc
    (∑ j : Fin 64, addressDownCoeff j.val) =
        ∑ j : Fin 64, (rBar + addressQ j.val) := by
          apply Finset.sum_congr rfl
          intro j hj
          have h := addressDownCoeff_centered j.val
          linarith
    _ = 64 * rBar + ∑ j : Fin 64, addressQ j.val := by
      rw [Finset.sum_add_distrib]
      simp
    _ = 64 * rBar := by rw [addressQ_sum_zero]; ring

def bagAddressDebt {d : Nat} (b : Chvatal.KBag 64 d) : Rat :=
  addressDebt b.l b.x

def addressDownAt {d : Nat} (b : Chvatal.KBag 64 d) (C : Rat) (j : Fin 64) : Rat :=
  addressDownCoeff j.val * C + bagAddressDebt b * C / 64

/-- The same block width indexed by a natural slot. This form is convenient
for cumulative sums, whose indices carry membership proofs rather than `Fin`.-/
def addressDownNatAt {d : Nat} (b : Chvatal.KBag 64 d) (C : Rat) (j : Nat) : Rat :=
  addressDownCoeff j * C + bagAddressDebt b * C / 64

def addressUpAt {d : Nat} (b : Chvatal.KBag 64 d) (C : Rat) : Rat :=
  upFlow * C - bagAddressDebt b * C

/-- The first `j` child addresses contain the left endpoint and otherwise
middle addresses, provided the right endpoint has not yet been included. -/
theorem addressDownCoeff_prefix_sum (j : Nat) (hj1 : 1 ≤ j) (hj63 : j ≤ 63) :
    (∑ i ∈ Finset.range j, addressDownCoeff i) =
      (j : Rat) / 64 - 1 / 2 ^ 17 := by
  induction j with
  | zero => omega
  | succ j ih =>
      have hjle : j + 1 ≤ 63 := by omega
      by_cases hj0 : j = 0
      · subst j
        norm_num [addressDownCoeff, rEnd]
      · have hj1' : 1 ≤ j := by omega
        have hj63' : j ≤ 63 := by omega
        have hcoeff : addressDownCoeff j = rMid := by
          simp [addressDownCoeff]
          omega
        rw [Finset.sum_range_succ, ih hj1' hj63', hcoeff]
        norm_num [rMid]
        push_cast
        ring

/-- Cumulative address-dependent down-flow in a prefix of child slots. -/
theorem addressDownAt_prefix_sum {d : Nat} (b : Chvatal.KBag 64 d)
    (C : Rat) (j : Nat) (hj1 : 1 ≤ j) (hj63 : j ≤ 63) :
    (∑ i ∈ Finset.range j,
      addressDownNatAt b C i) =
      (j : Rat) * C / 64 - C / 2 ^ 17 +
        (j : Rat) * bagAddressDebt b * C / 64 := by
  simp only [addressDownNatAt]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [addressDownCoeff_prefix_sum j hj1 hj63]
  simp only [Finset.sum_const, Finset.card_range, Nat.cast_ofNat, nsmul_eq_mul]
  push_cast
  ring_nf

/-- The last `64-j` child addresses contain the right endpoint and otherwise
middle addresses. Here `j` is the index immediately before that suffix. -/
theorem addressDownCoeff_suffix_sum (j : Nat) (hj : j ≤ 62) :
    (∑ i ∈ Finset.Ioc j 63, addressDownCoeff i) =
      (63 - j : Nat) / 64 - 1 / 2 ^ 17 := by
  have htotalRange :
      (∑ i ∈ Finset.range 64, addressDownCoeff i) = 64 * rBar := by
    rw [Finset.sum_range_succ]
    have hp := addressDownCoeff_prefix_sum 63 (by omega) (by omega)
    rw [hp]
    norm_num [addressDownCoeff, rEnd, rMid, rBar]
  have hj63 : j ≤ 63 := by omega
  have hprefix := addressDownCoeff_prefix_sum (j + 1) (by omega) (by omega)
  have hsplit : Finset.range 64 = Finset.range (j + 1) ∪ Finset.Ioc j 63 := by
    ext i
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.range (j + 1)) (Finset.Ioc j 63) := by
    refine Finset.disjoint_left.2 ?_
    intro i hi1 hi2
    simp only [Finset.mem_range] at hi1
    simp only [Finset.mem_Ioc] at hi2
    omega
  rw [hsplit, Finset.sum_union hdisj, hprefix] at htotalRange
  norm_num [rBar] at htotalRange ⊢
  push_cast [Nat.cast_sub hj63] at htotalRange ⊢
  linarith

/-- Cumulative address-dependent down-flow in the suffix strictly after slot
`j`; this is the right-hand counterpart of `addressDownAt_prefix_sum`. -/
theorem addressDownAt_suffix_sum {d : Nat} (b : Chvatal.KBag 64 d)
    (C : Rat) (j : Nat) (hj : j ≤ 62) :
    (∑ i ∈ Finset.Ioc j 63,
      addressDownNatAt b C i) =
      (63 - j : Nat) * C / 64 - C / 2 ^ 17 +
        (63 - j : Nat) * bagAddressDebt b * C / 64 := by
  simp only [addressDownNatAt]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [addressDownCoeff_suffix_sum j hj]
  have hcard : (Finset.Ioc j 63).card = 63 - j := by
    simp
  rw [Finset.sum_const, hcard]
  push_cast
  ring_nf

/-- Suffix form indexed by its first child address. The range `1 ≤ j ≤ 63`
includes the final endpoint singleton. -/
theorem addressDownAt_suffix_from_sum {d : Nat} (b : Chvatal.KBag 64 d)
    (C : Rat) (j : Nat) (hj1 : 1 ≤ j) (hj63 : j ≤ 63) :
    (∑ i ∈ Finset.Icc j 63,
      addressDownNatAt b C i) =
      (64 - j : Nat) * C / 64 - C / 2 ^ 17 +
        (64 - j : Nat) * bagAddressDebt b * C / 64 := by
  have h := addressDownAt_suffix_sum b C (j - 1) (by omega)
  have hset : Finset.Icc j 63 = Finset.Ioc (j - 1) 63 := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hset]
  have hlen : 63 - (j - 1) = 64 - j := by omega
  rw [hlen] at h
  exact h

/-- The real fringe after reserving the capacity defect has an exact half-width
formula. This is the amount `p + C/(2 cap)` in the tapered window estimates. -/
theorem address_bootstrap_up_half {d : Nat} (b : Chvatal.KBag 64 d)
    (C : Rat) :
    (addressUpAt b C + C / cap) / 2 =
      C / 2 ^ 17 - bagAddressDebt b * C / 2 := by
  rw [addressUpAt]
  unfold upFlow cap
  ring

/-- The explicitly reserved tail term used in the signed-window inequalities
is nonnegative for a nonnegative reference capacity. -/
theorem address_half_tail_nonneg (C : Rat) (hC : 0 ≤ C) :
    0 ≤ C / (2 * cap) := by
  apply div_nonneg hC
  norm_num [cap]

/-- The address-dependent prefix widths leave exactly the signed correction
required by the left cumulative rank-tail estimate. Integer rounding may be
added later as the nonnegative `j * rho` term. -/
theorem address_prefix_tail_width_budget {d : Nat}
    (b : Chvatal.KBag 64 d) (C : Rat) (j : Nat)
    (hj1 : 1 ≤ j) (hj62 : j ≤ 62) (hC : 0 ≤ C) :
    (j : Rat) * C / 64 ≤
      (∑ i ∈ Finset.range j,
        addressDownNatAt b C i) +
        (addressUpAt b C + C / cap) / 2 + C / (2 * cap) +
        (32 - j : Rat) * bagAddressDebt b * C / 64 := by
  have hp := addressDownAt_prefix_sum b C j hj1 (by omega)
  have hu := address_bootstrap_up_half b C
  rw [hp, hu]
  have hEq :
      (j : Rat) * C / 64 - C / 2 ^ 17 +
        (j : Rat) * bagAddressDebt b * C / 64 +
        (C / 2 ^ 17 - bagAddressDebt b * C / 2) +
        C / (2 * cap) + (32 - j : Rat) * bagAddressDebt b * C / 64 =
        (j : Rat) * C / 64 + C / (2 * cap) := by ring
  rw [hEq]
  exact le_add_of_nonneg_right (address_half_tail_nonneg C hC)

/-- The symmetric cumulative-width budget for the suffix following slot `j`.
-/
theorem address_suffix_tail_width_budget {d : Nat}
    (b : Chvatal.KBag 64 d) (C : Rat) (j : Nat)
    (hj1 : 1 ≤ j) (hj62 : j ≤ 62) (hC : 0 ≤ C) :
    (63 - j : Nat) * C / 64 ≤
      (∑ i ∈ Finset.Ioc j 63,
        addressDownNatAt b C i) +
        (addressUpAt b C + C / cap) / 2 + C / (2 * cap) +
        (j - 31 : Rat) * bagAddressDebt b * C / 64 := by
  have hp := addressDownAt_suffix_sum b C j (by omega)
  have hu := address_bootstrap_up_half b C
  rw [hp, hu]
  have hEq :
      (63 - j : Nat) * C / 64 - C / 2 ^ 17 +
        (63 - j : Nat) * bagAddressDebt b * C / 64 +
        (C / 2 ^ 17 - bagAddressDebt b * C / 2) +
        C / (2 * cap) + (j - 31 : Rat) * bagAddressDebt b * C / 64 =
        (63 - j : Nat) * C / 64 + C / (2 * cap) := by
    have hjcast : (j : Rat) ≤ 62 := by exact_mod_cast hj62
    have hjcast' : (1 : Rat) ≤ j := by exact_mod_cast hj1
    have hlen : ((63 - j : Nat) : Rat) = (63 : Rat) - j := by
      exact_mod_cast Nat.cast_sub (by omega : j ≤ 63)
    simp only [hlen]
    push_cast
    ring_nf
  rw [hEq]
  exact le_add_of_nonneg_right (address_half_tail_nonneg C hC)

theorem candidate_base_flow_split :
    upFlow + 64 * rBar = 1 - 1 / cap := by
  unfold upFlow rBar cap
  norm_num

/-- Integerize the exceptional stage-one bootstrap split. Its extra C/cap
up-flow exactly compensates for the capacity defect in the ordinary signed
flow, so a parent of size C is conserved with zero occupancy error. -/
theorem address_bootstrap_integer_split (C debt : Rat) (parent : Nat)
    (hC : 2 ^ 34 ≤ C)
    (hdebtLo : -eAbs * C ≤ debt) (hdebtHi : debt ≤ ePos * C)
    (hparent : (parent : Rat) = C) :
    ∃ up : Nat, ∃ blocks : Fin 64 → Nat,
      Even up ∧ up ≤ parent ∧
        |(up : Rat) - (upFlow * C - debt + C / cap)| ≤ 1 ∧
        (∑ j, blocks j) = parent - up ∧
        ∀ j, |(blocks j : Rat) -
          (addressDownCoeff j.val * C + debt / 64)| ≤ 1 + 70 / 64 := by
  let coeff : Fin 64 → Rat := fun j => addressDownCoeff j.val
  let idealUp : Rat := upFlow * C - debt + C / cap
  have hC0 : 0 ≤ C := by positivity
  have hcoeff : ∀ j, coeff j = rEnd ∨ coeff j = rMid := by
    intro j
    exact addressDownCoeff_cases j.val
  have hsumCoeffLower : (64 : Rat) * rEnd * C ≤
      ∑ j : Fin 64, coeff j * C := by
    have hpoint : ∀ j : Fin 64, rEnd * C ≤ coeff j * C := by
      intro j
      rcases hcoeff j with he | hm
      · rw [he]
      · rw [hm]
        exact mul_le_mul_of_nonneg_right
          (by norm_num [rEnd, rMid]) hC0
    calc
      (64 : Rat) * rEnd * C = ∑ _j : Fin 64, rEnd * C := by simp; ring
      _ ≤ ∑ j : Fin 64, coeff j * C := Finset.sum_le_sum fun j _ => hpoint j
  have hsumDebt : (∑ _j : Fin 64, debt / 64) = debt := by
    simp
    ring
  have hsum :
      (∑ j : Fin 64, (coeff j * C + debt / 64)) =
        (64 : Rat) * rBar * C + debt := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, addressDownCoeff_sum]
    simp [coeff, hsumDebt]
  have hdownLower :
      (64 : Rat) * rEnd * C + debt ≤
        ∑ j : Fin 64, (coeff j * C + debt / 64) := by
    rw [hsum]
    have hbar : (64 : Rat) * rEnd ≤ 64 * rBar := by
      unfold rEnd rBar
      norm_num
    nlinarith [mul_le_mul_of_nonneg_right hbar hC0]
  have hdownLarge : 1 ≤
      ∑ j : Fin 64, (coeff j * C + debt / 64) := by
    have hlow : ((64 : Rat) * rEnd - eAbs) * C ≤
        (64 : Rat) * rEnd * C + debt := by
      have hdebtLo' := hdebtLo
      unfold eAbs at hdebtLo'
      unfold eAbs
      nlinarith [hdebtLo']
    have hfactor : (1 : Rat) / 2 ≤ (64 : Rat) * rEnd - eAbs := by
      unfold rEnd eAbs
      norm_num
    have hbig : (1 : Rat) ≤ C / 2 := by
      have h2 : (2 : Rat) ≤ C := by
        have hNat : (2 : Rat) ≤ (2 ^ 34 : Rat) := by norm_num
        exact le_trans hNat (by exact_mod_cast hC)
      linarith
    calc
      (1 : Rat) ≤ C / 2 := hbig
      _ ≤ ((64 : Rat) * rEnd - eAbs) * C := by
        nlinarith [mul_le_mul_of_nonneg_right hfactor hC0]
      _ ≤ (64 : Rat) * rEnd * C + debt := hlow
      _ ≤ ∑ j : Fin 64, (coeff j * C + debt / 64) := hdownLower
  have hidealNonneg : 0 ≤ idealUp := by
    dsimp [idealUp]
    have hcoef : ePos ≤ upFlow + 1 / cap := by
      unfold ePos upFlow cap
      norm_num
    have hscaled := mul_le_mul_of_nonneg_right hcoef hC0
    have hflow : (upFlow + 1 / cap) * C = upFlow * C + C / cap := by ring
    nlinarith [hdebtHi, hscaled, hflow]
  have hparentFlow : (parent : Rat) = idealUp +
      (∑ j : Fin 64, (coeff j * C + debt / 64)) := by
    rw [hparent, hsum]
    dsimp [idealUp]
    have hbase := candidate_base_flow_split
    unfold cap at hbase ⊢
    nlinarith [hbase]
  have hroom : idealUp + 1 ≤ (parent : Rat) := by
    rw [hparentFlow]
    linarith [hdownLarge]
  obtain ⟨up, blocks, hupEven, hupLe, hupNear, hblocks, hblockError⟩ :=
    candidate_bootstrap_integer_flow_split C debt idealUp coeff parent
      hC hdebtLo hdebtHi hcoeff hidealNonneg hparentFlow hroom
  refine ⟨up, blocks, hupEven, hupLe, ?_, hblocks, ?_⟩
  · simpa [idealUp] using hupNear
  · intro j
    exact hblockError j

/-- Every finite address has the signed-debt bounds from the scalar recurrence. -/
theorem addressDebt_bounds (l x : Nat) (hx : x < 64 ^ l) :
    -eAbs ≤ addressDebt l x ∧ addressDebt l x ≤ ePos := by
  induction l generalizing x with
  | zero =>
    norm_num [addressDebt, eAbs, ePos]
  | succ l ih =>
    have hparent : x / 64 < 64 ^ l := by
      apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 64)).2
      simpa [pow_succ, Nat.mul_comm] using hx
    have hprev := ih (x / 64) hparent
    have hq := addressQ_bounds (x % 64)
    simpa [addressDebt] using
      debtStep_preserves_bounds (addressQ (x % 64)) (addressDebt l (x / 64))
        hq.1 hq.2 hprev.1 hprev.2

/-- The debt recurrence follows the parent-child address decomposition. -/
theorem addressDebt_child (l x j : Nat) (hj : j < 64) :
    addressDebt (l + 1) (64 * x + j) =
      debtStep (addressQ j) (addressDebt l x) := by
  have hmod : (64 * x + j) % 64 = j := by omega
  have hdiv : (64 * x + j) / 64 = x := by omega
  simp [addressDebt, hmod, hdiv]

theorem bagAddressDebt_bounds {d : Nat} (b : Chvatal.KBag 64 d) :
    -eAbs ≤ bagAddressDebt b ∧ bagAddressDebt b ≤ ePos :=
  addressDebt_bounds b.l b.x b.hx

theorem bagAddressDebt_child {d : Nat} (b : Chvatal.KBag 64 d)
    (j : Nat) (hj : j < 64) (h : b.l < d) :
    bagAddressDebt (b.child j hj h) =
      debtStep (addressQ j) (bagAddressDebt b) := by
  simp [bagAddressDebt, Chvatal.KBag.child, addressDebt_child, hj]

/-- Absolute debt at a child, in the parent's reference-capacity units. -/
theorem bagAddressDebt_child_scaled {d : Nat} (b : Chvatal.KBag 64 d)
    (j : Fin 64) (h : b.l < d) (C : Rat) :
    bagAddressDebt (b.child j.val j.isLt h) * (64 * C) =
      addressQ j.val * C + bagAddressDebt b * C / 64 := by
  rw [bagAddressDebt_child b j.val j.isLt h]
  simp [debtStep]
  ring

/-- Absolute debt at a grandchild, expressed as the correction entering the
corresponding child block in the two-level occupancy identity. -/
theorem bagAddressDebt_grandchild_scaled {d : Nat}
    (b : Chvatal.KBag 64 d) (j l : Fin 64) (hb : b.l < d)
    (hc : (b.child j.val j.isLt hb).l < d) (C : Rat) :
    bagAddressDebt
        ((b.child j.val j.isLt hb).child l.val l.isLt hc) *
        (64 ^ 2 * C) =
      addressQ l.val * (64 * C) +
        (addressQ j.val * C + bagAddressDebt b * C / 64) / 64 := by
  let child := b.child j.val j.isLt hb
  have hchild := bagAddressDebt_child b j.val j.isLt hb
  have hgrand := bagAddressDebt_child child l.val l.isLt hc
  rw [hgrand]
  rw [hchild]
  simp [debtStep]
  ring

theorem address_parent_split_mass {d : Nat} (b : Chvatal.KBag 64 d)
    (C : Rat) :
    addressUpAt b C + ∑ j : Fin 64, addressDownAt b C j =
      (1 - 1 / cap) * C := by
  simp only [addressUpAt, addressDownAt]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [addressDownCoeff_sum]
  let debt := bagAddressDebt b * C
  have hsumDebt : (∑ _j : Fin 64, debt / 64) = 64 * (debt / 64) := by simp
  rw [hsumDebt]
  have hdebt : 64 * (debt / 64) = debt := by ring
  rw [hdebt]
  calc
    upFlow * C - debt + (64 * rBar * C + debt) =
        (upFlow + 64 * rBar) * C := by ring
    _ = (1 - 1 / cap) * C := by rw [candidate_base_flow_split]

/-- The real-valued two-level occupancy arriving at any child address is
independent of whether that child is an endpoint or a middle address. -/
theorem address_child_occupancy_uniform {d : Nat}
    (b : Chvatal.KBag 64 d) (j : Fin 64) (hb : b.l < d)
    (hc : (b.child j.val j.isLt hb).l < d) (C : Rat) :
    addressDownAt b C j +
      ∑ l : Fin 64,
        addressUpAt
          ((b.child j.val j.isLt hb).child l.val l.isLt hc)
          (64 ^ 2 * C) =
      (rBar + 64 * upFlow * 64 ^ 2) * C := by
  let q : Fin 64 → Rat := fun l => addressQ l.val
  let debt := bagAddressDebt b * C
  let child := b.child j.val j.isLt hb
  have hq : ∑ l : Fin 64, q l = 0 := by
    simpa [q] using addressQ_sum_zero
  have hr : addressDownCoeff j.val - q j = rBar := by
    simpa [q] using addressDownCoeff_centered j.val
  have hid := signed_occupancy_identity q C 64 rBar upFlow
    (addressDownCoeff j.val) (q j) debt hq hr
  have hterms :
      (∑ l : Fin 64,
        addressUpAt
          (child.child l.val l.isLt hc)
          (64 ^ 2 * C)) =
      ∑ l : Fin 64,
        (upFlow * 64 ^ 2 * C -
          (q l * (64 * C) + (q j * C + debt / 64) / 64)) := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [addressUpAt, bagAddressDebt_grandchild_scaled b j l hb hc C]
    simp [q, debt]
    ring
  rw [addressDownAt, hterms]
  simpa [q, debt, Finset.sum_sub_distrib] using hid

/-- The local integer flow split applies directly to a tree address: the
normalized address debt supplies the signed bounds, and the edge digit selects
an end or middle down-flow coefficient. -/
theorem candidate_bag_integer_flow_split {d : Nat} (b : Chvatal.KBag 64 d)
    (C idealUp eta : Rat) (parent : Nat)
    (hC : 2 ^ 34 ≤ C)
    (heta : |eta| ≤ 69)
    (hidealUp : idealUp = upFlow * C - bagAddressDebt b * C)
    (hparent : (parent : Rat) = idealUp +
      (∑ j : Fin 64, (addressDownCoeff j.val * C + bagAddressDebt b * C / 64)) + eta) :
    ∃ up : Nat, ∃ blocks : Fin 64 → Nat,
      Even up ∧ up ≤ parent ∧ |(up : Rat) - idealUp| ≤ 1 ∧
        (∑ j, blocks j) = parent - up ∧
        ∀ j, |(blocks j : Rat) -
          (addressDownCoeff j.val * C + bagAddressDebt b * C / 64)| ≤ 1 + 70 / 64 := by
  have hC0 : 0 ≤ C := by positivity
  have hdebt := bagAddressDebt_bounds b
  have hdebtLo : -eAbs * C ≤ bagAddressDebt b * C :=
    mul_le_mul_of_nonneg_right hdebt.1 hC0
  have hdebtHi : bagAddressDebt b * C ≤ ePos * C :=
    mul_le_mul_of_nonneg_right hdebt.2 hC0
  exact candidate_integer_flow_split C (bagAddressDebt b * C) idealUp eta
    (fun j : Fin 64 => addressDownCoeff j.val) parent hC hdebtLo hdebtHi
      (fun j => addressDownCoeff_cases j.val) heta hidealUp hparent

/-- Apply the conditional integer split directly to a bag whose wire count is
within 69 of the signed schedule's uniform real occupancy. -/
theorem candidate_round_bag_of_occupancy {d : Nat}
    (b : Chvatal.KBag 64 d) (C eta : Rat) (parent : Nat)
    (hC : 2 ^ 34 ≤ C) (heta : |eta| ≤ 69)
    (hparent : (parent : Rat) = (1 - 1 / cap) * C + eta) :
    ∃ up : Nat, ∃ blocks : Fin 64 → Nat,
      Even up ∧ up ≤ parent ∧
        |(up : Rat) - addressUpAt b C| ≤ 1 ∧
        (∑ j, blocks j) = parent - up ∧
        ∀ j, |(blocks j : Rat) - addressDownAt b C j| ≤ 1 + 70 / 64 := by
  have hsplit := address_parent_split_mass b C
  have hparent' : (parent : Rat) =
      addressUpAt b C + ∑ j : Fin 64, addressDownAt b C j + eta := by
    rw [hsplit]
    exact hparent
  have hout := candidate_bag_integer_flow_split b C (addressUpAt b C) eta parent
    hC heta rfl (by simpa [addressUpAt, addressDownAt] using hparent')
  simpa [addressUpAt, addressDownAt] using hout

/-- One ordinary address-dependent routing step preserves the 69-wire
occupancy error, provided the actual child bag is exactly the parent block
plus the 64 up-flows from its children. -/
theorem candidate_occupancy_transition {d : Nat}
    (b : Chvatal.KBag 64 d) (j : Fin 64) (hb : b.l < d)
    (hc : (b.child j.val j.isLt hb).l < d)
    (C Cnext : Rat) (childCount block : Nat) (childUps : Fin 64 → Nat)
    (hCnext : Cnext = 4 * C)
    (hblock : |(block : Rat) - addressDownAt b C j| ≤ 1 + 70 / 64)
    (hups : ∀ l, |(childUps l : Rat) -
      addressUpAt ((b.child j.val j.isLt hb).child l.val l.isLt hc)
        (64 ^ 2 * C)| ≤ 1)
    (hactual : (childCount : Rat) = (block : Rat) + ∑ l, (childUps l : Rat)) :
    |(childCount : Rat) - (1 - 1 / cap) * Cnext| ≤ 69 := by
  have hmass := candidate_flow_mass_identity
  have hcoef : rBar + 64 * upFlow * 64 ^ 2 = 4 * (1 - 1 / cap) := by
    rw [hmass]
    ring
  have hreal := address_child_occupancy_uniform b j hb hc C
  have htarget : (1 - 1 / cap) * Cnext =
      addressDownAt b C j +
        ∑ l : Fin 64,
          addressUpAt ((b.child j.val j.isLt hb).child l.val l.isLt hc)
            (64 ^ 2 * C) := by
    calc
      (1 - 1 / cap) * Cnext = 4 * (1 - 1 / cap) * C := by rw [hCnext]; ring
      _ = (rBar + 64 * upFlow * 64 ^ 2) * C := by rw [← hcoef]
      _ = addressDownAt b C j +
          ∑ l : Fin 64,
            addressUpAt ((b.child j.val j.isLt hb).child l.val l.isLt hc)
              (64 ^ 2 * C) := hreal.symm
  exact candidate_next_bag_discrepancy childCount block (addressDownAt b C j)
    (fun l => childUps l) (fun l =>
      addressUpAt ((b.child j.val j.isLt hb).child l.val l.isLt hc)
        (64 ^ 2 * C)) ((1 - 1 / cap) * Cnext) hblock hups htarget hactual

end Tapered945
