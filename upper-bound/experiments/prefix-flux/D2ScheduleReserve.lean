import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.constructorNameAsVariable false

/-! Paper-level schedule arithmetic for the `(k,A,nu)=(8,8,1/4)` D2 route.

This file deliberately stays outside the accepted packages. It formalizes the
closed-form schedule consequences, abstract local conservation equations, and
a callback-instantiated finite-tree D2 transition used by the endpoint-reserve
induction. The reachable-state invariant proof, provider, and sorting-network
connection remain open.
-/

namespace Chvatal.D2Reserve

/-- Round a lower bound up to the parity class of the stage. -/
def ceilParity (m t : Nat) : Nat := if m % 2 = t % 2 then m else m + 1

/-- Nonnegative ceiling of the lower frontier `(2*t - 3*d + 11)/3`. -/
def alphaStar (d t : Nat) : Nat :=
  if 2 * t + 11 ≤ 3 * d then 0 else (2 * t + 11 - 3 * d + 2) / 3

theorem alphaStar_gap_before_tf {d t : Nat} (hd : 7 ≤ d) (ht : 2 ≤ t)
    (htf : t < 3 * d - 14) : alphaStar d t + 2 ≤ (t + 4) / 3 := by
  unfold alphaStar
  by_cases hzero : 2 * t + 11 ≤ 3 * d
  · simp [hzero]
    have ht4 : 6 ≤ t + 4 := by omega
    omega
  · simp only [if_neg hzero]
    have hnum : 2 * t + 11 - 3 * d + 2 + 6 ≤ t + 4 := by omega
    have hshift : (2 * t + 11 - 3 * d + 2 + 6) / 3 =
        (2 * t + 11 - 3 * d + 2) / 3 + 2 := by omega
    rw [← hshift]
    exact Nat.div_le_div_right hnum

/-- The `(3,3,2)` top frontier from its exact ceil/parity formula. -/
def alpha (d t : Nat) : Nat :=
  if t = 0 then 0 else if t = 1 then 1 else ceilParity (alphaStar d t) t

theorem ceilParity_le_iff {m i t : Nat} (hpar : i % 2 = t % 2) :
    ceilParity m t ≤ i ↔ m ≤ i := by
  unfold ceilParity
  by_cases h : m % 2 = t % 2
  · simp [h]
  · have hmne : m % 2 ≠ i % 2 := by rw [hpar]; exact h
    simp [h]
    omega

theorem ceilParity_gap_two {m n t : Nat} (hmn : m + 2 ≤ n) :
    ceilParity m t + 2 ≤ ceilParity n t := by
  unfold ceilParity
  by_cases hm : m % 2 = t % 2 <;>
    by_cases hn : n % 2 = t % 2 <;> simp [hm, hn] <;> omega

/-- With matching parity, the rounded lower frontier is below `i` exactly
when the unrounded integer threshold is met. -/
theorem alpha_le_iff_threshold {d i t : Nat} (ht : 2 ≤ t)
    (hpar : i % 2 = t % 2) :
    alpha d t ≤ i ↔ 2 * t + 11 ≤ 3 * d + 3 * i := by
  have ht0 : t ≠ 0 := by omega
  have ht1 : t ≠ 1 := by omega
  rw [show alpha d t = ceilParity (alphaStar d t) t by simp [alpha, ht0, ht1]]
  rw [ceilParity_le_iff hpar]
  by_cases hzero : 2 * t + 11 ≤ 3 * d
  · simp [alphaStar, hzero]
    omega
  · simp only [alphaStar, if_neg hzero]
    omega

/-- Equality in the lower activity threshold is exactly a top-descending
sender: the lower frontier occupies `i` now and rises to `i+1` next stage. -/
theorem lower_boundary_is_topDesc {d i t : Nat} (ht : 2 ≤ t)
    (hpar : i % 2 = t % 2) (heq : 3 * i + 3 * d = 2 * t + 11) :
    alpha d t = i ∧ alpha d (t + 1) = i + 1 := by
  have ht0 : t ≠ 0 := by omega
  have ht1 : t ≠ 1 := by omega
  have ht10 : t + 1 ≠ 0 := by omega
  have ht11 : t + 1 ≠ 1 := by omega
  have hstar : alphaStar d t = i := by
    unfold alphaStar
    split_ifs <;> omega
  have hstarNext : alphaStar d (t + 1) = i + 1 := by
    unfold alphaStar
    split_ifs <;> omega
  constructor
  · simp [alpha, ht0, ht1, hstar, ceilParity, hpar]
  · have hparNext : (i + 1) % 2 = (t + 1) % 2 := by omega
    unfold alpha
    simp only [if_neg ht10, if_neg ht11]
    rw [hstarNext]
    simp [ceilParity, hparNext]

/-- The unrounded top-frontier lower bound is nondecreasing in time. -/
theorem alphaStar_mono {d s t : Nat} (hst : s ≤ t) :
    alphaStar d s ≤ alphaStar d t := by
  unfold alphaStar
  by_cases hs : 2 * s + 11 ≤ 3 * d <;>
    by_cases ht : 2 * t + 11 ≤ 3 * d
  · simp [hs, ht]
  · simp [hs, ht]
  · omega
  · simp [hs, ht]
    apply Nat.div_le_div_right
    omega

/-- The unrounded top frontier advances by at most one per stage. -/
theorem alphaStar_succ_le {d t : Nat} :
    alphaStar d (t + 1) ≤ alphaStar d t + 1 := by
  unfold alphaStar
  by_cases h : 2 * t + 11 ≤ 3 * d
  · by_cases hn : 2 * (t + 1) + 11 ≤ 3 * d
    · simp [h, hn]
    · simp only [if_pos h, if_neg hn]
      omega
  · by_cases hn : 2 * (t + 1) + 11 ≤ 3 * d
    · simp only [if_neg h, if_pos hn]
      omega
    · simp only [if_neg h, if_neg hn]
      omega

/-- Across three stages the unrounded top frontier advances by at most two. -/
theorem alphaStar_three_le {d t : Nat} :
    alphaStar d (t + 3) ≤ alphaStar d t + 2 := by
  unfold alphaStar
  by_cases h : 2 * t + 11 ≤ 3 * d
  · by_cases hn : 2 * (t + 3) + 11 ≤ 3 * d
    · simp [h, hn]
    · simp only [if_pos h, if_neg hn]
      omega
  · have hn : ¬ 2 * (t + 3) + 11 ≤ 3 * d := by omega
    simp only [if_neg h, if_neg hn]
    omega

/-- Parity rounding moves an integer by at most one. -/
theorem ceilParity_bounds (m t : Nat) :
    m ≤ ceilParity m t ∧ ceilParity m t ≤ m + 1 := by
  unfold ceilParity
  split_ifs <;> omega

/-- The rounded top frontier has the stage's parity. -/
theorem alpha_parity (d t : Nat) : alpha d t % 2 = t % 2 := by
  by_cases ht0 : t = 0
  · simp [alpha, ht0]
  · by_cases ht1 : t = 1
    · simp [alpha, ht0, ht1]
    · simp only [alpha, if_neg ht0, if_neg ht1]
      unfold ceilParity
      split_ifs <;> omega

/-- Over three stages the rounded top frontier moves by exactly one of the
three odd displacements -1, +1, or +3. -/
theorem alpha_three_displacement {d t : Nat} (ht : 2 ≤ t) :
    alpha d (t + 3) + 1 = alpha d t ∨
      alpha d (t + 3) = alpha d t + 1 ∨
      alpha d (t + 3) = alpha d t + 3 := by
  have hstarMono := alphaStar_mono (d := d) (by omega : t ≤ t + 3)
  have hstarStep := alphaStar_three_le (d := d) (t := t)
  have ht0 : t ≠ 0 := by omega
  have ht1 : t ≠ 1 := by omega
  have hn0 : t + 3 ≠ 0 := by omega
  have hn1 : t + 3 ≠ 1 := by omega
  have hnowEq : alpha d t = ceilParity (alphaStar d t) t := by
    simp [alpha, ht0, ht1]
  have hnextEq : alpha d (t + 3) =
      ceilParity (alphaStar d (t + 3)) (t + 3) := by
    simp [alpha, hn0, hn1]
  have hnow := ceilParity_bounds (alphaStar d t) t
  have hnext := ceilParity_bounds (alphaStar d (t + 3)) (t + 3)
  rw [hnowEq, hnextEq]
  rcases hnow with ⟨hnowLo, hnowHi⟩
  rcases hnext with ⟨hnextLo, hnextHi⟩
  have hparNow := alpha_parity d t
  have hparNext := alpha_parity d (t + 3)
  omega

/-- Parity rounding changes a nondecreasing pair of integers at distance at
most one by at most one extra level. -/
theorem ceilParity_step_le {m n s t : Nat} (hmn : m ≤ n)
    (hnm : n ≤ m + 1) :
    ceilParity m s ≤ ceilParity n t + 1 := by
  unfold ceilParity
  split_ifs <;> omega

/-- The rounded top frontier at the previous stage is at most one level above
its current value. -/
theorem alpha_prev_le_succ {d t : Nat} (ht : 3 ≤ t) :
    alpha d (t - 1) ≤ alpha d t + 1 := by
  have hmon := alphaStar_mono (d := d) (by omega : t - 1 ≤ t)
  have hstep : alphaStar d t ≤ alphaStar d (t - 1) + 1 := by
    have h := alphaStar_succ_le (d := d) (t := t - 1)
    rw [show t - 1 + 1 = t by omega] at h
    exact h
  have hprev0 : t - 1 ≠ 0 := by omega
  have hprev1 : t - 1 ≠ 1 := by omega
  have hnow0 : t ≠ 0 := by omega
  have hnow1 : t ≠ 1 := by omega
  rw [show alpha d (t - 1) = ceilParity (alphaStar d (t - 1)) (t - 1) by
        simp [alpha, hprev0, hprev1],
      show alpha d t = ceilParity (alphaStar d t) t by
        simp [alpha, hnow0, hnow1]]
  exact ceilParity_step_le hmon hstep

/-- Parity rounding preserves monotonicity when both times have the same parity. -/
theorem ceilParity_mono_same_parity {m n s t : Nat}
    (hmn : m ≤ n) (hst : s % 2 = t % 2) :
    ceilParity m s ≤ ceilParity n t := by
  unfold ceilParity
  by_cases hm : m % 2 = s % 2 <;>
    by_cases hn : n % 2 = t % 2 <;> simp [hm, hn] <;> omega

/-- The parity-rounded top frontier is monotone along either parity subsequence. -/
theorem alpha_mono_same_parity {d s t : Nat} (hs : 2 ≤ s) (hstime : s ≤ t)
    (hpar : s % 2 = t % 2) : alpha d s ≤ alpha d t := by
  have ht : 2 ≤ t := by omega
  have hs0 : s ≠ 0 := by omega
  have hs1 : s ≠ 1 := by omega
  have ht0 : t ≠ 0 := by omega
  have ht1 : t ≠ 1 := by omega
  simp [alpha, hs0, hs1, ht0, ht1]
  exact ceilParity_mono_same_parity (alphaStar_mono hstime) hpar

/-- A top-descending sender at `t-2` forces the same level to be top-descending
at `t`; this is the role exclusion used by the reserve induction. -/
theorem topDesc_two_back_forces_current {d i t : Nat} (ht : 4 ≤ t)
    (hprev : i = alpha d (t - 2))
    (hprevRise : alpha d (t - 2) < alpha d (t - 1))
    (hactive : alpha d t ≤ i) :
    i = alpha d t ∧ alpha d t < alpha d (t + 1) := by
  have hmono0 := alpha_mono_same_parity (d := d) (by omega : 2 ≤ t - 2)
    (by omega : t - 2 ≤ t) (by omega)
  have hmono1 := alpha_mono_same_parity (d := d) (by omega : 2 ≤ t - 1)
    (by omega : t - 1 ≤ t + 1) (by omega)
  constructor <;> omega

/-- Thus a sender that is not top-descending now cannot have been
top-descending two stages earlier. -/
theorem topDesc_predecessor_excluded {d i t : Nat} (ht : 4 ≤ t)
    (hprev : i = alpha d (t - 2))
    (hprevRise : alpha d (t - 2) < alpha d (t - 1))
    (hactive : alpha d t ≤ i)
    (hnotCurrent : i ≠ alpha d t ∨ alpha d (t + 1) ≤ i) : False := by
  obtain ⟨heq, hrise⟩ := topDesc_two_back_forces_current ht hprev hprevRise hactive
  rcases hnotCurrent with hne | hle
  · exact hne heq
  · omega

/-- A `c/128` endpoint reserve contains either D2 cut front whenever the
parent deficit and up-port satisfy the proposed invariant bounds. -/
theorem endpoint_cut_fits {c G low high pi Uleft Uright : Rat}
    (hc : 0 < c)
    (hG : G ≤ c / 512)
    (hlow : low ≤ G) (hhigh : high ≤ G)
    (hpi : pi ≤ c / 256)
    (hleft : c / 128 ≤ Uleft) (hright : c / 128 ≤ Uright) :
    low + pi / 2 ≤ Uleft ∧ high + pi / 2 ≤ Uright := by
  constructor <;> linarith

/-- Integer form of the endpoint-reserve implication used by the actual
cut routine: `G<=c/512`, `pi<=c/256`, and `c/128` native reserves make each
ordinary front fit in its own end child. -/
theorem d2_endpoint_fronts_fit_of_reserve
    {c G low high pi half Uleft Uright : Nat}
    (hG : 512 * G ≤ c) (hlow : low ≤ G) (hhigh : high ≤ G)
    (hpi : 256 * pi ≤ c) (heven : pi = 2 * half)
    (hleft : c ≤ 128 * Uleft) (hright : c ≤ 128 * Uright) :
    low + half ≤ Uleft ∧ high + half ≤ Uright := by
  constructor <;> omega

/-- The relaxed `23/4096` deficit budget still keeps both ordinary fronts
inside endpoint children carrying the same `c/128` reserve. -/
theorem d2_endpoint_fronts_fit_of_tolerant_reserve
    {c G low high pi half Uleft Uright : Nat}
    (hG : 4096 * G ≤ 23 * c) (hlow : low ≤ G) (hhigh : high ≤ G)
    (hpi : 256 * pi ≤ c) (heven : pi = 2 * half)
    (hleft : c ≤ 128 * Uleft) (hright : c ≤ 128 * Uright) :
    low + half ≤ Uleft ∧ high + half ≤ Uright := by
  have hhalf : 4096 * half ≤ 8 * c := by omega
  have hfrontLeft : 4096 * (low + half) ≤ 31 * c := by omega
  have hfrontRight : 4096 * (high + half) ≤ 31 * c := by omega
  have hreserveLeft : 31 * c ≤ 3968 * Uleft := by omega
  have hreserveRight : 31 * c ≤ 3968 * Uright := by omega
  constructor <;> omega

/-- An ordinary contained cut leaves at least half its up-port in each end
child; after the two-stage capacity change this exceeds the current `c/128`
reserve target. -/
theorem ordinary_predecessor_reserve {c cOld piOld uOld uNow : Rat}
    (hc : 0 < c) (hcap : cOld = 16 * c)
    (hquota : 15 * cOld / 4096 ≤ piOld)
    (hcut : piOld / 2 ≤ uOld) (hgrow : uOld ≤ uNow) :
    c / 128 ≤ uNow := by
  linarith

/-- The D2 stage rule changes a node deficit only by adding its nonnegative
up-port; inactive nodes keep their deficit. -/
inductive D2Role
  | topDesc | topRise | mid | botDesc | botRise
  deriving DecidableEq

def d2NodeDeficitAfterStage (isActive : Bool) (G pi : Rat) : Rat :=
  if isActive then G + pi else G

theorem d2NodeDeficitAfterStage_mono (isActive : Bool) {G pi : Rat}
    (hpi : 0 ≤ pi) : G ≤ d2NodeDeficitAfterStage isActive G pi := by
  cases isActive with
  | false => simp [d2NodeDeficitAfterStage]
  | true => simp [d2NodeDeficitAfterStage]; linarith

/-- Deficit history for a single node under a prescribed activity and port
sequence. State `t` is the deficit after stages `0,...,t-1`. -/
def d2NodeDeficitTrace (initial : Rat) (isActive : Nat → Bool)
    (port : Nat → Rat) : Nat → Rat
  | 0 => initial
  | t + 1 => d2NodeDeficitAfterStage (isActive t)
      (d2NodeDeficitTrace initial isActive port t) (port t)

/-- A node's deficit is unchanged across any interval on which it is
inactive. -/
theorem d2NodeDeficitTrace_eq_of_inactive (initial : Rat)
    (isActive : Nat → Bool) (port : Nat → Rat) (s n : Nat)
    (hinactive : ∀ k, k < n → isActive (s + k) = false) :
    d2NodeDeficitTrace initial isActive port (s + n) =
      d2NodeDeficitTrace initial isActive port s := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show s + (n + 1) = (s + n) + 1 by omega,
        d2NodeDeficitTrace]
      rw [ih (by
        intro k hk
        have h := hinactive k (by omega)
        simpa [Nat.add_assoc] using h)]
      simp [d2NodeDeficitAfterStage, hinactive n (by omega)]

/-- A parent cut can overwrite a child deficit even when that child is
inactive. The child is preserved exactly when the parent is inactive or has
the exceptional `botRise` role, whose rule leaves all children untouched. -/
def d2ChildDeficitAfterStage (childActive parentActive : Bool)
    (parentRole : D2Role) (oldDeficit childPort cutDeficit : Rat) : Rat :=
  let selfUpdated := d2NodeDeficitAfterStage childActive oldDeficit childPort
  if parentActive then
    if parentRole = .botRise then selfUpdated else cutDeficit
  else selfUpdated

/-- Child deficit history includes both its own active up-port and the
overwriting parent's cut. -/
def d2ChildDeficitTrace (initial : Rat) (childActive : Nat → Bool)
    (childPort : Nat → Rat) (parentActive : Nat → Bool)
    (parentRole : Nat → D2Role) (cutDeficit : Nat → Rat) : Nat → Rat
  | 0 => initial
  | t + 1 => d2ChildDeficitAfterStage (childActive t) (parentActive t)
      (parentRole t)
      (d2ChildDeficitTrace initial childActive childPort parentActive
        parentRole cutDeficit t) (childPort t) (cutDeficit t)

/-- A child keeps its deficit when it is inactive and its parent is inactive
or uses `botRise`. -/
theorem d2ChildDeficitTrace_eq_of_preserves (initial : Rat)
    (childActive : Nat → Bool) (childPort : Nat → Rat)
    (parentActive : Nat → Bool) (parentRole : Nat → D2Role)
    (cutDeficit : Nat → Rat) (s n : Nat)
    (hpreserves : ∀ k, k < n →
      childActive (s + k) = false ∧
        (parentActive (s + k) = false ∨ parentRole (s + k) = .botRise)) :
    d2ChildDeficitTrace initial childActive childPort parentActive
      parentRole cutDeficit (s + n) =
      d2ChildDeficitTrace initial childActive childPort parentActive
        parentRole cutDeficit s := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show s + (n + 1) = (s + n) + 1 by omega,
        d2ChildDeficitTrace]
      rw [ih (by
        intro k hk
        have h := hpreserves k (by omega)
        simpa [Nat.add_assoc] using h)]
      rcases hpreserves n (by omega) with ⟨hchildInactive, hparent⟩
      rcases hparent with hparentInactive | hbotRise
      · simp [d2ChildDeficitAfterStage, d2NodeDeficitAfterStage,
          hchildInactive, hparentInactive]
      · simp [d2ChildDeficitAfterStage, d2NodeDeficitAfterStage,
          hchildInactive, hbotRise]

/-- Two stages after an ordinary update, the exact quota split and the
surviving endpoint half-port yield the `c/128` reserve, provided the
intermediate child update does not decrease its deficit. -/
theorem d2_ordinary_endpoint_reserve_transfer
    {c cOld piOld half uOld piChild : Rat} (isActive : Bool)
    (hc : 0 < c) (hcap : cOld = 16 * c)
    (hquota : 15 * cOld / 4096 ≤ piOld)
    (heven : piOld = 2 * half) (hcut : half ≤ uOld)
    (hpiChild : 0 ≤ piChild) :
    c / 128 ≤ d2NodeDeficitAfterStage isActive uOld piChild := by
  have hhalf : piOld / 2 ≤ uOld := by rw [heven]; norm_num; exact hcut
  exact ordinary_predecessor_reserve hc hcap hquota hhalf
    (d2NodeDeficitAfterStage_mono isActive hpiChild)

/-- Normalizing the D2 end-child update by the next-time child capacity
`2*c` gives the claimed half-old-deficit plus quarter-port recurrence. -/
theorem normalized_same_child_update {c g rho : Rat} (hc : c ≠ 0) :
    (g * c + rho * c / 2) / (2 * c) = g / 2 + rho / 4 := by
  field_simp
  ring

/-- An ordinary left endpoint cut, normalized by the child's next capacity
`2*c`, is charged by half the parent's normalized deficit plus one quarter
of its normalized port. -/
theorem d2_normalized_left_cut_le_parent_budget
    {c G low pi half : Nat} (hc : 0 < c)
    (hlow : low ≤ G) (heven : pi = 2 * half) :
    ((low + half : Nat) : Rat) / (2 * c) ≤
      (G : Rat) / c / 2 + (pi : Rat) / c / 4 := by
  have hnumNat : 2 * (low + half) ≤ 2 * G + pi := by omega
  have hnum : 2 * ((low + half : Nat) : Rat) ≤ 2 * (G : Rat) + (pi : Rat) :=
    by exact_mod_cast hnumNat
  have hc4 : (0 : Rat) < 4 * (c : Rat) := by exact_mod_cast (by omega : 0 < 4 * c)
  calc
    ((low + half : Nat) : Rat) / (2 * c) =
        (2 * ((low + half : Nat) : Rat)) / (4 * (c : Rat)) := by
          field_simp
          norm_num
    _ ≤ (2 * (G : Rat) + (pi : Rat)) / (4 * (c : Rat)) :=
      (div_le_div_iff_of_pos_right hc4).2 hnum
    _ = (G : Rat) / c / 2 + (pi : Rat) / c / 4 := by
      field_simp
      ring

/-- The corresponding right endpoint reset has the same normalized budget. -/
theorem d2_normalized_right_cut_le_parent_budget
    {c G high pi half : Nat} (hc : 0 < c)
    (hhigh : high ≤ G) (heven : pi = 2 * half) :
    ((high + half : Nat) : Rat) / (2 * c) ≤
      (G : Rat) / c / 2 + (pi : Rat) / c / 4 := by
  have hnumNat : 2 * (high + half) ≤ 2 * G + pi := by omega
  have hnum : 2 * ((high + half : Nat) : Rat) ≤ 2 * (G : Rat) + (pi : Rat) :=
    by exact_mod_cast hnumNat
  have hc4 : (0 : Rat) < 4 * (c : Rat) := by exact_mod_cast (by omega : 0 < 4 * c)
  calc
    ((high + half : Nat) : Rat) / (2 * c) =
        (2 * ((high + half : Nat) : Rat)) / (4 * (c : Rat)) := by
          field_simp
          norm_num
    _ ≤ (2 * (G : Rat) + (pi : Rat)) / (4 * (c : Rat)) :=
      (div_le_div_iff_of_pos_right hc4).2 hnum
    _ = (G : Rat) / c / 2 + (pi : Rat) / c / 4 := by
      field_simp
      ring

/-- Both endpoint cut resets fit the switched-envelope cap whenever the
parent deficit fits `B` and its port allowance `R` satisfies `R/2<=B`. -/
theorem d2_normalized_endpoint_cuts_fit_budget
    {c G low high pi half : Nat} {B R : Rat} (hc : 0 < c)
    (hlow : low ≤ G) (hhigh : high ≤ G) (heven : pi = 2 * half)
    (hG : (G : Rat) / c ≤ B) (hpi : (pi : Rat) / c ≤ R)
    (hR : R / 2 ≤ B) :
    ((low + half : Nat) : Rat) / (2 * c) ≤ B ∧
      ((high + half : Nat) : Rat) / (2 * c) ≤ B := by
  constructor
  · calc
      ((low + half : Nat) : Rat) / (2 * c) ≤
          (G : Rat) / c / 2 + (pi : Rat) / c / 4 :=
            d2_normalized_left_cut_le_parent_budget hc hlow heven
      _ ≤ B := by linarith
  · calc
      ((high + half : Nat) : Rat) / (2 * c) ≤
          (G : Rat) / c / 2 + (pi : Rat) / c / 4 :=
            d2_normalized_right_cut_le_parent_budget hc hhigh heven
      _ ≤ B := by linarith

/-- The cumulative outsider-error potential along a path whose ordinary
same-end updates contract old deficit by one half and inject one quarter of
the current normalized port error. -/
def d2OutsiderErrorPotential (rho : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => d2OutsiderErrorPotential rho n / 2 + rho n / 4

/-- A nonuniform per-step port allowance enters the deficit bound with
geometrically decaying weights. This is the pathwise charging identity behind
a depth-dependent outsider budget. -/
theorem d2_deficit_bound_by_outsider_potential
    {g rho : Nat → Rat} (hstep : ∀ n, g (n + 1) ≤ g n / 2 + rho n / 4)
    (n : Nat) :
    g n ≤ g 0 / (2 : Rat) ^ n + d2OutsiderErrorPotential rho n := by
  induction n with
  | zero => simp [d2OutsiderErrorPotential]
  | succ n ih =>
      have hhalf : g n / 2 ≤
          (g 0 / (2 : Rat) ^ n + d2OutsiderErrorPotential rho n) / 2 :=
        div_le_div_of_nonneg_right ih (by norm_num : (0 : Rat) ≤ 2)
      calc
        g (n + 1) ≤ g n / 2 + rho n / 4 := hstep n
        _ ≤ (g 0 / (2 : Rat) ^ n + d2OutsiderErrorPotential rho n) / 2 +
            rho n / 4 := add_le_add hhalf le_rfl
        _ = g 0 / (2 : Rat) ^ (n + 1) +
            d2OutsiderErrorPotential rho (n + 1) := by
          simp only [d2OutsiderErrorPotential, pow_succ]
          ring

/-- A uniform bound `rho≤R` gives the familiar limiting deficit allowance
`R/2`; a schedule-dependent potential can be strictly smaller. -/
theorem d2_outsider_potential_le_half {rho : Nat → Rat} {R : Rat}
    (hR : ∀ n, rho n ≤ R) (hRnonneg : 0 ≤ R) (n : Nat) :
    d2OutsiderErrorPotential rho n ≤ R / 2 := by
  induction n with
  | zero => simp [d2OutsiderErrorPotential]; linarith
  | succ n ih =>
      calc
        d2OutsiderErrorPotential rho (n + 1) =
            d2OutsiderErrorPotential rho n / 2 + rho n / 4 := rfl
        _ ≤ (R / 2) / 2 + R / 4 := by
          exact add_le_add
            (div_le_div_of_nonneg_right ih (by norm_num : (0 : Rat) ≤ 2))
            (div_le_div_of_nonneg_right (hR n) (by norm_num : (0 : Rat) ≤ 4))
        _ = R / 2 := by ring

/-- At each step, either the existing same-child recurrence contracts the
old deficit and injects a port error, or an ordinary parent cut replaces it
with a separately bounded cut value. This envelope models that branch choice
without charging the two mutually exclusive sources additively. -/
def d2DeficitEnvelopeWithCuts (initial : Rat) (rho cut : Nat → Rat) : Nat → Rat
  | 0 => initial
  | n + 1 => max
      (d2DeficitEnvelopeWithCuts initial rho cut n / 2 + rho n / 4)
      (cut n)

/-- Any concrete path trace satisfying the switched self-update / parent-cut
recurrence stays below its exact dynamic envelope. -/
theorem d2_deficit_bound_by_switched_cut_envelope
    {g rho cut : Nat → Rat} {initial : Rat}
    (hg0 : g 0 ≤ initial)
    (hstep : ∀ n, g (n + 1) ≤ max (g n / 2 + rho n / 4) (cut n))
    (n : Nat) :
    g n ≤ d2DeficitEnvelopeWithCuts initial rho cut n := by
  induction n with
  | zero => exact hg0
  | succ n ih =>
      apply le_trans (hstep n)
      apply max_le_max
      · exact add_le_add
          (div_le_div_of_nonneg_right ih (by norm_num : (0 : Rat) ≤ 2)) le_rfl
      · exact le_rfl

/-- Uniform port and cut allowances `rho<=R`, `cut<=C` preserve any envelope
cap `B` once both branches fit: `R/2<=B` and `C<=B`. -/
theorem d2_deficit_envelope_uniform_cap
    {rho cut : Nat → Rat} {initial B R C : Rat}
    (hinitial : initial ≤ B) (hR : ∀ n, rho n ≤ R)
    (hcut : ∀ n, cut n ≤ C) (hRfit : R / 2 ≤ B)
    (hCfit : C ≤ B) (n : Nat) :
    d2DeficitEnvelopeWithCuts initial rho cut n ≤ B := by
  induction n with
  | zero => exact hinitial
  | succ n ih =>
      unfold d2DeficitEnvelopeWithCuts
      apply max_le
      · calc
          d2DeficitEnvelopeWithCuts initial rho cut n / 2 + rho n / 4 ≤
              B / 2 + R / 4 := by
                exact add_le_add
                  (div_le_div_of_nonneg_right ih (by norm_num : (0 : Rat) ≤ 2))
                  (div_le_div_of_nonneg_right (hR n)
                    (by norm_num : (0 : Rat) ≤ 4))
          _ ≤ B := by linarith
      · exact le_trans (hcut n) hCfit

/-- The opposite end child receives only half the parent up-port. -/
theorem normalized_other_child_update {c rho : Rat} (hc : c ≠ 0) :
    (rho * c / 2) / (2 * c) = rho / 4 := by
  field_simp
  ring

/-- The proposed deficit invariant is preserved by an ordinary end-child
update when the sender's normalized up-port is at most `1/256`. -/
theorem normalized_same_child_preserves_bound {g rho : Rat}
    (hg : g ≤ 1 / 512) (hrho : rho ≤ 1 / 256) :
    g / 2 + rho / 4 ≤ 1 / 512 := by
  linarith

theorem normalized_other_child_preserves_bound {rho : Rat}
    (hrho : rho ≤ 1 / 256) : rho / 4 ≤ 1 / 512 := by
  linarith

/-- The exact `15/4096` ordinary quota preserves the observed
`15/8192` sender-deficit envelope under the same-end-child recurrence. -/
theorem normalized_same_child_preserves_15over8192 {g rho : Rat}
    (hg : g ≤ 15 / 8192) (hrho : rho ≤ 15 / 4096) :
    g / 2 + rho / 4 ≤ 15 / 8192 := by
  linarith

/-- The opposite end child gets at most a quarter of the normalized port. -/
theorem normalized_other_child_preserves_15over8192 {rho : Rat}
    (hrho : rho ≤ 15 / 4096) :
    rho / 4 ≤ 15 / 8192 := by
  linarith

/-- A top-rise parent starts at zero deficit, so its larger `1/256` port
still places both children below the `15/8192` envelope. -/
theorem normalized_topRise_child_preserves_15over8192 {rho : Rat}
    (hrho : rho ≤ 1 / 256) :
    rho / 4 ≤ 15 / 8192 := by
  linarith

/-- The stronger old-deficit budget `23/4096` is preserved by the ordinary
same-end-child recurrence `g/2 + rho/4`. -/
theorem normalized_same_child_preserves_tolerant_bound {g rho : Rat}
    (hg : g ≤ 23 / 4096) (hrho : rho ≤ 1 / 256) :
    g / 2 + rho / 4 ≤ 23 / 4096 := by
  linarith

theorem normalized_other_child_preserves_tolerant_bound {rho : Rat}
    (hrho : rho ≤ 1 / 256) : rho / 4 ≤ 23 / 4096 := by
  linarith

/-- The exact two-step identity forces noncrossing when the `t-2` sender was
ordinary: its port contributes at least `15/4096` of old capacity. -/
theorem ordinary_two_step_forces_noncrossing
    {a pi c gOld rhoOld childRho gNow rhoNow : Rat}
    (hc : 0 < c)
    (hid : a / c = 16 * gOld + 16 * rhoOld + 32 * childRho - gNow)
    (hgOld : 0 ≤ gOld) (hrhoOld : 15 / 4096 ≤ rhoOld)
    (hchild : 0 ≤ childRho) (hgNow : gNow ≤ 7 / 128)
    (hrhoNow : rhoNow ≤ 1 / 256) (hpi : pi / c = rhoNow) :
    pi ≤ a := by
  have hratio : 1 / 256 ≤ a / c := by
    rw [hid]
    linarith
  have hcleared := hratio
  have hcne : c ≠ 0 := ne_of_gt hc
  field_simp [hcne] at hcleared
  have hpiRatio : pi / c ≤ 1 / 256 := by rw [hpi]; exact hrhoNow
  have hpiBound : pi ≤ c / 256 := by
    have h := (div_le_iff₀ hc).1 hpiRatio
    nlinarith
  nlinarith

/-- The two-step identity also forces noncrossing after a `botRise`
predecessor, whose unchanged children give the exact `1/256` native sum. -/
theorem botRise_two_step_forces_noncrossing
    {a pi c gOld rhoOld gNow rhoNow : Rat}
    (hc : 0 < c)
    (hid : a / c = 16 * gOld + 16 * rhoOld - gNow)
    (hnative : gOld + rhoOld = 1 / 256)
    (hgNow : gNow ≤ 15 / 256) (hrhoNow : rhoNow ≤ 1 / 256)
    (hpi : pi / c = rhoNow) :
    pi ≤ a := by
  have hratio : 1 / 256 ≤ a / c := by
    rw [hid]
    linarith
  have hcleared := hratio
  have hcne : c ≠ 0 := ne_of_gt hc
  field_simp [hcne] at hcleared
  have hpiRatio : pi / c ≤ 1 / 256 := by rw [hpi]; exact hrhoNow
  have hpiBound : pi ≤ c / 256 := by
    have h := (div_le_iff₀ hc).1 hpiRatio
    nlinarith
  nlinarith

/-- Child deficit immediately after the older ordinary parent update:
`theta=G+pi/2` on the first child, `pi/2` on the last, and zero inside.
The factors 16 convert old parent capacity into current parent capacity. -/
def d2OldTheta (j : Fin 8) (c gOld rhoOld : Rat) : Rat :=
  (if j = 0 then 16 * c * gOld + 8 * c * rhoOld else 0) +
    (if j = 7 then 8 * c * rhoOld else 0)

theorem d2_old_theta_sum {c gOld rhoOld : Rat} :
    (Finset.univ.sum fun j : Fin 8 => d2OldTheta j c gOld rhoOld) =
      16 * c * (gOld + rhoOld) := by
  classical
  simp only [d2OldTheta, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_pos]
  ring

/-- Exact two-step conservation identity for an ordinary predecessor. Every
intermediate child port is normalized by its capacity `32*c`. -/
theorem d2_two_step_allocation_identity {c gOld rhoOld gNow : Rat}
    (hc : c ≠ 0) (childRho : Fin 8 → Rat) :
    ((Finset.univ.sum fun j : Fin 8 =>
        d2OldTheta j c gOld rhoOld + 32 * c * childRho j) - c * gNow) / c =
      16 * gOld + 16 * rhoOld +
        32 * (Finset.univ.sum childRho) - gNow := by
  have hsum : (Finset.univ.sum fun j : Fin 8 =>
      d2OldTheta j c gOld rhoOld + 32 * c * childRho j) =
      16 * c * (gOld + rhoOld) + 32 * c * (Finset.univ.sum childRho) := by
    rw [Finset.sum_add_distrib, d2_old_theta_sum, Finset.mul_sum]
  rw [hsum]
  field_simp [hc]

/-- Role-split form of the corrected `279/256` sender factor. The exceptional
child-`botRise` case allows a full unit of intermediate child-port mass, but
then its predecessor has the smaller `15/4096` quota; in the other case the
child-port term is at most `15/16`, while the predecessor quota is at most
`1/256`. -/
theorem d2_two_step_sender_factor_279
    {a c gOld rhoOld childRho gNow : Rat}
    (hid : a / c = 16 * gOld + 16 * rhoOld + 32 * childRho - gNow)
    (hgOld : gOld ≤ 1 / 512) (hgNow : 0 ≤ gNow)
    (hroles : (rhoOld ≤ 15 / 4096 ∧ 32 * childRho ≤ 1) ∨
      (rhoOld ≤ 1 / 256 ∧ 32 * childRho ≤ 15 / 16)) :
    a / c ≤ 279 / 256 := by
  rw [hid]
  rcases hroles with ⟨hrho, hchild⟩ | ⟨hrho, hchild⟩
  · nlinarith
  · nlinarith

/-- Applying the verified ordinary two-step identity to the lower-margin
lemma proves that the current ordinary cut fronts cannot cross. -/
theorem d2_ordinary_two_step_non_crossing
    {c gOld rhoOld gNow rhoNow : Rat} (hc : 0 < c)
    (childRho : Fin 8 → Rat)
    (hgOld : 0 ≤ gOld) (hrhoOld : 15 / 4096 ≤ rhoOld)
    (hchild : 0 ≤ Finset.univ.sum childRho)
    (hgNow : gNow ≤ 7 / 128) (hrhoNow : rhoNow ≤ 1 / 256) :
    c * rhoNow ≤
      (Finset.univ.sum fun j : Fin 8 =>
        d2OldTheta j c gOld rhoOld + 32 * c * childRho j) - c * gNow := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hid := d2_two_step_allocation_identity (gOld := gOld)
    (rhoOld := rhoOld) (gNow := gNow) hcne childRho
  have hpi : c * rhoNow / c = rhoNow := by field_simp [hcne]
  exact ordinary_two_step_forces_noncrossing hc hid hgOld hrhoOld hchild
    hgNow hrhoNow hpi

/-- The `(3,3,2)` bottom frontier from the exact ceil/parity formula. -/
def omega (t : Nat) : Nat :=
  if t = 0 then 0 else if t = 1 then 1 else ceilParity ((t + 4) / 3) t

theorem omega_parity (t : Nat) : omega t % 2 = t % 2 := by
  unfold omega ceilParity
  split_ifs <;> omega

/-- Candidate terminal stage for the `(3,3,2)` D2 schedule. -/
def tfD2 (d : Nat) : Nat := 3 * d - 14

/-- The parity-rounded top frontier is at least one level below the
`(t+4)/3` line strictly before termination. -/
theorem alpha_gap_before_tf {d t : Nat} (hd : 7 ≤ d) (ht : 2 ≤ t)
    (htf : t < tfD2 d) : alpha d t + 1 ≤ (t + 4) / 3 := by
  have hs := alphaStar_gap_before_tf hd ht htf
  have ht0 : t ≠ 0 := by omega
  have ht1 : t ≠ 1 := by omega
  unfold alpha
  simp only [if_neg ht0, if_neg ht1]
  unfold ceilParity
  split_ifs <;> omega

/-- The `(8,8,1/4)` capacity, written as a quotient of powers of two. -/
def capacityD2 (d i t : Nat) : Rat :=
  (2 : Rat) ^ (3 * d + 3 * i) / (2 : Rat) ^ (2 * t + 4)

/-- Native number of wires in a level-`i` subtree. -/
def nativeD2 (d i : Nat) : Rat := (2 : Rat) ^ (3 * (d - i))

theorem nativeD2_succ_level {d i : Nat} (hi : i < d) :
    nativeD2 d i = 8 * nativeD2 d (i + 1) := by
  unfold nativeD2
  have hexp : 3 * (d - i) = 3 * (d - (i + 1)) + 3 := by omega
  rw [hexp, pow_add]
  norm_num
  ring

/-- The parent capacity falls by a factor of 16 over two stages. -/
theorem capacityD2_two_stage_ratio {d i t : Nat} (ht : 2 ≤ t) :
    capacityD2 d i (t - 2) = 16 * capacityD2 d i t := by
  have hden : (2 : Rat) ^ (2 * t + 4) =
      (2 : Rat) ^ (2 * (t - 2) + 4) * 16 := by
    rw [show 2 * t + 4 = (2 * (t - 2) + 4) + 4 by omega, pow_add]
    norm_num
  unfold capacityD2
  rw [hden]
  field_simp

/-- A child at the intermediate stage has 32 times the current parent
capacity, giving the coefficient in the two-step port sum. -/
theorem capacityD2_child_mid_ratio {d i t : Nat} (ht : 1 ≤ t) :
    capacityD2 d (i + 1) (t - 1) = 32 * capacityD2 d i t := by
  have hnum : (2 : Rat) ^ (3 * d + 3 * (i + 1)) =
      (2 : Rat) ^ (3 * d + 3 * i) * 8 := by
    rw [show 3 * d + 3 * (i + 1) = (3 * d + 3 * i) + 3 by omega, pow_add]
    norm_num
  have hden : (2 : Rat) ^ (2 * t + 4) =
      (2 : Rat) ^ (2 * (t - 1) + 4) * 4 := by
    rw [show 2 * t + 4 = (2 * (t - 1) + 4) + 2 by omega, pow_add]
    norm_num
  unfold capacityD2
  rw [hnum, hden]
  field_simp
  ring

/-- At a `botRise` boundary, native size is exactly 1/256 of capacity. -/
theorem native_eq_capacity_div_256 {d i t : Nat} (hi : i ≤ d)
    (hboundary : 3 * i = t + 6) :
    nativeD2 d i = capacityD2 d i t / 256 := by
  let e := 3 * (d - i)
  let b := 2 * t + 4
  have hexp : 3 * d + 3 * i = e + b + 8 := by
    dsimp [e, b]
    omega
  have hpow : (2 : Rat) ^ (e + b + 8) =
      (2 : Rat) ^ e * (2 : Rat) ^ b * 256 := by
    rw [show e + b + 8 = (e + b) + 8 by omega, pow_add, pow_add]
    norm_num
  unfold nativeD2 capacityD2
  change (2 : Rat) ^ e = ((2 : Rat) ^ (3 * d + 3 * i) /
    (2 : Rat) ^ (2 * t + 4)) / 256
  rw [hexp, hpow]
  field_simp
  ring

/-- If a `botRise` at `(i,t)` is followed two stages later by the same
sender, its untouched child native size is exactly `c/128`. -/
theorem native_child_eq_later_capacity_div_128 {d i t : Nat}
    (hi : i + 1 ≤ d) (hboundary : 3 * i = t + 6) :
    nativeD2 d (i + 1) = capacityD2 d i (t + 2) / 128 := by
  let e := 3 * (d - (i + 1))
  let b := 2 * (t + 2) + 4
  have hexp : 3 * d + 3 * i = e + b + 7 := by
    dsimp [e, b]
    omega
  have hpow : (2 : Rat) ^ (e + b + 7) =
      (2 : Rat) ^ e * (2 : Rat) ^ b * 128 := by
    rw [show e + b + 7 = (e + b) + 7 by omega, pow_add, pow_add]
    norm_num
  have hb : b = 2 * (t + 2) + 4 := rfl
  unfold nativeD2 capacityD2
  change (2 : Rat) ^ e = ((2 : Rat) ^ (3 * d + 3 * i) /
    (2 : Rat) ^ (2 * (t + 2) + 4)) / 128
  rw [hexp, hpow]
  rw [← hb]
  field_simp

/-- Any allocation no larger than the native subtree has normalized port at
most 1/256 at a `botRise` sender. -/
theorem native_allocation_port_bound {d i t : Nat} {a : Rat}
    (hi : i ≤ d) (hboundary : 3 * i = t + 6)
    (ha : a ≤ nativeD2 d i) :
    a / capacityD2 d i t ≤ 1 / 256 := by
  have hcap : capacityD2 d i t = 256 * nativeD2 d i := by
    have hn := native_eq_capacity_div_256 hi hboundary
    have hc : 0 < capacityD2 d i t := by
      unfold capacityD2
      exact div_pos (pow_pos (by norm_num : (0 : Rat) < 2) _)
        (pow_pos (by norm_num : (0 : Rat) < 2) _)
    linarith
  have hc : 0 < capacityD2 d i t := by
    unfold capacityD2
    exact div_pos (pow_pos (by norm_num : (0 : Rat) < 2) _)
      (pow_pos (by norm_num : (0 : Rat) < 2) _)
  rw [div_le_iff₀ hc, hcap]
  nlinarith

/-- The D2 conservation allocation is at most the native parent size if each
of its eight child deficits is at most that child's native size. -/
theorem allocation_le_native_of_child_deficits {a G n : Nat}
    (childDeficit : Fin 8 → Nat)
    (halloc : a = (Finset.univ.sum childDeficit) - G)
    (hchild : ∀ j, childDeficit j ≤ n) : a ≤ 8 * n := by
  rw [halloc]
  apply (Nat.sub_le _ _).trans
  calc
    Finset.univ.sum childDeficit ≤ Finset.univ.sum (fun _ : Fin 8 => n) :=
      Finset.sum_le_sum (by intro j hj; exact hchild j)
    _ = 8 * n := by simp

/-- If every child deficit is at most its native child size, conservation
bounds the allocation by the native parent size. -/
theorem allocation_le_native_of_child_native {a G d i : Nat}
    (childDeficit : Fin 8 → Nat) (hi : i < d)
    (halloc : a = (Finset.univ.sum childDeficit) - G)
    (hchild : ∀ j, childDeficit j ≤ 8 ^ (d - i - 1)) :
    (a : Rat) ≤ nativeD2 d i := by
  have hnat := allocation_le_native_of_child_deficits childDeficit halloc hchild
  have he : 8 * 8 ^ (d - i - 1) = 8 ^ (d - i) := by
    calc
      8 * 8 ^ (d - i - 1) = 8 ^ (d - i - 1) * 8 := by ring
      _ = 8 ^ ((d - i - 1) + 1) := by rw [Nat.pow_succ]
      _ = 8 ^ (d - i) := by congr 1; omega
  have hnat' : a ≤ 8 ^ (d - i) := by rw [← he]; exact hnat
  have hcast : ((8 ^ (d - i) : Nat) : Rat) = nativeD2 d i := by
    unfold nativeD2
    norm_cast
    rw [show (8 : Nat) = 2 ^ 3 by norm_num, pow_mul]
  rw [← hcast]
  exact_mod_cast hnat'

def d2LeftCut (pos size left : Nat) : Nat := min (pos + size) left - pos

def d2RightCut (pos size right : Nat) : Nat :=
  pos + size - max pos right

theorem d2LeftCut_eq_min_difference (pos size left : Nat) :
    d2LeftCut pos size left =
      min (pos + size) left - min pos left := by
  unfold d2LeftCut
  by_cases hend : pos + size ≤ left
  · rw [Nat.min_eq_left hend, Nat.min_eq_left (by omega : pos ≤ left)]
  · have hleft : left ≤ pos + size := by omega
    rw [Nat.min_eq_right hleft]
    by_cases hpos : pos ≤ left
    · rw [Nat.min_eq_left hpos]
    · have hpos' : left ≤ pos := by omega
      rw [Nat.min_eq_right hpos']
      omega

theorem d2RightCut_eq_max_difference (pos size right : Nat) :
    d2RightCut pos size right =
      max (pos + size) right - max pos right := by
  unfold d2RightCut
  by_cases hpos : pos ≤ right
  · rw [Nat.max_eq_right hpos]
    by_cases hend : pos + size ≤ right
    · rw [Nat.max_eq_right hend]
      omega
    · have hend' : right ≤ pos + size := by omega
      rw [Nat.max_eq_left hend']
  · have hpos' : right ≤ pos := by omega
    rw [Nat.max_eq_left hpos']
    have hend : right ≤ pos + size := by omega
    rw [Nat.max_eq_left hend]

/-- A contained left front alone leaves at least its cut length as deficit in
the first child; the opposite front can only add to that reserve. -/
theorem first_child_cut_reserve {size left right half : Nat}
    (hfit : left ≤ size) (hhalf : half ≤ left) :
    half ≤ d2LeftCut 0 size left + d2RightCut 0 size right := by
  have hleft : d2LeftCut 0 size left = left := by
    simp [d2LeftCut, Nat.min_eq_right hfit]
  omega

/-- Symmetrically, a contained right front leaves at least its distance to
the final child boundary as deficit in the last child. -/
theorem last_child_cut_reserve {pos size left right total high half : Nat}
    (htotal : pos + size = total) (hpos : pos ≤ right)
    (hright : right = total - high - half)
    (hcontained : high + half ≤ total) :
    half ≤ d2LeftCut pos size left + d2RightCut pos size right := by
  have hrightCut : d2RightCut pos size right = high + half := by
    unfold d2RightCut
    rw [htotal, Nat.max_eq_right hpos]
    omega
  omega

/-- The first-child cut geometry directly supplies the half-port premise for
the two-stage reserve transfer. -/
theorem d2_first_endpoint_cut_reserve_transfer
    {size left right half : Nat} {c cOld piOld piChild : Rat}
    (hfit : left ≤ size) (hhalf : half ≤ left)
    (hc : 0 < c) (hcap : cOld = 16 * c)
    (hquota : 15 * cOld / 4096 ≤ piOld)
    (heven : piOld = 2 * (half : Rat)) (isActive : Bool)
    (hpiChild : 0 ≤ piChild) :
    c / 128 ≤ d2NodeDeficitAfterStage isActive
      ((d2LeftCut 0 size left + d2RightCut 0 size right : Nat) : Rat) piChild := by
  have hcut := first_child_cut_reserve (right := right) hfit hhalf
  have hcutRat : (half : Rat) ≤
      ((d2LeftCut 0 size left + d2RightCut 0 size right : Nat) : Rat) := by
    exact_mod_cast hcut
  exact d2_ordinary_endpoint_reserve_transfer isActive hc hcap hquota heven
    hcutRat hpiChild

/-- The last-child cut geometry directly supplies the same half-port premise.
-/
theorem d2_last_endpoint_cut_reserve_transfer
    {pos size left right total high half : Nat} {c cOld piOld piChild : Rat}
    (htotal : pos + size = total) (hpos : pos ≤ right)
    (hright : right = total - high - half)
    (hcontained : high + half ≤ total)
    (hc : 0 < c) (hcap : cOld = 16 * c)
    (hquota : 15 * cOld / 4096 ≤ piOld)
    (heven : piOld = 2 * (half : Rat)) (isActive : Bool)
    (hpiChild : 0 ≤ piChild) :
    c / 128 ≤ d2NodeDeficitAfterStage isActive
      ((d2LeftCut pos size left + d2RightCut pos size right : Nat) : Rat) piChild := by
  have hcut := last_child_cut_reserve (left := left) htotal hpos hright hcontained
  have hcutRat : (half : Rat) ≤
      ((d2LeftCut pos size left + d2RightCut pos size right : Nat) : Rat) := by
    exact_mod_cast hcut
  exact d2_ordinary_endpoint_reserve_transfer isActive hc hcap hquota heven
    hcutRat hpiChild

/-- Disjoint left and right cut fronts remove at most the interval's full
length. This is the local fact needed to keep child deficits under native. -/
theorem d2_cuts_total_le_interval {pos size left right : Nat}
    (hcuts : left ≤ right) :
    d2LeftCut pos size left + d2RightCut pos size right ≤ size := by
  unfold d2LeftCut d2RightCut
  simp only [Nat.min_def, Nat.max_def]
  split_ifs <;> omega

/-- Conservation and a nonnegative outgoing block imply that the updated
parent deficit is no larger than the sum of its child deficits. -/
theorem updated_parent_deficit_le_children {G pi a total : Nat}
    (hconserve : a + G = total) (hpi : pi ≤ a) : G + pi ≤ total := by
  omega

/-- The one-step native-deficit invariant for the parent, from the eight
child caps, conservation, and nonnegative blocks left in the parent. -/
theorem updated_parent_deficit_le_native {G pi a n : Nat}
    (childDeficit : Fin 8 → Nat)
    (hconserve : a + G = Finset.univ.sum childDeficit)
    (hpi : pi ≤ a) (hchild : ∀ j, childDeficit j ≤ n) :
    G + pi ≤ 8 * n := by
  have hsum : Finset.univ.sum childDeficit ≤ 8 * n := by
    calc
      Finset.univ.sum childDeficit ≤ Finset.univ.sum (fun _ : Fin 8 => n) :=
        Finset.sum_le_sum (by intro j hj; exact hchild j)
      _ = 8 * n := by simp
  have htotal := updated_parent_deficit_le_children hconserve hpi
  omega

/-- The D2 cut fronts do not cross whenever their total capacity is enough
to carry the parent deficit and up-port. -/
theorem d2_cut_fronts_noncrossing {a G total low high pi half : Nat}
    (hbalance : low + high = G)
    (hconserve : a + G = total) (hpi : pi ≤ a) (heven : pi = 2 * half) :
    low + half ≤ total - high - half := by
  omega

/-- Full ordinary-cut geometry from the two-step invariant interface: the
global fronts are disjoint and each fits inside its designated end child. -/
theorem d2_ordinary_cut_fronts_valid
    {a G total low high pi half Uleft Uright c : Nat}
    (hbalance : low + high = G) (hconserve : a + G = total)
    (hpiAlloc : pi ≤ a) (heven : pi = 2 * half)
    (hG : 512 * G ≤ c) (hlow : low ≤ G) (hhigh : high ≤ G)
    (hpi : 256 * pi ≤ c) (hleft : c ≤ 128 * Uleft)
    (hright : c ≤ 128 * Uright) :
    low + half ≤ total - high - half ∧
      low + half ≤ Uleft ∧ high + half ≤ Uright := by
  have hcross := d2_cut_fronts_noncrossing hbalance hconserve hpiAlloc heven
  have hends := d2_endpoint_fronts_fit_of_reserve hG hlow hhigh hpi heven
    hleft hright
  exact ⟨hcross, hends.1, hends.2⟩

/-- The five port-size cases in the `(8,8,1/4)` D2 update. -/
def d2PortSize (role : D2Role) (a c : Rat) : Rat :=
  match role with
  | .topDesc => 0
  | .topRise => c / 256
  | .mid => 15 * c / 4096
  | .botDesc => 15 * c / 4096
  | .botRise => a

theorem d2PortSize_nonneg {role : D2Role} {a c : Rat}
    (ha : 0 ≤ a) (hc : 0 ≤ c) : 0 ≤ d2PortSize role a c := by
  cases role with
  | topDesc => simp [d2PortSize]
  | topRise => exact div_nonneg hc (by norm_num)
  | mid => exact div_nonneg (mul_nonneg (by norm_num) hc) (by norm_num)
  | botDesc => exact div_nonneg (mul_nonneg (by norm_num) hc) (by norm_num)
  | botRise => exact ha

/-- Every ordinary positive-up role has quota between the bottom quota and
the uniform sender cap used by the invariant. -/
theorem d2_regular_port_range {role : D2Role} {a c : Rat}
    (hc : 0 ≤ c)
    (hrole : role = .topRise ∨ role = .mid ∨ role = .botDesc) :
    15 * c / 4096 ≤ d2PortSize role a c ∧
      d2PortSize role a c ≤ c / 256 := by
  rcases hrole with h | h | h
  · subst role
    constructor <;> simp [d2PortSize] <;> linarith
  · subst role
    constructor <;> simp [d2PortSize] <;> linarith
  · subst role
    constructor <;> simp [d2PortSize] <;> linarith

/-- Exact child-deficit update for one interval in the local D2 recurrence.
`topDesc` makes no child cuts, `botRise` bypasses the children, and every
ordinary role stores the two end pieces cut from this child's interval. -/
def d2LocalChildDeficitUpdate (role : D2Role) (pos size left right : Nat) : Nat :=
  match role with
  | .topDesc => 0
  | .botRise => size
  | .topRise | .mid | .botDesc =>
      d2LeftCut pos size left + d2RightCut pos size right

/-- An ordinary cut contained in the first child leaves exactly its left
front as that child's new deficit. -/
theorem d2_ordinary_first_child_update {size left right : Nat}
    (hleft : left ≤ size) (hright : size ≤ right) :
    d2LocalChildDeficitUpdate .mid 0 size left right = left := by
  simp [d2LocalChildDeficitUpdate, d2LeftCut, d2RightCut,
    Nat.min_eq_right hleft]
  omega

/-- If both fronts miss an interior child interval, its new deficit is zero. -/
theorem d2_ordinary_interior_child_update {pos size left right : Nat}
    (hleft : left ≤ pos) (hright : pos + size ≤ right) :
    d2LocalChildDeficitUpdate .mid pos size left right = 0 := by
  simp [d2LocalChildDeficitUpdate, d2LeftCut, d2RightCut,
    Nat.min_eq_right (by omega : left ≤ pos + size),
    Nat.max_eq_right (by omega : pos ≤ right)]
  omega

/-- A contained right front leaves exactly the high-side cut length in the
last child. -/
theorem d2_ordinary_last_child_update
    {pos size left right total high half : Nat}
    (htotal : pos + size = total) (hleft : left ≤ pos)
    (hright : pos ≤ right) (hrightCut : right = total - high - half)
    (hcontained : high + half ≤ total) :
    d2LocalChildDeficitUpdate .mid pos size left right = high + half := by
  have hrightLe : right ≤ total := by omega
  simp [d2LocalChildDeficitUpdate, d2LeftCut, d2RightCut,
    Nat.max_eq_right hright]
  omega

/-- Prefix positions of eight consecutive child intervals place every middle
child between the first child's end and the last child's start. -/
theorem d2_contiguous_children_ordered
    (size pos : Fin 8 → Nat) (hstart : pos 0 = 0)
    (hcontig : ∀ k : Nat, (hk : k < 7) →
      pos ⟨k + 1, by omega⟩ = pos ⟨k, by omega⟩ + size ⟨k, by omega⟩) :
    size 0 ≤ pos 7 ∧
      ∀ j : Fin 8, 0 < j.val → j.val < 7 →
        size 0 ≤ pos j ∧ pos j + size j ≤ pos 7 := by
  have hc0 := hcontig 0 (by omega)
  have hc1 := hcontig 1 (by omega)
  have hc2 := hcontig 2 (by omega)
  have hc3 := hcontig 3 (by omega)
  have hc4 := hcontig 4 (by omega)
  have hc5 := hcontig 5 (by omega)
  have hc6 := hcontig 6 (by omega)
  simp at hc0 hc1 hc2 hc3 hc4 hc5 hc6
  constructor
  · omega
  · intro j hjlo hjhi
    have hcases : j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨
        j.val = 4 ∨ j.val = 5 ∨ j.val = 6 := by omega
    rcases hcases with h | h | h | h | h | h
    · have hj : j = (1 : Fin 8) := Fin.ext h
      subst j
      simp_all
      omega
    · have hj : j = (2 : Fin 8) := Fin.ext h
      subst j
      simp_all
      omega
    · have hj : j = (3 : Fin 8) := Fin.ext h
      subst j
      simp_all
      omega
    · have hj : j = (4 : Fin 8) := Fin.ext h
      subst j
      simp_all
      omega
    · have hj : j = (5 : Fin 8) := Fin.ext h
      subst j
      simp_all
      omega
    · have hj : j = (6 : Fin 8) := Fin.ext h
      subst j
      simp_all
      omega

/-- When the ordered child intervals run from zero to `total`, and the two
fronts fit in the designated end children, the D2 cut update has exactly the
usual three-part shape: left endpoint, zero interior, right endpoint. -/
theorem d2_ordinary_cut_output_pattern
    (size pos : Fin 8 → Nat) {left right total high half : Nat}
    (hstart : pos 0 = 0)
    (hcontig : ∀ k : Nat, (hk : k < 7) →
      pos ⟨k + 1, by omega⟩ = pos ⟨k, by omega⟩ + size ⟨k, by omega⟩)
    (hfirst : left ≤ size 0)
    (htotal : pos 7 + size 7 = total)
    (hrightStart : pos 7 ≤ right)
    (hrightFit : high + half ≤ size 7)
    (hrightFormula : right = total - high - half)
    :
    d2LocalChildDeficitUpdate .mid (pos 0) (size 0) left right = left ∧
      d2LocalChildDeficitUpdate .mid (pos 7) (size 7) left right = high + half ∧
      ∀ j : Fin 8, 0 < j.val → j.val < 7 →
        d2LocalChildDeficitUpdate .mid (pos j) (size j) left right = 0 := by
  have hordered := d2_contiguous_children_ordered size pos hstart hcontig
  have hfirstLast : size 0 ≤ pos 7 := hordered.1
  have hinterior := hordered.2
  have hfirstRight : size 0 ≤ right := le_trans hfirstLast hrightStart
  have hleftLast : left ≤ pos 7 := le_trans hfirst hfirstLast
  have hcontained : high + half ≤ total := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hstart]
    exact d2_ordinary_first_child_update hfirst hfirstRight
  · exact d2_ordinary_last_child_update htotal hleftLast hrightStart
      hrightFormula hcontained
  · intro j hjlo hjhi
    exact d2_ordinary_interior_child_update
      (le_trans hfirst (hinterior j hjlo hjhi).1)
      (le_trans (hinterior j hjlo hjhi).2 hrightStart)

/-- An ordinary D2 node update under the proposed invariant has exactly the
two endpoint deficits `low+pi/2` and `high+pi/2`; its six interior children
are cleared. The only geometric inputs are contiguous child intervals and
the two `c/128` endpoint reserves. -/
theorem d2_ordinary_update_shape_of_reserve
    {a G total low high pi half c : Nat} (size pos : Fin 8 → Nat)
    (hbalance : low + high = G) (hconserve : a + G = total)
    (hpiAlloc : pi ≤ a) (heven : pi = 2 * half)
    (hG : 512 * G ≤ c) (hlow : low ≤ G) (hhigh : high ≤ G)
    (hpi : 256 * pi ≤ c) (hleftReserve : c ≤ 128 * size 0)
    (hrightReserve : c ≤ 128 * size 7)
    (hstart : pos 0 = 0)
    (hcontig : ∀ k : Nat, (hk : k < 7) →
      pos ⟨k + 1, by omega⟩ = pos ⟨k, by omega⟩ + size ⟨k, by omega⟩)
    (htotal : pos 7 + size 7 = total) :
    d2LocalChildDeficitUpdate .mid (pos 0) (size 0)
        (low + half) (total - high - half) = low + half ∧
      d2LocalChildDeficitUpdate .mid (pos 7) (size 7)
        (low + half) (total - high - half) = high + half ∧
      ∀ j : Fin 8, 0 < j.val → j.val < 7 →
        d2LocalChildDeficitUpdate .mid (pos j) (size j)
          (low + half) (total - high - half) = 0 := by
  have hvalid := d2_ordinary_cut_fronts_valid hbalance hconserve hpiAlloc
    heven hG hlow hhigh hpi hleftReserve hrightReserve
  have hrightStart : pos 7 ≤ total - high - half := by omega
  exact d2_ordinary_cut_output_pattern size pos hstart hcontig hvalid.2.1
    htotal hrightStart hvalid.2.2 rfl

/-- Under the relaxed `23/4096` deficit cap, an ordinary cut still has the
same exact two-endpoint/zero-interior shape, provided it fits the endpoint
reserves. -/
theorem d2_ordinary_update_shape_of_tolerant_reserve
    {a G total low high pi half c : Nat} (size pos : Fin 8 → Nat)
    (hbalance : low + high = G) (hconserve : a + G = total)
    (hpiAlloc : pi ≤ a) (heven : pi = 2 * half)
    (hG : 4096 * G ≤ 23 * c) (hlow : low ≤ G) (hhigh : high ≤ G)
    (hpi : 256 * pi ≤ c) (hleftReserve : c ≤ 128 * size 0)
    (hrightReserve : c ≤ 128 * size 7)
    (hstart : pos 0 = 0)
    (hcontig : ∀ k : Nat, (hk : k < 7) →
      pos ⟨k + 1, by omega⟩ = pos ⟨k, by omega⟩ + size ⟨k, by omega⟩)
    (htotal : pos 7 + size 7 = total) :
    d2LocalChildDeficitUpdate .mid (pos 0) (size 0)
        (low + half) (total - high - half) = low + half ∧
      d2LocalChildDeficitUpdate .mid (pos 7) (size 7)
        (low + half) (total - high - half) = high + half ∧
      ∀ j : Fin 8, 0 < j.val → j.val < 7 →
        d2LocalChildDeficitUpdate .mid (pos j) (size j)
          (low + half) (total - high - half) = 0 := by
  have hcross := d2_cut_fronts_noncrossing hbalance hconserve hpiAlloc heven
  have hends := d2_endpoint_fronts_fit_of_tolerant_reserve
    hG hlow hhigh hpi heven hleftReserve hrightReserve
  have hrightStart : pos 7 ≤ total - high - half := by omega
  exact d2_ordinary_cut_output_pattern size pos hstart hcontig
    hends.1 htotal hrightStart hends.2 rfl

/-- The relaxed sender cap propagates to both endpoint children at their
next-time `2*c` capacity with room to spare. -/
theorem d2_ordinary_end_child_deficit_tolerant_cap
    {G low high pi half c : Nat}
    (hG : 4096 * G ≤ 23 * c) (hlow : low ≤ G) (hhigh : high ≤ G)
    (hpi : 256 * pi ≤ c) (heven : pi = 2 * half) :
    4096 * (low + half) ≤ 46 * c ∧
      4096 * (high + half) ≤ 46 * c := by
  omega

/-- The ordinary end-child outputs fit the proposed `1/512` normalized
deficit cap at next-time child capacity `2*c`. -/
theorem d2_ordinary_end_child_deficit_cap
    {G low high pi half c : Nat}
    (hG : 512 * G ≤ c) (hlow : low ≤ G) (hhigh : high ≤ G)
    (hpi : 256 * pi ≤ c) (heven : pi = 2 * half) :
    512 * (low + half) ≤ 2 * c ∧ 512 * (high + half) ≤ 2 * c := by
  omega

/-- The actual ordinary quota supports the sharper fixed-point endpoint
budget `15/8192`: if the parent deficit is at most `15/8192` of `c` and
`pi/c <= 15/4096`, each end-child deficit is at most `15/8192` of its next
capacity `2*c`. -/
theorem d2_ordinary_end_child_deficit_15over8192
    {G low high pi half c : Nat}
    (hG : 8192 * G ≤ 15 * c) (hlow : low ≤ G) (hhigh : high ≤ G)
    (hpi : 4096 * pi ≤ 15 * c) (heven : pi = 2 * half) :
    4096 * (low + half) ≤ 15 * c ∧
      4096 * (high + half) ≤ 15 * c := by
  omega

/-- One ordinary D2 parent step preserves the normalized `1/512` deficit
bound on every child, given the induction hypotheses and endpoint reserves. -/
theorem d2_ordinary_update_preserves_child_g_bound
    {a G total low high pi half c : Nat} (size pos : Fin 8 → Nat)
    (hbalance : low + high = G) (hconserve : a + G = total)
    (hpiAlloc : pi ≤ a) (heven : pi = 2 * half)
    (hG : 512 * G ≤ c) (hlow : low ≤ G) (hhigh : high ≤ G)
    (hpi : 256 * pi ≤ c) (hleftReserve : c ≤ 128 * size 0)
    (hrightReserve : c ≤ 128 * size 7)
    (hstart : pos 0 = 0)
    (hcontig : ∀ k : Nat, (hk : k < 7) →
      pos ⟨k + 1, by omega⟩ = pos ⟨k, by omega⟩ + size ⟨k, by omega⟩)
    (htotal : pos 7 + size 7 = total) :
    ∀ j : Fin 8, 512 * d2LocalChildDeficitUpdate .mid (pos j)
      (size j) (low + half) (total - high - half) ≤ 2 * c := by
  have hshape := d2_ordinary_update_shape_of_reserve size pos hbalance
    hconserve hpiAlloc heven hG hlow hhigh hpi hleftReserve hrightReserve
    hstart hcontig htotal
  have hends := d2_ordinary_end_child_deficit_cap hG hlow hhigh hpi heven
  intro j
  by_cases hfirst : j = 0
  · subst j
    rw [hshape.1]
    exact hends.1
  · by_cases hlast : j = 7
    · subst j
      rw [hshape.2.1]
      exact hends.2
    · have hjlo : 0 < j.val := by omega
      have hjhi : j.val < 7 := by omega
      rw [hshape.2.2 j hjlo hjhi]
      omega

/-- The three ordinary roles use the same interval-cut deficit formula. -/
theorem d2LocalChildDeficitUpdate_regular_eq_mid {role : D2Role}
    (hrole : role = .topRise ∨ role = .mid ∨ role = .botDesc)
    (pos size left right : Nat) :
    d2LocalChildDeficitUpdate role pos size left right =
      d2LocalChildDeficitUpdate .mid pos size left right := by
  rcases hrole with h | h | h
  · subst role
    rfl
  · subst role
    rfl
  · subst role
    rfl

/-- Endpoint reserves and the sender caps propagate the `1/512` child
deficit invariant for any of the three ordinary parent roles. -/
theorem d2_regular_update_preserves_child_g_bound {role : D2Role}
    (hrole : role = .topRise ∨ role = .mid ∨ role = .botDesc)
    {a G total low high pi half c : Nat} (size pos : Fin 8 → Nat)
    (hbalance : low + high = G) (hconserve : a + G = total)
    (hpiAlloc : pi ≤ a) (heven : pi = 2 * half)
    (hG : 512 * G ≤ c) (hlow : low ≤ G) (hhigh : high ≤ G)
    (hpi : 256 * pi ≤ c) (hleftReserve : c ≤ 128 * size 0)
    (hrightReserve : c ≤ 128 * size 7) (hstart : pos 0 = 0)
    (hcontig : ∀ k : Nat, (hk : k < 7) →
      pos ⟨k + 1, by omega⟩ = pos ⟨k, by omega⟩ + size ⟨k, by omega⟩)
    (htotal : pos 7 + size 7 = total) :
    ∀ j : Fin 8, 512 * d2LocalChildDeficitUpdate role (pos j)
      (size j) (low + half) (total - high - half) ≤ 2 * c := by
  have hmid := d2_ordinary_update_preserves_child_g_bound size pos
    hbalance hconserve hpiAlloc heven hG hlow hhigh hpi hleftReserve
    hrightReserve hstart hcontig htotal
  intro j
  rw [d2LocalChildDeficitUpdate_regular_eq_mid hrole (pos j)
    (size j) (low + half) (total - high - half)]
  exact hmid j

/-- The executable local child update preserves the child's native-deficit
cap when the two ordinary cuts are disjoint. -/
theorem d2LocalChildDeficitUpdate_le_native {role : D2Role}
    {pos size left right native : Nat} (hsize : size ≤ native)
    (hcuts : left ≤ right) :
    d2LocalChildDeficitUpdate role pos size left right ≤ native := by
  cases role with
  | topDesc => simp [d2LocalChildDeficitUpdate]
  | topRise =>
      simpa [d2LocalChildDeficitUpdate] using
        (d2_cuts_total_le_interval (pos := pos) (size := size) hcuts).trans hsize
  | mid =>
      simpa [d2LocalChildDeficitUpdate] using
        (d2_cuts_total_le_interval (pos := pos) (size := size) hcuts).trans hsize
  | botDesc =>
      simpa [d2LocalChildDeficitUpdate] using
        (d2_cuts_total_le_interval (pos := pos) (size := size) hcuts).trans hsize
  | botRise => exact hsize

/-- One complete eight-child D2 node update preserves the native caps on the
parent and every child, provided the ordinary fronts are disjoint. The
conservation hypotheses are exactly the allocation and send-up equations. -/
theorem d2_local_update_preserves_native {role : D2Role}
    {a G pi childNative : Nat} (childSize pos : Fin 8 → Nat)
    (left right : Nat)
    (hconserve : a + G = Finset.univ.sum childSize)
    (hpi : pi ≤ a) (hchild : ∀ j, childSize j ≤ childNative)
    (hcuts : left ≤ right) :
    G + pi ≤ 8 * childNative ∧
      ∀ j, d2LocalChildDeficitUpdate role (pos j) (childSize j)
        left right ≤ childNative := by
  constructor
  · exact updated_parent_deficit_le_native childSize hconserve hpi hchild
  · intro j
    exact d2LocalChildDeficitUpdate_le_native (hchild j) hcuts

/-- Full ordinary local-invariant step. Given child-native bounds, sender
`g`/port bounds, and endpoint reserves, the exact D2 update preserves native
caps on the parent and children and propagates the `g<=1/512` child bound. -/
theorem d2_ordinary_local_invariant_step
    {a G total low high pi half c childNative : Nat}
    (childSize pos : Fin 8 → Nat)
    (hsum : Finset.univ.sum childSize = total)
    (hconserve : a + G = Finset.univ.sum childSize)
    (hbalance : low + high = G) (hpiAlloc : pi ≤ a)
    (hchild : ∀ j, childSize j ≤ childNative)
    (hG : 512 * G ≤ c) (hlow : low ≤ G) (hhigh : high ≤ G)
    (hpi : 256 * pi ≤ c) (heven : pi = 2 * half)
    (hleftReserve : c ≤ 128 * childSize 0)
    (hrightReserve : c ≤ 128 * childSize 7)
    (hstart : pos 0 = 0)
    (hcontig : ∀ k : Nat, (hk : k < 7) →
      pos ⟨k + 1, by omega⟩ = pos ⟨k, by omega⟩ + childSize ⟨k, by omega⟩)
    (htotal : pos 7 + childSize 7 = total) :
    a ≤ 8 * childNative ∧ G + pi ≤ 8 * childNative ∧
      (∀ j, d2LocalChildDeficitUpdate .mid (pos j) (childSize j)
        (low + half) (total - high - half) ≤ childNative) ∧
      (∀ j, 512 * d2LocalChildDeficitUpdate .mid (pos j) (childSize j)
        (low + half) (total - high - half) ≤ 2 * c) := by
  have htotalConserve : a + G = total := by omega
  have halloc : a = (Finset.univ.sum childSize) - G := by omega
  have hcross := d2_cut_fronts_noncrossing hbalance htotalConserve hpiAlloc heven
  have hnative := d2_local_update_preserves_native (role := .mid)
    childSize pos (low + half) (total - high - half) hconserve hpiAlloc hchild hcross
  have ha := allocation_le_native_of_child_deficits childSize halloc hchild
  have hg := d2_ordinary_update_preserves_child_g_bound childSize pos
    hbalance htotalConserve hpiAlloc heven hG hlow hhigh hpi hleftReserve
    hrightReserve hstart hcontig htotal
  exact ⟨ha, hnative.1, hnative.2, hg⟩

/-- Every D2 role has up-port at most `c/256`; only the exceptional `botRise`
case needs an allocation bound by native size. -/
theorem d2_role_port_bound {role : D2Role} {a c : Rat}
    (hc : 0 < c) (hbot : role = .botRise → a ≤ c / 256) :
    d2PortSize role a c ≤ c / 256 := by
  cases role with
  | topDesc => simp [d2PortSize]; linarith
  | topRise => simp [d2PortSize]
  | mid => unfold d2PortSize; linarith
  | botDesc => unfold d2PortSize; linarith
  | botRise => exact hbot rfl

/-- The role port bound follows from native allocation for the `botRise`
case, using the exact schedule boundary/capacity identity. -/
theorem d2_role_port_bound_of_native {d i t : Nat} {a : Rat}
    {role : D2Role} (hi : i ≤ d)
    (hbot : role = .botRise → 3 * i = t + 6)
    (ha : a ≤ nativeD2 d i) :
    d2PortSize role a (capacityD2 d i t) ≤ capacityD2 d i t / 256 := by
  have hc : 0 < capacityD2 d i t := by
    unfold capacityD2
    exact div_pos (pow_pos (by norm_num : (0 : Rat) < 2) _)
      (pow_pos (by norm_num : (0 : Rat) < 2) _)
  apply d2_role_port_bound hc
  intro hrole
  have hfrac := native_allocation_port_bound hi (hbot hrole) ha
  have hmul : a ≤ (1 / 256 : Rat) * capacityD2 d i t :=
    (div_le_iff₀ hc).1 hfrac
  nlinarith

/-- The exceptional `botRise` port bound follows directly from the eight
reachable child-deficit caps and the conservation allocation formula. -/
theorem botRise_port_bound_of_child_deficits {d i t a G : Nat}
    (childDeficit : Fin 8 → Nat) (hi : i < d)
    (hboundary : 3 * i = t + 6)
    (halloc : a = (Finset.univ.sum childDeficit) - G)
    (hchild : ∀ j, childDeficit j ≤ 8 ^ (d - i - 1)) :
    d2PortSize .botRise (a : Rat) (capacityD2 d i t) ≤
      capacityD2 d i t / 256 := by
  have ha := allocation_le_native_of_child_native childDeficit hi halloc hchild
  exact d2_role_port_bound_of_native hi.le (by intro; exact hboundary) ha

/-- At the candidate terminal stage the two rounded frontiers meet. -/
theorem frontiers_meet_at_tf {d : Nat} (hd : 7 ≤ d) :
    alpha d (tfD2 d) = omega (tfD2 d) := by
  have hdivA : (2 * (3 * d - 14) + 11 - 3 * d + 2) / 3 = d - 5 := by omega
  have hdivO : (3 * d - 14 + 4) / 3 = d - 4 := by omega
  have hnot : ¬ 2 * (3 * d - 14) + 11 ≤ 3 * d := by omega
  have ht0 : 3 * d - 14 ≠ 0 := by omega
  have ht1 : 3 * d - 14 ≠ 1 := by omega
  have hstar : alphaStar d (3 * d - 14) = d - 5 := by
    unfold alphaStar
    rw [if_neg hnot, hdivA]
  have hparA : (d - 5) % 2 ≠ (3 * d - 14) % 2 := by omega
  have hparO : (d - 4) % 2 = (3 * d - 14) % 2 := by omega
  change alpha d (3 * d - 14) = omega (3 * d - 14)
  rw [show alpha d (3 * d - 14) = ceilParity (d - 5) (3 * d - 14) by
    simp [alpha, ht0, ht1, hstar]]
  rw [show omega (3 * d - 14) = ceilParity (d - 4) (3 * d - 14) by
    simp [omega, ht0, ht1, hdivO]]
  simp [ceilParity, hparA, hparO]
  omega

/-- The candidate terminal stage is the first frontier meeting: throughout
the earlier active schedule there is a two-level gap. -/
theorem frontiers_separated_before_tf {d t : Nat} (hd : 7 ≤ d)
    (ht : 2 ≤ t) (htf : t < tfD2 d) : alpha d t + 2 ≤ omega t := by
  have ht0 : t ≠ 0 := by omega
  have ht1 : t ≠ 1 := by omega
  unfold tfD2 at htf
  have hgap := alphaStar_gap_before_tf hd ht htf
  rw [show alpha d t = ceilParity (alphaStar d t) t by
    simp [alpha, ht0, ht1]]
  rw [show omega t = ceilParity ((t + 4) / 3) t by
    simp [omega, ht0, ht1]]
  exact ceilParity_gap_two hgap

/-- With matching parity, the upper activity inequality is exactly the
rounded bottom-frontier condition. -/
theorem i_le_omega_iff_threshold {i t : Nat} (ht : 2 ≤ t)
    (hpar : i % 2 = t % 2) :
    i ≤ omega t ↔ 3 * i < t + 8 := by
  have ht0 : t ≠ 0 := by omega
  have ht1 : t ≠ 1 := by omega
  simp only [omega, if_neg ht0, if_neg ht1]
  unfold ceilParity
  split_ifs <;> omega

theorem omega_three_mul (j : Nat) (hj : 1 ≤ j) : omega (3 * j) = j + 2 := by
  have ht0 : 3 * j ≠ 0 := by omega
  have ht1 : 3 * j ≠ 1 := by omega
  have hdiv : (3 * j + 4) / 3 = j + 1 := by omega
  have hpar : (j + 1) % 2 ≠ (3 * j) % 2 := by omega
  simp [omega, ht0, ht1, ceilParity, hdiv, hpar]

theorem omega_three_mul_add_one (j : Nat) : omega (3 * j + 1) = j + 1 := by
  by_cases hj : j = 0
  · subst j
    norm_num [omega]
  · have hdiv : (3 * j + 1 + 4) / 3 = j + 1 := by omega
    have hpar : (j + 1) % 2 = (3 * j + 1) % 2 := by omega
    simp [omega, ceilParity, hdiv, hpar]

theorem omega_three_mul_add_two (j : Nat) : omega (3 * j + 2) = j + 2 := by
  have ht1 : 3 * j + 2 ≠ 1 := by omega
  have hdiv : (3 * j + 2 + 4) / 3 = j + 2 := by omega
  have hpar : (j + 2) % 2 = (3 * j + 2) % 2 := by omega
  simp [omega, ht1, ceilParity, hdiv, hpar]

/-- A falling bottom frontier occurs only at a multiple-of-three stage, with
the exact `botRise` boundary level. -/
theorem omega_drop_implies_botRise_boundary {i t : Nat} (ht : 2 ≤ t)
    (hi : i = omega t) (hdrop : omega (t + 1) < omega t) :
    3 * i = t + 6 := by
  have hmod : t % 3 < 3 := Nat.mod_lt _ (by decide)
  have hrem : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  have hdecomp : t = 3 * (t / 3) + t % 3 := by omega
  rcases hrem with hr | hr | hr
  · have ht' : t = 3 * (t / 3) := by omega
    have hj : 1 ≤ t / 3 := by omega
    have hcur : omega t = t / 3 + 2 := by
      rw [ht', omega_three_mul _ hj]
      simp
    have hnext : omega (t + 1) = t / 3 + 1 := by
      rw [show t + 1 = 3 * (t / 3) + 1 by omega,
        omega_three_mul_add_one]
    rw [hcur, hnext] at hdrop
    rw [hi, hcur]
    omega
  · have ht' : t = 3 * (t / 3) + 1 := by omega
    have hcur : omega t = t / 3 + 1 := by
      rw [ht', omega_three_mul_add_one]
      simp
      omega
    have hnext : omega (t + 1) = t / 3 + 2 := by
      rw [show t + 1 = 3 * (t / 3) + 2 by omega,
        omega_three_mul_add_two]
    rw [hcur, hnext] at hdrop
    rw [hi, hcur]
    omega
  · have ht' : t = 3 * (t / 3) + 2 := by omega
    have hj : 1 ≤ t / 3 + 1 := by omega
    have hcur : omega t = t / 3 + 2 := by
      rw [ht', omega_three_mul_add_two]
      simp
      omega
    have hnext : omega (t + 1) = t / 3 + 3 := by
      rw [show t + 1 = 3 * (t / 3 + 1) by omega,
        omega_three_mul (t / 3 + 1) hj]
    rw [hcur, hnext] at hdrop
    rw [hi, hcur]
    omega

/-- The equality boundary in the activity test is exactly the one-stage
bottom-frontier drop that defines a `botRise` sender. -/
theorem botRise_boundary_frontier {i t : Nat} (ht : 3 ≤ t)
    (hboundary : 3 * i = t + 6) :
    omega t = i ∧ omega (t + 1) + 1 = i := by
  have hi : 3 ≤ i := by omega
  let j := i - 2
  have hj : 1 ≤ j := by dsimp [j]; omega
  have htime : t = 3 * j := by dsimp [j]; omega
  rw [htime, omega_three_mul j hj, omega_three_mul_add_one j]
  dsimp [j]
  omega

/-- Before time `3*j`, the bottom frontier stays strictly above level `j+2`.
This is the parent-inactivity fact needed to keep a `botRise` sender's child
deficits at their native sizes. -/
theorem omega_le_before_botRise {s j : Nat} (h : s + 1 ≤ 3 * j) :
    omega s ≤ j + 1 := by
  have hmod : s % 3 < 3 := Nat.mod_lt _ (by decide)
  have hrem : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
  have hdecomp : s = 3 * (s / 3) + s % 3 := by omega
  rcases hrem with hr | hr | hr
  · have hs : s = 3 * (s / 3) := by omega
    by_cases hq : s / 3 = 0
    · rw [hs, hq]
      norm_num [omega]
    · have hqpos : 1 ≤ s / 3 := by omega
      rw [hs, omega_three_mul (s / 3) hqpos]
      omega
  · have hs : s = 3 * (s / 3) + 1 := by omega
    rw [hs, omega_three_mul_add_one]
    omega
  · have hs : s = 3 * (s / 3) + 2 := by omega
    rw [hs, omega_three_mul_add_two]
    omega

/-- The exact three residues around a bottom-rise sender. -/
theorem omega_botRise_window (j : Nat) (hj : 1 ≤ j) :
    omega (3 * j) = j + 2 ∧
      omega (3 * j + 1) = j + 1 ∧
      omega (3 * j + 2) = j + 2 := by
  exact ⟨omega_three_mul j hj, omega_three_mul_add_one j,
    omega_three_mul_add_two j⟩

/-- Closed activity inequalities from the `(3,3,2)` floor/parity schedule.
The special first stage has only level one active. -/
def active (d tf i t : Nat) : Prop :=
  if t = 1 then i = 1 else
    2 ≤ t ∧ t ≤ tf ∧ i % 2 = t % 2 ∧
      3 * i + 3 * d ≥ 2 * t + 11 ∧ 3 * i < t + 8

/-- The closed activity inequalities are exactly membership in the rounded
frontier interval, once the stage is past startup. -/
theorem active_iff_frontiers {d tf i t : Nat} (ht : 2 ≤ t) :
    active d tf i t ↔
      t ≤ tf ∧ alpha d t ≤ i ∧ i ≤ omega t ∧ i % 2 = t % 2 := by
  have ht1 : t ≠ 1 := by omega
  constructor
  · intro ha
    unfold active at ha
    simp only [if_neg ht1] at ha
    rcases ha with ⟨_, htf, hpar, hlow, hup⟩
    refine ⟨htf, ?_, ?_, hpar⟩
    · exact (alpha_le_iff_threshold ht hpar).2 (by omega)
    · exact (i_le_omega_iff_threshold ht hpar).2 (by omega)
  · rintro ⟨htf, hlow, hup, hpar⟩
    unfold active
    simp only [if_neg ht1]
    refine ⟨ht, htf, hpar, ?_, ?_⟩
    · have h := (alpha_le_iff_threshold ht hpar).1 hlow
      omega
    · exact (i_le_omega_iff_threshold ht hpar).1 hup

/-- A node active at stage `t` is inactive at the immediately preceding
stage: its level parity matches only one of the two stages. -/
theorem active_same_level_prev_stage_false {d tf i t : Nat}
    (ht : 2 ≤ t) (ha : active d tf i t) :
    ¬ active d tf i (t - 1) := by
  have hpar := (active_iff_frontiers (d := d) (tf := tf) (i := i)
    (t := t) ht).1 ha |>.2.2.2
  by_cases hprev1 : t - 1 = 1
  · intro hprev
    have hi : i = 1 := by simpa [active, hprev1] using hprev
    omega
  · intro hprev
    have hparts : 2 ≤ t - 1 ∧ t - 1 ≤ tf ∧
        i % 2 = (t - 1) % 2 ∧
        3 * i + 3 * d ≥ 2 * (t - 1) + 11 ∧ 3 * i < t - 1 + 8 := by
      simpa [active, hprev1] using hprev
    omega

/-- No leaf level is active before the candidate terminal stage, so every
active sender in the processed schedule has eight children. -/
theorem no_active_leaf_before_tf {d t : Nat} (hd : 7 ≤ d)
    (ht : 2 ≤ t) (htf : t ≤ tfD2 d) : ¬ active d (tfD2 d) d t := by
  intro ha
  have ⟨_, _, hup, hpar⟩ :=
    (active_iff_frontiers (d := d) (tf := tfD2 d) (i := d) (t := t) ht).1 ha
  have hup' := (i_le_omega_iff_threshold (i := d) (t := t) ht hpar).1 hup
  unfold tfD2 at htf
  have hterm : t + 14 ≤ 3 * d := by omega
  have hupper : 3 * d ≤ t + 7 := by omega
  omega

theorem active_false_above_omega {d tf i t : Nat} (ht : 2 ≤ t)
    (hi : omega t < i) : ¬ active d tf i t := by
  intro ha
  have hfront := (active_iff_frontiers ht).1 ha
  omega

/-- At a bottom-rise time `3*j`, its children are outside the active interval
both then and at the intervening stage, so no child cut changes their native
deficits. -/
theorem botRise_children_inactive {d tf j : Nat} (hj : 1 ≤ j) :
    ¬ active d tf (j + 3) (3 * j) ∧
      ¬ active d tf (j + 3) (3 * j + 1) := by
  have hw := omega_botRise_window j hj
  rcases hw with ⟨h0, h1, _⟩
  constructor
  · apply active_false_above_omega (by omega)
    rw [h0]
    omega
  · apply active_false_above_omega (by omega)
    rw [h1]
    omega

/-- Before a bottom-rise time `3*j`, both its sender and its children are
outside the active interval. -/
theorem botRise_history_inactive_before {d tf j s : Nat} (hj : 1 ≤ j)
    (hs : s + 1 ≤ 3 * j) :
    ¬ active d tf (j + 2) s ∧ ¬ active d tf (j + 3) s := by
  by_cases hs0 : s = 0
  · subst s
    simp [active]
  · by_cases hs1 : s = 1
    · subst s
      have hlevel : j + 2 ≠ 1 := by omega
      simp [active, hlevel]
    · have hs2 : 2 ≤ s := by omega
      have hw := omega_le_before_botRise hs
      constructor
      · apply active_false_above_omega hs2
        omega
      · apply active_false_above_omega hs2
        omega

/-- A bottom-rise sender's child level remains outside the active interval
through the rise stage and the following stage. -/
theorem botRise_child_inactive_through_next {d tf j s : Nat}
    (hj : 1 ≤ j) (hs : s ≤ 3 * j + 1) :
    ¬ active d tf (j + 3) s := by
  by_cases hbefore : s < 3 * j
  · exact (botRise_history_inactive_before hj (by omega)).2
  · by_cases heq : s = 3 * j
    · rw [heq]
      exact (botRise_children_inactive hj).1
    · have hnext : s = 3 * j + 1 := by omega
      rw [hnext]
      exact (botRise_children_inactive hj).2

/-- An active non-top-descending sender has an active parent one stage
earlier. The only possible failure of the lower inequality is the exact
top-descending boundary. -/
theorem active_parent_of_not_topDesc {d tf i t : Nat} (ht : 3 ≤ t)
    (hi : 1 ≤ i) (ha : active d tf i t)
    (hnotTop : ¬ (i = alpha d t ∧ alpha d t < alpha d (t + 1))) :
    active d tf (i - 1) (t - 1) := by
  have htNow : 2 ≤ t := by omega
  have htPrev : 2 ≤ t - 1 := by omega
  have ⟨htf, hlow, hup, hpar⟩ := (active_iff_frontiers htNow).1 ha
  have hlowThreshold := (alpha_le_iff_threshold htNow hpar).1 hlow
  have hupThreshold := (i_le_omega_iff_threshold htNow hpar).1 hup
  have hparPrev : (i - 1) % 2 = (t - 1) % 2 := by omega
  apply (active_iff_frontiers (d := d) (tf := tf) (i := i - 1)
    (t := t - 1) htPrev).2
  refine ⟨by omega, ?_, ?_, hparPrev⟩
  · apply (alpha_le_iff_threshold htPrev hparPrev).2
    by_contra hbad
    have heq : 3 * i + 3 * d = 2 * t + 11 := by omega
    obtain ⟨hcur, hnext⟩ := lower_boundary_is_topDesc htNow hpar heq
    exact hnotTop ⟨by omega, by omega⟩
  · apply (i_le_omega_iff_threshold htPrev hparPrev).2
    omega

/-- The unique bottom-rise boundary case in the activity inequalities. -/
def botRiseBoundary (i t : Nat) : Prop := 3 * i = t + 6

/-- Classify a sender by its active boundary and the direction in which that
boundary moves at the next stage. This is the schedule-only part of the D2
update; it does not assert that the corresponding sender is active. -/
def d2ScheduleRole (d i t : Nat) : D2Role :=
  if i = alpha d t then
    if alpha d t < alpha d (t + 1) then .topDesc else .topRise
  else if i = omega t then
    if omega t < omega (t + 1) then .botDesc else .botRise
  else .mid

/-- The role classifier makes `botRise` exactly the one-stage bottom-frontier
drop, hence exactly the level `3*i=t+6`. -/
theorem d2ScheduleRole_botRise_boundary {d i t : Nat} (ht : 2 ≤ t)
    (hrole : d2ScheduleRole d i t = .botRise) : 3 * i = t + 6 := by
  by_cases htop : i = alpha d t
  · by_cases hmove : alpha d t < alpha d (t + 1)
    · simp [d2ScheduleRole, htop, hmove] at hrole
    · simp [d2ScheduleRole, htop, hmove] at hrole
  · by_cases hbot : i = omega t
    · have hrole' :
          (if omega t < omega (t + 1) then D2Role.botDesc else D2Role.botRise) =
            D2Role.botRise := by
        simpa only [d2ScheduleRole, if_neg htop, if_pos hbot] using hrole
      have hnot : ¬ omega t < omega (t + 1) := by
        intro hmove
        rw [if_pos hmove] at hrole'
        cases hrole'
      have hdrop : omega (t + 1) < omega t := by
        have hpar0 := omega_parity t
        have hpar1 := omega_parity (t + 1)
        omega
      exact omega_drop_implies_botRise_boundary ht hbot hdrop
    · simp [d2ScheduleRole, htop, hbot] at hrole

/-- A bottom-rise sender's parent history never overwrites its children:
its parent level is inactive beforehand, uses the `botRise` rule at the rise
stage, and is inactive at the next stage. The child itself is also inactive
throughout this window. -/
theorem botRise_children_parent_trace_native {d : Nat}
    (hd : 7 ≤ d) (j : Nat) (hj : 1 ≤ j)
    [DecidablePred (active d (tfD2 d) (j + 2))]
    [DecidablePred (active d (tfD2 d) (j + 3))]
    (hstage : 3 * j < tfD2 d) (childPort cutDeficit : Nat → Rat) :
    d2ChildDeficitTrace (nativeD2 d (j + 3))
      (fun s => if active d (tfD2 d) (j + 3) s then true else false)
      childPort
      (fun s => if active d (tfD2 d) (j + 2) s then true else false)
      (fun s => d2ScheduleRole d (j + 2) s) cutDeficit (3 * j + 2) =
      nativeD2 d (j + 3) := by
  classical
  have htrace := d2ChildDeficitTrace_eq_of_preserves
    (initial := nativeD2 d (j + 3))
    (childActive := fun s =>
      if active d (tfD2 d) (j + 3) s then true else false)
    (childPort := childPort)
    (parentActive := fun s =>
      if active d (tfD2 d) (j + 2) s then true else false)
    (parentRole := fun s => d2ScheduleRole d (j + 2) s)
    (cutDeficit := cutDeficit) (s := 0) (n := 3 * j + 2) (by
      intro k hk
      have hchildInactive : ¬ (active d (tfD2 d) (j + 3) k) :=
        botRise_child_inactive_through_next (d := d) (tf := tfD2 d)
          (j := j) hj (s := k) (by omega)
      have hchildBool :
          (if active d (tfD2 d) (j + 3) k then true else false) = false := by
        simp [hchildInactive]
      by_cases hk' : k < 3 * j
      · have hinactive := (botRise_history_inactive_before
          (d := d) (tf := tfD2 d) (j := j) (s := k) hj (by omega)).1
        simpa [Nat.zero_add] using (And.intro hchildBool (Or.inl (by simp [hinactive])))
      · by_cases hkeq : k = 3 * j
        · subst k
          have hboundary : 3 * (j + 2) = 3 * j + 6 := by omega
          have hfront := frontiers_separated_before_tf hd (by omega) hstage
          have hwindow := botRise_boundary_frontier (by omega) hboundary
          have hnotTop : j + 2 ≠ alpha d (3 * j) := by
            intro heq
            rw [← heq, hwindow.1] at hfront
            omega
          have hnextEq : omega (3 * j + 1) = j + 1 := by omega
          have hrole : d2ScheduleRole d (j + 2) (3 * j) = .botRise := by
            simp [d2ScheduleRole, hnotTop, hwindow.1, hnextEq]
          simpa [Nat.zero_add] using (And.intro hchildBool (Or.inr hrole))
        · have hkeq : k = 3 * j + 1 := by omega
          subst k
          have hinactive : ¬ (active d (tfD2 d) (j + 2) (3 * j + 1)) := by
            unfold active
            simp only [if_neg (by omega : 3 * j + 1 ≠ 1)]
            omega
          simpa [Nat.zero_add] using (And.intro hchildBool (Or.inl (by simp [hinactive]))))
  simpa using htrace

/-- Immediately before the next ordinary visit, each untouched child of a
`botRise` sender has the exact `c/128` reserve required by the local cut. -/
theorem botRise_parent_trace_child_reserve {d : Nat}
    (hd : 7 ≤ d) (j : Nat) (hj : 1 ≤ j)
    [DecidablePred (active d (tfD2 d) (j + 2))]
    [DecidablePred (active d (tfD2 d) (j + 3))]
    (hstage : 3 * j < tfD2 d) (childPort cutDeficit : Nat → Rat) :
    capacityD2 d (j + 2) (3 * j + 2) ≤
      128 * d2ChildDeficitTrace (nativeD2 d (j + 3))
        (fun s => if active d (tfD2 d) (j + 3) s then true else false)
        childPort
        (fun s => if active d (tfD2 d) (j + 2) s then true else false)
        (fun s => d2ScheduleRole d (j + 2) s) cutDeficit (3 * j + 2) := by
  have hlevel : j + 3 ≤ d := by
    unfold tfD2 at hstage
    omega
  have hboundary : 3 * (j + 2) = 3 * j + 6 := by omega
  have hnative := native_child_eq_later_capacity_div_128 (d := d)
    (i := j + 2) (t := 3 * j) hlevel hboundary
  have htrace := botRise_children_parent_trace_native hd j hj hstage
    childPort cutDeficit
  have hc : capacityD2 d (j + 2) (3 * j + 2) ≠ 0 := by
    have hpos : 0 < capacityD2 d (j + 2) (3 * j + 2) := by
      unfold capacityD2
      exact div_pos (pow_pos (by norm_num : (0 : Rat) < 2) _)
        (pow_pos (by norm_num : (0 : Rat) < 2) _)
    exact ne_of_gt hpos
  have hreserve : capacityD2 d (j + 2) (3 * j + 2) =
      128 * d2ChildDeficitTrace (nativeD2 d (j + 3))
        (fun s => if active d (tfD2 d) (j + 3) s then true else false)
        childPort
        (fun s => if active d (tfD2 d) (j + 2) s then true else false)
        (fun s => d2ScheduleRole d (j + 2) s) cutDeficit (3 * j + 2) := by
   calc
    capacityD2 d (j + 2) (3 * j + 2) =
        128 * (capacityD2 d (j + 2) (3 * j + 2) / 128) := by
          field_simp [hc]
    _ = 128 * nativeD2 d (j + 3) := by rw [← hnative]
    _ = 128 * d2ChildDeficitTrace (nativeD2 d (j + 3))
        (fun s => if active d (tfD2 d) (j + 3) s then true else false)
        childPort
        (fun s => if active d (tfD2 d) (j + 2) s then true else false)
        (fun s => d2ScheduleRole d (j + 2) s) cutDeficit (3 * j + 2) := by
          exact congrArg (fun x : Rat => 128 * x) htrace.symm
  rw [hreserve]

/-- Conservation turns the untouched native children into the exceptional
`gOld + rhoOld = 1/256` identity. Child deficits follow their own activity
and the parent-overwrite rule. -/
theorem botRise_native_split_of_parent_trace {d : Nat}
    (hd : 7 ≤ d) (j : Nat) (hj : 1 ≤ j)
    [DecidablePred (active d (tfD2 d) (j + 2))]
    [DecidablePred (active d (tfD2 d) (j + 3))]
    (hstage : 3 * j < tfD2 d) {a G : Rat}
    (childPort cutDeficit : Nat → Rat)
    (hconserve : a + G = Finset.univ.sum fun _ : Fin 8 =>
      d2ChildDeficitTrace (nativeD2 d (j + 3))
        (fun s => if active d (tfD2 d) (j + 3) s then true else false)
        childPort
        (fun s => if active d (tfD2 d) (j + 2) s then true else false)
        (fun s => d2ScheduleRole d (j + 2) s) cutDeficit (3 * j + 2)) :
    G / capacityD2 d (j + 2) (3 * j) +
      a / capacityD2 d (j + 2) (3 * j) = 1 / 256 := by
  have hlevel : j + 2 < d := by
    unfold tfD2 at hstage
    omega
  have htrace := botRise_children_parent_trace_native hd j hj hstage
    childPort cutDeficit
  have htrace' : d2ChildDeficitTrace (nativeD2 d (j + 3))
      (fun s => decide (active d (tfD2 d) (j + 3) s)) childPort
      (fun s => decide (active d (tfD2 d) (j + 2) s))
      (fun s => d2ScheduleRole d (j + 2) s) cutDeficit (3 * j + 2) =
      nativeD2 d (j + 3) := by simpa using htrace
  have hsum : (Finset.univ.sum fun _ : Fin 8 =>
      d2ChildDeficitTrace (nativeD2 d (j + 3))
        (fun s => if active d (tfD2 d) (j + 3) s then true else false)
        childPort
        (fun s => if active d (tfD2 d) (j + 2) s then true else false)
        (fun s => d2ScheduleRole d (j + 2) s) cutDeficit (3 * j + 2)) =
      nativeD2 d (j + 2) := by
    calc
      (Finset.univ.sum fun _ : Fin 8 =>
          d2ChildDeficitTrace (nativeD2 d (j + 3))
            (fun s => if active d (tfD2 d) (j + 3) s then true else false)
            childPort
            (fun s => if active d (tfD2 d) (j + 2) s then true else false)
            (fun s => d2ScheduleRole d (j + 2) s) cutDeficit (3 * j + 2)) =
          8 * nativeD2 d (j + 3) := by simp [htrace']
      _ = nativeD2 d (j + 2) := by
        symm
        exact nativeD2_succ_level hlevel
  have hboundary : 3 * (j + 2) = 3 * j + 6 := by omega
  have hnative := native_eq_capacity_div_256 (d := d) (i := j + 2)
    (t := 3 * j) (by omega) hboundary
  have hcap : capacityD2 d (j + 2) (3 * j) ≠ 0 := by
    have hpos : 0 < capacityD2 d (j + 2) (3 * j) := by
      unfold capacityD2
      exact div_pos (pow_pos (by norm_num : (0 : Rat) < 2) _)
        (pow_pos (by norm_num : (0 : Rat) < 2) _)
    exact ne_of_gt hpos
  calc
    G / capacityD2 d (j + 2) (3 * j) +
        a / capacityD2 d (j + 2) (3 * j) =
        (G + a) / capacityD2 d (j + 2) (3 * j) := by ring
    _ = nativeD2 d (j + 2) / capacityD2 d (j + 2) (3 * j) := by
      rw [add_comm G a, hconserve, hsum]
    _ = 1 / 256 := by rw [hnative]; field_simp [hcap]

/-- The untouched child state supplies the exact two-step allocation identity
across a `botRise` predecessor, using conservation at both visits. -/
theorem botRise_parent_trace_two_step_identity {d : Nat}
    (hd : 7 ≤ d) (j : Nat) (hj : 1 ≤ j)
    [DecidablePred (active d (tfD2 d) (j + 2))]
    [DecidablePred (active d (tfD2 d) (j + 3))]
    (hstage : 3 * j + 2 < tfD2 d)
    {aOld GOld aNow GNow : Rat} (childPort cutDeficit : Nat → Rat)
    (hOldConserve : aOld + GOld = Finset.univ.sum fun _ : Fin 8 =>
      d2ChildDeficitTrace (nativeD2 d (j + 3))
        (fun s => if active d (tfD2 d) (j + 3) s then true else false)
        childPort
        (fun s => if active d (tfD2 d) (j + 2) s then true else false)
        (fun s => d2ScheduleRole d (j + 2) s) cutDeficit (3 * j + 2))
    (hNowConserve : aNow + GNow = Finset.univ.sum fun _ : Fin 8 =>
      d2ChildDeficitTrace (nativeD2 d (j + 3))
        (fun s => if active d (tfD2 d) (j + 3) s then true else false)
        childPort
        (fun s => if active d (tfD2 d) (j + 2) s then true else false)
        (fun s => d2ScheduleRole d (j + 2) s) cutDeficit (3 * j + 2)) :
    aNow / capacityD2 d (j + 2) (3 * j + 2) =
      16 * (GOld / capacityD2 d (j + 2) (3 * j)) +
      16 * (aOld / capacityD2 d (j + 2) (3 * j)) -
      GNow / capacityD2 d (j + 2) (3 * j + 2) := by
  have hOldSplit := botRise_native_split_of_parent_trace
    (a := aOld) (G := GOld) hd j hj (by omega) childPort cutDeficit hOldConserve
  have hsame : aNow + GNow = aOld + GOld := by
    calc
      aNow + GNow = Finset.univ.sum fun _ : Fin 8 =>
          d2ChildDeficitTrace (nativeD2 d (j + 3))
            (fun s => if active d (tfD2 d) (j + 3) s then true else false)
            childPort
            (fun s => if active d (tfD2 d) (j + 2) s then true else false)
            (fun s => d2ScheduleRole d (j + 2) s) cutDeficit (3 * j + 2) := hNowConserve
      _ = aOld + GOld := hOldConserve.symm
  have hcap : capacityD2 d (j + 2) (3 * j) =
      16 * capacityD2 d (j + 2) (3 * j + 2) := by
    have h := capacityD2_two_stage_ratio (d := d) (i := j + 2)
      (t := 3 * j + 2) (by omega)
    simpa using h
  have hc : capacityD2 d (j + 2) (3 * j + 2) ≠ 0 := by
    have hpos : 0 < capacityD2 d (j + 2) (3 * j + 2) := by
      unfold capacityD2
      exact div_pos (pow_pos (by norm_num : (0 : Rat) < 2) _)
        (pow_pos (by norm_num : (0 : Rat) < 2) _)
    exact ne_of_gt hpos
  have hOldRatio : (aOld + GOld) / capacityD2 d (j + 2) (3 * j) = 1 / 256 := by
    calc
      (aOld + GOld) / capacityD2 d (j + 2) (3 * j) =
          aOld / capacityD2 d (j + 2) (3 * j) +
            GOld / capacityD2 d (j + 2) (3 * j) := by ring
      _ = 1 / 256 := by linarith [hOldSplit]
  have hCurrentRatio : (aOld + GOld) /
      capacityD2 d (j + 2) (3 * j + 2) = 1 / 16 := by
    rw [hcap] at hOldRatio
    field_simp [hc] at hOldRatio
    rw [div_eq_iff hc]
    nlinarith
  have hcurrentsum :
      aNow / capacityD2 d (j + 2) (3 * j + 2) +
        GNow / capacityD2 d (j + 2) (3 * j + 2) = 1 / 16 := by
    calc
      aNow / capacityD2 d (j + 2) (3 * j + 2) +
          GNow / capacityD2 d (j + 2) (3 * j + 2) =
          (aNow + GNow) / capacityD2 d (j + 2) (3 * j + 2) := by ring
      _ = (aOld + GOld) / capacityD2 d (j + 2) (3 * j + 2) := by rw [hsame]
      _ = 1 / 16 := hCurrentRatio
  calc
    aNow / capacityD2 d (j + 2) (3 * j + 2) =
        (aNow / capacityD2 d (j + 2) (3 * j + 2) +
          GNow / capacityD2 d (j + 2) (3 * j + 2)) -
          GNow / capacityD2 d (j + 2) (3 * j + 2) := by ring
    _ = 1 / 16 - GNow / capacityD2 d (j + 2) (3 * j + 2) := by rw [hcurrentsum]
    _ = 16 * (GOld / capacityD2 d (j + 2) (3 * j)) +
        16 * (aOld / capacityD2 d (j + 2) (3 * j)) -
        GNow / capacityD2 d (j + 2) (3 * j + 2) := by linarith

/-- The schedule-derived native child reserve and exact two-visit
conservation identity rule out crossing at the sender two stages after
`botRise`, given the current normalized deficit and port caps. -/
theorem botRise_parent_trace_forces_noncrossing {d : Nat}
    (hd : 7 ≤ d) (j : Nat) (hj : 1 ≤ j)
    [DecidablePred (active d (tfD2 d) (j + 2))]
    [DecidablePred (active d (tfD2 d) (j + 3))]
    (hstage : 3 * j + 2 < tfD2 d)
    {aOld GOld aNow GNow piNow rhoNow : Rat}
    (childPort cutDeficit : Nat → Rat)
    (hOldConserve : aOld + GOld = Finset.univ.sum fun _ : Fin 8 =>
      d2ChildDeficitTrace (nativeD2 d (j + 3))
        (fun s => if active d (tfD2 d) (j + 3) s then true else false)
        childPort
        (fun s => if active d (tfD2 d) (j + 2) s then true else false)
        (fun s => d2ScheduleRole d (j + 2) s) cutDeficit (3 * j + 2))
    (hNowConserve : aNow + GNow = Finset.univ.sum fun _ : Fin 8 =>
      d2ChildDeficitTrace (nativeD2 d (j + 3))
        (fun s => if active d (tfD2 d) (j + 3) s then true else false)
        childPort
        (fun s => if active d (tfD2 d) (j + 2) s then true else false)
        (fun s => d2ScheduleRole d (j + 2) s) cutDeficit (3 * j + 2))
    (hgNow : GNow / capacityD2 d (j + 2) (3 * j + 2) ≤ 15 / 256)
    (hrhoNow : rhoNow ≤ 1 / 256)
    (hpiNow : piNow / capacityD2 d (j + 2) (3 * j + 2) = rhoNow) :
    piNow ≤ aNow := by
  have hnative := botRise_native_split_of_parent_trace
    (a := aOld) (G := GOld) hd j hj (by omega) childPort cutDeficit
    hOldConserve
  have hid := botRise_parent_trace_two_step_identity hd j hj hstage
    (aOld := aOld) (GOld := GOld) (aNow := aNow) (GNow := GNow)
    childPort cutDeficit hOldConserve hNowConserve
  have hc : 0 < capacityD2 d (j + 2) (3 * j + 2) := by
    unfold capacityD2
    exact div_pos (pow_pos (by norm_num : (0 : Rat) < 2) _)
      (pow_pos (by norm_num : (0 : Rat) < 2) _)
  exact botRise_two_step_forces_noncrossing hc hid hnative hgNow hrhoNow hpiNow

/-- Native allocation suffices for every role once roles are assigned by the
closed-form schedule: the exceptional boundary is derived from the role. -/
theorem d2ScheduleRole_port_bound_of_native {d i t : Nat} {a : Rat}
    (ht : 2 ≤ t) (hi : i ≤ d) (ha : a ≤ nativeD2 d i) :
    d2PortSize (d2ScheduleRole d i t) a (capacityD2 d i t) ≤
      capacityD2 d i t / 256 := by
  apply d2_role_port_bound_of_native hi
  · intro hrole
    exact d2ScheduleRole_botRise_boundary ht hrole
  · exact ha

/-- Child-native bounds and the exact D2 allocation equation imply the
role-specific `pi/c<=1/256` bound for the schedule-defined sender. -/
theorem d2ScheduleRole_port_bound_of_flow_children
    {d i t a G : Nat} (childDeficit : Fin 8 → Nat)
    (ht : 2 ≤ t) (hi : i < d)
    (halloc : a = (Finset.univ.sum childDeficit) - G)
    (hchild : ∀ j, childDeficit j ≤ 8 ^ (d - i - 1)) :
    d2PortSize (d2ScheduleRole d i t) (a : Rat) (capacityD2 d i t) ≤
      capacityD2 d i t / 256 := by
  have ha := allocation_le_native_of_child_native childDeficit hi halloc hchild
  exact d2ScheduleRole_port_bound_of_native ht hi.le ha

/-- A non-top-descending active sender has its intermediate child strictly
below the child's top frontier. Thus the child cannot have either top role. -/
theorem active_child_below_top_frontier {d tf i t : Nat} (ht : 3 ≤ t)
    (ha : active d tf i t)
    (hrole : d2ScheduleRole d i t ≠ .topDesc) :
    alpha d (t - 1) ≤ i := by
  have hfront := (active_iff_frontiers (d := d) (tf := tf) (i := i)
    (t := t) (by omega)).1 ha
  have hprevStep := alpha_prev_le_succ (d := d) ht
  by_cases heq : i = alpha d t
  · have hnotRise : ¬ alpha d t < alpha d (t + 1) := by
      intro hmove
      apply hrole
      simp [d2ScheduleRole, heq, hmove]
    have hmono := alpha_mono_same_parity (d := d) (by omega : 2 ≤ t - 1)
      (by omega : t - 1 ≤ t + 1) (by omega)
    omega
  · have hnow : alpha d t ≤ i := hfront.2.1
    omega

/-- In the two-step identity's ordinary regime, the intermediate child is
never classified as a top-frontier role. -/
theorem schedule_child_role_not_top {d tf i t : Nat} (ht : 3 ≤ t)
    (ha : active d tf i t)
    (hrole : d2ScheduleRole d i t ≠ .topDesc) :
    d2ScheduleRole d (i + 1) (t - 1) ≠ .topDesc ∧
      d2ScheduleRole d (i + 1) (t - 1) ≠ .topRise := by
  have htop := active_child_below_top_frontier ht ha hrole
  have hneq : i + 1 ≠ alpha d (t - 1) := by omega
  constructor <;> intro hbad
  · unfold d2ScheduleRole at hbad
    simp only [if_neg hneq] at hbad
    split_ifs at hbad
  · unfold d2ScheduleRole at hbad
    simp only [if_neg hneq] at hbad
    split_ifs at hbad

/-- Hence the schedule's intermediate-child role is one of the three cases
appearing in the ordinary/exceptional split of the sender-factor argument. -/
theorem schedule_child_role_cases {d tf i t : Nat} (ht : 3 ≤ t)
    (ha : active d tf i t)
    (hrole : d2ScheduleRole d i t ≠ .topDesc) :
    d2ScheduleRole d (i + 1) (t - 1) = .mid ∨
      d2ScheduleRole d (i + 1) (t - 1) = .botDesc ∨
      d2ScheduleRole d (i + 1) (t - 1) = .botRise := by
  have hnot := schedule_child_role_not_top ht ha hrole
  cases hchild : d2ScheduleRole d (i + 1) (t - 1) with
  | topDesc => exact False.elim (hnot.1 hchild)
  | topRise => exact False.elim (hnot.2 hchild)
  | mid => exact Or.inl rfl
  | botDesc => exact Or.inr (Or.inl rfl)
  | botRise => exact Or.inr (Or.inr rfl)

/-- If the intermediate child is `botRise`, the schedule forces both the
current sender and its two-stage predecessor to be `botDesc`. This is the
exceptional role branch in the `279/256` two-step factor. -/
theorem botRise_child_forces_desc_roles {d i t : Nat} (hd : 7 ≤ d)
    (ht : 3 ≤ t) (htf : t < tfD2 d)
    (hchild : d2ScheduleRole d (i + 1) (t - 1) = .botRise) :
    d2ScheduleRole d i t = .botDesc ∧
      d2ScheduleRole d i (t - 2) = .botDesc := by
  have hboundary := d2ScheduleRole_botRise_boundary (by omega) hchild
  have hq : 1 ≤ i - 1 := by omega
  have htform : t = 3 * (i - 1) + 1 := by omega
  have hprevform : t - 2 = 3 * (i - 2) + 2 := by omega
  have hcurOmega : omega t = i := by
    rw [htform, omega_three_mul_add_one]
    omega
  have hnextOmega : omega (t + 1) = i + 1 := by
    rw [show t + 1 = 3 * (i - 1) + 2 by omega,
      omega_three_mul_add_two]
    omega
  have hprevOmega : omega (t - 2) = i := by
    rw [hprevform, omega_three_mul_add_two]
    omega
  have hprevNextOmega : omega (t - 1) = i + 1 := by
    rw [show t - 1 = 3 * (i - 1) by omega,
      omega_three_mul (i - 1) hq]
    omega
  have hcurTop : i ≠ alpha d t := by
    have hgap := alpha_gap_before_tf hd (by omega) htf
    have hquot : (t + 4) / 3 = i := by rw [htform]; omega
    omega
  have hprevTop : i ≠ alpha d (t - 2) := by
    have hgap := alpha_gap_before_tf hd (by omega) (by omega : t - 2 < tfD2 d)
    have hquot : (t - 2 + 4) / 3 = i := by rw [hprevform]; omega
    omega
  constructor
  · simp [d2ScheduleRole, hcurTop, hcurOmega, hnextOmega]
  · have hprevNextOmega' : omega (t - 2 + 1) = i + 1 := by
      rw [show t - 2 + 1 = 3 * (i - 1) by omega,
        omega_three_mul (i - 1) hq]
      omega
    simp [d2ScheduleRole, hprevTop, hprevOmega, hprevNextOmega']

/-- The active child cannot have a `botRise` parent: the parent boundary would
put the child exactly at its excluded upper frontier. -/
theorem active_parent_not_botRise {d tf i t : Nat} (ht : 3 ≤ t)
    (hi : 1 ≤ i) (ha : active d tf i t) :
    ¬ botRiseBoundary (i - 1) (t - 1) := by
  have ⟨_, _, _, hpar⟩ := (active_iff_frontiers (d := d) (tf := tf)
    (i := i) (t := t) (by omega)).1 ha
  have hupper := (i_le_omega_iff_threshold (i := i) (t := t) (by omega) hpar).1
    ((active_iff_frontiers (d := d) (tf := tf) (i := i) (t := t)
      (by omega)).1 ha).2.2.1
  intro hb
  unfold botRiseBoundary at hb
  omega

/-- Every active child that is not top-descending has an active parent; the
parent is either top-descending or one of the three ordinary cut roles. -/
theorem active_nonTop_parent_role_cases {d tf i t : Nat}
    (ht : 3 ≤ t) (hi : 1 ≤ i) (ha : active d tf i t)
    (hrole : d2ScheduleRole d i t ≠ .topDesc) :
    active d tf (i - 1) (t - 1) ∧
      (d2ScheduleRole d (i - 1) (t - 1) = .topDesc ∨
       d2ScheduleRole d (i - 1) (t - 1) = .topRise ∨
       d2ScheduleRole d (i - 1) (t - 1) = .mid ∨
       d2ScheduleRole d (i - 1) (t - 1) = .botDesc) := by
  have hnotTop : ¬ (i = alpha d t ∧ alpha d t < alpha d (t + 1)) := by
    intro h
    apply hrole
    simp [d2ScheduleRole, h.1, h.2]
  have hparent := active_parent_of_not_topDesc ht hi ha hnotTop
  have hnotBot := active_parent_not_botRise ht hi ha
  refine ⟨hparent, ?_⟩
  cases hparentRole : d2ScheduleRole d (i - 1) (t - 1) with
  | topDesc => exact Or.inl rfl
  | topRise => exact Or.inr (Or.inl rfl)
  | mid => exact Or.inr (Or.inr (Or.inl rfl))
  | botDesc => exact Or.inr (Or.inr (Or.inr rfl))
  | botRise =>
      have hboundary := d2ScheduleRole_botRise_boundary (by omega) hparentRole
      exact False.elim (hnotBot hboundary)

/-- Local child `g` bound for a parent whose schedule role is either
top-descending (which clears the child) or an ordinary cut role. -/
theorem d2_parent_child_g_bound_of_role_cases {role : D2Role}
    (hrole : role = .topDesc ∨ role = .topRise ∨ role = .mid ∨ role = .botDesc)
    {a G total low high pi half c childG : Nat}
    (size pos : Fin 8 → Nat) (j : Fin 8)
    (hchild : childG = d2LocalChildDeficitUpdate role (pos j) (size j)
      (low + half) (total - high - half))
    (hbalance : low + high = G) (hconserve : a + G = total)
    (hpiAlloc : pi ≤ a) (heven : pi = 2 * half)
    (hG : 512 * G ≤ c) (hlow : low ≤ G) (hhigh : high ≤ G)
    (hpi : 256 * pi ≤ c) (hleftReserve : c ≤ 128 * size 0)
    (hrightReserve : c ≤ 128 * size 7) (hstart : pos 0 = 0)
    (hcontig : ∀ k : Nat, (hk : k < 7) →
      pos ⟨k + 1, by omega⟩ = pos ⟨k, by omega⟩ + size ⟨k, by omega⟩)
    (htotal : pos 7 + size 7 = total) :
    512 * childG ≤ 2 * c := by
  rcases hrole with htop | htopRise | hmid | hbotDesc
  · subst role
    simp [d2LocalChildDeficitUpdate] at hchild
    omega
  · have hregular : role = .topRise ∨ role = .mid ∨ role = .botDesc :=
      Or.inl htopRise
    have hbound := d2_regular_update_preserves_child_g_bound hregular size pos
      hbalance hconserve hpiAlloc heven hG hlow hhigh hpi hleftReserve
      hrightReserve hstart hcontig htotal j
    rw [hchild]
    exact hbound
  · have hregular : role = .topRise ∨ role = .mid ∨ role = .botDesc :=
      Or.inr (Or.inl hmid)
    have hbound := d2_regular_update_preserves_child_g_bound hregular size pos
      hbalance hconserve hpiAlloc heven hG hlow hhigh hpi hleftReserve
      hrightReserve hstart hcontig htotal j
    rw [hchild]
    exact hbound
  · have hregular : role = .topRise ∨ role = .mid ∨ role = .botDesc :=
      Or.inr (Or.inr hbotDesc)
    have hbound := d2_regular_update_preserves_child_g_bound hregular size pos
      hbalance hconserve hpiAlloc heven hG hlow hhigh hpi hleftReserve
      hrightReserve hstart hcontig htotal j
    rw [hchild]
    exact hbound

/-- One-stage schedule-to-state propagation: every active, non-top-descending
child gets the `1/512` normalized deficit cap from its active parent, assuming
the parent's local reserve and sender bounds. -/
theorem active_nonTop_child_g_bound_step {d tf i t : Nat}
    (ht : 3 ≤ t) (hi : 1 ≤ i) (ha : active d tf i t)
    (hrole : d2ScheduleRole d i t ≠ .topDesc)
    {a G total low high pi half c childG : Nat}
    (size pos : Fin 8 → Nat) (j : Fin 8)
    (hchild : childG = d2LocalChildDeficitUpdate
      (d2ScheduleRole d (i - 1) (t - 1)) (pos j) (size j)
      (low + half) (total - high - half))
    (hbalance : low + high = G) (hconserve : a + G = total)
    (hpiAlloc : pi ≤ a) (heven : pi = 2 * half)
    (hG : 512 * G ≤ c) (hlow : low ≤ G) (hhigh : high ≤ G)
    (hpi : 256 * pi ≤ c) (hleftReserve : c ≤ 128 * size 0)
    (hrightReserve : c ≤ 128 * size 7) (hstart : pos 0 = 0)
    (hcontig : ∀ k : Nat, (hk : k < 7) →
      pos ⟨k + 1, by omega⟩ = pos ⟨k, by omega⟩ + size ⟨k, by omega⟩)
    (htotal : pos 7 + size 7 = total) :
    512 * childG ≤ 2 * c := by
  have hcases := active_nonTop_parent_role_cases ht hi ha hrole
  exact d2_parent_child_g_bound_of_role_cases hcases.2 size pos j hchild hbalance
    hconserve hpiAlloc heven hG hlow hhigh hpi hleftReserve hrightReserve
    hstart hcontig htotal

/-- Moving a stage back by two preserves activity unless the current sender
is the bot-rise boundary (which ordinary positive-up senders exclude). -/
theorem active_prev_two_of_not_botRise {d tf i t : Nat}
    (ht : 3 ≤ t) (ha : active d tf i t)
    (hbr : ¬ botRiseBoundary i t) : active d tf i (t - 2) := by
  by_cases ht3 : t = 3
  · subst t
    have hparts :
        2 ≤ 3 ∧ 3 ≤ tf ∧ i % 2 = 3 % 2 ∧
          3 * i + 3 * d ≥ 2 * 3 + 11 ∧ 3 * i < 3 + 8 := by
      simpa [active] using ha
    have hi : i = 1 := by
      unfold botRiseBoundary at hbr
      rcases hparts with ⟨_, _, hpar, _, htop⟩
      omega
    simp [active, hi]
  · have ht_ne_one : t ≠ 1 := by omega
    have hs_ne_one : t - 2 ≠ 1 := by omega
    unfold active at *
    simp only [if_neg ht_ne_one, if_neg hs_ne_one] at ha ⊢
    rcases ha with ⟨htlo, hthi, hpar, hbottom, htop⟩
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · omega
    · omega
    · unfold botRiseBoundary at hbr
      omega

/-- A regular active sender before termination is active again two stages
earlier. That predecessor cannot be `topDesc`, so the reserve induction has
only the ordinary-update and `botRise` cases. -/
theorem active_regular_prev_two_role_cases {d i t : Nat}
    (hd : 7 ≤ d) (ht : 4 ≤ t) (htf : t < tfD2 d)
    (ha : active d (tfD2 d) i t)
    (hrole : d2ScheduleRole d i t = .topRise ∨
      d2ScheduleRole d i t = .mid ∨ d2ScheduleRole d i t = .botDesc) :
    active d (tfD2 d) i (t - 2) ∧
      (d2ScheduleRole d i (t - 2) = .topRise ∨
       d2ScheduleRole d i (t - 2) = .mid ∨
       d2ScheduleRole d i (t - 2) = .botDesc ∨
       d2ScheduleRole d i (t - 2) = .botRise) := by
  have hnotTop : d2ScheduleRole d i t ≠ .topDesc := by
    intro h
    rcases hrole with h | h | h <;> simp_all
  have hnotBotRole : d2ScheduleRole d i t ≠ .botRise := by
    intro hb
    rcases hrole with h | h | h <;> rw [hb] at h <;> cases h
  have hnotBR : ¬ botRiseBoundary i t := by
    intro hb
    have hwindow := botRise_boundary_frontier (by omega) hb
    have hsep := frontiers_separated_before_tf hd (by omega) htf
    have hnotTopLevel : i ≠ alpha d t := by
      intro heq
      rw [← heq, hwindow.1] at hsep
      omega
    have hnotAlphaOmega : omega t ≠ alpha d t := by
      intro heq
      exact hnotTopLevel (hwindow.1.symm.trans heq)
    have hnextLt : omega (t + 1) < omega t := by
      rw [hwindow.1]
      omega
    have hnotMove : ¬ omega t < omega (t + 1) := not_lt_of_gt hnextLt
    have hbot : d2ScheduleRole d i t = .botRise := by
      simp [d2ScheduleRole, hwindow.1.symm, hnotAlphaOmega, hnotMove]
    exact hnotBotRole hbot
  have hprev := active_prev_two_of_not_botRise
    (d := d) (tf := tfD2 d) (i := i) (by omega) ha hnotBR
  have hnotPrevTop : d2ScheduleRole d i (t - 2) ≠ .topDesc := by
    intro hprevRole
    have hboundary : i = alpha d (t - 2) ∧
        alpha d (t - 2) < alpha d (t - 2 + 1) := by
      by_cases heq : i = alpha d (t - 2)
      · have hprevRole' :
            (if alpha d (t - 2) < alpha d (t - 2 + 1)
              then D2Role.topDesc else D2Role.topRise) = D2Role.topDesc := by
          simpa [d2ScheduleRole, heq] using hprevRole
        have hmove : alpha d (t - 2) < alpha d (t - 2 + 1) := by
          by_cases hm : alpha d (t - 2) < alpha d (t - 2 + 1)
          · exact hm
          · simp [hm] at hprevRole'
        exact ⟨heq, hmove⟩
      · simp only [d2ScheduleRole, if_neg heq] at hprevRole
        split_ifs at hprevRole
    have hnotCurrent : i ≠ alpha d t ∨ alpha d (t + 1) ≤ i := by
      by_cases heq : i = alpha d t
      · right
        have hmove : ¬ alpha d t < alpha d (t + 1) := by
          intro hm
          apply hnotTop
          simp [d2ScheduleRole, heq, hm]
        omega
      · exact Or.inl heq
    have hprevRise : alpha d (t - 2) < alpha d (t - 1) := by
      simpa [show t - 2 + 1 = t - 1 by omega] using hboundary.2
    exact topDesc_predecessor_excluded ht hboundary.1 hprevRise
      ((active_iff_frontiers (by omega)).1 ha).2.1 hnotCurrent
  refine ⟨hprev, ?_⟩
  cases hpr : d2ScheduleRole d i (t - 2) with
  | topDesc => exact False.elim (hnotPrevTop hpr)
  | topRise => exact Or.inl rfl
  | mid => exact Or.inr (Or.inl rfl)
  | botDesc => exact Or.inr (Or.inr (Or.inl rfl))
  | botRise => exact Or.inr (Or.inr (Or.inr rfl))

/-- Summing uniform intermediate-child quota bounds gives exactly the two
mass cases required by the corrected two-step sender-factor estimate. -/
theorem d2_child_quota_sum_role_split {rhoOld : Rat}
    (childRho : Fin 8 → Rat) {childRole : D2Role}
    (hrole : childRole = .mid ∨ childRole = .botDesc ∨
      childRole = .botRise)
    (hold : rhoOld ≤ 1 / 256)
    (holdBot : childRole = .botRise → rhoOld ≤ 15 / 4096)
    (hregular : childRole = .mid ∨ childRole = .botDesc →
      ∀ j, childRho j ≤ 15 / 4096)
    (hbot : childRole = .botRise → ∀ j, childRho j ≤ 1 / 256) :
    (rhoOld ≤ 15 / 4096 ∧
      32 * (Finset.univ.sum childRho) ≤ 1) ∨
    (rhoOld ≤ 1 / 256 ∧
      32 * (Finset.univ.sum childRho) ≤ 15 / 16) := by
  rcases hrole with hmid | hdesc | hbotRole
  · right
    constructor
    · exact hold
    · have hsum := Finset.sum_le_sum (s := Finset.univ)
        (fun j _ => hregular (Or.inl hmid) j)
      have hconst : (Finset.univ.sum fun _ : Fin 8 => (15 / 4096 : Rat)) =
          8 * (15 / 4096 : Rat) := by norm_num
      rw [hconst] at hsum
      nlinarith
  · right
    constructor
    · exact hold
    · have hsum := Finset.sum_le_sum (s := Finset.univ)
        (fun j _ => hregular (Or.inr hdesc) j)
      have hconst : (Finset.univ.sum fun _ : Fin 8 => (15 / 4096 : Rat)) =
          8 * (15 / 4096 : Rat) := by norm_num
      rw [hconst] at hsum
      nlinarith
  · left
    constructor
    · exact holdBot hbotRole
    · have hsum := Finset.sum_le_sum (s := Finset.univ)
        (fun j _ => hbot hbotRole j)
      have hconst : (Finset.univ.sum fun _ : Fin 8 => (1 / 256 : Rat)) =
          8 * (1 / 256 : Rat) := by norm_num
      rw [hconst] at hsum
      nlinarith

/-- The closed-form schedule splits the eight intermediate child quotas into
the two cases consumed by the `279/256` factor lemma. It assumes only that
each child allocation is bounded by its native subtree size. -/
theorem d2_schedule_two_step_quota_roles {d i t : Nat}
    (hd : 7 ≤ d) (hi : i < d) (ht : 4 ≤ t)
    (htf : t < tfD2 d)
    (ha : active d (tfD2 d) i t)
    (hrole : d2ScheduleRole d i t = .topRise ∨
      d2ScheduleRole d i t = .mid ∨
      d2ScheduleRole d i t = .botDesc)
    {aOld : Rat} (haOld : aOld ≤ nativeD2 d i)
    (childAlloc : Fin 8 → Rat)
    (hchildAlloc : ∀ j, childAlloc j ≤ nativeD2 d (i + 1))
    (rhoOld : Rat) (childRho : Fin 8 → Rat)
    (hOldDef : rhoOld = d2PortSize (d2ScheduleRole d i (t - 2)) aOld
      (capacityD2 d i (t - 2)) / capacityD2 d i (t - 2))
    (hChildDef : ∀ j, childRho j =
      d2PortSize (d2ScheduleRole d (i + 1) (t - 1)) (childAlloc j)
        (capacityD2 d (i + 1) (t - 1)) /
      capacityD2 d (i + 1) (t - 1)) :
    (rhoOld ≤ 15 / 4096 ∧
      32 * (Finset.univ.sum childRho) ≤ 1) ∨
    (rhoOld ≤ 1 / 256 ∧
      32 * (Finset.univ.sum childRho) ≤ 15 / 16) := by
  have hnotTop : d2ScheduleRole d i t ≠ .topDesc := by
    intro h
    rcases hrole with h | h | h <;> simp_all
  have hchildRoles := schedule_child_role_cases (by omega) ha hnotTop
  have holdcap : 0 < capacityD2 d i (t - 2) := by
    unfold capacityD2
    exact div_pos (pow_pos (by norm_num : (0 : Rat) < 2) _)
      (pow_pos (by norm_num : (0 : Rat) < 2) _)
  have hchildcap : 0 < capacityD2 d (i + 1) (t - 1) := by
    unfold capacityD2
    exact div_pos (pow_pos (by norm_num : (0 : Rat) < 2) _)
      (pow_pos (by norm_num : (0 : Rat) < 2) _)
  have holdport := d2ScheduleRole_port_bound_of_native
    (d := d) (i := i) (t := t - 2) (a := aOld) (by omega) hi.le haOld
  have hold : rhoOld ≤ 1 / 256 := by
    rw [hOldDef]
    apply (div_le_iff₀ holdcap).2
    nlinarith [holdport]
  have hregular :
      d2ScheduleRole d (i + 1) (t - 1) = .mid ∨
      d2ScheduleRole d (i + 1) (t - 1) = .botDesc →
      ∀ j, childRho j ≤ 15 / 4096 := by
    intro hreg j
    have heq : childRho j = 15 / 4096 := by
      rw [hChildDef j]
      rcases hreg with hm | hb
      · rw [hm]
        unfold d2PortSize
        field_simp [ne_of_gt hchildcap]
      · rw [hb]
        unfold d2PortSize
        field_simp [ne_of_gt hchildcap]
    rw [heq]
  have hbot :
      d2ScheduleRole d (i + 1) (t - 1) = .botRise →
      ∀ j, childRho j ≤ 1 / 256 := by
    intro hb j
    have hport := d2ScheduleRole_port_bound_of_native
      (d := d) (i := i + 1) (t := t - 1) (a := childAlloc j) (by omega) (by omega)
      (hchildAlloc j)
    rw [hChildDef j]
    apply (div_le_iff₀ hchildcap).2
    nlinarith [hport]
  have holdBot :
      d2ScheduleRole d (i + 1) (t - 1) = .botRise →
      rhoOld ≤ 15 / 4096 := by
    intro hbr
    have hforced := botRise_child_forces_desc_roles hd (by omega) htf hbr
    rw [hOldDef, hforced.2]
    unfold d2PortSize
    field_simp [ne_of_gt holdcap]
    norm_num
  exact d2_child_quota_sum_role_split childRho hchildRoles hold holdBot
    hregular hbot

/-- The schedule-derived child-quota split closes the corrected sender-factor
bound once the exact two-step conservation identity and deficit caps hold. -/
theorem d2_schedule_two_step_sender_factor_279 {d i t : Nat}
    (hd : 7 ≤ d) (hi : i < d) (ht : 4 ≤ t)
    (htf : t < tfD2 d)
    (ha : active d (tfD2 d) i t)
    (hrole : d2ScheduleRole d i t = .topRise ∨
      d2ScheduleRole d i t = .mid ∨
      d2ScheduleRole d i t = .botDesc)
    {aOld : Rat} (haOld : aOld ≤ nativeD2 d i)
    (childAlloc : Fin 8 → Rat)
    (hchildAlloc : ∀ j, childAlloc j ≤ nativeD2 d (i + 1))
    {a c gOld gNow rhoOld : Rat} (childRho : Fin 8 → Rat)
    (hOldDef : rhoOld = d2PortSize (d2ScheduleRole d i (t - 2)) aOld
      (capacityD2 d i (t - 2)) / capacityD2 d i (t - 2))
    (hChildDef : ∀ j, childRho j =
      d2PortSize (d2ScheduleRole d (i + 1) (t - 1)) (childAlloc j)
        (capacityD2 d (i + 1) (t - 1)) /
      capacityD2 d (i + 1) (t - 1))
    (hid : a / c = 16 * gOld + 16 * rhoOld +
      32 * (Finset.univ.sum childRho) - gNow)
    (hgOld : gOld ≤ 1 / 512) (hgNow : 0 ≤ gNow) :
    a / c ≤ 279 / 256 := by
  have hroles := d2_schedule_two_step_quota_roles hd hi ht htf ha hrole
    haOld childAlloc hchildAlloc rhoOld childRho hOldDef hChildDef
  exact d2_two_step_sender_factor_279 hid hgOld hgNow hroles

/-- An ordinary sender whose two-stage predecessor is an ordinary role has
noncrossing current fronts, assuming the exact two-step identity and the
native/deficit caps. -/
theorem d2_schedule_ordinary_predecessor_noncrossing {d i t : Nat}
    (hd : 7 ≤ d) (hi : i < d) (ht : 4 ≤ t)
    (htf : t < tfD2 d)
    (ha : active d (tfD2 d) i t)
    (hrole : d2ScheduleRole d i t = .topRise ∨
      d2ScheduleRole d i t = .mid ∨
      d2ScheduleRole d i t = .botDesc)
    (hOldRole : d2ScheduleRole d i (t - 2) = .topRise ∨
      d2ScheduleRole d i (t - 2) = .mid ∨
      d2ScheduleRole d i (t - 2) = .botDesc)
    {aOld a gOld gNow : Rat} (haOld : aOld ≤ nativeD2 d i)
    (halloc : a ≤ nativeD2 d i)
    (childAlloc : Fin 8 → Rat)
    (hchildAlloc : ∀ j, childAlloc j ≤ nativeD2 d (i + 1))
    (hchildNonneg : ∀ j, 0 ≤ childAlloc j)
    (rhoOld : Rat) (childRho : Fin 8 → Rat)
    (hOldDef : rhoOld = d2PortSize (d2ScheduleRole d i (t - 2)) aOld
      (capacityD2 d i (t - 2)) / capacityD2 d i (t - 2))
    (hChildDef : ∀ j, childRho j =
      d2PortSize (d2ScheduleRole d (i + 1) (t - 1)) (childAlloc j)
        (capacityD2 d (i + 1) (t - 1)) /
      capacityD2 d (i + 1) (t - 1))
    (hid : a / capacityD2 d i t = 16 * gOld + 16 * rhoOld +
      32 * (Finset.univ.sum childRho) - gNow)
    (hgOld : 0 ≤ gOld) (hgNow : gNow ≤ 7 / 128) :
    d2PortSize (d2ScheduleRole d i t) a (capacityD2 d i t) ≤ a := by
  have hc : 0 < capacityD2 d i t := by
    unfold capacityD2
    exact div_pos (pow_pos (by norm_num : (0 : Rat) < 2) _)
      (pow_pos (by norm_num : (0 : Rat) < 2) _)
  have holdc : 0 < capacityD2 d i (t - 2) := by
    unfold capacityD2
    exact div_pos (pow_pos (by norm_num : (0 : Rat) < 2) _)
      (pow_pos (by norm_num : (0 : Rat) < 2) _)
  have hchildc : 0 < capacityD2 d (i + 1) (t - 1) := by
    unfold capacityD2
    exact div_pos (pow_pos (by norm_num : (0 : Rat) < 2) _)
      (pow_pos (by norm_num : (0 : Rat) < 2) _)
  have hOldRange := d2_regular_port_range (a := aOld)
    (le_of_lt holdc) hOldRole
  have hrhoOld : 15 / 4096 ≤ rhoOld := by
    rw [hOldDef]
    apply (le_div_iff₀ holdc).2
    nlinarith [hOldRange.1]
  have hchildNonnegRatio : ∀ j, 0 ≤ childRho j := by
    intro j
    have hport := d2PortSize_nonneg
      (role := d2ScheduleRole d (i + 1) (t - 1))
      (hchildNonneg j) (le_of_lt hchildc)
    rw [hChildDef j]
    exact div_nonneg hport (le_of_lt hchildc)
  have hchildSum : 0 ≤ Finset.univ.sum childRho :=
    Finset.sum_nonneg fun j hj => hchildNonnegRatio j
  have hport := d2ScheduleRole_port_bound_of_native
    (d := d) (i := i) (t := t) (a := a) (by omega) hi.le halloc
  have hrhoNow :
      d2PortSize (d2ScheduleRole d i t) a (capacityD2 d i t) /
        capacityD2 d i t ≤ 1 / 256 := by
    apply (div_le_iff₀ hc).2
    nlinarith [hport]
  have hratio := ordinary_two_step_forces_noncrossing
    (a := a) (pi := d2PortSize (d2ScheduleRole d i t) a
      (capacityD2 d i t)) (c := capacityD2 d i t)
    (gOld := gOld) (rhoOld := rhoOld)
    (childRho := Finset.univ.sum childRho) (gNow := gNow)
    (rhoNow := d2PortSize (d2ScheduleRole d i t) a
      (capacityD2 d i t) / capacityD2 d i t)
    hc hid hgOld hrhoOld hchildSum hgNow hrhoNow rfl
  exact hratio

/-- Two visits after `botRise`, conservation and nonnegative current deficit
give the stronger sender-allocation cap `a/c<=1/16`. -/
theorem botRise_parent_trace_sender_factor {d : Nat}
    (hd : 7 ≤ d) (j : Nat) (hj : 1 ≤ j)
    [DecidablePred (active d (tfD2 d) (j + 2))]
    [DecidablePred (active d (tfD2 d) (j + 3))]
    (hstage : 3 * j + 2 < tfD2 d)
    {aOld GOld aNow GNow : Rat} (childPort cutDeficit : Nat → Rat)
    (hOldConserve : aOld + GOld = Finset.univ.sum fun _ : Fin 8 =>
      d2ChildDeficitTrace (nativeD2 d (j + 3))
        (fun s => if active d (tfD2 d) (j + 3) s then true else false)
        childPort
        (fun s => if active d (tfD2 d) (j + 2) s then true else false)
        (fun s => d2ScheduleRole d (j + 2) s) cutDeficit (3 * j + 2))
    (hNowConserve : aNow + GNow = Finset.univ.sum fun _ : Fin 8 =>
      d2ChildDeficitTrace (nativeD2 d (j + 3))
        (fun s => if active d (tfD2 d) (j + 3) s then true else false)
        childPort
        (fun s => if active d (tfD2 d) (j + 2) s then true else false)
        (fun s => d2ScheduleRole d (j + 2) s) cutDeficit (3 * j + 2))
    (hGNow : 0 ≤ GNow) :
    aNow / capacityD2 d (j + 2) (3 * j + 2) ≤ 1 / 16 := by
  have hnative := botRise_native_split_of_parent_trace
    (a := aOld) (G := GOld) hd j hj (by omega) childPort cutDeficit
    hOldConserve
  have hid := botRise_parent_trace_two_step_identity hd j hj hstage
    (aOld := aOld) (GOld := GOld) (aNow := aNow) (GNow := GNow)
    childPort cutDeficit hOldConserve hNowConserve
  have hc : 0 < capacityD2 d (j + 2) (3 * j + 2) := by
    unfold capacityD2
    exact div_pos (pow_pos (by norm_num : (0 : Rat) < 2) _)
      (pow_pos (by norm_num : (0 : Rat) < 2) _)
  have hGnorm : 0 ≤ GNow / capacityD2 d (j + 2) (3 * j + 2) :=
    div_nonneg hGNow (le_of_lt hc)
  have hsum :
      GOld / capacityD2 d (j + 2) (3 * j) +
        aOld / capacityD2 d (j + 2) (3 * j) = 1 / 256 := by
    linarith [hnative]
  rw [hid]
  linarith

/-- An active node is inactive at the intervening stage one step before its
next same-level visit, by the schedule's parity constraint. -/
theorem active_level_inactive_previous_stage {d tf i t : Nat}
    (ht : 4 ≤ t) (ha : active d tf i t) :
    ¬ active d tf i (t - 1) := by
  intro hprev
  have hnow := (active_iff_frontiers (d := d) (tf := tf) (i := i)
    (t := t) (by omega)).1 ha
  have hbefore := (active_iff_frontiers (d := d) (tf := tf) (i := i)
    (t := t - 1) (by omega)).1 hprev
  omega

/-- An ordinary predecessor's half-port reserve survives the intervening
stage before the same-level sender's next visit: the parent is inactive then,
and an active child can only add nonnegative up-port deficit. -/
theorem d2_scheduled_endpoint_reserve_persists {d tf i t : Nat}
    (ht : 4 ≤ t) (ha : active d tf i t)
    {c cOld piOld half uOld piChild : Rat}
    (hc : 0 < c) (hcap : cOld = 16 * c)
    (hquota : 15 * cOld / 4096 ≤ piOld)
    (heven : piOld = 2 * half) (hcut : half ≤ uOld)
    (isChildActive : Bool) (hpiChild : 0 ≤ piChild) :
    c / 128 ≤ d2ChildDeficitAfterStage isChildActive false
      (d2ScheduleRole d i (t - 1)) uOld piChild 0 := by
  have hreserve := d2_ordinary_endpoint_reserve_transfer isChildActive
    hc hcap hquota heven hcut hpiChild
  simpa [d2ChildDeficitAfterStage] using hreserve

/-! ## Concrete finite-tree state (bridge in progress)

Unlike the rational trace interfaces above, this datatype represents one
actual recursively nested D2 flow state. The saturated case deliberately has
no endpoint-balance requirement, matching `FlowDAG.subtree_interval`.
-/

inductive D2FlowTree : Nat → Type
  | leaf (G low high : Nat) : D2FlowTree 0
  | node {h : Nat} (G low high : Nat)
      (children : Fin 8 → D2FlowTree h) : D2FlowTree (h + 1)

def d2FlowTreeRootDeficit : {h : Nat} → D2FlowTree h → Nat
  | 0, .leaf G _ _ => G
  | _ + 1, .node G _ _ _ => G

def d2FlowTreeFull (scale : Nat) : (h : Nat) → D2FlowTree h
  | 0 => .leaf scale 0 0
  | h + 1 => .node (scale * 8 ^ (h + 1)) 0 0
      (fun _ => d2FlowTreeFull scale h)

def d2FlowTreeInitial (scale : Nat) : (depth : Nat) → D2FlowTree depth
  | 0 => .leaf 0 0 0
  | depth + 1 => .node 0 0 0 (fun _ => d2FlowTreeFull scale depth)

theorem d2FlowTreeFull_root_deficit (scale h : Nat) :
    d2FlowTreeRootDeficit (d2FlowTreeFull scale h) = scale * 8 ^ h := by
  cases h <;> simp [d2FlowTreeFull, d2FlowTreeRootDeficit]

def d2FlowTreeInv : (scale : Nat) → {h : Nat} → D2FlowTree h → Prop
  | scale, 0, .leaf G low high =>
      G ≤ scale ∧ (G < scale → low + high = G)
  | scale, h + 1, .node G low high children =>
      G ≤ scale * 8 ^ (h + 1) ∧
      G ≤ Finset.univ.sum (fun j : Fin 8 =>
        d2FlowTreeRootDeficit (children j)) ∧
      (G < scale * 8 ^ (h + 1) → low + high = G) ∧
      (∀ j, d2FlowTreeInv scale (children j))

theorem d2FlowTreeFull_inv (scale h : Nat) :
    d2FlowTreeInv scale (d2FlowTreeFull scale h) := by
  induction h with
  | zero => simp [d2FlowTreeFull, d2FlowTreeInv]
  | succ h ih =>
      simp only [d2FlowTreeFull, d2FlowTreeInv]
      refine ⟨Nat.le_refl _, ?_, ?_, ?_⟩
      · have hsum : (Finset.univ.sum fun j : Fin 8 =>
            d2FlowTreeRootDeficit (d2FlowTreeFull scale h)) =
            scale * 8 ^ (h + 1) := by
          cases h <;>
            simp [d2FlowTreeRootDeficit, d2FlowTreeFull, Nat.pow_succ,
              mul_assoc, mul_left_comm, mul_comm]
        rw [hsum]
      · intro hlt
        omega
      · intro j
        exact ih

theorem d2FlowTreeInitial_inv (scale depth : Nat) :
    d2FlowTreeInv scale (d2FlowTreeInitial scale depth) := by
  cases depth with
  | zero => simp [d2FlowTreeInitial, d2FlowTreeInv]
  | succ depth =>
      simp only [d2FlowTreeInitial, d2FlowTreeInv]
      refine ⟨Nat.zero_le _, Nat.zero_le _, ?_, ?_⟩
      · intro _
        trivial
      · intro j
        exact d2FlowTreeFull_inv scale depth

theorem d2FlowTreeInv_root_native_bound {h scale : Nat}
    (tree : D2FlowTree h) (hinv : d2FlowTreeInv scale tree) :
    d2FlowTreeRootDeficit tree ≤ scale * 8 ^ h := by
  cases tree with
  | leaf G low high =>
      simpa [d2FlowTreeInv] using hinv.1
  | node G low high children =>
      simpa [d2FlowTreeInv] using hinv.1

def d2FlowTreeSetRoot : {h : Nat} → D2FlowTree h → Nat → Nat → Nat → D2FlowTree h
  | 0, .leaf _ _ _, G, low, high => .leaf G low high
  | h + 1, .node _ _ _ children, G, low, high =>
      .node G low high children

def d2FlowTreeRootData : {h : Nat} → D2FlowTree h → Nat × Nat × Nat
  | _, .leaf G low high => (G, low, high)
  | _, .node G low high _ => (G, low, high)

theorem d2FlowTreeRootData_fst_eq_deficit {h : Nat}
    (tree : D2FlowTree h) :
    (d2FlowTreeRootData tree).1 = d2FlowTreeRootDeficit tree := by
  cases tree <;> rfl

theorem d2FlowTreeRootData_setRoot {h : Nat} (tree : D2FlowTree h)
    (G low high : Nat) :
    d2FlowTreeRootData (d2FlowTreeSetRoot tree G low high) = (G, low, high) := by
  cases tree <;> rfl

theorem d2FlowTreeSetRoot_rootData_identity {h : Nat}
    (tree : D2FlowTree h) :
    d2FlowTreeSetRoot tree (d2FlowTreeRootData tree).1
      (d2FlowTreeRootData tree).2.1 (d2FlowTreeRootData tree).2.2 = tree := by
  cases tree <;> rfl

/-- Overwriting a subtree root with a no-larger deficit preserves its tree
invariant: the old root already covered the deficits below it. -/
theorem d2FlowTreeSetRoot_preserves_inv_of_lower_deficit
    {h scale : Nat} (tree : D2FlowTree h)
    (hinv : d2FlowTreeInv scale tree) (G low high : Nat)
    (hcap : G ≤ scale * 8 ^ h)
    (hbal : G < scale * 8 ^ h → low + high = G)
    (hle : G ≤ d2FlowTreeRootDeficit tree) :
    d2FlowTreeInv scale (d2FlowTreeSetRoot tree G low high) := by
  cases tree with
  | leaf oldG oldLow oldHigh =>
      simp only [d2FlowTreeInv] at hinv
      simp only [d2FlowTreeSetRoot, d2FlowTreeInv]
      constructor
      · simpa using hcap
      · intro hlt
        exact hbal (by simpa using hlt)
  | node oldG oldLow oldHigh children =>
      simp only [d2FlowTreeInv] at hinv
      have hcoverOld : oldG ≤ Finset.univ.sum (fun j : Fin 8 =>
          d2FlowTreeRootDeficit (children j)) := hinv.2.1
      have hcoverNew : G ≤ Finset.univ.sum (fun j : Fin 8 =>
          d2FlowTreeRootDeficit (children j)) := le_trans hle hcoverOld
      have hchildren : ∀ j, d2FlowTreeInv scale (children j) := hinv.2.2.2
      simp only [d2FlowTreeSetRoot, d2FlowTreeInv]
      exact ⟨hcap, hcoverNew, hbal, hchildren⟩

def d2FlowTreeChild : {h : Nat} → D2FlowTree (h + 1) → Fin 8 → D2FlowTree h
  | _, .node _ _ _ children, j => children j

def d2FlowPosition (sizes : Fin 8 → Nat) (j : Fin 8) : Nat :=
  (Finset.univ.filter fun k : Fin 8 => k.val < j.val).sum sizes

def d2FlowTotal (sizes : Fin 8 → Nat) : Nat :=
  Finset.univ.sum sizes

theorem d2FlowSize_le_total (sizes : Fin 8 → Nat) (j : Fin 8) :
    sizes j ≤ d2FlowTotal sizes := by
  unfold d2FlowTotal
  exact Finset.single_le_sum
    (fun k hk => Nat.zero_le (sizes k)) (Finset.mem_univ j)

theorem d2FlowPosition_zero (sizes : Fin 8 → Nat) :
    d2FlowPosition sizes 0 = 0 := by
  simp [d2FlowPosition]

theorem d2FlowPosition_succ (sizes : Fin 8 → Nat) (n : Nat) (hn : n < 7) :
    d2FlowPosition sizes ⟨n + 1, by omega⟩ =
      d2FlowPosition sizes ⟨n, by omega⟩ + sizes ⟨n, by omega⟩ := by
  let j : Fin 8 := ⟨n, by omega⟩
  have hfilter :
      (Finset.univ.filter fun k : Fin 8 => k.val < n + 1) =
        (Finset.univ.filter fun k : Fin 8 => k.val < n) ∪ {j} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro hk
      by_cases hlt : k.val < n
      · exact Or.inl hlt
      · right
        apply Fin.ext
        simp [j]
        omega
    · rintro (hlt | heq)
      · omega
      · have hv : k.val = n := by simpa [j] using congrArg Fin.val heq
        omega
  have hdisj : Disjoint
      (Finset.univ.filter fun k : Fin 8 => k.val < n) ({j} : Finset (Fin 8)) := by
    apply Finset.disjoint_left.mpr
    intro k hk hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] at hk hj
    subst k
    simp [j] at hk
  unfold d2FlowPosition
  rw [hfilter, Finset.sum_union hdisj]
  simp [j]

theorem d2FlowPosition_uniform (u : Nat) (j : Fin 8) :
    d2FlowPosition (fun _ : Fin 8 => u) j = j.val * u := by
  have hrec : ∀ n : Nat, ∀ hn : n ≤ 7,
      d2FlowPosition (fun _ : Fin 8 => u) ⟨n, by omega⟩ = n * u := by
    intro n hn
    induction n with
    | zero => simp [d2FlowPosition_zero]
    | succ n ih =>
        have hnlt : n < 7 := by omega
        rw [d2FlowPosition_succ (fun _ : Fin 8 => u) n hnlt]
        rw [ih (by omega)]
        ring
  simpa using hrec j.val (by omega)

theorem d2FlowPosition_last_end (sizes : Fin 8 → Nat) :
    d2FlowPosition sizes ⟨7, by omega⟩ + sizes ⟨7, by omega⟩ =
      d2FlowTotal sizes := by
  let j : Fin 8 := ⟨7, by omega⟩
  have hfilter :
      (Finset.univ.filter fun k : Fin 8 => k.val < 7) ∪ {j} = Finset.univ := by
    ext k
    simp [j]
    omega
  have hdisj : Disjoint
      (Finset.univ.filter fun k : Fin 8 => k.val < 7) ({j} : Finset (Fin 8)) := by
    apply Finset.disjoint_left.mpr
    intro k hk hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] at hk hj
    subst k
    simp [j] at hk
  unfold d2FlowPosition d2FlowTotal
  calc
    (Finset.univ.filter fun k : Fin 8 => k.val < 7).sum sizes + sizes j =
        (Finset.univ.filter fun k : Fin 8 => k.val < 7).sum sizes +
          ({j} : Finset (Fin 8)).sum sizes := by simp
    _ = ((Finset.univ.filter fun k : Fin 8 => k.val < 7) ∪ {j}).sum sizes :=
        (Finset.sum_union hdisj).symm
    _ = Finset.univ.sum sizes := by rw [hfilter]

theorem d2FlowPositions_contiguous (sizes : Fin 8 → Nat) :
    d2FlowPosition sizes 0 = 0 ∧
      (∀ k : Nat, (hk : k < 7) →
        d2FlowPosition sizes ⟨k + 1, by omega⟩ =
          d2FlowPosition sizes ⟨k, by omega⟩ + sizes ⟨k, by omega⟩) ∧
      d2FlowPosition sizes ⟨7, by omega⟩ + sizes ⟨7, by omega⟩ =
        d2FlowTotal sizes := by
  exact ⟨d2FlowPosition_zero sizes,
    (fun k hk => d2FlowPosition_succ sizes k hk),
    d2FlowPosition_last_end sizes⟩

def d2FlowBoundary (sizes : Fin 8 → Nat) (n : Fin 9) : Nat :=
  if h : n.val = 8 then d2FlowTotal sizes
  else d2FlowPosition sizes ⟨n.val, by omega⟩

theorem d2FlowBoundary_succ (sizes : Fin 8 → Nat) (j : Fin 8) :
    d2FlowBoundary sizes ⟨j.val + 1, by omega⟩ =
      d2FlowBoundary sizes ⟨j.val, by omega⟩ + sizes j := by
  by_cases hj : j.val = 7
  · have hjeq : j = ⟨7, by omega⟩ := Fin.ext hj
    rw [hjeq]
    simpa [d2FlowBoundary] using (d2FlowPosition_last_end sizes).symm
  · have hjlt : j.val < 7 := by omega
    have hjnext : j.val + 1 ≠ 8 := by omega
    have hjval8 : j.val ≠ 8 := by omega
    simpa [d2FlowBoundary, hj, hjnext, hjval8] using
      (d2FlowPosition_succ sizes j.val hjlt)

theorem d2FlowBoundary_zero (sizes : Fin 8 → Nat) :
    d2FlowBoundary sizes 0 = 0 := by
  simp [d2FlowBoundary, d2FlowPosition_zero]

theorem d2FlowBoundary_eight (sizes : Fin 8 → Nat) :
    d2FlowBoundary sizes ⟨8, by omega⟩ = d2FlowTotal sizes := by
  simp [d2FlowBoundary]

theorem d2FlowBoundary_at_child (sizes : Fin 8 → Nat) (j : Fin 8) :
    d2FlowBoundary sizes ⟨j.val, by omega⟩ = d2FlowPosition sizes j := by
  have hj : j.val ≠ 8 := by omega
  simp [d2FlowBoundary, hj]

theorem d2FlowSumSuccDiff (f : Fin 9 → Nat)
    (hmono : ∀ j : Fin 8, f ⟨j.val, by omega⟩ ≤ f ⟨j.val + 1, by omega⟩) :
    (Finset.univ.sum fun j : Fin 8 =>
      f ⟨j.val + 1, by omega⟩ - f ⟨j.val, by omega⟩) =
        f ⟨8, by omega⟩ - f 0 := by
  have h0 := hmono ⟨0, by omega⟩
  have h1 := hmono ⟨1, by omega⟩
  have h2 := hmono ⟨2, by omega⟩
  have h3 := hmono ⟨3, by omega⟩
  have h4 := hmono ⟨4, by omega⟩
  have h5 := hmono ⟨5, by omega⟩
  have h6 := hmono ⟨6, by omega⟩
  have h7 := hmono ⟨7, by omega⟩
  simp_all [Fin.sum_univ_succ]
  omega

theorem d2FlowLeftCuts_sum (sizes : Fin 8 → Nat) (left : Nat)
    (hleft : left ≤ d2FlowTotal sizes) :
    (Finset.univ.sum fun j : Fin 8 =>
      d2LeftCut (d2FlowBoundary sizes ⟨j.val, by omega⟩) (sizes j) left) = left := by
  let f : Fin 9 → Nat := fun n => min (d2FlowBoundary sizes n) left
  have hmono : ∀ j : Fin 8, f ⟨j.val, by omega⟩ ≤ f ⟨j.val + 1, by omega⟩ := by
    intro j
    dsimp [f]
    rw [d2FlowBoundary_succ]
    omega
  have hcut (j : Fin 8) :
      d2LeftCut (d2FlowBoundary sizes ⟨j.val, by omega⟩) (sizes j) left =
        f ⟨j.val + 1, by omega⟩ - f ⟨j.val, by omega⟩ := by
    rw [d2LeftCut_eq_min_difference, ← d2FlowBoundary_succ]
  calc
    (Finset.univ.sum fun j : Fin 8 =>
        d2LeftCut (d2FlowBoundary sizes ⟨j.val, by omega⟩) (sizes j) left) =
      Finset.univ.sum (fun j : Fin 8 =>
        f ⟨j.val + 1, by omega⟩ - f ⟨j.val, by omega⟩) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hcut j
    _ = f ⟨8, by omega⟩ - f 0 := d2FlowSumSuccDiff f hmono
    _ = left := by
          change min (d2FlowBoundary sizes ⟨8, by omega⟩) left -
            min (d2FlowBoundary sizes 0) left = left
          rw [d2FlowBoundary_eight, d2FlowBoundary_zero]
          simp [Nat.min_eq_right hleft]

theorem d2FlowRightCuts_sum (sizes : Fin 8 → Nat) (right : Nat)
    (hright : right ≤ d2FlowTotal sizes) :
    (Finset.univ.sum fun j : Fin 8 =>
      d2RightCut (d2FlowBoundary sizes ⟨j.val, by omega⟩) (sizes j) right) =
        d2FlowTotal sizes - right := by
  let f : Fin 9 → Nat := fun n => max (d2FlowBoundary sizes n) right
  have hmono : ∀ j : Fin 8, f ⟨j.val, by omega⟩ ≤ f ⟨j.val + 1, by omega⟩ := by
    intro j
    dsimp [f]
    rw [d2FlowBoundary_succ]
    omega
  have hcut (j : Fin 8) :
      d2RightCut (d2FlowBoundary sizes ⟨j.val, by omega⟩) (sizes j) right =
        f ⟨j.val + 1, by omega⟩ - f ⟨j.val, by omega⟩ := by
    rw [d2RightCut_eq_max_difference, ← d2FlowBoundary_succ]
  calc
    (Finset.univ.sum fun j : Fin 8 =>
        d2RightCut (d2FlowBoundary sizes ⟨j.val, by omega⟩) (sizes j) right) =
      Finset.univ.sum (fun j : Fin 8 =>
        f ⟨j.val + 1, by omega⟩ - f ⟨j.val, by omega⟩) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hcut j
    _ = f ⟨8, by omega⟩ - f 0 := d2FlowSumSuccDiff f hmono
    _ = d2FlowTotal sizes - right := by
          change max (d2FlowBoundary sizes ⟨8, by omega⟩) right -
            max (d2FlowBoundary sizes 0) right = d2FlowTotal sizes - right
          rw [d2FlowBoundary_eight, d2FlowBoundary_zero]
          simp [Nat.max_eq_left hright]

theorem d2FlowLeftCuts_sum_position (sizes : Fin 8 → Nat) (left : Nat)
    (hleft : left ≤ d2FlowTotal sizes) :
    (Finset.univ.sum fun j : Fin 8 =>
      d2LeftCut (d2FlowPosition sizes j) (sizes j) left) = left := by
  simpa only [← d2FlowBoundary_at_child] using
    d2FlowLeftCuts_sum sizes left hleft

theorem d2FlowRightCuts_sum_position (sizes : Fin 8 → Nat) (right : Nat)
    (hright : right ≤ d2FlowTotal sizes) :
    (Finset.univ.sum fun j : Fin 8 =>
      d2RightCut (d2FlowPosition sizes j) (sizes j) right) =
        d2FlowTotal sizes - right := by
  simpa only [← d2FlowBoundary_at_child] using
    d2FlowRightCuts_sum sizes right hright

theorem d2FlowPositionedChildren_ordered (sizes : Fin 8 → Nat) :
    sizes 0 ≤ d2FlowPosition sizes ⟨7, by omega⟩ ∧
      (∀ j : Fin 8, 0 < j.val → j.val < 7 →
        sizes 0 ≤ d2FlowPosition sizes j ∧
          d2FlowPosition sizes j + sizes j ≤ d2FlowPosition sizes ⟨7, by omega⟩) := by
  have h := d2FlowPositions_contiguous sizes
  exact d2_contiguous_children_ordered sizes (fun j => d2FlowPosition sizes j)
    h.1 h.2.1

def d2FlowTreeAllocation : {h : Nat} → (scale : Nat) → D2FlowTree h → Nat
  | 0, scale, .leaf G _ _ => scale - G
  | h + 1, _, .node G _ _ children =>
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G

/-- The tree invariant bounds every actual subtree allocation by its native
capacity. This is the recursive-tree form of the child-deficit allocation
bound used by the two-step sender estimate. -/
theorem d2FlowTreeInv_allocation_bound {h scale : Nat}
    (tree : D2FlowTree h) (hinv : d2FlowTreeInv scale tree) :
    d2FlowTreeAllocation scale tree ≤ scale * 8 ^ h := by
  induction tree with
  | leaf G low high =>
      simp only [d2FlowTreeInv] at hinv
      simp [d2FlowTreeAllocation]
  | @node h G low high children ih =>
      simp only [d2FlowTreeInv] at hinv
      have hchildren : ∀ j, d2FlowTreeInv scale (children j) := hinv.2.2.2
      have hchild : ∀ j, d2FlowTreeRootDeficit (children j) ≤ scale * 8 ^ h := by
        intro j
        exact d2FlowTreeInv_root_native_bound (children j) (hchildren j)
      have hsum : d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) ≤
          8 * (scale * 8 ^ h) := by
        unfold d2FlowTotal
        calc
          Finset.univ.sum (fun j : Fin 8 => d2FlowTreeRootDeficit (children j)) ≤
              Finset.univ.sum (fun _ : Fin 8 => scale * 8 ^ h) :=
            Finset.sum_le_sum (by intro j hj; exact hchild j)
          _ = 8 * (scale * 8 ^ h) := by simp
      have hpow : 8 * (scale * 8 ^ h) = scale * 8 ^ (h + 1) := by
        rw [Nat.pow_succ]
        ring
      calc
        d2FlowTreeAllocation scale (.node G low high children) ≤
            d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := Nat.sub_le _ _
        _ ≤ 8 * (scale * 8 ^ h) := hsum
        _ = scale * 8 ^ (h + 1) := hpow

/-- At scale8192, the actual tree allocation at level `i` normalizes to at
most the schedule's native capacity. This supplies the native-allocation
premises in the schedule's two-step role split directly from tree induction. -/
theorem d2FlowCandidateTreeAllocation_le_native {d i : Nat}
    (hi : i ≤ d) (tree : D2FlowTree (d - i))
    (hinv : d2FlowTreeInv 8192 tree) :
    (d2FlowTreeAllocation 8192 tree : Rat) / 8192 ≤ nativeD2 d i := by
  have halloc := d2FlowTreeInv_allocation_bound tree hinv
  have hallocRat : (d2FlowTreeAllocation 8192 tree : Rat) ≤
      8192 * (8 : Rat) ^ (d - i) := by
    exact_mod_cast halloc
  have hnative : (8 : Rat) ^ (d - i) = nativeD2 d i := by
    unfold nativeD2
    rw [show (8 : Rat) = 2 ^ 3 by norm_num, pow_mul]
  rw [div_le_iff₀ (by norm_num : (0 : Rat) < 8192)]
  rw [hnative] at hallocRat
  nlinarith

theorem d2FlowTreeInv_node_children_cover {h scale G low high : Nat}
    (children : Fin 8 → D2FlowTree h)
    (hinv : d2FlowTreeInv scale (.node G low high children)) :
    G ≤ d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
  simpa only [d2FlowTreeInv] using hinv.2.1

/-- If an invariant node is saturated at its full native deficit, every child
must also be saturated: child-cover forces their sum to the parent's full
capacity, while the invariant caps each child by its own native size. -/
theorem d2FlowTreeInv_native_node_children {h scale G low high : Nat}
    (children : Fin 8 → D2FlowTree h)
    (hinv : d2FlowTreeInv scale (.node G low high children))
    (hfull : G = scale * 8 ^ (h + 1)) :
    ∀ j, d2FlowTreeRootDeficit (children j) = scale * 8 ^ h := by
  have hcover := d2FlowTreeInv_node_children_cover children hinv
  have hchildBound : ∀ j, d2FlowTreeRootDeficit (children j) ≤
      scale * 8 ^ h := by
    intro j
    have hchildInv : d2FlowTreeInv scale (children j) := by
      simpa only [d2FlowTreeInv] using hinv.2.2.2 j
    exact d2FlowTreeInv_root_native_bound (children j) hchildInv
  have hfullEq : scale * 8 ^ (h + 1) = 8 * (scale * 8 ^ h) := by
    rw [Nat.pow_succ]
    ring
  intro j
  let f : Fin 8 → Nat := fun k => d2FlowTreeRootDeficit (children k)
  have hsplit : f j + (∑ k ∈ Finset.univ.erase j, f k) =
      d2FlowTotal f := by
    simpa [d2FlowTotal] using
      (Finset.add_sum_erase Finset.univ f (Finset.mem_univ j))
  have hothers : (∑ k ∈ Finset.univ.erase j, f k) ≤
      7 * (scale * 8 ^ h) := by
    calc
      (∑ k ∈ Finset.univ.erase j, f k) ≤
          ∑ k ∈ Finset.univ.erase j, scale * 8 ^ h :=
        Finset.sum_le_sum fun k hk => hchildBound k
      _ = 7 * (scale * 8 ^ h) := by simp
  have htotal : 8 * (scale * 8 ^ h) ≤ d2FlowTotal f := by
    rw [← hfullEq, ← hfull]
    exact hcover
  rw [← hsplit] at htotal
  have hlo : scale * 8 ^ h ≤ f j := by omega
  exact Nat.le_antisymm (hchildBound j) hlo

/-- The recursive invariant passes through any two nested child projections. -/
theorem d2FlowTreeInv_grandchild {h scale : Nat}
    (tree : D2FlowTree (h + 2)) (hinv : d2FlowTreeInv scale tree)
    (j k : Fin 8) :
    d2FlowTreeInv scale
      (d2FlowTreeChild (d2FlowTreeChild tree j) k) := by
  cases tree with
  | node G low high children =>
      have hroot := hinv
      simp only [d2FlowTreeInv] at hroot
      have hchildInv := hroot.2.2.2 j
      cases hchild : children j with
      | node G' low' high' grandchildren =>
          rw [hchild] at hchildInv
          simp only [d2FlowTreeInv] at hchildInv
          simpa only [d2FlowTreeChild, hchild] using hchildInv.2.2.2 k

theorem d2FlowTreeInv_node_allocation_exact {h scale G low high : Nat}
    (children : Fin 8 → D2FlowTree h)
    (hinv : d2FlowTreeInv scale (.node G low high children)) :
    d2FlowTreeAllocation scale (.node G low high children) + G =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
  have hcover := d2FlowTreeInv_node_children_cover children hinv
  exact Nat.sub_add_cancel hcover

theorem d2FlowTreeRootDeficit_full (scale h : Nat) :
    d2FlowTreeRootDeficit (d2FlowTreeFull scale h) = scale * 8 ^ h := by
  cases h with
  | zero => simp [d2FlowTreeFull, d2FlowTreeRootDeficit]
  | succ h => simp [d2FlowTreeFull, d2FlowTreeRootDeficit]

theorem d2FlowTreeAllocation_initial (scale depth : Nat) :
    d2FlowTreeAllocation scale (d2FlowTreeInitial scale depth) =
      scale * 8 ^ depth := by
  cases depth with
  | zero => simp [d2FlowTreeAllocation, d2FlowTreeInitial]
  | succ depth =>
      simp only [d2FlowTreeInitial, d2FlowTreeAllocation, Nat.sub_zero]
      simp_rw [d2FlowTreeRootDeficit_full]
      simp [d2FlowTotal]
      rw [Nat.pow_succ]
      ring

def d2FlowCutChild (pos size left right : Nat) : Nat × Nat × Nat :=
  let leftCut := d2LeftCut pos size left
  let rightCut := d2RightCut pos size right
  (leftCut + rightCut, leftCut, rightCut)

/-- The stage-three top-rise cut acts on the ragged stage-two profile
`38M,30M,...,30M,38M`. A half-`M` front at either end touches only that
endpoint child. -/
theorem d2FlowCutChild_tapered_38_30_profile (M : Nat) :
    let sizes : Fin 8 → Nat := fun j =>
      if j.val = 0 ∨ j.val = 7 then 38 * M else 30 * M
    ∀ j : Fin 8,
      d2FlowCutChild (d2FlowPosition sizes j) (sizes j)
        (M / 2) (256 * M - M / 2) =
        if j.val = 0 then (M / 2, M / 2, 0)
        else if j.val = 7 then (M / 2, 0, M / 2)
        else (0, 0, 0) := by
  intro sizes j
  fin_cases j <;>
    simp [d2FlowCutChild, d2LeftCut, d2RightCut, d2FlowPosition,
      sizes, Finset.sum_filter, Fin.sum_univ_succ] <;> omega

/-- If equal full children are cut by two short fronts, only the first and
last children are touched; this is the exact first-sender profile. -/
theorem d2FlowCutChild_uniform_profile {u left : Nat} (hleft : left ≤ u) :
    ∀ j : Fin 8,
      d2FlowCutChild (j.val * u) u left (8 * u - left) =
        if j.val = 0 then (left, left, 0)
        else if j.val = 7 then (left, 0, left)
        else (0, 0, 0) := by
  intro j
  fin_cases j <;>
    simp [d2FlowCutChild, d2LeftCut, d2RightCut, hleft] <;> omega

/-- Equal full children cut by possibly different low and high fronts. If each
front fits in one endpoint child, only the first and last child are touched. -/
theorem d2FlowCutChild_uniform_asymmetric
    {u left tail : Nat} (hleft : left ≤ u) (htail : tail ≤ u) :
    ∀ j : Fin 8,
      d2FlowCutChild (j.val * u) u left (8 * u - tail) =
        if j.val = 0 then (left, left, 0)
        else if j.val = 7 then (tail, 0, tail)
        else (0, 0, 0) := by
  intro j
  fin_cases j <;>
    simp [d2FlowCutChild, d2LeftCut, d2RightCut, hleft, htail] <;> omega

theorem d2FlowCutChildren_sum (sizes : Fin 8 → Nat) (left right : Nat)
    (hleft : left ≤ d2FlowTotal sizes) (hright : right ≤ d2FlowTotal sizes) :
    (Finset.univ.sum fun j : Fin 8 =>
      (d2FlowCutChild (d2FlowPosition sizes j) (sizes j) left right).1) =
        left + (d2FlowTotal sizes - right) := by
  calc
    (Finset.univ.sum fun j : Fin 8 =>
        (d2FlowCutChild (d2FlowPosition sizes j) (sizes j) left right).1) =
      (Finset.univ.sum fun j : Fin 8 =>
        d2LeftCut (d2FlowPosition sizes j) (sizes j) left) +
      (Finset.univ.sum fun j : Fin 8 =>
        d2RightCut (d2FlowPosition sizes j) (sizes j) right) := by
          simp [d2FlowCutChild, Finset.sum_add_distrib]
    _ = left + (d2FlowTotal sizes - right) := by
          rw [d2FlowLeftCuts_sum_position sizes left hleft,
            d2FlowRightCuts_sum_position sizes right hright]

/-- Exact aggregate child deficit after an ordinary D2 cut. The parent
endpoint balance turns the two front lengths into `G + pi`; the hypotheses
ensure both cuts stay inside the concatenated child interval. -/
theorem d2FlowOrdinaryCut_conserves (sizes : Fin 8 → Nat)
    (G low high pi : Nat) (hbal : G = low + high) (heven : pi % 2 = 0)
    (hleft : low + pi / 2 ≤ d2FlowTotal sizes)
    (hright : high + pi / 2 ≤ d2FlowTotal sizes)
    (hdisjoint : low + pi / 2 ≤ d2FlowTotal sizes - high - pi / 2) :
    (Finset.univ.sum fun j : Fin 8 =>
      (d2FlowCutChild (d2FlowPosition sizes j) (sizes j)
        (low + pi / 2) (d2FlowTotal sizes - high - pi / 2)).1) = G + pi := by
  have hright' : d2FlowTotal sizes - high - pi / 2 ≤ d2FlowTotal sizes := by omega
  have hrightEq : d2FlowTotal sizes - high - pi / 2 =
      d2FlowTotal sizes - (high + pi / 2) := by omega
  have hremaining : d2FlowTotal sizes -
      (d2FlowTotal sizes - (high + pi / 2)) = high + pi / 2 := by omega
  rw [d2FlowCutChildren_sum sizes (low + pi / 2)
    (d2FlowTotal sizes - high - pi / 2) hleft hright']
  rw [hrightEq, hremaining]
  omega

theorem d2FlowCutChild_deficit_eq_update (pos size left right : Nat) :
    (d2FlowCutChild pos size left right).1 =
      d2LocalChildDeficitUpdate .mid pos size left right := rfl

/-- A child's new deficit from an ordinary cut is bounded by the total lengths
of the two fronts. This is useful when a middle sender creates a small
level-three deficit for the next stage's sender-cap gate. -/
theorem d2FlowCutChild_deficit_le_fronts
    {pos size left right total : Nat}
    (hinterval : pos + size <= total) (hright : right <= total) :
    (d2FlowCutChild pos size left right).1 <= left + (total - right) := by
  have hleft : d2LeftCut pos size left <= left := by
    unfold d2LeftCut
    omega
  have hrightCut : d2RightCut pos size right <= total - right := by
    unfold d2RightCut
    omega
  unfold d2FlowCutChild
  simp only
  omega

theorem d2FlowCutChild_le_native {pos size left right native : Nat}
    (hsize : size ≤ native) (hcuts : left ≤ right) :
    (d2FlowCutChild pos size left right).1 ≤ native := by
  simpa [d2FlowCutChild, d2LocalChildDeficitUpdate] using
    d2LocalChildDeficitUpdate_le_native (role := .mid) hsize hcuts

/-- One exact recursive D2 tree transition. The schedule callbacks provide
activity, role, and integer quota at the current stage. As in `FlowDAG.step`,
descendants are stepped first, but allocation and cuts use the old child-root
deficits; the resulting child roots are then overwritten. Schedule-specific
integrality and cut-validity hypotheses are separate proof obligations. -/
def d2FlowStage (active : Nat → Bool) (role : Nat → D2Role)
    (quota : Nat → D2Role → Nat) : (h : Nat) → Nat → D2FlowTree h → D2FlowTree h
  | 0, _, .leaf G low high => .leaf G low high
  | h + 1, i, .node G low high children =>
      let steppedChildren := fun j =>
        d2FlowStage active role quota h (i + 1) (children j)
      if active i then
        let r := role i
        let sizes := fun j => d2FlowTreeRootDeficit (children j)
        let total := d2FlowTotal sizes
        let allocation := total - G
        let pi := match r with
          | .topDesc => 0
          | .botRise => allocation
          | _ => quota i r
        let half := pi / 2
        let left := low + half
        let right := total - high - half
        let updatedChildren := match r with
          | .botRise => steppedChildren
          | .topDesc => fun j => d2FlowTreeSetRoot (steppedChildren j) 0 0 0
          | .topRise | .mid | .botDesc => fun j =>
              let pos := d2FlowPosition sizes j
              let (newG, newLow, newHigh) :=
                d2FlowCutChild pos (sizes j) left right
              d2FlowTreeSetRoot (steppedChildren j) newG newLow newHigh
        .node (G + pi) (low + half) (high + pi - half) updatedChildren
      else
        .node G low high steppedChildren

/-- A recursive stage never decreases the deficit stored at the root of the
subtree it is called on: inactive roots keep it, active roots add a natural
quota (or the truncated natural allocation in the bot-rise case). -/
theorem d2FlowStage_root_deficit_mono
    (active : Nat → Bool) (role : Nat → D2Role)
    (quota : Nat → D2Role → Nat) :
    ∀ {h : Nat} (i : Nat) (tree : D2FlowTree h),
      d2FlowTreeRootDeficit tree ≤
        d2FlowTreeRootDeficit (d2FlowStage active role quota h i tree) := by
  intro h i tree
  cases tree with
  | leaf G low high => rfl
  | node G low high children =>
      by_cases ha : active i = true
      · simp only [d2FlowStage, d2FlowTreeRootDeficit, ha]
        cases role i <;> simp <;> omega
      · simp [d2FlowStage, d2FlowTreeRootDeficit, ha]

/-- If a node is inactive at its own level, its recursive stage call keeps
the deficit stored at that root exactly, regardless of what happens below. -/
theorem d2FlowStage_root_deficit_of_inactive
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i : Nat}
    (tree : D2FlowTree h) (ha : active i = false) :
    d2FlowTreeRootDeficit (d2FlowStage active role quota h i tree) =
      d2FlowTreeRootDeficit tree := by
  cases tree with
  | leaf G low high => rfl
  | node G low high children => simp [d2FlowStage, ha, d2FlowTreeRootDeficit]

/-- At an inactive node, the child projection is exactly the recursive stage
call on that child, with its index advanced by one. -/
theorem d2FlowStage_inactive_child
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high : Nat}
    (children : Fin 8 → D2FlowTree h) (ha : active i = false) (j : Fin 8) :
    d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) j =
      d2FlowStage active role quota h (i + 1) (children j) := by
  simp [d2FlowStage, ha, d2FlowTreeChild]

/-- A bottom-rise sender leaves each descendant root deficit unchanged when
the next scheduled level is inactive: its child update is just the recursive
stage call, whose inactive root preserves the deficit. -/
theorem d2FlowStage_botRise_child_root_deficit
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high : Nat}
    (children : Fin 8 → D2FlowTree h)
    (ha : active i = true) (hr : role i = .botRise)
    (hn : active (i + 1) = false) (j : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) =
      d2FlowTreeRootDeficit (children j) := by
  simp only [d2FlowStage, ha, if_pos, hr, d2FlowTreeChild]
  exact d2FlowStage_root_deficit_of_inactive
    (active := active) (role := role) (quota := quota)
    (h := h) (i := i + 1) (children j) hn

/-- Integer exponent for the physical capacity at row scale `2^13=8192`.
On every active schedule point with `d>=7`, this exponent is at least20. -/
def d2FlowCandidateCapacityExponent (d i t : Nat) : Nat :=
  13 + 3 * d + 3 * i - (2 * t + 4)

def d2FlowCandidateCapacity (d i t : Nat) : Nat :=
  2 ^ d2FlowCandidateCapacityExponent d i t

/-- Advancing one level and one stage doubles scheduled capacity. This is the
scale change needed to turn a tolerant child bound at `2*c` into the
next-stage sender cap. -/
theorem d2FlowCandidateCapacity_succ_level_next_stage
    (d i t : Nat)
    (hscale : 2 * t + 4 ≤ 13 + 3 * d + 3 * i) :
    d2FlowCandidateCapacity d (i + 1) (t + 1) =
      2 * d2FlowCandidateCapacity d i t := by
  have hexp : d2FlowCandidateCapacityExponent d (i + 1) (t + 1) =
      d2FlowCandidateCapacityExponent d i t + 1 := by
    simp only [d2FlowCandidateCapacityExponent]
    omega
  simp only [d2FlowCandidateCapacity, hexp, pow_succ]
  ring

theorem rat_two_pow_sub_eq_div {a b : Nat} (h : b ≤ a) :
    (2 : Rat) ^ (a - b) = (2 : Rat) ^ a / (2 : Rat) ^ b := by
  have hsub : a - b + b = a := Nat.sub_add_cancel h
  calc
    (2 : Rat) ^ (a - b) =
        ((2 : Rat) ^ (a - b) * (2 : Rat) ^ b) / (2 : Rat) ^ b := by
          field_simp
    _ = (2 : Rat) ^ (a - b + b) / (2 : Rat) ^ b := by rw [pow_add]
    _ = (2 : Rat) ^ a / (2 : Rat) ^ b := by rw [hsub]

theorem d2FlowCandidateCapacityExponent_ge_twenty {d i t : Nat}
    (hd : 7 ≤ d) (ha : active d (tfD2 d) i t) :
    20 ≤ d2FlowCandidateCapacityExponent d i t := by
  by_cases ht : t = 1
  · have hi : i = 1 := by
      simpa [active, ht] using ha
    simp [d2FlowCandidateCapacityExponent, ht]
    omega
  · have hparts : 2 ≤ t ∧ t ≤ tfD2 d ∧ i % 2 = t % 2 ∧
        3 * i + 3 * d ≥ 2 * t + 11 ∧ 3 * i < t + 8 := by
      simpa [active, ht] using ha
    unfold d2FlowCandidateCapacityExponent
    omega

theorem d2FlowCandidateCapacity_eq {d i t : Nat} (hd : 7 ≤ d)
    (ha : active d (tfD2 d) i t) :
    (d2FlowCandidateCapacity d i t : Rat) =
      8192 * capacityD2 d i t := by
  have he := d2FlowCandidateCapacityExponent_ge_twenty hd ha
  have hden : 2 * t + 4 ≤ 13 + 3 * d + 3 * i := by
    unfold d2FlowCandidateCapacityExponent at he
    omega
  have hgroup : 13 + 3 * d + 3 * i = 13 + (3 * d + 3 * i) := by omega
  calc
    (d2FlowCandidateCapacity d i t : Rat) =
        (2 : Rat) ^ d2FlowCandidateCapacityExponent d i t := by
          simp [d2FlowCandidateCapacity]
    _ = (2 : Rat) ^ (13 + 3 * d + 3 * i) / (2 : Rat) ^ (2 * t + 4) := by
          simpa [d2FlowCandidateCapacityExponent] using
            (rat_two_pow_sub_eq_div hden)
    _ = 8192 * capacityD2 d i t := by
          rw [hgroup, pow_add]
          unfold capacityD2
          rw [show (8192 : Rat) = (2 : Rat) ^ 13 by norm_num]
          ring

def d2FlowCandidateActive (d t i : Nat) : Bool :=
  if t = 0 then decide (i = 0) else
  if t = 1 then decide (i = 1) else
    decide (2 ≤ t ∧ t ≤ tfD2 d ∧ i % 2 = t % 2 ∧
      3 * i + 3 * d ≥ 2 * t + 11 ∧ 3 * i < t + 8)

def d2FlowCandidateRole (d t i : Nat) : D2Role :=
  if t = 0 then .topDesc else d2ScheduleRole d i t

def d2FlowCandidateQuota (d t i : Nat) (r : D2Role) : Nat :=
  let e := d2FlowCandidateCapacityExponent d i t
  match r with
  | .topRise => 2 ^ (e - 8)
  | .mid | .botDesc => 15 * 2 ^ (e - 12)
  | .topDesc | .botRise => 0

theorem d2FlowCandidateQuota_eq_portSize {d i t : Nat} (hd : 7 ≤ d)
    (ha : active d (tfD2 d) i t) (r : D2Role) (hr : r ≠ .botRise) :
    (d2FlowCandidateQuota d t i r : Rat) =
      d2PortSize r 0 (8192 * capacityD2 d i t) := by
  have he := d2FlowCandidateCapacityExponent_ge_twenty hd ha
  have hc := d2FlowCandidateCapacity_eq hd ha
  have hc' : (2 : Rat) ^ d2FlowCandidateCapacityExponent d i t =
      8192 * capacityD2 d i t := by
    simpa [d2FlowCandidateCapacity] using hc
  cases r with
  | topDesc => simp [d2FlowCandidateQuota, d2PortSize]
  | topRise =>
      have hp := rat_two_pow_sub_eq_div
        (a := d2FlowCandidateCapacityExponent d i t) (b := 8) (by omega)
      simp only [d2FlowCandidateQuota, d2PortSize]
      calc
        ((2 ^ (d2FlowCandidateCapacityExponent d i t - 8) : Nat) : Rat) =
            (2 : Rat) ^ (d2FlowCandidateCapacityExponent d i t - 8) := by norm_cast
        _ =
            (2 : Rat) ^ d2FlowCandidateCapacityExponent d i t / 256 := by
              simpa using hp
        _ = 8192 * capacityD2 d i t / 256 := by rw [hc']
  | mid =>
      have hp := rat_two_pow_sub_eq_div
        (a := d2FlowCandidateCapacityExponent d i t) (b := 12) (by omega)
      simp only [d2FlowCandidateQuota, d2PortSize]
      calc
        ((15 * 2 ^ (d2FlowCandidateCapacityExponent d i t - 12) : Nat) : Rat) =
            15 * (2 : Rat) ^ (d2FlowCandidateCapacityExponent d i t - 12) := by
              norm_cast
        _ =
            15 * ((2 : Rat) ^ d2FlowCandidateCapacityExponent d i t / 4096) := by
              have hp' : (2 : Rat) ^
                  (d2FlowCandidateCapacityExponent d i t - 12) =
                  (2 : Rat) ^ d2FlowCandidateCapacityExponent d i t / 4096 := by
                simpa using hp
              rw [hp']
        _ = 15 * (8192 * capacityD2 d i t) / 4096 := by
              rw [hc']
              ring
  | botDesc =>
      have hp := rat_two_pow_sub_eq_div
        (a := d2FlowCandidateCapacityExponent d i t) (b := 12) (by omega)
      simp only [d2FlowCandidateQuota, d2PortSize]
      calc
        ((15 * 2 ^ (d2FlowCandidateCapacityExponent d i t - 12) : Nat) : Rat) =
            15 * (2 : Rat) ^ (d2FlowCandidateCapacityExponent d i t - 12) := by
              norm_cast
        _ =
            15 * ((2 : Rat) ^ d2FlowCandidateCapacityExponent d i t / 4096) := by
              have hp' : (2 : Rat) ^
                  (d2FlowCandidateCapacityExponent d i t - 12) =
                  (2 : Rat) ^ d2FlowCandidateCapacityExponent d i t / 4096 := by
                simpa using hp
              rw [hp']
        _ = 15 * (8192 * capacityD2 d i t) / 4096 := by
              rw [hc']
              ring
  | botRise => exact False.elim (hr rfl)

/-- The fixed candidate quota always satisfies the local `c/256` sender
cap for an ordinary scheduled role, with `c` the physical scale8192 capacity.
This removes a separate numerical premise from candidate-stage induction. -/
theorem d2FlowCandidateQuota_le_capacity_div_256 {d i t : Nat}
    (hd : 7 ≤ d) (ha : active d (tfD2 d) i t)
    (hrole : d2ScheduleRole d i t = .topRise ∨
      d2ScheduleRole d i t = .mid ∨ d2ScheduleRole d i t = .botDesc) :
    256 * d2FlowCandidateQuota d t i (d2ScheduleRole d i t) ≤
      d2FlowCandidateCapacity d i t := by
  have hc := d2FlowCandidateCapacity_eq hd ha
  cases hr : d2ScheduleRole d i t with
  | topDesc => simp [hr] at hrole
  | topRise =>
      have hquota := d2FlowCandidateQuota_eq_portSize hd ha .topRise (by decide)
      have hrat : (256 : Rat) * d2FlowCandidateQuota d t i .topRise ≤
          d2FlowCandidateCapacity d i t := by
        rw [hquota, hc]
        simp [d2PortSize]
        nlinarith
      exact_mod_cast hrat
  | mid =>
      have hquota := d2FlowCandidateQuota_eq_portSize hd ha .mid (by decide)
      have hrat : (256 : Rat) * d2FlowCandidateQuota d t i .mid ≤
          d2FlowCandidateCapacity d i t := by
        rw [hquota, hc]
        simp [d2PortSize]
        norm_num
        have hcap : 0 ≤ capacityD2 d i t := by
          unfold capacityD2
          exact div_nonneg
            (pow_nonneg (by norm_num : (0 : Rat) ≤ 2) _)
            (pow_nonneg (by norm_num : (0 : Rat) ≤ 2) _)
        nlinarith
      exact_mod_cast hrat
  | botDesc =>
      have hquota := d2FlowCandidateQuota_eq_portSize hd ha .botDesc (by decide)
      have hrat : (256 : Rat) * d2FlowCandidateQuota d t i .botDesc ≤
          d2FlowCandidateCapacity d i t := by
        rw [hquota, hc]
        simp [d2PortSize]
        norm_num
        have hcap : 0 ≤ capacityD2 d i t := by
          unfold capacityD2
          exact div_nonneg
            (pow_nonneg (by norm_num : (0 : Rat) ≤ 2) _)
            (pow_nonneg (by norm_num : (0 : Rat) ≤ 2) _)
        nlinarith
      exact_mod_cast hrat
  | botRise => simp [hr] at hrole

/-- Every regular candidate quota is even: the candidate capacity exponent
is at least20, leaving a positive power-of-two factor after either shift. -/
theorem d2FlowCandidateQuota_even {d i t : Nat}
    (hd : 7 ≤ d) (ha : active d (tfD2 d) i t) (ht : 0 < t)
    (hrole : d2ScheduleRole d i t = .topRise ∨
      d2ScheduleRole d i t = .mid ∨ d2ScheduleRole d i t = .botDesc) :
    d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) % 2 = 0 := by
  rw [show d2FlowCandidateRole d t i = d2ScheduleRole d i t by
    simp [d2FlowCandidateRole, Nat.ne_of_gt ht]]
  have he := d2FlowCandidateCapacityExponent_ge_twenty hd ha
  cases hr : d2ScheduleRole d i t with
  | topDesc => simp [hr] at hrole
  | topRise =>
      have hfactor : 2 ^ (d2FlowCandidateCapacityExponent d i t - 8) =
          2 * 2 ^ (d2FlowCandidateCapacityExponent d i t - 9) := by
        rw [show d2FlowCandidateCapacityExponent d i t - 8 =
          (d2FlowCandidateCapacityExponent d i t - 9) + 1 by omega,
          pow_succ]
        ring
      simp only [d2FlowCandidateQuota, hr]
      rw [hfactor]
      omega
  | mid =>
      have hfactor : 2 ^ (d2FlowCandidateCapacityExponent d i t - 12) =
          2 * 2 ^ (d2FlowCandidateCapacityExponent d i t - 13) := by
        rw [show d2FlowCandidateCapacityExponent d i t - 12 =
          (d2FlowCandidateCapacityExponent d i t - 13) + 1 by omega,
          pow_succ]
        ring
      simp only [d2FlowCandidateQuota, hr]
      rw [hfactor]
      omega
  | botDesc =>
      have hfactor : 2 ^ (d2FlowCandidateCapacityExponent d i t - 12) =
          2 * 2 ^ (d2FlowCandidateCapacityExponent d i t - 13) := by
        rw [show d2FlowCandidateCapacityExponent d i t - 12 =
          (d2FlowCandidateCapacityExponent d i t - 13) + 1 by omega,
          pow_succ]
        ring
      simp only [d2FlowCandidateQuota, hr]
      rw [hfactor]
      omega
  | botRise => simp [hr] at hrole

/-- One candidate D2 stage at physical row scale8192, with the exact rounded
schedule callbacks. The quota exponents encode `c/256` and `15*c/4096`;
their rational correspondence is only asserted on active schedule points. -/
def d2FlowCandidateStage (d t : Nat) (tree : D2FlowTree d) :
    D2FlowTree d :=
  d2FlowStage (d2FlowCandidateActive d t)
    (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
    d 0 tree

theorem d2FlowCandidateActive_root_at_zero (d : Nat) :
    d2FlowCandidateActive d 0 0 = true := by
  simp [d2FlowCandidateActive]

theorem d2FlowCandidateActive_nonroot_at_zero {d i : Nat} (hi : i ≠ 0) :
    d2FlowCandidateActive d 0 i = false := by
  simp [d2FlowCandidateActive, hi]

theorem d2FlowCandidateActive_matches_schedule {d t i : Nat}
    [DecidablePred (fun i : Nat => active d (tfD2 d) i t)] (ht : 0 < t) :
    d2FlowCandidateActive d t i =
      decide (active d (tfD2 d) i t) := by
  classical
  by_cases ht1 : t = 1
  · subst t
    simp [d2FlowCandidateActive, active]
  · have ht0 : t ≠ 0 := by omega
    simp [d2FlowCandidateActive, active, ht0, ht1, decide_eq_true_eq]

theorem d2FlowCandidateRole_matches_schedule {d t i : Nat} (ht : 0 < t) :
    d2FlowCandidateRole d t i = d2ScheduleRole d i t := by
  simp [d2FlowCandidateRole, Nat.ne_of_gt ht]

/-- Convert the existing normalized schedule-port inequality into the exact
integer `quota <= allocation` guard needed by the scale8192 tree step. -/
theorem d2FlowCandidateQuota_le_scaled_allocation
    {d i t allocation : Nat} (hd : 7 ≤ d)
    (hactive : active d (tfD2 d) i t) (ht : 0 < t)
    (hrole : d2ScheduleRole d i t = .topRise ∨
      d2ScheduleRole d i t = .mid ∨ d2ScheduleRole d i t = .botDesc)
    (hport : d2PortSize (d2ScheduleRole d i t)
        ((allocation : Rat) / 8192) (capacityD2 d i t) ≤
          (allocation : Rat) / 8192) :
    d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) ≤ allocation := by
  rw [d2FlowCandidateRole_matches_schedule ht]
  let r := d2ScheduleRole d i t
  have hrbot : r ≠ .botRise := by
    intro hb
    dsimp [r] at hb
    rcases hrole with htop | hmid | hbot
    · rw [htop] at hb
      cases hb
    · rw [hmid] at hb
      cases hb
    · rw [hbot] at hb
      cases hb
  have hquota := d2FlowCandidateQuota_eq_portSize hd hactive r hrbot
  dsimp [r] at hquota hport
  have hscaled : (d2FlowCandidateQuota d t i r : Rat) =
      8192 * d2PortSize r ((allocation : Rat) / 8192)
        (capacityD2 d i t) := by
    rw [hquota]
    rcases hrole with htop | hmid | hbot
    · rw [htop]
      simp [d2PortSize, r, htop]
      ring
    · rw [hmid]
      simp [d2PortSize, r, hmid]
      ring
    · rw [hbot]
      simp [d2PortSize, r, hbot]
      ring
  have hquotaLe : (d2FlowCandidateQuota d t i r : Rat) ≤ allocation := by
    rw [hscaled]
    nlinarith [hport]
  exact_mod_cast hquotaLe

theorem d2FlowCandidateActive_leaf_false {d t : Nat} (hd : 7 ≤ d)
    (ht : t ≤ tfD2 d) : d2FlowCandidateActive d t d = false := by
  classical
  by_cases ht0 : t = 0
  · subst t
    have hdi : d ≠ 0 := by omega
    simp [d2FlowCandidateActive, hdi]
  · by_cases ht1 : t = 1
    · subst t
      have hdi : d ≠ 1 := by omega
      simp [d2FlowCandidateActive, hdi]
    · have ht2 : 2 ≤ t := by omega
      have hfalse : ¬ active d (tfD2 d) d t :=
        no_active_leaf_before_tf hd ht2 ht
      have hmatch := d2FlowCandidateActive_matches_schedule
        (d := d) (t := t) (i := d) (by omega)
      rw [hmatch]
      simp [hfalse]

theorem d2FlowTreeSetRoot_deficit {h : Nat} (tree : D2FlowTree h)
    (G low high : Nat) :
    d2FlowTreeRootDeficit (d2FlowTreeSetRoot tree G low high) = G := by
  cases tree <;> rfl

theorem d2FlowStage_active_node_deficit {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true) :
    d2FlowTreeRootDeficit
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) =
      G + (match role i with
        | .topDesc => 0
        | .botRise => d2FlowTotal (fun j =>
            d2FlowTreeRootDeficit (children j)) - G
        | r => quota i r) := by
  cases hr : role i <;>
    simp [d2FlowStage, d2FlowTreeRootDeficit, ha, hr]

/-- The actual up-port charged to a subtree in one recursive stage: its
post-stage root deficit minus its old root deficit. -/
def d2FlowStagePort (active : Nat → Bool) (role : Nat → D2Role)
    (quota : Nat → D2Role → Nat) (h i : Nat) (tree : D2FlowTree h) : Nat :=
  d2FlowTreeRootDeficit (d2FlowStage active role quota h i tree) -
    d2FlowTreeRootDeficit tree

/-- Every concrete subtree stage is exactly its old deficit plus its actual
up-port. This converts the recursive tree evolution to the additive node
trace, leaving only parent overwrites to account for separately. -/
theorem d2FlowStage_root_eq_old_add_port
    (active : Nat → Bool) (role : Nat → D2Role)
    (quota : Nat → D2Role → Nat) {h : Nat} (i : Nat)
    (tree : D2FlowTree h) :
    d2FlowTreeRootDeficit (d2FlowStage active role quota h i tree) =
      d2FlowTreeRootDeficit tree + d2FlowStagePort active role quota h i tree := by
  have hmono := d2FlowStage_root_deficit_mono active role quota i tree
  unfold d2FlowStagePort
  omega

/-- After normalizing by the physical row scale8192, the concrete subtree
root update is exactly the additive single-node trace update. -/
theorem d2FlowStage_normalized_root_update
    (active : Nat → Bool) (role : Nat → D2Role)
    (quota : Nat → D2Role → Nat) {h : Nat} (i : Nat)
    (tree : D2FlowTree h) :
    (d2FlowTreeRootDeficit (d2FlowStage active role quota h i tree) : Rat) / 8192 =
      d2NodeDeficitAfterStage (active i)
        ((d2FlowTreeRootDeficit tree : Rat) / 8192)
        ((d2FlowStagePort active role quota h i tree : Rat) / 8192) := by
  have hroot := d2FlowStage_root_eq_old_add_port active role quota i tree
  have hrootRat :
      (d2FlowTreeRootDeficit (d2FlowStage active role quota h i tree) : Rat) =
        (d2FlowTreeRootDeficit tree : Rat) +
          (d2FlowStagePort active role quota h i tree : Rat) := by
    exact_mod_cast hroot
  cases ha : active i
  · have hport : d2FlowStagePort active role quota h i tree = 0 := by
      cases tree with
      | leaf G low high => simp [d2FlowStagePort, d2FlowStage, ha]
      | node G low high children =>
          simp [d2FlowStagePort, d2FlowStage, d2FlowTreeRootDeficit, ha]
    rw [hrootRat]
    simp [d2NodeDeficitAfterStage, ha, hport]
  · rw [hrootRat]
    simp [d2NodeDeficitAfterStage, ha]
    ring

/-- At an active ordinary candidate node the actual port is precisely its
fixed scheduled quota. -/
theorem d2FlowStage_regular_actual_port {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc) :
    d2FlowStagePort active role quota (h + 1) i
      (.node G low high children) = quota i (role i) := by
  unfold d2FlowStagePort
  rw [d2FlowStage_active_node_deficit children ha]
  simp only [d2FlowTreeRootDeficit]
  rcases hr with htop | hmid | hbot
  · simp [htop]
  · simp [hmid]
  · simp [hbot]

/-- At an active bottom-rise node, child-cover makes the actual port its
conservation allocation, despite natural-number subtraction in the code. -/
theorem d2FlowStage_botRise_actual_port {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true) (hr : role i = .botRise)
    (hcover : G ≤ d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j))) :
    d2FlowStagePort active role quota (h + 1) i
      (.node G low high children) =
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
  unfold d2FlowStagePort
  rw [d2FlowStage_active_node_deficit children ha, hr]
  simp only [d2FlowTreeRootDeficit]
  simp only [d2FlowTreeRootDeficit] at hcover
  omega

/-- If the eight children are saturated at a bottom-rise visit, the actual
up-port is exactly their native total minus the root deficit written by the
parent. This is the transition link behind the sharp endpoint quota
calculation. -/
theorem d2FlowStage_botRise_actual_port_of_saturated_children
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat}
    {h i G low high scale : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true) (hr : role i = .botRise)
    (hchildren : ∀ j, d2FlowTreeRootDeficit (children j) = scale * 8 ^ h)
    (hcover : G ≤ d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j))) :
    d2FlowStagePort active role quota (h + 1) i
      (.node G low high children) = scale * 8 ^ (h + 1) - G := by
  have htotal : d2FlowTotal (fun j =>
      d2FlowTreeRootDeficit (children j)) = scale * 8 ^ (h + 1) := by
    unfold d2FlowTotal
    calc
      (Finset.univ.sum fun j : Fin 8 =>
          d2FlowTreeRootDeficit (children j)) =
        Finset.univ.sum (fun _ : Fin 8 => scale * 8 ^ h) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hchildren j
      _ = scale * 8 ^ (h + 1) := by simp [Nat.pow_succ]; ring
  rw [d2FlowStage_botRise_actual_port children ha hr hcover, htotal]

/-- For the concrete candidate, the actual normalized subtree port is the
scheduled `d2PortSize`: fixed quota for ordinary roles, zero for top-descending,
and the live conservation allocation for bottom-rise. -/
theorem d2FlowCandidateStage_actual_port_eq_schedule
    {d i t h G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (hd : 7 ≤ d) (ht : 0 < t)
    (hactive : active d (tfD2 d) i t)
    (hinv : d2FlowTreeInv 8192 (.node G low high children)) :
    (d2FlowStagePort (d2FlowCandidateActive d t)
      (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
      (h + 1) i (.node G low high children) : Rat) / 8192 =
      d2PortSize (d2ScheduleRole d i t)
        ((d2FlowTreeAllocation 8192 (.node G low high children) : Rat) / 8192)
        (capacityD2 d i t) := by
  classical
  have ha : d2FlowCandidateActive d t i = true := by
    have hmatch := d2FlowCandidateActive_matches_schedule
      (d := d) (t := t) (i := i) ht
    rw [hmatch]
    simp [hactive]
  have hr : d2FlowCandidateRole d t i = d2ScheduleRole d i t :=
    d2FlowCandidateRole_matches_schedule ht
  have hcover := d2FlowTreeInv_node_children_cover children hinv
  cases hs : d2ScheduleRole d i t with
  | topDesc =>
      have hport : d2FlowStagePort (d2FlowCandidateActive d t)
          (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
          (h + 1) i (.node G low high children) = 0 := by
        unfold d2FlowStagePort
        rw [d2FlowStage_active_node_deficit children ha, hr, hs]
        simp only [d2FlowTreeRootDeficit]
        omega
      rw [hport]
      simp [d2PortSize]
  | topRise =>
      have hregular : d2FlowCandidateRole d t i = .topRise := by rw [hr, hs]
      have hport := d2FlowStage_regular_actual_port
        (active := d2FlowCandidateActive d t)
        (role := d2FlowCandidateRole d t)
        (quota := d2FlowCandidateQuota d t) (i := i) (G := G)
        (low := low) (high := high) children ha (Or.inl hregular)
      have hquota := d2FlowCandidateQuota_eq_portSize hd hactive .topRise (by decide)
      have hscaled : (d2FlowCandidateQuota d t i .topRise : Rat) / 8192 =
          d2PortSize .topRise
            ((d2FlowTreeAllocation 8192 (.node G low high children) : Rat) / 8192)
            (capacityD2 d i t) := by
        rw [hquota]
        simp [d2PortSize]
        ring
      have hport' : d2FlowStagePort (d2FlowCandidateActive d t)
          (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
          (h + 1) i (.node G low high children) =
            d2FlowCandidateQuota d t i .topRise := by
        simpa [hregular] using hport
      exact (congrArg (fun x : Nat => (x : Rat) / 8192) hport').trans hscaled
  | mid =>
      have hregular : d2FlowCandidateRole d t i = .mid := by rw [hr, hs]
      have hport := d2FlowStage_regular_actual_port
        (active := d2FlowCandidateActive d t)
        (role := d2FlowCandidateRole d t)
        (quota := d2FlowCandidateQuota d t) (i := i) (G := G)
        (low := low) (high := high) children ha (Or.inr (Or.inl hregular))
      have hquota := d2FlowCandidateQuota_eq_portSize hd hactive .mid (by decide)
      have hscaled : (d2FlowCandidateQuota d t i .mid : Rat) / 8192 =
          d2PortSize .mid
            ((d2FlowTreeAllocation 8192 (.node G low high children) : Rat) / 8192)
            (capacityD2 d i t) := by
        rw [hquota]
        simp [d2PortSize]
        ring
      have hport' : d2FlowStagePort (d2FlowCandidateActive d t)
          (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
          (h + 1) i (.node G low high children) =
            d2FlowCandidateQuota d t i .mid := by
        simpa [hregular] using hport
      exact (congrArg (fun x : Nat => (x : Rat) / 8192) hport').trans hscaled
  | botDesc =>
      have hregular : d2FlowCandidateRole d t i = .botDesc := by rw [hr, hs]
      have hport := d2FlowStage_regular_actual_port
        (active := d2FlowCandidateActive d t)
        (role := d2FlowCandidateRole d t)
        (quota := d2FlowCandidateQuota d t) (i := i) (G := G)
        (low := low) (high := high) children ha (Or.inr (Or.inr hregular))
      have hquota := d2FlowCandidateQuota_eq_portSize hd hactive .botDesc (by decide)
      have hscaled : (d2FlowCandidateQuota d t i .botDesc : Rat) / 8192 =
          d2PortSize .botDesc
            ((d2FlowTreeAllocation 8192 (.node G low high children) : Rat) / 8192)
            (capacityD2 d i t) := by
        rw [hquota]
        simp [d2PortSize]
        ring
      have hport' : d2FlowStagePort (d2FlowCandidateActive d t)
          (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
          (h + 1) i (.node G low high children) =
            d2FlowCandidateQuota d t i .botDesc := by
        simpa [hregular] using hport
      exact (congrArg (fun x : Nat => (x : Rat) / 8192) hport').trans hscaled
  | botRise =>
      have hbot : d2FlowCandidateRole d t i = .botRise := by rw [hr, hs]
      have hport := d2FlowStage_botRise_actual_port
        (active := d2FlowCandidateActive d t)
        (role := d2FlowCandidateRole d t)
        (quota := d2FlowCandidateQuota d t) (i := i) (G := G)
        (low := low) (high := high) children ha hbot hcover
      simpa [hbot, d2FlowTreeAllocation, d2FlowTotal, d2PortSize] using
        congrArg (fun x : Nat => (x : Rat) / 8192) hport

theorem d2FlowStage_mid_child_deficit {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true) (hr : role i = .mid) (j : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) =
      (d2FlowCutChild
        (d2FlowPosition (fun k => d2FlowTreeRootDeficit (children k)) j)
        (d2FlowTreeRootDeficit (children j))
        (low + quota i .mid / 2)
        (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
          high - quota i .mid / 2)).1 := by
  simp [d2FlowStage, d2FlowTreeChild, ha, hr,
    d2FlowTreeSetRoot_deficit]

/-- The concrete recursive stage preserves aggregate deficit at an active
mid node whenever its parent endpoints are balanced and its ordinary cuts
are even, in range, and noncrossing. -/
theorem d2FlowStage_mid_child_mass {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true) (hr : role i = .mid)
    (hbal : G = low + high)
    (heven : quota i .mid % 2 = 0)
    (hleft : low + quota i .mid / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hright : high + quota i .mid / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hdisjoint : low + quota i .mid / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i .mid / 2) :
    (Finset.univ.sum fun j : Fin 8 =>
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j)) = G + quota i .mid := by
  simp_rw [d2FlowStage_mid_child_deficit children ha hr]
  exact d2FlowOrdinaryCut_conserves
    (fun j => d2FlowTreeRootDeficit (children j)) G low high (quota i .mid)
    hbal heven hleft hright hdisjoint

theorem d2FlowStage_regular_child_deficit {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (j : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) =
      (d2FlowCutChild
        (d2FlowPosition (fun k => d2FlowTreeRootDeficit (children k)) j)
        (d2FlowTreeRootDeficit (children j))
        (low + quota i (role i) / 2)
        (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
          high - quota i (role i) / 2)).1 := by
  rcases hr with htop | hmid | hbot
  · simp [d2FlowStage, d2FlowTreeChild, ha, htop,
      d2FlowTreeSetRoot_deficit]
  · simp [d2FlowStage, d2FlowTreeChild, ha, hmid,
      d2FlowTreeSetRoot_deficit]
  · simp [d2FlowStage, d2FlowTreeChild, ha, hbot,
      d2FlowTreeSetRoot_deficit]

/-- Concrete form of the relaxed ordinary cut profile: the actual recursive
stage writes the two endpoint deficits and clears all six interior roots. -/
theorem d2FlowStage_regular_child_profile_tolerant
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat}
    {h i G low high a c : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hbalance : low + high = G)
    (hconserve : a + G = d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)))
    (hpiAlloc : quota i (role i) ≤ a)
    (heven : quota i (role i) = 2 * (quota i (role i) / 2))
    (hG : 4096 * G ≤ 23 * c)
    (hlow : low ≤ G) (hhigh : high ≤ G)
    (hpi : 256 * quota i (role i) ≤ c)
    (hleftReserve : c ≤ 128 * d2FlowTreeRootDeficit (children 0))
    (hrightReserve : c ≤ 128 * d2FlowTreeRootDeficit (children 7)) :
    d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) 0) = low + quota i (role i) / 2 ∧
      d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) 7) = high + quota i (role i) / 2 ∧
      ∀ j : Fin 8, 0 < j.val → j.val < 7 →
        d2FlowTreeRootDeficit
          (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j) = 0 := by
  let sizes : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
  let positions : Fin 8 → Nat := fun j => d2FlowPosition sizes j
  have hpositions := d2FlowPositions_contiguous sizes
  have hshape := d2_ordinary_update_shape_of_tolerant_reserve
    sizes positions hbalance hconserve hpiAlloc heven hG hlow hhigh hpi
    hleftReserve hrightReserve hpositions.1 hpositions.2.1 hpositions.2.2
  have hchildDeficit : ∀ j : Fin 8,
      d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) =
      d2LocalChildDeficitUpdate .mid (positions j) (sizes j)
        (low + quota i (role i) / 2)
        (d2FlowTotal sizes - high - quota i (role i) / 2) := by
    intro j
    rw [d2FlowStage_regular_child_deficit children ha hr j]
    exact d2FlowCutChild_deficit_eq_update
      (positions j) (sizes j) (low + quota i (role i) / 2)
      (d2FlowTotal sizes - high - quota i (role i) / 2)
  refine ⟨?_, ?_, ?_⟩
  · rw [hchildDeficit 0]
    exact hshape.1
  · rw [hchildDeficit 7]
    exact hshape.2.1
  · intro j hjlo hjhi
    rw [hchildDeficit j]
    exact hshape.2.2 j hjlo hjhi

/-- A tolerant ordinary sender's endpoint half-port reserve survives the
next recursive child update. With the schedule's 16-to-1 capacity ratio and
the ordinary quota floor, it supplies the reserve for the next same-level
visit. -/
theorem d2FlowStage_regular_endpoint_quota_persists
    {active childActive : Nat → Bool}
    {role childRole : Nat → D2Role}
    {quota childQuota : Nat → D2Role → Nat}
    {h i G low high allocation oldCap newCap : Nat}
    (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hbalance : low + high = G)
    (hconserve : allocation + G =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hpiAlloc : quota i (role i) ≤ allocation)
    (heven : quota i (role i) = 2 * (quota i (role i) / 2))
    (hG : 4096 * G ≤ 23 * oldCap)
    (hlow : low ≤ G) (hhigh : high ≤ G)
    (hpi : 256 * quota i (role i) ≤ oldCap)
    (hleftReserve : oldCap ≤ 128 * d2FlowTreeRootDeficit (children 0))
    (hrightReserve : oldCap ≤ 128 * d2FlowTreeRootDeficit (children 7))
    (hcap : oldCap = 16 * newCap)
    (hquota : 15 * oldCap ≤ 4096 * quota i (role i)) :
    newCap ≤ 128 * d2FlowTreeRootDeficit
        (d2FlowStage childActive childRole childQuota h (i + 1)
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) 0)) ∧
    newCap ≤ 128 * d2FlowTreeRootDeficit
        (d2FlowStage childActive childRole childQuota h (i + 1)
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) 7)) := by
  have hprofile := d2FlowStage_regular_child_profile_tolerant
    children ha hr hbalance hconserve hpiAlloc heven hG hlow hhigh hpi
    hleftReserve hrightReserve
  rcases hprofile with ⟨hfirst, hlast, _⟩
  have hquotaHalf : newCap ≤ 128 * (quota i (role i) / 2) := by
    rw [hcap, heven] at hquota
    omega
  constructor
  · have hbefore : newCap ≤ 128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) 0) := by
      rw [hfirst]
      omega
    have hmono := d2FlowStage_root_deficit_mono childActive childRole
      childQuota (i + 1)
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) 0)
    exact le_trans hbefore (Nat.mul_le_mul_left 128 hmono)
  · have hbefore : newCap ≤ 128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) 7) := by
      rw [hlast]
      omega
    have hmono := d2FlowStage_root_deficit_mono childActive childRole
      childQuota (i + 1)
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) 7)
    exact le_trans hbefore (Nat.mul_le_mul_left 128 hmono)

/-- The normalized child-deficit cap is inherited by the actual regular
stage cut, not merely by its abstract interval update. -/
theorem d2FlowStage_regular_child_g_bound_of_reserves
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat}
    {h i G low high scale c : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hinvParent : d2FlowTreeInv scale (.node G low high children))
    (hbalance : low + high = G)
    (hpiAlloc : quota i (role i) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G)
    (hG : 512 * G ≤ c)
    (hquota : 256 * quota i (role i) ≤ c)
    (heven : quota i (role i) % 2 = 0)
    (hleftReserve : c ≤ 128 *
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hrightReserve : c ≤ 128 *
      d2FlowTreeRootDeficit (children ⟨7, by omega⟩)) :
    ∀ j, 512 * d2FlowTreeRootDeficit
      (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) j) ≤ 2 * c := by
  let sizes : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
  let positions : Fin 8 → Nat := d2FlowPosition sizes
  let total : Nat := d2FlowTotal sizes
  have hcover := d2FlowTreeInv_node_children_cover children hinvParent
  have htotalCover : G ≤ total := by
    simpa [total, sizes] using hcover
  have hconserve : (total - G) + G = total := Nat.sub_add_cancel htotalCover
  have hquotaEven : quota i (role i) = 2 * (quota i (role i) / 2) := by omega
  have halloc : quota i (role i) ≤ total - G := by
    simpa [total, sizes] using hpiAlloc
  have hlow : low ≤ G := by omega
  have hhigh : high ≤ G := by omega
  have hpositions := d2FlowPositions_contiguous sizes
  have hbound := d2_ordinary_update_preserves_child_g_bound sizes positions
    hbalance hconserve halloc hquotaEven hG hlow hhigh hquota
    (by simpa [sizes] using hleftReserve)
    (by simpa [sizes] using hrightReserve)
    (by simpa [positions, sizes] using hpositions.1)
    (by simpa [positions, sizes] using hpositions.2.1)
    (by simpa [positions, sizes, total] using hpositions.2.2)
  intro j
  rw [d2FlowStage_regular_child_deficit children ha hr j]
  simp only [d2FlowCutChild_deficit_eq_update]
  simpa [sizes, positions, total] using hbound j

/-- The recursive stage-input predicate packages exactly the reserves needed
to export its ordinary sender's normalized child cap. -/
theorem d2FlowStage_regular_child_setroot {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (j : Fin 8) :
    d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) j =
      d2FlowTreeSetRoot
        (d2FlowStage active role quota h (i + 1) (children j))
        (d2FlowCutChild
          (d2FlowPosition (fun k => d2FlowTreeRootDeficit (children k)) j)
          (d2FlowTreeRootDeficit (children j))
          (low + quota i (role i) / 2)
          (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
            high - quota i (role i) / 2)).1
        (d2FlowCutChild
          (d2FlowPosition (fun k => d2FlowTreeRootDeficit (children k)) j)
          (d2FlowTreeRootDeficit (children j))
          (low + quota i (role i) / 2)
          (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
            high - quota i (role i) / 2)).2.1
        (d2FlowCutChild
          (d2FlowPosition (fun k => d2FlowTreeRootDeficit (children k)) j)
          (d2FlowTreeRootDeficit (children j))
          (low + quota i (role i) / 2)
          (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
            high - quota i (role i) / 2)).2.2 := by
  rcases hr with htop | hmid | hbot
  · simp [d2FlowStage, d2FlowTreeChild, d2FlowTreeSetRoot, ha, htop]
  · simp [d2FlowStage, d2FlowTreeChild, d2FlowTreeSetRoot, ha, hmid]
  · simp [d2FlowStage, d2FlowTreeChild, d2FlowTreeSetRoot, ha, hbot]

/-- A regular active parent may reset each immediate child's root data, but
after one inactive intermediate level its grandchild subtree is exactly the
recursive stage applied at the advanced level. -/
theorem d2FlowStage_regular_child_grandchild_stage
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree (h + 1))
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hnext : active (i + 1) = false) (j k : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 2) i
          (.node G low high children)) j) k =
    d2FlowStage active role quota h (i + 2)
      (d2FlowTreeChild (children j) k) := by
  rw [d2FlowStage_regular_child_setroot children ha hr j]
  simp only [d2FlowTreeSetRoot, d2FlowTreeChild]
  cases hchild : children j with
  | node G' low' high' grandchildren =>
      simp [d2FlowTreeSetRoot, d2FlowStage, hnext, d2FlowTreeChild]

/-- An ordinary sender writes every child's deficit as the sum of its two
end pieces, so the child endpoint-balance equation holds automatically. -/
theorem d2FlowStage_regular_child_balanced {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (j : Fin 8) :
    (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j)).2.1 +
    (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j)).2.2 =
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) := by
  rw [d2FlowStage_regular_child_setroot children ha hr j]
  rw [d2FlowTreeRootData_setRoot, d2FlowTreeSetRoot_deficit]
  rfl

/-- Every child produced by a parent stage is its own recursively updated
subtree followed by exactly one root replacement. The replacement is read
from the actual child result, covering every parent branch uniformly. -/
theorem d2FlowStage_child_decomposes {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (j : Fin 8) :
    d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) j =
      d2FlowTreeSetRoot
        (d2FlowStage active role quota h (i + 1) (children j))
        (d2FlowTreeRootData
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)).1
        (d2FlowTreeRootData
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)).2.1
        (d2FlowTreeRootData
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)).2.2 := by
  cases ha : active i with
  | false =>
      have hchild : d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j =
          d2FlowStage active role quota h (i + 1) (children j) := by
        simp [d2FlowStage, d2FlowTreeChild, ha]
      rw [hchild]
      exact (d2FlowTreeSetRoot_rootData_identity _).symm
  | true =>
      cases hr : role i with
      | topDesc =>
          have hchild : d2FlowTreeChild
              (d2FlowStage active role quota (h + 1) i
                (.node G low high children)) j =
              d2FlowTreeSetRoot
                (d2FlowStage active role quota h (i + 1) (children j)) 0 0 0 := by
            simp [d2FlowStage, d2FlowTreeChild, ha, hr]
          rw [hchild]
          simp [d2FlowTreeRootData_setRoot]
      | botRise =>
          have hchild : d2FlowTreeChild
              (d2FlowStage active role quota (h + 1) i
                (.node G low high children)) j =
              d2FlowStage active role quota h (i + 1) (children j) := by
            simp [d2FlowStage, d2FlowTreeChild, ha, hr]
          rw [hchild]
          exact (d2FlowTreeSetRoot_rootData_identity _).symm
      | topRise =>
          have hregular : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc :=
            Or.inl hr
          rw [d2FlowStage_regular_child_setroot children ha hregular j]
          simp [d2FlowTreeRootData_setRoot]
      | mid =>
          have hregular : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc :=
            Or.inr (Or.inl hr)
          rw [d2FlowStage_regular_child_setroot children ha hregular j]
          simp [d2FlowTreeRootData_setRoot]
      | botDesc =>
          have hregular : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc :=
            Or.inr (Or.inr hr)
          rw [d2FlowStage_regular_child_setroot children ha hregular j]
          simp [d2FlowTreeRootData_setRoot]

/-- A regular parent's cut overwrite preserves the full invariant of each
child subtree when the recursively stepped child is invariant, the cut fronts
do not cross, and the new root stays within its native cap. -/
theorem d2FlowStage_regular_child_inv {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high scale : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (j : Fin 8)
    (hinv : d2FlowTreeInv scale
      (d2FlowStage active role quota h (i + 1) (children j)))
    (hcuts : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
        high - quota i (role i) / 2)
    (hcap : (d2FlowCutChild
        (d2FlowPosition (fun k => d2FlowTreeRootDeficit (children k)) j)
        (d2FlowTreeRootDeficit (children j))
        (low + quota i (role i) / 2)
        (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
          high - quota i (role i) / 2)).1 ≤ scale * 8 ^ h) :
    d2FlowTreeInv scale
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) := by
  let cuts := d2FlowCutChild
    (d2FlowPosition (fun k => d2FlowTreeRootDeficit (children k)) j)
    (d2FlowTreeRootDeficit (children j))
    (low + quota i (role i) / 2)
    (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
      high - quota i (role i) / 2)
  have hcutLe : cuts.1 ≤ d2FlowTreeRootDeficit (children j) := by
    dsimp [cuts, d2FlowCutChild]
    exact d2_cuts_total_le_interval hcuts
  have hmono := d2FlowStage_root_deficit_mono active role quota
    (i + 1) (children j)
  have hle : cuts.1 ≤ d2FlowTreeRootDeficit
      (d2FlowStage active role quota h (i + 1) (children j)) :=
    le_trans hcutLe hmono
  have hbal : cuts.1 < scale * 8 ^ h → cuts.2.1 + cuts.2.2 = cuts.1 := by
    intro _
    dsimp [cuts, d2FlowCutChild]
  rw [d2FlowStage_regular_child_setroot children ha hr j]
  exact d2FlowTreeSetRoot_preserves_inv_of_lower_deficit
    (d2FlowStage active role quota h (i + 1) (children j)) hinv
    cuts.1 cuts.2.1 cuts.2.2 hcap hbal hle

/-- The same conditional aggregate conservation bridge for all three
ordinary roles used by the schedule. -/
theorem d2FlowStage_regular_child_mass {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hbal : G = low + high)
    (heven : quota i (role i) % 2 = 0)
    (hleft : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hright : high + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hdisjoint : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2) :
    (Finset.univ.sum fun j : Fin 8 =>
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j)) = G + quota i (role i) := by
  simp_rw [d2FlowStage_regular_child_deficit children ha hr]
  exact d2FlowOrdinaryCut_conserves
    (fun j => d2FlowTreeRootDeficit (children j)) G low high
    (quota i (role i)) hbal heven hleft hright hdisjoint

/-- Conditional one-stage invariant preservation for an active ordinary
node. The reserve argument supplies the parent and child native caps; the
recursive hypothesis supplies the unchanged lower subtrees. -/
theorem d2FlowStage_regular_node_inv {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high scale : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hchildren : ∀ j, d2FlowTreeInv scale
      (d2FlowStage active role quota h (i + 1) (children j)))
    (hbalance : low + high = G)
    (heven : quota i (role i) % 2 = 0)
    (hleft : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hright : high + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hdisjoint : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2)
    (hparentCap : G + quota i (role i) ≤ scale * 8 ^ (h + 1))
    (hchildCap : ∀ j, (d2FlowCutChild
        (d2FlowPosition (fun k => d2FlowTreeRootDeficit (children k)) j)
        (d2FlowTreeRootDeficit (children j))
        (low + quota i (role i) / 2)
        (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
          high - quota i (role i) / 2)).1 ≤ scale * 8 ^ h) :
    d2FlowTreeInv scale
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) := by
  have hmass := d2FlowStage_regular_child_mass children ha hr
    hbalance.symm heven hleft hright hdisjoint
  have hcoverNew : d2FlowTreeRootDeficit
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) ≤
      Finset.univ.sum (fun j : Fin 8 =>
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)) := by
    have hroot : d2FlowTreeRootDeficit
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) = G + quota i (role i) := by
      rw [d2FlowStage_active_node_deficit children ha]
      rcases hr with htop | hmid | hbot
      · simp [htop]
      · simp [hmid]
      · simp [hbot]
    rw [hroot, ← hmass]
  have hchildInv : ∀ j, d2FlowTreeInv scale
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) := by
    intro j
    exact d2FlowStage_regular_child_inv children ha hr j (hchildren j)
      hdisjoint (hchildCap j)
  have hbalanceNew : G + quota i (role i) < scale * 8 ^ (h + 1) →
      (low + quota i (role i) / 2) +
        (high + quota i (role i) - quota i (role i) / 2) =
        G + quota i (role i) := by
    intro _
    omega
  rcases hr with htop | hmid | hbot
  · simp only [d2FlowStage, d2FlowTreeInv, ha, htop]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [htop] using hparentCap
    · simpa [d2FlowStage, d2FlowTreeChild, d2FlowTreeSetRoot,
        d2FlowTreeRootDeficit, ha, htop] using hcoverNew
    · intro hlt
      have hb : G + quota i D2Role.topRise < scale * 8 ^ (h + 1) →
          (low + quota i D2Role.topRise / 2) +
            (high + quota i D2Role.topRise - quota i D2Role.topRise / 2) =
            G + quota i D2Role.topRise := by
        simpa [htop] using hbalanceNew
      exact hb hlt
    · simpa [d2FlowStage, d2FlowTreeChild, d2FlowTreeSetRoot,
        d2FlowTreeRootDeficit, ha, htop] using hchildInv
  · simp only [d2FlowStage, d2FlowTreeInv, ha, hmid]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hmid] using hparentCap
    · simpa [d2FlowStage, d2FlowTreeChild, d2FlowTreeSetRoot,
        d2FlowTreeRootDeficit, ha, hmid] using hcoverNew
    · intro hlt
      have hb : G + quota i D2Role.mid < scale * 8 ^ (h + 1) →
          (low + quota i D2Role.mid / 2) +
            (high + quota i D2Role.mid - quota i D2Role.mid / 2) =
            G + quota i D2Role.mid := by
        simpa [hmid] using hbalanceNew
      exact hb hlt
    · simpa [d2FlowStage, d2FlowTreeChild, d2FlowTreeSetRoot,
        d2FlowTreeRootDeficit, ha, hmid] using hchildInv
  · simp only [d2FlowStage, d2FlowTreeInv, ha, hbot]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hbot] using hparentCap
    · simpa [d2FlowStage, d2FlowTreeChild, d2FlowTreeSetRoot,
        d2FlowTreeRootDeficit, ha, hbot] using hcoverNew
    · intro hlt
      have hb : G + quota i D2Role.botDesc < scale * 8 ^ (h + 1) →
          (low + quota i D2Role.botDesc / 2) +
            (high + quota i D2Role.botDesc - quota i D2Role.botDesc / 2) =
            G + quota i D2Role.botDesc := by
        simpa [hbot] using hbalanceNew
      exact hb hlt
    · simpa [d2FlowStage, d2FlowTreeChild, d2FlowTreeSetRoot,
        d2FlowTreeRootDeficit, ha, hbot] using hchildInv

/-- The established local reserve theorem discharges the native-cap
hypotheses of ordinary one-stage preservation. -/
theorem d2FlowStage_regular_node_inv_of_reserves {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high scale c : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hinvParent : d2FlowTreeInv scale (.node G low high children))
    (hchildren : ∀ j, d2FlowTreeInv scale
      (d2FlowStage active role quota h (i + 1) (children j)))
    (hbalance : low + high = G)
    (hpiAlloc : quota i (role i) ≤ d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) - G)
    (hG : 512 * G ≤ c)
    (hquota : 256 * quota i (role i) ≤ c)
    (heven : quota i (role i) % 2 = 0)
    (hleftReserve : c ≤ 128 *
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hrightReserve : c ≤ 128 *
      d2FlowTreeRootDeficit (children ⟨7, by omega⟩)) :
    d2FlowTreeInv scale
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) := by
  let sizes : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
  let positions : Fin 8 → Nat := d2FlowPosition sizes
  let total : Nat := d2FlowTotal sizes
  have hcover := d2FlowTreeInv_node_children_cover children hinvParent
  have hchildrenOld : ∀ j, d2FlowTreeInv scale (children j) := by
    have hinv' := hinvParent
    simp only [d2FlowTreeInv] at hinv'
    exact hinv'.2.2.2
  have hchildNative : ∀ j, sizes j ≤ scale * 8 ^ h := by
    intro j
    exact d2FlowTreeInv_root_native_bound (children j) (hchildrenOld j)
  have htotalCover : G ≤ total := by
    simpa [total, sizes] using hcover
  have hconserve : (total - G) + G = Finset.univ.sum sizes := by
    simpa [total, d2FlowTotal] using Nat.sub_add_cancel htotalCover
  have hQuotaEven : quota i (role i) = 2 * (quota i (role i) / 2) := by
    omega
  have hpiAlloc' : quota i (role i) ≤ total - G := by
    simpa [total, sizes] using hpiAlloc
  have hlow : low ≤ G := by omega
  have hhigh : high ≤ G := by omega
  have hfronts := d2_ordinary_cut_fronts_valid
    (a := total - G) (G := G) (total := total)
    (low := low) (high := high) (pi := quota i (role i))
    (half := quota i (role i) / 2)
    (Uleft := sizes ⟨0, by omega⟩) (Uright := sizes ⟨7, by omega⟩)
    (c := c) hbalance hconserve hpiAlloc' hQuotaEven hG hlow hhigh hquota
    (by simpa [sizes] using hleftReserve)
    (by simpa [sizes] using hrightReserve)
  have hleftTotal : low + quota i (role i) / 2 ≤ total :=
    le_trans hfronts.2.1 (d2FlowSize_le_total sizes ⟨0, by omega⟩)
  have hrightTotal : high + quota i (role i) / 2 ≤ total :=
    le_trans hfronts.2.2 (d2FlowSize_le_total sizes ⟨7, by omega⟩)
  have hpositions := d2FlowPositions_contiguous sizes
  have hlocal := d2_ordinary_local_invariant_step
    (a := total - G) (G := G) (total := total)
    (low := low) (high := high) (pi := quota i (role i))
    (half := quota i (role i) / 2) (c := c)
    (childNative := scale * 8 ^ h) sizes positions
    rfl hconserve hbalance hpiAlloc'
    hchildNative hG hlow hhigh hquota hQuotaEven hleftReserve hrightReserve
    (by simpa [positions, sizes] using hpositions.1)
    (by simpa [positions, sizes] using hpositions.2.1)
    (by simpa [positions, sizes, total] using hpositions.2.2)
  have hparentCap : G + quota i (role i) ≤ scale * 8 ^ (h + 1) := by
    calc
      G + quota i (role i) ≤ 8 * (scale * 8 ^ h) := hlocal.2.1
      _ = scale * 8 ^ (h + 1) := by rw [Nat.pow_succ]; ring
  have hchildCap : ∀ j, (d2FlowCutChild
      (d2FlowPosition sizes j) (sizes j)
      (low + quota i (role i) / 2)
      (total - high - quota i (role i) / 2)).1 ≤ scale * 8 ^ h := by
    intro j
    have hj := hlocal.2.2.1 j
    simpa only [d2FlowCutChild_deficit_eq_update] using hj
  exact d2FlowStage_regular_node_inv children ha hr hchildren hbalance
    heven (by simpa [sizes, total] using hleftTotal)
    (by simpa [sizes, total] using hrightTotal)
    (by simpa [sizes, total] using hfronts.1)
    hparentCap (by simpa [sizes, total] using hchildCap)

/-- Relaxed-cap counterpart of the ordinary node invariant step. The
`23/4096` parent budget still contains both cut fronts in the reserved end
children; native-cap preservation then follows from cut disjointness and
allocation conservation. -/
theorem d2FlowStage_regular_node_inv_of_tolerant_reserves
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat}
    {h i G low high scale cap : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hinvParent : d2FlowTreeInv scale (.node G low high children))
    (hchildren : ∀ j, d2FlowTreeInv scale
      (d2FlowStage active role quota h (i + 1) (children j)))
    (hbalance : low + high = G)
    (halloc : quota i (role i) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G)
    (hG : 4096 * G ≤ 23 * cap)
    (hquota : 256 * quota i (role i) ≤ cap)
    (heven : quota i (role i) % 2 = 0)
    (hleftReserve : cap ≤ 128 * d2FlowTreeRootDeficit
      (children ⟨0, by omega⟩))
    (hrightReserve : cap ≤ 128 * d2FlowTreeRootDeficit
      (children ⟨7, by omega⟩)) :
    d2FlowTreeInv scale
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) := by
  let sizes : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
  let positions : Fin 8 → Nat := d2FlowPosition sizes
  let total : Nat := d2FlowTotal sizes
  have hcover := d2FlowTreeInv_node_children_cover children hinvParent
  have hchildrenOld : ∀ j, d2FlowTreeInv scale (children j) := by
    have hinv' := hinvParent
    simp only [d2FlowTreeInv] at hinv'
    exact hinv'.2.2.2
  have hchildNative : ∀ j, sizes j ≤ scale * 8 ^ h := by
    intro j
    exact d2FlowTreeInv_root_native_bound (children j) (hchildrenOld j)
  have hconserve : (total - G) + G = Finset.univ.sum sizes := by
    have hsum : total = Finset.univ.sum sizes := by simp [total, d2FlowTotal]
    rw [hsum]
    exact Nat.sub_add_cancel (by simpa [total, sizes] using hcover)
  have hpiAlloc : quota i (role i) ≤ total - G := by
    simpa [total, sizes] using halloc
  have hquotaEven : quota i (role i) = 2 * (quota i (role i) / 2) := by omega
  have hlow : low ≤ G := by omega
  have hhigh : high ≤ G := by omega
  have hdisjoint := d2_cut_fronts_noncrossing hbalance hconserve
    hpiAlloc hquotaEven
  have hends := d2_endpoint_fronts_fit_of_tolerant_reserve
    hG hlow hhigh hquota hquotaEven
    (by simpa [sizes] using hleftReserve)
    (by simpa [sizes] using hrightReserve)
  have hleftTotal : low + quota i (role i) / 2 ≤ total :=
    le_trans hends.1 (d2FlowSize_le_total sizes ⟨0, by omega⟩)
  have hrightTotal : high + quota i (role i) / 2 ≤ total :=
    le_trans hends.2 (d2FlowSize_le_total sizes ⟨7, by omega⟩)
  have hpositions := d2FlowPositions_contiguous sizes
  have hnative := d2_local_update_preserves_native (role := .mid)
    sizes positions (low + quota i (role i) / 2)
    (total - high - quota i (role i) / 2)
    hconserve hpiAlloc hchildNative hdisjoint
  have hparentCap : G + quota i (role i) ≤ scale * 8 ^ (h + 1) := by
    calc
      G + quota i (role i) ≤ 8 * (scale * 8 ^ h) := hnative.1
      _ = scale * 8 ^ (h + 1) := by rw [Nat.pow_succ]; ring
  have hchildCap : ∀ j, (d2FlowCutChild (positions j) (sizes j)
      (low + quota i (role i) / 2)
      (total - high - quota i (role i) / 2)).1 ≤ scale * 8 ^ h := by
    intro j
    have hj := hnative.2 j
    simpa only [d2FlowCutChild_deficit_eq_update] using hj
  exact d2FlowStage_regular_node_inv children ha hr hchildren hbalance heven
    (by simpa [sizes, total] using hleftTotal)
    (by simpa [sizes, total] using hrightTotal)
    (by simpa [sizes, total] using hdisjoint)
    hparentCap (by simpa [sizes, total, positions] using hchildCap)

/-- Compose the ordinary local invariant step with the exact candidate quota
and role callbacks. Its only allocation-side premise is the normalized
schedule-port inequality, which may be supplied by the existing two-step
sender theorem. -/
theorem d2FlowCandidateStage_regular_node_inv_of_reserves
    {d i t h G low high c : Nat}
    (children : Fin 8 → D2FlowTree h)
    (hd : 7 ≤ d) (ht : 0 < t)
    (hactive : active d (tfD2 d) i t)
    (hrole : d2ScheduleRole d i t = .topRise ∨
      d2ScheduleRole d i t = .mid ∨ d2ScheduleRole d i t = .botDesc)
    (hinvParent : d2FlowTreeInv 8192 (.node G low high children))
    (hchildren : ∀ j, d2FlowTreeInv 8192
      (d2FlowStage (d2FlowCandidateActive d t)
        (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
        h (i + 1) (children j)))
    (hbalance : low + high = G)
    (hG : 512 * G ≤ c)
    (hcapacity : c = d2FlowCandidateCapacity d i t)
    (hleftReserve : c ≤ 128 *
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hrightReserve : c ≤ 128 *
      d2FlowTreeRootDeficit (children ⟨7, by omega⟩))
    (hport : d2PortSize (d2ScheduleRole d i t)
        ((d2FlowTreeAllocation 8192 (.node G low high children) : Rat) / 8192)
        (capacityD2 d i t) ≤
          (d2FlowTreeAllocation 8192 (.node G low high children) : Rat) / 8192) :
    d2FlowTreeInv 8192
      (d2FlowStage (d2FlowCandidateActive d t)
        (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
        (h + 1) i (.node G low high children)) := by
  classical
  have ha : d2FlowCandidateActive d t i = true := by
    have hmatch := d2FlowCandidateActive_matches_schedule
      (d := d) (t := t) (i := i) ht
    rw [hmatch]
    simp [hactive]
  have hr : d2FlowCandidateRole d t i = d2ScheduleRole d i t :=
    d2FlowCandidateRole_matches_schedule ht
  have hquotaAlloc := d2FlowCandidateQuota_le_scaled_allocation
    hd hactive ht hrole hport
  have hquotaAlloc' : d2FlowCandidateQuota d t i
      (d2FlowCandidateRole d t i) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
    simpa [d2FlowTreeAllocation, d2FlowTotal] using hquotaAlloc
  have hroleCandidate : d2FlowCandidateRole d t i = .topRise ∨
      d2FlowCandidateRole d t i = .mid ∨
      d2FlowCandidateRole d t i = .botDesc := by
    simpa [hr] using hrole
  have hquotaCap : 256 * d2FlowCandidateQuota d t i
      (d2FlowCandidateRole d t i) ≤ c := by
    rw [hr, hcapacity]
    exact d2FlowCandidateQuota_le_capacity_div_256 hd hactive hrole
  have hquotaEven := d2FlowCandidateQuota_even hd hactive ht hrole
  exact d2FlowStage_regular_node_inv_of_reserves children ha hroleCandidate
    hinvParent hchildren hbalance hquotaAlloc' hG
    hquotaCap hquotaEven
    (by simpa [hr] using hleftReserve)
    (by simpa [hr] using hrightReserve)

theorem d2FlowStage_topDesc_child_deficit {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true) (hr : role i = .topDesc) (j : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) = 0 := by
  simp [d2FlowStage, d2FlowTreeChild, ha, hr,
    d2FlowTreeSetRoot_deficit]

/-- A top-descending sender resets all three stored child-root fields to zero. -/
theorem d2FlowStage_topDesc_child_rootdata {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true) (hr : role i = .topDesc) (j : Fin 8) :
    d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) = (0, 0, 0) := by
  simp [d2FlowStage, d2FlowTreeChild, ha, hr,
    d2FlowTreeRootData_setRoot]

/-- `topDesc` satisfies aggregate conservation exactly when the executable
branch's required zero-parent-deficit condition holds. -/
theorem d2FlowStage_topDesc_child_mass {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true) (hr : role i = .topDesc) (hG : G = 0) :
    (Finset.univ.sum fun j : Fin 8 =>
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j)) =
      d2FlowTreeRootDeficit
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) := by
  simp [d2FlowStage_topDesc_child_deficit children ha hr,
    d2FlowStage_active_node_deficit children ha, hr, hG]

theorem d2FlowStage_botRise_child_deficit {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true) (hr : role i = .botRise) (j : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) =
      d2FlowTreeRootDeficit
        (d2FlowStage active role quota h (i + 1) (children j)) := by
  simp [d2FlowStage, d2FlowTreeChild, ha, hr,
    d2FlowTreeRootDeficit]

/-- Deficit that the parent cut would write into child `j` at this stage.
For `topDesc` and `botRise` this value is ignored by their distinct branches. -/
def d2FlowStageParentCutChildDeficit {h i G low high : Nat}
    (children : Fin 8 → D2FlowTree h) (role : Nat → D2Role)
    (quota : Nat → D2Role → Nat) (j : Fin 8) : Nat :=
  let sizes := fun k => d2FlowTreeRootDeficit (children k)
  let total := d2FlowTotal sizes
  match role i with
  | .topDesc => 0
  | r =>
      let pi := if r = .botRise then total - G else quota i r
      (d2FlowCutChild (d2FlowPosition sizes j) (sizes j)
        (low + pi / 2) (total - high - pi / 2)).1

/-- The parent's one-stage action on a recursively updated child root. -/
def d2FlowChildAfterParentStage (parentActive : Bool) (parentRole : D2Role)
    (selfUpdated cutUpdated : Nat) : Nat :=
  if parentActive then
    match parentRole with
    | .topDesc => 0
    | .botRise => selfUpdated
    | .topRise | .mid | .botDesc => cutUpdated
  else selfUpdated

/-- Exact one-stage projection from the recursive tree update to the two
sources of a child's deficit history: its own recursive update, followed by
the parent overwrite (clear, preserve, or ordinary cut). This is the concrete
adapter needed to instantiate `d2ChildDeficitTrace` on actual trees. -/
theorem d2FlowStage_child_root_parent_recurrence {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h) (j : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) =
      d2FlowChildAfterParentStage (active i) (role i)
        (d2FlowTreeRootDeficit
          (d2FlowStage active role quota h (i + 1) (children j)))
        (d2FlowStageParentCutChildDeficit (i := i) (G := G)
          (low := low) (high := high) children role quota j) := by
  cases hactive : active i with
  | false =>
      simp [d2FlowStage, d2FlowTreeChild, d2FlowChildAfterParentStage,
        hactive]
  | true =>
      cases hrole : role i with
      | topDesc =>
          simp [d2FlowStage, d2FlowTreeChild,
            d2FlowChildAfterParentStage, hactive, hrole,
            d2FlowTreeSetRoot_deficit]
      | botRise =>
          simp [d2FlowStage, d2FlowTreeChild,
            d2FlowChildAfterParentStage, hactive, hrole,
            d2FlowTreeRootDeficit]
      | topRise =>
          rw [d2FlowStage_regular_child_deficit children hactive (Or.inl hrole) j]
          simp [d2FlowChildAfterParentStage, hactive, hrole,
            d2FlowStageParentCutChildDeficit]
      | mid =>
          rw [d2FlowStage_regular_child_deficit children hactive
            (Or.inr (Or.inl hrole)) j]
          simp [d2FlowChildAfterParentStage, hactive, hrole,
            d2FlowStageParentCutChildDeficit]
      | botDesc =>
          rw [d2FlowStage_regular_child_deficit children hactive
            (Or.inr (Or.inr hrole)) j]
          simp [d2FlowChildAfterParentStage, hactive, hrole,
            d2FlowStageParentCutChildDeficit]

/-- The one-step parent/child recurrence, normalized at row scale8192, is
exactly the abstract `d2ChildDeficitAfterStage` used by the two-stage reserve
and sender lemmas. Its ports and cut values are extracted from the concrete
recursive tree transition. -/
theorem d2FlowStage_normalized_child_parent_recurrence
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high : Nat}
    (children : Fin 8 → D2FlowTree h) (j : Fin 8) :
    (d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) : Rat) / 8192 =
      d2ChildDeficitAfterStage (active (i + 1)) (active i) (role i)
        ((d2FlowTreeRootDeficit (children j) : Rat) / 8192)
        ((d2FlowStagePort active role quota h (i + 1) (children j) : Rat) / 8192)
        ((d2FlowStageParentCutChildDeficit (i := i) (G := G)
          (low := low) (high := high) children role quota j : Rat) / 8192) := by
  have hparent := d2FlowStage_child_root_parent_recurrence
    (active := active) (role := role) (quota := quota) (i := i)
    (G := G) (low := low) (high := high) children j
  have hparentRat :
      (d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j) : Rat) / 8192 =
        (d2FlowChildAfterParentStage (active i) (role i)
          (d2FlowTreeRootDeficit
            (d2FlowStage active role quota h (i + 1) (children j)))
          (d2FlowStageParentCutChildDeficit (i := i) (G := G)
            (low := low) (high := high) children role quota j) : Rat) / 8192 := by
    exact_mod_cast congrArg (fun n : Nat => (n : Rat) / 8192) hparent
  have hself := d2FlowStage_normalized_root_update active role quota
    (i + 1) (children j)
  rw [hparentRat]
  cases ha : active i <;> cases hr : role i <;>
    simp [d2FlowChildAfterParentStage, d2ChildDeficitAfterStage,
      d2FlowStageParentCutChildDeficit, ha, hr, hself]

/-- A local subtree history allows an arbitrary root overwrite after each
recursive stage. This models the effect of its own parent cut: ancestors can
replace this subtree's root, while its descendants retain the recursive
stage result. -/
def d2FlowTreeRunWithParentOverwrites {h : Nat}
    (initial : D2FlowTree h) (i : Nat)
    (active : Nat → Nat → Bool) (role : Nat → Nat → D2Role)
    (quota : Nat → Nat → D2Role → Nat)
    (overwrite : Nat → Nat × Nat × Nat) : Nat → D2FlowTree h
  | 0 => initial
  | n + 1 =>
      let stepped := d2FlowStage (active n) (role n) (quota n)
        h i (d2FlowTreeRunWithParentOverwrites initial i
          active role quota overwrite n)
      let root := overwrite n
      d2FlowTreeSetRoot stepped root.1 root.2.1 root.2.2

theorem d2FlowTreeChild_setRoot {h : Nat} (tree : D2FlowTree (h + 1))
    (G low high : Nat) (j : Fin 8) :
    d2FlowTreeChild (d2FlowTreeSetRoot tree G low high) j =
      d2FlowTreeChild tree j := by
  cases tree <;> rfl

/-- Any parent action only resets its immediate child's root data. Therefore
projecting one more level commutes with the stage, without assumptions on the
active pattern or sender role. -/
theorem d2FlowStage_child_child_projection
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat}
    {h i : Nat} (tree : D2FlowTree (h + 2))
    (j k : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 2) i tree) j) k =
    d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) (i + 1)
        (d2FlowTreeChild tree j)) k := by
  cases tree with
  | node G low high children =>
      have hdecomp := d2FlowStage_child_decomposes
        (active := active) (role := role) (quota := quota)
        (h := h + 1) (i := i) (G := G) (low := low) (high := high)
        children j
      have hproject :=
        congrArg (fun subtree => d2FlowTreeChild subtree k) hdecomp
      change d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 2) i
              (.node G low high children)) j) k =
        d2FlowTreeChild
          (d2FlowTreeSetRoot
            (d2FlowStage active role quota (h + 1) (i + 1) (children j))
            _ _ _) k at hproject
      rw [d2FlowTreeChild_setRoot] at hproject
      exact hproject

/-- A five-edge path through a staged tree reduces to the last child action
at its level-four ancestor. This makes precise that earlier parent root
overwrites cannot affect the reserve stored at the level-five endpoint. -/
theorem d2FlowStage_path5_projection
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i : Nat}
    (tree : D2FlowTree (h + 5)) (j k m l q : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowStage active role quota (h + 5) i tree) j) k) m) l) q) =
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) (i + 4)
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild tree j) k) m) l)) q) := by
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]

/-- Six-edge root projection, leaving the final child action at its level-five
ancestor. This exposes level-six native reserves across sparse frontiers. -/
theorem d2FlowStage_path6_projection
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i : Nat}
    (tree : D2FlowTree (h + 6)) (j k m l q s : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowStage active role quota (h + 6) i tree) j) k) m) l) q) s) =
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) (i + 5)
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild tree j) k) m) l) q)) s) := by
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]

/-- Three-edge projection: the level-three child after a stage is produced
by the stage recursively applied at its level-two ancestor. -/
theorem d2FlowStage_path3_projection
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i : Nat}
    (tree : D2FlowTree (h + 3)) (j k m : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 3) i tree) j) k) m =
    d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) (i + 2)
        (d2FlowTreeChild (d2FlowTreeChild tree j) k)) m := by
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]

/-- Four-edge projection: the level-four subtree after a stage is the level
four child produced by the stage recursively applied at its level-three
ancestor. -/
theorem d2FlowStage_path4_projection
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i : Nat}
    (tree : D2FlowTree (h + 4)) (j k m l : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 4) i tree) j) k) m) l =
    d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) (i + 3)
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild tree j) k) m)) l := by
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]

/-- Projecting two levels through a parent stage gives the grandchild stage
call whenever the intermediate level is inactive. -/
theorem d2FlowStage_child_child_of_inactive
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree (h + 1))
    (hinactive : active (i + 1) = false) (j k : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 2) i
          (.node G low high children)) j) k =
      d2FlowStage active role quota h (i + 2)
        (d2FlowTreeChild (children j) k) := by
  have hdecomp := d2FlowStage_child_decomposes
    (active := active) (role := role) (quota := quota)
    (h := h + 1) (i := i) (G := G) (low := low) (high := high)
    children j
  have hproject := congrArg (fun subtree => d2FlowTreeChild subtree k) hdecomp
  change d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 2) i
          (.node G low high children)) j) k =
    d2FlowTreeChild
      (d2FlowTreeSetRoot
        (d2FlowStage active role quota (h + 1) (i + 1) (children j)) _ _ _) k
    at hproject
  rw [d2FlowTreeChild_setRoot] at hproject
  cases hchild : children j with
  | node G' low' high' grandchildren =>
      rw [hchild] at hproject
      rw [d2FlowStage_inactive_child grandchildren hinactive k] at hproject
      simpa only [d2FlowTreeChild] using hproject

/-- A regular parent cut changes the child root by its cut, while two
inactive schedule levels below it preserve each grandchild's root deficit. -/
theorem d2FlowStage_regular_child_grandchild_deficit
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree (h + 1))
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hnext : active (i + 1) = false)
    (hnextnext : active (i + 2) = false) (j k : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 2) i
            (.node G low high children)) j) k) =
      d2FlowTreeRootDeficit (d2FlowTreeChild (children j) k) := by
  rw [d2FlowStage_regular_child_setroot children ha hr j]
  rw [d2FlowTreeChild_setRoot]
  cases hchild : children j with
  | node G' low' high' grandchildren =>
      rw [d2FlowStage_inactive_child grandchildren hnext k]
      have hroot := d2FlowStage_root_deficit_of_inactive
        (active := active) (role := role) (quota := quota)
        (h := h) (i := i + 2) (d2FlowTreeChild (children j) k) hnextnext
      rw [hchild] at hroot
      simpa only [d2FlowTreeChild] using hroot

theorem d2FlowTreeSetRoot_node {h : Nat} (tree : D2FlowTree (h + 1))
    (G low high : Nat) :
    d2FlowTreeSetRoot tree G low high =
      .node G low high (fun j => d2FlowTreeChild tree j) := by
  cases tree <;> rfl

def d2FlowTreeChildOverwrite {h i : Nat}
    (parent : Nat → D2FlowTree (h + 1))
    (active : Nat → Nat → Bool) (role : Nat → Nat → D2Role)
    (quota : Nat → Nat → D2Role → Nat) (j : Fin 8) :
    Nat → Nat × Nat × Nat := fun n =>
  d2FlowTreeRootData
    (d2FlowTreeChild
      (d2FlowStage (active n) (role n) (quota n) (h + 1) i (parent n)) j)

/-- Projecting a child from any subtree history with parent overwrites yields
another history of the same form. The child-stage callbacks advance its level,
and its parent overwrite is exactly the root data written by the concrete
parent stage. Iterating this theorem covers every path from the full root. -/
theorem d2FlowTreeRun_child_as_history {h i : Nat}
    (initial : D2FlowTree (h + 1))
    (active : Nat → Nat → Bool) (role : Nat → Nat → D2Role)
    (quota : Nat → Nat → D2Role → Nat)
    (overwrite : Nat → Nat × Nat × Nat) (j : Fin 8) (n : Nat) :
    d2FlowTreeChild
      (d2FlowTreeRunWithParentOverwrites initial i active role quota
        overwrite n) j =
      d2FlowTreeRunWithParentOverwrites (d2FlowTreeChild initial j) (i + 1)
        active role quota
        (d2FlowTreeChildOverwrite
          (fun k => d2FlowTreeRunWithParentOverwrites initial i active role quota
            overwrite k) (i := i) active role quota j) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change d2FlowTreeChild
          (d2FlowTreeSetRoot
            (d2FlowStage (active n) (role n) (quota n) (h + 1) i
              (d2FlowTreeRunWithParentOverwrites initial i active role quota
                overwrite n))
            (overwrite n).1 (overwrite n).2.1 (overwrite n).2.2) j =
        d2FlowTreeSetRoot
          (d2FlowStage (active n) (role n) (quota n) h (i + 1)
            (d2FlowTreeRunWithParentOverwrites (d2FlowTreeChild initial j)
              (i + 1) active role quota
              (d2FlowTreeChildOverwrite
                (fun k => d2FlowTreeRunWithParentOverwrites initial i active role quota
                  overwrite k) (i := i) active role quota j) n))
          (d2FlowTreeChildOverwrite
            (fun k => d2FlowTreeRunWithParentOverwrites initial i active role quota
              overwrite k) (i := i) active role quota j n).1
          (d2FlowTreeChildOverwrite
            (fun k => d2FlowTreeRunWithParentOverwrites initial i active role quota
              overwrite k) (i := i) active role quota j n).2.1
          (d2FlowTreeChildOverwrite
            (fun k => d2FlowTreeRunWithParentOverwrites initial i active role quota
              overwrite k) (i := i) active role quota j n).2.2
      rw [d2FlowTreeChild_setRoot]
      cases ht : d2FlowTreeRunWithParentOverwrites initial i active role quota
          overwrite n with
      | node G low high children =>
          rw [d2FlowStage_child_decomposes]
          simp only [d2FlowTreeChildOverwrite]
          rw [← ih]
          rw [ht]
          rfl

/-- A finite path selects one subtree at each level. -/
inductive D2FlowPath : Nat → Type
  | nil : D2FlowPath 0
  | cons {n : Nat} (j : Fin 8) (tail : D2FlowPath n) :
      D2FlowPath (n + 1)

/-- Project a tree to the subtree selected by a path. -/
def d2FlowTreeAtPath {h : Nat} : (n : Nat) →
    D2FlowTree (h + n) → D2FlowPath n → D2FlowTree h
  | 0, tree, .nil => tree
  | n + 1, tree, .cons j tail =>
      d2FlowTreeAtPath n (d2FlowTreeChild tree j) tail

/-- The subtree history along a path is again a recursive history, with each
ancestor's concrete root overwrite passed down one level. -/
def d2FlowTreePathHistory {h : Nat} : (n : Nat) →
    (initial : D2FlowTree (h + n)) → (path : D2FlowPath n) →
    (i : Nat) → (active : Nat → Nat → Bool) →
    (role : Nat → Nat → D2Role) →
    (quota : Nat → Nat → D2Role → Nat) →
    (overwrite : Nat → Nat × Nat × Nat) → Nat → D2FlowTree h
  | 0, initial, .nil, i, active, role, quota, overwrite, n =>
      d2FlowTreeRunWithParentOverwrites initial i active role quota overwrite n
  | depth + 1, initial, .cons j tail, i, active, role, quota, overwrite, n =>
      d2FlowTreePathHistory depth (d2FlowTreeChild initial j) tail (i + 1)
        active role quota
        (d2FlowTreeChildOverwrite
          (fun k => d2FlowTreeRunWithParentOverwrites initial i active role
            quota overwrite k) (i := i) active role quota j) n

/-- The selected node of a path, together with the level and overwrite
callback that describe its complete local history. Keeping this context
explicit lets trace lemmas be applied at any depth, rather than only at the
root or its immediate children. -/
structure D2FlowPathContext (h : Nat) where
  initial : D2FlowTree h
  level : Nat
  overwrite : Nat → Nat × Nat × Nat

def d2FlowTreePathContext {h : Nat} : (n : Nat) →
    (initial : D2FlowTree (h + n)) → (path : D2FlowPath n) →
    (i : Nat) → (active : Nat → Nat → Bool) →
    (role : Nat → Nat → D2Role) →
    (quota : Nat → Nat → D2Role → Nat) →
    (overwrite : Nat → Nat × Nat × Nat) → D2FlowPathContext h
  | 0, initial, .nil, i, _active, _role, _quota, overwrite =>
      ⟨initial, i, overwrite⟩
  | depth + 1, initial, .cons j tail, i, active, role, quota, overwrite =>
      d2FlowTreePathContext depth (d2FlowTreeChild initial j) tail (i + 1)
        active role quota
        (d2FlowTreeChildOverwrite
          (fun k => d2FlowTreeRunWithParentOverwrites initial i active role
            quota overwrite k) (i := i) active role quota j)

theorem d2FlowTreePathHistory_eq_context_run {h n : Nat}
    (initial : D2FlowTree (h + n)) (path : D2FlowPath n) (i : Nat)
    (active : Nat → Nat → Bool) (role : Nat → Nat → D2Role)
    (quota : Nat → Nat → D2Role → Nat)
    (overwrite : Nat → Nat × Nat × Nat) (step : Nat) :
    d2FlowTreePathHistory n initial path i active role quota overwrite step =
      d2FlowTreeRunWithParentOverwrites
        (d2FlowTreePathContext n initial path i active role quota overwrite).initial
        (d2FlowTreePathContext n initial path i active role quota overwrite).level
        active role quota
        (d2FlowTreePathContext n initial path i active role quota overwrite).overwrite
        step := by
  induction path generalizing i overwrite step with
  | nil => rfl
  | @cons depth j tail ih =>
      simp only [d2FlowTreePathHistory, d2FlowTreePathContext]
      exact ih (initial := d2FlowTreeChild initial j) (i := i + 1)
        (overwrite := d2FlowTreeChildOverwrite
          (fun k => d2FlowTreeRunWithParentOverwrites initial i active role
            quota overwrite k) (i := i) active role quota j)
        (step := step)

/-- Arbitrary-depth path projection commutes with the concrete run: the
selected subtree is exactly the recursively constructed history with all
ancestor overwrites included. -/
theorem d2FlowTreeRun_path_as_history {h n : Nat}
    (initial : D2FlowTree (h + n)) (path : D2FlowPath n) (i : Nat)
    (active : Nat → Nat → Bool) (role : Nat → Nat → D2Role)
    (quota : Nat → Nat → D2Role → Nat)
    (overwrite : Nat → Nat × Nat × Nat) (step : Nat) :
    d2FlowTreeAtPath n
      (d2FlowTreeRunWithParentOverwrites initial i active role quota
        overwrite step) path =
    d2FlowTreePathHistory n initial path i active role quota overwrite step := by
  induction path generalizing i overwrite step with
  | nil => simp [d2FlowTreeAtPath, d2FlowTreePathHistory]
  | @cons depth j tail ih =>
      change d2FlowTreeAtPath depth
          (d2FlowTreeChild
            (d2FlowTreeRunWithParentOverwrites initial i active role quota
              overwrite step) j) tail = _
      rw [d2FlowTreeRun_child_as_history]
      exact ih (initial := d2FlowTreeChild initial j) (i := i + 1)
        (overwrite := d2FlowTreeChildOverwrite
          (fun k => d2FlowTreeRunWithParentOverwrites initial i active role
            quota overwrite k) (i := i) active role quota j) (step := step)

/-- The candidate's concrete full-tree evolution. The iteration counter is
zero-based and step 
+1` uses candidate stage 
`, including the bootstrap. -/
def d2FlowCandidateRun (d : Nat) (initial : D2FlowTree d) :
    Nat -> D2FlowTree d
  | 0 => initial
  | n + 1 => d2FlowCandidateStage d n
      (d2FlowCandidateRun d initial n)

def d2FlowCandidateRunActive (d : Nat) : Nat -> Nat -> Bool :=
  fun n i => d2FlowCandidateActive d n i

def d2FlowCandidateRunRole (d : Nat) : Nat -> Nat -> D2Role :=
  fun n i => d2FlowCandidateRole d n i

def d2FlowCandidateRunQuota (d : Nat) :
    Nat -> Nat -> D2Role -> Nat :=
  fun n i r => d2FlowCandidateQuota d n i r

def d2FlowCandidateRunOverwrite (d : Nat) (initial : D2FlowTree d) :
    Nat -> Prod Nat (Prod Nat Nat) :=
  fun n => d2FlowTreeRootData
    (d2FlowCandidateStage d n (d2FlowCandidateRun d initial n))

/-- The concrete candidate run is exactly a generic recursive history with
the root overwritten by its own post-stage value. Thus the child-history and
trace adapters apply to every actual candidate snapshot. -/
theorem d2FlowCandidateRun_eq_generic_history {d : Nat}
    (initial : D2FlowTree d) (n : Nat) :
    d2FlowCandidateRun d initial n =
      d2FlowTreeRunWithParentOverwrites initial 0
        (d2FlowCandidateRunActive d) (d2FlowCandidateRunRole d)
        (d2FlowCandidateRunQuota d)
        (d2FlowCandidateRunOverwrite d initial) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [d2FlowCandidateRun, d2FlowTreeRunWithParentOverwrites]
      rw [ih]
      simp only [d2FlowCandidateRunActive, d2FlowCandidateRunRole, d2FlowCandidateRunQuota, d2FlowCandidateRunOverwrite, d2FlowCandidateStage]
      rw [ih]
      exact (d2FlowTreeSetRoot_rootData_identity _).symm

/-- Every depth-`n` subtree in the concrete candidate run is its path history
with the candidate's actual schedule callbacks and ancestor overwrites. -/
theorem d2FlowCandidateRun_path_as_history {h n : Nat}
    (initial : D2FlowTree (h + n)) (path : D2FlowPath n) (step : Nat) :
    d2FlowTreeAtPath n (d2FlowCandidateRun (h + n) initial step) path =
      d2FlowTreePathHistory n initial path 0
        (d2FlowCandidateRunActive (h + n))
        (d2FlowCandidateRunRole (h + n))
        (d2FlowCandidateRunQuota (h + n))
        (d2FlowCandidateRunOverwrite (h + n) initial) step := by
  rw [d2FlowCandidateRun_eq_generic_history]
  exact d2FlowTreeRun_path_as_history initial path 0
    (d2FlowCandidateRunActive (h + n))
    (d2FlowCandidateRunRole (h + n))
    (d2FlowCandidateRunQuota (h + n))
    (d2FlowCandidateRunOverwrite (h + n) initial) step

/-- The actual cut value for one child in a parent snapshot. -/
def d2FlowTreeParentCutAt {h i : Nat} (parent : D2FlowTree (h + 1))
    (role : Nat → D2Role) (quota : Nat → D2Role → Nat) (j : Fin 8) : Nat :=
  match parent with
  | .node G low high children =>
      d2FlowStageParentCutChildDeficit (i := i) (G := G)
        (low := low) (high := high) children role quota j

/-- Repeated concrete subtree stages, with arbitrary ancestor root
overwrites, produce exactly the abstract rational child-deficit trace. This
closes the adapter gap between the recursive tree transition and the trace
interface; the trace's numerical bounds remain separate obligations. -/
theorem d2FlowTreeRun_child_trace {h i : Nat}
    (initial : D2FlowTree (h + 1))
    (active : Nat → Nat → Bool) (role : Nat → Nat → D2Role)
    (quota : Nat → Nat → D2Role → Nat)
    (overwrite : Nat → Nat × Nat × Nat) (j : Fin 8) (n : Nat) :
    (d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeRunWithParentOverwrites initial i active role quota
          overwrite n) j) : Rat) / 8192 =
      d2ChildDeficitTrace
        ((d2FlowTreeRootDeficit (d2FlowTreeChild initial j) : Rat) / 8192)
        (fun k => active k (i + 1))
        (fun k =>
          (d2FlowStagePort (active k) (role k) (quota k) h (i + 1)
            (d2FlowTreeChild
              (d2FlowTreeRunWithParentOverwrites initial i active role quota
                overwrite k) j) : Rat) / 8192)
        (fun k => active k i) (fun k => role k i)
        (fun k =>
          (d2FlowTreeParentCutAt
            (i := i) (d2FlowTreeRunWithParentOverwrites initial i active role quota
              overwrite k) (role k) (quota k) j : Rat) / 8192)
        n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases hs : d2FlowTreeRunWithParentOverwrites initial i active role quota
          overwrite n with
      | node G low high children =>
          have hstep := d2FlowStage_normalized_child_parent_recurrence
            (active := active n) (role := role n) (quota := quota n)
            (i := i) (G := G) (low := low) (high := high) children j
          simp only [d2FlowTreeRunWithParentOverwrites, d2ChildDeficitTrace]
          rw [hs]
          rw [d2FlowTreeChild_setRoot]
          change (d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowStage (active n) (role n) (quota n) (h + 1) i
                (.node G low high children)) j) : Rat) / 8192 = _
          rw [hstep]
          have hprev :
              (d2FlowTreeRootDeficit
                (d2FlowTreeChild (.node G low high children) j) : Rat) / 8192 =
              d2ChildDeficitTrace
                ((d2FlowTreeRootDeficit (d2FlowTreeChild initial j) : Rat) / 8192)
                (fun k => active k (i + 1))
                (fun k =>
                  (d2FlowStagePort (active k) (role k) (quota k) h (i + 1)
                    (d2FlowTreeChild
                      (d2FlowTreeRunWithParentOverwrites initial i active role quota
                        overwrite k) j) : Rat) / 8192)
                (fun k => active k i) (fun k => role k i)
                (fun k =>
                  (d2FlowTreeParentCutAt (i := i)
                    (d2FlowTreeRunWithParentOverwrites initial i active role quota
                      overwrite k) (role k) (quota k) j : Rat) / 8192)
                n := by
            simpa [hs] using ih
          have hprev' :
              (d2FlowTreeRootDeficit (children j) : Rat) / 8192 =
              d2ChildDeficitTrace
                ((d2FlowTreeRootDeficit (d2FlowTreeChild initial j) : Rat) / 8192)
                (fun k => active k (i + 1))
                (fun k =>
                  (d2FlowStagePort (active k) (role k) (quota k) h (i + 1)
                    (d2FlowTreeChild
                      (d2FlowTreeRunWithParentOverwrites initial i active role quota
                        overwrite k) j) : Rat) / 8192)
                (fun k => active k i) (fun k => role k i)
                (fun k =>
                  (d2FlowTreeParentCutAt (i := i)
                    (d2FlowTreeRunWithParentOverwrites initial i active role quota
                      overwrite k) (role k) (quota k) j : Rat) / 8192)
                n := by
            simpa [d2FlowTreeChild] using hprev
          rw [hprev']
          simp [hs, d2FlowTreeChild, d2FlowTreeParentCutAt]

/-- After any path prefix, the deficit of one more selected child obeys the
same exact child-deficit trace. This is the compositional path interface for
transporting local reserve gates to arbitrarily deep nodes. -/
theorem d2FlowTreePathHistory_child_trace {h n : Nat}
    (initial : D2FlowTree (h + 1 + n)) (path : D2FlowPath n) (i : Nat)
    (active : Nat → Nat → Bool) (role : Nat → Nat → D2Role)
    (quota : Nat → Nat → D2Role → Nat)
    (overwrite : Nat → Nat × Nat × Nat) (j : Fin 8) (step : Nat) :
    (d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreePathHistory n initial path i active role quota overwrite step)
        j) : Rat) / 8192 =
      d2ChildDeficitTrace
        ((d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreePathContext n initial path i active role quota overwrite).initial
            j) : Rat) / 8192)
        (fun k => active k
          ((d2FlowTreePathContext n initial path i active role quota overwrite).level + 1))
        (fun k =>
          (d2FlowStagePort (active k) (role k) (quota k)
            h
            ((d2FlowTreePathContext n initial path i active role quota overwrite).level + 1)
            (d2FlowTreeChild
              (d2FlowTreeRunWithParentOverwrites
                (d2FlowTreePathContext n initial path i active role quota overwrite).initial
                (d2FlowTreePathContext n initial path i active role quota overwrite).level
                active role quota
                (d2FlowTreePathContext n initial path i active role quota overwrite).overwrite
                k) j) : Rat) / 8192)
        (fun k => active k
          (d2FlowTreePathContext n initial path i active role quota overwrite).level)
        (fun k => role k
          (d2FlowTreePathContext n initial path i active role quota overwrite).level)
        (fun k =>
          (d2FlowTreeParentCutAt
            (i := (d2FlowTreePathContext n initial path i active role quota overwrite).level)
            (d2FlowTreeRunWithParentOverwrites
              (d2FlowTreePathContext n initial path i active role quota overwrite).initial
              (d2FlowTreePathContext n initial path i active role quota overwrite).level
              active role quota
              (d2FlowTreePathContext n initial path i active role quota overwrite).overwrite
              k)
            (role k) (quota k)
            j : Rat) / 8192) step := by
  rw [d2FlowTreePathHistory_eq_context_run]
  exact d2FlowTreeRun_child_trace
    (d2FlowTreePathContext n initial path i active role quota overwrite).initial
    active role quota
    (d2FlowTreePathContext n initial path i active role quota overwrite).overwrite
    j step

/-- The concrete candidate child deficit satisfies the same exact trace
recurrence, including the actual scheduler callbacks and parent cuts. -/
theorem d2FlowCandidateRun_child_trace {d : Nat}
    (initial : D2FlowTree (d + 1)) (j : Fin 8) (n : Nat) :
    (d2FlowTreeRootDeficit
      (d2FlowTreeChild (d2FlowCandidateRun (d + 1) initial n) j) : Rat) / 8192 =
      d2ChildDeficitTrace
        ((d2FlowTreeRootDeficit (d2FlowTreeChild initial j) : Rat) / 8192)
        (fun k => d2FlowCandidateRunActive (d + 1) k 1)
        (fun k =>
          (d2FlowStagePort (d2FlowCandidateRunActive (d + 1) k)
            (d2FlowCandidateRunRole (d + 1) k)
            (d2FlowCandidateRunQuota (d + 1) k) d 1
            (d2FlowTreeChild
              (d2FlowTreeRunWithParentOverwrites initial 0
                (d2FlowCandidateRunActive (d + 1))
                (d2FlowCandidateRunRole (d + 1))
                (d2FlowCandidateRunQuota (d + 1))
                (d2FlowCandidateRunOverwrite (d + 1) initial) k) j) : Rat) / 8192)
        (fun k => d2FlowCandidateRunActive (d + 1) k 0)
        (fun k => d2FlowCandidateRunRole (d + 1) k 0)
        (fun k =>
          (d2FlowTreeParentCutAt (i := 0)
            (d2FlowTreeRunWithParentOverwrites initial 0
              (d2FlowCandidateRunActive (d + 1))
              (d2FlowCandidateRunRole (d + 1))
              (d2FlowCandidateRunQuota (d + 1))
              (d2FlowCandidateRunOverwrite (d + 1) initial) k)
            (d2FlowCandidateRunRole (d + 1) k)
            (d2FlowCandidateRunQuota (d + 1) k) j : Rat) / 8192) n := by
  rw [d2FlowCandidateRun_eq_generic_history]
  exact d2FlowTreeRun_child_trace initial
    (d2FlowCandidateRunActive (d + 1))
    (d2FlowCandidateRunRole (d + 1))
    (d2FlowCandidateRunQuota (d + 1))
    (d2FlowCandidateRunOverwrite (d + 1) initial) j n

/-- The bot-rise branch preserves the non-leaf child-cover invariant. Its
parent deficit becomes the old child total, while each child root can only
increase during its recursive stage. -/
theorem d2FlowStage_botRise_child_cover {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true) (hr : role i = .botRise)
    (hcover : G ≤ d2FlowTotal (fun j =>
      d2FlowTreeRootDeficit (children j))) :
    d2FlowTreeRootDeficit
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) ≤
      (Finset.univ.sum fun j : Fin 8 =>
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)) := by
  have hsum : (Finset.univ.sum fun j : Fin 8 =>
      d2FlowTreeRootDeficit (children j)) ≤
      (Finset.univ.sum fun j : Fin 8 =>
        d2FlowTreeRootDeficit
          (d2FlowStage active role quota h (i + 1) (children j))) := by
    apply Finset.sum_le_sum
    intro j hj
    exact d2FlowStage_root_deficit_mono active role quota (i + 1) (children j)
  rw [d2FlowStage_active_node_deficit children ha, hr]
  simp_rw [d2FlowStage_botRise_child_deficit children ha hr]
  have hsum' : d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) ≤
      Finset.univ.sum (fun j : Fin 8 =>
        d2FlowTreeRootDeficit
          (d2FlowStage active role quota h (i + 1) (children j))) := by
    simpa [d2FlowTotal] using hsum
  dsimp [d2FlowTotal] at hcover hsum' ⊢
  have hcancel : G + ((Finset.univ.sum fun j : Fin 8 =>
      d2FlowTreeRootDeficit (children j)) - G) =
      Finset.univ.sum (fun j : Fin 8 =>
        d2FlowTreeRootDeficit (children j)) := by omega
  rw [hcancel]
  exact hsum'

/-- Under recursive child native bounds, a bot-rise parent remains within
its own native size: its new deficit is exactly the old child-root total. -/
theorem d2FlowStage_botRise_parent_native {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} {scale : Nat}
    (children : Fin 8 → D2FlowTree h)
    (ha : active i = true) (hr : role i = .botRise)
    (hinv : ∀ j, d2FlowTreeInv scale (children j))
    (hcover : G ≤ d2FlowTotal (fun j =>
      d2FlowTreeRootDeficit (children j))) :
    d2FlowTreeRootDeficit
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) ≤ scale * 8 ^ (h + 1) := by
  have hsumCap : (Finset.univ.sum fun j : Fin 8 =>
      d2FlowTreeRootDeficit (children j)) ≤ scale * 8 ^ (h + 1) := by
    calc
      (Finset.univ.sum fun j : Fin 8 =>
          d2FlowTreeRootDeficit (children j)) ≤
        (Finset.univ.sum fun _j : Fin 8 => scale * 8 ^ h) := by
          apply Finset.sum_le_sum
          intro j hj
          exact d2FlowTreeInv_root_native_bound (children j) (hinv j)
      _ = scale * 8 ^ (h + 1) := by
          rw [Nat.pow_succ]
          calc
            (Finset.univ.sum fun _j : Fin 8 => scale * 8 ^ h) =
                8 * (scale * 8 ^ h) := by simp
            _ = scale * (8 ^ h * 8) := by ring
  have hnew : d2FlowTreeRootDeficit
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    rw [d2FlowStage_active_node_deficit children ha]
    simp only [hr]
    exact Nat.add_sub_of_le hcover
  rw [hnew]
  exact hsumCap

/-- A `botRise` node preserves the full tree invariant whenever its recursively
updated children do. Its new deficit is the old total child deficit, so the
native cap follows by summing child caps; the old endpoint balance transfers
to the new root. -/
theorem d2FlowStage_botRise_node_inv {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high scale : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true) (hr : role i = .botRise)
    (hinvParent : d2FlowTreeInv scale (.node G low high children))
    (hchildren : ∀ j, d2FlowTreeInv scale
      (d2FlowStage active role quota h (i + 1) (children j)))
    (hbalance : low + high = G) :
    d2FlowTreeInv scale
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) := by
  have hcover := d2FlowTreeInv_node_children_cover children hinvParent
  have hchildrenOld : ∀ j, d2FlowTreeInv scale (children j) := by
    have hinv' := hinvParent
    simp only [d2FlowTreeInv] at hinv'
    exact hinv'.2.2.2
  have hparentCap := d2FlowStage_botRise_parent_native
    (active := active) (role := role) (quota := quota)
    (h := h) (i := i) (G := G) (low := low) (high := high)
    (scale := scale) children ha hr hchildrenOld hcover
  have hchildCover := d2FlowStage_botRise_child_cover
    (active := active) (role := role) (quota := quota)
    (h := h) (i := i) (G := G) (low := low) (high := high)
    children ha hr hcover
  have hparentCap' : G +
      (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) ≤
      scale * 8 ^ (h + 1) := by
    rw [d2FlowStage_active_node_deficit children ha, hr] at hparentCap
    exact hparentCap
  have hchildCover' : G +
      (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) ≤
      Finset.univ.sum (fun j : Fin 8 =>
        d2FlowTreeRootDeficit
          (d2FlowStage active role quota h (i + 1) (children j))) := by
    rw [d2FlowStage_active_node_deficit children ha, hr] at hchildCover
    simpa [d2FlowTotal, d2FlowStage_botRise_child_deficit children ha hr] using
      hchildCover
  have hnewBalance :
      low + (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) / 2 +
        (high + (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) -
          (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) / 2) =
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    omega
  simp only [d2FlowStage, ha, hr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hparentCap'
  · exact hchildCover'
  · intro _
    omega
  · exact hchildren

/-- A valid `topDesc` node has zero parent deficit and resets every child
root to zero. Descendant subtrees keep their recursive invariant under that
root replacement. -/
theorem d2FlowStage_topDesc_node_inv {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high scale : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true) (hr : role i = .topDesc)
    (hG : G = 0) (hbalance : low + high = G)
    (hchildren : ∀ j, d2FlowTreeInv scale
      (d2FlowStage active role quota h (i + 1) (children j))) :
    d2FlowTreeInv scale
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) := by
  have hlow : low = 0 := by omega
  have hhigh : high = 0 := by omega
  subst G low high
  have hreset : ∀ j, d2FlowTreeInv scale
      (d2FlowTreeSetRoot
        (d2FlowStage active role quota h (i + 1) (children j)) 0 0 0) := by
    intro j
    have hinv := hchildren j
    have hcap : 0 ≤ scale * 8 ^ h := by omega
    have hbal : 0 < scale * 8 ^ h → 0 + 0 = 0 := by intro _; omega
    have hle : 0 ≤ d2FlowTreeRootDeficit
        (d2FlowStage active role quota h (i + 1) (children j)) := Nat.zero_le _
    exact d2FlowTreeSetRoot_preserves_inv_of_lower_deficit
      (d2FlowStage active role quota h (i + 1) (children j)) hinv
      0 0 0 hcap hbal hle
  simp only [d2FlowStage, ha, hr]
  refine ⟨by omega, ?_, ?_, ?_⟩
  · simp [d2FlowTreeRootDeficit]
  · intro _
    omega
  · exact hreset

/-- An inactive node retains its root data; recursive child-cover monotonicity
is the only additional fact needed for the invariant. -/
theorem d2FlowStage_inactive_node_inv {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high scale : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = false)
    (hinvParent : d2FlowTreeInv scale (.node G low high children))
    (hchildren : ∀ j, d2FlowTreeInv scale
      (d2FlowStage active role quota h (i + 1) (children j))) :
    d2FlowTreeInv scale
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) := by
  have hchildSum := d2FlowTreeInv_node_children_cover children hinvParent
  have hsum : (Finset.univ.sum fun j : Fin 8 =>
      d2FlowTreeRootDeficit (children j)) ≤
      Finset.univ.sum (fun j : Fin 8 =>
        d2FlowTreeRootDeficit
          (d2FlowStage active role quota h (i + 1) (children j))) := by
    apply Finset.sum_le_sum
    intro j hj
    exact d2FlowStage_root_deficit_mono active role quota (i + 1) (children j)
  have hchildCover : G ≤ Finset.univ.sum (fun j : Fin 8 =>
      d2FlowTreeRootDeficit
        (d2FlowStage active role quota h (i + 1) (children j))) :=
    le_trans hchildSum hsum
  have hparentCap : G ≤ scale * 8 ^ (h + 1) := hinvParent.1
  have hbalance : G < scale * 8 ^ (h + 1) → low + high = G := hinvParent.2.2.1
  simp only [d2FlowStage, ha]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hparentCap
  · exact hchildCover
  · exact hbalance
  · exact hchildren

/-- Recursive local hypotheses sufficient for one complete tree stage to
preserve `d2FlowTreeInv`. At ordinary senders, `cap i` is the local schedule
capacity and the six conjuncts are exactly the deficit, quota, allocation,
parity, and two endpoint-reserve obligations. -/
def d2FlowStageInvInputs (scale : Nat) (active : Nat → Bool)
    (role : Nat → D2Role) (quota : Nat → D2Role → Nat)
    (cap : Nat → Nat) : {h : Nat} → Nat → D2FlowTree h → Prop
  | 0, _, .leaf _ _ _ => True
  | h + 1, i, .node G low high children =>
      (∀ j, d2FlowStageInvInputs scale active role quota cap (i + 1)
        (children j)) ∧
      (if active i then
        low + high = G ∧
          match role i with
          | .topDesc => G = 0
          | .botRise => True
          | r =>
              512 * G ≤ cap i ∧
              256 * quota i r ≤ cap i ∧
              quota i r ≤ d2FlowTotal
                (fun j => d2FlowTreeRootDeficit (children j)) - G ∧
              quota i r % 2 = 0 ∧
              cap i ≤ 128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩) ∧
              cap i ≤ 128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩)
      else True)

/-- Tolerant version of the recursive stage-input contract. It allows a
per-sender deficit up to `23/4096` of scheduled capacity while retaining the
same quota, allocation, parity, and endpoint-reserve gates. -/
def d2FlowStageInvInputsTolerant (scale : Nat) (active : Nat → Bool)
    (role : Nat → D2Role) (quota : Nat → D2Role → Nat)
    (cap : Nat → Nat) : {h : Nat} → Nat → D2FlowTree h → Prop
  | 0, _, .leaf _ _ _ => True
  | h + 1, i, .node G low high children =>
      (∀ j, d2FlowStageInvInputsTolerant scale active role quota cap
        (i + 1) (children j)) ∧
      (if active i then
        low + high = G ∧
          match role i with
          | .topDesc => G = 0
          | .botRise => True
          | r =>
              4096 * G ≤ 23 * cap i ∧
              256 * quota i r ≤ cap i ∧
              quota i r ≤ d2FlowTotal
                (fun j => d2FlowTreeRootDeficit (children j)) - G ∧
              quota i r % 2 = 0 ∧
              cap i ≤ 128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩) ∧
              cap i ≤ 128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩)
      else True)

/-- The original `1/512` input gate implies the relaxed `23/4096` gate, so
existing checked bootstrap stages can be reused under the tolerant contract. -/
theorem d2FlowStageInvInputs_tolerant_of_strict
    {scale : Nat} {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {cap : Nat → Nat} :
    ∀ {h i : Nat} (tree : D2FlowTree h),
      d2FlowStageInvInputs scale active role quota cap i tree →
      d2FlowStageInvInputsTolerant scale active role quota cap i tree := by
  intro h
  induction h with
  | zero =>
      intro i tree hinputs
      cases tree <;> simp [d2FlowStageInvInputs,
        d2FlowStageInvInputsTolerant] at *
  | succ h ih =>
      intro i tree hinputs
      cases tree with
      | node G low high children =>
          simp only [d2FlowStageInvInputs, d2FlowStageInvInputsTolerant]
            at hinputs ⊢
          rcases hinputs with ⟨hchildren, hlocal⟩
          refine ⟨?_, ?_⟩
          · intro j
            exact ih (i := i + 1) (children j) (hchildren j)
          · by_cases ha : active i = true
            · simp only [ha, if_pos] at hlocal ⊢
              rcases hlocal with ⟨hbalance, hroleInput⟩
              refine ⟨hbalance, ?_⟩
              cases hr : role i with
              | topDesc => simpa [hr] using hroleInput
              | botRise => simpa [hr] using hroleInput
              | topRise =>
                  simp only [hr] at hroleInput
                  rcases hroleInput with
                    ⟨hG, hquota, halloc, heven, hleft, hright⟩
                  exact ⟨by omega, hquota, halloc, heven, hleft, hright⟩
              | mid =>
                  simp only [hr] at hroleInput
                  rcases hroleInput with
                    ⟨hG, hquota, halloc, heven, hleft, hright⟩
                  exact ⟨by omega, hquota, halloc, heven, hleft, hright⟩
              | botDesc =>
                  simp only [hr] at hroleInput
                  rcases hroleInput with
                    ⟨hG, hquota, halloc, heven, hleft, hright⟩
                  exact ⟨by omega, hquota, halloc, heven, hleft, hright⟩
            · simp [ha]

/-- If every level at or below a subtree root is inactive, its recursive
stage-input obligations are vacuous. -/
theorem d2FlowStageInvInputs_all_inactive
    {scale : Nat} {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {cap : Nat → Nat} :
    ∀ {h i : Nat} (tree : D2FlowTree h),
      (∀ k, i ≤ k → active k = false) →
      d2FlowStageInvInputs scale active role quota cap i tree := by
  intro h
  induction h with
  | zero =>
      intro i tree hinactive
      cases tree
      simp [d2FlowStageInvInputs]
  | succ h ih =>
      intro i tree hinactive
      cases tree with
      | node G low high children =>
          simp only [d2FlowStageInvInputs]
          constructor
          · intro j
            exact ih (i := i + 1) (children j) (by
              intro k hk
              exact hinactive k (by omega))
          · simp [hinactive i (by omega)]

/-- The recursive stage-input predicate packages exactly the reserves needed
to export its ordinary sender's normalized child cap. -/
theorem d2FlowStage_regular_child_g_bound_of_inputs
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {cap : Nat → Nat}
    {h i G low high scale : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hinvParent : d2FlowTreeInv scale (.node G low high children))
    (hinputs : d2FlowStageInvInputs scale active role quota cap
      i (.node G low high children)) :
    ∀ j, 512 * d2FlowTreeRootDeficit
      (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) j) ≤ 2 * cap i := by
  simp only [d2FlowStageInvInputs] at hinputs
  have hlocal := hinputs.2
  simp only [ha, if_true] at hlocal
  rcases hr with htop | hmid | hbot
  · simp only [htop] at hlocal
    rcases hlocal with ⟨hbalance, hG, hquota, halloc, heven, hleft, hright⟩
    have hquota' : 256 * quota i (role i) ≤ cap i := by simpa [htop] using hquota
    have halloc' : quota i (role i) ≤
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
      simpa [htop] using halloc
    have heven' : quota i (role i) % 2 = 0 := by simpa [htop] using heven
    exact d2FlowStage_regular_child_g_bound_of_reserves children ha
      (Or.inl htop) hinvParent hbalance halloc' hG hquota' heven' hleft hright
  · simp only [hmid] at hlocal
    rcases hlocal with ⟨hbalance, hG, hquota, halloc, heven, hleft, hright⟩
    have hquota' : 256 * quota i (role i) ≤ cap i := by simpa [hmid] using hquota
    have halloc' : quota i (role i) ≤
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
      simpa [hmid] using halloc
    have heven' : quota i (role i) % 2 = 0 := by simpa [hmid] using heven
    exact d2FlowStage_regular_child_g_bound_of_reserves children ha
      (Or.inr (Or.inl hmid)) hinvParent hbalance halloc' hG hquota' heven' hleft hright
  · simp only [hbot] at hlocal
    rcases hlocal with ⟨hbalance, hG, hquota, halloc, heven, hleft, hright⟩
    have hquota' : 256 * quota i (role i) ≤ cap i := by simpa [hbot] using hquota
    have halloc' : quota i (role i) ≤
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
      simpa [hbot] using halloc
    have heven' : quota i (role i) % 2 = 0 := by simpa [hbot] using heven
    exact d2FlowStage_regular_child_g_bound_of_reserves children ha
      (Or.inr (Or.inr hbot)) hinvParent hbalance halloc' hG hquota' heven' hleft hright

/-- Same local gate for a tree whose constructor is hidden.  This wrapper lets
the schedule-level proof use a subtree invariant and its input predicate
without normalizing the subtree-producing recursion. -/
theorem d2FlowStage_regular_child_g_bound_of_tree_inputs
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {cap : Nat → Nat}
    {stageDepth i : Nat} (t : D2FlowTree (stageDepth + 1))
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hinv : d2FlowTreeInv 8192 t)
    (hinputs : d2FlowStageInvInputs 8192 active role quota cap i t) :
    ∀ j, 512 * d2FlowTreeRootDeficit
      (d2FlowTreeChild (d2FlowStage active role quota (stageDepth + 1) i t) j) ≤
      2 * cap i := by
  cases t with
  | node G low high children =>
      exact d2FlowStage_regular_child_g_bound_of_inputs children ha hr hinv hinputs

/-- The exact ordinary-cut profile propagates the relaxed `23/4096` sender
budget to every child at its next-time capacity `2*cap`. -/
theorem d2FlowStage_regular_child_tolerant_g_bound_of_reserves
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high scale cap : Nat}
    (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hinvParent : d2FlowTreeInv scale (.node G low high children))
    (hbalance : low + high = G)
    (hG : 4096 * G ≤ 23 * cap)
    (hquota : 256 * quota i (role i) ≤ cap)
    (halloc : quota i (role i) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G)
    (heven : quota i (role i) % 2 = 0)
    (hleft : cap ≤ 128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hright : cap ≤ 128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩)) :
    ∀ j, 4096 * d2FlowTreeRootDeficit
      (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) j) ≤ 23 * (2 * cap) := by
  let sizes : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
  let total : Nat := d2FlowTotal sizes
  have hcover := d2FlowTreeInv_node_children_cover children hinvParent
  have hconserve : (total - G) + G = d2FlowTotal sizes := by
    dsimp [total]
    exact Nat.sub_add_cancel hcover
  have hlow : low ≤ G := by omega
  have hhigh : high ≤ G := by omega
  have hevenEq : quota i (role i) = 2 * (quota i (role i) / 2) := by omega
  have hprofile := d2FlowStage_regular_child_profile_tolerant children ha hr
    hbalance (by simpa [total, sizes] using hconserve)
    (by simpa [total, sizes] using halloc) hevenEq hG hlow hhigh hquota
    (by simpa [sizes] using hleft) (by simpa [sizes] using hright)
  have hends := d2_ordinary_end_child_deficit_tolerant_cap
    hG hlow hhigh hquota hevenEq
  intro j
  by_cases hfirst : j = 0
  · subst j
    rw [hprofile.1]
    omega
  · by_cases hlast : j = 7
    · subst j
      rw [hprofile.2.1]
      omega
    · have hjfirst : 0 < j.val := by omega
      have hjlast : j.val < 7 := by omega
      rw [hprofile.2.2 j hjfirst hjlast]
      omega

/-- Input-predicate adapter for the tolerant child-cap propagation lemma. -/
theorem d2FlowStage_regular_child_tolerant_g_bound_of_inputs
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {cap : Nat → Nat}
    {h i G low high scale : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hinvParent : d2FlowTreeInv scale (.node G low high children))
    (hinputs : d2FlowStageInvInputsTolerant scale active role quota cap
      i (.node G low high children)) :
    ∀ j, 4096 * d2FlowTreeRootDeficit
      (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) j) ≤ 23 * (2 * cap i) := by
  simp only [d2FlowStageInvInputsTolerant] at hinputs
  have hlocal := hinputs.2
  simp only [ha, if_true] at hlocal
  rcases hr with htop | hmid | hbot
  · simp only [htop] at hlocal
    rcases hlocal with ⟨hbalance, hG, hquota, halloc, heven, hleft, hright⟩
    exact d2FlowStage_regular_child_tolerant_g_bound_of_reserves
      children ha (Or.inl htop) hinvParent hbalance hG
      (by simpa [htop] using hquota) (by simpa [htop] using halloc)
      (by simpa [htop] using heven) hleft hright
  · simp only [hmid] at hlocal
    rcases hlocal with ⟨hbalance, hG, hquota, halloc, heven, hleft, hright⟩
    exact d2FlowStage_regular_child_tolerant_g_bound_of_reserves
      children ha (Or.inr (Or.inl hmid)) hinvParent hbalance hG
      (by simpa [hmid] using hquota) (by simpa [hmid] using halloc)
      (by simpa [hmid] using heven) hleft hright
  · simp only [hbot] at hlocal
    rcases hlocal with ⟨hbalance, hG, hquota, halloc, heven, hleft, hright⟩
    exact d2FlowStage_regular_child_tolerant_g_bound_of_reserves
      children ha (Or.inr (Or.inr hbot)) hinvParent hbalance hG
      (by simpa [hbot] using hquota) (by simpa [hbot] using halloc)
      (by simpa [hbot] using heven) hleft hright

/-- Height induction composes the local invariant lemmas into preservation
for the entire recursive stage. This is the exact global interface: the
remaining arithmetic problem is to prove `d2FlowStageInvInputs` for every
snapshot of the candidate run. -/
theorem d2FlowStage_preserves_inv_of_inputs
    {h i scale : Nat} {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {cap : Nat → Nat} (tree : D2FlowTree h)
    (hinv : d2FlowTreeInv scale tree)
    (hinputs : d2FlowStageInvInputs scale active role quota cap i tree) :
    d2FlowTreeInv scale (d2FlowStage active role quota h i tree) := by
  induction tree generalizing i with
  | leaf G low high =>
      simpa [d2FlowStage, d2FlowTreeInv] using hinv
  | @node h G low high children ih =>
      simp only [d2FlowStageInvInputs] at hinputs
      have hinvChildrenOld : ∀ j, d2FlowTreeInv scale (children j) := by
        have hparent := hinv
        simp only [d2FlowTreeInv] at hparent
        exact hparent.2.2.2
      have hchildren : ∀ j, d2FlowTreeInv scale
          (d2FlowStage active role quota h (i + 1) (children j)) := by
        intro j
        exact ih j (hinvChildrenOld j) (hinputs.1 j)
      by_cases ha : active i = false
      · exact d2FlowStage_inactive_node_inv children ha hinv hchildren
      · have ha' : active i = true := Bool.eq_true_of_not_eq_false ha
        have hlocal := hinputs.2
        simp only [ha'] at hlocal
        have hbalance := hlocal.1
        have hroleInput := hlocal.2
        cases hr : role i with
        | topDesc =>
            have hG : G = 0 := by simpa [hr] using hroleInput
            exact d2FlowStage_topDesc_node_inv children ha' hr
              hG hbalance hchildren
        | botRise =>
            have htrivial : True := by simpa [hr] using hroleInput
            exact d2FlowStage_botRise_node_inv children ha' hr hinv
              hchildren hbalance
        | topRise =>
            have hregular : role i = .topRise ∨ role i = .mid ∨
                role i = .botDesc := Or.inl hr
            have hprops := by simpa [hr] using hroleInput
            rcases hprops with ⟨hG, hquota, halloc, heven, hleft, hright⟩
            have hquota' : 256 * quota i (role i) ≤ cap i := by simpa [hr] using hquota
            have halloc' : quota i (role i) ≤
                d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
              simpa [hr] using halloc
            have heven' : quota i (role i) % 2 = 0 := by simpa [hr] using heven
            exact d2FlowStage_regular_node_inv_of_reserves children ha'
              hregular hinv hchildren hbalance halloc' hG hquota' heven' hleft hright
        | mid =>
            have hregular : role i = .topRise ∨ role i = .mid ∨
                role i = .botDesc := Or.inr (Or.inl hr)
            have hprops := by simpa [hr] using hroleInput
            rcases hprops with ⟨hG, hquota, halloc, heven, hleft, hright⟩
            have hquota' : 256 * quota i (role i) ≤ cap i := by simpa [hr] using hquota
            have halloc' : quota i (role i) ≤
                d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
              simpa [hr] using halloc
            have heven' : quota i (role i) % 2 = 0 := by simpa [hr] using heven
            exact d2FlowStage_regular_node_inv_of_reserves children ha'
              hregular hinv hchildren hbalance halloc' hG hquota' heven' hleft hright
        | botDesc =>
            have hregular : role i = .topRise ∨ role i = .mid ∨
                role i = .botDesc := Or.inr (Or.inr hr)
            have hprops := by simpa [hr] using hroleInput
            rcases hprops with ⟨hG, hquota, halloc, heven, hleft, hright⟩
            have hquota' : 256 * quota i (role i) ≤ cap i := by simpa [hr] using hquota
            have halloc' : quota i (role i) ≤
                d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
              simpa [hr] using halloc
            have heven' : quota i (role i) % 2 = 0 := by simpa [hr] using heven
            exact d2FlowStage_regular_node_inv_of_reserves children ha'
              hregular hinv hchildren hbalance halloc' hG hquota' heven' hleft hright

/-- Tolerant counterpart of recursive stage preservation. The larger
`23/4096` local deficit allowance suffices at every ordinary node, while the
same conservation, endpoint-reserve, and role branches handle the tree. -/
theorem d2FlowStage_preserves_inv_of_tolerant_inputs
    {h i scale : Nat} {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {cap : Nat → Nat} (tree : D2FlowTree h)
    (hinv : d2FlowTreeInv scale tree)
    (hinputs : d2FlowStageInvInputsTolerant scale active role quota cap i tree) :
    d2FlowTreeInv scale (d2FlowStage active role quota h i tree) := by
  induction tree generalizing i with
  | leaf G low high =>
      simpa [d2FlowStage, d2FlowTreeInv] using hinv
  | @node h G low high children ih =>
      simp only [d2FlowStageInvInputsTolerant] at hinputs
      have hinvChildrenOld : ∀ j, d2FlowTreeInv scale (children j) := by
        have hparent := hinv
        simp only [d2FlowTreeInv] at hparent
        exact hparent.2.2.2
      have hchildren : ∀ j, d2FlowTreeInv scale
          (d2FlowStage active role quota h (i + 1) (children j)) := by
        intro j
        exact ih j (hinvChildrenOld j) (hinputs.1 j)
      by_cases ha : active i = false
      · exact d2FlowStage_inactive_node_inv children ha hinv hchildren
      · have ha' : active i = true := Bool.eq_true_of_not_eq_false ha
        have hlocal := hinputs.2
        simp only [ha'] at hlocal
        have hbalance := hlocal.1
        have hroleInput := hlocal.2
        cases hr : role i with
        | topDesc =>
            have hG : G = 0 := by simpa [hr] using hroleInput
            exact d2FlowStage_topDesc_node_inv children ha' hr
              hG hbalance hchildren
        | botRise =>
            have htrivial : True := by simpa [hr] using hroleInput
            exact d2FlowStage_botRise_node_inv children ha' hr hinv
              hchildren hbalance
        | topRise =>
            have hregular : role i = .topRise ∨ role i = .mid ∨
                role i = .botDesc := Or.inl hr
            have hprops := by simpa [hr] using hroleInput
            rcases hprops with ⟨hG, hquota, halloc, heven, hleft, hright⟩
            have hquota' : 256 * quota i (role i) ≤ cap i := by
              simpa [hr] using hquota
            have halloc' : quota i (role i) ≤
                d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
              simpa [hr] using halloc
            have heven' : quota i (role i) % 2 = 0 := by
              simpa [hr] using heven
            exact d2FlowStage_regular_node_inv_of_tolerant_reserves children
              ha' hregular hinv hchildren hbalance halloc' hG hquota' heven'
              hleft hright
        | mid =>
            have hregular : role i = .topRise ∨ role i = .mid ∨
                role i = .botDesc := Or.inr (Or.inl hr)
            have hprops := by simpa [hr] using hroleInput
            rcases hprops with ⟨hG, hquota, halloc, heven, hleft, hright⟩
            have hquota' : 256 * quota i (role i) ≤ cap i := by
              simpa [hr] using hquota
            have halloc' : quota i (role i) ≤
                d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
              simpa [hr] using halloc
            have heven' : quota i (role i) % 2 = 0 := by
              simpa [hr] using heven
            exact d2FlowStage_regular_node_inv_of_tolerant_reserves children
              ha' hregular hinv hchildren hbalance halloc' hG hquota' heven'
              hleft hright
        | botDesc =>
            have hregular : role i = .topRise ∨ role i = .mid ∨
                role i = .botDesc := Or.inr (Or.inr hr)
            have hprops := by simpa [hr] using hroleInput
            rcases hprops with ⟨hG, hquota, halloc, heven, hleft, hright⟩
            have hquota' : 256 * quota i (role i) ≤ cap i := by
              simpa [hr] using hquota
            have halloc' : quota i (role i) ≤
                d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
              simpa [hr] using halloc
            have heven' : quota i (role i) % 2 = 0 := by
              simpa [hr] using heven
            exact d2FlowStage_regular_node_inv_of_tolerant_reserves children
              ha' hregular hinv hchildren hbalance halloc' hG hquota' heven'
              hleft hright

/-- At bootstrap stage zero, every node of a full sentinel subtree below the
root is inactive, so it contributes no local sender obligations. -/
theorem d2FlowCandidateFull_inactive_inputs {d h i scale : Nat}
    (hi : 0 < i) :
    d2FlowStageInvInputs scale
      (d2FlowCandidateActive d 0) (d2FlowCandidateRole d 0)
      (d2FlowCandidateQuota d 0) (fun k => d2FlowCandidateCapacity d k 0)
      i (d2FlowTreeFull scale h) := by
  induction h generalizing i with
  | zero => simp [d2FlowStageInvInputs, d2FlowTreeFull]
  | succ h ih =>
      simp only [d2FlowStageInvInputs, d2FlowTreeFull]
      constructor
      · intro j
        exact ih (i := i + 1) (by omega)
      · simp [d2FlowCandidateActive, Nat.ne_of_gt hi]

/-- At stage one, every full subtree below active level one is inactive. -/
theorem d2FlowCandidateFull_stage1_inactive_inputs {d h i scale : Nat}
    (hi : 2 ≤ i) :
    d2FlowStageInvInputs scale
      (d2FlowCandidateActive d 1) (d2FlowCandidateRole d 1)
      (d2FlowCandidateQuota d 1) (fun k => d2FlowCandidateCapacity d k 1)
      i (d2FlowTreeFull scale h) := by
  induction h generalizing i with
  | zero => simp [d2FlowStageInvInputs, d2FlowTreeFull]
  | succ h ih =>
      simp only [d2FlowStageInvInputs, d2FlowTreeFull]
      constructor
      · intro j
        exact ih (i := i + 1) (by omega)
      · have hi1 : i ≠ 1 := by omega
        simp [d2FlowCandidateActive, hi1]

/-- The root-only top-descending bootstrap satisfies the complete recursive
stage-input predicate on the actual full initialization. -/
theorem d2FlowCandidateBootstrap_inputs (d : Nat) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 0) (d2FlowCandidateRole d 0)
      (d2FlowCandidateQuota d 0) (fun k => d2FlowCandidateCapacity d k 0)
      0 (d2FlowTreeInitial 8192 d) := by
  cases d with
  | zero => simp [d2FlowStageInvInputs, d2FlowTreeInitial]
  | succ d =>
      simp only [d2FlowTreeInitial, d2FlowStageInvInputs]
      constructor
      · intro j
        exact d2FlowCandidateFull_inactive_inputs (d := d + 1)
          (h := d) (i := 1) (scale := 8192) (by omega)
      · simp [d2FlowCandidateActive, d2FlowCandidateRole]

/-- The concrete bootstrap stage preserves the saturated-aware tree
invariant. Later stages use the same structural induction once their local
sender/reserve inputs are proved. -/
theorem d2FlowCandidateBootstrap_preserves_inv (d : Nat) :
    d2FlowTreeInv 8192
      (d2FlowCandidateStage d 0 (d2FlowTreeInitial 8192 d)) := by
  have hpres := d2FlowStage_preserves_inv_of_inputs
    (active := d2FlowCandidateActive d 0)
    (role := d2FlowCandidateRole d 0)
    (quota := d2FlowCandidateQuota d 0)
    (cap := fun k => d2FlowCandidateCapacity d k 0)
    (i := 0) (d2FlowTreeInitial 8192 d)
    (d2FlowTreeInitial_inv 8192 d)
    (d2FlowCandidateBootstrap_inputs d)
  simpa [d2FlowCandidateStage] using hpres

/-- The bootstrap recursively leaves every below-root full sentinel subtree
untouched before the root's top-descending cut. -/
theorem d2FlowCandidateFull_bootstrap_stage_eq {d h i scale : Nat}
    (hi : 0 < i) :
    d2FlowStage (d2FlowCandidateActive d 0)
      (d2FlowCandidateRole d 0) (d2FlowCandidateQuota d 0)
      h i (d2FlowTreeFull scale h) = d2FlowTreeFull scale h := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih =>
      have hinactive : d2FlowCandidateActive d 0 i = false := by
        simp [d2FlowCandidateActive, Nat.ne_of_gt hi]
      simp only [d2FlowTreeFull, d2FlowStage, hinactive,
        if_neg (by decide : false ≠ true)]
      congr 1
      funext j
      exact ih (i := i + 1) (by omega)

/-- Exact shape after the bootstrap: the root keeps zero deficit and each
formerly full child has only its root reset; all deeper sentinel subtrees
remain full. -/
theorem d2FlowCandidateBootstrap_shape (d : Nat) :
    d2FlowCandidateStage (d + 1) 0 (d2FlowTreeInitial 8192 (d + 1)) =
      .node 0 0 0 (fun _ =>
        d2FlowTreeSetRoot (d2FlowTreeFull 8192 d) 0 0 0) := by
  have hactive : d2FlowCandidateActive (d + 1) 0 0 = true := by
    simp [d2FlowCandidateActive]
  have hrole : d2FlowCandidateRole (d + 1) 0 0 = .topDesc := by
    simp [d2FlowCandidateRole]
  have hquota : d2FlowCandidateQuota (d + 1) 0 0 .topDesc = 0 := by
    simp [d2FlowCandidateQuota]
  have hchild : ∀ j : Fin 8,
      d2FlowStage (d2FlowCandidateActive (d + 1) 0)
        (d2FlowCandidateRole (d + 1) 0)
        (d2FlowCandidateQuota (d + 1) 0)
        d 1 (d2FlowTreeFull 8192 d) = d2FlowTreeFull 8192 d := by
    intro j
    exact d2FlowCandidateFull_bootstrap_stage_eq
      (d := d + 1) (h := d) (i := 1) (scale := 8192) (by omega)
  simp [d2FlowCandidateStage, d2FlowTreeInitial, d2FlowStage,
    hactive, hrole, hquota]
  funext j
  exact congrArg (fun t => d2FlowTreeSetRoot t 0 0 0) (hchild j)

/-- At the first ordinary schedule visit, level one is the top frontier and
its role is a rising top sender. -/
theorem d2ScheduleRole_first_sender {d : Nat} (hd : 7 ≤ d) :
    d2ScheduleRole d 1 1 = .topRise := by
  have ha1 : alpha d 1 = 1 := by simp [alpha]
  have ha2 : alpha d 2 = 0 := by
    have hbound : 15 ≤ 3 * d := by omega
    simp [alpha, alphaStar, hbound, ceilParity]
  have hw1 : omega 1 = 1 := by simp [omega]
  have hw2 : omega 2 = 2 := by simp [omega, ceilParity]
  simp [d2ScheduleRole, ha1, ha2, hw1, hw2]

/-- Each child after bootstrap has zero root deficit and full grandchildren. -/
theorem d2FlowCandidateBootstrap_child_shape (d : Nat) (j : Fin 8) :
    d2FlowTreeChild
      (d2FlowCandidateStage (d + 2) 0 (d2FlowTreeInitial 8192 (d + 2))) j =
      .node 0 0 0 (fun _ => d2FlowTreeFull 8192 d) := by
  rw [d2FlowCandidateBootstrap_shape (d + 1)]
  simp [d2FlowTreeChild, d2FlowTreeSetRoot, d2FlowTreeFull]

/-- The first active sender after bootstrap satisfies every local hypothesis
in the recursive stage-preservation interface. Its old deficit is zero, its
children are full native subtrees, and the scheduled top-rise quota is
`capacity/256`. -/
theorem d2FlowCandidateBootstrap_sender_inputs {d : Nat} (hd : 5 ≤ d) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 1)
      (d2FlowCandidateRole (d + 2) 1)
      (d2FlowCandidateQuota (d + 2) 1)
      (fun k => d2FlowCandidateCapacity (d + 2) k 1)
      1 (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 d)) := by
  have hrole : d2FlowCandidateRole (d + 2) 1 1 = .topRise := by
    rw [d2FlowCandidateRole_matches_schedule (d := d + 2) (t := 1)
      (i := 1) (by omega)]
    exact d2ScheduleRole_first_sender (by omega)
  have hactive : d2FlowCandidateActive (d + 2) 1 1 = true := by
    simp [d2FlowCandidateActive]
  have hexp : d2FlowCandidateCapacityExponent (d + 2) 1 1 = 3 * d + 16 := by
    unfold d2FlowCandidateCapacityExponent
    omega
  have hcap : d2FlowCandidateCapacity (d + 2) 1 1 = 2 ^ (3 * d + 16) := by
    simp [d2FlowCandidateCapacity, hexp]
  have hquota : d2FlowCandidateQuota (d + 2) 1 1 .topRise =
      2 ^ (3 * d + 8) := by
    simp [d2FlowCandidateQuota, hexp]
  have hchildNative : d2FlowTreeRootDeficit (d2FlowTreeFull 8192 d) =
      8192 * 8 ^ d := d2FlowTreeFull_root_deficit 8192 d
  have htotal : d2FlowTotal (fun _ : Fin 8 =>
      d2FlowTreeRootDeficit (d2FlowTreeFull 8192 d)) =
      2 ^ (3 * d + 16) := by
    calc
      d2FlowTotal (fun _ : Fin 8 =>
          d2FlowTreeRootDeficit (d2FlowTreeFull 8192 d)) =
          8 * (8192 * 8 ^ d) := by
            simp [d2FlowTotal, hchildNative]
      _ = 2 ^ (3 * d + 16) := by
        rw [show (8192 : Nat) = 2 ^ 13 by norm_num,
          show (8 : Nat) = 2 ^ 3 by norm_num]
        rw [← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add]
        congr 1 <;> omega
  have hquotaCap : 256 * d2FlowCandidateQuota (d + 2) 1 1 .topRise =
      d2FlowCandidateCapacity (d + 2) 1 1 := by
    rw [hquota, hcap]
    calc
      256 * 2 ^ (3 * d + 8) = 2 ^ 8 * 2 ^ (3 * d + 8) := by norm_num
      _ = 2 ^ (8 + (3 * d + 8)) := by rw [← Nat.pow_add]
      _ = 2 ^ (3 * d + 16) := by congr 1 <;> omega
  have htotalCap : d2FlowTotal (fun _ : Fin 8 =>
      d2FlowTreeRootDeficit (d2FlowTreeFull 8192 d)) =
      d2FlowCandidateCapacity (d + 2) 1 1 := by rw [htotal, hcap]
  have halloc : d2FlowCandidateQuota (d + 2) 1 1 .topRise ≤
      d2FlowTotal (fun _ : Fin 8 =>
        d2FlowTreeRootDeficit (d2FlowTreeFull 8192 d)) := by
    rw [htotalCap]
    omega
  have hquotaEven : d2FlowCandidateQuota (d + 2) 1 1 .topRise % 2 = 0 := by
    rw [hquota, show 3 * d + 8 = (3 * d + 7) + 1 by omega, pow_succ]
    simp
  have hcapReserve : d2FlowCandidateCapacity (d + 2) 1 1 ≤
      128 * d2FlowTreeRootDeficit (d2FlowTreeFull 8192 d) := by
    have htotalNat : 8 * (8192 * 8 ^ d) = 2 ^ (3 * d + 16) := by
      simpa [d2FlowTotal, hchildNative] using htotal
    rw [hcap, hchildNative, ← htotalNat]
    omega
  simp only [d2FlowStageInvInputs]
  constructor
  · intro j
    exact d2FlowCandidateFull_stage1_inactive_inputs
      (d := d + 2) (h := d) (i := 2) (scale := 8192) (by omega)
  · rw [hactive]
    simp only [if_true]
    constructor
    · trivial
    · rw [hrole]
      exact ⟨by omega, le_of_eq hquotaCap, halloc, hquotaEven,
        hcapReserve, hcapReserve⟩

/-- The entire initialized tree satisfies the sender-input predicate at stage
one: its root is inactive and every active level-one node has the local
bootstrap shape verified above. -/
theorem d2FlowCandidateStage1_inputs (d : Nat) (hd : 5 ≤ d) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 1) (d2FlowCandidateRole (d + 2) 1)
      (d2FlowCandidateQuota (d + 2) 1)
      (fun k => d2FlowCandidateCapacity (d + 2) k 1)
      0 (d2FlowCandidateRun (d + 2) (d2FlowTreeInitial 8192 (d + 2)) 1) := by
  have hshape := d2FlowCandidateBootstrap_shape (d + 1)
  have hstage : d2FlowCandidateRun (d + 2) (d2FlowTreeInitial 8192 (d + 2)) 1 =
      d2FlowCandidateStage (d + 2) 0 (d2FlowTreeInitial 8192 (d + 2)) := rfl
  rw [hstage, hshape]
  have hchildren : ∀ j : Fin 8,
      d2FlowTreeSetRoot (d2FlowTreeFull 8192 (d + 1)) 0 0 0 =
        .node 0 0 0 (fun _ => d2FlowTreeFull 8192 d) := by
    intro j
    simp [d2FlowTreeSetRoot, d2FlowTreeFull]
  simp only [d2FlowStageInvInputs]
  constructor
  · intro j
    rw [hchildren j]
    exact d2FlowCandidateBootstrap_sender_inputs (d := d) hd
  · have hrootInactive : d2FlowCandidateActive (d + 2) 1 0 = false := by
      simp [d2FlowCandidateActive]
    simp [hrootInactive]

/-- The candidate tree invariant now holds through bootstrap and the first
ordinary sender stage for every dimension at least seven. -/
theorem d2FlowCandidateStage1_preserves_inv (d : Nat) (hd : 5 ≤ d) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (d + 2) (d2FlowTreeInitial 8192 (d + 2)) 2) := by
  have hrun1 : d2FlowCandidateRun (d + 2)
      (d2FlowTreeInitial 8192 (d + 2)) 1 =
      d2FlowCandidateStage (d + 2) 0 (d2FlowTreeInitial 8192 (d + 2)) := rfl
  have hinv1 : d2FlowTreeInv 8192
      (d2FlowCandidateRun (d + 2) (d2FlowTreeInitial 8192 (d + 2)) 1) := by
    rw [hrun1]
    exact d2FlowCandidateBootstrap_preserves_inv (d + 2)
  have hpres := d2FlowStage_preserves_inv_of_inputs
    (active := d2FlowCandidateActive (d + 2) 1)
    (role := d2FlowCandidateRole (d + 2) 1)
    (quota := d2FlowCandidateQuota (d + 2) 1)
    (cap := fun k => d2FlowCandidateCapacity (d + 2) k 1)
    (i := 0)
    (d2FlowCandidateRun (d + 2) (d2FlowTreeInitial 8192 (d + 2)) 1)
    hinv1 (d2FlowCandidateStage1_inputs d hd)
  change d2FlowTreeInv 8192
    (d2FlowCandidateStage (d + 2) 1
      (d2FlowCandidateRun (d + 2) (d2FlowTreeInitial 8192 (d + 2)) 1))
  simpa [d2FlowCandidateStage] using hpres

/-- Exact level-two endpoint profile after the first positive sender. In each
level-one subtree, only the first and last of its eight full children acquire
deficit, each equal to half the sender quota. -/
theorem d2FlowCandidateStage1_child_profile (d : Nat) (hd : 5 ≤ d)
    (j : Fin 8) :
    d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (d + 2) 1)
          (d2FlowCandidateRole (d + 2) 1)
          (d2FlowCandidateQuota (d + 2) 1)
          (d + 1) 1
          (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 d))) j) =
      if j.val = 0 then (2 ^ (3 * d + 7), 2 ^ (3 * d + 7), 0)
      else if j.val = 7 then (2 ^ (3 * d + 7), 0, 2 ^ (3 * d + 7))
      else (0, 0, 0) := by
  have hactive : d2FlowCandidateActive (d + 2) 1 1 = true := by
    simp [d2FlowCandidateActive]
  have hrole : d2FlowCandidateRole (d + 2) 1 1 = .topRise := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    exact d2ScheduleRole_first_sender (by omega)
  have hregular : d2FlowCandidateRole (d + 2) 1 1 = .topRise ∨
      d2FlowCandidateRole (d + 2) 1 1 = .mid ∨
      d2FlowCandidateRole (d + 2) 1 1 = .botDesc := Or.inl hrole
  have hquota : d2FlowCandidateQuota (d + 2) 1 1 .topRise =
      2 ^ (3 * d + 8) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    congr 1 <;> omega
  have hu : d2FlowTreeRootDeficit (d2FlowTreeFull 8192 d) =
      8192 * 8 ^ d := d2FlowTreeRootDeficit_full 8192 d
  have hposition : d2FlowPosition
      (fun _ : Fin 8 => d2FlowTreeRootDeficit (d2FlowTreeFull 8192 d)) j =
        j.val * (8192 * 8 ^ d) := by
    simpa [hu] using d2FlowPosition_uniform (8192 * 8 ^ d) j
  have htotal : d2FlowTotal
      (fun _ : Fin 8 => d2FlowTreeRootDeficit (d2FlowTreeFull 8192 d)) =
        8 * (8192 * 8 ^ d) := by
    simp [d2FlowTotal, hu]
  have hleft : 2 ^ (3 * d + 7) ≤ 8192 * 8 ^ d := by
    have hu' : 8192 * 8 ^ d = 2 ^ (3 * d + 13) := by
      rw [show (8192 : Nat) = 2 ^ 13 by norm_num,
        show (8 : Nat) = 2 ^ 3 by norm_num]
      rw [show 3 * d + 13 = 13 + 3 * d by omega, Nat.pow_add,
        ← Nat.pow_mul]
    rw [hu']
    have hfactor : 2 ^ (3 * d + 13) =
        2 ^ (3 * d + 7) * 2 ^ 6 := by
      rw [show 3 * d + 13 = (3 * d + 7) + 6 by omega, pow_add]
    rw [hfactor]
    norm_num
  have hcut := d2FlowStage_regular_child_setroot
    (active := d2FlowCandidateActive (d + 2) 1)
    (role := d2FlowCandidateRole (d + 2) 1)
    (quota := d2FlowCandidateQuota (d + 2) 1)
    (h := d) (i := 1) (G := 0) (low := 0) (high := 0)
    (children := fun _ : Fin 8 => d2FlowTreeFull 8192 d)
    hactive hregular j
  rw [hcut, d2FlowTreeRootData_setRoot]
  rw [hposition, htotal, hrole, hquota, hu]
  have hhalf : 2 ^ (3 * d + 8) / 2 = 2 ^ (3 * d + 7) := by
    have hpow : 2 ^ (3 * d + 8) = 2 ^ (3 * d + 7) * 2 := by
      rw [show 3 * d + 8 = (3 * d + 7) + 1 by omega, pow_succ]
    omega
  rw [hhalf]
  simp only [Nat.zero_add, Nat.sub_zero]
  exact d2FlowCutChild_uniform_profile hleft j

/-- Full subtrees beginning below the stage-two bottom frontier contribute no
sender obligations: at stage two, all levels at least three are inactive. -/
theorem d2FlowCandidateFull_stage2_inactive_inputs
    {d h i scale : Nat} (hi : 3 ≤ i) :
    d2FlowStageInvInputs scale
      (d2FlowCandidateActive (d + 2) 2)
      (d2FlowCandidateRole (d + 2) 2)
      (d2FlowCandidateQuota (d + 2) 2)
      (fun k => d2FlowCandidateCapacity (d + 2) k 2)
      i (d2FlowTreeFull scale h) := by
  induction h generalizing i with
  | zero => trivial
  | succ h ih =>
      simp only [d2FlowStageInvInputs, d2FlowTreeFull]
      constructor
      · intro j
        exact ih (i := i + 1) (by omega)
      · have hnot : ¬ (2 ≤ 2 ∧ 2 ≤ tfD2 (d + 2) ∧ i % 2 = 2 % 2 ∧
            3 * i + 3 * (d + 2) ≥ 2 * 2 + 11 ∧ 3 * i < 2 + 8) := by omega
        have hfalse : d2FlowCandidateActive (d + 2) 2 i = false := by
          simp only [d2FlowCandidateActive, if_neg (by decide : 2 ≠ 0),
            if_neg (by decide : 2 ≠ 1)]
          rw [decide_eq_false_iff_not]
          simpa using hnot
        simp [hfalse]

/-- Exact role at the newly exposed lower frontier in stage two. -/
theorem d2FlowCandidateStage2_boundary_role (d : Nat) (hd : 5 ≤ d) :
    d2FlowCandidateActive (d + 2) 2 2 = true ∧
      d2FlowCandidateRole (d + 2) 2 2 = .botDesc := by
  have hactive : d2FlowCandidateActive (d + 2) 2 2 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hrole : d2FlowCandidateRole (d + 2) 2 2 = .botDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    have ha2 : alpha (d + 2) 2 = 0 := by
      have hineq : 15 ≤ 3 * (d + 2) := by omega
      simp [alpha, alphaStar, hineq, ceilParity]
    have ha3 : alpha (d + 2) 3 = 1 := by
      have hineq : 17 ≤ 3 * (d + 2) := by omega
      simp [alpha, alphaStar, hineq, ceilParity]
    have ho2 : omega 2 = 2 := by simp [omega, ceilParity]
    have ho3 : omega 3 = 3 := by simp [omega, ceilParity]
    simp [d2ScheduleRole, ha2, ha3, ho2, ho3]
  exact ⟨hactive, hrole⟩

/-- The exact stage-two local gate for either endpoint child produced by the
first sender. It includes the tight reserve equality
`capacity = 128 * nativeChildSize`. -/
theorem d2FlowCandidateStage2_sender_inputs (d : Nat) (hd : 5 ≤ d)
    (G low high : Nat) (hG : G = 0 ∨ G = 2 ^ (3 * d + 7))
    (hbal : low + high = G) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 2)
      (d2FlowCandidateRole (d + 2) 2)
      (d2FlowCandidateQuota (d + 2) 2)
      (fun k => d2FlowCandidateCapacity (d + 2) k 2)
      2 (.node G low high (fun _ => d2FlowTreeFull 8192 (d - 1))) := by
  rcases d2FlowCandidateStage2_boundary_role d hd with ⟨hactive, hrole⟩
  have hcap : d2FlowCandidateCapacity (d + 2) 2 2 = 2 ^ (3 * d + 17) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    congr 1 <;> omega
  have hquota : d2FlowCandidateQuota (d + 2) 2 2 .botDesc =
      15 * 2 ^ (3 * d + 5) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    congr 1 <;> omega
  have hchild : d2FlowTreeRootDeficit (d2FlowTreeFull 8192 (d - 1)) =
      8192 * 8 ^ (d - 1) := d2FlowTreeRootDeficit_full 8192 (d - 1)
  have hchildPow : 8192 * 8 ^ (d - 1) = 2 ^ (3 * d + 10) := by
    rw [show (8192 : Nat) = 2 ^ 13 by norm_num,
      show (8 : Nat) = 2 ^ 3 by norm_num, ← Nat.pow_mul,
      ← pow_add]
    congr 1 <;> omega
  have htotal : d2FlowTotal (fun _ : Fin 8 =>
      d2FlowTreeRootDeficit (d2FlowTreeFull 8192 (d - 1))) =
        8 * (8192 * 8 ^ (d - 1)) := by
    simp [d2FlowTotal, hchild]
  have htotalFact : 8 * (8192 * 8 ^ (d - 1)) =
      256 * 2 ^ (3 * d + 5) := by
    rw [hchildPow]
    have hchildFact : 2 ^ (3 * d + 10) =
        32 * 2 ^ (3 * d + 5) := by
      rw [show 3 * d + 10 = 5 + (3 * d + 5) by omega, pow_add]
      norm_num
    rw [hchildFact]
    ring
  have hreserve : 2 ^ (3 * d + 17) ≤
      128 * (8192 * 8 ^ (d - 1)) := by
    rw [hchildPow]
    have heq : 2 ^ (3 * d + 17) = 128 * 2 ^ (3 * d + 10) := by
      rw [show 3 * d + 17 = 7 + (3 * d + 10) by omega, pow_add]
      norm_num
    rw [heq]
  have hGbound : G ≤ 2 ^ (3 * d + 7) := by
    rcases hG with hzero | hmax
    · simp [hzero]
    · exact le_of_eq hmax
  have hGfactor : 2 ^ (3 * d + 7) = 4 * 2 ^ (3 * d + 5) := by
    rw [show 3 * d + 7 = 2 + (3 * d + 5) by omega, pow_add]
    norm_num
  have hGscaled : 512 * G ≤ 2 ^ (3 * d + 17) := by
    calc
      512 * G ≤ 512 * 2 ^ (3 * d + 7) := Nat.mul_le_mul_left _ hGbound
      _ = 2 ^ (3 * d + 16) := by
        rw [show 512 = 2 ^ 9 by norm_num, ← pow_add]
        congr 1 <;> omega
      _ ≤ 2 ^ (3 * d + 17) := by
        have hstep : 2 ^ (3 * d + 17) =
            2 ^ (3 * d + 16) * 2 := by
          rw [show 3 * d + 17 = (3 * d + 16) + 1 by omega, pow_succ]
        rw [hstep]
        omega
  have hquotaScaled : 256 * (15 * 2 ^ (3 * d + 5)) ≤
      2 ^ (3 * d + 17) := by
    have hleft : 256 * (15 * 2 ^ (3 * d + 5)) =
        15 * 2 ^ (3 * d + 13) := by
      rw [show 256 = 2 ^ 8 by norm_num]
      calc
        2 ^ 8 * (15 * 2 ^ (3 * d + 5)) =
            15 * (2 ^ 8 * 2 ^ (3 * d + 5)) := by ring
        _ = 15 * 2 ^ (3 * d + 13) := by
          rw [← pow_add]
          congr 2 <;> omega
    have hright : 2 ^ (3 * d + 17) = 16 * 2 ^ (3 * d + 13) := by
      rw [show 3 * d + 17 = 4 + (3 * d + 13) by omega, pow_add]
      norm_num
    rw [hleft, hright]
    omega
  have halloc : 15 * 2 ^ (3 * d + 5) ≤
      d2FlowTotal (fun _ : Fin 8 =>
        d2FlowTreeRootDeficit (d2FlowTreeFull 8192 (d - 1))) - G := by
    rw [htotal, htotalFact]
    have hGbound' : G ≤ 4 * 2 ^ (3 * d + 5) := by
      rw [← hGfactor]
      exact hGbound
    omega
  have hquotaEven : (15 * 2 ^ (3 * d + 5)) % 2 = 0 := by
    have hpowEven : (2 ^ (3 * d + 5)) % 2 = 0 := by
      rw [show 3 * d + 5 = (3 * d + 4) + 1 by omega, pow_succ]
      simp
    omega
  have hGscaled' : 512 * G ≤ d2FlowCandidateCapacity (d + 2) 2 2 := by
    rw [hcap]
    exact hGscaled
  have hquotaScaled' : 256 * d2FlowCandidateQuota (d + 2) 2 2 .botDesc ≤
      d2FlowCandidateCapacity (d + 2) 2 2 := by
    rw [hquota, hcap]
    exact hquotaScaled
  have halloc' : d2FlowCandidateQuota (d + 2) 2 2 .botDesc ≤
      d2FlowTotal (fun _ : Fin 8 =>
        d2FlowTreeRootDeficit (d2FlowTreeFull 8192 (d - 1))) - G := by
    rw [hquota]
    exact halloc
  have hquotaEven' :
      d2FlowCandidateQuota (d + 2) 2 2 .botDesc % 2 = 0 := by
    rw [hquota]
    exact hquotaEven
  have hreserve' : d2FlowCandidateCapacity (d + 2) 2 2 ≤
      128 * d2FlowTreeRootDeficit (d2FlowTreeFull 8192 (d - 1)) := by
    rw [hcap, hchild]
    exact hreserve
  simp only [d2FlowStageInvInputs]
  constructor
  · intro j
    exact d2FlowCandidateFull_stage2_inactive_inputs
      (d := d) (h := d - 1) (i := 3) (scale := 8192) (by omega)
  · rw [hactive]
    simp only [if_true]
    constructor
    · exact hbal
    · rw [hrole]
      exact ⟨hGscaled', hquotaScaled', halloc', hquotaEven',
        hreserve', hreserve'⟩

/-- At stage one, every subtree below the top sender remains exactly full. -/
theorem d2FlowCandidateFull_stage1_inactive_eq
    {d h i scale : Nat} (hi : 2 ≤ i) :
    d2FlowStage (d2FlowCandidateActive (d + 2) 1)
      (d2FlowCandidateRole (d + 2) 1)
      (d2FlowCandidateQuota (d + 2) 1)
      h i (d2FlowTreeFull scale h) = d2FlowTreeFull scale h := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih =>
      have hactive : d2FlowCandidateActive (d + 2) 1 i = false := by
        simp [d2FlowCandidateActive, hi]
        omega
      simp [d2FlowStage, hactive, d2FlowTreeFull]
      congr 1
      funext j
      exact ih (i := i + 1) (by omega)

/-- The entire first-sender child, including its untouched full descendants,
has the endpoint profile required by the stage-two local gate. -/
theorem d2FlowCandidateStage1_child_tree (d : Nat) (hd : 5 ≤ d)
    (j : Fin 8) :
    d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (d + 2) 1)
          (d2FlowCandidateRole (d + 2) 1)
          (d2FlowCandidateQuota (d + 2) 1)
          (d + 1) 1 (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 d))) j =
      d2FlowTreeSetRoot (d2FlowTreeFull 8192 d)
        (if j.val = 0 then 2 ^ (3 * d + 7)
          else if j.val = 7 then 2 ^ (3 * d + 7) else 0)
        (if j.val = 0 then 2 ^ (3 * d + 7) else 0)
        (if j.val = 7 then 2 ^ (3 * d + 7) else 0) := by
  have hactive : d2FlowCandidateActive (d + 2) 1 1 = true := by
    simp [d2FlowCandidateActive]
  have hrole : d2FlowCandidateRole (d + 2) 1 1 = .topRise := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    exact d2ScheduleRole_first_sender (by omega)
  have hregular : d2FlowCandidateRole (d + 2) 1 1 = .topRise ∨
      d2FlowCandidateRole (d + 2) 1 1 = .mid ∨
      d2FlowCandidateRole (d + 2) 1 1 = .botDesc := Or.inl hrole
  have hcut := d2FlowStage_regular_child_setroot
    (active := d2FlowCandidateActive (d + 2) 1)
    (role := d2FlowCandidateRole (d + 2) 1)
    (quota := d2FlowCandidateQuota (d + 2) 1)
    (h := d) (i := 1) (G := 0) (low := 0) (high := 0)
    (children := fun _ : Fin 8 => d2FlowTreeFull 8192 d)
    hactive hregular j
  have hfull : d2FlowStage (d2FlowCandidateActive (d + 2) 1)
      (d2FlowCandidateRole (d + 2) 1)
      (d2FlowCandidateQuota (d + 2) 1) d 2
      (d2FlowTreeFull 8192 d) = d2FlowTreeFull 8192 d :=
    d2FlowCandidateFull_stage1_inactive_eq (d := d) (i := 2) (by omega)
  have htuple := d2FlowCandidateStage1_child_profile d hd j
  rw [hcut, hfull, d2FlowTreeRootData_setRoot] at htuple
  rw [hcut, hfull]
  split_ifs at htuple ⊢ <;> simp_all [d2FlowTreeSetRoot]

/-- Each actual level-two child left by stage one satisfies its own stage-two
sender-input contract, using the just-proved local boundary estimate. -/
theorem d2FlowCandidateStage1_child_stage2_inputs
    (d : Nat) (hd : 5 ≤ d) (j : Fin 8) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 2)
      (d2FlowCandidateRole (d + 2) 2)
      (d2FlowCandidateQuota (d + 2) 2)
      (fun k => d2FlowCandidateCapacity (d + 2) k 2)
      2 (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (d + 2) 1)
          (d2FlowCandidateRole (d + 2) 1)
          (d2FlowCandidateQuota (d + 2) 1)
          (d + 1) 1 (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 d))) j) := by
  rw [d2FlowCandidateStage1_child_tree d hd j]
  cases d with
  | zero => omega
  | succ d' =>
      by_cases h0 : j.val = 0
      · simpa [h0, d2FlowTreeSetRoot, d2FlowTreeFull] using
          (d2FlowCandidateStage2_sender_inputs (d := d' + 1) (by omega)
            (2 ^ (3 * (d' + 1) + 7))
            (2 ^ (3 * (d' + 1) + 7)) 0 (Or.inr rfl) (by simp))
      · by_cases h7 : j.val = 7
        · simpa [h0, h7, d2FlowTreeSetRoot, d2FlowTreeFull] using
            (d2FlowCandidateStage2_sender_inputs (d := d' + 1) (by omega)
              (2 ^ (3 * (d' + 1) + 7)) 0
              (2 ^ (3 * (d' + 1) + 7)) (Or.inr rfl) (by simp))
        · simpa [h0, h7, d2FlowTreeSetRoot, d2FlowTreeFull] using
            (d2FlowCandidateStage2_sender_inputs (d := d' + 1) (by omega)
              0 0 0 (Or.inl rfl) (by simp))

/-- The complete first-sender subtree satisfies the recursive stage-two input
predicate, not just its individual bottom-boundary nodes. -/
theorem d2FlowCandidateStage1_subtree_stage2_inputs
    (d : Nat) (hd : 5 ≤ d) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 2)
      (d2FlowCandidateRole (d + 2) 2)
      (d2FlowCandidateQuota (d + 2) 2)
      (fun k => d2FlowCandidateCapacity (d + 2) k 2)
      1 (d2FlowStage (d2FlowCandidateActive (d + 2) 1)
        (d2FlowCandidateRole (d + 2) 1)
        (d2FlowCandidateQuota (d + 2) 1)
        (d + 1) 1 (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 d))) := by
  have hfalse : d2FlowCandidateActive (d + 2) 2 1 = false := by
    simp [d2FlowCandidateActive]
  cases htree : d2FlowStage (d2FlowCandidateActive (d + 2) 1)
      (d2FlowCandidateRole (d + 2) 1)
      (d2FlowCandidateQuota (d + 2) 1)
      (d + 1) 1 (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 d)) with
  | node G low high children =>
      simp only [d2FlowStageInvInputs]
      constructor
      · intro j
        have hchild : children j = d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive (d + 2) 1)
              (d2FlowCandidateRole (d + 2) 1)
              (d2FlowCandidateQuota (d + 2) 1)
              (d + 1) 1 (.node 0 0 0
                (fun _ => d2FlowTreeFull 8192 d))) j := by
          rw [htree]
          rfl
        rw [hchild]
        exact d2FlowCandidateStage1_child_stage2_inputs d hd j
      · simp [hfalse]

/-- At the root, stage two is the top-descending cleanup sender. -/
theorem d2FlowCandidateStage2_root_role (d : Nat) (hd : 5 ≤ d) :
    d2FlowCandidateActive (d + 2) 2 0 = true ∧
      d2FlowCandidateRole (d + 2) 2 0 = .topDesc := by
  have hactive : d2FlowCandidateActive (d + 2) 2 0 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have ha2 : alpha (d + 2) 2 = 0 := by
    have hineq : 15 ≤ 3 * (d + 2) := by omega
    simp [alpha, alphaStar, hineq, ceilParity]
  have ha3 : alpha (d + 2) 3 = 1 := by
    have hineq : 17 ≤ 3 * (d + 2) := by omega
    simp [alpha, alphaStar, hineq, ceilParity]
  have hrole : d2FlowCandidateRole (d + 2) 2 0 = .topDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha2, ha3]
  exact ⟨hactive, hrole⟩

/-- The concrete candidate tree satisfies every sender premise in stage two.
Consequently the invariant-preservation interface now applies to stage two
itself, including the root top-descending cleanup. -/
theorem d2FlowCandidateStage2_inputs (d : Nat) (hd : 5 ≤ d) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 2)
      (d2FlowCandidateRole (d + 2) 2)
      (d2FlowCandidateQuota (d + 2) 2)
      (fun k => d2FlowCandidateCapacity (d + 2) k 2)
      0 (d2FlowCandidateRun (d + 2)
        (d2FlowTreeInitial 8192 (d + 2)) 2) := by
  have hrun1 : d2FlowCandidateRun (d + 2)
      (d2FlowTreeInitial 8192 (d + 2)) 1 =
      d2FlowCandidateStage (d + 2) 0
        (d2FlowTreeInitial 8192 (d + 2)) := rfl
  have htree : d2FlowCandidateRun (d + 2)
      (d2FlowTreeInitial 8192 (d + 2)) 2 =
      .node 0 0 0 (fun _ =>
        d2FlowStage (d2FlowCandidateActive (d + 2) 1)
          (d2FlowCandidateRole (d + 2) 1)
          (d2FlowCandidateQuota (d + 2) 1)
          (d + 1) 1 (.node 0 0 0
            (fun _ => d2FlowTreeFull 8192 d)) ) := by
    rw [show d2FlowCandidateRun (d + 2)
        (d2FlowTreeInitial 8192 (d + 2)) 2 =
          d2FlowCandidateStage (d + 2) 1
            (d2FlowCandidateRun (d + 2)
              (d2FlowTreeInitial 8192 (d + 2)) 1) by rfl,
      hrun1, d2FlowCandidateBootstrap_shape (d + 1)]
    simp [d2FlowCandidateStage, d2FlowStage, d2FlowCandidateActive,
      d2FlowTreeSetRoot, d2FlowTreeFull]
  rcases d2FlowCandidateStage2_root_role d hd with ⟨hactive, hrole⟩
  rw [htree]
  simp only [d2FlowStageInvInputs]
  constructor
  · intro j
    exact d2FlowCandidateStage1_subtree_stage2_inputs d hd
  · rw [hactive]
    simp only [if_true]
    constructor
    · trivial
    · rw [hrole]
      trivial

/-- The saturated-aware tree invariant is now established through the complete
second scheduled stage for every dimension at least seven. -/
theorem d2FlowCandidateStage2_preserves_inv (d : Nat) (hd : 5 ≤ d) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (d + 2)
        (d2FlowTreeInitial 8192 (d + 2)) 3) := by
  have hinv := d2FlowCandidateStage1_preserves_inv d hd
  have hpres := d2FlowStage_preserves_inv_of_inputs
    (active := d2FlowCandidateActive (d + 2) 2)
    (role := d2FlowCandidateRole (d + 2) 2)
    (quota := d2FlowCandidateQuota (d + 2) 2)
    (cap := fun k => d2FlowCandidateCapacity (d + 2) k 2)
    (i := 0)
    (d2FlowCandidateRun (d + 2)
      (d2FlowTreeInitial 8192 (d + 2)) 2)
    hinv (d2FlowCandidateStage2_inputs d hd)
  change d2FlowTreeInv 8192
    (d2FlowCandidateStage (d + 2) 2
      (d2FlowCandidateRun (d + 2)
        (d2FlowTreeInitial 8192 (d + 2)) 2))
  simpa [d2FlowCandidateStage] using hpres

/-- Exact child-root profile for a stage-two bottom-descending sender with
full equal-sized children. This isolates the arithmetic needed to initialize
the stage-three bottom-rise nodes. -/
theorem d2FlowCandidateStage2_child_profile
    (d h : Nat) (hd : 5 ≤ d) (G low high left tail : Nat)
    (hleftFront : low +
      d2FlowCandidateQuota (d + 2) 2 2 .botDesc / 2 = left)
    (htailFront : high +
      d2FlowCandidateQuota (d + 2) 2 2 .botDesc / 2 = tail)
    (hleft : left ≤ 8192 * 8 ^ h)
    (htail : tail ≤ 8192 * 8 ^ h) (j : Fin 8) :
    d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (d + 2) 2)
          (d2FlowCandidateRole (d + 2) 2)
          (d2FlowCandidateQuota (d + 2) 2)
          (h + 1) 2 (.node G low high (fun _ =>
            d2FlowTreeFull 8192 h))) j) =
      if j.val = 0 then (left, left, 0)
      else if j.val = 7 then (tail, 0, tail)
      else (0, 0, 0) := by
  rcases d2FlowCandidateStage2_boundary_role d hd with ⟨hactive, hrole⟩
  have hquota : d2FlowCandidateQuota (d + 2) 2 2 .botDesc =
      15 * 2 ^ (3 * d + 5) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    congr 1 <;> omega
  have hu : d2FlowTreeRootDeficit
      (d2FlowTreeFull 8192 h) = 8192 * 8 ^ h :=
    d2FlowTreeRootDeficit_full 8192 h
  have hposition : d2FlowPosition
      (fun _ : Fin 8 => d2FlowTreeRootDeficit
        (d2FlowTreeFull 8192 h)) j =
        j.val * (8192 * 8 ^ h) := by
    simpa [hu] using d2FlowPosition_uniform (8192 * 8 ^ h) j
  have htotal : d2FlowTotal
      (fun _ : Fin 8 => d2FlowTreeRootDeficit
        (d2FlowTreeFull 8192 h)) =
          8 * (8192 * 8 ^ h) := by
    simp [d2FlowTotal, hu]
  have hregular : d2FlowCandidateRole (d + 2) 2 2 = .topRise ∨
      d2FlowCandidateRole (d + 2) 2 2 = .mid ∨
      d2FlowCandidateRole (d + 2) 2 2 = .botDesc := Or.inr (Or.inr hrole)
  have hcut := d2FlowStage_regular_child_setroot
    (active := d2FlowCandidateActive (d + 2) 2)
    (role := d2FlowCandidateRole (d + 2) 2)
    (quota := d2FlowCandidateQuota (d + 2) 2)
    (h := h) (i := 2) (G := G) (low := low) (high := high)
    (children := fun _ : Fin 8 => d2FlowTreeFull 8192 h)
    hactive hregular j
  rw [hcut, d2FlowTreeRootData_setRoot]
  rw [hposition, htotal, hu, hrole, hquota]
  have hleftFront' : low + (15 * 2 ^ (3 * d + 5)) / 2 = left := by
    rw [← hquota]
    exact hleftFront
  have htailFront' : high + (15 * 2 ^ (3 * d + 5)) / 2 = tail := by
    rw [← hquota]
    exact htailFront
  rw [hleftFront']
  have hright : 8 * (8192 * 8 ^ h) - high -
      (15 * 2 ^ (3 * d + 5)) / 2 =
        8 * (8192 * 8 ^ h) - tail := by omega
  rw [hright]
  exact d2FlowCutChild_uniform_asymmetric hleft htail j

/-- The first-stage endpoint deficits plus the stage-two half-quota fit inside
one full level-three child; this discharges the containment premise for the
asymmetric stage-two cut profile. -/
theorem d2FlowCandidateStage2_fronts_fit
    (d : Nat) (hd : 5 ≤ d) (low high : Nat)
    (hlow : low ≤ 2 ^ (3 * d + 7))
    (hhigh : high ≤ 2 ^ (3 * d + 7)) :
    low + d2FlowCandidateQuota (d + 2) 2 2 .botDesc / 2 ≤
        8192 * 8 ^ (d - 1) ∧
      high + d2FlowCandidateQuota (d + 2) 2 2 .botDesc / 2 ≤
        8192 * 8 ^ (d - 1) := by
  have hquota : d2FlowCandidateQuota (d + 2) 2 2 .botDesc =
      15 * 2 ^ (3 * d + 5) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    congr 1 <;> omega
  have hhalf : d2FlowCandidateQuota (d + 2) 2 2 .botDesc / 2 =
      15 * 2 ^ (3 * d + 4) := by
    rw [hquota, show 3 * d + 5 = (3 * d + 4) + 1 by omega,
      pow_succ]
    omega
  have hu : 8192 * 8 ^ (d - 1) =
      64 * 2 ^ (3 * d + 4) := by
    have hu' : 8192 * 8 ^ (d - 1) = 2 ^ (3 * d + 10) := by
      rw [show (8192 : Nat) = 2 ^ 13 by norm_num,
        show (8 : Nat) = 2 ^ 3 by norm_num, ← Nat.pow_mul,
        ← pow_add]
      congr 1 <;> omega
    rw [hu', show 3 * d + 10 = 6 + (3 * d + 4) by omega,
      pow_add]
    norm_num
  have hdeficitFactor : 2 ^ (3 * d + 7) =
      8 * 2 ^ (3 * d + 4) := by
    rw [show 3 * d + 7 = 3 + (3 * d + 4) by omega, pow_add]
    norm_num
  rw [hdeficitFactor] at hlow hhigh
  constructor <;> rw [hhalf, hu] <;> omega

/-- The stage-three active band has only levels one and three; all deeper
subtrees satisfy the recursive premise without sender arithmetic. -/
theorem d2FlowCandidateAny_stage3_inactive_inputs
    {d h i : Nat} (hi : 4 ≤ i) (tree : D2FlowTree h) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 3)
      (d2FlowCandidateRole (d + 2) 3)
      (d2FlowCandidateQuota (d + 2) 3)
      (fun k => d2FlowCandidateCapacity (d + 2) k 3)
      i tree := by
  induction tree generalizing i with
  | leaf G low high => trivial
  | node G low high children ih =>
      simp only [d2FlowStageInvInputs]
      constructor
      · intro j
        exact ih (i := i + 1) j (by omega)
      · have hnot : ¬ (2 ≤ 3 ∧ 3 ≤ tfD2 (d + 2) ∧
            i % 2 = 3 % 2 ∧ 3 * i + 3 * (d + 2) ≥ 2 * 3 + 11 ∧
            3 * i < 3 + 8) := by omega
        have hfalse : d2FlowCandidateActive (d + 2) 3 i = false := by
          simp only [d2FlowCandidateActive, if_neg (by decide : 3 ≠ 0),
            if_neg (by decide : 3 ≠ 1)]
          rw [decide_eq_false_iff_not]
          simpa using hnot
        simp [hfalse]

/-- Exact stage-three schedule frontier: level one rises from the top and
level three rises from the bottom. -/
theorem d2FlowCandidateStage3_frontiers (d : Nat) (hd : 5 ≤ d) :
    d2FlowCandidateActive (d + 2) 3 1 = true ∧
      d2FlowCandidateRole (d + 2) 3 1 = .topRise ∧
      d2FlowCandidateActive (d + 2) 3 3 = true ∧
      d2FlowCandidateRole (d + 2) 3 3 = .botRise := by
  have hactive1 : d2FlowCandidateActive (d + 2) 3 1 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive3 : d2FlowCandidateActive (d + 2) 3 3 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have ha3 : alpha (d + 2) 3 = 1 := by
    have hineq : 17 ≤ 3 * (d + 2) := by omega
    simp [alpha, alphaStar, hineq, ceilParity]
  have ha4 : alpha (d + 2) 4 = 0 := by
    have hineq : 19 ≤ 3 * (d + 2) := by omega
    simp [alpha, alphaStar, hineq, ceilParity]
  have ho3 : omega 3 = 3 := by simp [omega, ceilParity]
  have ho4 : omega 4 = 2 := by simp [omega, ceilParity]
  have hrole1 : d2FlowCandidateRole (d + 2) 3 1 = .topRise := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha3, ha4, ho3, ho4]
  have hrole3 : d2FlowCandidateRole (d + 2) 3 3 = .botRise := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha3, ha4, ho3, ho4]
  exact ⟨hactive1, hrole1, hactive3, hrole3⟩

/-- Stage four returns to the level-zero top-descending cleanup and the
level-two bottom-descending sender. -/
theorem d2FlowCandidateStage4_frontiers (d : Nat) (hd : 5 ≤ d) :
    d2FlowCandidateActive (d + 2) 4 0 = true ∧
      d2FlowCandidateRole (d + 2) 4 0 = .topDesc ∧
      d2FlowCandidateActive (d + 2) 4 2 = true ∧
      d2FlowCandidateRole (d + 2) 4 2 = .botDesc := by
  have hactive0 : d2FlowCandidateActive (d + 2) 4 0 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive2 : d2FlowCandidateActive (d + 2) 4 2 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have ha4 : alpha (d + 2) 4 = 0 := by
    have hineq : 19 ≤ 3 * (d + 2) := by omega
    simp [alpha, alphaStar, hineq, ceilParity]
  have ha5 : alpha (d + 2) 5 = 1 := by
    have hineq : 21 ≤ 3 * (d + 2) := by omega
    simp [alpha, alphaStar, hineq, ceilParity]
  have ho4 : omega 4 = 2 := by simp [omega, ceilParity]
  have ho5 : omega 5 = 3 := by simp [omega, ceilParity]
  have hrole0 : d2FlowCandidateRole (d + 2) 4 0 = .topDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha4, ha5]
  have hrole2 : d2FlowCandidateRole (d + 2) 4 2 = .botDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha4, ha5, ho4, ho5]
  exact ⟨hactive0, hrole0, hactive2, hrole2⟩

/-- The stage-four cut has no senders at levels three and four. -/
theorem d2FlowCandidateStage4_inactive_below_frontier (d : Nat) :
    d2FlowCandidateActive (d + 3) 4 3 = false ∧
      d2FlowCandidateActive (d + 3) 4 4 = false := by
  constructor <;> simp [d2FlowCandidateActive, tfD2] <;> omega

/-- A factor of two after the stage-four level-two cut is exactly the
stage-five level-three sender capacity. -/
theorem d2FlowCandidateStage4_to_stage5_capacity (d : Nat) :
    2 * d2FlowCandidateCapacity (d + 3) 2 4 =
      d2FlowCandidateCapacity (d + 3) 3 5 := by
  have hexp : d2FlowCandidateCapacityExponent (d + 3) 3 5 =
      d2FlowCandidateCapacityExponent (d + 3) 2 4 + 1 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  unfold d2FlowCandidateCapacity
  rw [hexp, Nat.pow_succ]
  exact Nat.mul_comm _ _

/-- At large enough dimensions stage five moves the top frontier inward as a
top-rise sender while the bottom frontier advances as a bottom-descending
sender. -/
theorem d2FlowCandidateStage5_frontiers (d : Nat) (hd : 9 ≤ d) :
    d2FlowCandidateActive d 5 1 = true ∧
      d2FlowCandidateRole d 5 1 = .topRise ∧
      d2FlowCandidateActive d 5 3 = true ∧
      d2FlowCandidateRole d 5 3 = .botDesc := by
  have hactive1 : d2FlowCandidateActive d 5 1 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive3 : d2FlowCandidateActive d 5 3 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have ha5 : alpha d 5 = 1 := by
    have h : 21 ≤ 3 * d := by omega
    simp [alpha, alphaStar, h, ceilParity]
  have ha6 : alpha d 6 = 0 := by
    have h : 23 ≤ 3 * d := by omega
    simp [alpha, alphaStar, h, ceilParity]
  have ho5 : omega 5 = 3 := by simp [omega, ceilParity]
  have ho6 : omega 6 = 4 := by simp [omega, ceilParity]
  have hrole1 : d2FlowCandidateRole d 5 1 = .topRise := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha5, ha6]
  have hrole3 : d2FlowCandidateRole d 5 3 = .botDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha5, ha6, ho5, ho6]
  exact ⟨hactive1, hrole1, hactive3, hrole3⟩

/-- The first repeating-schedule transition activates the root cleanup, the
level-two middle sender, and the level-four bottom-rise sender. -/
theorem d2FlowCandidateStage6_frontiers (d : Nat) (hd : 9 ≤ d) :
    d2FlowCandidateActive d 6 0 = true ∧
      d2FlowCandidateRole d 6 0 = .topDesc ∧
      d2FlowCandidateActive d 6 2 = true ∧
      d2FlowCandidateRole d 6 2 = .mid ∧
      d2FlowCandidateActive d 6 4 = true ∧
      d2FlowCandidateRole d 6 4 = .botRise ∧
      d2FlowCandidateActive d 6 6 = false := by
  have hactive0 : d2FlowCandidateActive d 6 0 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive2 : d2FlowCandidateActive d 6 2 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive4 : d2FlowCandidateActive d 6 4 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hinactive6 : d2FlowCandidateActive d 6 6 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have ha6 : alpha d 6 = 0 := by
    have h : 23 ≤ 3 * d := by omega
    simp [alpha, alphaStar, h, ceilParity]
  have ha7 : alpha d 7 = 1 := by
    have h : 25 ≤ 3 * d := by omega
    simp [alpha, alphaStar, h, ceilParity]
  have ho6 : omega 6 = 4 := by simp [omega, ceilParity]
  have ho7 : omega 7 = 3 := by simp [omega, ceilParity]
  have hrole0 : d2FlowCandidateRole d 6 0 = .topDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha6, ha7]
  have hrole2 : d2FlowCandidateRole d 6 2 = .mid := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha6, ha7, ho6, ho7]
  have hrole4 : d2FlowCandidateRole d 6 4 = .botRise := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha6, ha7, ho6, ho7]
  exact ⟨hactive0, hrole0, hactive2, hrole2, hactive4, hrole4,
    hinactive6⟩

/-- Stage seven repeats the ordinary top-rise/bottom-descending pair from
stage five, now behind the checked first repeating transition. -/
theorem d2FlowCandidateStage7_frontiers (d : Nat) (hd : 9 ≤ d) :
    d2FlowCandidateActive d 7 1 = true ∧
      d2FlowCandidateRole d 7 1 = .topRise ∧
      d2FlowCandidateActive d 7 3 = true ∧
      d2FlowCandidateRole d 7 3 = .botDesc ∧
      d2FlowCandidateActive d 7 5 = false := by
  have hactive1 : d2FlowCandidateActive d 7 1 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive3 : d2FlowCandidateActive d 7 3 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hinactive5 : d2FlowCandidateActive d 7 5 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have ha7 : alpha d 7 = 1 := by
    have h : 25 ≤ 3 * d := by omega
    simp [alpha, alphaStar, h, ceilParity]
  have ha8 : alpha d 8 = 0 := by
    have h : 27 ≤ 3 * d := by omega
    simp [alpha, alphaStar, h, ceilParity]
  have ho7 : omega 7 = 3 := by simp [omega, ceilParity]
  have ho8 : omega 8 = 4 := by simp [omega, ceilParity]
  have hrole1 : d2FlowCandidateRole d 7 1 = .topRise := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha7, ha8]
  have hrole3 : d2FlowCandidateRole d 7 3 = .botDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha7, ha8, ho7, ho8]
  exact ⟨hactive1, hrole1, hactive3, hrole3, hinactive5⟩

/-- Stage eight is the next exact local pattern once `d>=10`: a root
top-descending sender, level-two mid sender, and level-four
bottom-descending sender. -/
theorem d2FlowCandidateStage8_frontiers (d : Nat) (hd : 10 ≤ d) :
    d2FlowCandidateActive d 8 0 = true ∧
      d2FlowCandidateRole d 8 0 = .topDesc ∧
      d2FlowCandidateActive d 8 2 = true ∧
      d2FlowCandidateRole d 8 2 = .mid ∧
      d2FlowCandidateActive d 8 4 = true ∧
      d2FlowCandidateRole d 8 4 = .botDesc ∧
      d2FlowCandidateActive d 8 6 = false := by
  have hactive0 : d2FlowCandidateActive d 8 0 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive2 : d2FlowCandidateActive d 8 2 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive4 : d2FlowCandidateActive d 8 4 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hinactive6 : d2FlowCandidateActive d 8 6 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have ha8 : alpha d 8 = 0 := by
    have h : 27 ≤ 3 * d := by omega
    simp [alpha, alphaStar, h, ceilParity]
  have ha9 : alpha d 9 = 1 := by
    have h : 29 ≤ 3 * d := by omega
    simp [alpha, alphaStar, h, ceilParity]
  have ho8 : omega 8 = 4 := by simp [omega, ceilParity]
  have ho9 : omega 9 = 5 := by simp [omega, ceilParity]
  have hrole0 : d2FlowCandidateRole d 8 0 = .topDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha8, ha9]
  have hrole2 : d2FlowCandidateRole d 8 2 = .mid := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha8, ho8]
  have hrole4 : d2FlowCandidateRole d 8 4 = .botDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha8, ho8, ho9]
  exact ⟨hactive0, hrole0, hactive2, hrole2,
    hactive4, hrole4, hinactive6⟩

/-- For `d>=11`, the next phase activates a level-one top-rising sender, a level-three
mid sender, and a level-five bottom-rise sender. -/
theorem d2FlowCandidateStage9_frontiers (d : Nat) (hd : 11 ≤ d) :
    d2FlowCandidateActive d 9 1 = true ∧
      d2FlowCandidateRole d 9 1 = .topRise ∧
      d2FlowCandidateActive d 9 3 = true ∧
      d2FlowCandidateRole d 9 3 = .mid ∧
      d2FlowCandidateActive d 9 5 = true ∧
      d2FlowCandidateRole d 9 5 = .botRise ∧
      d2FlowCandidateActive d 9 7 = false := by
  have hactive1 : d2FlowCandidateActive d 9 1 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive3 : d2FlowCandidateActive d 9 3 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive5 : d2FlowCandidateActive d 9 5 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hinactive7 : d2FlowCandidateActive d 9 7 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have ha9 : alpha d 9 = 1 := by
    have h : 29 ≤ 3 * d := by omega
    simp [alpha, alphaStar, h, ceilParity]
  have ha10 : alpha d 10 = 0 := by
    have h : 31 ≤ 3 * d := by omega
    simp [alpha, alphaStar, h, ceilParity]
  have ho9 : omega 9 = 5 := by simp [omega, ceilParity]
  have ho10 : omega 10 = 4 := by simp [omega, ceilParity]
  have hrole1 : d2FlowCandidateRole d 9 1 = .topRise := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha9, ha10]
  have hrole3 : d2FlowCandidateRole d 9 3 = .mid := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha9, ho9]
  have hrole5 : d2FlowCandidateRole d 9 5 = .botRise := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha9, ho9, ho10]
  exact ⟨hactive1, hrole1, hactive3, hrole3,
    hactive5, hrole5, hinactive7⟩

/-- At stage ten the active frontier is at levels zero, two, and four: the
root descends, the middle sender is regular, and the bottom sender descends. -/
theorem d2FlowCandidateStage10_frontiers (d : Nat) (hd : 11 ≤ d) :
    d2FlowCandidateActive d 10 0 = true ∧
      d2FlowCandidateRole d 10 0 = .topDesc ∧
      d2FlowCandidateActive d 10 2 = true ∧
      d2FlowCandidateRole d 10 2 = .mid ∧
      d2FlowCandidateActive d 10 4 = true ∧
      d2FlowCandidateRole d 10 4 = .botDesc ∧
      d2FlowCandidateActive d 10 6 = false := by
  have hactive0 : d2FlowCandidateActive d 10 0 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive2 : d2FlowCandidateActive d 10 2 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive4 : d2FlowCandidateActive d 10 4 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hinactive6 : d2FlowCandidateActive d 10 6 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have ha10 : alpha d 10 = 0 := by
    simp [alpha, alphaStar, show 31 ≤ 3 * d by omega, ceilParity]
  have ha11 : alpha d 11 = 1 := by
    simp [alpha, alphaStar, show 33 ≤ 3 * d by omega, ceilParity]
  have ho10 : omega 10 = 4 := by norm_num [omega, ceilParity]
  have ho11 : omega 11 = 5 := by norm_num [omega, ceilParity]
  have hrole0 : d2FlowCandidateRole d 10 0 = .topDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha10, ha11]
  have hrole2 : d2FlowCandidateRole d 10 2 = .mid := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha10, ho10]
  have hrole4 : d2FlowCandidateRole d 10 4 = .botDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha10, ho10, ho11]
  exact ⟨hactive0, hrole0, hactive2, hrole2,
    hactive4, hrole4, hinactive6⟩

/-- Stage eleven has the shifted level-one/three/five frontier. For `d>=12`
the top sender rises, the middle remains regular, and the bottom descends. -/
theorem d2FlowCandidateStage11_frontiers (d : Nat) (hd : 12 ≤ d) :
    d2FlowCandidateActive d 11 1 = true ∧
      d2FlowCandidateRole d 11 1 = .topRise ∧
      d2FlowCandidateActive d 11 3 = true ∧
      d2FlowCandidateRole d 11 3 = .mid ∧
      d2FlowCandidateActive d 11 5 = true ∧
      d2FlowCandidateRole d 11 5 = .botDesc ∧
      d2FlowCandidateActive d 11 7 = false := by
  have hactive1 : d2FlowCandidateActive d 11 1 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive3 : d2FlowCandidateActive d 11 3 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive5 : d2FlowCandidateActive d 11 5 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hinactive7 : d2FlowCandidateActive d 11 7 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have ha11 : alpha d 11 = 1 := by
    simp [alpha, alphaStar, show 33 ≤ 3 * d by omega, ceilParity]
  have ha12 : alpha d 12 = 0 := by
    simp [alpha, alphaStar, show 35 ≤ 3 * d by omega, ceilParity]
  have ho11 : omega 11 = 5 := by norm_num [omega, ceilParity]
  have ho12 : omega 12 = 6 := by norm_num [omega, ceilParity]
  have hrole1 : d2FlowCandidateRole d 11 1 = .topRise := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha11, ha12]
  have hrole3 : d2FlowCandidateRole d 11 3 = .mid := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha11, ho11]
  have hrole5 : d2FlowCandidateRole d 11 5 = .botDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha11, ho11, ho12]
  exact ⟨hactive1, hrole1, hactive3, hrole3,
    hactive5, hrole5, hinactive7⟩

/-- The depth-eleven startup boundary differs only in Stage 11's top role. -/
theorem d2FlowCandidateStage11_frontiers_depth11 :
    d2FlowCandidateActive 11 11 1 = true ∧
      d2FlowCandidateRole 11 11 1 = .topDesc ∧
      d2FlowCandidateActive 11 11 3 = true ∧
      d2FlowCandidateRole 11 11 3 = .mid ∧
      d2FlowCandidateActive 11 11 5 = true ∧
      d2FlowCandidateRole 11 11 5 = .botDesc ∧
      d2FlowCandidateActive 11 11 7 = false := by
  have hactive1 : d2FlowCandidateActive 11 11 1 = true := by
    simp [d2FlowCandidateActive, tfD2]
  have hactive3 : d2FlowCandidateActive 11 11 3 = true := by
    simp [d2FlowCandidateActive, tfD2]
  have hactive5 : d2FlowCandidateActive 11 11 5 = true := by
    simp [d2FlowCandidateActive, tfD2]
  have hinactive7 : d2FlowCandidateActive 11 11 7 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have ha11 : alpha 11 11 = 1 := by norm_num [alpha, alphaStar, ceilParity]
  have ha12 : alpha 11 12 = 2 := by norm_num [alpha, alphaStar, ceilParity]
  have ho11 : omega 11 = 5 := by norm_num [omega, ceilParity]
  have ho12 : omega 12 = 6 := by norm_num [omega, ceilParity]
  have hrole1 : d2FlowCandidateRole 11 11 1 = .topDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha11, ha12]
  have hrole3 : d2FlowCandidateRole 11 11 3 = .mid := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha11, ho11]
  have hrole5 : d2FlowCandidateRole 11 11 5 = .botDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha11, ho11, ho12]
  exact ⟨hactive1, hrole1, hactive3, hrole3,
    hactive5, hrole5, hinactive7⟩

/-- The stage-ten endpoint reserve and sender cap pay its bottom-descending
quota by concentrating the mass estimate in either endpoint child. -/
theorem d2FlowCandidateStage10_boundary_mass_suffices
    (d : Nat) (hd : 11 ≤ d) (G : Nat) {r : Nat}
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 4 10)
    (children : Fin 8 → D2FlowTree r)
    (hleft : d2FlowCandidateCapacity d 4 10 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩)) :
    d2FlowCandidateQuota d 10 4 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
  have hcap : d2FlowCandidateCapacity d 4 10 = 2 ^ (3 * d + 1) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 10 4 .botDesc =
      15 * 2 ^ (3 * d - 11) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hGsmall : G ≤ 2 ^ (3 * d - 8) := by
    rw [hcap] at hG
    have hp : 512 * 2 ^ (3 * d - 8) = 2 ^ (3 * d + 1) := by
      rw [show (512 : Nat) = 2 ^ 9 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hroot : 2 ^ (3 * d - 6) ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hcap] at hleft
    have hp : 128 * 2 ^ (3 * d - 6) = 2 ^ (3 * d + 1) := by
      rw [show (128 : Nat) = 2 ^ 7 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hrootTotal : d2FlowTreeRootDeficit (children ⟨0, by omega⟩) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    let f : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
    change f ⟨0, by omega⟩ ≤ Finset.univ.sum f
    exact Finset.single_le_sum
      (fun j hj => Nat.zero_le (f j)) (Finset.mem_univ (⟨0, by omega⟩ : Fin 8))
  have hpG : 2 ^ (3 * d - 8) = 8 * 2 ^ (3 * d - 11) := by
    rw [show 3 * d - 8 = 3 + (3 * d - 11) by omega, pow_add]
    norm_num
  have hpRoot : 2 ^ (3 * d - 6) = 32 * 2 ^ (3 * d - 11) := by
    rw [show 3 * d - 6 = 5 + (3 * d - 11) by omega, pow_add]
    norm_num
  have hmass : G + d2FlowCandidateQuota d 10 4 .botDesc ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hquota]
    rw [hpG] at hGsmall
    rw [hpRoot] at hroot
    nlinarith
  have hmassTotal : G + d2FlowCandidateQuota d 10 4 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) :=
    le_trans hmass hrootTotal
  omega

/-- Complete local input gate for a stage-ten level-four bottom-descending
sender, from its cap, balance, and endpoint reserves. -/
theorem d2FlowCandidateStage10_botDesc_inputs
    (d : Nat) (hd : 11 ≤ d) (G low high : Nat) {r : Nat}
    (hbalance : low + high = G)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 4 10)
    (children : Fin 8 → D2FlowTree r)
    (hleft : d2FlowCandidateCapacity d 4 10 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hright : d2FlowCandidateCapacity d 4 10 ≤
      128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩))
    (htotal : d2FlowCandidateQuota d 10 4 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 10)
      (d2FlowCandidateRole d 10)
      (d2FlowCandidateQuota d 10)
      (fun k => d2FlowCandidateCapacity d k 10) 4
      (.node G low high children) := by
  rcases d2FlowCandidateStage10_frontiers d hd with
    ⟨_, _, _, _, hactive, hrole, _⟩
  have hcap : d2FlowCandidateCapacity d 4 10 = 2 ^ (3 * d + 1) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 10 4 .botDesc =
      15 * 2 ^ (3 * d - 11) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hquotaEven : d2FlowCandidateQuota d 10 4 .botDesc % 2 = 0 := by
    rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 11 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 10 4 .botDesc ≤
      d2FlowCandidateCapacity d 4 10 := by
    rw [hquota, hcap]
    have hp : 256 * 2 ^ (3 * d - 11) = 2 ^ (3 * d - 3) := by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_add]
      congr 1 <;> omega
    have hpCap : 2 ^ (3 * d + 1) = 16 * 2 ^ (3 * d - 3) := by
      rw [show 3 * d + 1 = 4 + (3 * d - 3) by omega, pow_add]
      norm_num
    nlinarith [hp, hpCap]
  have hrecursive : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 10)
      (d2FlowCandidateRole d 10)
      (d2FlowCandidateQuota d 10)
      (fun k => d2FlowCandidateCapacity d k 10) 5 (children j) := by
    intro j
    apply d2FlowStageInvInputs_all_inactive
    intro k hk
    simp [d2FlowCandidateActive, tfD2]
    omega
  simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
  exact ⟨hrecursive, ⟨hbalance, hG, hquotaCap, htotal, hquotaEven,
    hleft, hright⟩⟩

/-- The Stage 11 level-five bot-descending endpoint reserve and sender cap
imply its quota fits in the children. -/
theorem d2FlowCandidateStage11_boundary_mass_suffices
    (d : Nat) (hd : 12 ≤ d) (G : Nat)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 5 11) {r : Nat}
    (children : Fin 8 → D2FlowTree r)
    (hleft : d2FlowCandidateCapacity d 5 11 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩)) :
    d2FlowCandidateQuota d 11 5 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
  have hcap : d2FlowCandidateCapacity d 5 11 = 2 ^ (3 * d + 2) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 11 5 .botDesc =
      15 * 2 ^ (3 * d - 10) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hGsmall : G ≤ 2 ^ (3 * d - 7) := by
    rw [hcap] at hG
    have hp : 512 * 2 ^ (3 * d - 7) = 2 ^ (3 * d + 2) := by
      rw [show (512 : Nat) = 2 ^ 9 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hroot : 2 ^ (3 * d - 5) ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hcap] at hleft
    have hp : 128 * 2 ^ (3 * d - 5) = 2 ^ (3 * d + 2) := by
      rw [show (128 : Nat) = 2 ^ 7 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hrootTotal : d2FlowTreeRootDeficit (children ⟨0, by omega⟩) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    let f : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
    change f ⟨0, by omega⟩ ≤ Finset.univ.sum f
    exact Finset.single_le_sum
      (fun j hj => Nat.zero_le (f j))
      (Finset.mem_univ (⟨0, by omega⟩ : Fin 8))
  have hpG : 2 ^ (3 * d - 7) = 8 * 2 ^ (3 * d - 10) := by
    rw [show 3 * d - 7 = 3 + (3 * d - 10) by omega, pow_add]
    norm_num
  have hpRoot : 2 ^ (3 * d - 5) = 32 * 2 ^ (3 * d - 10) := by
    rw [show 3 * d - 5 = 5 + (3 * d - 10) by omega, pow_add]
    norm_num
  have hmass : G + d2FlowCandidateQuota d 11 5 .botDesc ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hquota]
    rw [hpG] at hGsmall
    rw [hpRoot] at hroot
    nlinarith
  have hmassTotal : G + d2FlowCandidateQuota d 11 5 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) :=
    le_trans hmass hrootTotal
  omega

/-- Complete local recursive input gate for a Stage 11 level-five
bot-descending sender. -/
theorem d2FlowCandidateStage11_botDesc_inputs
    (d : Nat) (hd : 12 ≤ d) (G low high : Nat) {r : Nat}
    (hbalance : low + high = G)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 5 11)
    (children : Fin 8 → D2FlowTree r)
    (hleft : d2FlowCandidateCapacity d 5 11 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hright : d2FlowCandidateCapacity d 5 11 ≤
      128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩))
    (htotal : d2FlowCandidateQuota d 11 5 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 11)
      (d2FlowCandidateRole d 11)
      (d2FlowCandidateQuota d 11)
      (fun k => d2FlowCandidateCapacity d k 11) 5
      (.node G low high children) := by
  rcases d2FlowCandidateStage11_frontiers d hd with
    ⟨_, _, _, _, hactive, hrole, _⟩
  have hcap : d2FlowCandidateCapacity d 5 11 = 2 ^ (3 * d + 2) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 11 5 .botDesc =
      15 * 2 ^ (3 * d - 10) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hquotaEven : d2FlowCandidateQuota d 11 5 .botDesc % 2 = 0 := by
    rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 10 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 11 5 .botDesc ≤
      d2FlowCandidateCapacity d 5 11 := by
    rw [hquota, hcap]
    have hp : 256 * 2 ^ (3 * d - 10) = 2 ^ (3 * d - 2) := by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_add]
      congr 1 <;> omega
    have hpCap : 2 ^ (3 * d + 2) = 16 * 2 ^ (3 * d - 2) := by
      rw [show 3 * d + 2 = 4 + (3 * d - 2) by omega, pow_add]
      norm_num
    nlinarith [hp, hpCap]
  have hrecursive : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 11)
      (d2FlowCandidateRole d 11)
      (d2FlowCandidateQuota d 11)
      (fun k => d2FlowCandidateCapacity d k 11) 6 (children j) := by
    intro j
    apply d2FlowStageInvInputs_all_inactive
    intro k hk
    by_cases hk6 : k = 6
    · subst k
      simp [d2FlowCandidateActive, tfD2]
    · have hk7 : 7 ≤ k := by omega
      have hnot : ¬ 3 * k < 19 := by omega
      simp [d2FlowCandidateActive, show 11 ≠ 0 by omega,
        show 11 ≠ 1 by omega, tfD2, hnot]
  simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
  exact ⟨hrecursive, ⟨hbalance, hG, hquotaCap, htotal, hquotaEven,
    hleft, hright⟩⟩

/-- The Stage 11 top-rise gate is paid by the quota produced by each Stage 10
level-two mid sender below it. -/
theorem d2FlowCandidateStage11_topRise_inputs
    (d : Nat) (hd : 12 ≤ d) (low high : Nat)
    (hbalance : low + high = 0)
    (children : Fin 8 → D2FlowTree (d - 2))
    (hchildren : ∀ j,
      d2FlowCandidateQuota d 10 2 .mid ≤
        d2FlowTreeRootDeficit (children j))
    (hrec : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 11)
      (d2FlowCandidateRole d 11)
      (d2FlowCandidateQuota d 11)
      (fun k => d2FlowCandidateCapacity d k 11) 2 (children j)) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 11)
      (d2FlowCandidateRole d 11)
      (d2FlowCandidateQuota d 11)
      (fun k => d2FlowCandidateCapacity d k 11) 1
      (.node 0 low high children) := by
  rcases d2FlowCandidateStage11_frontiers d hd with
    ⟨hactive, hrole, _, _, _, _, _⟩
  have hcap : d2FlowCandidateCapacity d 1 11 = 2 ^ (3 * d - 10) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 11 1 .topRise =
      2 ^ (3 * d - 18) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hmid : d2FlowCandidateQuota d 10 2 .mid =
      15 * 2 ^ (3 * d - 17) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hquotaEven : d2FlowCandidateQuota d 11 1 .topRise % 2 = 0 := by
    rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 18 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 11 1 .topRise ≤
      d2FlowCandidateCapacity d 1 11 := by
    rw [hquota, hcap]
    have hp : 256 * 2 ^ (3 * d - 18) = 2 ^ (3 * d - 10) := by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_add]
      congr 1 <;> omega
    exact le_of_eq hp
  have hreserve : ∀ j, d2FlowCandidateCapacity d 1 11 ≤
      128 * d2FlowTreeRootDeficit (children j) := by
    intro j
    have hbase : d2FlowCandidateCapacity d 1 11 =
        128 * 2 ^ (3 * d - 17) := by
      rw [hcap]
      have hp : 2 ^ (3 * d - 10) = 128 * 2 ^ (3 * d - 17) := by
        rw [show 3 * d - 10 = 7 + (3 * d - 17) by omega, pow_add]
        norm_num
      exact hp
    have hchild : 2 ^ (3 * d - 17) ≤
        d2FlowTreeRootDeficit (children j) := by
      have hj := hchildren j
      rw [hmid] at hj
      omega
    rw [hbase]
    exact Nat.mul_le_mul_left 128 hchild
  have htotal : 8 * d2FlowCandidateQuota d 10 2 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    unfold d2FlowTotal
    calc
      8 * d2FlowCandidateQuota d 10 2 .mid =
          ∑ j : Fin 8, d2FlowCandidateQuota d 10 2 .mid := by simp
      _ ≤ ∑ j : Fin 8, d2FlowTreeRootDeficit (children j) :=
        Finset.sum_le_sum fun j _ => hchildren j
  have halloc : d2FlowCandidateQuota d 11 1 .topRise ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    have hsmall : d2FlowCandidateQuota d 11 1 .topRise ≤
        8 * d2FlowCandidateQuota d 10 2 .mid := by
      rw [hquota, hmid]
      have he : 2 ^ (3 * d - 17) = 2 * 2 ^ (3 * d - 18) := by
        rw [show 3 * d - 17 = 1 + (3 * d - 18) by omega, pow_add]
        norm_num
      rw [he]
      omega
    exact le_trans hsmall htotal
  simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
  refine ⟨hrec, ⟨hbalance, ?_, hquotaCap, halloc, hquotaEven, ?_, ?_⟩⟩
  · simp
  · exact hreserve ⟨0, by omega⟩
  · exact hreserve ⟨7, by omega⟩

/-- A Stage 11 level-three mid sender's cap and one endpoint reserve pay its
quota from the children. -/
theorem d2FlowCandidateStage11_levelThree_boundary_mass_suffices
    (d : Nat) (hd : 12 ≤ d) (G : Nat)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 3 11) {r : Nat}
    (children : Fin 8 → D2FlowTree r)
    (hleft : d2FlowCandidateCapacity d 3 11 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩)) :
    d2FlowCandidateQuota d 11 3 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
  have hcap : d2FlowCandidateCapacity d 3 11 = 2 ^ (3 * d - 4) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 11 3 .mid =
      15 * 2 ^ (3 * d - 16) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hGsmall : G ≤ 2 ^ (3 * d - 13) := by
    rw [hcap] at hG
    have hp : 512 * 2 ^ (3 * d - 13) = 2 ^ (3 * d - 4) := by
      rw [show (512 : Nat) = 2 ^ 9 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hroot : 2 ^ (3 * d - 11) ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hcap] at hleft
    have hp : 128 * 2 ^ (3 * d - 11) = 2 ^ (3 * d - 4) := by
      rw [show (128 : Nat) = 2 ^ 7 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hrootTotal : d2FlowTreeRootDeficit (children ⟨0, by omega⟩) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    let f : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
    change f ⟨0, by omega⟩ ≤ Finset.univ.sum f
    exact Finset.single_le_sum
      (fun j hj => Nat.zero_le (f j))
      (Finset.mem_univ (⟨0, by omega⟩ : Fin 8))
  have hpG : 2 ^ (3 * d - 13) = 8 * 2 ^ (3 * d - 16) := by
    rw [show 3 * d - 13 = 3 + (3 * d - 16) by omega, pow_add]
    norm_num
  have hpRoot : 2 ^ (3 * d - 11) = 32 * 2 ^ (3 * d - 16) := by
    rw [show 3 * d - 11 = 5 + (3 * d - 16) by omega, pow_add]
    norm_num
  have hmass : G + d2FlowCandidateQuota d 11 3 .mid ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hquota]
    rw [hpG] at hGsmall
    rw [hpRoot] at hroot
    nlinarith
  have hmassTotal : G + d2FlowCandidateQuota d 11 3 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) :=
    le_trans hmass hrootTotal
  omega

/-- Complete local recursive input gate for a Stage 11 level-three mid
sender. -/
theorem d2FlowCandidateStage11_mid_inputs
    (d : Nat) (hd : 12 ≤ d) (G low high : Nat) {r : Nat}
    (hbalance : low + high = G)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 3 11)
    (children : Fin 8 → D2FlowTree r)
    (hrecursive : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 11)
      (d2FlowCandidateRole d 11)
      (d2FlowCandidateQuota d 11)
      (fun k => d2FlowCandidateCapacity d k 11) 4 (children j))
    (hleft : d2FlowCandidateCapacity d 3 11 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hright : d2FlowCandidateCapacity d 3 11 ≤
      128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩))
    (htotal : d2FlowCandidateQuota d 11 3 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 11)
      (d2FlowCandidateRole d 11)
      (d2FlowCandidateQuota d 11)
      (fun k => d2FlowCandidateCapacity d k 11) 3
      (.node G low high children) := by
  rcases d2FlowCandidateStage11_frontiers d hd with
    ⟨_, _, hactive, hrole, _, _, _⟩
  have hcap : d2FlowCandidateCapacity d 3 11 = 2 ^ (3 * d - 4) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 11 3 .mid =
      15 * 2 ^ (3 * d - 16) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hquotaEven : d2FlowCandidateQuota d 11 3 .mid % 2 = 0 := by
    rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 16 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 11 3 .mid ≤
      d2FlowCandidateCapacity d 3 11 := by
    rw [hquota, hcap]
    have hp : 256 * 2 ^ (3 * d - 16) = 2 ^ (3 * d - 8) := by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_add]
      congr 1 <;> omega
    have hpCap : 2 ^ (3 * d - 4) = 16 * 2 ^ (3 * d - 8) := by
      rw [show 3 * d - 4 = 4 + (3 * d - 8) by omega, pow_add]
      norm_num
    nlinarith [hp, hpCap]
  simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
  exact ⟨hrecursive, ⟨hbalance, hG, hquotaCap, htotal, hquotaEven,
    hleft, hright⟩⟩

/-- A stage-ten level-two endpoint reserve and sender cap suffice for its
mid-sender allocation inequality. -/
theorem d2FlowCandidateStage10_mid_boundary_mass_suffices
    (d : Nat) (hd : 11 ≤ d) (G : Nat)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 2 10) {r : Nat}
    (children : Fin 8 → D2FlowTree r)
    (hleft : d2FlowCandidateCapacity d 2 10 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩)) :
    d2FlowCandidateQuota d 10 2 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
  have hcap : d2FlowCandidateCapacity d 2 10 = 2 ^ (3 * d - 5) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 10 2 .mid =
      15 * 2 ^ (3 * d - 17) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hGsmall : G ≤ 2 ^ (3 * d - 14) := by
    rw [hcap] at hG
    have hp : 512 * 2 ^ (3 * d - 14) = 2 ^ (3 * d - 5) := by
      rw [show (512 : Nat) = 2 ^ 9 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hroot : 2 ^ (3 * d - 12) ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hcap] at hleft
    have hp : 128 * 2 ^ (3 * d - 12) = 2 ^ (3 * d - 5) := by
      rw [show (128 : Nat) = 2 ^ 7 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hrootTotal : d2FlowTreeRootDeficit (children ⟨0, by omega⟩) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    let f : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
    change f ⟨0, by omega⟩ ≤ Finset.univ.sum f
    exact Finset.single_le_sum
      (fun j hj => Nat.zero_le (f j)) (Finset.mem_univ (⟨0, by omega⟩ : Fin 8))
  have hpG : 2 ^ (3 * d - 14) = 8 * 2 ^ (3 * d - 17) := by
    rw [show 3 * d - 14 = 3 + (3 * d - 17) by omega, pow_add]
    norm_num
  have hpRoot : 2 ^ (3 * d - 12) = 32 * 2 ^ (3 * d - 17) := by
    rw [show 3 * d - 12 = 5 + (3 * d - 17) by omega, pow_add]
    norm_num
  have hmass : G + d2FlowCandidateQuota d 10 2 .mid ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hquota]
    rw [hpG] at hGsmall
    rw [hpRoot] at hroot
    nlinarith
  have hmassTotal : G + d2FlowCandidateQuota d 10 2 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) :=
    le_trans hmass hrootTotal
  omega

/-- Complete local input gate for a stage-ten level-two mid sender. -/
theorem d2FlowCandidateStage10_mid_inputs
    (d : Nat) (hd : 11 ≤ d) (G low high : Nat) {r : Nat}
    (hbalance : low + high = G)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 2 10)
    (children : Fin 8 → D2FlowTree r)
    (hrecursive : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 10)
      (d2FlowCandidateRole d 10)
      (d2FlowCandidateQuota d 10)
      (fun k => d2FlowCandidateCapacity d k 10) 3 (children j))
    (hleft : d2FlowCandidateCapacity d 2 10 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hright : d2FlowCandidateCapacity d 2 10 ≤
      128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩))
    (htotal : d2FlowCandidateQuota d 10 2 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 10)
      (d2FlowCandidateRole d 10)
      (d2FlowCandidateQuota d 10)
      (fun k => d2FlowCandidateCapacity d k 10) 2
      (.node G low high children) := by
  rcases d2FlowCandidateStage10_frontiers d hd with
    ⟨_, _, hactive, hrole, _, _, _⟩
  have hcap : d2FlowCandidateCapacity d 2 10 = 2 ^ (3 * d - 5) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 10 2 .mid =
      15 * 2 ^ (3 * d - 17) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hquotaEven : d2FlowCandidateQuota d 10 2 .mid % 2 = 0 := by
    rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 17 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 10 2 .mid ≤
      d2FlowCandidateCapacity d 2 10 := by
    rw [hquota, hcap]
    have hp : 256 * 2 ^ (3 * d - 17) = 2 ^ (3 * d - 9) := by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_add]
      congr 1 <;> omega
    have hpCap : 2 ^ (3 * d - 5) = 16 * 2 ^ (3 * d - 9) := by
      rw [show 3 * d - 5 = 4 + (3 * d - 9) by omega, pow_add]
      norm_num
    nlinarith [hp, hpCap]
  simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
  exact ⟨hrecursive, ⟨hbalance, hG, hquotaCap, htotal, hquotaEven,
    hleft, hright⟩⟩

/-- At stage eight, a single level-five endpoint reserve plus the sender cap
already supplies enough total mass for the bottom-descending quota. -/
theorem d2FlowCandidateStage8_boundary_mass_suffices
    (d : Nat) (hd : 10 ≤ d) (G : Nat) {r : Nat}
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 4 8)
    (children : Fin 8 → D2FlowTree r)
    (hleft : d2FlowCandidateCapacity d 4 8 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩)) :
    d2FlowCandidateQuota d 8 4 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
  have hcap : d2FlowCandidateCapacity d 4 8 = 2 ^ (3 * d + 5) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 8 4 .botDesc =
      15 * 2 ^ (3 * d - 7) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hGsmall : G ≤ 2 ^ (3 * d - 4) := by
    rw [hcap] at hG
    have hp : 512 * 2 ^ (3 * d - 4) = 2 ^ (3 * d + 5) := by
      rw [show (512 : Nat) = 2 ^ 9 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hroot : 2 ^ (3 * d - 2) ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hcap] at hleft
    have hp : 128 * 2 ^ (3 * d - 2) = 2 ^ (3 * d + 5) := by
      rw [show (128 : Nat) = 2 ^ 7 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hrootTotal : d2FlowTreeRootDeficit (children ⟨0, by omega⟩) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    let f : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
    change f ⟨0, by omega⟩ ≤ Finset.univ.sum f
    exact Finset.single_le_sum
      (fun j hj => Nat.zero_le (f j)) (Finset.mem_univ (⟨0, by omega⟩ : Fin 8))
  have hpQuota : 2 ^ (3 * d - 2) = 32 * 2 ^ (3 * d - 7) := by
    rw [show 3 * d - 2 = 5 + (3 * d - 7) by omega, pow_add]
    norm_num
  have hpG : 2 ^ (3 * d - 4) = 8 * 2 ^ (3 * d - 7) := by
    rw [show 3 * d - 4 = 3 + (3 * d - 7) by omega, pow_add]
    norm_num
  have hroot' : 32 * 2 ^ (3 * d - 7) ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [← hpQuota]
    exact hroot
  have hGsmall' : G ≤ 8 * 2 ^ (3 * d - 7) := by
    rw [← hpG]
    exact hGsmall
  have hmass : G + d2FlowCandidateQuota d 8 4 .botDesc ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hquota]
    nlinarith
  have hmassTotal : G + d2FlowCandidateQuota d 8 4 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) :=
    le_trans hmass hrootTotal
  omega

/-- Complete local input gate for a stage-eight level-four bottom-descending
sender, from its normalized cap, balanced endpoints, and endpoint reserves. -/
theorem d2FlowCandidateStage8_botDesc_inputs
    (d : Nat) (hd : 10 ≤ d) (G low high : Nat) {r : Nat}
    (hbalance : low + high = G)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 4 8)
    (children : Fin 8 → D2FlowTree r)
    (hleft : d2FlowCandidateCapacity d 4 8 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hright : d2FlowCandidateCapacity d 4 8 ≤
      128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩))
    (htotal : d2FlowCandidateQuota d 8 4 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 8)
      (d2FlowCandidateRole d 8)
      (d2FlowCandidateQuota d 8)
      (fun k => d2FlowCandidateCapacity d k 8) 4
      (.node G low high children) := by
  rcases d2FlowCandidateStage8_frontiers d hd with
    ⟨_, _, _, _, hactive, hrole, _⟩
  have hcap : d2FlowCandidateCapacity d 4 8 = 2 ^ (3 * d + 5) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 8 4 .botDesc =
      15 * 2 ^ (3 * d - 7) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hquotaEven : d2FlowCandidateQuota d 8 4 .botDesc % 2 = 0 := by
    rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 7 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 8 4 .botDesc ≤
      d2FlowCandidateCapacity d 4 8 := by
    rw [hquota, hcap]
    have hp : 256 * 2 ^ (3 * d - 7) = 2 ^ (3 * d + 1) := by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_add]
      congr 1 <;> omega
    have hpCap : 2 ^ (3 * d + 5) = 16 * 2 ^ (3 * d + 1) := by
      rw [show 3 * d + 5 = 4 + (3 * d + 1) by omega, pow_add]
      norm_num
    nlinarith [hp, hpCap]
  have hrecursive : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 8)
      (d2FlowCandidateRole d 8)
      (d2FlowCandidateQuota d 8)
      (fun k => d2FlowCandidateCapacity d k 8) 5 (children j) := by
    intro j
    apply d2FlowStageInvInputs_all_inactive
    intro k hk
    simp [d2FlowCandidateActive, tfD2]
    omega
  simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
  exact ⟨hrecursive, ⟨hbalance, hG, hquotaCap, htotal, hquotaEven,
    hleft, hright⟩⟩

/-- A stage-eight level-two endpoint reserve and sender cap suffice for its
mid-sender allocation inequality. -/
theorem d2FlowCandidateStage8_mid_boundary_mass_suffices
    (d : Nat) (hd : 10 ≤ d) (G : Nat)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 2 8) {r : Nat}
    (children : Fin 8 → D2FlowTree r)
    (hleft : d2FlowCandidateCapacity d 2 8 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩)) :
    d2FlowCandidateQuota d 8 2 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
  have hcap : d2FlowCandidateCapacity d 2 8 = 2 ^ (3 * d - 1) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 8 2 .mid =
      15 * 2 ^ (3 * d - 13) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hGsmall : G ≤ 2 ^ (3 * d - 10) := by
    rw [hcap] at hG
    have hp : 512 * 2 ^ (3 * d - 10) = 2 ^ (3 * d - 1) := by
      rw [show (512 : Nat) = 2 ^ 9 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hroot : 2 ^ (3 * d - 8) ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hcap] at hleft
    have hp : 128 * 2 ^ (3 * d - 8) = 2 ^ (3 * d - 1) := by
      rw [show (128 : Nat) = 2 ^ 7 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hrootTotal : d2FlowTreeRootDeficit (children ⟨0, by omega⟩) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    let f : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
    change f ⟨0, by omega⟩ ≤ Finset.univ.sum f
    exact Finset.single_le_sum
      (fun j hj => Nat.zero_le (f j)) (Finset.mem_univ (⟨0, by omega⟩ : Fin 8))
  have hpQuota : 2 ^ (3 * d - 8) = 32 * 2 ^ (3 * d - 13) := by
    rw [show 3 * d - 8 = 5 + (3 * d - 13) by omega, pow_add]
    norm_num
  have hpG : 2 ^ (3 * d - 10) = 8 * 2 ^ (3 * d - 13) := by
    rw [show 3 * d - 10 = 3 + (3 * d - 13) by omega, pow_add]
    norm_num
  have hroot' : 32 * 2 ^ (3 * d - 13) ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [← hpQuota]
    exact hroot
  have hGsmall' : G ≤ 8 * 2 ^ (3 * d - 13) := by
    rw [← hpG]
    exact hGsmall
  have hmass : G + d2FlowCandidateQuota d 8 2 .mid ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hquota]
    nlinarith
  have hmassTotal : G + d2FlowCandidateQuota d 8 2 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) :=
    le_trans hmass hrootTotal
  omega

/-- Complete local input gate for a stage-eight level-two mid sender. -/
theorem d2FlowCandidateStage8_mid_inputs
    (d : Nat) (hd : 10 ≤ d) (G low high : Nat) {r : Nat}
    (hbalance : low + high = G)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 2 8)
    (children : Fin 8 → D2FlowTree r)
    (hrecursive : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 8)
      (d2FlowCandidateRole d 8)
      (d2FlowCandidateQuota d 8)
      (fun q => d2FlowCandidateCapacity d q 8) 3 (children j))
    (hleft : d2FlowCandidateCapacity d 2 8 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hright : d2FlowCandidateCapacity d 2 8 ≤
      128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩))
    (htotal : d2FlowCandidateQuota d 8 2 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 8)
      (d2FlowCandidateRole d 8)
      (d2FlowCandidateQuota d 8)
      (fun q => d2FlowCandidateCapacity d q 8) 2
      (.node G low high children) := by
  rcases d2FlowCandidateStage8_frontiers d hd with
    ⟨_, _, hactive, hrole, _, _, _⟩
  have hcap : d2FlowCandidateCapacity d 2 8 = 2 ^ (3 * d - 1) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 8 2 .mid =
      15 * 2 ^ (3 * d - 13) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hquotaEven : d2FlowCandidateQuota d 8 2 .mid % 2 = 0 := by
    rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 13 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 8 2 .mid ≤
      d2FlowCandidateCapacity d 2 8 := by
    rw [hquota, hcap]
    have hp : 256 * 2 ^ (3 * d - 13) = 2 ^ (3 * d - 5) := by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_add]
      congr 1 <;> omega
    have hpCap : 2 ^ (3 * d - 1) = 16 * 2 ^ (3 * d - 5) := by
      rw [show 3 * d - 1 = 4 + (3 * d - 5) by omega, pow_add]
      norm_num
    nlinarith [hp, hpCap]
  simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
  exact ⟨hrecursive, ⟨hbalance, hG, hquotaCap, htotal, hquotaEven,
    hleft, hright⟩⟩

/-- The level-five native reserve is exactly the stage-eight level-four
endpoint quota after scaling by 128. -/
theorem d2FlowCandidateStage8_capacity_eq_native (h : Nat) :
    d2FlowCandidateCapacity (h + 5) 4 8 =
      128 * (8192 * 8 ^ h) := by
  have hcap : d2FlowCandidateCapacity (h + 5) 4 8 = 2 ^ (3 * h + 20) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hnative : 128 * (8192 * 8 ^ h) = 2 ^ (3 * h + 20) := by
    rw [show (128 : Nat) = 2 ^ 7 by norm_num,
      show (8192 : Nat) = 2 ^ 13 by norm_num,
      show (8 : Nat) = 2 ^ 3 by norm_num]
    rw [show (2 ^ 3) ^ h = 2 ^ (3 * h) by rw [Nat.pow_mul]]
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  rw [hcap, hnative]

/-- At a stage-five level-four node, the child level-five root deficits are
unchanged: both the parent and child schedule positions are inactive. -/
theorem d2FlowCandidateStage5_levelFour_child_root
    (d h G low high : Nat) (hd : 10 ≤ d)
    (children : Fin 8 → D2FlowTree h) (j : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 5)
          (d2FlowCandidateRole d 5) (d2FlowCandidateQuota d 5)
          (h + 1) 4 (.node G low high children)) j) =
      d2FlowTreeRootDeficit (children j) := by
  have hparent : d2FlowCandidateActive d 5 4 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hchild : d2FlowCandidateActive d 5 5 = false := by
    simp [d2FlowCandidateActive, tfD2]
  rw [d2FlowStage_inactive_child children hparent j]
  exact d2FlowStage_root_deficit_of_inactive (children j) hchild

/-- The stage-six bottom-rise sender passes each level-five child's root
deficit through unchanged because the recursively applied level-five point is
inactive. -/
theorem d2FlowCandidateStage6_levelFour_child_root
    (d h G low high : Nat) (hd : 10 ≤ d)
    (children : Fin 8 → D2FlowTree h) (j : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 6)
          (d2FlowCandidateRole d 6) (d2FlowCandidateQuota d 6)
          (h + 1) 4 (.node G low high children)) j) =
      d2FlowTreeRootDeficit (children j) := by
  rcases d2FlowCandidateStage6_frontiers d (by omega) with
    ⟨_, _, _, _, hactive4, hrole4, _⟩
  have hchild : d2FlowCandidateActive d 6 5 = false := by
    simp [d2FlowCandidateActive, tfD2]
  rw [d2FlowStage_botRise_child_deficit children hactive4 hrole4 j]
  exact d2FlowStage_root_deficit_of_inactive (children j) hchild

/-- The final inactive two-level tail of stage seven also preserves the
level-five child root deficits below every level-four node. -/
theorem d2FlowCandidateStage7_levelFour_child_root
    (d h G low high : Nat) (hd : 10 ≤ d)
    (children : Fin 8 → D2FlowTree h) (j : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 7)
          (d2FlowCandidateRole d 7) (d2FlowCandidateQuota d 7)
          (h + 1) 4 (.node G low high children)) j) =
      d2FlowTreeRootDeficit (children j) := by
  have hparent : d2FlowCandidateActive d 7 4 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hchild : d2FlowCandidateActive d 7 5 = false := by
    simp [d2FlowCandidateActive, tfD2]
  rw [d2FlowStage_inactive_child children hparent j]
  exact d2FlowStage_root_deficit_of_inactive (children j) hchild

/-- The stage-seven bottom-descending local gate follows from its exported
sender-deficit cap and the two endpoint reserves. Recursive obligations below
level four are vacuous at this stage. -/
theorem d2FlowCandidateStage7_boundary_mass_suffices
    (d : Nat) (hd : 9 ≤ d) (G : Nat)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 3 7)
    (children : Fin 8 → D2FlowTree (d - 4))
    (hleft : d2FlowCandidateCapacity d 3 7 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩)) :
    d2FlowCandidateQuota d 7 3 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
  have hcap : d2FlowCandidateCapacity d 3 7 = 2 ^ (3 * d + 4) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 7 3 .botDesc =
      15 * 2 ^ (3 * d - 8) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hGsmall : G ≤ 2 ^ (3 * d - 5) := by
    rw [hcap] at hG
    have hp : 512 * 2 ^ (3 * d - 5) = 2 ^ (3 * d + 4) := by
      rw [show (512 : Nat) = 2 ^ 9 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hroot : 2 ^ (3 * d - 3) ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hcap] at hleft
    have hp : 128 * 2 ^ (3 * d - 3) = 2 ^ (3 * d + 4) := by
      rw [show (128 : Nat) = 2 ^ 7 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hrootTotal : d2FlowTreeRootDeficit (children ⟨0, by omega⟩) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    let f : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
    change f ⟨0, by omega⟩ ≤ Finset.univ.sum f
    exact Finset.single_le_sum
      (fun j hj => Nat.zero_le (f j)) (Finset.mem_univ (⟨0, by omega⟩ : Fin 8))
  have hpQuota : 2 ^ (3 * d - 3) = 32 * 2 ^ (3 * d - 8) := by
    rw [show 3 * d - 3 = 5 + (3 * d - 8) by omega, pow_add]
    norm_num
  have hpG : 2 ^ (3 * d - 5) = 8 * 2 ^ (3 * d - 8) := by
    rw [show 3 * d - 5 = 3 + (3 * d - 8) by omega, pow_add]
    norm_num
  have hroot' : 32 * 2 ^ (3 * d - 8) ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [← hpQuota]
    exact hroot
  have hGsmall' : G ≤ 8 * 2 ^ (3 * d - 8) := by
    rw [← hpG]
    exact hGsmall
  have hmass : G + d2FlowCandidateQuota d 7 3 .botDesc ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hquota]
    nlinarith
  have hmassTotal : G + d2FlowCandidateQuota d 7 3 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) :=
    le_trans hmass hrootTotal
  omega

theorem d2FlowCandidateStage7_botDesc_inputs
    (d : Nat) (hd : 9 ≤ d) (G low high : Nat)
    (hbalance : low + high = G)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 3 7)
    (children : Fin 8 → D2FlowTree (d - 4))
    (hleft : d2FlowCandidateCapacity d 3 7 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hright : d2FlowCandidateCapacity d 3 7 ≤
      128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩))
    (htotal : d2FlowCandidateQuota d 7 3 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 7)
      (d2FlowCandidateRole d 7)
      (d2FlowCandidateQuota d 7)
      (fun k => d2FlowCandidateCapacity d k 7) 3
      (.node G low high children) := by
  rcases d2FlowCandidateStage7_frontiers d hd with
    ⟨_, _, hactive, hrole, _⟩
  have hcap : d2FlowCandidateCapacity d 3 7 = 2 ^ (3 * d + 4) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 7 3 .botDesc =
      15 * 2 ^ (3 * d - 8) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hGsmall : G ≤ 2 ^ (3 * d - 5) := by
    rw [hcap] at hG
    have hp : 512 * 2 ^ (3 * d - 5) = 2 ^ (3 * d + 4) := by
      rw [show (512 : Nat) = 2 ^ 9 by norm_num,
        ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hquotaEven :
      d2FlowCandidateQuota d 7 3 .botDesc % 2 = 0 := by
    rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 8 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 7 3 .botDesc ≤
      d2FlowCandidateCapacity d 3 7 := by
    rw [hquota, hcap]
    have hp : 256 * 2 ^ (3 * d - 8) = 2 ^ (3 * d) := by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num,
        ← pow_add]
      congr 1 <;> omega
    have hpCap : 2 ^ (3 * d + 4) = 16 * 2 ^ (3 * d) := by
      rw [pow_add]
      norm_num
      exact Nat.mul_comm _ _
    have hpPos : 0 < 2 ^ (3 * d) := by positivity
    rw [hpCap]
    nlinarith
  have halloc := htotal
  have hrecursive : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 7)
      (d2FlowCandidateRole d 7)
      (d2FlowCandidateQuota d 7)
      (fun k => d2FlowCandidateCapacity d k 7) 4 (children j) := by
    intro j
    apply d2FlowStageInvInputs_all_inactive
    intro k hk
    simp [d2FlowCandidateActive, tfD2]
    omega
  simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
  exact ⟨hrecursive, ⟨hbalance, hG, hquotaCap, halloc, hquotaEven,
    hleft, hright⟩⟩

/-- The stage-seven top-rise gate follows from zero parent deficit and the
quota added by each of the eight stage-six level-two mid senders. -/
theorem d2FlowCandidateStage7_topRise_inputs
    (d : Nat) (hd : 9 ≤ d) (low high : Nat)
    (hbalance : low + high = 0)
    (children : Fin 8 → D2FlowTree (d - 2))
    (hchildren : ∀ j,
      d2FlowCandidateQuota d 6 2 .mid ≤
        d2FlowTreeRootDeficit (children j))
    (hrec : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 7)
      (d2FlowCandidateRole d 7)
      (d2FlowCandidateQuota d 7)
      (fun k => d2FlowCandidateCapacity d k 7) 2 (children j)) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 7)
      (d2FlowCandidateRole d 7)
      (d2FlowCandidateQuota d 7)
      (fun k => d2FlowCandidateCapacity d k 7) 1
      (.node 0 low high children) := by
  rcases d2FlowCandidateStage7_frontiers d hd with
    ⟨hactive, hrole, _, _, _⟩
  have hcapExp : d2FlowCandidateCapacityExponent d 1 7 = 3 * d - 2 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  have hcap : d2FlowCandidateCapacity d 1 7 = 2 ^ (3 * d - 2) := by
    simp [d2FlowCandidateCapacity, hcapExp]
  have hquota : d2FlowCandidateQuota d 7 1 .topRise =
      2 ^ (3 * d - 10) := by
    calc
      d2FlowCandidateQuota d 7 1 .topRise =
          2 ^ (d2FlowCandidateCapacityExponent d 1 7 - 8) := by
        simp [d2FlowCandidateQuota]
      _ = 2 ^ (3 * d - 10) := by rw [hcapExp]; congr 1 <;> omega
  have hmid : d2FlowCandidateQuota d 6 2 .mid =
      15 * 2 ^ (3 * d - 9) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hquotaEven :
      d2FlowCandidateQuota d 7 1 .topRise % 2 = 0 := by
    rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 10 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 7 1 .topRise ≤
      d2FlowCandidateCapacity d 1 7 := by
    rw [hquota, hcap]
    have hp : 256 * 2 ^ (3 * d - 10) = 2 ^ (3 * d - 2) := by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num,
        ← pow_add]
      congr 1 <;> omega
    exact le_of_eq hp
  have hreserveBase : 2 ^ (3 * d - 9) ≤
      d2FlowCandidateQuota d 6 2 .mid := by
    rw [hmid]
    omega
  have hreserve : ∀ j, d2FlowCandidateCapacity d 1 7 ≤
      128 * d2FlowTreeRootDeficit (children j) := by
    intro j
    have hbase : d2FlowCandidateCapacity d 1 7 =
        128 * 2 ^ (3 * d - 9) := by
      rw [hcap]
      have hp : 2 ^ (3 * d - 2) = 128 * 2 ^ (3 * d - 9) := by
        rw [show 3 * d - 2 = 7 + (3 * d - 9) by omega,
          pow_add]
        norm_num
      exact hp
    rw [hbase]
    exact Nat.mul_le_mul_left 128
      ((le_trans hreserveBase (hchildren j)))
  have htotal : 8 * d2FlowCandidateQuota d 6 2 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    unfold d2FlowTotal
    calc
      8 * d2FlowCandidateQuota d 6 2 .mid =
          ∑ j : Fin 8, d2FlowCandidateQuota d 6 2 .mid := by simp
      _ ≤ ∑ j : Fin 8, d2FlowTreeRootDeficit (children j) :=
        Finset.sum_le_sum fun j _ => hchildren j
  have hquotaSmall : d2FlowCandidateQuota d 7 1 .topRise ≤
      8 * d2FlowCandidateQuota d 6 2 .mid := by
    rw [hquota, hmid]
    have hp : 2 ^ (3 * d - 10) ≤ 120 * 2 ^ (3 * d - 9) := by
      have he : 2 ^ (3 * d - 9) = 2 * 2 ^ (3 * d - 10) := by
        rw [show 3 * d - 9 = 1 + (3 * d - 10) by omega,
          pow_add]
        norm_num
      rw [he]
      omega
    calc
      2 ^ (3 * d - 10) ≤ 120 * 2 ^ (3 * d - 9) := hp
      _ = 8 * (15 * 2 ^ (3 * d - 9)) := by ring
  have halloc : d2FlowCandidateQuota d 7 1 .topRise ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) :=
    le_trans hquotaSmall htotal
  simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
  refine ⟨hrec, ⟨hbalance, ?_, hquotaCap, ?_, hquotaEven, ?_, ?_⟩⟩
  · simp
  · simpa using halloc
  · exact hreserve ⟨0, by omega⟩
  · exact hreserve ⟨7, by omega⟩

/-- No stage-six sender occurs at level five or below. -/
theorem d2FlowCandidateStage6_inactive_tail
    (d i : Nat) (hd : 9 ≤ d) (hi : 5 ≤ i) :
    d2FlowCandidateActive d 6 i = false := by
  simp [d2FlowCandidateActive, tfD2]
  omega

/-- Every subtree rooted at level five satisfies the stage-six input
predicate, since all its levels are inactive. -/
theorem d2FlowCandidateStage6_tail_inputs
    (d i h : Nat) (hd : 9 ≤ d) (hi : 5 ≤ i)
    (tree : D2FlowTree h) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 6) (d2FlowCandidateRole d 6)
      (d2FlowCandidateQuota d 6)
      (fun k => d2FlowCandidateCapacity d k 6) i tree := by
  apply d2FlowStageInvInputs_all_inactive
  intro k hk
  exact d2FlowCandidateStage6_inactive_tail d k hd (by omega)

/-- Capacity arithmetic across the stage-five to stage-six middle sender. -/
theorem d2FlowCandidateStage6_capacity_identities (d : Nat) :
    d2FlowCandidateCapacity d 1 5 * 2 =
        d2FlowCandidateCapacity d 2 6 ∧
      d2FlowCandidateCapacity d 3 5 =
        32 * d2FlowCandidateCapacity d 2 6 := by
  constructor
  · have hexp : d2FlowCandidateCapacityExponent d 2 6 =
        d2FlowCandidateCapacityExponent d 1 5 + 1 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    unfold d2FlowCandidateCapacity
    rw [hexp, Nat.pow_succ]
  · have hexp : d2FlowCandidateCapacityExponent d 3 5 =
        d2FlowCandidateCapacityExponent d 2 6 + 5 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    unfold d2FlowCandidateCapacity
    rw [hexp, pow_add]
    calc
      (2 : Nat) ^ d2FlowCandidateCapacityExponent d 2 6 * 2 ^ 5 =
          (2 : Nat) ^ d2FlowCandidateCapacityExponent d 2 6 * 32 := by
        congr 1
      _ = 32 * (2 : Nat) ^ d2FlowCandidateCapacityExponent d 2 6 :=
        Nat.mul_comm _ _

/-- The first repeating mid sender satisfies its complete local gate whenever
its stage-five children carry the guaranteed bot-descending quota and its own
deficit obeys the exported `c/512` cap. -/
theorem d2FlowCandidateStage6_mid_inputs_of_state
    (d h : Nat) (hd : 9 ≤ d) (G low high : Nat)
    (children : Fin 8 → D2FlowTree h)
    (hbalance : low + high = G)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 2 6)
    (hchild : ∀ j,
      d2FlowCandidateQuota d 5 3 .botDesc ≤
        d2FlowTreeRootDeficit (children j))
    (hrec : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 6) (d2FlowCandidateRole d 6)
      (d2FlowCandidateQuota d 6)
      (fun i => d2FlowCandidateCapacity d i 6) 3 (children j)) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 6) (d2FlowCandidateRole d 6)
      (d2FlowCandidateQuota d 6)
      (fun i => d2FlowCandidateCapacity d i 6) 2
      (.node G low high children) := by
  classical
  rcases d2FlowCandidateStage6_frontiers d hd with
    ⟨_, _, hactive2, hrole2, _, _, _⟩
  have hcapExp : d2FlowCandidateCapacityExponent d 2 6 = 3 * d + 3 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  have hbotExp : d2FlowCandidateCapacityExponent d 3 5 = 3 * d + 8 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  have hmid : d2FlowCandidateQuota d 6 2 .mid =
      15 * 2 ^ (3 * d - 9) := by
    simp [d2FlowCandidateQuota, hcapExp]
  have hbot : d2FlowCandidateQuota d 5 3 .botDesc =
      15 * 2 ^ (3 * d - 4) := by
    simp [d2FlowCandidateQuota, hbotExp]
  have hcap : d2FlowCandidateCapacity d 2 6 = 2 ^ (3 * d + 3) := by
    simp [d2FlowCandidateCapacity, hcapExp]
  have hchildScale : 128 * d2FlowCandidateQuota d 5 3 .botDesc =
      15 * d2FlowCandidateCapacity d 2 6 := by
    rw [hbot, hcap]
    have hp : 128 * 2 ^ (3 * d - 4) = 2 ^ (3 * d + 3) := by
      rw [show (128 : Nat) = 2 ^ 7 by norm_num,
        ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hquotaScale : 4096 * d2FlowCandidateQuota d 6 2 .mid =
      15 * d2FlowCandidateCapacity d 2 6 := by
    rw [hmid, hcap]
    have hp : 4096 * 2 ^ (3 * d - 9) = 2 ^ (3 * d + 3) := by
      rw [show (4096 : Nat) = 2 ^ 12 by norm_num,
        ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hGsmall : G ≤ d2FlowCandidateQuota d 5 3 .botDesc := by
    nlinarith
  have hquotaSmall : d2FlowCandidateQuota d 6 2 .mid ≤
      d2FlowCandidateQuota d 5 3 .botDesc := by
    rw [hmid, hbot]
    have hp : 3 * d - 4 = (3 * d - 9) + 5 := by omega
    rw [hp, pow_add]
    norm_num
  have htotal : 8 * d2FlowCandidateQuota d 5 3 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    unfold d2FlowTotal
    calc
      8 * d2FlowCandidateQuota d 5 3 .botDesc =
          ∑ _j : Fin 8, d2FlowCandidateQuota d 5 3 .botDesc := by simp
      _ ≤ ∑ j : Fin 8, d2FlowTreeRootDeficit (children j) :=
        Finset.sum_le_sum fun j _ => hchild j
  have halloc : d2FlowCandidateQuota d 6 2 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 6 2 .mid ≤
      d2FlowCandidateCapacity d 2 6 := by
    nlinarith
  have hleft : d2FlowCandidateCapacity d 2 6 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    have hcPos : 0 < d2FlowCandidateCapacity d 2 6 := by
      simp [hcap]
    have hscaled := hchild ⟨0, by omega⟩
    nlinarith
  have hright : d2FlowCandidateCapacity d 2 6 ≤
      128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩) := by
    have hcPos : 0 < d2FlowCandidateCapacity d 2 6 := by
      simp [hcap]
    have hscaled := hchild ⟨7, by omega⟩
    nlinarith
  have hrawActive : active d (tfD2 d) 2 6 := by
    rw [d2FlowCandidateActive_matches_schedule (d := d) (t := 6)
      (i := 2) (by omega)] at hactive2
    simpa using hactive2
  have hscheduledRole : d2ScheduleRole d 2 6 = .mid := by
    rw [← d2FlowCandidateRole_matches_schedule (d := d) (t := 6)
      (i := 2) (by omega)]
    exact hrole2
  have heven := d2FlowCandidateQuota_even (by omega) hrawActive (by omega)
    (Or.inr (Or.inl hscheduledRole))
  simp only [d2FlowStageInvInputs, hactive2, hrole2, if_true]
  refine ⟨?_, ?_⟩
  · exact hrec
  · exact ⟨hbalance, hG, hquotaCap, halloc, by simpa [hrole2] using heven,
      hleft, hright⟩

/-- The level-two stage-four bottom-descending quota is exactly the reserve
required by each level-two child in stage five's top-rise gate. -/
theorem d2FlowCandidateStage4_levelTwo_quota (d : Nat) :
    d2FlowCandidateQuota d 4 2 .botDesc = 15 * 2 ^ (3 * d - 5) := by
  have he : d2FlowCandidateCapacityExponent d 2 4 = 3 * d + 7 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  calc
    d2FlowCandidateQuota d 4 2 .botDesc =
        15 * 2 ^ (d2FlowCandidateCapacityExponent d 2 4 - 12) := by
      simp [d2FlowCandidateQuota]
    _ = 15 * 2 ^ (3 * d + 7 - 12) := by rw [he]
    _ = 15 * 2 ^ (3 * d - 5) := by congr 2 <;> omega

/-- The stage-five top-rise gate is discharged by zero parent deficit and a
uniform lower bound on the eight level-two child deficits. The recursive
stage-five obligations below those children are passed through unchanged. -/
theorem d2FlowCandidateStage5_topRise_inputs
    (d : Nat) (hd : 9 ≤ d) (low high : Nat) (hbalance : low + high = 0)
    (children : Fin 8 → D2FlowTree (d - 2))
    (hchildren : ∀ j,
      15 * 2 ^ (3 * d - 5) ≤ d2FlowTreeRootDeficit (children j))
    (hrec : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 5) (d2FlowCandidateRole d 5)
      (d2FlowCandidateQuota d 5)
      (fun k => d2FlowCandidateCapacity d k 5) 2 (children j)) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 5) (d2FlowCandidateRole d 5)
      (d2FlowCandidateQuota d 5)
      (fun k => d2FlowCandidateCapacity d k 5) 1
      (.node 0 low high children) := by
  rcases d2FlowCandidateStage5_frontiers d hd with
    ⟨hactive, hrole, _, _⟩
  have hcap : d2FlowCandidateCapacity d 1 5 = 2 ^ (3 * d + 2) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 5 1 .topRise = 2 ^ (3 * d - 6) := by
    have he : d2FlowCandidateCapacityExponent d 1 5 = 3 * d + 2 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    calc
      d2FlowCandidateQuota d 5 1 .topRise =
          2 ^ (d2FlowCandidateCapacityExponent d 1 5 - 8) := by
        simp [d2FlowCandidateQuota]
      _ = 2 ^ (3 * d + 2 - 8) := by rw [he]
      _ = 2 ^ (3 * d - 6) := by congr 1 <;> omega
  have hexp : 1 ≤ 3 * d - 6 := by omega
  have hquotaEven : d2FlowCandidateQuota d 5 1 .topRise % 2 = 0 := by
    rw [hquota]
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : 3 * d - 6 ≠ 0)
    rw [hk, pow_succ]
    simp
  have hquotaReserve : 256 * d2FlowCandidateQuota d 5 1 .topRise =
      d2FlowCandidateCapacity d 1 5 := by
    rw [hquota, hcap]
    have heq : 3 * d + 2 = 8 + (3 * d - 6) := by omega
    rw [heq, pow_add]
    norm_num
  have hchildMin : 2 ^ (3 * d + 2) ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    have hpowers : 2 ^ (3 * d + 2) = 128 * 2 ^ (3 * d - 5) := by
      rw [show 3 * d + 2 = 7 + (3 * d - 5) by omega, pow_add]
      norm_num
    calc
      2 ^ (3 * d + 2) ≤ 128 * (15 * 2 ^ (3 * d - 5)) := by
        rw [hpowers]
        omega
      _ ≤ 128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
        exact Nat.mul_le_mul_left _ (hchildren ⟨0, by omega⟩)
  simp only [d2FlowStageInvInputs]
  refine ⟨hrec, ?_⟩
  simp only [hactive, if_true, hrole]
  refine ⟨hbalance, ?_, ?_, ?_, hquotaEven, ?_, ?_⟩
  · simp
  · rw [hquotaReserve]
  · have htotal : d2FlowCandidateQuota d 5 1 .topRise ≤
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
      have hsum : (Finset.univ.sum fun j : Fin 8 =>
          15 * 2 ^ (3 * d - 5)) ≤
          d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hchildren j
      have hsum' : 8 * (15 * 2 ^ (3 * d - 5)) ≤
          d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
        simpa [d2FlowTotal] using hsum
      have hsmall : 2 ^ (3 * d - 6) ≤ 8 * (15 * 2 ^ (3 * d - 5)) := by
        have hpowers : 2 ^ (3 * d - 5) = 2 * 2 ^ (3 * d - 6) := by
          rw [show 3 * d - 5 = 1 + (3 * d - 6) by omega, pow_add]
          norm_num
        have hp : 0 < 2 ^ (3 * d - 6) := by positivity
        nlinarith [hpowers]
      rw [hquota]
      exact le_trans hsmall hsum'
    simpa using htotal
  · rw [hcap]
    exact hchildMin
  · have hlast : 2 ^ (3 * d + 2) ≤
        128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩) := by
      have hpowers : 2 ^ (3 * d + 2) = 128 * 2 ^ (3 * d - 5) := by
        rw [show 3 * d + 2 = 7 + (3 * d - 5) by omega, pow_add]
        norm_num
      calc
        2 ^ (3 * d + 2) ≤ 128 * (15 * 2 ^ (3 * d - 5)) := by
          rw [hpowers]
          omega
        _ ≤ 128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩) :=
          Nat.mul_le_mul_left _ (hchildren ⟨7, by omega⟩)
    rw [hcap]
    exact hlast

/-- At stage five all recursive inputs below level three are vacuous: the
schedule has no active levels four and deeper. -/
theorem d2FlowCandidateAny_stage5_inactive_inputs
    {d h i : Nat} (hi : 4 ≤ i) (tree : D2FlowTree h) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 5)
      (d2FlowCandidateRole d 5)
      (d2FlowCandidateQuota d 5)
      (fun k => d2FlowCandidateCapacity d k 5) i tree := by
  induction tree generalizing i with
  | leaf G low high => trivial
  | node G low high children ih =>
      simp only [d2FlowStageInvInputs]
      constructor
      · intro j
        exact ih j (i := i + 1) (by omega)
      · have hnot : ¬ (2 ≤ 5 ∧ 5 ≤ tfD2 d ∧ i % 2 = 5 % 2 ∧
            3 * i + 3 * d ≥ 2 * 5 + 11 ∧ 3 * i < 5 + 8) := by omega
        have hfalse : d2FlowCandidateActive d 5 i = false := by
          simp only [d2FlowCandidateActive,
            if_neg (by decide : 5 ≠ 0), if_neg (by decide : 5 ≠ 1)]
          rw [decide_eq_false_iff_not]
          simpa using hnot
        simp [hfalse]

/-- A stage-five level-three bottom-descending sender satisfies its complete
local gate when its deficit is within the inherited child cap and its eight
level-four children retain native deficits. The recursive calls below it are
inactive at this stage. -/
theorem d2FlowCandidateStage5_botDesc_inputs
    (d : Nat) (hd : 9 ≤ d) (G low high : Nat)
    (hbalance : low + high = G)
    (children : Fin 8 → D2FlowTree (d - 4))
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 3 5)
    (hchildren : ∀ j,
      d2FlowTreeRootDeficit (children j) = 8192 * 8 ^ (d - 4)) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 5)
      (d2FlowCandidateRole d 5)
      (d2FlowCandidateQuota d 5)
      (fun k => d2FlowCandidateCapacity d k 5) 3
      (.node G low high children) := by
  rcases d2FlowCandidateStage5_frontiers d hd with
    ⟨_, _, hactive, hrole⟩
  have hcap : d2FlowCandidateCapacity d 3 5 = 2 ^ (3 * d + 8) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 5 3 .botDesc =
      15 * 2 ^ (3 * d - 4) := by
    have he : d2FlowCandidateCapacityExponent d 3 5 = 3 * d + 8 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    calc
      d2FlowCandidateQuota d 5 3 .botDesc =
          15 * 2 ^ (d2FlowCandidateCapacityExponent d 3 5 - 12) := by
        simp [d2FlowCandidateQuota]
      _ = 15 * 2 ^ (3 * d + 8 - 12) := by rw [he]
      _ = 15 * 2 ^ (3 * d - 4) := by congr 2 <;> omega
  have hexp : 1 ≤ 3 * d - 4 := by omega
  have hquotaEven : d2FlowCandidateQuota d 5 3 .botDesc % 2 = 0 := by
    rw [hquota]
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : 3 * d - 4 ≠ 0)
    rw [hk, pow_succ]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 5 3 .botDesc ≤
      d2FlowCandidateCapacity d 3 5 := by
    rw [hquota, hcap]
    have he : 3 * d + 8 = 12 + (3 * d - 4) := by omega
    rw [he, pow_add]
    norm_num
    omega
  have hnative : 8192 * 8 ^ (d - 4) = 2 ^ (3 * d + 1) := by
    rw [show (8192 : Nat) = 2 ^ 13 by norm_num,
      show (8 : Nat) = 2 ^ 3 by norm_num]
    rw [← Nat.pow_mul, ← Nat.pow_add]
    congr 1 <;> omega
  have htotal : d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) =
      2 ^ (3 * d + 4) := by
    calc
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) =
          8 * (8192 * 8 ^ (d - 4)) := by
            simp [d2FlowTotal, hchildren]
      _ = 2 ^ (3 * d + 4) := by
        rw [hnative, show (8 : Nat) = 2 ^ 3 by norm_num, ← Nat.pow_add]
        congr 1 <;> omega
  have hG' : G ≤ 8 * 2 ^ (3 * d - 4) := by
    rw [hcap] at hG
    have he : 3 * d + 8 = 12 + (3 * d - 4) := by omega
    rw [he, pow_add] at hG
    norm_num at hG
    omega
  have halloc : d2FlowCandidateQuota d 5 3 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
    rw [hquota, htotal]
    have he : 3 * d + 4 = 8 + (3 * d - 4) := by omega
    rw [he, pow_add]
    have hp : 0 < 2 ^ (3 * d - 4) := by positivity
    omega
  have hrecursive : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 5)
      (d2FlowCandidateRole d 5)
      (d2FlowCandidateQuota d 5)
      (fun k => d2FlowCandidateCapacity d k 5) 4 (children j) := by
    intro j
    exact d2FlowCandidateAny_stage5_inactive_inputs (d := d) (by omega) (children j)
  simp only [d2FlowStageInvInputs]
  refine ⟨hrecursive, ?_⟩
  simp only [hactive, if_true, hrole]
  refine ⟨hbalance, hG, ?_, halloc, hquotaEven, ?_, ?_⟩
  · exact hquotaCap
  · have hpow : 2 ^ (3 * d + 8) = 128 * 2 ^ (3 * d + 1) := by
      rw [show 3 * d + 8 = 7 + (3 * d + 1) by omega, pow_add]
      norm_num
    rw [hcap, hchildren ⟨0, by omega⟩, hnative, hpow]
  · have hpow : 2 ^ (3 * d + 8) = 128 * 2 ^ (3 * d + 1) := by
      rw [show 3 * d + 8 = 7 + (3 * d + 1) by omega, pow_add]
      norm_num
    rw [hcap, hchildren ⟨7, by omega⟩, hnative, hpow]

/-- A bot-rise sender fills its root deficit to the sum of its old child
deficits. This is the structural source of stage-four's saturated level-three
children. -/
theorem d2FlowStage_botRise_root_saturates
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high : Nat}
    (children : Fin 8 → D2FlowTree h) (hactive : active i = true)
    (hrole : role i = .botRise)
    (hcover : G ≤ d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j))) :
    d2FlowTreeRootDeficit
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
  simp only [d2FlowStage, hactive, if_true, hrole]
  change G + (d2FlowTotal
    (fun j => d2FlowTreeRootDeficit (children j)) - G) = _
  omega

/-- A valid bottom-rise transition preserves any lower bound on its root
deficit: child-cover makes the filled root at least its old root. -/
theorem d2FlowStage_botRise_root_mono_of_inv
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {scale h i G low high bound : Nat}
    (children : Fin 8 → D2FlowTree h)
    (hactive : active i = true) (hrole : role i = .botRise)
    (hinv : d2FlowTreeInv scale (.node G low high children))
    (hbound : bound ≤ G) :
    bound ≤ d2FlowTreeRootDeficit
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) := by
  have hcover := d2FlowTreeInv_node_children_cover children hinv
  have hsaturates := d2FlowStage_botRise_root_saturates
    (quota := quota) (h := h) (i := i) (G := G) (low := low)
    (high := high) children hactive hrole hcover
  rw [hsaturates]
  exact le_trans hbound hcover

/-- A bottom-descending sender adds its scheduled quota to the root deficit;
the parent cut changes only the child roots. -/
theorem d2FlowStage_botDesc_root_add_quota
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high : Nat}
    (children : Fin 8 → D2FlowTree h) (hactive : active i = true)
    (hrole : role i = .botDesc) :
    d2FlowTreeRootDeficit
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) = G + quota i .botDesc := by
  simp [d2FlowStage, hactive, hrole, d2FlowTreeRootDeficit]

/-- A top-descending root clears each level-one deficit, but its recursive
stage still reaches level two. If level one is inactive and level two is a
bottom-descending sender, every resulting level-two root receives its quota. -/
theorem d2FlowStage_topDesc_inactive_botDesc_grandchild_reserve
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h G low high : Nat}
    (children : Fin 8 → D2FlowTree (h + 2))
    (hactive0 : active 0 = true) (hrole0 : role 0 = .topDesc)
    (hactive1 : active 1 = false)
    (hactive2 : active 2 = true) (hrole2 : role 2 = .botDesc) :
    ∀ j k, quota 2 .botDesc ≤ d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 3) 0
            (.node G low high children)) j) k) := by
  intro j k
  cases hchild : children j with
  | node G1 low1 high1 grandchildren =>
      cases hgrandchild : grandchildren k with
      | node G2 low2 high2 greatGrandchildren =>
          have hrootChild : d2FlowTreeChild
              (d2FlowStage active role quota (h + 3) 0
                (.node G low high children)) j =
              d2FlowTreeSetRoot
                (d2FlowStage active role quota (h + 2) 1 (children j)) 0 0 0 := by
            simp only [d2FlowStage, hactive0, if_pos, hrole0]
            norm_num
            rfl
          have hfirst : d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowStage active role quota (h + 3) 0
                  (.node G low high children)) j) k =
              d2FlowTreeChild
                (d2FlowStage active role quota (h + 2) 1 (children j)) k := by
            rw [hrootChild]
            rw [d2FlowTreeChild_setRoot]
          have hsecond : d2FlowTreeChild
              (d2FlowStage active role quota (h + 2) 1 (children j)) k =
              d2FlowStage active role quota (h + 1) 2
                (grandchildren k) := by
            rw [hchild]
            exact d2FlowStage_inactive_child
              (active := active) (role := role) (quota := quota)
              (h := h + 1) (i := 1) (G := G1) (low := low1) (high := high1)
              (children := grandchildren) hactive1 k
          have hgrandchildEq : d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowStage active role quota (h + 3) 0
                  (.node G low high children)) j) k =
              d2FlowStage active role quota (h + 1) 2
                (.node G2 low2 high2 greatGrandchildren) := by
            calc
              _ = d2FlowTreeChild
                  (d2FlowStage active role quota (h + 2) 1 (children j)) k := hfirst
              _ = d2FlowStage active role quota (h + 1) 2
                  (grandchildren k) := hsecond
              _ = d2FlowStage active role quota (h + 1) 2
                  (.node G2 low2 high2 greatGrandchildren) := by rw [hgrandchild]
          rw [hgrandchildEq, d2FlowStage_botDesc_root_add_quota
            (active := active) (role := role) (quota := quota)
            (h := h) (i := 2) (G := G2) (low := low2) (high := high2)
            (children := greatGrandchildren) hactive2 hrole2]
          omega

/-- For the actual candidate stage-four schedule, every level-two root in the
output receives the stage-four bottom-descending quota. -/
theorem d2FlowCandidateStage4_levelTwo_reserves
    (d : Nat) (hd : 5 ≤ d) (tree : D2FlowTree (d + 3)) :
    ∀ j k, 15 * 2 ^ (3 * (d + 3) - 5) ≤ d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild (d2FlowCandidateStage (d + 3) 4 tree) j) k) := by
  cases tree with
  | node G low high children =>
      have hfront := d2FlowCandidateStage4_frontiers (d + 1) (by omega)
      have hactive0 : d2FlowCandidateActive (d + 3) 4 0 = true := by
        simpa using hfront.1
      have hrole0 : d2FlowCandidateRole (d + 3) 4 0 = .topDesc := by
        simpa using hfront.2.1
      have hactive2 : d2FlowCandidateActive (d + 3) 4 2 = true := by
        simpa using hfront.2.2.1
      have hrole2 : d2FlowCandidateRole (d + 3) 4 2 = .botDesc := by
        simpa using hfront.2.2.2
      have hactive1 : d2FlowCandidateActive (d + 3) 4 1 = false := by
        simp [d2FlowCandidateActive]
      have hreserve := d2FlowStage_topDesc_inactive_botDesc_grandchild_reserve
        (active := d2FlowCandidateActive (d + 3) 4)
        (role := d2FlowCandidateRole (d + 3) 4)
        (quota := d2FlowCandidateQuota (d + 3) 4)
        (h := d) (G := G) (low := low) (high := high)
        (children := children) hactive0 hrole0 hactive1 hactive2 hrole2
      have hquota := d2FlowCandidateStage4_levelTwo_quota (d + 3)
      simpa [d2FlowCandidateStage, hquota] using hreserve

/-- Stage four's top-descending root action gives every level-one subtree the
zero root profile needed by stage five's top-rise sender. -/
theorem d2FlowCandidateStage4_levelOne_roots_zero
    (d : Nat) (hd : 5 ≤ d) (tree : D2FlowTree (d + 3)) :
    ∀ j, d2FlowTreeRootData
      (d2FlowTreeChild (d2FlowCandidateStage (d + 3) 4 tree) j) =
        (0, 0, 0) := by
  cases tree with
  | node G low high children =>
      have hfront := d2FlowCandidateStage4_frontiers (d + 1) (by omega)
      have hactive0 : d2FlowCandidateActive (d + 3) 4 0 = true := by
        simpa using hfront.1
      have hrole0 : d2FlowCandidateRole (d + 3) 4 0 = .topDesc := by
        simpa using hfront.2.1
      intro j
      simpa [d2FlowCandidateStage] using
        d2FlowStage_topDesc_child_rootdata
          (active := d2FlowCandidateActive (d + 3) 4)
          (role := d2FlowCandidateRole (d + 3) 4)
          (quota := d2FlowCandidateQuota (d + 3) 4)
          (children := children) hactive0 hrole0 j

/-- The stage-five level-one top-rise input predicates follow from the actual
stage-four output profile, once the remaining level-three stage-five sender
predicates are supplied. -/
theorem d2FlowCandidateStage5_levelOne_inputs
    (d : Nat) (hd : 6 ≤ d) (tree : D2FlowTree (d + 3))
    (hrec : ∀ j k, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 3) 5)
      (d2FlowCandidateRole (d + 3) 5)
      (d2FlowCandidateQuota (d + 3) 5)
      (fun m => d2FlowCandidateCapacity (d + 3) m 5) 2
      (d2FlowTreeChild
        (d2FlowTreeChild (d2FlowCandidateStage (d + 3) 4 tree) j) k)) :
    ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 3) 5)
      (d2FlowCandidateRole (d + 3) 5)
      (d2FlowCandidateQuota (d + 3) 5)
      (fun m => d2FlowCandidateCapacity (d + 3) m 5) 1
      (d2FlowTreeChild (d2FlowCandidateStage (d + 3) 4 tree) j) := by
  intro j
  cases hsubtree : d2FlowTreeChild (d2FlowCandidateStage (d + 3) 4 tree) j with
  | node G low high children =>
      have hdata := d2FlowCandidateStage4_levelOne_roots_zero d (by omega) tree j
      rw [hsubtree] at hdata
      simp only [d2FlowTreeRootData] at hdata
      have hG : G = 0 := congrArg Prod.fst hdata
      have htail : (low, high) = (0, 0) := congrArg Prod.snd hdata
      have hlow : low = 0 := congrArg Prod.fst htail
      have hhigh : high = 0 := congrArg Prod.snd htail
      have hbalance : low + high = 0 := by omega
      have hchildren : ∀ k,
          15 * 2 ^ (3 * (d + 3) - 5) ≤ d2FlowTreeRootDeficit (children k) := by
        intro k
        have hreserve := d2FlowCandidateStage4_levelTwo_reserves d (by omega) tree j k
        simpa [hsubtree] using hreserve
      have hrec' : ∀ k, d2FlowStageInvInputs 8192
          (d2FlowCandidateActive (d + 3) 5)
          (d2FlowCandidateRole (d + 3) 5)
          (d2FlowCandidateQuota (d + 3) 5)
          (fun m => d2FlowCandidateCapacity (d + 3) m 5) 2 (children k) := by
        intro k
        simpa [hsubtree] using hrec j k
      have hlocal := d2FlowCandidateStage5_topRise_inputs
        (d + 3) (by omega) low high hbalance children hchildren hrec'
      simpa [hsubtree, hG] using hlocal

/-- The complete stage-five input predicate on the actual stage-four output
reduces to the recursive input predicates rooted at its level-two nodes (the
level-three bottom-descending senders). -/
theorem d2FlowCandidateStage5_inputs_of_levelThree_inputs
    (d : Nat) (hd : 6 ≤ d) (tree : D2FlowTree (d + 3))
    (hrec : ∀ j k, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 3) 5)
      (d2FlowCandidateRole (d + 3) 5)
      (d2FlowCandidateQuota (d + 3) 5)
      (fun m => d2FlowCandidateCapacity (d + 3) m 5) 2
      (d2FlowTreeChild
        (d2FlowTreeChild (d2FlowCandidateStage (d + 3) 4 tree) j) k)) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 3) 5)
      (d2FlowCandidateRole (d + 3) 5)
      (d2FlowCandidateQuota (d + 3) 5)
      (fun m => d2FlowCandidateCapacity (d + 3) m 5) 0
      (d2FlowCandidateStage (d + 3) 4 tree) := by
  cases hstage : d2FlowCandidateStage (d + 3) 4 tree with
  | node G low high children =>
      have hactive0 : d2FlowCandidateActive (d + 3) 5 0 = false := by
        simp [d2FlowCandidateActive]
      simp only [d2FlowStageInvInputs]
      constructor
      · intro j
        simpa [hstage] using
          d2FlowCandidateStage5_levelOne_inputs d hd tree hrec j
      · simp [hactive0]

/-- A stage-three level-three `botRise` fills its root whenever its eight
level-four children retain their native deficits. This isolates the numeric
fact needed for the stage-four local gate from the separate reachable-tree
shape argument. -/
theorem d2FlowCandidateStage3_botRise_saturates_native_children
    (d h : Nat) (hd : 5 ≤ d) (G low high : Nat)
    (children : Fin 8 → D2FlowTree h)
    (hG : G ≤ 8192 * 8 ^ (h + 1))
    (hchildren : ∀ j,
      d2FlowTreeRootDeficit (children j) = 8192 * 8 ^ h) :
    d2FlowTreeRootDeficit
      (d2FlowStage (d2FlowCandidateActive (d + 2) 3)
        (d2FlowCandidateRole (d + 2) 3)
        (d2FlowCandidateQuota (d + 2) 3)
        (h + 1) 3 (.node G low high children)) =
      8192 * 8 ^ (h + 1) := by
  rcases d2FlowCandidateStage3_frontiers d hd with
    ⟨_, _, hactive, hrole⟩
  have htotal : d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) =
      8192 * 8 ^ (h + 1) := by
    simp [d2FlowTotal, hchildren, Fin.sum_univ_succ, Nat.pow_succ]
    <;> ring
  have hcover : G ≤ d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) := by
    rw [htotal]
    exact hG
  rw [d2FlowStage_botRise_root_saturates
    (active := d2FlowCandidateActive (d + 2) 3)
    (role := d2FlowCandidateRole (d + 2) 3)
    (quota := d2FlowCandidateQuota (d + 2) 3)
    (low := low) (high := high) (children := children)
    hactive hrole hcover]
  exact htotal

/-- After stage four, every subtree rooted below level two is recursively
inactive, so its stage-four input predicate requires no numerical bounds. -/
theorem d2FlowCandidateAny_stage4_inactive_inputs
    {d h i : Nat} (hi : 3 ≤ i) (tree : D2FlowTree h) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 4)
      (d2FlowCandidateRole (d + 2) 4)
      (d2FlowCandidateQuota (d + 2) 4)
      (fun k => d2FlowCandidateCapacity (d + 2) k 4)
      i tree := by
  induction tree generalizing i with
  | leaf G low high => trivial
  | node G low high children ih =>
      simp only [d2FlowStageInvInputs]
      constructor
      · intro j
        exact ih j (i := i + 1) (by omega)
      · have hnot : ¬ (2 ≤ 4 ∧ 4 ≤ tfD2 (d + 2) ∧ i % 2 = 4 % 2 ∧
            3 * i + 3 * (d + 2) ≥ 2 * 4 + 11 ∧ 3 * i < 4 + 8) := by
          by_cases h3 : i = 3
          · subst i
            norm_num
          · have h4 : 4 ≤ i := by omega
            omega
        have hfalse : d2FlowCandidateActive (d + 2) 4 i = false := by
          simp only [d2FlowCandidateActive,
            if_neg (by decide : 4 ≠ 0), if_neg (by decide : 4 ≠ 1)]
          rw [decide_eq_false_iff_not]
          simpa using hnot
        simp [hfalse]

/-- The numerical stage-four bottom-descending gate closes whenever its
level-three children carry their full native deficits. Here `M=2^(3d+4)`:
the level-two capacity is `512M`, the quota is `15M/8`, and endpoint parent
deficits may be as large as `M/2`. -/
theorem d2FlowCandidateStage4_botDesc_inputs
    (d : Nat) (hd : 5 ≤ d) (G low high : Nat)
    (hbalance : low + high = G)
    (hG : G ≤ 2 ^ (3 * d + 3))
    (children : Fin 8 → D2FlowTree (d - 1))
    (hchildren : ∀ j,
      d2FlowTreeRootDeficit (children j) = 64 * 2 ^ (3 * d + 4)) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 4)
      (d2FlowCandidateRole (d + 2) 4)
      (d2FlowCandidateQuota (d + 2) 4)
      (fun k => d2FlowCandidateCapacity (d + 2) k 4)
      2 (.node G low high children) := by
  rcases d2FlowCandidateStage4_frontiers d hd with
    ⟨_, _, hactive, hrole⟩
  have hcap : d2FlowCandidateCapacity (d + 2) 2 4 =
      512 * 2 ^ (3 * d + 4) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    rw [show 13 + 3 * (d + 2) - 6 = 3 * d + 13 by omega]
    rw [show 3 * d + 13 = 9 + (3 * d + 4) by omega, pow_add]
    norm_num
  have hquota : d2FlowCandidateQuota (d + 2) 4 2 .botDesc =
      15 * 2 ^ (3 * d + 1) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    congr 1 <;> omega
  have hM : 2 ^ (3 * d + 4) = 8 * 2 ^ (3 * d + 1) := by
    rw [show 3 * d + 4 = 3 + (3 * d + 1) by omega, pow_add]
    norm_num
  have hG' : G ≤ 4 * 2 ^ (3 * d + 1) := by
    rw [show 3 * d + 3 = 2 + (3 * d + 1) by omega, pow_add] at hG
    norm_num at hG
    exact hG
  have htotal : d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) =
      512 * 2 ^ (3 * d + 4) := by
    simp [d2FlowTotal, hchildren, Fin.sum_univ_succ]
    <;> ring
  have hscaledCap : d2FlowCandidateCapacity (d + 2) 2 4 =
      4096 * 2 ^ (3 * d + 1) := by rw [hcap, hM]; ring
  have hscaledTotal : d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) =
      4096 * 2 ^ (3 * d + 1) := by rw [htotal, hM]; ring
  have h512G : 512 * G ≤ d2FlowCandidateCapacity (d + 2) 2 4 := by
    rw [hscaledCap]
    omega
  have h256q : 256 * d2FlowCandidateQuota (d + 2) 4 2 .botDesc ≤
      d2FlowCandidateCapacity (d + 2) 2 4 := by
    rw [hquota, hscaledCap]
    omega
  have hquotaLe : d2FlowCandidateQuota (d + 2) 4 2 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
    rw [hquota, hscaledTotal]
    omega
  have hquotaEven :
      d2FlowCandidateQuota (d + 2) 4 2 .botDesc % 2 = 0 := by
    rw [hquota]
    have hdiv : 2 ∣ 2 ^ (3 * d + 1) := by
      rw [show 3 * d + 1 = 3 * d + 1 by omega, pow_succ]
      exact ⟨2 ^ (3 * d), by ring⟩
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_mul_of_dvd_right hdiv 15)
  have hfirst : d2FlowCandidateCapacity (d + 2) 2 4 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hcap, hchildren]
    omega
  have hlast : d2FlowCandidateCapacity (d + 2) 2 4 ≤
      128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩) := by
    rw [hcap, hchildren]
    omega
  simp only [d2FlowStageInvInputs]
  constructor
  · intro j
    exact d2FlowCandidateAny_stage4_inactive_inputs (by omega) (children j)
  · rw [hactive]
    simp only [if_true]
    constructor
    · exact hbalance
    · rw [hrole]
      exact ⟨h512G, h256q, hquotaLe, hquotaEven, hfirst, hlast⟩

/-- A stage-three bottom-rise node needs only balanced endpoint data; all of
its descendants lie below the active band. -/
theorem d2FlowCandidateStage3_botRise_inputs
    {d h G low high : Nat} (hd : 5 ≤ d)
    (children : Fin 8 → D2FlowTree h) (hbal : low + high = G) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 3)
      (d2FlowCandidateRole (d + 2) 3)
      (d2FlowCandidateQuota (d + 2) 3)
      (fun k => d2FlowCandidateCapacity (d + 2) k 3)
      3 (.node G low high children) := by
  rcases d2FlowCandidateStage3_frontiers d hd with
    ⟨_, _, hactive, hrole⟩
  simp only [d2FlowStageInvInputs]
  constructor
  · intro j
    exact d2FlowCandidateAny_stage3_inactive_inputs
      (d := d) (i := 4) (by omega) (children j)
  · rw [hactive]
    simp only [if_true]
    constructor
    · exact hbal
    · rw [hrole]
      trivial

/-- Stage-three top-rise input contract, reduced to the exact child-mass sum
and the two endpoint reserves. -/
theorem d2FlowCandidateStage3_topRise_inputs
    {d h : Nat} (hd : 5 ≤ d) (children : Fin 8 → D2FlowTree h)
    (hchildren : ∀ j,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (d + 2) 3)
        (d2FlowCandidateRole (d + 2) 3)
        (d2FlowCandidateQuota (d + 2) 3)
        (fun k => d2FlowCandidateCapacity (d + 2) k 3)
        2 (children j))
    (hmass : d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) =
      2 ^ (3 * d + 12))
    (hfirst : 2 ^ (3 * d + 12) ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hlast : 2 ^ (3 * d + 12) ≤
      128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩)) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 3)
      (d2FlowCandidateRole (d + 2) 3)
      (d2FlowCandidateQuota (d + 2) 3)
      (fun k => d2FlowCandidateCapacity (d + 2) k 3)
      1 (.node 0 0 0 children) := by
  rcases d2FlowCandidateStage3_frontiers d hd with
    ⟨hactive, hrole, _, _⟩
  have hcap : d2FlowCandidateCapacity (d + 2) 1 3 =
      2 ^ (3 * d + 12) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    congr 1 <;> omega
  have hquota : d2FlowCandidateQuota (d + 2) 3 1 .topRise =
      2 ^ (3 * d + 4) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    congr 1 <;> omega
  have hquotaCap : 256 * d2FlowCandidateQuota (d + 2) 3 1 .topRise =
      d2FlowCandidateCapacity (d + 2) 1 3 := by
    rw [hquota, hcap]
    rw [show 256 = 2 ^ 8 by norm_num,
      show 3 * d + 12 = 8 + (3 * d + 4) by omega,
      ← pow_add]
  have hquotaEven :
      d2FlowCandidateQuota (d + 2) 3 1 .topRise % 2 = 0 := by
    rw [hquota, show 3 * d + 4 = (3 * d + 3) + 1 by omega, pow_succ]
    simp
  simp only [d2FlowStageInvInputs]
  constructor
  · exact hchildren
  · rw [hactive]
    simp only [if_true]
    constructor
    · trivial
    · rw [hrole]
      refine ⟨by simp [hcap], ?_, ?_, hquotaEven, ?_, ?_⟩
      · exact le_of_eq hquotaCap
      · rw [hmass]
        have hquotaLe : d2FlowCandidateQuota (d + 2) 3 1 .topRise ≤
            2 ^ (3 * d + 12) := by
          rw [← hcap, ← hquotaCap]
          omega
        simpa using hquotaLe
      · simpa [hcap] using hfirst
      · simpa [hcap] using hlast

/-- A concrete stage-two bottom-descending sender adds its fixed quota to its
parent deficit. The children and cut profile do not affect this root update. -/
theorem d2FlowCandidateStage2_sender_root_update
    (d h G low high : Nat) (children : Fin 8 → D2FlowTree h)
    (hd : 5 ≤ d) :
    d2FlowTreeRootDeficit
      (d2FlowStage (d2FlowCandidateActive (d + 2) 2)
        (d2FlowCandidateRole (d + 2) 2)
        (d2FlowCandidateQuota (d + 2) 2)
        (h + 1) 2 (.node G low high children)) =
      G + d2FlowCandidateQuota (d + 2) 2 2 .botDesc := by
  rcases d2FlowCandidateStage2_boundary_role d hd with ⟨hactive, hrole⟩
  simp [d2FlowStage, d2FlowTreeRootDeficit, hactive, hrole]

/-- The first sender's level-two endpoint deficits are carried through the
stage-two bottom-descending sender as `38M` at the two outer endpoints and
`30M` at the six interior positions, where `M = 2^(3*d+4)`. This is the
concrete local arithmetic expected at the stage-three frontier. -/
theorem d2FlowCandidateStage2_afterStage1_levelTwo_deficits
    (d : Nat) (hd : 5 ≤ d) (j : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowStage (d2FlowCandidateActive (d + 2) 2)
        (d2FlowCandidateRole (d + 2) 2)
        (d2FlowCandidateQuota (d + 2) 2)
        d 2
        (d2FlowTreeSetRoot (d2FlowTreeFull 8192 d)
          (if j.val = 0 then 2 ^ (3 * d + 7)
            else if j.val = 7 then 2 ^ (3 * d + 7) else 0)
          (if j.val = 0 then 2 ^ (3 * d + 7) else 0)
          (if j.val = 7 then 2 ^ (3 * d + 7) else 0))) =
      if j.val = 0 ∨ j.val = 7 then 38 * 2 ^ (3 * d + 4)
      else 30 * 2 ^ (3 * d + 4) := by
  cases d with
  | zero => omega
  | succ d' =>
    have hd' : 5 ≤ d' + 1 := hd
    simp only [d2FlowTreeFull, d2FlowTreeSetRoot]
    rw [d2FlowCandidateStage2_sender_root_update (d' + 1) d'
    (if j.val = 0 then 2 ^ (3 * (d' + 1) + 7)
      else if j.val = 7 then 2 ^ (3 * (d' + 1) + 7) else 0)
    (if j.val = 0 then 2 ^ (3 * (d' + 1) + 7) else 0)
    (if j.val = 7 then 2 ^ (3 * (d' + 1) + 7) else 0)
    (fun _ => d2FlowTreeFull 8192 d') hd']
    have hquota : d2FlowCandidateQuota (d' + 3) 2 2 .botDesc =
        30 * 2 ^ (3 * (d' + 1) + 4) := by
      have hraw : d2FlowCandidateQuota (d' + 3) 2 2 .botDesc =
          15 * 2 ^ (3 * (d' + 1) + 5) := by
        simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
        congr 1 <;> omega
      rw [hraw, show 3 * (d' + 1) + 5 = (3 * (d' + 1) + 4) + 1 by omega,
        pow_succ]
      omega
    rw [hquota]
    have hend : 2 ^ (3 * (d' + 1) + 7) =
        8 * 2 ^ (3 * (d' + 1) + 4) := by
      rw [show 3 * (d' + 1) + 7 = 3 + (3 * (d' + 1) + 4) by omega,
        pow_add]
      norm_num
    rw [hend]
    split_ifs <;> omega

/-- In each actual first-sender subtree, the stage-two recursive call at its
inactive level-one root leaves the stage-two sender's exact level-two root
updates visible. This composes the first-stage child profile with the local
`38M`/`30M` calculation above. -/
theorem d2FlowCandidateStage2_stage1_subtree_frontier
    (d : Nat) (hd : 5 ≤ d) (j : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (d + 2) 2)
          (d2FlowCandidateRole (d + 2) 2)
          (d2FlowCandidateQuota (d + 2) 2)
          (d + 1) 1
          (d2FlowStage (d2FlowCandidateActive (d + 2) 1)
            (d2FlowCandidateRole (d + 2) 1)
            (d2FlowCandidateQuota (d + 2) 1)
            (d + 1) 1
            (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 d)))) j) =
      if j.val = 0 ∨ j.val = 7 then 38 * 2 ^ (3 * d + 4)
      else 30 * 2 ^ (3 * d + 4) := by
  let first := d2FlowStage (d2FlowCandidateActive (d + 2) 1)
    (d2FlowCandidateRole (d + 2) 1)
    (d2FlowCandidateQuota (d + 2) 1)
    (d + 1) 1 (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 d))
  have hinactive : d2FlowCandidateActive (d + 2) 2 1 = false := by
    simp [d2FlowCandidateActive]
  have hchild : d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive (d + 2) 2)
        (d2FlowCandidateRole (d + 2) 2)
        (d2FlowCandidateQuota (d + 2) 2) (d + 1) 1 first) j =
      d2FlowStage (d2FlowCandidateActive (d + 2) 2)
        (d2FlowCandidateRole (d + 2) 2)
        (d2FlowCandidateQuota (d + 2) 2) d 2
        (d2FlowTreeChild first j) := by
    cases first with
    | node G low high children =>
        simp [d2FlowStage, d2FlowTreeChild, hinactive]
  change d2FlowTreeRootDeficit
    (d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive (d + 2) 2)
        (d2FlowCandidateRole (d + 2) 2)
        (d2FlowCandidateQuota (d + 2) 2) (d + 1) 1 first) j) = _
  rw [hchild, d2FlowCandidateStage1_child_tree d hd j]
  exact d2FlowCandidateStage2_afterStage1_levelTwo_deficits d hd j

/-- After a stage-two bottom-descending cut, each exposed child has balanced
root endpoints, exactly the stage-three `botRise` precondition. This uses the
actual asymmetric cut profile rather than deriving balance from the general
invariant (which permits saturated nodes). -/
theorem d2FlowCandidateStage2_cut_child_stage3_botRise_inputs
    (d h : Nat) (hd : 5 ≤ d) (hh : 0 < h) (G low high : Nat)
    (leftFits : low + d2FlowCandidateQuota (d + 2) 2 2 .botDesc / 2 ≤
      8192 * 8 ^ h)
    (tailFits : high + d2FlowCandidateQuota (d + 2) 2 2 .botDesc / 2 ≤
      8192 * 8 ^ h) (k : Fin 8) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 3)
      (d2FlowCandidateRole (d + 2) 3)
      (d2FlowCandidateQuota (d + 2) 3)
      (fun m => d2FlowCandidateCapacity (d + 2) m 3)
      3
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (d + 2) 2)
          (d2FlowCandidateRole (d + 2) 2)
          (d2FlowCandidateQuota (d + 2) 2)
          (h + 1) 2
          (.node G low high (fun _ => d2FlowTreeFull 8192 h))) k) := by
  let q := d2FlowCandidateQuota (d + 2) 2 2 .botDesc
  let left := low + q / 2
  let tail := high + q / 2
  have hleft : left ≤ 8192 * 8 ^ h := by simpa [left, q] using leftFits
  have htail : tail ≤ 8192 * 8 ^ h := by simpa [tail, q] using tailFits
  have hprofile := d2FlowCandidateStage2_child_profile d h hd G low high
    left tail rfl rfl hleft htail k
  cases htree : d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive (d + 2) 2)
        (d2FlowCandidateRole (d + 2) 2)
        (d2FlowCandidateQuota (d + 2) 2)
        (h + 1) 2
        (.node G low high (fun _ => d2FlowTreeFull 8192 h))) k with
  | leaf G' low' high' =>
      omega
  | node G' low' high' grandchildren =>
      have htuple : (G', low', high') =
          (if k.val = 0 then (left, left, 0)
            else if k.val = 7 then (tail, 0, tail) else (0, 0, 0)) := by
        simpa [d2FlowTreeRootData, htree] using hprofile
      have hbalance : low' + high' = G' := by
        by_cases hk0 : k.val = 0
        · simp [hk0] at htuple
          omega
        · by_cases hk7 : k.val = 7
          · simp [hk0, hk7] at htuple
            omega
          · simp [hk0, hk7] at htuple
            omega
      exact d2FlowCandidateStage3_botRise_inputs (d := d) hd
        grandchildren hbalance

/-- Every actual level-two subtree after stages one and two satisfies the
stage-three recursive input gate: its level-three children have the balanced
root data produced by the stage-two asymmetric cut profile. -/
theorem d2FlowCandidateStage2_stage1_levelTwo_inputs
    (d : Nat) (hd : 5 ≤ d) (j : Fin 8) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 3)
      (d2FlowCandidateRole (d + 2) 3)
      (d2FlowCandidateQuota (d + 2) 3)
      (fun m => d2FlowCandidateCapacity (d + 2) m 3)
      2
      (d2FlowStage (d2FlowCandidateActive (d + 2) 2)
        (d2FlowCandidateRole (d + 2) 2)
        (d2FlowCandidateQuota (d + 2) 2)
        d 2
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive (d + 2) 1)
            (d2FlowCandidateRole (d + 2) 1)
            (d2FlowCandidateQuota (d + 2) 1)
            (d + 1) 1
            (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 d))) j)) := by
  cases d with
  | zero => omega
  | succ d' =>
    let A := 2 ^ (3 * (d' + 1) + 7)
    let G := if j.val = 0 then A else if j.val = 7 then A else 0
    let low := if j.val = 0 then A else 0
    let high := if j.val = 7 then A else 0
    have htree : d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (d' + 1 + 2) 1)
          (d2FlowCandidateRole (d' + 1 + 2) 1)
          (d2FlowCandidateQuota (d' + 1 + 2) 1)
          (d' + 1 + 1) 1
          (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 (d' + 1)))) j =
        .node G low high (fun _ => d2FlowTreeFull 8192 d') := by
      rw [d2FlowCandidateStage1_child_tree (d' + 1) hd j]
      simp [G, low, high, A, d2FlowTreeSetRoot, d2FlowTreeFull]
    have hlow : low ≤ 2 ^ (3 * (d' + 1) + 7) := by
      by_cases h : j.val = 0 <;> simp [low, A, h]
    have hhigh : high ≤ 2 ^ (3 * (d' + 1) + 7) := by
      by_cases h : j.val = 7 <;> simp [high, A, h]
    have hfit := d2FlowCandidateStage2_fronts_fit (d' + 1) hd
      low high hlow hhigh
    have hfit' :
        low + d2FlowCandidateQuota (d' + 1 + 2) 2 2 .botDesc / 2 ≤
            8192 * 8 ^ d' ∧
          high + d2FlowCandidateQuota (d' + 1 + 2) 2 2 .botDesc / 2 ≤
            8192 * 8 ^ d' := by
      simpa using hfit
    rw [htree]
    rcases d2FlowCandidateStage2_boundary_role (d' + 1) hd with
      ⟨hactive2, hrole2⟩
    simp only [d2FlowStage, hactive2, hrole2, d2FlowStageInvInputs]
    constructor
    · intro k
      simpa [d2FlowStage, hactive2, hrole2] using
        (d2FlowCandidateStage2_cut_child_stage3_botRise_inputs
          (d' + 1) d' hd (by omega) G low high hfit'.1 hfit'.2 k)
    · simp [d2FlowCandidateActive]

/-- In an actual stage-two boundary sender with full level-three child
subtrees, the cuts replace level-three roots but retain every level-four
child at native deficit. This is the concrete reservoir hypothesis needed
by the stage-three `botRise` saturation lemma. -/
theorem d2FlowCandidateStage2_boundary_grandchild_native
    (h : Nat) (hh : 3 ≤ h) (G low high : Nat) (k l : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild (h := h)
        (d2FlowTreeChild (h := h + 1)
          (d2FlowStage (d2FlowCandidateActive (h + 4) 2)
            (d2FlowCandidateRole (h + 4) 2)
            (d2FlowCandidateQuota (h + 4) 2)
            (h + 2) 2
            (.node G low high (fun _ => d2FlowTreeFull 8192 (h + 1)))) k) l) =
      8192 * 8 ^ h := by
  have hd : 5 ≤ h + 2 := by omega
  rcases d2FlowCandidateStage2_boundary_role (h + 2) hd with
    ⟨hactive, hrole⟩
  have hactive' : d2FlowCandidateActive (h + 4) 2 2 = true := by
    simpa [Nat.add_assoc] using hactive
  have hrole' : d2FlowCandidateRole (h + 4) 2 2 = .botDesc := by
    simpa [Nat.add_assoc] using hrole
  have hregular : d2FlowCandidateRole (h + 4) 2 2 = .topRise ∨
      d2FlowCandidateRole (h + 4) 2 2 = .mid ∨
      d2FlowCandidateRole (h + 4) 2 2 = .botDesc := Or.inr (Or.inr hrole')
  have hstage2three : d2FlowCandidateActive (h + 4) 2 3 = false := by
    simp [d2FlowCandidateActive]
  have hstage2four : d2FlowCandidateActive (h + 4) 2 4 = false := by
    simp [d2FlowCandidateActive]
  rw [d2FlowStage_regular_child_setroot
    (active := d2FlowCandidateActive (h + 4) 2)
    (role := d2FlowCandidateRole (h + 4) 2)
    (quota := d2FlowCandidateQuota (h + 4) 2)
    (h := h + 1) (i := 2) (G := G) (low := low) (high := high)
    (children := fun _ : Fin 8 => d2FlowTreeFull 8192 (h + 1))
    hactive' hregular k]
  rw [d2FlowTreeChild_setRoot]
  rw [show 2 + 1 = 3 by omega]
  change d2FlowTreeRootDeficit
    (d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive (h + 4) 2)
        (d2FlowCandidateRole (h + 4) 2)
        (d2FlowCandidateQuota (h + 4) 2) (h + 1) 3
        (.node (8192 * 8 ^ (h + 1)) 0 0
          (fun _ => d2FlowTreeFull 8192 h))) l) = _
  rw [d2FlowStage_inactive_child
    (active := d2FlowCandidateActive (h + 4) 2)
    (role := d2FlowCandidateRole (h + 4) 2)
    (quota := d2FlowCandidateQuota (h + 4) 2)
    (children := fun _ : Fin 8 => d2FlowTreeFull 8192 h)
    hstage2three l]
  rw [d2FlowStage_root_deficit_of_inactive
    (active := d2FlowCandidateActive (h + 4) 2)
    (role := d2FlowCandidateRole (h + 4) 2)
    (quota := d2FlowCandidateQuota (h + 4) 2)
    (tree := d2FlowTreeFull 8192 h) hstage2four]
  exact d2FlowTreeFull_root_deficit 8192 h

/-- The actual first-stage endpoint bounds leave the stage-two boundary
fronts widely disjoint: each endpoint is at most one eighth of a level-three
child, while the half-quota is less than one quarter of that child. -/
theorem d2FlowCandidateStage2_boundary_disjoint_of_endpoint_bounds
    (h : Nat) (hh : 3 ≤ h) (low high : Nat)
    (hlow : low ≤ 2 ^ (3 * (h + 2) + 7))
    (hhigh : high ≤ 2 ^ (3 * (h + 2) + 7)) :
    low + d2FlowCandidateQuota (h + 4) 2 2 .botDesc / 2 ≤
      8 * (8192 * 8 ^ (h + 1)) - high -
        d2FlowCandidateQuota (h + 4) 2 2 .botDesc / 2 := by
  let X := 2 ^ (3 * h + 10)
  have hendpoint : 2 ^ (3 * (h + 2) + 7) = 8 * X := by
    rw [show 3 * (h + 2) + 7 = 3 + (3 * h + 10) by omega, pow_add]
    norm_num [X]
  have hnative : 8192 * 8 ^ (h + 1) = 64 * X := by
    rw [show (8192 : Nat) = 2 ^ 13 by norm_num,
      show (8 : Nat) = 2 ^ 3 by norm_num, ← Nat.pow_mul, ← pow_add]
    rw [show 13 + 3 * (h + 1) = 6 + (3 * h + 10) by omega, pow_add]
    norm_num [X]
  have hquota : d2FlowCandidateQuota (h + 4) 2 2 .botDesc =
      15 * 2 ^ (3 * h + 11) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    congr 1 <;> omega
  have hhalf : d2FlowCandidateQuota (h + 4) 2 2 .botDesc / 2 =
      15 * X := by
    rw [hquota, show 3 * h + 11 = (3 * h + 10) + 1 by omega,
      pow_succ]
    dsimp [X]
    omega
  rw [hendpoint] at hlow hhigh
  rw [hnative, hhalf]
  omega

/-- Under a valid stage-two boundary cut, the exposed level-three sender is
saturated by stage three. This composes the native level-four reserve with
the `botRise` root-fill identity on the actual child tree. -/
theorem d2FlowCandidateStage3_boundary_child_saturates
    (h : Nat) (hh : 3 ≤ h) (G low high : Nat) (k : Fin 8)
    (hdisjoint : low +
        d2FlowCandidateQuota (h + 4) 2 2 .botDesc / 2 ≤
      8 * (8192 * 8 ^ (h + 1)) - high -
        d2FlowCandidateQuota (h + 4) 2 2 .botDesc / 2) :
    let stageTwo := d2FlowStage (d2FlowCandidateActive (h + 4) 2)
      (d2FlowCandidateRole (h + 4) 2)
      (d2FlowCandidateQuota (h + 4) 2)
      (h + 2) 2
      (.node G low high (fun _ => d2FlowTreeFull 8192 (h + 1)));
    d2FlowTreeRootDeficit
      (d2FlowStage (d2FlowCandidateActive (h + 4) 3)
        (d2FlowCandidateRole (h + 4) 3)
        (d2FlowCandidateQuota (h + 4) 3)
        (h + 1) 3
        (d2FlowTreeChild stageTwo k)) =
      8192 * 8 ^ (h + 1) := by
  have hd : 5 ≤ h + 2 := by omega
  rcases d2FlowCandidateStage2_boundary_role (h + 2) hd with
    ⟨hactive, hrole⟩
  have hactive2 : d2FlowCandidateActive (h + 4) 2 2 = true := by
    simpa [Nat.add_assoc] using hactive
  have hrole2 : d2FlowCandidateRole (h + 4) 2 2 = .botDesc := by
    simpa [Nat.add_assoc] using hrole
  have hregular : d2FlowCandidateRole (h + 4) 2 2 = .topRise ∨
      d2FlowCandidateRole (h + 4) 2 2 = .mid ∨
      d2FlowCandidateRole (h + 4) 2 2 = .botDesc := Or.inr (Or.inr hrole2)
  have hsize : d2FlowTreeRootDeficit (d2FlowTreeFull 8192 (h + 1)) =
      8192 * 8 ^ (h + 1) := d2FlowTreeFull_root_deficit 8192 (h + 1)
  have htotal : d2FlowTotal
      (fun _ : Fin 8 => d2FlowTreeRootDeficit (d2FlowTreeFull 8192 (h + 1))) =
      8 * (8192 * 8 ^ (h + 1)) := by
    simp [d2FlowTotal, hsize]
  have hrootBound : d2FlowTreeRootDeficit
      (d2FlowTreeChild (h := h + 1)
        (d2FlowStage (d2FlowCandidateActive (h + 4) 2)
          (d2FlowCandidateRole (h + 4) 2)
          (d2FlowCandidateQuota (h + 4) 2)
          (h + 2) 2
          (.node G low high
            (fun _ => d2FlowTreeFull 8192 (h + 1)))) k) ≤
      8192 * 8 ^ (h + 1) := by
    rw [d2FlowStage_regular_child_deficit
      (children := fun _ : Fin 8 => d2FlowTreeFull 8192 (h + 1))
      hactive2 hregular k]
    apply d2FlowCutChild_le_native
    · rw [hsize]
    · rw [htotal]
      simpa [hrole2] using hdisjoint
  have hstage3four : d2FlowCandidateActive (h + 4) 3 4 = false := by
    simp [d2FlowCandidateActive]
  let levelThree := d2FlowTreeChild (h := h + 1)
    (d2FlowStage (d2FlowCandidateActive (h + 4) 2)
      (d2FlowCandidateRole (h + 4) 2)
      (d2FlowCandidateQuota (h + 4) 2)
      (h + 2) 2
      (.node G low high (fun _ => d2FlowTreeFull 8192 (h + 1)))) k
  cases htree : levelThree with
  | node G3 low3 high3 children =>
      have hchildren : ∀ j,
          d2FlowTreeRootDeficit (children j) = 8192 * 8 ^ h := by
        intro j
        have hnative : d2FlowTreeRootDeficit
            (d2FlowTreeChild levelThree j) = 8192 * 8 ^ h := by
          change d2FlowTreeRootDeficit
              (d2FlowTreeChild (h := h)
                (d2FlowTreeChild (h := h + 1)
                  (d2FlowStage (d2FlowCandidateActive (h + 4) 2)
                    (d2FlowCandidateRole (h + 4) 2)
                    (d2FlowCandidateQuota (h + 4) 2)
                    (h + 2) 2
                    (.node G low high
                      (fun _ => d2FlowTreeFull 8192 (h + 1)))) k) j) = _
          exact d2FlowCandidateStage2_boundary_grandchild_native
            h hh G low high k j
        rw [htree] at hnative
        simpa [d2FlowTreeChild] using hnative
      have hG3 : G3 ≤ 8192 * 8 ^ (h + 1) := by
        have hbound' : d2FlowTreeRootDeficit levelThree ≤
            8192 * 8 ^ (h + 1) := by
          simpa [levelThree] using hrootBound
        rw [htree] at hbound'
        simpa [d2FlowTreeRootDeficit] using hbound'
      dsimp only
      change d2FlowTreeRootDeficit
        (d2FlowStage (d2FlowCandidateActive (h + 4) 3)
          (d2FlowCandidateRole (h + 4) 3)
          (d2FlowCandidateQuota (h + 4) 3)
          (h + 1) 3 levelThree) = _
      rw [htree]
      exact d2FlowCandidateStage3_botRise_saturates_native_children
        (d := h + 2) h hd G3 low3 high3 children hG3 hchildren

/-- The endpoint profile produced by the actual first stage discharges the
front-disjointness premise, so each actual stage-two boundary sender's
level-three child is saturated by stage three. -/
theorem d2FlowCandidateStage3_actual_boundary_child_saturates
    (h : Nat) (hh : 3 ≤ h) (j k : Fin 8) :
    let stageOne := d2FlowStage (d2FlowCandidateActive (h + 4) 1)
      (d2FlowCandidateRole (h + 4) 1) (d2FlowCandidateQuota (h + 4) 1)
      (h + 3) 1
      (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 (h + 2)));
    let stageTwo := d2FlowStage (d2FlowCandidateActive (h + 4) 2)
      (d2FlowCandidateRole (h + 4) 2) (d2FlowCandidateQuota (h + 4) 2)
      (h + 2) 2 (d2FlowTreeChild (h := h + 2) stageOne j);
    d2FlowTreeRootDeficit
      (d2FlowStage (d2FlowCandidateActive (h + 4) 3)
        (d2FlowCandidateRole (h + 4) 3)
        (d2FlowCandidateQuota (h + 4) 3)
        (h + 1) 3
        (d2FlowTreeChild (h := h + 1) stageTwo k)) =
      8192 * 8 ^ (h + 1) := by
  let stageOne := d2FlowStage (d2FlowCandidateActive (h + 4) 1)
    (d2FlowCandidateRole (h + 4) 1) (d2FlowCandidateQuota (h + 4) 1)
    (h + 3) 1
    (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 (h + 2)))
  let stageTwo := d2FlowStage (d2FlowCandidateActive (h + 4) 2)
    (d2FlowCandidateRole (h + 4) 2) (d2FlowCandidateQuota (h + 4) 2)
    (h + 2) 2 (d2FlowTreeChild (h := h + 2) stageOne j)
  have hd : 5 ≤ h + 2 := by omega
  have hfirstChild : d2FlowTreeChild (h := h + 2) stageOne j =
      d2FlowTreeSetRoot (d2FlowTreeFull 8192 (h + 2))
        (if j.val = 0 then 2 ^ (3 * (h + 2) + 7)
          else if j.val = 7 then 2 ^ (3 * (h + 2) + 7) else 0)
        (if j.val = 0 then 2 ^ (3 * (h + 2) + 7) else 0)
        (if j.val = 7 then 2 ^ (3 * (h + 2) + 7) else 0) := by
    exact d2FlowCandidateStage1_child_tree (h + 2) hd j
  cases htree : d2FlowTreeChild (h := h + 2) stageOne j with
  | node G low high children =>
      rw [htree] at hfirstChild
      simp [d2FlowTreeSetRoot, d2FlowTreeFull] at hfirstChild
      rcases hfirstChild with ⟨hG', hlow', hhigh', hchildren'⟩
      subst children
      have hlow : low ≤ 2 ^ (3 * (h + 2) + 7) := by
        rw [hlow']
        split_ifs <;> simp
      have hhigh : high ≤ 2 ^ (3 * (h + 2) + 7) := by
        rw [hhigh']
        split_ifs <;> simp
      have hdisjoint :=
        d2FlowCandidateStage2_boundary_disjoint_of_endpoint_bounds
          h hh low high hlow hhigh
      have hsat := d2FlowCandidateStage3_boundary_child_saturates
        h hh G low high k hdisjoint
      dsimp only
      rw [htree]
      change d2FlowTreeRootDeficit
        (d2FlowStage (d2FlowCandidateActive (h + 4) 3)
          (d2FlowCandidateRole (h + 4) 3)
          (d2FlowCandidateQuota (h + 4) 3)
          (h + 1) 3
          (d2FlowTreeChild (h := h + 1)
            (d2FlowStage (d2FlowCandidateActive (h + 4) 2)
              (d2FlowCandidateRole (h + 4) 2)
              (d2FlowCandidateQuota (h + 4) 2)
              (h + 2) 2
              (.node G low high
                (fun _ => d2FlowTreeFull 8192 (h + 1)))) k)) = _
      exact hsat

/-- The stage-two result inside one root child, before the root top-descending
cleanup resets that child's own root data. -/
def d2FlowCandidateStage2_firstSenderSubtree (d : Nat) :
    D2FlowTree (d + 1) :=
  d2FlowStage (d2FlowCandidateActive (d + 2) 2)
    (d2FlowCandidateRole (d + 2) 2)
    (d2FlowCandidateQuota (d + 2) 2)
    (d + 1) 1
    (d2FlowStage (d2FlowCandidateActive (d + 2) 1)
      (d2FlowCandidateRole (d + 2) 1)
      (d2FlowCandidateQuota (d + 2) 1)
      (d + 1) 1 (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 d)))

theorem d2FlowCandidateStage2_firstSenderSubtree_child_deficit
    (d : Nat) (hd : 5 ≤ d) (j : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild (d2FlowCandidateStage2_firstSenderSubtree d) j) =
      if j.val = 0 ∨ j.val = 7 then 38 * 2 ^ (3 * d + 4)
      else 30 * 2 ^ (3 * d + 4) := by
  simpa [d2FlowCandidateStage2_firstSenderSubtree] using
    d2FlowCandidateStage2_stage1_subtree_frontier d hd j

/-- Since stage two is inactive at the first-sender subtree root, its child
call is exactly the stage-two recursion on the corresponding stage-one child.
This identifies the concrete subtree used by the later stage-three reserve
argument, not just its root deficit. -/
theorem d2FlowCandidateStage2_firstSenderSubtree_child_eq
    (d : Nat) (hd : 5 ≤ d) (j : Fin 8) :
    d2FlowTreeChild (d2FlowCandidateStage2_firstSenderSubtree d) j =
      d2FlowStage (d2FlowCandidateActive (d + 2) 2)
        (d2FlowCandidateRole (d + 2) 2)
        (d2FlowCandidateQuota (d + 2) 2) d 2
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive (d + 2) 1)
            (d2FlowCandidateRole (d + 2) 1)
            (d2FlowCandidateQuota (d + 2) 1)
            (d + 1) 1 (.node 0 0 0
              (fun _ => d2FlowTreeFull 8192 d))) j) := by
  let first := d2FlowStage (d2FlowCandidateActive (d + 2) 1)
    (d2FlowCandidateRole (d + 2) 1)
    (d2FlowCandidateQuota (d + 2) 1)
    (d + 1) 1 (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 d))
  have hinactive : d2FlowCandidateActive (d + 2) 2 1 = false := by
    simp [d2FlowCandidateActive]
  have hchild : d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive (d + 2) 2)
        (d2FlowCandidateRole (d + 2) 2)
        (d2FlowCandidateQuota (d + 2) 2) (d + 1) 1 first) j =
      d2FlowStage (d2FlowCandidateActive (d + 2) 2)
        (d2FlowCandidateRole (d + 2) 2)
        (d2FlowCandidateQuota (d + 2) 2) d 2
        (d2FlowTreeChild first j) := by
    cases first with
    | node G low high children =>
        simp [d2FlowStage, d2FlowTreeChild, hinactive]
  simpa [d2FlowCandidateStage2_firstSenderSubtree, first] using hchild

/-- The concrete stage-two first-sender subtree retains native level-four
roots below each of its level-two senders. This is the reserve profile needed
by stage five after the intervening stage-three bot-rise. -/
theorem d2FlowCandidateStage2_firstSenderSubtree_levelFour_native
    (h : Nat) (hh : 3 ≤ h) (j k l : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateStage2_firstSenderSubtree (h + 2)) j) k) l) =
      8192 * 8 ^ h := by
  rw [d2FlowCandidateStage2_firstSenderSubtree_child_eq (h + 2) (by omega) j]
  rw [d2FlowCandidateStage1_child_tree (h + 2) (by omega) j]
  exact d2FlowCandidateStage2_boundary_grandchild_native
    h hh _ _ _ k l

/-- The eight actual level-two children inside a first-sender subtree jointly
meet the stage-three level-one top-rise gate. Their deficits add to capacity
exactly; the endpoint reserves retain a factor-of-19 surplus. -/
theorem d2FlowCandidateStage3_firstSenderSubtree_topRise_inputs
    (d : Nat) (hd : 5 ≤ d) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 3)
      (d2FlowCandidateRole (d + 2) 3)
      (d2FlowCandidateQuota (d + 2) 3)
      (fun m => d2FlowCandidateCapacity (d + 2) m 3)
      1 (.node 0 0 0 (fun j =>
        d2FlowTreeChild (d2FlowCandidateStage2_firstSenderSubtree d) j)) := by
  apply d2FlowCandidateStage3_topRise_inputs (d := d) hd
  · intro j
    have hinactive : d2FlowCandidateActive (d + 2) 2 1 = false := by
      simp [d2FlowCandidateActive]
    let first := d2FlowStage (d2FlowCandidateActive (d + 2) 1)
      (d2FlowCandidateRole (d + 2) 1)
      (d2FlowCandidateQuota (d + 2) 1)
      (d + 1) 1 (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 d))
    have hchild : d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (d + 2) 2)
          (d2FlowCandidateRole (d + 2) 2)
          (d2FlowCandidateQuota (d + 2) 2) (d + 1) 1 first) j =
        d2FlowStage (d2FlowCandidateActive (d + 2) 2)
          (d2FlowCandidateRole (d + 2) 2)
          (d2FlowCandidateQuota (d + 2) 2) d 2
          (d2FlowTreeChild first j) := by
      cases first with
      | node G low high children =>
          simp [d2FlowStage, d2FlowTreeChild, hinactive]
    change d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 3)
      (d2FlowCandidateRole (d + 2) 3)
      (d2FlowCandidateQuota (d + 2) 3)
      (fun m => d2FlowCandidateCapacity (d + 2) m 3)
      2 (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (d + 2) 2)
          (d2FlowCandidateRole (d + 2) 2)
          (d2FlowCandidateQuota (d + 2) 2) (d + 1) 1 first) j)
    rw [hchild]
    exact d2FlowCandidateStage2_stage1_levelTwo_inputs d hd j
  · have hsum : d2FlowTotal (fun j => d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowCandidateStage2_firstSenderSubtree d) j)) =
        2 ^ (3 * d + 12) := by
      have hp : 2 ^ (3 * d + 12) = 256 * 2 ^ (3 * d + 4) := by
        rw [show 3 * d + 12 = 8 + (3 * d + 4) by omega, pow_add]
        norm_num
      rw [hp]
      simp [d2FlowTotal, Fin.sum_univ_succ,
        d2FlowCandidateStage2_firstSenderSubtree_child_deficit, hd]
      <;> ring
    exact hsum
  · have hfirst : 2 ^ (3 * d + 12) ≤ 128 *
        d2FlowTreeRootDeficit
          (d2FlowTreeChild (d2FlowCandidateStage2_firstSenderSubtree d)
            ⟨0, by omega⟩) := by
      rw [d2FlowCandidateStage2_firstSenderSubtree_child_deficit d hd
        ⟨0, by omega⟩]
      simp
      have hp : 2 ^ (3 * d + 12) = 256 * 2 ^ (3 * d + 4) := by
        rw [show 3 * d + 12 = 8 + (3 * d + 4) by omega, pow_add]
        norm_num
      rw [hp]
      omega
    exact hfirst
  · have hlast : 2 ^ (3 * d + 12) ≤ 128 *
        d2FlowTreeRootDeficit
          (d2FlowTreeChild (d2FlowCandidateStage2_firstSenderSubtree d)
            ⟨7, by omega⟩) := by
      rw [d2FlowCandidateStage2_firstSenderSubtree_child_deficit d hd
        ⟨7, by omega⟩]
      simp
      have hp : 2 ^ (3 * d + 12) = 256 * 2 ^ (3 * d + 4) := by
        rw [show 3 * d + 12 = 8 + (3 * d + 4) by omega, pow_add]
        norm_num
      rw [hp]
      omega
    exact hlast

/-- Shape of the full tree after its stage-two root cleanup: each level-one
child is the corresponding first-sender subtree with only its own root reset. -/
theorem d2FlowCandidateRun_stage2_shape (d : Nat) (hd : 5 ≤ d) :
    d2FlowCandidateRun (d + 2) (d2FlowTreeInitial 8192 (d + 2)) 3 =
      .node 0 0 0 (fun _ =>
        d2FlowTreeSetRoot (d2FlowCandidateStage2_firstSenderSubtree d) 0 0 0) := by
  have hrun1 : d2FlowCandidateRun (d + 2)
      (d2FlowTreeInitial 8192 (d + 2)) 1 =
      d2FlowCandidateStage (d + 2) 0
        (d2FlowTreeInitial 8192 (d + 2)) := rfl
  have htree : d2FlowCandidateRun (d + 2)
      (d2FlowTreeInitial 8192 (d + 2)) 2 =
      .node 0 0 0 (fun _ =>
        d2FlowStage (d2FlowCandidateActive (d + 2) 1)
          (d2FlowCandidateRole (d + 2) 1)
          (d2FlowCandidateQuota (d + 2) 1)
          (d + 1) 1 (.node 0 0 0
            (fun _ => d2FlowTreeFull 8192 d)) ) := by
    rw [show d2FlowCandidateRun (d + 2)
        (d2FlowTreeInitial 8192 (d + 2)) 2 =
          d2FlowCandidateStage (d + 2) 1
            (d2FlowCandidateRun (d + 2)
              (d2FlowTreeInitial 8192 (d + 2)) 1) by rfl,
      hrun1, d2FlowCandidateBootstrap_shape (d + 1)]
    simp [d2FlowCandidateStage, d2FlowStage, d2FlowCandidateActive,
      d2FlowTreeSetRoot, d2FlowTreeFull]
  rcases d2FlowCandidateStage2_root_role d hd with ⟨hactive, hrole⟩
  rw [show d2FlowCandidateRun (d + 2)
      (d2FlowTreeInitial 8192 (d + 2)) 3 =
        d2FlowCandidateStage (d + 2) 2
          (d2FlowCandidateRun (d + 2)
            (d2FlowTreeInitial 8192 (d + 2)) 2) by rfl,
    htree]
  simp [d2FlowCandidateStage, d2FlowStage, hactive, hrole,
    d2FlowCandidateStage2_firstSenderSubtree]

/-- The complete concrete stage-two tree satisfies all stage-three sender
input obligations, including the root's eight level-one top-rise senders. -/
theorem d2FlowCandidateStage3_inputs (d : Nat) (hd : 5 ≤ d) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (d + 2) 3)
      (d2FlowCandidateRole (d + 2) 3)
      (d2FlowCandidateQuota (d + 2) 3)
      (fun m => d2FlowCandidateCapacity (d + 2) m 3)
      0 (d2FlowCandidateRun (d + 2)
        (d2FlowTreeInitial 8192 (d + 2)) 3) := by
  rw [d2FlowCandidateRun_stage2_shape d hd]
  simp only [d2FlowStageInvInputs]
  constructor
  · intro j
    cases htree : d2FlowCandidateStage2_firstSenderSubtree d with
    | node G low high children =>
        simpa [d2FlowTreeSetRoot, d2FlowTreeChild, htree] using
          d2FlowCandidateStage3_firstSenderSubtree_topRise_inputs d hd
  · have hinactive : d2FlowCandidateActive (d + 2) 3 0 = false := by
      simp [d2FlowCandidateActive]
    simp [hinactive]

/-- The actual stage-three top-rise cut transforms each stage-two ragged child
profile `38M,30M,...,38M` into the sparse level-two endpoint profile
`M/2,0,...,0,M/2`. This is the state profile needed by stage four. -/
theorem d2FlowCandidateStage3_firstSenderSubtree_child_profile
    (d : Nat) (hd : 5 ≤ d) (j : Fin 8) :
    d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (d + 2) 3)
          (d2FlowCandidateRole (d + 2) 3)
          (d2FlowCandidateQuota (d + 2) 3)
          (d + 1) 1
          (d2FlowTreeSetRoot
            (d2FlowCandidateStage2_firstSenderSubtree d) 0 0 0)) j) =
      if j.val = 0 then (2 ^ (3 * d + 3), 2 ^ (3 * d + 3), 0)
      else if j.val = 7 then (2 ^ (3 * d + 3), 0, 2 ^ (3 * d + 3))
      else (0, 0, 0) := by
  rcases d2FlowCandidateStage3_frontiers d hd with
    ⟨hactive, hrole, _, _⟩
  let M := 2 ^ (3 * d + 4)
  let sizes : Fin 8 → Nat := fun k =>
    if k.val = 0 ∨ k.val = 7 then 38 * M else 30 * M
  have hquota : d2FlowCandidateQuota (d + 2) 3 1 .topRise = M := by
    simp [M, d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    congr 1 <;> omega
  have htotal : d2FlowTotal sizes = 256 * M := by
    simp [d2FlowTotal, sizes, Fin.sum_univ_succ]
    <;> ring
  have hsizes : (fun k => d2FlowTreeRootDeficit
      (d2FlowTreeChild (d2FlowCandidateStage2_firstSenderSubtree d) k)) =
      sizes := by
    funext k
    simpa [sizes, M] using
      d2FlowCandidateStage2_firstSenderSubtree_child_deficit d hd k
  cases htree : d2FlowCandidateStage2_firstSenderSubtree d with
  | node G low high children =>
      have hcut := d2FlowStage_regular_child_setroot
        (active := d2FlowCandidateActive (d + 2) 3)
        (role := d2FlowCandidateRole (d + 2) 3)
        (quota := d2FlowCandidateQuota (d + 2) 3)
        (h := d) (i := 1) (G := 0) (low := 0) (high := 0)
        (children := children) hactive (Or.inl hrole) j
      simp only [htree, d2FlowTreeSetRoot]
      have hchildSizes : (fun k => d2FlowTreeRootDeficit (children k)) =
          sizes := by
        simpa only [htree, d2FlowTreeChild] using hsizes
      rw [hcut, d2FlowTreeRootData_setRoot]
      rw [hchildSizes, htotal, hrole, hquota]
      have hsizej : d2FlowTreeRootDeficit (children j) = sizes j :=
        congrFun hchildSizes j
      rw [hsizej]
      have htarget : M / 2 = 2 ^ (3 * d + 3) := by
        simp [M, show 3 * d + 4 = (3 * d + 3) + 1 by omega, pow_succ]
      rw [htarget]
      simpa [sizes, M, htarget] using
        d2FlowCutChild_tapered_38_30_profile M j

/-- Each actual level-two subtree entering stage four satisfies the numeric
`botDesc` gate. The post-stage-three endpoint profile supplies the parent
balance and half-capacity bound, while recursive stage-three calls fill all
eight level-three child roots to their native deficits. -/
theorem d2FlowCandidateStage4_firstSenderSubtree_child_inputs
    (h : Nat) (hh : 3 ≤ h) (j : Fin 8) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 4) 4)
      (d2FlowCandidateRole (h + 4) 4)
      (d2FlowCandidateQuota (h + 4) 4)
      (fun m => d2FlowCandidateCapacity (h + 4) m 4)
      2
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (h + 4) 3)
          (d2FlowCandidateRole (h + 4) 3)
          (d2FlowCandidateQuota (h + 4) 3)
          (h + 3) 1
          (d2FlowTreeSetRoot
            (d2FlowCandidateStage2_firstSenderSubtree (h + 2)) 0 0 0)) j) := by
  let base := d2FlowCandidateStage2_firstSenderSubtree (h + 2)
  let resetBase := d2FlowTreeSetRoot base 0 0 0
  let baseChildren := fun k => d2FlowTreeChild resetBase k
  let stageThreeRoot := d2FlowStage (d2FlowCandidateActive (h + 4) 3)
    (d2FlowCandidateRole (h + 4) 3)
    (d2FlowCandidateQuota (h + 4) 3) (h + 3) 1
    (.node 0 0 0 baseChildren)
  have hrootShape : resetBase = .node 0 0 0 baseChildren := by
    dsimp only [resetBase, baseChildren]
    rw [d2FlowTreeSetRoot_node base 0 0 0]
    congr 1
  have hroot : stageThreeRoot = d2FlowStage
      (d2FlowCandidateActive (h + 4) 3)
      (d2FlowCandidateRole (h + 4) 3)
      (d2FlowCandidateQuota (h + 4) 3) (h + 3) 1 resetBase := by
    simp [stageThreeRoot, hrootShape]
  have hprofile := d2FlowCandidateStage3_firstSenderSubtree_child_profile
    (h + 2) (by omega) j
  cases htree : d2FlowTreeChild stageThreeRoot j with
  | node G low high children =>
      have htree' := htree
      rw [hroot] at htree'
      rw [htree'] at hprofile
      simp [d2FlowTreeRootData] at hprofile
      have hdata : (G, low, high) =
          if j = 0 then (2 ^ (3 * (h + 2) + 3), 2 ^ (3 * (h + 2) + 3), 0)
          else if j.val = 7 then
            (2 ^ (3 * (h + 2) + 3), 0, 2 ^ (3 * (h + 2) + 3))
          else (0, 0, 0) := by
        simpa [Nat.add_assoc] using hprofile
      have hparent : G ≤ 2 ^ (3 * (h + 2) + 3) ∧ low + high = G := by
        by_cases hj0 : j = 0
        · simp [hj0] at hdata
          rcases hdata with ⟨rfl, rfl, rfl⟩
          exact ⟨le_rfl, by omega⟩
        · by_cases hj7 : j.val = 7
          · simp [hj0, hj7] at hdata
            rcases hdata with ⟨rfl, rfl, rfl⟩
            exact ⟨le_rfl, by omega⟩
          · simp [hj0, hj7] at hdata
            rcases hdata with ⟨rfl, rfl, rfl⟩
            exact ⟨Nat.zero_le _, by omega⟩
      have hchildren : ∀ k,
          d2FlowTreeRootDeficit (children k) =
          64 * 2 ^ (3 * (h + 2) + 4) := by
        intro k
        have hinactive2 : d2FlowCandidateActive (h + 4) 3 2 = false := by
          simp [d2FlowCandidateActive]
        cases hnode : baseChildren j with
        | node G' low' high' grandchildren =>
          have hstage2child : baseChildren j =
              d2FlowStage (d2FlowCandidateActive (h + 4) 2)
                (d2FlowCandidateRole (h + 4) 2)
                (d2FlowCandidateQuota (h + 4) 2) (h + 2) 2
                (d2FlowTreeChild
                  (d2FlowStage (d2FlowCandidateActive (h + 4) 1)
                    (d2FlowCandidateRole (h + 4) 1)
                    (d2FlowCandidateQuota (h + 4) 1)
                    (h + 3) 1
                    (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 (h + 2)))) j) := by
            dsimp only [baseChildren, resetBase]
            rw [d2FlowTreeChild_setRoot]
            exact d2FlowCandidateStage2_firstSenderSubtree_child_eq (h + 2)
              (by omega) j
          have hgrandchild : grandchildren k = d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive (h + 4) 2)
                (d2FlowCandidateRole (h + 4) 2)
                (d2FlowCandidateQuota (h + 4) 2) (h + 2) 2
                (d2FlowTreeChild
                  (d2FlowStage (d2FlowCandidateActive (h + 4) 1)
                    (d2FlowCandidateRole (h + 4) 1)
                    (d2FlowCandidateQuota (h + 4) 1)
                    (h + 3) 1
                    (.node 0 0 0 (fun _ => d2FlowTreeFull 8192 (h + 2)))) j)) k := by
            have hx := congrArg (fun tree => d2FlowTreeChild tree k) hstage2child
            rw [hnode] at hx
            simpa only [d2FlowTreeChild] using hx
          have hdecomp := d2FlowStage_child_decomposes
            (active := d2FlowCandidateActive (h + 4) 3)
            (role := d2FlowCandidateRole (h + 4) 3)
            (quota := d2FlowCandidateQuota (h + 4) 3)
            (h := h + 2) (i := 1) (G := 0) (low := 0) (high := 0)
            (children := baseChildren) j
          have hk := congrArg (fun tree => d2FlowTreeChild tree k) hdecomp
          dsimp at hk
          rw [htree] at hk
          rw [d2FlowTreeChild_setRoot] at hk
          rw [hnode, d2FlowStage_inactive_child
            (children := grandchildren) hinactive2 k] at hk
          rw [hgrandchild] at hk
          have hsat := d2FlowCandidateStage3_actual_boundary_child_saturates
            h (by omega) j k
          have hsat0 := hsat
          have hscale : 8192 * 8 ^ (h + 1) =
              64 * 2 ^ (3 * (h + 2) + 4) := by
            rw [show (8192 : Nat) = 2 ^ 13 by norm_num,
              show (8 : Nat) = 2 ^ 3 by norm_num, ← Nat.pow_mul,
              ← pow_add, show (64 : Nat) = 2 ^ 6 by norm_num,
              ← pow_add]
            congr 1 <;> omega
          simp only [d2FlowTreeChild] at hk
          rw [hk]
          simpa only [d2FlowTreeChild] using hsat0.trans hscale
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (h + 4) 4)
        (d2FlowCandidateRole (h + 4) 4)
        (d2FlowCandidateQuota (h + 4) 4)
        (fun m => d2FlowCandidateCapacity (h + 4) m 4)
        2 (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive (h + 4) 3)
            (d2FlowCandidateRole (h + 4) 3)
            (d2FlowCandidateQuota (h + 4) 3) (h + 3) 1 resetBase) j)
      rw [← hroot]
      rw [htree]
      exact d2FlowCandidateStage4_botDesc_inputs (h + 2) (by omega) G low high
        hparent.2 hparent.1 children hchildren

 /-- The concrete tree after the first three scheduled stages has a root
profile of zero and repeats the same stage-three boundary subtree below it. -/
theorem d2FlowCandidateRun_stage3_shape (h : Nat) (hh : 3 ≤ h) :
    d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4 =
      .node 0 0 0 (fun j =>
        d2FlowStage (d2FlowCandidateActive (h + 4) 3)
          (d2FlowCandidateRole (h + 4) 3)
          (d2FlowCandidateQuota (h + 4) 3)
          (h + 3) 1
          (d2FlowTreeSetRoot
            (d2FlowCandidateStage2_firstSenderSubtree (h + 2)) 0 0 0)) := by
  have hd : 5 ≤ h + 2 := by omega
  have hinactive0 : d2FlowCandidateActive (h + 4) 3 0 = false := by
    simp [d2FlowCandidateActive]
  have hrun3 := d2FlowCandidateRun_stage2_shape (h + 2) hd
  rw [show d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4 =
      d2FlowCandidateStage (h + 4) 3
        (d2FlowCandidateRun (h + 4)
          (d2FlowTreeInitial 8192 (h + 4)) 3) by rfl,
    hrun3]
  simp [d2FlowCandidateStage, d2FlowStage, hinactive0]

/-- The complete stage-four input predicate holds on the actual whole-tree
snapshot after stages one through three. Level one is inactive for stage four;
its eight level-two children use the local gate proved above, while the root
top-descending cleanup sees the zero root profile. -/
theorem d2FlowCandidateStage4_inputs (h : Nat) (hh : 3 ≤ h) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 4) 4)
      (d2FlowCandidateRole (h + 4) 4)
      (d2FlowCandidateQuota (h + 4) 4)
      (fun k => d2FlowCandidateCapacity (h + 4) k 4)
      0 (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 4) := by
  have hd : 5 ≤ h + 2 := by omega
  have hshape := d2FlowCandidateRun_stage3_shape h hh
  have hsubtree : ∀ j : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (h + 4) 4)
        (d2FlowCandidateRole (h + 4) 4)
        (d2FlowCandidateQuota (h + 4) 4)
        (fun k => d2FlowCandidateCapacity (h + 4) k 4)
        1
        (d2FlowStage (d2FlowCandidateActive (h + 4) 3)
          (d2FlowCandidateRole (h + 4) 3)
          (d2FlowCandidateQuota (h + 4) 3)
          (h + 3) 1
          (d2FlowTreeSetRoot
            (d2FlowCandidateStage2_firstSenderSubtree (h + 2)) 0 0 0)) := by
    intro j
    let subtree := d2FlowStage (d2FlowCandidateActive (h + 4) 3)
      (d2FlowCandidateRole (h + 4) 3)
      (d2FlowCandidateQuota (h + 4) 3)
      (h + 3) 1
      (d2FlowTreeSetRoot
        (d2FlowCandidateStage2_firstSenderSubtree (h + 2)) 0 0 0)
    change d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 4) 4)
      (d2FlowCandidateRole (h + 4) 4)
      (d2FlowCandidateQuota (h + 4) 4)
      (fun k => d2FlowCandidateCapacity (h + 4) k 4)
      1 subtree
    have hinactive1 : d2FlowCandidateActive (h + 4) 4 1 = false := by
      simp [d2FlowCandidateActive]
    cases htree : subtree with
    | node G low high children =>
        simp only [d2FlowStageInvInputs]
        constructor
        · intro k
          have hlocal :=
            d2FlowCandidateStage4_firstSenderSubtree_child_inputs h hh k
          simpa [subtree, htree] using hlocal
        · simp [hinactive1]
  rw [hshape]
  simp only [d2FlowStageInvInputs]
  constructor
  · intro j
    exact hsubtree j
  · rcases d2FlowCandidateStage4_frontiers (h + 2) hd with
      ⟨hactive0, hrole0, _, _⟩
    simp [hactive0, hrole0]

/-- The saturated-aware tree invariant is now established through the complete
third scheduled stage for every dimension at least seven. -/
theorem d2FlowCandidateStage3_preserves_inv (d : Nat) (hd : 5 ≤ d) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (d + 2)
        (d2FlowTreeInitial 8192 (d + 2)) 4) := by
  have hinv := d2FlowCandidateStage2_preserves_inv d hd
  have hpres := d2FlowStage_preserves_inv_of_inputs
    (active := d2FlowCandidateActive (d + 2) 3)
    (role := d2FlowCandidateRole (d + 2) 3)
    (quota := d2FlowCandidateQuota (d + 2) 3)
    (cap := fun k => d2FlowCandidateCapacity (d + 2) k 3)
    (i := 0)
    (d2FlowCandidateRun (d + 2)
      (d2FlowTreeInitial 8192 (d + 2)) 3)
    hinv (d2FlowCandidateStage3_inputs d hd)
  change d2FlowTreeInv 8192
    (d2FlowCandidateStage (d + 2) 3
      (d2FlowCandidateRun (d + 2)
        (d2FlowTreeInitial 8192 (d + 2)) 3))
  simpa [d2FlowCandidateStage] using hpres

/-- The repeated level-one subtree in the actual snapshot entering stage four. -/
def d2FlowCandidateStage4StageThreeRoot (h : Nat) : D2FlowTree (h + 3) :=
  d2FlowStage (d2FlowCandidateActive (h + 4) 3)
    (d2FlowCandidateRole (h + 4) 3)
    (d2FlowCandidateQuota (h + 4) 3) (h + 3) 1
    (d2FlowTreeSetRoot
      (d2FlowCandidateStage2_firstSenderSubtree (h + 2)) 0 0 0)

/- In the actual stage-three snapshot, the level-two source subtrees have
both the tree invariant and the complete stage-four local input predicate. -/
set_option maxHeartbeats 1000000 in
theorem d2FlowCandidateStage4_levelTwo_sources
    (h : Nat) (hh : 3 ≤ h) (j k : Fin 8) :
    d2FlowTreeInv 8192 (d2FlowTreeChild (d2FlowCandidateStage4StageThreeRoot h) k) ∧
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (h + 4) 4)
        (d2FlowCandidateRole (h + 4) 4)
        (d2FlowCandidateQuota (h + 4) 4)
        (fun q => d2FlowCandidateCapacity (h + 4) q 4)
        2 (d2FlowTreeChild (d2FlowCandidateStage4StageThreeRoot h) k) := by
  have hshape := d2FlowCandidateRun_stage3_shape h hh
  have hpreInv := d2FlowCandidateStage3_preserves_inv (h + 2) (by omega)
  rw [hshape] at hpreInv
  change d2FlowTreeInv 8192
    (.node 0 0 0 (fun _ => d2FlowCandidateStage4StageThreeRoot h)) at hpreInv
  have hrootInv := d2FlowTreeInv_grandchild
    (.node 0 0 0 (fun _ => d2FlowCandidateStage4StageThreeRoot h)) hpreInv j k
  have hnodeInv : d2FlowTreeInv 8192
      (d2FlowTreeChild (d2FlowCandidateStage4StageThreeRoot h) k) := by
    change d2FlowTreeInv 8192
      (d2FlowTreeChild (d2FlowCandidateStage4StageThreeRoot h) k)
    exact hrootInv
  have hnodeInputs := d2FlowCandidateStage4_firstSenderSubtree_child_inputs
    h hh k
  exact ⟨hnodeInv, by simpa [d2FlowCandidateStage4StageThreeRoot] using hnodeInputs⟩

/-- Before the stage-four cut, every level-four root below an actual
level-two sender still has its native deficit. Stage three's level-three
bot-rise leaves child roots to their inactive recursive calls, and stage two
already established the native reserve at those positions. -/
theorem d2FlowCandidateStage4_levelTwo_source_levelFour_native
    (h : Nat) (hh : 3 ≤ h) (j k l : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild (d2FlowCandidateStage4StageThreeRoot h) j) k) l) =
      8192 * 8 ^ h := by
  let base := d2FlowCandidateStage2_firstSenderSubtree (h + 2)
  let resetBase := d2FlowTreeSetRoot base 0 0 0
  have hresetNode : resetBase = .node 0 0 0 (fun q => d2FlowTreeChild base q) := by
    dsimp [resetBase]
    rw [d2FlowTreeSetRoot_node]
  have hfront := d2FlowCandidateStage3_frontiers (h + 2) (by omega)
  have hinactive2 : d2FlowCandidateActive (h + 4) 3 2 = false := by
    simp [d2FlowCandidateActive]
  have hproject := d2FlowStage_child_child_of_inactive
    (active := d2FlowCandidateActive (h + 4) 3)
    (role := d2FlowCandidateRole (h + 4) 3)
    (quota := d2FlowCandidateQuota (h + 4) 3)
    (h := h + 1) (i := 1) (G := 0) (low := 0) (high := 0)
    (children := fun q => d2FlowTreeChild base q) hinactive2 j k
  rw [← hresetNode] at hproject
  change d2FlowTreeChild
      (d2FlowTreeChild (d2FlowCandidateStage4StageThreeRoot h) j) k =
    d2FlowStage (d2FlowCandidateActive (h + 4) 3)
      (d2FlowCandidateRole (h + 4) 3)
      (d2FlowCandidateQuota (h + 4) 3) (h + 1) 3
      (d2FlowTreeChild (d2FlowTreeChild base j) k) at hproject
  have hprojectChild := congrArg (fun t => d2FlowTreeChild t l) hproject
  change d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild (d2FlowCandidateStage4StageThreeRoot h) j) k) l =
    d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive (h + 4) 3)
        (d2FlowCandidateRole (h + 4) 3)
        (d2FlowCandidateQuota (h + 4) 3) (h + 1) 3
        (d2FlowTreeChild (d2FlowTreeChild base j) k)) l at hprojectChild
  rw [hprojectChild]
  let source := d2FlowTreeChild (d2FlowTreeChild base j) k
  cases hsource : source with
  | node G low high grandchildren =>
      have hactive3 := hfront.2.2.1
      have hrole3 := hfront.2.2.2
      have hinactive4 : d2FlowCandidateActive (h + 4) 3 4 = false := by
        simp [d2FlowCandidateActive]
      have hbot := d2FlowStage_botRise_child_deficit
        (active := d2FlowCandidateActive (h + 4) 3)
        (role := d2FlowCandidateRole (h + 4) 3)
        (quota := d2FlowCandidateQuota (h + 4) 3)
        (G := G) (low := low) (high := high)
        (children := grandchildren) hactive3 hrole3 l
      rw [d2FlowStage_root_deficit_of_inactive
        (active := d2FlowCandidateActive (h + 4) 3)
        (role := d2FlowCandidateRole (h + 4) 3)
        (quota := d2FlowCandidateQuota (h + 4) 3)
        (tree := grandchildren l) hinactive4] at hbot
      have hnative := d2FlowCandidateStage2_firstSenderSubtree_levelFour_native
        h hh j k l
      have hnativeSub : d2FlowTreeRootDeficit
          (d2FlowTreeChild source l) = 8192 * 8 ^ h := by
        simpa [source, resetBase, d2FlowTreeChild_setRoot] using hnative
      rw [hsource] at hnativeSub
      simp only [d2FlowTreeChild] at hnativeSub
      change d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive (h + 4) 3)
              (d2FlowCandidateRole (h + 4) 3)
              (d2FlowCandidateQuota (h + 4) 3) (h + 1) 3 source) l) =
          8192 * 8 ^ h
      rw [hsource]
      exact hbot.trans hnativeSub

/-- The full stage-four output projects at depth two to the corresponding
level-two subtree after its own sender cut. -/
theorem d2FlowCandidateStage4_levelTwo_projection
    (h : Nat) (hh : 3 ≤ h) (j k : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowCandidateStage (h + 4) 4
          (d2FlowCandidateRun (h + 4)
            (d2FlowTreeInitial 8192 (h + 4)) 4)) j) k =
      d2FlowStage (d2FlowCandidateActive (h + 4) 4)
        (d2FlowCandidateRole (h + 4) 4)
        (d2FlowCandidateQuota (h + 4) 4)
        (h + 2) 2 (d2FlowTreeChild (d2FlowCandidateStage4StageThreeRoot h) k) := by
  have hshape := d2FlowCandidateRun_stage3_shape h hh
  have hactive1 : d2FlowCandidateActive (h + 4) 4 1 = false := by
    simp [d2FlowCandidateActive]
  have hproject := d2FlowStage_child_child_of_inactive
    (active := d2FlowCandidateActive (h + 4) 4)
    (role := d2FlowCandidateRole (h + 4) 4)
    (quota := d2FlowCandidateQuota (h + 4) 4)
    (h := h + 2) (i := 0) (G := 0) (low := 0) (high := 0)
    (children := fun _ => d2FlowCandidateStage4StageThreeRoot h) hactive1 j k
  rw [hshape]
  simpa [d2FlowCandidateStage, d2FlowCandidateStage4StageThreeRoot] using hproject

/- The actual stage-four level-two cut gives each level-three child the
inherited factor-two cap. -/
set_option maxHeartbeats 5000000
theorem d2FlowCandidateStage4_local_levelThree_cap
    (h : Nat) (hh : 3 ≤ h) (k m : Fin 8) :
    512 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (h + 4) 4)
          (d2FlowCandidateRole (h + 4) 4)
          (d2FlowCandidateQuota (h + 4) 4)
          (h + 2) 2
          (d2FlowTreeChild (d2FlowCandidateStage4StageThreeRoot h) k)) m) ≤
      2 * d2FlowCandidateCapacity (h + 4) 2 4 := by
  have hsource := d2FlowCandidateStage4_levelTwo_sources h hh 0 k
  rcases d2FlowCandidateStage4_frontiers (h + 2) (by omega) with
    ⟨_, _, hactive2, hrole2⟩
  exact d2FlowStage_regular_child_g_bound_of_tree_inputs
    (active := d2FlowCandidateActive (h + 4) 4)
    (role := d2FlowCandidateRole (h + 4) 4)
    (quota := d2FlowCandidateQuota (h + 4) 4)
    (cap := fun q => d2FlowCandidateCapacity (h + 4) q 4)
    (stageDepth := h + 1) (i := 2)
    (d2FlowTreeChild (d2FlowCandidateStage4StageThreeRoot h) k)
    hactive2 (Or.inr (Or.inr hrole2)) hsource.1 hsource.2 m

/-- The inherited factor-two cap is exactly the stage-five capacity. -/
theorem d2FlowCandidateStage4_local_levelThree_stage5_cap
    (h : Nat) (hh : 3 ≤ h) (k m : Fin 8) :
    512 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (h + 4) 4)
          (d2FlowCandidateRole (h + 4) 4)
          (d2FlowCandidateQuota (h + 4) 4)
          (h + 2) 2
          (d2FlowTreeChild (d2FlowCandidateStage4StageThreeRoot h) k)) m) ≤
      d2FlowCandidateCapacity (h + 4) 3 5 := by
  have hbound := d2FlowCandidateStage4_local_levelThree_cap h hh k m
  rw [d2FlowCandidateStage4_to_stage5_capacity (h + 1)] at hbound
  exact hbound
set_option maxHeartbeats 200000

/- Project the local stage-four child cap through the actual full-tree
schedule. -/
theorem d2FlowCandidateStage4_actual_levelThree_cap
    (h : Nat) (hh : 3 ≤ h) (j k m : Fin 8) :
    512 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateStage (h + 4) 4
              (d2FlowCandidateRun (h + 4)
                (d2FlowTreeInitial 8192 (h + 4)) 4)) j) k) m) ≤
      d2FlowCandidateCapacity (h + 4) 3 5 := by
  have hproject := d2FlowCandidateStage4_levelTwo_projection h hh j k
  rw [hproject]
  simpa using d2FlowCandidateStage4_local_levelThree_stage5_cap h hh k m

/-- The actual stage-four level-two cut preserves every level-four root, so
the native child profile required by stage five survives the projection. -/
theorem d2FlowCandidateStage4_actual_levelFour_native
    (h : Nat) (hh : 3 ≤ h) (j k m l : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateStage (h + 4) 4
                (d2FlowCandidateRun (h + 4)
                  (d2FlowTreeInitial 8192 (h + 4)) 4)) j) k) m) l) =
      8192 * 8 ^ h := by
  have hproject := d2FlowCandidateStage4_levelTwo_projection h hh j k
  have hprojectM := congrArg (fun t => d2FlowTreeChild t m) hproject
  change d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateStage (h + 4) 4
            (d2FlowCandidateRun (h + 4)
              (d2FlowTreeInitial 8192 (h + 4)) 4)) j) k) m =
    d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive (h + 4) 4)
        (d2FlowCandidateRole (h + 4) 4)
        (d2FlowCandidateQuota (h + 4) 4) (h + 2) 2
        (d2FlowTreeChild (d2FlowCandidateStage4StageThreeRoot h) k)) m
    at hprojectM
  have hprojectL := congrArg (fun t => d2FlowTreeChild t l) hprojectM
  change d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateStage (h + 4) 4
              (d2FlowCandidateRun (h + 4)
                (d2FlowTreeInitial 8192 (h + 4)) 4)) j) k) m) l =
    d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (h + 4) 4)
          (d2FlowCandidateRole (h + 4) 4)
          (d2FlowCandidateQuota (h + 4) 4) (h + 2) 2
          (d2FlowTreeChild (d2FlowCandidateStage4StageThreeRoot h) k)) m) l
    at hprojectL
  rw [hprojectL]
  let source := d2FlowTreeChild (d2FlowCandidateStage4StageThreeRoot h) k
  cases hsource : source with
  | node G low high children =>
      rcases d2FlowCandidateStage4_frontiers (h + 2) (by omega) with
        ⟨_, _, hactive2, hrole2⟩
      have hinactive3 : d2FlowCandidateActive (h + 4) 4 3 = false := by
        simp [d2FlowCandidateActive]
      have hinactive4 : d2FlowCandidateActive (h + 4) 4 4 = false := by
        simp [d2FlowCandidateActive]
      have hlocal := d2FlowStage_regular_child_grandchild_deficit
        (active := d2FlowCandidateActive (h + 4) 4)
        (role := d2FlowCandidateRole (h + 4) 4)
        (quota := d2FlowCandidateQuota (h + 4) 4)
        (G := G) (low := low) (high := high)
        (children := children) hactive2 (Or.inr (Or.inr hrole2))
        hinactive3 hinactive4 m l
      have hnative := d2FlowCandidateStage4_levelTwo_source_levelFour_native
        h hh k m l
      have hsource' :
          d2FlowTreeChild (d2FlowCandidateStage4StageThreeRoot h) k =
            .node G low high children := by
        simpa [source] using hsource
      have hnativeSub := hnative
      rw [hsource'] at hnativeSub
      simp only [d2FlowTreeChild] at hnativeSub
      change d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive (h + 4) 4)
                (d2FlowCandidateRole (h + 4) 4)
                (d2FlowCandidateQuota (h + 4) 4) (h + 2) 2 source) m) l) =
          8192 * 8 ^ h
      rw [hsource]
      exact hlocal.trans hnativeSub

/-- The saturated-aware invariant now composes through stage four on the
actual whole-tree snapshot for every dimension at least seven. -/
theorem d2FlowCandidateStage4_preserves_inv (h : Nat) (hh : 3 ≤ h) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 5) := by
  have hd : 5 ≤ h + 2 := by omega
  have hinv := d2FlowCandidateStage3_preserves_inv (h + 2) hd
  have hpres := d2FlowStage_preserves_inv_of_inputs
    (active := d2FlowCandidateActive (h + 4) 4)
    (role := d2FlowCandidateRole (h + 4) 4)
    (quota := d2FlowCandidateQuota (h + 4) 4)
    (cap := fun k => d2FlowCandidateCapacity (h + 4) k 4)
    (i := 0)
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4)
    hinv (d2FlowCandidateStage4_inputs h hh)
  change d2FlowTreeInv 8192
    (d2FlowCandidateStage (h + 4) 4
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 4))
  simpa [d2FlowCandidateStage] using hpres

/-- The actual stage-four level-four trees are fully native-sized, so the
invariant's child-cover forces each of their level-five child roots to be
native-sized as well. -/
theorem d2FlowCandidateStage4_actual_levelFive_native
    (h : Nat) (hh : 2 ≤ h) (j k m l q : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateStage (h + 5) 4
                  (d2FlowCandidateRun (h + 5)
                    (d2FlowTreeInitial 8192 (h + 5)) 4)) j) k) m) l) q) =
      8192 * 8 ^ h := by
  let stageFour := d2FlowCandidateStage (h + 5) 4
    (d2FlowCandidateRun (h + 5) (d2FlowTreeInitial 8192 (h + 5)) 4)
  let levelTwo := d2FlowTreeChild (d2FlowTreeChild stageFour j) k
  let levelFour := d2FlowTreeChild (d2FlowTreeChild levelTwo m) l
  have hglobal : d2FlowTreeInv 8192 stageFour := by
    change d2FlowTreeInv 8192
      (d2FlowCandidateRun (h + 5)
        (d2FlowTreeInitial 8192 (h + 5)) 5)
    exact d2FlowCandidateStage4_preserves_inv (h + 1) (by omega)
  have hlevelTwo : d2FlowTreeInv 8192 levelTwo := by
    exact d2FlowTreeInv_grandchild (h := h + 3) stageFour hglobal j k
  have hlevelFour : d2FlowTreeInv 8192 levelFour := by
    exact d2FlowTreeInv_grandchild (h := h + 1) levelTwo hlevelTwo m l
  have hnative := d2FlowCandidateStage4_actual_levelFour_native
    (h + 1) (by omega) j k m l
  cases hnode : levelFour with
  | node G low high children =>
      have hnodeInv : d2FlowTreeInv 8192 (.node G low high children) := by
        simpa [levelFour, hnode] using hlevelFour
      have hnative' := hnative
      change d2FlowTreeRootDeficit levelFour = 8192 * 8 ^ (h + 1)
        at hnative'
      rw [hnode] at hnative'
      have hfull : G = 8192 * 8 ^ (h + 1) := by
        simpa [d2FlowTreeRootDeficit] using hnative'
      have hchildren := d2FlowTreeInv_native_node_children
        (h := h) (scale := 8192) children hnodeInv hfull
      change d2FlowTreeRootDeficit (d2FlowTreeChild levelFour q) =
        8192 * 8 ^ h
      rw [hnode]
      simpa only [d2FlowTreeChild] using hchildren q

/-- Stage five carries every stage-four native level-five reserve through the
actual whole-tree transition. The path projection reduces the claim to its
level-four parent, where the local inactive-level fact applies. -/
theorem d2FlowCandidateStage5_actual_levelFive_native
    (h : Nat) (hh : 5 ≤ h) (j k m l q : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (h + 5)
                  (d2FlowTreeInitial 8192 (h + 5)) 6) j) k) m) l) q) =
      8192 * 8 ^ h := by
  let stageFour := d2FlowCandidateStage (h + 5) 4
    (d2FlowCandidateRun (h + 5) (d2FlowTreeInitial 8192 (h + 5)) 4)
  let levelFour := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild stageFour j) k) m) l
  have hproject := d2FlowStage_path5_projection
    (active := d2FlowCandidateActive (h + 5) 5)
    (role := d2FlowCandidateRole (h + 5) 5)
    (quota := d2FlowCandidateQuota (h + 5) 5)
    (i := 0) stageFour j k m l q
  change d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateStage (h + 5) 5 stageFour) j) k) m) l) q) =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive (h + 5) 5)
            (d2FlowCandidateRole (h + 5) 5)
            (d2FlowCandidateQuota (h + 5) 5) (h + 1) 4 levelFour) q)
    at hproject
  have hlocal : d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (h + 5) 5)
          (d2FlowCandidateRole (h + 5) 5)
          (d2FlowCandidateQuota (h + 5) 5) (h + 1) 4 levelFour) q) =
      d2FlowTreeRootDeficit (d2FlowTreeChild levelFour q) := by
    cases hnode : levelFour with
    | node G low high children =>
        have hpres := d2FlowCandidateStage5_levelFour_child_root
          (h + 5) h G low high (by omega) children q
        simpa [hnode, d2FlowCandidateStage] using hpres
  have hnative := d2FlowCandidateStage4_actual_levelFive_native
    h (by omega) j k m l q
  change d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild stageFour j) k) m) l) q) =
      8192 * 8 ^ h at hnative
  change d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateStage (h + 5) 5 stageFour) j) k) m) l) q) =
      8192 * 8 ^ h
  rw [hproject]
  exact hlocal.trans hnative

/-- Stage six also carries every level-five reserve through the actual
whole-tree transition; at level four its bottom-rise branch passes through
the recursively preserved child root. -/
theorem d2FlowCandidateStage6_actual_levelFive_native
    (h : Nat) (hh : 5 ≤ h) (j k m l q : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (h + 5)
                  (d2FlowTreeInitial 8192 (h + 5)) 7) j) k) m) l) q) =
      8192 * 8 ^ h := by
  let stageFive := d2FlowCandidateRun (h + 5)
    (d2FlowTreeInitial 8192 (h + 5)) 6
  let levelFour := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild stageFive j) k) m) l
  have hproject := d2FlowStage_path5_projection
    (active := d2FlowCandidateActive (h + 5) 6)
    (role := d2FlowCandidateRole (h + 5) 6)
    (quota := d2FlowCandidateQuota (h + 5) 6)
    (i := 0) stageFive j k m l q
  change d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateStage (h + 5) 6 stageFive) j) k) m) l) q) =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive (h + 5) 6)
            (d2FlowCandidateRole (h + 5) 6)
            (d2FlowCandidateQuota (h + 5) 6) (h + 1) 4 levelFour) q)
    at hproject
  have hlocal : d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (h + 5) 6)
          (d2FlowCandidateRole (h + 5) 6)
          (d2FlowCandidateQuota (h + 5) 6) (h + 1) 4 levelFour) q) =
      d2FlowTreeRootDeficit (d2FlowTreeChild levelFour q) := by
    cases hnode : levelFour with
    | node G low high children =>
        have hpres := d2FlowCandidateStage6_levelFour_child_root
          (h + 5) h G low high (by omega) children q
        simpa [hnode, d2FlowCandidateStage] using hpres
  have hnative := d2FlowCandidateStage5_actual_levelFive_native
    h hh j k m l q
  change d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild stageFive j) k) m) l) q) =
      8192 * 8 ^ h at hnative
  change d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateStage (h + 5) 6 stageFive) j) k) m) l) q) =
      8192 * 8 ^ h
  rw [hproject]
  exact hlocal.trans hnative

/-- Stage seven leaves the level-five native reserves unchanged in its actual
whole-tree transition, since both its level-four and level-five points are
inactive. -/
theorem d2FlowCandidateStage7_actual_levelFive_native
    (h : Nat) (hh : 5 ≤ h) (j k m l q : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (h + 5)
                  (d2FlowTreeInitial 8192 (h + 5)) 8) j) k) m) l) q) =
      8192 * 8 ^ h := by
  let stageSix := d2FlowCandidateRun (h + 5)
    (d2FlowTreeInitial 8192 (h + 5)) 7
  let levelFour := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild stageSix j) k) m) l
  have hproject := d2FlowStage_path5_projection
    (active := d2FlowCandidateActive (h + 5) 7)
    (role := d2FlowCandidateRole (h + 5) 7)
    (quota := d2FlowCandidateQuota (h + 5) 7)
    (i := 0) stageSix j k m l q
  change d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateStage (h + 5) 7 stageSix) j) k) m) l) q) =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive (h + 5) 7)
            (d2FlowCandidateRole (h + 5) 7)
            (d2FlowCandidateQuota (h + 5) 7) (h + 1) 4 levelFour) q)
    at hproject
  have hlocal : d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (h + 5) 7)
          (d2FlowCandidateRole (h + 5) 7)
          (d2FlowCandidateQuota (h + 5) 7) (h + 1) 4 levelFour) q) =
      d2FlowTreeRootDeficit (d2FlowTreeChild levelFour q) := by
    cases hnode : levelFour with
    | node G low high children =>
        have hpres := d2FlowCandidateStage7_levelFour_child_root
          (h + 5) h G low high (by omega) children q
        simpa [hnode, d2FlowCandidateStage] using hpres
  have hnative := d2FlowCandidateStage6_actual_levelFive_native
    h hh j k m l q
  change d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild stageSix j) k) m) l) q) =
      8192 * 8 ^ h at hnative
  change d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateStage (h + 5) 7 stageSix) j) k) m) l) q) =
      8192 * 8 ^ h
  rw [hproject]
  exact hlocal.trans hnative

/-- The actual stage-four output satisfies every stage-five level-three
bottom-descending gate: its normalized cap is below native saturation, so the
tree invariant gives balanced endpoints, and the level-four reserves remain
native. -/
theorem d2FlowCandidateStage5_actual_levelThree_inputs
    (h : Nat) (hh : 5 ≤ h) :
    ∀ j k m, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 4) 5)
      (d2FlowCandidateRole (h + 4) 5)
      (d2FlowCandidateQuota (h + 4) 5)
      (fun q => d2FlowCandidateCapacity (h + 4) q 5) 3
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateStage (h + 4) 4
              (d2FlowCandidateRun (h + 4)
                (d2FlowTreeInitial 8192 (h + 4)) 4)) j) k) m) := by
  intro j k m
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4) (d2FlowTreeInitial 8192 (h + 4)) 4)
  have hinvRun := d2FlowCandidateStage4_preserves_inv h (by omega)
  have hinv : d2FlowTreeInv 8192 stageFour := by
    change d2FlowTreeInv 8192
      (d2FlowCandidateStage (h + 4) 4
        (d2FlowCandidateRun (h + 4)
          (d2FlowTreeInitial 8192 (h + 4)) 4))
    exact hinvRun
  have hlevelTwoInv := d2FlowTreeInv_grandchild
    (h := h + 2) stageFour hinv j k
  let levelTwo := d2FlowTreeChild (d2FlowTreeChild stageFour j) k
  cases hparent : levelTwo with
  | node G₂ low₂ high₂ levelThree =>
      have hparentInv := hlevelTwoInv
      change d2FlowTreeInv 8192 levelTwo at hparentInv
      rw [hparent] at hparentInv
      simp only [d2FlowTreeInv] at hparentInv
      have hlevelThreeInv := hparentInv.2.2.2 m
      change d2FlowTreeInv 8192 (levelThree m) at hlevelThreeInv
      cases hnode : levelThree m with
      | node G low high children =>
          rw [hnode] at hlevelThreeInv
          simp only [d2FlowTreeInv] at hlevelThreeInv
          have hcap := d2FlowCandidateStage4_actual_levelThree_cap
            h (by omega) j k m
          change 512 * d2FlowTreeRootDeficit
              (d2FlowTreeChild levelTwo m) ≤
            d2FlowCandidateCapacity (h + 4) 3 5 at hcap
          rw [hparent, d2FlowTreeChild] at hcap
          change 512 * d2FlowTreeRootDeficit (levelThree m) ≤
            d2FlowCandidateCapacity (h + 4) 3 5 at hcap
          rw [hnode, d2FlowTreeRootDeficit] at hcap
          have hG : 512 * G ≤ d2FlowCandidateCapacity (h + 4) 3 5 := hcap
          have hcapExp : d2FlowCandidateCapacity (h + 4) 3 5 =
              2 ^ (3 * h + 20) := by
            simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
            omega
          have hnativeExp : 8192 * 8 ^ (h + 1) = 2 ^ (3 * h + 16) := by
            rw [show (8192 : Nat) = 2 ^ 13 by norm_num,
              show (8 : Nat) = 2 ^ 3 by norm_num,
              ← Nat.pow_mul, ← pow_add]
            congr 1 <;> omega
          have hfactor : 512 * 2 ^ (3 * h + 11) =
              2 ^ (3 * h + 20) := by
            rw [show (512 : Nat) = 2 ^ 9 by norm_num, ← pow_add]
            congr 1 <;> omega
          have hGsmall : G ≤ 2 ^ (3 * h + 11) := by
            rw [hcapExp, ← hfactor] at hG
            omega
          have hpow : 2 ^ (3 * h + 16) =
              32 * 2 ^ (3 * h + 11) := by
            rw [show 3 * h + 16 = 5 + (3 * h + 11) by omega, pow_add]
            norm_num
          have hbaseLt : 2 ^ (3 * h + 11) < 2 ^ (3 * h + 16) := by
            rw [hpow]
            have hp : 0 < 2 ^ (3 * h + 11) := by positivity
            omega
          have hstrict : G < 8192 * 8 ^ (h + 1) := by
            rw [hnativeExp]
            omega
          have hbalance : low + high = G := hlevelThreeInv.2.2.1 hstrict
          have hchildren : ∀ l,
              d2FlowTreeRootDeficit (children l) = 8192 * 8 ^ h := by
            intro l
            have hnative := d2FlowCandidateStage4_actual_levelFour_native
              h (by omega) j k m l
            change d2FlowTreeRootDeficit
              (d2FlowTreeChild (d2FlowTreeChild levelTwo m) l) =
                8192 * 8 ^ h at hnative
            rw [hparent, d2FlowTreeChild] at hnative
            change d2FlowTreeRootDeficit
              (d2FlowTreeChild (levelThree m) l) = 8192 * 8 ^ h at hnative
            rw [hnode, d2FlowTreeChild] at hnative
            simpa only [d2FlowTreeChild] using hnative
          change d2FlowStageInvInputs 8192
            (d2FlowCandidateActive (h + 4) 5)
            (d2FlowCandidateRole (h + 4) 5)
            (d2FlowCandidateQuota (h + 4) 5)
            (fun q => d2FlowCandidateCapacity (h + 4) q 5) 3
            (d2FlowTreeChild levelTwo m)
          rw [hparent, d2FlowTreeChild]
          change d2FlowStageInvInputs 8192
            (d2FlowCandidateActive (h + 4) 5)
            (d2FlowCandidateRole (h + 4) 5)
            (d2FlowCandidateQuota (h + 4) 5)
            (fun q => d2FlowCandidateCapacity (h + 4) q 5) 3
            (levelThree m)
          rw [hnode]
          exact d2FlowCandidateStage5_botDesc_inputs (h + 4) (by omega)
            G low high hbalance children hG hchildren

set_option maxHeartbeats 10000000 in
/-- The stage-five bottom-descending cut writes at least half its quota into
each endpoint level-four child. The equal-native profile makes these exact
front lengths, which stage six's bottom-rise nodes can carry forward. -/
theorem d2FlowCandidateStage5_endpoint_reserves (h : Nat) (hh : 5 ≤ h) :
    let stageFour := d2FlowCandidateStage (h + 4) 4
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 4)
    let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
    ∀ j k m,
      d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2 ≤
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m)
            ⟨0, by omega⟩) ∧
      d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2 ≤
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m)
            ⟨7, by omega⟩) := by
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4)
  let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
  change ∀ j k m, _
  have hfront := d2FlowCandidateStage5_frontiers (h + 4) (by omega)
  rcases hfront with ⟨_, _, hactive3, hrole3⟩
  intro j k m
  let source := d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild stageFour j) k) m
  have hinputs := d2FlowCandidateStage5_actual_levelThree_inputs h hh j k m
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive (h + 4) 5)
    (d2FlowCandidateRole (h + 4) 5)
    (d2FlowCandidateQuota (h + 4) 5)
    (fun q => d2FlowCandidateCapacity (h + 4) q 5) 3 source at hinputs
  have hrootProj : d2FlowTreeChild stageFive j =
      d2FlowStage (d2FlowCandidateActive (h + 4) 5)
        (d2FlowCandidateRole (h + 4) 5)
        (d2FlowCandidateQuota (h + 4) 5)
        (h + 3) 1 (d2FlowTreeChild stageFour j) := by
    change d2FlowTreeChild
        (d2FlowCandidateStage (h + 4) 5 stageFour) j = _
    unfold d2FlowCandidateStage
    cases htree : stageFour with
    | node G0 low0 high0 children0 =>
        simpa [htree] using (d2FlowStage_inactive_child
          (active := d2FlowCandidateActive (h + 4) 5)
          (role := d2FlowCandidateRole (h + 4) 5)
          (quota := d2FlowCandidateQuota (h + 4) 5)
          (h := h + 3) (i := 0) children0
          (by simp [d2FlowCandidateActive, tfD2]) j)
  have hgrandchildProj :
      d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive (h + 4) 5)
              (d2FlowCandidateRole (h + 4) 5)
              (d2FlowCandidateQuota (h + 4) 5)
              (h + 3) 1 (d2FlowTreeChild stageFour j)) k) m =
        d2FlowStage (d2FlowCandidateActive (h + 4) 5)
          (d2FlowCandidateRole (h + 4) 5)
          (d2FlowCandidateQuota (h + 4) 5)
          (h + 1) 3 source := by
    cases htree : stageFour with
    | node G0 low0 high0 children0 =>
        cases hparent : children0 j with
        | node G1 low1 high1 children1 =>
            have hproject := d2FlowStage_child_child_of_inactive
              (active := d2FlowCandidateActive (h + 4) 5)
              (role := d2FlowCandidateRole (h + 4) 5)
              (quota := d2FlowCandidateQuota (h + 4) 5)
              (h := h + 1) (i := 1) (G := G1) (low := low1)
              (high := high1) children1
              (by simp [d2FlowCandidateActive, tfD2]) k m
            simpa [htree, hparent, source, d2FlowTreeChild,
              Nat.add_assoc] using hproject
  have hlevelThreeProj :
      d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m =
        d2FlowStage (d2FlowCandidateActive (h + 4) 5)
          (d2FlowCandidateRole (h + 4) 5)
          (d2FlowCandidateQuota (h + 4) 5) (h + 1) 3 source := by
    rw [hrootProj]
    exact hgrandchildProj
  cases hsource : source with
  | node G low high children =>
    rw [hsource] at hinputs hlevelThreeProj
    have hgate := hinputs
    simp only [d2FlowStageInvInputs, hactive3, if_true, hrole3] at hgate
    rcases hgate with ⟨_, ⟨hbalance, hG, hquotaCap, halloc, heven,
      hleftReserve, hrightReserve⟩⟩
    have hcap : d2FlowCandidateCapacity (h + 4) 3 5 =
        2 ^ (3 * h + 20) := by
      simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
      omega
    have hquota : d2FlowCandidateQuota (h + 4) 5 3 .botDesc =
        15 * 2 ^ (3 * h + 8) := by
      calc
        d2FlowCandidateQuota (h + 4) 5 3 .botDesc =
            15 * 2 ^ (d2FlowCandidateCapacityExponent (h + 4) 3 5 - 12) := by
          simp [d2FlowCandidateQuota]
        _ = 15 * 2 ^ (3 * h + 8) := by
          congr 2 <;> simp [d2FlowCandidateCapacityExponent] <;> omega
    have hlow : low ≤ G := by omega
    have hhigh : high ≤ G := by omega
    have hquotaPos : 0 < d2FlowCandidateQuota (h + 4) 5 3 .botDesc := by
      rw [hquota]
      positivity
    have htotalGe : G ≤
        d2FlowTotal (fun l => d2FlowTreeRootDeficit (children l)) := by
      have hsubpos : 0 <
          d2FlowTotal (fun l => d2FlowTreeRootDeficit (children l)) - G :=
        lt_of_lt_of_le hquotaPos halloc
      have hlt : G <
          d2FlowTotal (fun l => d2FlowTreeRootDeficit (children l)) := by
        omega
      exact Nat.le_of_lt hlt
    have hconserve :
        (d2FlowTotal (fun l => d2FlowTreeRootDeficit (children l)) - G) + G =
          d2FlowTotal (fun l => d2FlowTreeRootDeficit (children l)) :=
      Nat.sub_add_cancel htotalGe
    have hquotaEq : d2FlowCandidateQuota (h + 4) 5 3 .botDesc =
        2 * (d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2) := by omega
    have hvalid := d2_ordinary_cut_fronts_valid
      (a := d2FlowTotal (fun l => d2FlowTreeRootDeficit (children l)) - G)
      (G := G) (total := d2FlowTotal
        (fun l => d2FlowTreeRootDeficit (children l)))
      (low := low) (high := high)
      (pi := d2FlowCandidateQuota (h + 4) 5 3 .botDesc)
      (half := d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2)
      (Uleft := d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
      (Uright := d2FlowTreeRootDeficit (children ⟨7, by omega⟩))
      (c := d2FlowCandidateCapacity (h + 4) 3 5)
        hbalance hconserve halloc hquotaEq hG hlow hhigh
        hquotaCap hleftReserve hrightReserve
    have hnative : ∀ l : Fin 8,
        d2FlowTreeRootDeficit (children l) = 8192 * 8 ^ h := by
      intro l
      have hn := d2FlowCandidateStage4_actual_levelFour_native
        h (by omega) j k m l
      change d2FlowTreeRootDeficit (d2FlowTreeChild source l) = _ at hn
      rw [hsource, d2FlowTreeChild] at hn
      exact hn
    have hu := hnative ⟨0, by omega⟩
    have htotal : d2FlowTotal (fun l => d2FlowTreeRootDeficit (children l)) =
        8 * (8192 * 8 ^ h) := by
      simp [d2FlowTotal, hnative]
    have hleftFit : low +
        d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2 ≤ 8192 * 8 ^ h := by
      have hf := hvalid.2.1
      simp [hnative] at hf
      exact hf
    have hrightFit : high +
        d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2 ≤ 8192 * 8 ^ h := by
      have hf := hvalid.2.2
      simp [hnative] at hf
      exact hf
    have hrightFormula :
        d2FlowTotal (fun l => d2FlowTreeRootDeficit (children l)) - high -
          d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2 =
        8 * (8192 * 8 ^ h) -
          (high + d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2) := by
      rw [htotal]
      omega
    have hprofile := d2FlowCutChild_uniform_asymmetric hleftFit hrightFit
    have hcut0 := d2FlowStage_regular_child_deficit
      (active := d2FlowCandidateActive (h + 4) 5)
      (role := d2FlowCandidateRole (h + 4) 5)
      (quota := d2FlowCandidateQuota (h + 4) 5)
      (i := 3) (G := G) (low := low) (high := high)
      children hactive3 (Or.inr (Or.inr hrole3)) ⟨0, by omega⟩
    have hcut7 := d2FlowStage_regular_child_deficit
      (active := d2FlowCandidateActive (h + 4) 5)
      (role := d2FlowCandidateRole (h + 4) 5)
      (quota := d2FlowCandidateQuota (h + 4) 5)
      (i := 3) (G := G) (low := low) (high := high)
      children hactive3 (Or.inr (Or.inr hrole3)) ⟨7, by omega⟩
    rw [hlevelThreeProj]
    simp_rw [hnative] at hcut0 hcut7
    simp [d2FlowPosition_uniform, d2FlowTotal, hrole3] at hcut0 hcut7
    have hrightFormula' :
        8 * (8192 * 8 ^ h) - high -
          d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2 =
        8 * (8192 * 8 ^ h) -
          (high + d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2) := by omega
    rw [hrightFormula'] at hcut0 hcut7
    have hprofile0 := hprofile (0 : Fin 8)
    have hprofile7 := hprofile (7 : Fin 8)
    have hprofile0' :
        d2FlowCutChild 0 (8192 * 8 ^ h)
          (low + d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2)
          (8 * (8192 * 8 ^ h) -
            (high + d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2)) =
        (low + d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2,
          low + d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2, 0) := by
      simpa using hprofile0
    rw [hprofile0'] at hcut0
    have hprofile7' :
        d2FlowCutChild (7 * (8192 * 8 ^ h)) (8192 * 8 ^ h)
          (low + d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2)
          (8 * (8192 * 8 ^ h) -
            (high + d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2)) =
        (high + d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2,
          0, high + d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2) := by
      simpa using hprofile7
    rw [hprofile7'] at hcut7
    simp at hcut0 hcut7
    have hcut0Fin :
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive (h + 4) 5)
              (d2FlowCandidateRole (h + 4) 5)
              (d2FlowCandidateQuota (h + 4) 5) (h + 1) 3
              (.node G low high children))
            ⟨0, by omega⟩) =
          low + d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2 := by
      simpa using hcut0
    have hcut7Fin :
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive (h + 4) 5)
              (d2FlowCandidateRole (h + 4) 5)
              (d2FlowCandidateQuota (h + 4) 5) (h + 1) 3
              (.node G low high children))
            ⟨7, by omega⟩) =
          high + d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2 := by
      simpa using hcut7
    constructor
    case left =>
      rw [hcut0Fin]
      omega
    case right =>
      rw [hcut7Fin]
      omega

set_option maxHeartbeats 1000000 in
/-- The complete stage-five input predicate holds on the actual stage-four
snapshot. Level two is inactive, so its recursive obligations are precisely
the level-three gates established above. -/
theorem d2FlowCandidateStage5_actual_inputs
    (h : Nat) (hh : 5 ≤ h) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 4) 5)
      (d2FlowCandidateRole (h + 4) 5)
      (d2FlowCandidateQuota (h + 4) 5)
      (fun q => d2FlowCandidateCapacity (h + 4) q 5) 0
      (d2FlowCandidateStage (h + 4) 4
        (d2FlowCandidateRun (h + 4)
          (d2FlowTreeInitial 8192 (h + 4)) 4)) := by
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4) (d2FlowTreeInitial 8192 (h + 4)) 4)
  have hlevelThree := d2FlowCandidateStage5_actual_levelThree_inputs h hh
  have hlevelTwo : ∀ j k, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 4) 5)
      (d2FlowCandidateRole (h + 4) 5)
      (d2FlowCandidateQuota (h + 4) 5)
      (fun q => d2FlowCandidateCapacity (h + 4) q 5) 2
      (d2FlowTreeChild (d2FlowTreeChild stageFour j) k) := by
    intro j k
    let levelTwo := d2FlowTreeChild (d2FlowTreeChild stageFour j) k
    cases hparent : levelTwo with
    | node G low high children =>
        change d2FlowStageInvInputs 8192
          (d2FlowCandidateActive (h + 4) 5)
          (d2FlowCandidateRole (h + 4) 5)
          (d2FlowCandidateQuota (h + 4) 5)
          (fun q => d2FlowCandidateCapacity (h + 4) q 5) 2 levelTwo
        rw [hparent]
        simp only [d2FlowStageInvInputs]
        constructor
        · intro m
          have hchild := hlevelThree j k m
          change d2FlowStageInvInputs 8192
            (d2FlowCandidateActive (h + 4) 5)
            (d2FlowCandidateRole (h + 4) 5)
            (d2FlowCandidateQuota (h + 4) 5)
            (fun q => d2FlowCandidateCapacity (h + 4) q 5) 3
            (d2FlowTreeChild levelTwo m) at hchild
          rw [hparent, d2FlowTreeChild] at hchild
          exact hchild
        · have hinactive : d2FlowCandidateActive (h + 4) 5 2 = false := by
            simp [d2FlowCandidateActive]
          simp [hinactive]
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive ((h + 1) + 3) 5)
    (d2FlowCandidateRole ((h + 1) + 3) 5)
    (d2FlowCandidateQuota ((h + 1) + 3) 5)
    (fun q => d2FlowCandidateCapacity ((h + 1) + 3) q 5) 0 stageFour
  exact d2FlowCandidateStage5_inputs_of_levelThree_inputs
    (h + 1) (by omega)
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4) hlevelTwo

/-- The saturated-aware tree invariant now composes through stage five on the
actual whole-tree snapshot for every dimension at least nine. -/
theorem d2FlowCandidateStage5_preserves_inv (h : Nat) (hh : 5 ≤ h) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 6) := by
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4) (d2FlowTreeInitial 8192 (h + 4)) 4)
  have hinvRun := d2FlowCandidateStage4_preserves_inv h (by omega)
  have hinv : d2FlowTreeInv 8192 stageFour := by
    change d2FlowTreeInv 8192
      (d2FlowCandidateStage (h + 4) 4
        (d2FlowCandidateRun (h + 4)
          (d2FlowTreeInitial 8192 (h + 4)) 4))
    exact hinvRun
  have hinputs := d2FlowCandidateStage5_actual_inputs h hh
  have hpres := d2FlowStage_preserves_inv_of_inputs
    (active := d2FlowCandidateActive (h + 4) 5)
    (role := d2FlowCandidateRole (h + 4) 5)
    (quota := d2FlowCandidateQuota (h + 4) 5)
    (cap := fun q => d2FlowCandidateCapacity (h + 4) q 5)
    (i := 0) stageFour hinv hinputs
  change d2FlowTreeInv 8192
    (d2FlowCandidateStage (h + 4) 5
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 5))
  simpa [d2FlowCandidateRun, d2FlowCandidateStage] using hpres

set_option maxHeartbeats 10000000 in
/-- The actual stage-five output supplies both scalar hypotheses needed by
the level-two stage-six mid gate: its parent cap comes from the level-one
top-rise cut, and its eight child reserves come from the level-three
bottom-descending updates. -/
theorem d2FlowCandidateStage6_actual_mid_state (h : Nat) (hh : 5 ≤ h) :
    let stageFour := d2FlowCandidateStage (h + 4) 4
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 4)
    let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
    ∀ j k,
      512 * d2FlowTreeRootDeficit
          (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) ≤
        d2FlowCandidateCapacity (h + 4) 2 6 ∧
      (∀ m, d2FlowCandidateQuota (h + 4) 5 3 .botDesc ≤
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m)) := by
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4)
  let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
  change ∀ j k,
    512 * d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) ≤
      d2FlowCandidateCapacity (h + 4) 2 6 ∧
    (∀ m, d2FlowCandidateQuota (h + 4) 5 3 .botDesc ≤
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m))
  have hinvFour := d2FlowCandidateStage4_preserves_inv h (by omega)
  have hinputsFive := d2FlowCandidateStage5_actual_inputs h hh
  have hfront := d2FlowCandidateStage5_frontiers (h + 4) (by omega)
  rcases hfront with ⟨hactive1, hrole1, hactive3, hrole3⟩
  have hactive0 : d2FlowCandidateActive (h + 4) 5 0 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hactive2 : d2FlowCandidateActive (h + 4) 5 2 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hcapacity := d2FlowCandidateStage6_capacity_identities (h + 4)
  intro j k
  have hlevelOneCap : ∀ k,
      512 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive (h + 4) 5)
            (d2FlowCandidateRole (h + 4) 5)
            (d2FlowCandidateQuota (h + 4) 5)
            (h + 3) 1 (d2FlowTreeChild stageFour j)) k) ≤
        2 * d2FlowCandidateCapacity (h + 4) 1 5 := by
    have hinvStageFour : d2FlowTreeInv 8192 stageFour := by
      change d2FlowTreeInv 8192
        (d2FlowCandidateRun (h + 4)
          (d2FlowTreeInitial 8192 (h + 4)) 5)
      exact hinvFour
    cases htree : stageFour with
    | node G0 low0 high0 children0 =>
        have hinvRoot := hinvStageFour
        rw [htree] at hinvRoot
        simp only [d2FlowTreeInv] at hinvRoot
        have hinvOne := hinvRoot.2.2.2 j
        have hinputsRoot := hinputsFive
        change d2FlowStageInvInputs 8192
          (d2FlowCandidateActive (h + 4) 5)
          (d2FlowCandidateRole (h + 4) 5)
          (d2FlowCandidateQuota (h + 4) 5)
          (fun q => d2FlowCandidateCapacity (h + 4) q 5) 0 stageFour
            at hinputsRoot
        rw [htree] at hinputsRoot
        simp only [d2FlowStageInvInputs] at hinputsRoot
        have hinputsOne := hinputsRoot.1 j
        have hbound := d2FlowStage_regular_child_g_bound_of_tree_inputs
          (children0 j) hactive1 (Or.inl hrole1)
          hinvOne hinputsOne
        simpa [htree] using hbound
  have hrootProj : d2FlowTreeChild stageFive j =
      d2FlowStage (d2FlowCandidateActive (h + 4) 5)
        (d2FlowCandidateRole (h + 4) 5)
        (d2FlowCandidateQuota (h + 4) 5)
        (h + 3) 1 (d2FlowTreeChild stageFour j) := by
    change d2FlowTreeChild
        (d2FlowCandidateStage (h + 4) 5 stageFour) j = _
    unfold d2FlowCandidateStage
    cases htree : stageFour with
    | node G0 low0 high0 children0 =>
        simpa [htree] using (d2FlowStage_inactive_child
          (active := d2FlowCandidateActive (h + 4) 5)
          (role := d2FlowCandidateRole (h + 4) 5)
          (quota := d2FlowCandidateQuota (h + 4) 5)
          (h := h + 3) (i := 0) children0 hactive0 j)
  have hcap : 512 * d2FlowTreeRootDeficit
      (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) ≤
      d2FlowCandidateCapacity (h + 4) 2 6 := by
    have hbound := hlevelOneCap k
    rw [← hrootProj] at hbound
    have hscale := hcapacity.1
    omega
  have hchildReserve : ∀ m,
      d2FlowCandidateQuota (h + 4) 5 3 .botDesc ≤
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m) := by
    intro m
    have hgrandchildProj :
        d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive (h + 4) 5)
                (d2FlowCandidateRole (h + 4) 5)
                (d2FlowCandidateQuota (h + 4) 5)
                (h + 3) 1 (d2FlowTreeChild stageFour j)) k) m =
          d2FlowStage (d2FlowCandidateActive (h + 4) 5)
            (d2FlowCandidateRole (h + 4) 5)
            (d2FlowCandidateQuota (h + 4) 5)
            (h + 1) 3
            (d2FlowTreeChild (d2FlowTreeChild
              (d2FlowTreeChild stageFour j) k) m) := by
      cases htree : stageFour with
      | node G0 low0 high0 children0 =>
          cases hparent : children0 j with
          | node G1 low1 high1 children1 =>
              have hproject := d2FlowStage_child_child_of_inactive
                (active := d2FlowCandidateActive (h + 4) 5)
                (role := d2FlowCandidateRole (h + 4) 5)
                (quota := d2FlowCandidateQuota (h + 4) 5)
                (h := h + 1) (i := 1) (G := G1) (low := low1)
                (high := high1) children1 hactive2 k m
              simpa [htree, hparent, d2FlowTreeChild, Nat.add_assoc]
                using hproject
    have hprojected :
        d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m) =
          d2FlowTreeRootDeficit
            (d2FlowStage (d2FlowCandidateActive (h + 4) 5)
              (d2FlowCandidateRole (h + 4) 5)
              (d2FlowCandidateQuota (h + 4) 5)
              (h + 1) 3
              (d2FlowTreeChild (d2FlowTreeChild
                (d2FlowTreeChild stageFour j) k) m)) := by
      rw [hrootProj]
      exact congrArg d2FlowTreeRootDeficit hgrandchildProj
    rw [hprojected]
    cases hsource : d2FlowTreeChild
        (d2FlowTreeChild (d2FlowTreeChild stageFour j) k) m with
    | node G3 low3 high3 children3 =>
        have hbotRoot := d2FlowStage_botDesc_root_add_quota
          (active := d2FlowCandidateActive (h + 4) 5)
          (role := d2FlowCandidateRole (h + 4) 5)
          (quota := d2FlowCandidateQuota (h + 4) 5)
          (h := h) (i := 3) (G := G3) (low := low3) (high := high3)
          children3 hactive3 hrole3
        rw [hbotRoot]
        omega
  exact ⟨hcap, hchildReserve⟩

set_option maxHeartbeats 10000000 in
/-- The full actual stage-six input gate at level two follows from the scalar
stage-five bridge and recursive gates below the eight level-three children.
The stage-five invariant supplies the endpoint balance because the exported
cap is strictly below the level-two native size. -/
theorem d2FlowCandidateStage6_actual_levelTwo_inputs
    (h : Nat) (hh : 5 ≤ h) :
    let stageFour := d2FlowCandidateStage (h + 4) 4
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 4)
    let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
    ∀ j k,
      (∀ m, d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (h + 4) 6)
        (d2FlowCandidateRole (h + 4) 6)
        (d2FlowCandidateQuota (h + 4) 6)
        (fun q => d2FlowCandidateCapacity (h + 4) q 6) 3
        (d2FlowTreeChild
          (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m)) →
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (h + 4) 6)
        (d2FlowCandidateRole (h + 4) 6)
        (d2FlowCandidateQuota (h + 4) 6)
        (fun q => d2FlowCandidateCapacity (h + 4) q 6) 2
        (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) := by
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4)
  let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
  change ∀ j k,
    (∀ m, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 4) 6)
      (d2FlowCandidateRole (h + 4) 6)
      (d2FlowCandidateQuota (h + 4) 6)
      (fun q => d2FlowCandidateCapacity (h + 4) q 6) 3
      (d2FlowTreeChild
        (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m)) →
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 4) 6)
      (d2FlowCandidateRole (h + 4) 6)
      (d2FlowCandidateQuota (h + 4) 6)
      (fun q => d2FlowCandidateCapacity (h + 4) q 6) 2
      (d2FlowTreeChild (d2FlowTreeChild stageFive j) k)
  have hstate := d2FlowCandidateStage6_actual_mid_state h hh
  have hinvFive := d2FlowCandidateStage5_preserves_inv h hh
  intro j k hrec
  let levelTwo := d2FlowTreeChild (d2FlowTreeChild stageFive j) k
  cases hnode : levelTwo with
  | node G low high children =>
      have hInv := d2FlowTreeInv_grandchild
        (h := h + 2) stageFive hinvFive j k
      change d2FlowTreeInv 8192 levelTwo at hInv
      rw [hnode] at hInv
      simp only [d2FlowTreeInv] at hInv
      have hstatejk := hstate j k
      change 512 * d2FlowTreeRootDeficit levelTwo ≤
        d2FlowCandidateCapacity (h + 4) 2 6 ∧ _ at hstatejk
      rw [hnode] at hstatejk
      have hG := hstatejk.1
      change 512 * G ≤ d2FlowCandidateCapacity (h + 4) 2 6 at hG
      have hchildrenReserve : ∀ m,
          d2FlowCandidateQuota (h + 4) 5 3 .botDesc ≤
            d2FlowTreeRootDeficit (children m) := by
        intro m
        have hb := hstatejk.2 m
        change d2FlowCandidateQuota (h + 4) 5 3 .botDesc ≤
          d2FlowTreeRootDeficit (d2FlowTreeChild levelTwo m) at hb
        rw [hnode] at hb
        simpa [d2FlowTreeChild] using hb
      have hrecChildren : ∀ m, d2FlowStageInvInputs 8192
          (d2FlowCandidateActive (h + 4) 6)
          (d2FlowCandidateRole (h + 4) 6)
          (d2FlowCandidateQuota (h + 4) 6)
          (fun q => d2FlowCandidateCapacity (h + 4) q 6) 3
          (children m) := by
        intro m
        have hm := hrec m
        change d2FlowStageInvInputs 8192
          (d2FlowCandidateActive (h + 4) 6)
          (d2FlowCandidateRole (h + 4) 6)
          (d2FlowCandidateQuota (h + 4) 6)
          (fun q => d2FlowCandidateCapacity (h + 4) q 6) 3
          (d2FlowTreeChild levelTwo m) at hm
        rw [hnode] at hm
        simpa [d2FlowTreeChild] using hm
      have hcapExp : d2FlowCandidateCapacityExponent (h + 4) 2 6 =
          3 * h + 15 := by
        simp [d2FlowCandidateCapacityExponent]
        omega
      have hcap : d2FlowCandidateCapacity (h + 4) 2 6 =
          2 ^ (3 * h + 15) := by
        simp [d2FlowCandidateCapacity, hcapExp]
      have hnative : 8192 * 8 ^ (h + 2) = 2 ^ (3 * h + 19) := by
        rw [show (8192 : Nat) = 2 ^ 13 by norm_num,
          show (8 : Nat) = 2 ^ 3 by norm_num,
          ← Nat.pow_mul, ← pow_add]
        congr 1 <;> omega
      have hpow : 2 ^ (3 * h + 19) = 16 * 2 ^ (3 * h + 15) := by
        rw [show 3 * h + 19 = 4 + (3 * h + 15) by omega,
          pow_add]
        norm_num
      have hcapLt : d2FlowCandidateCapacity (h + 4) 2 6 <
          8192 * 8 ^ (h + 2) := by
        rw [hcap, hnative, hpow]
        have hp : 0 < 2 ^ (3 * h + 15) := by positivity
        omega
      have hstrict : G < 8192 * 8 ^ (h + 2) := by omega
      have hbalance : low + high = G := hInv.2.2.1 hstrict
      have hmidInputs := d2FlowCandidateStage6_mid_inputs_of_state
        (h + 4) (h + 1) (by omega) G low high children hbalance hG
        hchildrenReserve hrecChildren
      rw [← hnode] at hmidInputs
      exact hmidInputs

set_option maxHeartbeats 10000000 in
/-- Every actual level-four stage-six bot-rise node is balanced: stage five's
ordinary bottom-descending cut wrote its root as the sum of the two cut ends.
All descendants below it are inactive in stage six. -/
theorem d2FlowCandidateStage6_actual_levelFour_inputs
    (h : Nat) (hh : 5 ≤ h) :
    let stageFour := d2FlowCandidateStage (h + 4) 4
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 4)
    let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
    ∀ j k m l,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (h + 4) 6)
        (d2FlowCandidateRole (h + 4) 6)
        (d2FlowCandidateQuota (h + 4) 6)
        (fun q => d2FlowCandidateCapacity (h + 4) q 6) 4
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m) l) := by
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4)
  let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
  change ∀ j k m l,
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 4) 6)
      (d2FlowCandidateRole (h + 4) 6)
      (d2FlowCandidateQuota (h + 4) 6)
      (fun q => d2FlowCandidateCapacity (h + 4) q 6) 4
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m) l)
  let d := h + 4
  have hfront5 := d2FlowCandidateStage5_frontiers (h + 4) (by omega)
  have hfront6 := d2FlowCandidateStage6_frontiers (h + 4) (by omega)
  rcases hfront5 with ⟨hactive1, hrole1, hactive3, hrole3⟩
  rcases hfront6 with ⟨_, _, _, _, hactive4, hrole4, _⟩
  have hactive0 : d2FlowCandidateActive (h + 4) 5 0 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hactive2 : d2FlowCandidateActive (h + 4) 5 2 = false := by
    simp [d2FlowCandidateActive, tfD2]
  intro j k m l
  have hrootProj : d2FlowTreeChild stageFive j =
      d2FlowStage (d2FlowCandidateActive (h + 4) 5)
        (d2FlowCandidateRole (h + 4) 5)
        (d2FlowCandidateQuota (h + 4) 5)
        (h + 3) 1 (d2FlowTreeChild stageFour j) := by
    change d2FlowTreeChild
        (d2FlowCandidateStage (h + 4) 5 stageFour) j = _
    unfold d2FlowCandidateStage
    cases htree : stageFour with
    | node G0 low0 high0 children0 =>
        simpa [htree] using (d2FlowStage_inactive_child
          (active := d2FlowCandidateActive (h + 4) 5)
          (role := d2FlowCandidateRole (h + 4) 5)
          (quota := d2FlowCandidateQuota (h + 4) 5)
          (h := h + 3) (i := 0) children0 hactive0 j)
  have hgrandchildProj :
      d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive (h + 4) 5)
              (d2FlowCandidateRole (h + 4) 5)
              (d2FlowCandidateQuota (h + 4) 5)
              (h + 3) 1 (d2FlowTreeChild stageFour j)) k) m =
        d2FlowStage (d2FlowCandidateActive (h + 4) 5)
          (d2FlowCandidateRole (h + 4) 5)
          (d2FlowCandidateQuota (h + 4) 5)
          (h + 1) 3
          (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild stageFour j) k) m) := by
    cases htree : stageFour with
    | node G0 low0 high0 children0 =>
        cases hparent : children0 j with
        | node G1 low1 high1 children1 =>
            have hproject := d2FlowStage_child_child_of_inactive
              (active := d2FlowCandidateActive (h + 4) 5)
              (role := d2FlowCandidateRole (h + 4) 5)
              (quota := d2FlowCandidateQuota (h + 4) 5)
              (h := h + 1) (i := 1) (G := G1) (low := low1)
              (high := high1) children1 hactive2 k m
            simpa [htree, hparent, d2FlowTreeChild, Nat.add_assoc]
              using hproject
  have hlevelFourProj :
      d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild stageFive j) k) m) l =
        d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive (h + 4) 5)
            (d2FlowCandidateRole (h + 4) 5)
            (d2FlowCandidateQuota (h + 4) 5)
            (h + 1) 3
            (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild stageFour j) k) m)) l := by
    rw [hrootProj]
    exact congrArg (fun t => d2FlowTreeChild t l) hgrandchildProj
  have hbalanced :
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild stageFive j) k) m) l)).2.1 +
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild stageFive j) k) m) l)).2.2 =
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild stageFive j) k) m) l)).1 := by
    rw [hlevelFourProj]
    cases htree : stageFour with
    | node G0 low0 high0 children0 =>
        cases hparent : children0 j with
        | node G1 low1 high1 children1 =>
            cases hsource : d2FlowTreeChild
                (d2FlowTreeChild (d2FlowTreeChild (D2FlowTree.node G0 low0 high0 children0) j) k) m with
            | node G3 low3 high3 children3 =>
                simpa [hsource, d2FlowTreeRootData_fst_eq_deficit] using
                  (d2FlowStage_regular_child_balanced
                    (active := d2FlowCandidateActive (h + 4) 5)
                    (role := d2FlowCandidateRole (h + 4) 5)
                    (quota := d2FlowCandidateQuota (h + 4) 5)
                    (G := G3) (low := low3) (high := high3)
                    (i := 3) (children := children3)
                    hactive3 (Or.inr (Or.inr hrole3)) l)
  let levelFour := d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m) l
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive (h + 4) 6)
    (d2FlowCandidateRole (h + 4) 6)
    (d2FlowCandidateQuota (h + 4) 6)
    (fun q => d2FlowCandidateCapacity (h + 4) q 6) 4 levelFour
  have hbalancedLevel :
      (d2FlowTreeRootData levelFour).2.1 +
        (d2FlowTreeRootData levelFour).2.2 =
        (d2FlowTreeRootData levelFour).1 := by
    simpa [levelFour] using hbalanced
  cases hnode : levelFour with
  | leaf G4 low4 high4 => omega
  | node G4 low4 high4 children4 =>
      have hbal := hbalancedLevel
      rw [hnode] at hbal
      simp only [d2FlowTreeRootData] at hbal
      simp only [d2FlowStageInvInputs, hactive4, if_true, hrole4]
      refine ⟨?_, ⟨hbal, trivial⟩⟩
      intro l
      apply d2FlowStageInvInputs_all_inactive
      intro k hk
      exact d2FlowCandidateStage6_inactive_tail d k (by omega) (by omega)

set_option maxHeartbeats 10000000 in
/-- Stage six's actual bottom-rise update preserves the stage-five endpoint
cut mass. Its filled root is the sum of descendant deficits, which dominates
the old root by the stage-five child-cover invariant. -/
theorem d2FlowCandidateStage6_local_endpoint_reserves
    (h : Nat) (hh : 5 ≤ h) :
    let stageFour := d2FlowCandidateStage (h + 4) 4
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 4)
    let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
    ∀ j k m,
      d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2 ≤
        d2FlowTreeRootDeficit
          (d2FlowStage (d2FlowCandidateActive (h + 4) 6)
            (d2FlowCandidateRole (h + 4) 6)
            (d2FlowCandidateQuota (h + 4) 6) h 4
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m)
              ⟨0, by omega⟩)) ∧
      d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2 ≤
        d2FlowTreeRootDeficit
          (d2FlowStage (d2FlowCandidateActive (h + 4) 6)
            (d2FlowCandidateRole (h + 4) 6)
            (d2FlowCandidateQuota (h + 4) 6) h 4
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m)
              ⟨7, by omega⟩)) := by
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4)
  let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
  change ∀ j k m, _
  have hinvRun := d2FlowCandidateStage5_preserves_inv h hh
  have hinvFive : d2FlowTreeInv 8192 stageFive := by
    change d2FlowTreeInv 8192
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 6)
    exact hinvRun
  have hfront := d2FlowCandidateStage6_frontiers (h + 4) (by omega)
  rcases hfront with ⟨hactive0, hrole0, _, _, hactive4, hrole4, _⟩
  intro j k m
  have hInvLevelTwo := d2FlowTreeInv_grandchild stageFive hinvFive j k
  have hends := d2FlowCandidateStage5_endpoint_reserves h hh j k m
  have hendsLeft := hends.1
  have hendsRight := hends.2
  have hInvLeft := d2FlowTreeInv_grandchild
    (d2FlowTreeChild (d2FlowTreeChild stageFive j) k)
    hInvLevelTwo m ⟨0, by omega⟩
  have hInvRight := d2FlowTreeInv_grandchild
    (d2FlowTreeChild (d2FlowTreeChild stageFive j) k)
    hInvLevelTwo m ⟨7, by omega⟩
  have hleft : d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2 ≤
      d2FlowTreeRootDeficit
        (d2FlowStage (d2FlowCandidateActive (h + 4) 6)
          (d2FlowCandidateRole (h + 4) 6)
          (d2FlowCandidateQuota (h + 4) 6) h 4
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m)
            ⟨0, by omega⟩)) := by
    let runDepth := h + 4
    let active6 := d2FlowCandidateActive runDepth 6
    let role6 := d2FlowCandidateRole runDepth 6
    let quota6 := d2FlowCandidateQuota runDepth 6
    cases hsource : d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m)
        ⟨0, by omega⟩ with
    | leaf G low high => omega
    | node G low high children =>
        have hinvSource := hInvLeft
        change d2FlowTreeInv 8192
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m)
            ⟨0, by omega⟩) at hinvSource
        rw [hsource] at hinvSource
        rw [hsource] at hendsLeft
        simp only [d2FlowTreeRootDeficit] at hendsLeft
        have hkeep := d2FlowStage_botRise_root_mono_of_inv
          (active := active6) (role := role6) (quota := quota6)
          (i := 4) (G := G) (low := low) (high := high)
          children hactive4 hrole4 hinvSource hendsLeft
        exact hkeep
  have hright : d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2 ≤
      d2FlowTreeRootDeficit
        (d2FlowStage (d2FlowCandidateActive (h + 4) 6)
          (d2FlowCandidateRole (h + 4) 6)
          (d2FlowCandidateQuota (h + 4) 6) h 4
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m)
            ⟨7, by omega⟩)) := by
    let runDepth := h + 4
    let active6 := d2FlowCandidateActive runDepth 6
    let role6 := d2FlowCandidateRole runDepth 6
    let quota6 := d2FlowCandidateQuota runDepth 6
    cases hsource : d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m)
        ⟨7, by omega⟩ with
    | leaf G low high => omega
    | node G low high children =>
        have hinvSource := hInvRight
        change d2FlowTreeInv 8192
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m)
            ⟨7, by omega⟩) at hinvSource
        rw [hsource] at hinvSource
        rw [hsource] at hendsRight
        simp only [d2FlowTreeRootDeficit] at hendsRight
        have hkeep := d2FlowStage_botRise_root_mono_of_inv
          (active := active6) (role := role6) (quota := quota6)
          (i := 4) (G := G) (low := low) (high := high)
          children hactive4 hrole4 hinvSource hendsRight
        exact hkeep
  exact ⟨hleft, hright⟩

set_option maxHeartbeats 10000000 in
/-- The recursive level-four results of stage six survive the level-two mid
parent's root overwrite. The two inactive intervening levels let the concrete
whole-tree snapshot project exactly to the local bot-rise call. -/
theorem d2FlowCandidateStage6_endpoint_reserves
    (h : Nat) (hh : 5 ≤ h) :
    let stageFour := d2FlowCandidateStage (h + 4) 4
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 4)
    let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
    let stageSix := d2FlowCandidateStage (h + 4) 6 stageFive
    ∀ j k m,
      d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2 ≤
        d2FlowTreeRootDeficit
          (d2FlowTreeChild (d2FlowTreeChild
            (d2FlowTreeChild (d2FlowTreeChild stageSix j) k) m)
            ⟨0, by omega⟩) ∧
      d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2 ≤
        d2FlowTreeRootDeficit
          (d2FlowTreeChild (d2FlowTreeChild
            (d2FlowTreeChild (d2FlowTreeChild stageSix j) k) m)
            ⟨7, by omega⟩) := by
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4)
  let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
  let stageSix := d2FlowCandidateStage (h + 4) 6 stageFive
  change ∀ j k m, _
  have hinactive1 : d2FlowCandidateActive (h + 4) 6 1 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hinactive3 : d2FlowCandidateActive (h + 4) 6 3 = false := by
    simp [d2FlowCandidateActive, tfD2]
  intro j k m
  have hrootProj :
      d2FlowTreeChild (d2FlowTreeChild stageSix j) k =
        d2FlowStage (d2FlowCandidateActive (h + 4) 6)
          (d2FlowCandidateRole (h + 4) 6)
          (d2FlowCandidateQuota (h + 4) 6) (h + 2) 2
          (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) := by
    change d2FlowTreeChild (d2FlowTreeChild
      (d2FlowCandidateStage (h + 4) 6 stageFive) j) k = _
    cases htree : stageFive with
    | node G low high children =>
        simpa [d2FlowCandidateStage, htree, Nat.add_assoc] using
          (d2FlowStage_child_child_of_inactive
            (active := d2FlowCandidateActive (h + 4) 6)
            (role := d2FlowCandidateRole (h + 4) 6)
            (quota := d2FlowCandidateQuota (h + 4) 6)
            (h := h + 2) (i := 0) (G := G) (low := low)
            (high := high) children hinactive1 j k)
  have hlocal := d2FlowCandidateStage6_local_endpoint_reserves h hh j k m
  have hprojection : ∀ l : Fin 8,
      d2FlowTreeChild (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (h + 4) 6)
          (d2FlowCandidateRole (h + 4) 6)
          (d2FlowCandidateQuota (h + 4) 6) (h + 2) 2
          (d2FlowTreeChild (d2FlowTreeChild stageFive j) k)) m) l =
        d2FlowStage (d2FlowCandidateActive (h + 4) 6)
          (d2FlowCandidateRole (h + 4) 6)
          (d2FlowCandidateQuota (h + 4) 6) h 4
          (d2FlowTreeChild (d2FlowTreeChild
            (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m) l) := by
    intro l
    cases hsource : d2FlowTreeChild (d2FlowTreeChild stageFive j) k with
    | node G low high children =>
        simpa [hsource, Nat.add_assoc] using
          (d2FlowStage_child_child_of_inactive
            (active := d2FlowCandidateActive (h + 4) 6)
            (role := d2FlowCandidateRole (h + 4) 6)
            (quota := d2FlowCandidateQuota (h + 4) 6)
            (h := h) (i := 2) (G := G) (low := low)
            (high := high) children hinactive3 m l)
  have hfullProjection (l : Fin 8) :
      d2FlowTreeChild (d2FlowTreeChild
        (d2FlowTreeChild (d2FlowTreeChild stageSix j) k) m) l =
      d2FlowStage (d2FlowCandidateActive (h + 4) 6)
        (d2FlowCandidateRole (h + 4) 6)
        (d2FlowCandidateQuota (h + 4) 6) h 4
        (d2FlowTreeChild (d2FlowTreeChild
          (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m) l) := by
    rw [hrootProj]
    exact hprojection l
  rcases hlocal with ⟨hleft, hright⟩
  constructor
  · rw [hfullProjection ⟨0, by omega⟩]
    exact hleft
  · rw [hfullProjection ⟨7, by omega⟩]
    exact hright

set_option maxHeartbeats 10000000 in
/-- Exact projection of an actual stage-six level-two subtree from the whole
tree. Stage six is top-descending at level zero and inactive at level one. -/
theorem d2FlowCandidateStage6_levelTwo_projection
    (h : Nat) (hh : 5 ≤ h) :
    let stageFour := d2FlowCandidateStage (h + 4) 4
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 4)
    let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
    let stageSix := d2FlowCandidateStage (h + 4) 6 stageFive
    ∀ j k, d2FlowTreeChild (d2FlowTreeChild stageSix j) k =
      d2FlowStage (d2FlowCandidateActive (h + 4) 6)
        (d2FlowCandidateRole (h + 4) 6)
        (d2FlowCandidateQuota (h + 4) 6) (h + 2) 2
        (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) := by
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4)
  let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
  let stageSix := d2FlowCandidateStage (h + 4) 6 stageFive
  change ∀ j k, _
  have hinactive1 : d2FlowCandidateActive (h + 4) 6 1 = false := by
    simp [d2FlowCandidateActive, tfD2]
  intro j k
  change d2FlowTreeChild (d2FlowTreeChild
    (d2FlowStage (d2FlowCandidateActive (h + 4) 6)
      (d2FlowCandidateRole (h + 4) 6)
      (d2FlowCandidateQuota (h + 4) 6) (h + 4) 0 stageFive) j) k =
    d2FlowStage (d2FlowCandidateActive (h + 4) 6)
      (d2FlowCandidateRole (h + 4) 6)
      (d2FlowCandidateQuota (h + 4) 6) (h + 2) 2
      (d2FlowTreeChild (d2FlowTreeChild stageFive j) k)
  cases htree : stageFive with
  | node G low high children =>
      have hrootChild := d2FlowStage_child_decomposes
        (active := d2FlowCandidateActive (h + 4) 6)
        (role := d2FlowCandidateRole (h + 4) 6)
        (quota := d2FlowCandidateQuota (h + 4) 6)
        (h := h + 3) (i := 0) (G := G) (low := low)
        (high := high) children j
      have hrootGrandchild := congrArg
        (fun tree => d2FlowTreeChild tree k) hrootChild
      change d2FlowTreeChild (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (h + 4) 6)
          (d2FlowCandidateRole (h + 4) 6)
          (d2FlowCandidateQuota (h + 4) 6) (h + 4) 0
          (.node G low high children)) j) k =
        d2FlowTreeChild (d2FlowTreeSetRoot
          (d2FlowStage (d2FlowCandidateActive (h + 4) 6)
            (d2FlowCandidateRole (h + 4) 6)
            (d2FlowCandidateQuota (h + 4) 6) (h + 3) 1
            (children j)) _ _ _) k at hrootGrandchild
      rw [d2FlowTreeChild_setRoot] at hrootGrandchild
      cases hchild : children j with
      | node G1 low1 high1 grandchildren =>
          have hinactiveChild := d2FlowStage_inactive_child
            (active := d2FlowCandidateActive (h + 4) 6)
            (role := d2FlowCandidateRole (h + 4) 6)
            (quota := d2FlowCandidateQuota (h + 4) 6)
            (h := h + 2) (i := 1) (G := G1) (low := low1)
            (high := high1) grandchildren hinactive1 k
          have hinactiveChild' := by
            simpa [Nat.add_assoc] using hinactiveChild
          rw [hchild] at hrootGrandchild
          rw [hinactiveChild'] at hrootGrandchild
          simpa [hchild, d2FlowTreeChild] using hrootGrandchild

set_option maxHeartbeats 10000000 in
/-- Level three is inactive at stage six; its recursive obligations are
exactly the balanced level-four bot-rise inputs proved from stage five's cuts. -/
theorem d2FlowCandidateStage6_actual_levelThree_inputs
    (h : Nat) (hh : 5 ≤ h) :
    let stageFour := d2FlowCandidateStage (h + 4) 4
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 4)
    let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
    ∀ j k m, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 4) 6)
      (d2FlowCandidateRole (h + 4) 6)
      (d2FlowCandidateQuota (h + 4) 6)
      (fun q => d2FlowCandidateCapacity (h + 4) q 6) 3
      (d2FlowTreeChild
        (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m) := by
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4)
  let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
  change ∀ j k m, d2FlowStageInvInputs 8192
    (d2FlowCandidateActive (h + 4) 6)
    (d2FlowCandidateRole (h + 4) 6)
    (d2FlowCandidateQuota (h + 4) 6)
    (fun q => d2FlowCandidateCapacity (h + 4) q 6) 3
    (d2FlowTreeChild
      (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m)
  have hinactive3 : d2FlowCandidateActive (h + 4) 6 3 = false := by
    simp [d2FlowCandidateActive, tfD2]
  intro j k m
  let levelThree := d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) m
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive (h + 4) 6)
    (d2FlowCandidateRole (h + 4) 6)
    (d2FlowCandidateQuota (h + 4) 6)
    (fun q => d2FlowCandidateCapacity (h + 4) q 6) 3 levelThree
  cases hnode : levelThree with
  | node G low high children =>
      simp only [d2FlowStageInvInputs, hinactive3, if_false]
      refine ⟨?_, trivial⟩
      intro l
      have hchild := d2FlowCandidateStage6_actual_levelFour_inputs h hh j k m l
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (h + 4) 6)
        (d2FlowCandidateRole (h + 4) 6)
        (d2FlowCandidateQuota (h + 4) 6)
        (fun q => d2FlowCandidateCapacity (h + 4) q 6) 4
        (d2FlowTreeChild levelThree l) at hchild
      rw [hnode] at hchild
      simpa [d2FlowTreeChild] using hchild

set_option maxHeartbeats 10000000 in
/-- Combining the actual level-three gates with the local midpoint lemma
closes every level-two stage-six input on the concrete stage-five output. -/
theorem d2FlowCandidateStage6_actual_levelTwo_inputs_closed
    (h : Nat) (hh : 5 ≤ h) :
    let stageFour := d2FlowCandidateStage (h + 4) 4
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 4)
    let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
    ∀ j k, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 4) 6)
      (d2FlowCandidateRole (h + 4) 6)
      (d2FlowCandidateQuota (h + 4) 6)
      (fun q => d2FlowCandidateCapacity (h + 4) q 6) 2
      (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) := by
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4)
  let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
  change ∀ j k, d2FlowStageInvInputs 8192
    (d2FlowCandidateActive (h + 4) 6)
    (d2FlowCandidateRole (h + 4) 6)
    (d2FlowCandidateQuota (h + 4) 6)
    (fun q => d2FlowCandidateCapacity (h + 4) q 6) 2
    (d2FlowTreeChild (d2FlowTreeChild stageFive j) k)
  intro j k
  apply d2FlowCandidateStage6_actual_levelTwo_inputs h hh j k
  intro m
  exact d2FlowCandidateStage6_actual_levelThree_inputs h hh j k m

set_option maxHeartbeats 10000000 in
/-- Stage six's inactive level-one nodes inherit the proved midpoint gates
from their eight actual level-two children. -/
theorem d2FlowCandidateStage6_actual_levelOne_inputs
    (h : Nat) (hh : 5 ≤ h) :
    let stageFour := d2FlowCandidateStage (h + 4) 4
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 4)
    let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
    ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 4) 6)
      (d2FlowCandidateRole (h + 4) 6)
      (d2FlowCandidateQuota (h + 4) 6)
      (fun q => d2FlowCandidateCapacity (h + 4) q 6) 1
      (d2FlowTreeChild stageFive j) := by
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4)
  let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
  change ∀ j, d2FlowStageInvInputs 8192
    (d2FlowCandidateActive (h + 4) 6)
    (d2FlowCandidateRole (h + 4) 6)
    (d2FlowCandidateQuota (h + 4) 6)
    (fun q => d2FlowCandidateCapacity (h + 4) q 6) 1
    (d2FlowTreeChild stageFive j)
  have hlevelTwo := d2FlowCandidateStage6_actual_levelTwo_inputs_closed h hh
  have hinactive1 : d2FlowCandidateActive (h + 4) 6 1 = false := by
    simp [d2FlowCandidateActive, tfD2]
  intro j
  cases htree : stageFive with
  | node G0 low0 high0 children0 =>
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (h + 4) 6)
        (d2FlowCandidateRole (h + 4) 6)
        (d2FlowCandidateQuota (h + 4) 6)
        (fun q => d2FlowCandidateCapacity (h + 4) q 6) 1 (children0 j)
      cases hchild : children0 j with
      | node G1 low1 high1 children1 =>
          simp only [d2FlowStageInvInputs, hinactive1, if_false]
          refine ⟨?_, trivial⟩
          intro k
          have hk := hlevelTwo j k
          change d2FlowStageInvInputs 8192
            (d2FlowCandidateActive (h + 4) 6)
            (d2FlowCandidateRole (h + 4) 6)
            (d2FlowCandidateQuota (h + 4) 6)
            (fun q => d2FlowCandidateCapacity (h + 4) q 6) 2
            (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) at hk
          rw [htree] at hk
          simp only [d2FlowTreeChild] at hk
          rw [hchild] at hk
          simpa [d2FlowTreeChild] using hk

set_option maxHeartbeats 10000000 in
/-- The actual stage-five output satisfies the complete stage-six recursive
input predicate. The root is zero from the bootstrap shape and stage-four
top-descending update; level one recurses into the proved middle gates. -/
theorem d2FlowCandidateStage6_actual_inputs
    (h : Nat) (hh : 5 ≤ h) :
    let stageFour := d2FlowCandidateStage (h + 4) 4
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 4)
    let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 4) 6)
      (d2FlowCandidateRole (h + 4) 6)
      (d2FlowCandidateQuota (h + 4) 6)
      (fun q => d2FlowCandidateCapacity (h + 4) q 6) 0 stageFive := by
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4)
  let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive (h + 4) 6)
    (d2FlowCandidateRole (h + 4) 6)
    (d2FlowCandidateQuota (h + 4) 6)
    (fun q => d2FlowCandidateCapacity (h + 4) q 6) 0 stageFive
  have hshape := d2FlowCandidateRun_stage3_shape h (by omega)
  have hfront4 := d2FlowCandidateStage4_frontiers (h + 2) (by omega)
  have hactive4root : d2FlowCandidateActive (h + 4) 4 0 = true := hfront4.1
  have hrole4root : d2FlowCandidateRole (h + 4) 4 0 = .topDesc := hfront4.2.1
  have hrootFour : d2FlowTreeRootDeficit stageFour = 0 := by
    change d2FlowTreeRootDeficit
      (d2FlowCandidateStage (h + 4) 4
        (d2FlowCandidateRun (h + 4)
          (d2FlowTreeInitial 8192 (h + 4)) 4)) = 0
    rw [hshape]
    unfold d2FlowCandidateStage
    rw [d2FlowStage_active_node_deficit
      (active := d2FlowCandidateActive (h + 4) 4)
      (role := d2FlowCandidateRole (h + 4) 4)
      (quota := d2FlowCandidateQuota (h + 4) 4)
      (h := h + 3) (i := 0) (G := 0) (low := 0) (high := 0)
      (children := fun j => d2FlowStage
        (d2FlowCandidateActive (h + 4) 3)
        (d2FlowCandidateRole (h + 4) 3)
        (d2FlowCandidateQuota (h + 4) 3) (h + 3) 1
        (d2FlowTreeSetRoot
          (d2FlowCandidateStage2_firstSenderSubtree (h + 2)) 0 0 0))
      hactive4root]
    simp [hrole4root]
  have hactive5root : d2FlowCandidateActive (h + 4) 5 0 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hrootFive : d2FlowTreeRootDeficit stageFive = 0 := by
    change d2FlowTreeRootDeficit
      (d2FlowCandidateStage (h + 4) 5 stageFour) = 0
    unfold d2FlowCandidateStage
    rw [d2FlowStage_root_deficit_of_inactive
      (active := d2FlowCandidateActive (h + 4) 5)
      (role := d2FlowCandidateRole (h + 4) 5)
      (quota := d2FlowCandidateQuota (h + 4) 5)
      stageFour hactive5root]
    exact hrootFour
  have hfront6 := d2FlowCandidateStage6_frontiers (h + 4) (by omega)
  rcases hfront6 with
    ⟨hactive6root, hrole6root, _, _, _, _, _⟩
  have hlevelOne := d2FlowCandidateStage6_actual_levelOne_inputs h hh
  have hinvFive := d2FlowCandidateStage5_preserves_inv h hh
  cases hnode : stageFive with
  | node G low high children =>
      have hG : G = 0 := by
        have hz := hrootFive
        rw [hnode] at hz
        exact hz
      have hInv := hinvFive
      change d2FlowTreeInv 8192 stageFive at hInv
      rw [hnode] at hInv
      simp only [d2FlowTreeInv] at hInv
      have hstrict : G < 8192 * 8 ^ (h + 4) := by
        rw [hG]
        positivity
      have hbalance : low + high = G := hInv.2.2.1 hstrict
      simp only [d2FlowStageInvInputs, hactive6root, if_true, hrole6root]
      refine ⟨?_, ⟨hbalance, hG⟩⟩
      intro j
      have hj := hlevelOne j
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (h + 4) 6)
        (d2FlowCandidateRole (h + 4) 6)
        (d2FlowCandidateQuota (h + 4) 6)
        (fun q => d2FlowCandidateCapacity (h + 4) q 6) 1
        (d2FlowTreeChild stageFive j) at hj
      rw [hnode] at hj
      simpa [d2FlowTreeChild] using hj

set_option maxHeartbeats 10000000 in
/-- The saturated-aware endpoint-reserve invariant now composes through the
first repeating stage on the actual whole-tree snapshot. -/
theorem d2FlowCandidateStage6_preserves_inv (h : Nat) (hh : 5 ≤ h) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 7) := by
  let stageFive := d2FlowCandidateStage (h + 4) 5
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 5)
  have hinvRun := d2FlowCandidateStage5_preserves_inv h hh
  have hinv : d2FlowTreeInv 8192 stageFive := by
    change d2FlowTreeInv 8192
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 6)
    exact hinvRun
  have hinputs := d2FlowCandidateStage6_actual_inputs h hh
  have hpres := d2FlowStage_preserves_inv_of_inputs
    (active := d2FlowCandidateActive (h + 4) 6)
    (role := d2FlowCandidateRole (h + 4) 6)
    (quota := d2FlowCandidateQuota (h + 4) 6)
    (cap := fun q => d2FlowCandidateCapacity (h + 4) q 6)
    (i := 0) stageFive hinv hinputs
  change d2FlowTreeInv 8192
    (d2FlowCandidateStage (h + 4) 6
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 6))
  simpa [d2FlowCandidateRun, d2FlowCandidateStage] using hpres

set_option maxHeartbeats 10000000 in
/-- The stage-six snapshot meets stage seven's local bottom-descending gate at
every actual level-three node. The mid parent supplies the sender cap and
balance; the carried stage-five boundary reserve supplies both endpoints and
enough aggregate child mass. -/
theorem d2FlowCandidateStage7_actual_levelThree_inputs
    (h : Nat) (hh : 5 ≤ h) :
    let stageFour := d2FlowCandidateStage (h + 4) 4
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 4)
    let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
    let stageSix := d2FlowCandidateStage (h + 4) 6 stageFive
    ∀ j k m, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 4) 7)
      (d2FlowCandidateRole (h + 4) 7)
      (d2FlowCandidateQuota (h + 4) 7)
      (fun q => d2FlowCandidateCapacity (h + 4) q 7) 3
      (d2FlowTreeChild
        (d2FlowTreeChild (d2FlowTreeChild stageSix j) k) m) := by
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4)
  let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
  let stageSix := d2FlowCandidateStage (h + 4) 6 stageFive
  change ∀ j k m, _
  have hinvFive := d2FlowCandidateStage5_preserves_inv h hh
  have hinputsSix := d2FlowCandidateStage6_actual_levelTwo_inputs_closed h hh
  have hfront6 := d2FlowCandidateStage6_frontiers (h + 4) (by omega)
  rcases hfront6 with ⟨_, _, hactive2, hrole2, _, _, _⟩
  have hfront7 := d2FlowCandidateStage7_frontiers (h + 4) (by omega)
  have hcap7 : d2FlowCandidateCapacity (h + 4) 3 7 =
      2 ^ (3 * (h + 4) + 4) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota5 : d2FlowCandidateQuota (h + 4) 5 3 .botDesc =
      15 * 2 ^ (3 * (h + 4) - 4) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hhalf5 : d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2 =
      15 * 2 ^ (3 * (h + 4) - 5) := by
    rw [hquota5, show 3 * (h + 4) - 4 =
      (3 * (h + 4) - 5) + 1 by omega, pow_succ]
    omega
  have hcapHalf : d2FlowCandidateCapacity (h + 4) 3 7 ≤
      128 * (d2FlowCandidateQuota (h + 4) 5 3 .botDesc / 2) := by
    rw [hcap7, hhalf5]
    have hp : 2 ^ (3 * (h + 4) + 4) =
        512 * 2 ^ (3 * (h + 4) - 5) := by
      rw [show 3 * (h + 4) + 4 =
        9 + (3 * (h + 4) - 5) by omega, pow_add]
      norm_num
    rw [hp]
    nlinarith
  have hcapRelation : 2 * d2FlowCandidateCapacity (h + 4) 2 6 =
      d2FlowCandidateCapacity (h + 4) 3 7 := by
    have hexp : d2FlowCandidateCapacityExponent (h + 4) 3 7 =
        d2FlowCandidateCapacityExponent (h + 4) 2 6 + 1 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    unfold d2FlowCandidateCapacity
    rw [hexp, Nat.pow_succ]
    omega
  intro j k m
  have hInvLevelTwo := d2FlowTreeInv_grandchild stageFive hinvFive j k
  have hInputsLevelTwo := hinputsSix j k
  cases hsource : d2FlowTreeChild (d2FlowTreeChild stageFive j) k with
  | node G2 low2 high2 children2 =>
      have hsourceInv := hInvLevelTwo
      change d2FlowTreeInv 8192
        (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) at hsourceInv
      rw [hsource] at hsourceInv
      have hsourceInputs := hInputsLevelTwo
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (h + 4) 6)
        (d2FlowCandidateRole (h + 4) 6)
        (d2FlowCandidateQuota (h + 4) 6)
        (fun q => d2FlowCandidateCapacity (h + 4) q 6) 2
        (d2FlowTreeChild (d2FlowTreeChild stageFive j) k) at hsourceInputs
      rw [hsource] at hsourceInputs
      have hchildCap := d2FlowStage_regular_child_g_bound_of_tree_inputs
        (.node G2 low2 high2 children2) hactive2
        (Or.inr (Or.inl hrole2)) hsourceInv hsourceInputs
      have hchildBalance := d2FlowStage_regular_child_balanced
        (active := d2FlowCandidateActive (h + 4) 6)
        (role := d2FlowCandidateRole (h + 4) 6)
        (quota := d2FlowCandidateQuota (h + 4) 6)
        (h := h + 1) (i := 2) (G := G2) (low := low2) (high := high2)
        children2 hactive2 (Or.inr (Or.inl hrole2)) m
      have hproject := d2FlowCandidateStage6_levelTwo_projection h hh j k
      have hnodeEq :
          d2FlowTreeChild (d2FlowTreeChild
            (d2FlowTreeChild stageSix j) k) m =
          d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive (h + 4) 6)
              (d2FlowCandidateRole (h + 4) 6)
              (d2FlowCandidateQuota (h + 4) 6) (h + 2) 2
              (d2FlowTreeChild (d2FlowTreeChild stageFive j) k)) m := by
        exact congrArg (fun t => d2FlowTreeChild t m) hproject
      rw [hsource] at hnodeEq
      have hchildNodeInv :
          512 * d2FlowTreeRootDeficit
            (d2FlowTreeChild (d2FlowTreeChild
              (d2FlowTreeChild stageSix j) k) m) ≤
            d2FlowCandidateCapacity (h + 4) 3 7 := by
        have hb := hchildCap m
        rw [hnodeEq, ← hcapRelation]
        exact hb
      have hbalanceData :
          (d2FlowTreeRootData
            (d2FlowTreeChild (d2FlowStage
              (d2FlowCandidateActive (h + 4) 6)
              (d2FlowCandidateRole (h + 4) 6)
              (d2FlowCandidateQuota (h + 4) 6) (h + 2) 2
              (.node G2 low2 high2 children2)) m)).2.1 +
          (d2FlowTreeRootData
            (d2FlowTreeChild (d2FlowStage
              (d2FlowCandidateActive (h + 4) 6)
              (d2FlowCandidateRole (h + 4) 6)
              (d2FlowCandidateQuota (h + 4) 6) (h + 2) 2
              (.node G2 low2 high2 children2)) m)).2.2 =
          d2FlowTreeRootDeficit
            (d2FlowTreeChild (d2FlowStage
              (d2FlowCandidateActive (h + 4) 6)
              (d2FlowCandidateRole (h + 4) 6)
              (d2FlowCandidateQuota (h + 4) 6) (h + 2) 2
              (.node G2 low2 high2 children2)) m) := by
        exact hchildBalance
      have hreserves := d2FlowCandidateStage6_endpoint_reserves h hh j k m
      cases hactual : d2FlowTreeChild
          (d2FlowTreeChild (d2FlowTreeChild stageSix j) k) m with
      | node G low high children3 =>
          have hbalanceActual :
              (d2FlowTreeRootData
                (d2FlowTreeChild (d2FlowTreeChild
                  (d2FlowTreeChild stageSix j) k) m)).2.1 +
              (d2FlowTreeRootData
                (d2FlowTreeChild (d2FlowTreeChild
                  (d2FlowTreeChild stageSix j) k) m)).2.2 =
              d2FlowTreeRootDeficit
                (d2FlowTreeChild (d2FlowTreeChild
                  (d2FlowTreeChild stageSix j) k) m) := by
            rw [hnodeEq]
            exact hbalanceData
          have hbalance : low + high = G := by
            simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit, hactual]
              using hbalanceActual
          have hG : 512 * G ≤ d2FlowCandidateCapacity (h + 4) 3 7 := by
            simpa [d2FlowTreeRootDeficit, hactual] using hchildNodeInv
          have hleft : d2FlowCandidateCapacity (h + 4) 3 7 ≤
              128 * d2FlowTreeRootDeficit (children3 ⟨0, by omega⟩) := by
            have hr := hreserves.1
            rw [hactual] at hr
            simp only [d2FlowTreeChild] at hr
            simpa [hhalf5] using
              Nat.le_trans hcapHalf (Nat.mul_le_mul_left 128 hr)
          have hright : d2FlowCandidateCapacity (h + 4) 3 7 ≤
              128 * d2FlowTreeRootDeficit (children3 ⟨7, by omega⟩) := by
            have hr := hreserves.2
            rw [hactual] at hr
            simp only [d2FlowTreeChild] at hr
            simpa [hhalf5] using
              Nat.le_trans hcapHalf (Nat.mul_le_mul_left 128 hr)
          have htotal := d2FlowCandidateStage7_boundary_mass_suffices
            (h + 4) (by omega) G hG children3 hleft
          exact d2FlowCandidateStage7_botDesc_inputs
            (h + 4) (by omega) G low high hbalance hG children3
            hleft hright htotal

set_option maxHeartbeats 10000000 in
/-- The actual stage-six output satisfies every inactive stage-seven
level-two input gate by recursively exposing the proved level-three senders. -/
theorem d2FlowCandidateStage7_actual_levelTwo_inputs
    (h : Nat) (hh : 5 ≤ h) :
    let stageFour := d2FlowCandidateStage (h + 4) 4
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 4)
    let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
    let stageSix := d2FlowCandidateStage (h + 4) 6 stageFive
    ∀ j k, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 4) 7)
      (d2FlowCandidateRole (h + 4) 7)
      (d2FlowCandidateQuota (h + 4) 7)
      (fun q => d2FlowCandidateCapacity (h + 4) q 7) 2
      (d2FlowTreeChild (d2FlowTreeChild stageSix j) k) := by
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4)
  let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
  let stageSix := d2FlowCandidateStage (h + 4) 6 stageFive
  change ∀ j k, _
  have hinactive2 : d2FlowCandidateActive (h + 4) 7 2 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hlevelThree := d2FlowCandidateStage7_actual_levelThree_inputs h hh
  intro j k
  let levelTwo := d2FlowTreeChild (d2FlowTreeChild stageSix j) k
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive (h + 4) 7)
    (d2FlowCandidateRole (h + 4) 7)
    (d2FlowCandidateQuota (h + 4) 7)
    (fun q => d2FlowCandidateCapacity (h + 4) q 7) 2 levelTwo
  cases hnode : levelTwo with
  | node G low high children =>
      simp only [d2FlowStageInvInputs, hinactive2, if_false]
      refine ⟨?_, trivial⟩
      intro m
      have hchild := hlevelThree j k m
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (h + 4) 7)
        (d2FlowCandidateRole (h + 4) 7)
        (d2FlowCandidateQuota (h + 4) 7)
        (fun q => d2FlowCandidateCapacity (h + 4) q 7) 3
        (d2FlowTreeChild levelTwo m) at hchild
      rw [hnode] at hchild
      simpa [d2FlowTreeChild] using hchild

set_option maxHeartbeats 10000000 in
/-- Every actual stage-six level-one child has zero parent data from the
top-descending root and receives the eight level-two `mid` increments needed
by stage seven's `topRise` gate. -/
theorem d2FlowCandidateStage7_actual_levelOne_inputs
    (h : Nat) (hh : 5 ≤ h) :
    let stageFour := d2FlowCandidateStage (h + 4) 4
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 4)
    let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
    let stageSix := d2FlowCandidateStage (h + 4) 6 stageFive
    ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 4) 7)
      (d2FlowCandidateRole (h + 4) 7)
      (d2FlowCandidateQuota (h + 4) 7)
      (fun q => d2FlowCandidateCapacity (h + 4) q 7) 1
      (d2FlowTreeChild stageSix j) := by
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4)
  let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
  let stageSix := d2FlowCandidateStage (h + 4) 6 stageFive
  change ∀ j, _
  have hfront6 := d2FlowCandidateStage6_frontiers (h + 4) (by omega)
  rcases hfront6 with
    ⟨hactive0, hrole0, hactive2, hrole2, _, _, _⟩
  have hfront7 := d2FlowCandidateStage7_frontiers (h + 4) (by omega)
  rcases hfront7 with ⟨hactive1, hrole1, _, _, _⟩
  have hrec := d2FlowCandidateStage7_actual_levelTwo_inputs h hh
  intro j
  cases hroot : stageFive with
  | node G0 low0 high0 children0 =>
      have hdata : d2FlowTreeRootData
          (d2FlowTreeChild stageSix j) = (0, 0, 0) := by
        change d2FlowTreeRootData
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive (h + 4) 6)
              (d2FlowCandidateRole (h + 4) 6)
              (d2FlowCandidateQuota (h + 4) 6) (h + 4) 0 stageFive) j) = _
        rw [hroot]
        exact d2FlowStage_topDesc_child_rootdata
          (active := d2FlowCandidateActive (h + 4) 6)
          (role := d2FlowCandidateRole (h + 4) 6)
          (quota := d2FlowCandidateQuota (h + 4) 6)
          (h := h + 3) (i := 0) (G := G0) (low := low0)
          (high := high0) children0 hactive0 hrole0 j
      cases hchild : d2FlowTreeChild stageSix j with
      | node G1 low1 high1 children1 =>
          have hdata' := hdata
          rw [hchild] at hdata'
          simp only [d2FlowTreeRootData] at hdata'
          have hG0 : G1 = 0 := by
            exact congrArg Prod.fst hdata'
          have hLow0 : low1 = 0 := by
            exact congrArg (fun p : Nat × Nat × Nat => p.2.1) hdata'
          have hHigh0 : high1 = 0 := by
            exact congrArg (fun p : Nat × Nat × Nat => p.2.2) hdata'
          have hbalance : low1 + high1 = 0 := by omega
          have hchildren : ∀ k : Fin 8,
              d2FlowCandidateQuota (h + 4) 6 2 .mid ≤
                d2FlowTreeRootDeficit (children1 k) := by
            intro k
            have hproject := d2FlowCandidateStage6_levelTwo_projection h hh j k
            have hrootQuota :
                d2FlowCandidateQuota (h + 4) 6 2 .mid ≤
                  d2FlowTreeRootDeficit
                    (d2FlowStage (d2FlowCandidateActive (h + 4) 6)
                      (d2FlowCandidateRole (h + 4) 6)
                      (d2FlowCandidateQuota (h + 4) 6) (h + 2) 2
                      (d2FlowTreeChild (d2FlowTreeChild stageFive j) k)) := by
              cases hsource : d2FlowTreeChild
                  (d2FlowTreeChild stageFive j) k with
              | node G2 low2 high2 grandchildren =>
                  have hrootEq :
                      d2FlowTreeRootDeficit
                        (d2FlowStage (d2FlowCandidateActive (h + 4) 6)
                          (d2FlowCandidateRole (h + 4) 6)
                          (d2FlowCandidateQuota (h + 4) 6) (h + 2) 2
                          (.node G2 low2 high2 grandchildren)) =
                        G2 + d2FlowCandidateQuota (h + 4) 6 2 .mid := by
                    simpa [Nat.add_assoc, hrole2] using
                      (d2FlowStage_active_node_deficit
                        (active := d2FlowCandidateActive (h + 4) 6)
                        (role := d2FlowCandidateRole (h + 4) 6)
                        (quota := d2FlowCandidateQuota (h + 4) 6)
                        (h := h + 1) (i := 2) (G := G2)
                        (low := low2) (high := high2) grandchildren hactive2)
                  omega
            have hactualQuota := hrootQuota
            rw [← hproject] at hactualQuota
            rw [hchild] at hactualQuota
            simpa [d2FlowTreeChild] using hactualQuota
          have hrecursive : ∀ k : Fin 8,
              d2FlowStageInvInputs 8192
                (d2FlowCandidateActive (h + 4) 7)
                (d2FlowCandidateRole (h + 4) 7)
                (d2FlowCandidateQuota (h + 4) 7)
                (fun q => d2FlowCandidateCapacity (h + 4) q 7) 2
                (children1 k) := by
            intro k
            have hk := hrec j k
            change d2FlowStageInvInputs 8192
              (d2FlowCandidateActive (h + 4) 7)
              (d2FlowCandidateRole (h + 4) 7)
              (d2FlowCandidateQuota (h + 4) 7)
              (fun q => d2FlowCandidateCapacity (h + 4) q 7) 2
              (d2FlowTreeChild (d2FlowTreeChild stageSix j) k) at hk
            rw [hchild] at hk
            simpa [d2FlowTreeChild] using hk
          have htop := d2FlowCandidateStage7_topRise_inputs
            (h + 4) (by omega) low1 high1 hbalance children1
            hchildren hrecursive
          simpa [hchild, hG0, hLow0, hHigh0] using htop

set_option maxHeartbeats 10000000 in
/-- The complete recursive input predicate for stage seven holds on the
actual stage-six snapshot: the root is inactive and every level-one child has
the checked top-rise gate. -/
theorem d2FlowCandidateStage7_actual_inputs
    (h : Nat) (hh : 5 ≤ h) :
    let stageFour := d2FlowCandidateStage (h + 4) 4
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 4)
    let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
    let stageSix := d2FlowCandidateStage (h + 4) 6 stageFive
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 4) 7)
      (d2FlowCandidateRole (h + 4) 7)
      (d2FlowCandidateQuota (h + 4) 7)
      (fun q => d2FlowCandidateCapacity (h + 4) q 7) 0 stageSix := by
  let stageFour := d2FlowCandidateStage (h + 4) 4
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 4)
  let stageFive := d2FlowCandidateStage (h + 4) 5 stageFour
  let stageSix := d2FlowCandidateStage (h + 4) 6 stageFive
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive (h + 4) 7)
    (d2FlowCandidateRole (h + 4) 7)
    (d2FlowCandidateQuota (h + 4) 7)
    (fun q => d2FlowCandidateCapacity (h + 4) q 7) 0 stageSix
  have hinactive0 : d2FlowCandidateActive (h + 4) 7 0 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hlevelOne := d2FlowCandidateStage7_actual_levelOne_inputs h hh
  cases hroot : stageSix with
  | node G low high children =>
      simp only [d2FlowStageInvInputs, hinactive0, if_false]
      refine ⟨?_, trivial⟩
      intro j
      have hj := hlevelOne j
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (h + 4) 7)
        (d2FlowCandidateRole (h + 4) 7)
        (d2FlowCandidateQuota (h + 4) 7)
        (fun q => d2FlowCandidateCapacity (h + 4) q 7) 1
        (d2FlowTreeChild stageSix j) at hj
      rw [hroot] at hj
      simpa [d2FlowTreeChild] using hj

set_option maxHeartbeats 10000000 in
/-- One full additional stage of the candidate schedule preserves the
saturated-aware tree invariant, now with the whole stage-seven gate checked. -/
theorem d2FlowCandidateStage7_preserves_inv (h : Nat) (hh : 5 ≤ h) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 8) := by
  let stageSix := d2FlowCandidateStage (h + 4) 6
    (d2FlowCandidateRun (h + 4)
      (d2FlowTreeInitial 8192 (h + 4)) 6)
  have hinvRun := d2FlowCandidateStage6_preserves_inv h hh
  have hinv : d2FlowTreeInv 8192 stageSix := by
    change d2FlowTreeInv 8192
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 7)
    exact hinvRun
  have hinputs := d2FlowCandidateStage7_actual_inputs h hh
  have hpres := d2FlowStage_preserves_inv_of_inputs
    (active := d2FlowCandidateActive (h + 4) 7)
    (role := d2FlowCandidateRole (h + 4) 7)
    (quota := d2FlowCandidateQuota (h + 4) 7)
    (cap := fun q => d2FlowCandidateCapacity (h + 4) q 7)
    (i := 0) stageSix hinv hinputs
  change d2FlowTreeInv 8192
    (d2FlowCandidateStage (h + 4) 7
      (d2FlowCandidateRun (h + 4)
        (d2FlowTreeInitial 8192 (h + 4)) 7))
  simpa [d2FlowCandidateRun, d2FlowCandidateStage] using hpres

set_option maxHeartbeats 10000000 in
/-- The actual stage-seven output meets every stage-eight level-four
bottom-descending input gate. Its parent cap and balance come from stage seven;
the level-five endpoint reserves are the transported native reserves. -/
theorem d2FlowCandidateStage8_actual_levelFour_inputs
    (h : Nat) (hh : 5 ≤ h) :
    ∀ j k m l, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 5) 8)
      (d2FlowCandidateRole (h + 5) 8)
      (d2FlowCandidateQuota (h + 5) 8)
      (fun q => d2FlowCandidateCapacity (h + 5) q 8) 4
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateRun (h + 5)
                (d2FlowTreeInitial 8192 (h + 5)) 8) j) k) m) l) := by
  intro j k m l
  let stageSix := d2FlowCandidateRun (h + 5)
    (d2FlowTreeInitial 8192 (h + 5)) 7
  let stageSeven := d2FlowCandidateStage (h + 5) 7 stageSix
  let levelTwo := d2FlowTreeChild (d2FlowTreeChild stageSix j) k
  let levelThree := d2FlowTreeChild levelTwo m
  let levelFour := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild stageSeven j) k) m) l
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive (h + 5) 8)
    (d2FlowCandidateRole (h + 5) 8)
    (d2FlowCandidateQuota (h + 5) 8)
    (fun q => d2FlowCandidateCapacity (h + 5) q 8) 4 levelFour
  have hInvGlobal := d2FlowCandidateStage6_preserves_inv (h + 1) (by omega)
  have hInvTwo := d2FlowTreeInv_grandchild
    (h := h + 3) stageSix hInvGlobal j k
  have hinputs := d2FlowCandidateStage7_actual_levelThree_inputs
    (h + 1) (by omega) j k m
  have hfront7 := d2FlowCandidateStage7_frontiers (h + 5) (by omega)
  rcases hfront7 with ⟨_, _, hactive3, hrole3, _⟩
  have hexpRelation : d2FlowCandidateCapacityExponent (h + 5) 4 8 =
      d2FlowCandidateCapacityExponent (h + 5) 3 7 + 1 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  have hcapRelation : 2 * d2FlowCandidateCapacity (h + 5) 3 7 =
      d2FlowCandidateCapacity (h + 5) 4 8 := by
    unfold d2FlowCandidateCapacity
    rw [hexpRelation, Nat.pow_succ]
    omega
  have hproject := d2FlowStage_path4_projection
    (active := d2FlowCandidateActive (h + 5) 7)
    (role := d2FlowCandidateRole (h + 5) 7)
    (quota := d2FlowCandidateQuota (h + 5) 7)
    (i := 0) stageSix j k m l
  have hproject' : levelFour = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive (h + 5) 7)
        (d2FlowCandidateRole (h + 5) 7)
        (d2FlowCandidateQuota (h + 5) 7) (h + 2) 3 levelThree) l := by
    simpa [levelFour, stageSeven, d2FlowCandidateStage,
      d2FlowCandidateRun, levelThree, levelTwo] using hproject
  have hcapNative := d2FlowCandidateStage8_capacity_eq_native h
  cases htwo : levelTwo with
  | node G2 low2 high2 children2 =>
      have hInvTwo' := hInvTwo
      change d2FlowTreeInv 8192 levelTwo at hInvTwo'
      rw [htwo] at hInvTwo'
      simp only [d2FlowTreeInv] at hInvTwo'
      have hInvThree := hInvTwo'.2.2.2 m
      cases hthree : levelThree with
      | node G3 low3 high3 children3 =>
          have hthree' : d2FlowTreeChild (D2FlowTree.node G2 low2 high2 children2) m =
              .node G3 low3 high3 children3 := by
            simpa [levelThree, htwo] using hthree
          have hthree'' : children2 m = .node G3 low3 high3 children3 := by
            simpa only [d2FlowTreeChild] using hthree'
          have hInvThree' : d2FlowTreeInv 8192
              (.node G3 low3 high3 children3) := by
            rw [hthree''] at hInvThree
            exact hInvThree
          have hinputs' := hinputs
          change d2FlowStageInvInputs 8192
            (d2FlowCandidateActive (h + 5) 7)
            (d2FlowCandidateRole (h + 5) 7)
            (d2FlowCandidateQuota (h + 5) 7)
            (fun q => d2FlowCandidateCapacity (h + 5) q 7) 3 levelThree
            at hinputs'
          rw [hthree] at hinputs'
          have hchildCap := d2FlowStage_regular_child_g_bound_of_tree_inputs
            (active := d2FlowCandidateActive (h + 5) 7)
            (role := d2FlowCandidateRole (h + 5) 7)
            (quota := d2FlowCandidateQuota (h + 5) 7)
            (cap := fun q => d2FlowCandidateCapacity (h + 5) q 7)
            (.node G3 low3 high3 children3) hactive3
            (Or.inr (Or.inr hrole3)) hInvThree' hinputs'
          have hchildBalanced := d2FlowStage_regular_child_balanced
            (active := d2FlowCandidateActive (h + 5) 7)
            (role := d2FlowCandidateRole (h + 5) 7)
            (quota := d2FlowCandidateQuota (h + 5) 7)
            (h := h + 1) (i := 3) (G := G3) (low := low3) (high := high3)
            children3 hactive3 (Or.inr (Or.inr hrole3)) l
          have hproject'' := hproject'
          rw [hthree] at hproject''
          have hGout : 512 * d2FlowTreeRootDeficit levelFour ≤
              d2FlowCandidateCapacity (h + 5) 4 8 := by
            rw [hproject'']
            rw [← hcapRelation]
            exact hchildCap l
          have hbalanceOut : (d2FlowTreeRootData levelFour).2.1 +
              (d2FlowTreeRootData levelFour).2.2 =
            d2FlowTreeRootDeficit levelFour := by
            rw [hproject'']
            exact hchildBalanced
          cases hnode : levelFour with
          | node G low high children =>
              have hbalance : low + high = G := by
                have hb := hbalanceOut
                rw [hnode] at hb
                simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hb
              have hG : 512 * G ≤ d2FlowCandidateCapacity (h + 5) 4 8 := by
                have hg := hGout
                rw [hnode] at hg
                simpa [d2FlowTreeRootDeficit] using hg
              have hreserve0 : d2FlowTreeRootDeficit
                  (children ⟨0, by omega⟩) = 8192 * 8 ^ h := by
                have hr := d2FlowCandidateStage7_actual_levelFive_native
                  h hh j k m l ⟨0, by omega⟩
                change d2FlowTreeRootDeficit
                  (d2FlowTreeChild levelFour ⟨0, by omega⟩) =
                  8192 * 8 ^ h at hr
                rw [hnode] at hr
                simpa only [d2FlowTreeChild] using hr
              have hreserve7 : d2FlowTreeRootDeficit
                  (children ⟨7, by omega⟩) = 8192 * 8 ^ h := by
                have hr := d2FlowCandidateStage7_actual_levelFive_native
                  h hh j k m l ⟨7, by omega⟩
                change d2FlowTreeRootDeficit
                  (d2FlowTreeChild levelFour ⟨7, by omega⟩) =
                  8192 * 8 ^ h at hr
                rw [hnode] at hr
                simpa only [d2FlowTreeChild] using hr
              have hleft : d2FlowCandidateCapacity (h + 5) 4 8 ≤
                  128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
                rw [hcapNative, hreserve0]
              have hright : d2FlowCandidateCapacity (h + 5) 4 8 ≤
                  128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩) := by
                rw [hcapNative, hreserve7]
              have htotal := d2FlowCandidateStage8_boundary_mass_suffices
                (h + 5) (by omega) G hG children hleft
              have hgate := d2FlowCandidateStage8_botDesc_inputs
                (h + 5) (by omega) G low high hbalance hG children
                hleft hright htotal
              exact hgate

set_option maxHeartbeats 10000000 in
/-- The actual stage-seven output meets every stage-eight level-two mid gate.
The cap and balance descend from stage seven's level-one top-rise sender; its
level-three bottom-descending children have already added enough reserve. -/
theorem d2FlowCandidateStage8_actual_levelTwo_inputs
    (h : Nat) (hh : 5 ≤ h) :
    ∀ j k, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 5) 8)
      (d2FlowCandidateRole (h + 5) 8)
      (d2FlowCandidateQuota (h + 5) 8)
      (fun q => d2FlowCandidateCapacity (h + 5) q 8) 2
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun (h + 5)
            (d2FlowTreeInitial 8192 (h + 5)) 8) j) k) := by
  intro j k
  let stageSix := d2FlowCandidateRun (h + 5)
    (d2FlowTreeInitial 8192 (h + 5)) 7
  let stageSeven := d2FlowCandidateStage (h + 5) 7 stageSix
  let levelOne := d2FlowTreeChild stageSix j
  let levelTwoOut := d2FlowTreeChild (d2FlowTreeChild stageSeven j) k
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive (h + 5) 8)
    (d2FlowCandidateRole (h + 5) 8)
    (d2FlowCandidateQuota (h + 5) 8)
    (fun q => d2FlowCandidateCapacity (h + 5) q 8) 2 levelTwoOut
  have hInvGlobal := d2FlowCandidateStage6_preserves_inv (h + 1) (by omega)
  have hinputsOne := d2FlowCandidateStage7_actual_levelOne_inputs
    (h + 1) (by omega) j
  have hinputsThree := d2FlowCandidateStage7_actual_levelThree_inputs
    (h + 1) (by omega)
  have hfront7 := d2FlowCandidateStage7_frontiers (h + 5) (by omega)
  rcases hfront7 with ⟨hactive1, hrole1, _, _, _⟩
  have hfront7Bottom := d2FlowCandidateStage7_frontiers (h + 5) (by omega)
  rcases hfront7Bottom with ⟨_, _, hactive3, hrole3, _⟩
  have hactive0 : d2FlowCandidateActive (h + 5) 7 0 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hinactive2 : d2FlowCandidateActive (h + 5) 7 2 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hactive3Eight : d2FlowCandidateActive (h + 5) 8 3 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hcapExponentRelation :
      d2FlowCandidateCapacityExponent (h + 5) 2 8 =
        d2FlowCandidateCapacityExponent (h + 5) 1 7 + 1 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  have hcapRelation : 2 * d2FlowCandidateCapacity (h + 5) 1 7 =
      d2FlowCandidateCapacity (h + 5) 2 8 := by
    unfold d2FlowCandidateCapacity
    rw [hcapExponentRelation, Nat.pow_succ]
    omega
  have hquota7 : d2FlowCandidateQuota (h + 5) 7 3 .botDesc =
      15 * 2 ^ (3 * (h + 5) - 8) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hcapNative : d2FlowCandidateCapacity (h + 5) 2 8 =
      2 ^ (3 * (h + 5) - 1) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquotaReserve : d2FlowCandidateCapacity (h + 5) 2 8 ≤
      128 * d2FlowCandidateQuota (h + 5) 7 3 .botDesc := by
    rw [hcapNative, hquota7]
    have hp : 128 * 2 ^ (3 * (h + 5) - 8) =
        2 ^ (3 * (h + 5) - 1) := by
      rw [show (128 : Nat) = 2 ^ 7 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith [hp]
  have hprojectTwo := d2FlowStage_child_child_projection
    (active := d2FlowCandidateActive (h + 5) 7)
    (role := d2FlowCandidateRole (h + 5) 7)
    (quota := d2FlowCandidateQuota (h + 5) 7)
    (i := 0) stageSix j k
  have hprojectTwo' : levelTwoOut = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive (h + 5) 7)
        (d2FlowCandidateRole (h + 5) 7)
        (d2FlowCandidateQuota (h + 5) 7) (h + 4) 1 levelOne) k := by
    simpa [levelTwoOut, stageSeven, d2FlowCandidateStage] using hprojectTwo
  have hrootProjection : d2FlowTreeChild stageSeven j =
      d2FlowStage (d2FlowCandidateActive (h + 5) 7)
        (d2FlowCandidateRole (h + 5) 7)
        (d2FlowCandidateQuota (h + 5) 7) (h + 4) 1 levelOne := by
    cases hroot : stageSix with
    | node G0 low0 high0 children0 =>
        have hp := d2FlowStage_inactive_child
          (active := d2FlowCandidateActive (h + 5) 7)
          (role := d2FlowCandidateRole (h + 5) 7)
          (quota := d2FlowCandidateQuota (h + 5) 7)
          (h := h + 4) (i := 0) (G := G0) (low := low0) (high := high0)
          children0 hactive0 j
        simpa [stageSeven, d2FlowCandidateStage, levelOne, hroot] using hp
  cases hroot : stageSix with
  | node G0 low0 high0 children0 =>
      have hInvRoot : d2FlowTreeInv 8192 stageSix := by
        simpa [stageSix] using hInvGlobal
      rw [hroot] at hInvRoot
      simp only [d2FlowTreeInv] at hInvRoot
      have hInvOne := hInvRoot.2.2.2 j
      cases hone : levelOne with
      | node G1 low1 high1 children1 =>
          have hInvOne' : d2FlowTreeInv 8192
              (.node G1 low1 high1 children1) := by
            rw [← hone]
            have hlevelOne : levelOne = children0 j := by
              simp [levelOne, hroot, d2FlowTreeChild]
            rw [hlevelOne]
            exact hInvOne
          have hinputsOne' := hinputsOne
          change d2FlowStageInvInputs 8192
            (d2FlowCandidateActive (h + 5) 7)
            (d2FlowCandidateRole (h + 5) 7)
            (d2FlowCandidateQuota (h + 5) 7)
            (fun q => d2FlowCandidateCapacity (h + 5) q 7) 1 levelOne
            at hinputsOne'
          rw [hone] at hinputsOne'
          have hchildCap := d2FlowStage_regular_child_g_bound_of_tree_inputs
            (active := d2FlowCandidateActive (h + 5) 7)
            (role := d2FlowCandidateRole (h + 5) 7)
            (quota := d2FlowCandidateQuota (h + 5) 7)
            (cap := fun q => d2FlowCandidateCapacity (h + 5) q 7)
            (.node G1 low1 high1 children1) hactive1
            (Or.inl hrole1) hInvOne' hinputsOne'
          have hchildBalanced := d2FlowStage_regular_child_balanced
            (active := d2FlowCandidateActive (h + 5) 7)
            (role := d2FlowCandidateRole (h + 5) 7)
            (quota := d2FlowCandidateQuota (h + 5) 7)
            (h := h + 3) (i := 1) (G := G1) (low := low1) (high := high1)
            children1 hactive1 (Or.inl hrole1) k
          have hGout : 512 * d2FlowTreeRootDeficit levelTwoOut ≤
              d2FlowCandidateCapacity (h + 5) 2 8 := by
            rw [hprojectTwo', hone]
            rw [← hcapRelation]
            simpa using hchildCap k
          have hbalanceOut : (d2FlowTreeRootData levelTwoOut).2.1 +
              (d2FlowTreeRootData levelTwoOut).2.2 =
            d2FlowTreeRootDeficit levelTwoOut := by
            rw [hprojectTwo', hone]
            exact hchildBalanced
          cases hnodeTwo : levelTwoOut with
          | node G2 low2 high2 children2 =>
              have hbalance : low2 + high2 = G2 := by
                have hb := hbalanceOut
                rw [hnodeTwo] at hb
                simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hb
              have hG : 512 * G2 ≤ d2FlowCandidateCapacity (h + 5) 2 8 := by
                have hg := hGout
                rw [hnodeTwo] at hg
                simpa [d2FlowTreeRootDeficit] using hg
              have hrecursive : ∀ q, d2FlowStageInvInputs 8192
                  (d2FlowCandidateActive (h + 5) 8)
                  (d2FlowCandidateRole (h + 5) 8)
                  (d2FlowCandidateQuota (h + 5) 8)
                  (fun n => d2FlowCandidateCapacity (h + 5) n 8) 3
                  (children2 q) := by
                intro q
                cases hchildThree : children2 q with
                | node G3 low3 high3 children3 =>
                    have hlevelThree : d2FlowTreeChild levelTwoOut q =
                        .node G3 low3 high3 children3 := by
                      rw [hnodeTwo]
                      simpa only [d2FlowTreeChild] using hchildThree
                    constructor
                    · intro s
                      have hlevelFour :=
                        d2FlowCandidateStage8_actual_levelFour_inputs h hh j k q s
                      change d2FlowStageInvInputs 8192
                        (d2FlowCandidateActive (h + 5) 8)
                        (d2FlowCandidateRole (h + 5) 8)
                        (d2FlowCandidateQuota (h + 5) 8)
                        (fun n => d2FlowCandidateCapacity (h + 5) n 8) 4
                        (d2FlowTreeChild
                          (d2FlowTreeChild
                            (d2FlowTreeChild
                              (d2FlowTreeChild stageSeven j) k) q) s)
                        at hlevelFour
                      rw [show d2FlowTreeChild
                          (d2FlowTreeChild
                            (d2FlowTreeChild stageSeven j) k) q =
                              d2FlowTreeChild levelTwoOut q by rfl] at hlevelFour
                      rw [hlevelThree] at hlevelFour
                      exact hlevelFour
                    · simp [d2FlowStageInvInputs, hactive3Eight]
              have hrootOutput (q : Fin 8) :
                  d2FlowCandidateQuota (h + 5) 7 3 .botDesc ≤
                    d2FlowTreeRootDeficit (d2FlowTreeChild levelTwoOut q) := by
                let sourceThree := d2FlowTreeChild
                  (d2FlowTreeChild (.node G1 low1 high1 children1) k) q
                have hinputsThree := hinputsThree j k q
                have hlocalProjection :=
                  d2FlowStage_child_child_of_inactive
                    (active := d2FlowCandidateActive (h + 5) 7)
                    (role := d2FlowCandidateRole (h + 5) 7)
                    (quota := d2FlowCandidateQuota (h + 5) 7)
                    (h := h + 2) (i := 1)
                    (G := G1) (low := low1) (high := high1)
                    children1 hinactive2 k q
                have hprojectThree : d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowTreeChild stageSeven j) k) q =
                    d2FlowStage (d2FlowCandidateActive (h + 5) 7)
                      (d2FlowCandidateRole (h + 5) 7)
                      (d2FlowCandidateQuota (h + 5) 7) (h + 2) 3
                      sourceThree := by
                  have hp := congrArg
                    (fun t => d2FlowTreeChild (d2FlowTreeChild t k) q)
                    hrootProjection
                  rw [hone] at hp
                  simpa [sourceThree] using hp.trans hlocalProjection
                cases hsource : sourceThree with
                | node G3 low3 high3 children3 =>
                    have hrootStep := d2FlowStage_active_node_deficit
                      (active := d2FlowCandidateActive (h + 5) 7)
                      (role := d2FlowCandidateRole (h + 5) 7)
                      (quota := d2FlowCandidateQuota (h + 5) 7)
                      (h := h + 1) (i := 3) (G := G3)
                      (low := low3) (high := high3) children3 hactive3
                    have hrootStep' : d2FlowTreeRootDeficit
                        (d2FlowStage (d2FlowCandidateActive (h + 5) 7)
                          (d2FlowCandidateRole (h + 5) 7)
                          (d2FlowCandidateQuota (h + 5) 7) (h + 2) 3
                          (.node G3 low3 high3 children3)) =
                      G3 + d2FlowCandidateQuota (h + 5) 7 3 .botDesc := by
                      simpa [hrole3] using hrootStep
                    have hlocalProjection' :
                        d2FlowTreeChild
                            (d2FlowTreeChild
                              (d2FlowStage (d2FlowCandidateActive (h + 5) 7)
                                (d2FlowCandidateRole (h + 5) 7)
                                (d2FlowCandidateQuota (h + 5) 7)
                                (h + 4) 1 levelOne) k) q =
                          d2FlowStage (d2FlowCandidateActive (h + 5) 7)
                            (d2FlowCandidateRole (h + 5) 7)
                            (d2FlowCandidateQuota (h + 5) 7)
                            (h + 2) 3 (.node G3 low3 high3 children3) := by
                      rw [← hrootProjection]
                      have hp := hprojectThree
                      rw [hsource] at hp
                      exact hp
                    rw [hprojectTwo', hlocalProjection']
                    rw [hrootStep']
                    omega
              have hleft : d2FlowCandidateCapacity (h + 5) 2 8 ≤
                  128 * d2FlowTreeRootDeficit
                    (children2 ⟨0, by omega⟩) := by
                have hout := hrootOutput ⟨0, by omega⟩
                rw [hnodeTwo] at hout
                simpa only [d2FlowTreeChild] using
                  Nat.le_trans hquotaReserve
                    (Nat.mul_le_mul_left 128 hout)
              have hright : d2FlowCandidateCapacity (h + 5) 2 8 ≤
                  128 * d2FlowTreeRootDeficit
                    (children2 ⟨7, by omega⟩) := by
                have hout := hrootOutput ⟨7, by omega⟩
                rw [hnodeTwo] at hout
                simpa only [d2FlowTreeChild] using
                  Nat.le_trans hquotaReserve
                    (Nat.mul_le_mul_left 128 hout)
              have htotal := d2FlowCandidateStage8_mid_boundary_mass_suffices
                (h + 5) (by omega) G2 hG children2 hleft
              have hgate := d2FlowCandidateStage8_mid_inputs
                (h + 5) (by omega) G2 low2 high2 hbalance hG children2
                hrecursive hleft hright htotal
              exact hgate

/-- During the first eight stages, the root is either inactive or a
top-descending sender. Thus its initially zero deficit remains zero. -/
theorem d2FlowCandidateStage8_root_zero (h : Nat) (hh : 5 ≤ h) :
    d2FlowTreeRootDeficit
      (d2FlowCandidateRun (h + 5)
        (d2FlowTreeInitial 8192 (h + 5)) 8) = 0 := by
  let d := h + 5
  have hd : 10 ≤ d := by dsimp [d]; omega
  have hAlpha : ∀ t ≤ 8, alpha d t = t % 2 := by
    intro t ht
    interval_cases t
    · simp [alpha]
    · simp [alpha]
    · simp [alpha, alphaStar, ceilParity,
        show 15 ≤ 3 * d by omega]
    · simp [alpha, alphaStar, ceilParity,
        show 17 ≤ 3 * d by omega]
    · simp [alpha, alphaStar, ceilParity,
        show 19 ≤ 3 * d by omega]
    · simp [alpha, alphaStar, ceilParity,
        show 21 ≤ 3 * d by omega]
    · simp [alpha, alphaStar, ceilParity,
        show 23 ≤ 3 * d by omega]
    · simp [alpha, alphaStar, ceilParity,
        show 25 ≤ 3 * d by omega]
    · simp [alpha, alphaStar, ceilParity,
        show 27 ≤ 3 * d by omega]
  have hrootPattern : ∀ n, n < 8 →
      d2FlowCandidateActive d n 0 = false ∨
        (d2FlowCandidateActive d n 0 = true ∧
          d2FlowCandidateRole d n 0 = .topDesc) := by
    intro n hn
    interval_cases n
    · right
      constructor <;> simp [d2FlowCandidateActive, d2FlowCandidateRole]
    · left
      simp [d2FlowCandidateActive]
    · right
      constructor
      · simp [d2FlowCandidateActive, tfD2]
        omega
      · simp [d2FlowCandidateRole, d2ScheduleRole,
          hAlpha 2 (by omega), hAlpha 3 (by omega)]
    · left
      simp [d2FlowCandidateActive]
    · right
      constructor
      · simp [d2FlowCandidateActive, tfD2]
        omega
      · simp [d2FlowCandidateRole, d2ScheduleRole,
          hAlpha 4 (by omega), hAlpha 5 (by omega)]
    · left
      simp [d2FlowCandidateActive]
    · right
      constructor
      · simp [d2FlowCandidateActive, tfD2]
        omega
      · simp [d2FlowCandidateRole, d2ScheduleRole,
          hAlpha 6 (by omega), hAlpha 7 (by omega)]
    · left
      simp [d2FlowCandidateActive]
  have hrootZero : ∀ n, n ≤ 8 → d2FlowTreeRootDeficit
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) n) = 0 := by
    intro n
    induction n with
    | zero =>
        intro _
        simp [d, d2FlowCandidateRun, d2FlowTreeInitial,
          d2FlowTreeRootDeficit]
    | succ n ih =>
        intro hn
        have hprev := ih (by omega)
        change d2FlowTreeRootDeficit
          (d2FlowCandidateStage d n
            (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) n)) = 0
        rcases hrootPattern n (by omega) with hinactive | ⟨hactive, hrole⟩
        · rw [d2FlowCandidateStage,
            d2FlowStage_root_deficit_of_inactive _ hinactive]
          exact hprev
        · cases htree : d2FlowCandidateRun (h + 5)
            (d2FlowTreeInitial 8192 (h + 5)) n with
          | node G low high children =>
              have htreeD : d2FlowCandidateRun d
                  (d2FlowTreeInitial 8192 d) n =
                    .node G low high children := by
                simpa [d] using htree
              rw [d2FlowCandidateStage]
              have hdef := d2FlowStage_active_node_deficit
                (active := d2FlowCandidateActive d n)
                (role := d2FlowCandidateRole d n)
                (quota := d2FlowCandidateQuota d n)
                (h := h + 4) (i := 0) (G := G)
                (low := low) (high := high) children hactive
              rw [hdef, hrole]
              have hprev' := hprev
              rw [htreeD] at hprev'
              simpa [d2FlowTreeRootDeficit] using hprev'
  simpa [d] using hrootZero 8 (by omega)

/-- The checked stage-eight level-two gate is the only non-root part still
needed to assemble the actual recursive stage-input predicate. -/
theorem d2FlowCandidateStage8_actual_inputs
    (h : Nat) (hh : 5 ≤ h) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 5) 8)
      (d2FlowCandidateRole (h + 5) 8)
      (d2FlowCandidateQuota (h + 5) 8)
      (fun q => d2FlowCandidateCapacity (h + 5) q 8) 0
      (d2FlowCandidateRun (h + 5)
        (d2FlowTreeInitial 8192 (h + 5)) 8) := by
  have hinv := d2FlowCandidateStage7_preserves_inv (h + 1) (by omega)
  have hfront := d2FlowCandidateStage8_frontiers (h + 5) (by omega)
  rcases hfront with ⟨hactive0, hrole0, hactive2, _, _, _, _⟩
  have hactive1 : d2FlowCandidateActive (h + 5) 8 1 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hrootZero := d2FlowCandidateStage8_root_zero h hh
  cases htree : d2FlowCandidateRun (h + 5)
      (d2FlowTreeInitial 8192 (h + 5)) 8 with
  | node G low high children =>
      have hzero : G = 0 := by
        have hz := hrootZero
        rw [htree] at hz
        simpa [d2FlowTreeRootDeficit] using hz
      have hbalance : low + high = G := by
        have hinv' := hinv
        rw [htree] at hinv'
        simp only [d2FlowTreeInv] at hinv'
        have hcap : G < 8192 * 8 ^ (h + 5) := by
          rw [hzero]
          positivity
        exact hinv'.2.2.1 hcap
      have hchildren : ∀ j, d2FlowStageInvInputs 8192
          (d2FlowCandidateActive (h + 5) 8)
          (d2FlowCandidateRole (h + 5) 8)
          (d2FlowCandidateQuota (h + 5) 8)
          (fun q => d2FlowCandidateCapacity (h + 5) q 8) 1
          (children j) := by
        intro j
        cases hchild : children j with
        | node G1 low1 high1 grandchildren =>
            simp only [d2FlowStageInvInputs, hactive1, if_false]
            constructor
            · intro k
              have hk := d2FlowCandidateStage8_actual_levelTwo_inputs h hh j k
              rw [htree] at hk
              simpa [hchild, d2FlowTreeChild] using hk
            · trivial
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (h + 5) 8)
        (d2FlowCandidateRole (h + 5) 8)
        (d2FlowCandidateQuota (h + 5) 8)
        (fun q => d2FlowCandidateCapacity (h + 5) q 8) 0
        (.node G low high children)
      simp only [d2FlowStageInvInputs, hactive0, if_true, hrole0]
      exact ⟨hchildren, hbalance, hzero⟩

/-- The checked Stage 8 input predicate carries the saturated-aware invariant
through the next complete run stage. -/
theorem d2FlowCandidateStage8_preserves_inv
    (h : Nat) (hh : 5 ≤ h) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (h + 5)
        (d2FlowTreeInitial 8192 (h + 5)) 9) := by
  let before := d2FlowCandidateRun (h + 5)
    (d2FlowTreeInitial 8192 (h + 5)) 8
  have hinv := d2FlowCandidateStage7_preserves_inv (h + 1) (by omega)
  have hinputs := d2FlowCandidateStage8_actual_inputs h hh
  have hpres := d2FlowStage_preserves_inv_of_inputs
    (active := d2FlowCandidateActive (h + 5) 8)
    (role := d2FlowCandidateRole (h + 5) 8)
    (quota := d2FlowCandidateQuota (h + 5) 8)
    (cap := fun q => d2FlowCandidateCapacity (h + 5) q 8)
    (i := 0) before hinv hinputs
  change d2FlowTreeInv 8192
    (d2FlowCandidateStage (h + 5) 8 before)
  simpa [before, d2FlowCandidateRun, d2FlowCandidateStage] using hpres

/-- Stage eight's root top-descending cut zeroes every level-one root in the
actual run-stage-nine tree, which is the first local gate for stage nine. -/
theorem d2FlowCandidateStage9_levelOne_rootdata_zero
    (h : Nat) (hh : 6 ≤ h) :
    ∀ j, d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowCandidateRun (h + 5)
          (d2FlowTreeInitial 8192 (h + 5)) 9) j) = (0, 0, 0) := by
  intro j
  have hfront := d2FlowCandidateStage8_frontiers (h + 5) (by omega)
  rcases hfront with ⟨hactive0, hrole0, _, _, _, _, _⟩
  change d2FlowTreeRootData
    (d2FlowTreeChild
      (d2FlowCandidateStage (h + 5) 8
        (d2FlowCandidateRun (h + 5)
          (d2FlowTreeInitial 8192 (h + 5)) 8)) j) = (0, 0, 0)
  cases htree : d2FlowCandidateRun (h + 5)
      (d2FlowTreeInitial 8192 (h + 5)) 8 with
  | node G low high children =>
      exact d2FlowStage_topDesc_child_rootdata
        (active := d2FlowCandidateActive (h + 5) 8)
        (role := d2FlowCandidateRole (h + 5) 8)
        (quota := d2FlowCandidateQuota (h + 5) 8)
        (h := h + 4) (i := 0) (G := G) (low := low) (high := high)
        children hactive0 hrole0 j

/-- Each level-two mid sender adds its stage-eight quota to its own root.
The level-one root's top-descending rewrite leaves this deeper root intact. -/
theorem d2FlowCandidateStage9_levelTwo_quota_lower
    (h : Nat) (hh : 6 ≤ h) :
    ∀ j k, d2FlowCandidateQuota (h + 5) 8 2 .mid ≤
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (h + 5)
              (d2FlowTreeInitial 8192 (h + 5)) 9) j) k) := by
  intro j k
  have hfront := d2FlowCandidateStage8_frontiers (h + 5) (by omega)
  rcases hfront with ⟨_, _, hactive2, hrole2, _, _, _⟩
  let before := d2FlowCandidateRun (h + 5)
    (d2FlowTreeInitial 8192 (h + 5)) 8
  have hprojection := d2FlowStage_child_child_projection
    (active := d2FlowCandidateActive (h + 5) 8)
    (role := d2FlowCandidateRole (h + 5) 8)
    (quota := d2FlowCandidateQuota (h + 5) 8)
    (h := h + 3) (i := 0) before j k
  have hinactive1 : d2FlowCandidateActive (h + 5) 8 1 = false := by
    simp [d2FlowCandidateActive, tfD2]
  cases hsourceOne : d2FlowTreeChild before j with
  | node G1 low1 high1 children1 =>
      have hinactiveChild := d2FlowStage_inactive_child
        (active := d2FlowCandidateActive (h + 5) 8)
        (role := d2FlowCandidateRole (h + 5) 8)
        (quota := d2FlowCandidateQuota (h + 5) 8)
        (h := h + 3) (i := 1) (G := G1) (low := low1)
        (high := high1) children1 hinactive1 k
      have houtput : d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (h + 5)
              (d2FlowTreeInitial 8192 (h + 5)) 9) j) k =
          d2FlowStage (d2FlowCandidateActive (h + 5) 8)
            (d2FlowCandidateRole (h + 5) 8)
            (d2FlowCandidateQuota (h + 5) 8) (h + 3) 2
            (children1 k) := by
        change d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateStage (h + 5) 8 before) j) k = _
        rw [d2FlowCandidateStage, hprojection, hsourceOne]
        exact hinactiveChild
      cases hchildTwo : children1 k with
      | node G2 low2 high2 children2 =>
          have hrootStep := d2FlowStage_active_node_deficit
            (active := d2FlowCandidateActive (h + 5) 8)
            (role := d2FlowCandidateRole (h + 5) 8)
            (quota := d2FlowCandidateQuota (h + 5) 8)
            (h := h + 2) (i := 2) (G := G2)
            (low := low2) (high := high2) children2 hactive2
          have hrootStep' : d2FlowTreeRootDeficit
              (d2FlowStage (d2FlowCandidateActive (h + 5) 8)
                (d2FlowCandidateRole (h + 5) 8)
                (d2FlowCandidateQuota (h + 5) 8) (h + 3) 2
                (.node G2 low2 high2 children2)) =
              G2 + d2FlowCandidateQuota (h + 5) 8 2 .mid := by
            simpa [hrole2] using hrootStep
          rw [houtput, hchildTwo, hrootStep']
          omega

set_option maxHeartbeats 10000000 in
/-- Complete local gate for the stage-nine level-three mid sender. Its sender
bound comes from the preceding level-two cut, at half the current capacity. -/
theorem d2FlowCandidateStage9_mid_inputs
    (d : Nat) (hd : 11 ≤ d) (G low high : Nat) {r : Nat}
    (hbalance : low + high = G)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 3 9)
    (children : Fin 8 → D2FlowTree r)
    (hrecursive : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 9)
      (d2FlowCandidateRole d 9)
      (d2FlowCandidateQuota d 9)
      (fun q => d2FlowCandidateCapacity d q 9) 4 (children j))
    (hleft : d2FlowCandidateCapacity d 3 9 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hright : d2FlowCandidateCapacity d 3 9 ≤
      128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩))
    (htotal : d2FlowCandidateQuota d 9 3 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 9)
      (d2FlowCandidateRole d 9)
      (d2FlowCandidateQuota d 9)
      (fun q => d2FlowCandidateCapacity d q 9) 3
      (.node G low high children) := by
  rcases d2FlowCandidateStage9_frontiers d hd with
    ⟨_, _, hactive, hrole, _, _, _⟩
  have hcap3 : d2FlowCandidateCapacity d 3 9 = 2 ^ (3 * d) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
  have hquota : d2FlowCandidateQuota d 9 3 .mid =
      15 * 2 ^ (3 * d - 12) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
  have hquotaEven : d2FlowCandidateQuota d 9 3 .mid % 2 = 0 := by
    rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 12 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 9 3 .mid ≤
      d2FlowCandidateCapacity d 3 9 := by
    rw [hquota, hcap3]
    have hp : 256 * 2 ^ (3 * d - 12) = 2 ^ (3 * d - 4) := by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_add]
      congr 1 <;> omega
    have hpCap : 2 ^ (3 * d) = 16 * 2 ^ (3 * d - 4) := by
      rw [show 3 * d = 4 + (3 * d - 4) by omega, pow_add]
      norm_num
    nlinarith [hp, hpCap]
  simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
  exact ⟨hrecursive, ⟨hbalance, hG, hquotaCap, htotal, hquotaEven,
    hleft, hright⟩⟩

/-- The inherited sender cap and one endpoint reserve pay for the stage-nine
mid quota, including the parent's deficit. -/
theorem d2FlowCandidateStage9_mid_boundary_mass_suffices
    (d : Nat) (hd : 11 ≤ d) (G : Nat)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 3 9) {r : Nat}
    (children : Fin 8 → D2FlowTree r)
    (hleft : d2FlowCandidateCapacity d 3 9 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩)) :
    d2FlowCandidateQuota d 9 3 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
  have hcap3 : d2FlowCandidateCapacity d 3 9 = 2 ^ (3 * d) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
  have hquota : d2FlowCandidateQuota d 9 3 .mid =
      15 * 2 ^ (3 * d - 12) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
  have hGsmall : G ≤ 2 ^ (3 * d - 9) := by
    rw [hcap3] at hG
    have hp : 512 * 2 ^ (3 * d - 9) = 2 ^ (3 * d) := by
      rw [show (512 : Nat) = 2 ^ 9 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hrootSmall : 2 ^ (3 * d - 7) ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hcap3] at hleft
    have hp : 128 * 2 ^ (3 * d - 7) = 2 ^ (3 * d) := by
      rw [show (128 : Nat) = 2 ^ 7 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hA : 2 ^ (3 * d - 7) = 64 * 2 ^ (3 * d - 13) := by
    rw [show 3 * d - 7 = 6 + (3 * d - 13) by omega, pow_add]
    norm_num
  have hB : 2 ^ (3 * d - 9) = 16 * 2 ^ (3 * d - 13) := by
    rw [show 3 * d - 9 = 4 + (3 * d - 13) by omega, pow_add]
    norm_num
  have hQ : 2 ^ (3 * d - 12) = 2 * 2 ^ (3 * d - 13) := by
    rw [show 3 * d - 12 = 1 + (3 * d - 13) by omega, pow_add]
    norm_num
  have hmass : G + d2FlowCandidateQuota d 9 3 .mid ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hA] at hrootSmall
    rw [hB] at hGsmall
    rw [hquota, hQ]
    nlinarith
  have hrootTotal : d2FlowTreeRootDeficit (children ⟨0, by omega⟩) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    let f : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
    change f ⟨0, by omega⟩ ≤ Finset.univ.sum f
    exact Finset.single_le_sum
      (fun j hj => Nat.zero_le (f j))
      (Finset.mem_univ (⟨0, by omega⟩ : Fin 8))
  omega

set_option maxHeartbeats 10000000 in
/-- Stage eight's level-four bottom-descending cut leaves at least its quota
at every actual level-four root in the stage-nine input tree. -/
theorem d2FlowCandidateStage9_levelFour_quota_lower
    (h : Nat) (hh : 6 ≤ h) :
    ∀ j k m l, d2FlowCandidateQuota (h + 5) 8 4 .botDesc ≤
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (h + 5)
                  (d2FlowTreeInitial 8192 (h + 5)) 9) j) k) m) l) := by
  intro j k m l
  let before := d2FlowCandidateRun (h + 5)
    (d2FlowTreeInitial 8192 (h + 5)) 8
  let sourceThree := d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild before j) k) m
  let sourceFour := d2FlowTreeChild sourceThree l
  let levelFourOut := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun (h + 5)
            (d2FlowTreeInitial 8192 (h + 5)) 9) j) k) m) l
  have hfront := d2FlowCandidateStage8_frontiers (h + 5) (by omega)
  rcases hfront with ⟨_, _, _, _, hactive4, hrole4, _⟩
  have hpath := d2FlowStage_path4_projection
    (active := d2FlowCandidateActive (h + 5) 8)
    (role := d2FlowCandidateRole (h + 5) 8)
    (quota := d2FlowCandidateQuota (h + 5) 8)
    (h := h + 1) (i := 0) before j k m l
  have hproject : levelFourOut = d2FlowTreeChild (d2FlowStage
      (d2FlowCandidateActive (h + 5) 8)
      (d2FlowCandidateRole (h + 5) 8)
      (d2FlowCandidateQuota (h + 5) 8) (h + 2) 3 sourceThree) l := by
    change d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateStage (h + 5) 8 before) j) k) m) l = _
    unfold d2FlowCandidateStage
    simpa [sourceThree] using hpath
  have hinactive3 : d2FlowCandidateActive (h + 5) 8 3 = false := by
    simp [d2FlowCandidateActive, tfD2]
  cases hsourceThree : sourceThree with
  | node G3 low3 high3 children3 =>
      have hinactiveChild := d2FlowStage_inactive_child
        (active := d2FlowCandidateActive (h + 5) 8)
        (role := d2FlowCandidateRole (h + 5) 8)
        (quota := d2FlowCandidateQuota (h + 5) 8)
        (h := h + 1) (i := 3) (G := G3) (low := low3)
        (high := high3) children3 hinactive3 l
      have hlocal : levelFourOut = d2FlowStage
          (d2FlowCandidateActive (h + 5) 8)
          (d2FlowCandidateRole (h + 5) 8)
          (d2FlowCandidateQuota (h + 5) 8) (h + 1) 4 sourceFour := by
        calc
          levelFourOut = d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive (h + 5) 8)
                (d2FlowCandidateRole (h + 5) 8)
                (d2FlowCandidateQuota (h + 5) 8) (h + 2) 3
                (.node G3 low3 high3 children3)) l := by
              rw [hsourceThree] at hproject
              exact hproject
          _ = d2FlowStage (d2FlowCandidateActive (h + 5) 8)
                (d2FlowCandidateRole (h + 5) 8)
                (d2FlowCandidateQuota (h + 5) 8) (h + 1) 4 sourceFour := by
              simpa [sourceFour, hsourceThree, d2FlowTreeChild] using hinactiveChild
      cases hsource : sourceFour with
      | node G low high children =>
          have hroot := d2FlowStage_active_node_deficit
            (active := d2FlowCandidateActive (h + 5) 8)
            (role := d2FlowCandidateRole (h + 5) 8)
            (quota := d2FlowCandidateQuota (h + 5) 8)
            (h := h) (i := 4) (G := G) (low := low) (high := high)
            children hactive4
          have hroot' : d2FlowTreeRootDeficit
              (d2FlowStage (d2FlowCandidateActive (h + 5) 8)
                (d2FlowCandidateRole (h + 5) 8)
                (d2FlowCandidateQuota (h + 5) 8) (h + 1) 4
                (.node G low high children)) =
              G + d2FlowCandidateQuota (h + 5) 8 4 .botDesc := by
            simpa [hrole4] using hroot
          change d2FlowCandidateQuota (h + 5) 8 4 .botDesc ≤
            d2FlowTreeRootDeficit levelFourOut
          rw [hlocal, hsource, hroot']
          omega

/-- The stage-eight mid quota on each level-two root exceeds the
stage-nine level-one top-rise endpoint-reserve requirement. -/
theorem d2FlowCandidateStage9_levelOne_endpoint_reserves
    (h : Nat) (hh : 6 ≤ h) :
    ∀ j k, d2FlowCandidateCapacity (h + 5) 1 9 ≤
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (h + 5)
              (d2FlowTreeInitial 8192 (h + 5)) 9) j) k) := by
  have hcap : d2FlowCandidateCapacity (h + 5) 1 9 =
      2 ^ (3 * (h + 5) - 6) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota (h + 5) 8 2 .mid =
      15 * 2 ^ (3 * (h + 5) - 13) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hfactor : 128 * 2 ^ (3 * (h + 5) - 13) =
      2 ^ (3 * (h + 5) - 6) := by
    rw [show (128 : Nat) = 2 ^ 7 by norm_num, ← pow_add]
    congr 1 <;> omega
  have harith : d2FlowCandidateCapacity (h + 5) 1 9 ≤
      128 * d2FlowCandidateQuota (h + 5) 8 2 .mid := by
    rw [hcap, hquota]
    nlinarith [hfactor]
  intro j k
  exact Nat.le_trans harith
    (Nat.mul_le_mul_left 128
      (d2FlowCandidateStage9_levelTwo_quota_lower h hh j k))

set_option maxHeartbeats 10000000 in
/-- Once the level-three recursive obligations are supplied, each actual
stage-nine level-one top-rise node meets its complete local input gate. -/
theorem d2FlowCandidateStage9_levelOne_inputs
    (h : Nat) (hh : 6 ≤ h)
    (hrecursive : ∀ j k, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 5) 9)
      (d2FlowCandidateRole (h + 5) 9)
      (d2FlowCandidateQuota (h + 5) 9)
      (fun q => d2FlowCandidateCapacity (h + 5) q 9) 2
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun (h + 5)
            (d2FlowTreeInitial 8192 (h + 5)) 9) j) k)) :
    ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 5) 9)
      (d2FlowCandidateRole (h + 5) 9)
      (d2FlowCandidateQuota (h + 5) 9)
      (fun q => d2FlowCandidateCapacity (h + 5) q 9) 1
      (d2FlowTreeChild
        (d2FlowCandidateRun (h + 5)
          (d2FlowTreeInitial 8192 (h + 5)) 9) j) := by
  classical
  intro j
  have hfront := d2FlowCandidateStage9_frontiers (h + 5) (by omega)
  rcases hfront with ⟨hactive1, hrole1, _, _, _, _, _⟩
  have hdata := d2FlowCandidateStage9_levelOne_rootdata_zero h hh j
  cases hnode : d2FlowTreeChild
      (d2FlowCandidateRun (h + 5)
        (d2FlowTreeInitial 8192 (h + 5)) 9) j with
  | node G low high children =>
      rw [hnode] at hdata
      have hG : G = 0 := by
        have hp := congrArg Prod.fst hdata
        simpa [d2FlowTreeRootData] using hp
      have hlow : low = 0 := by
        have hp := congrArg (fun x : Nat × Nat × Nat => x.2.1) hdata
        simpa [d2FlowTreeRootData] using hp
      have hhigh : high = 0 := by
        have hp := congrArg (fun x : Nat × Nat × Nat => x.2.2) hdata
        simpa [d2FlowTreeRootData] using hp
      have hbalance : low + high = G := by omega
      have hGcap : 512 * G ≤ d2FlowCandidateCapacity (h + 5) 1 9 := by
        rw [hG]
        omega
      have hactiveProp : active (h + 5) (tfD2 (h + 5)) 1 9 := by
        have hm := d2FlowCandidateActive_matches_schedule
          (d := h + 5) (t := 9) (i := 1) (by omega)
        rw [hactive1] at hm
        exact of_decide_eq_true hm.symm
      have hroleSchedule : d2ScheduleRole (h + 5) 1 9 = .topRise := by
        have hr := d2FlowCandidateRole_matches_schedule
          (d := h + 5) (i := 1) (t := 9) (by omega)
        exact hr.symm.trans hrole1
      have hregularRole : d2ScheduleRole (h + 5) 1 9 = .topRise ∨
          d2ScheduleRole (h + 5) 1 9 = .mid ∨
          d2ScheduleRole (h + 5) 1 9 = .botDesc := Or.inl hroleSchedule
      have hquotaCap := d2FlowCandidateQuota_le_capacity_div_256
        (by omega) hactiveProp hregularRole
      have hquotaEven := d2FlowCandidateQuota_even
        (by omega) hactiveProp (by omega) hregularRole
      have hleft : d2FlowCandidateCapacity (h + 5) 1 9 ≤
          128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
        have he := d2FlowCandidateStage9_levelOne_endpoint_reserves
          h hh j ⟨0, by omega⟩
        rw [hnode] at he
        simpa only [d2FlowTreeChild] using he
      have hright : d2FlowCandidateCapacity (h + 5) 1 9 ≤
          128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩) := by
        have he := d2FlowCandidateStage9_levelOne_endpoint_reserves
          h hh j ⟨7, by omega⟩
        rw [hnode] at he
        simpa only [d2FlowTreeChild] using he
      have hquotaChild : d2FlowCandidateQuota (h + 5) 9 1 .topRise ≤
          d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
        have hq := hquotaCap
        rw [hroleSchedule] at hq
        nlinarith [hleft]
      have hquotaTotal : d2FlowCandidateQuota (h + 5) 9 1 .topRise ≤
          d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G := by
        have hsize := d2FlowSize_le_total
          (fun k => d2FlowTreeRootDeficit (children k)) ⟨0, by omega⟩
        have hle := le_trans hquotaChild hsize
        simpa [hG] using hle
      have hquotaCap' : 256 * d2FlowCandidateQuota (h + 5) 9 1
          (d2FlowCandidateRole (h + 5) 9 1) ≤
          d2FlowCandidateCapacity (h + 5) 1 9 := by
        simpa [hrole1, hroleSchedule] using hquotaCap
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (h + 5) 9)
        (d2FlowCandidateRole (h + 5) 9)
        (d2FlowCandidateQuota (h + 5) 9)
        (fun q => d2FlowCandidateCapacity (h + 5) q 9) 1
        (.node G low high children)
      simp only [d2FlowStageInvInputs, hactive1, if_true, hrole1]
      have hrecursive' : ∀ k, d2FlowStageInvInputs 8192
          (d2FlowCandidateActive (h + 5) 9)
          (d2FlowCandidateRole (h + 5) 9)
          (d2FlowCandidateQuota (h + 5) 9)
          (fun q => d2FlowCandidateCapacity (h + 5) q 9) 2
          (children k) := by
        intro k
        have hk := hrecursive j k
        rw [hnode] at hk
        simpa [d2FlowTreeChild] using hk
      exact ⟨hrecursive', hbalance, hGcap,
        (by simpa [hrole1] using hquotaCap'), hquotaTotal,
        (by simpa [hrole1] using hquotaEven), hleft, hright⟩

set_option maxHeartbeats 10000000 in
/-- Stage eight leaves every actual level-six root at native size. The
level-five roots are saturated in the preceding state, so invariant
child-cover saturates their level-six children; the stage-eight cuts overwrite
only level-five root data. -/
theorem d2FlowCandidateStage8_actual_levelSix_native
    (depth : Nat) (hh : 5 ≤ depth) :
    ∀ j k m l q s, d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (depth + 6)
                    (d2FlowTreeInitial 8192 (depth + 6)) 9) j) k) m) l) q) s) =
      8192 * 8 ^ depth := by
  intro j k m l q s
  let before := d2FlowCandidateRun (depth + 6)
    (d2FlowTreeInitial 8192 (depth + 6)) 8
  let levelTwo := d2FlowTreeChild (d2FlowTreeChild before j) k
  let levelFour := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild before j) k) m) l
  have hinvGlobal := d2FlowCandidateStage7_preserves_inv (depth + 2) (by omega)
  have hinvTwo := d2FlowTreeInv_grandchild (h := depth + 4)
    before hinvGlobal j k
  have hinvFour := d2FlowTreeInv_grandchild (h := depth + 2)
    levelTwo hinvTwo m l
  have hnativeFive := d2FlowCandidateStage7_actual_levelFive_native
    (depth + 1) (by omega) j k m l q
  have hfront := d2FlowCandidateStage8_frontiers (depth + 6) (by omega)
  rcases hfront with ⟨_, _, _, _, _, _, hinactive6⟩
  have hinactive5 : d2FlowCandidateActive (depth + 6) 8 5 = false := by
    simp [d2FlowCandidateActive, tfD2]
  cases hnodeFour : levelFour with
  | node G4 low4 high4 children4 =>
      have hinvFour' : d2FlowTreeInv 8192
          (.node G4 low4 high4 children4) := by
        rw [← hnodeFour]
        exact hinvFour
      have hinvFive := hinvFour'.2.2.2 q
      have hnativeFive' := hnativeFive
      change d2FlowTreeRootDeficit (d2FlowTreeChild levelFour q) =
        8192 * 8 ^ (depth + 1) at hnativeFive'
      rw [hnodeFour] at hnativeFive'
      cases hnodeFive : children4 q with
      | node G5 low5 high5 children5 =>
          have hinvFive' : d2FlowTreeInv 8192
              (.node G5 low5 high5 children5) := by
            rw [← hnodeFive]
            exact hinvFive
          have hG5 : G5 = 8192 * 8 ^ (depth + 1) := by
            simpa [d2FlowTreeChild, hnodeFive, d2FlowTreeRootDeficit] using
              hnativeFive'
          have hfull : G5 = 8192 * 8 ^ (depth + 1) := hG5
          have hchildrenNative := d2FlowTreeInv_native_node_children
            (h := depth) (scale := 8192) children5 hinvFive' hfull
          have hnativeChild : d2FlowTreeRootDeficit (children5 s) =
              8192 * 8 ^ depth := hchildrenNative s
          have hprojection := d2FlowStage_path6_projection
            (active := d2FlowCandidateActive (depth + 6) 8)
            (role := d2FlowCandidateRole (depth + 6) 8)
            (quota := d2FlowCandidateQuota (depth + 6) 8)
            (h := depth) (i := 0) before j k m l q s
          have hlocal : d2FlowTreeRootDeficit
              (d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive (depth + 6) 8)
                  (d2FlowCandidateRole (depth + 6) 8)
                  (d2FlowCandidateQuota (depth + 6) 8) (depth + 1) 5
                  (.node G5 low5 high5 children5)) s) =
              d2FlowTreeRootDeficit (children5 s) := by
            have hchild := d2FlowStage_inactive_child
              (active := d2FlowCandidateActive (depth + 6) 8)
              (role := d2FlowCandidateRole (depth + 6) 8)
              (quota := d2FlowCandidateQuota (depth + 6) 8)
              (h := depth) (i := 5) (G := G5) (low := low5)
              (high := high5) children5 hinactive5 s
            rw [hchild]
            exact d2FlowStage_root_deficit_of_inactive
              (children5 s) hinactive6
          change d2FlowTreeRootDeficit
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowTreeChild
                        (d2FlowTreeChild
                          (d2FlowCandidateStage (depth + 6) 8 before) j) k) m) l) q) s) = _
          unfold d2FlowCandidateStage
          rw [hprojection]
          have hsourceFive : d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild before j) k) m) l) q =
              .node G5 low5 high5 children5 := by
            change d2FlowTreeChild levelFour q = _
            rw [hnodeFour]
            simpa [d2FlowTreeChild] using hnodeFive
          rw [hsourceFive]
          exact hlocal.trans hnativeChild

set_option maxHeartbeats 10000000 in
/-- Stage nine's bottom-rise turns each actual level-five root into the exact
sum of its level-six children. The preceding native level-six reserve lemma
therefore makes every level-five root native in run stage ten. -/
theorem d2FlowCandidateStage9_actual_levelFive_native
    (depth : Nat) (hh : 6 ≤ depth) :
    ∀ j k m l q, d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (depth + 5)
                  (d2FlowTreeInitial 8192 (depth + 5)) 10) j) k) m) l) q) =
      8192 * 8 ^ depth := by
  intro j k m l q
  let before := d2FlowCandidateRun (depth + 5)
    (d2FlowTreeInitial 8192 (depth + 5)) 9
  let levelFour := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild before j) k) m) l
  have hprojection := d2FlowStage_path5_projection
    (active := d2FlowCandidateActive (depth + 5) 9)
    (role := d2FlowCandidateRole (depth + 5) 9)
    (quota := d2FlowCandidateQuota (depth + 5) 9)
    (h := depth) (i := 0) before j k m l q
  have hinvGlobal := d2FlowCandidateStage8_preserves_inv depth (by omega)
  have hinvTwo := d2FlowTreeInv_grandchild (h := depth + 3)
    before hinvGlobal j k
  have hinvFour := d2FlowTreeInv_grandchild (h := depth + 1)
    (d2FlowTreeChild (d2FlowTreeChild before j) k) hinvTwo m l
  let depthKeep := depth
  cases hnodeFour : levelFour with
  | node G4 low4 high4 children4 =>
      have hfront := d2FlowCandidateStage9_frontiers (depthKeep + 5) (by omega)
      rcases hfront with ⟨_, _, _, _, hactive5, hrole5, hinactive7⟩
      have hinactive4 : d2FlowCandidateActive (depthKeep + 5) 9 4 = false := by
        simp [d2FlowCandidateActive, tfD2]
      have hinvFour' : d2FlowTreeInv 8192
          (.node G4 low4 high4 children4) := by
        rw [← hnodeFour]
        exact hinvFour
      have hinvFive := hinvFour'.2.2.2 q
      have hinactiveChild := d2FlowStage_inactive_child
        (active := d2FlowCandidateActive (depthKeep + 5) 9)
        (role := d2FlowCandidateRole (depthKeep + 5) 9)
        (quota := d2FlowCandidateQuota (depthKeep + 5) 9)
        (h := depthKeep) (i := 4) (G := G4) (low := low4) (high := high4)
        children4 hinactive4 q
      cases hnodeFive : children4 q with
      | node G5 low5 high5 children5 =>
          have hinvFive' : d2FlowTreeInv 8192
              (.node G5 low5 high5 children5) := by
            rw [← hnodeFive]
            exact hinvFive
          have hnativeSix := d2FlowCandidateStage8_actual_levelSix_native
            (depthKeep - 1) (by omega) j k m l q
          have hsourceFive : d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild before j) k) m) l) q =
              .node G5 low5 high5 children5 := by
            change d2FlowTreeChild levelFour q = _
            rw [hnodeFour]
            simpa only [d2FlowTreeChild] using hnodeFive
          have hchildrenNative : ∀ s,
              d2FlowTreeRootDeficit (children5 s) = 8192 * 8 ^ (depthKeep - 1) := by
            intro s
            have hn := hnativeSix s
            simp only [depthKeep, Nat.succ_sub_one] at hn
            rw [hsourceFive] at hn
            simpa only [d2FlowTreeChild] using hn
          have htotal : d2FlowTotal
              (fun s => d2FlowTreeRootDeficit (children5 s)) =
              8192 * 8 ^ depthKeep := by
            rw [d2FlowTotal]
            calc
              Finset.univ.sum (fun s : Fin 8 =>
                  d2FlowTreeRootDeficit (children5 s)) =
                Finset.univ.sum (fun _ : Fin 8 => 8192 * 8 ^ (depthKeep - 1)) := by
                  apply Finset.sum_congr rfl
                  intro s hs
                  exact hchildrenNative s
              _ = 8 * (8192 * 8 ^ (depthKeep - 1)) := by simp
              _ = 8192 * 8 ^ depthKeep := by
                simp only [depthKeep, Nat.succ_sub_one]
                rw [pow_succ]
                ring
          have hcover := d2FlowTreeInv_node_children_cover children5 hinvFive'
          have hcover' : G5 ≤ 8192 * 8 ^ depthKeep := by
            rw [← htotal]
            exact hcover
          have hlocal : d2FlowTreeRootDeficit
              (d2FlowStage (d2FlowCandidateActive (depthKeep + 5) 9)
                (d2FlowCandidateRole (depthKeep + 5) 9)
                (d2FlowCandidateQuota (depthKeep + 5) 9) depthKeep 5
                (.node G5 low5 high5 children5)) = 8192 * 8 ^ depthKeep := by
            rw [d2FlowStage_active_node_deficit children5 hactive5, hrole5]
            rw [htotal]
            exact Nat.add_sub_of_le hcover'
          have hparentProjection :
              d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive (depthKeep + 5) 9)
                  (d2FlowCandidateRole (depthKeep + 5) 9)
                  (d2FlowCandidateQuota (depthKeep + 5) 9) (depthKeep + 1) 4
                  (.node G4 low4 high4 children4)) q =
              d2FlowStage (d2FlowCandidateActive (depthKeep + 5) 9)
                (d2FlowCandidateRole (depthKeep + 5) 9)
                (d2FlowCandidateQuota (depthKeep + 5) 9) depthKeep 5
                (.node G5 low5 high5 children5) := by
            simpa [hnodeFive] using hinactiveChild
          change d2FlowTreeRootDeficit
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowTreeChild
                        (d2FlowCandidateStage (depthKeep + 5) 9 before) j) k) m) l) q) = _
          unfold d2FlowCandidateStage
          have hprojected : d2FlowTreeRootDeficit
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowTreeChild
                        (d2FlowStage (d2FlowCandidateActive (depthKeep + 5) 9)
                          (d2FlowCandidateRole (depthKeep + 5) 9)
                          (d2FlowCandidateQuota (depthKeep + 5) 9)
                          (depthKeep + 5) 0 before) j) k) m) l) q) =
              d2FlowTreeRootDeficit
                (d2FlowTreeChild
                  (d2FlowStage (d2FlowCandidateActive (depthKeep + 5) 9)
                    (d2FlowCandidateRole (depthKeep + 5) 9)
                    (d2FlowCandidateQuota (depthKeep + 5) 9)
                    (depthKeep + 1) 4 levelFour) q) := by
            simpa only [depthKeep] using hprojection
          rw [hprojected]
          rw [hnodeFour]
          rw [hparentProjection]
          exact hlocal
      | leaf G5 low5 high5 => omega

set_option maxHeartbeats 10000000 in
/-- Stage nine's bottom-rise preserves the native level-six roots supplied by
stage eight. -/
theorem d2FlowCandidateStage9_actual_levelSix_native
    (depth : Nat) (hd : 5 ≤ depth) :
    ∀ j k m l q s, d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (depth + 6)
                    (d2FlowTreeInitial 8192 (depth + 6)) 10) j) k) m) l) q) s) =
      8192 * 8 ^ depth := by
  intro j k m l q s
  let d := depth + 6
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 9
  have hfront := d2FlowCandidateStage9_frontiers d (by omega)
  rcases hfront with ⟨_, _, _, _, hactive5, hrole5, _⟩
  have hinactive6 : d2FlowCandidateActive d 9 6 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hbase := d2FlowCandidateStage8_actual_levelSix_native
    depth hd j k m l q s
  have hproject := d2FlowStage_path6_projection
    (active := d2FlowCandidateActive d 9)
    (role := d2FlowCandidateRole d 9)
    (quota := d2FlowCandidateQuota d 9)
    (h := depth) (i := 0) before j k m l q s
  have hproject' : d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 10) j) k) m) l) q) s) =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 9)
            (d2FlowCandidateRole d 9) (d2FlowCandidateQuota d 9)
            (depth + 1) 5
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild before j) k) m) l) q)) s) := by
    simpa [d, before, d2FlowCandidateRun, d2FlowCandidateStage] using hproject
  let parent := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild before j) k) m) l) q
  have hpathParent : d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild before j) k) m) l) q = parent := rfl
  cases hparent : parent with
  | node G low high children =>
      have hkeep := d2FlowStage_botRise_child_root_deficit
        (active := d2FlowCandidateActive d 9)
        (role := d2FlowCandidateRole d 9)
        (quota := d2FlowCandidateQuota d 9)
        (h := depth) (i := 5) (G := G) (low := low) (high := high)
        children hactive5 hrole5 hinactive6 s
      have hproject'' := hproject'
      rw [hpathParent, hparent] at hproject''
      rw [hkeep] at hproject''
      have hbase' : d2FlowTreeRootDeficit (children s) =
          8192 * 8 ^ depth := by
        have hb := hbase
        change d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild before j) k) m) l) q) s) = _ at hb
        rw [hpathParent, hparent] at hb
        simpa [parent, d2FlowTreeChild] using hb
      exact hproject''.trans hbase'

set_option maxHeartbeats 10000000 in
/-- The inactive level-five frontier in stage ten carries those exact
level-six reserves through to the stage-eleven input tree. -/
theorem d2FlowCandidateStage10_actual_levelSix_native
    (depth : Nat) (hd : 5 ≤ depth) :
    ∀ j k m l q s, d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (depth + 6)
                    (d2FlowTreeInitial 8192 (depth + 6)) 11) j) k) m) l) q) s) =
      8192 * 8 ^ depth := by
  intro j k m l q s
  let d := depth + 6
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 10
  have hbase := d2FlowCandidateStage9_actual_levelSix_native depth hd j k m l q s
  have hproject := d2FlowStage_path6_projection
    (active := d2FlowCandidateActive d 10)
    (role := d2FlowCandidateRole d 10)
    (quota := d2FlowCandidateQuota d 10)
    (h := depth) (i := 0) before j k m l q s
  have hinactive5 : d2FlowCandidateActive d 10 5 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hinactive6 : d2FlowCandidateActive d 10 6 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hproject' : d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 11) j) k) m) l) q) s) =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 10)
            (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
            (depth + 1) 5
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild before j) k) m) l) q)) s) := by
    simpa [d, before, d2FlowCandidateRun, d2FlowCandidateStage] using hproject
  let parent := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild before j) k) m) l) q
  have hpathParent : d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild before j) k) m) l) q = parent := rfl
  cases hparent : parent with
  | node G low high children =>
      have hkeep : d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 10)
              (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
            (depth + 1) 5 (.node G low high children)) s) =
          d2FlowTreeRootDeficit (children s) := by
        simp only [d2FlowStage, hinactive5, if_false, d2FlowTreeChild]
        exact d2FlowStage_root_deficit_of_inactive
          (active := d2FlowCandidateActive d 10)
          (role := d2FlowCandidateRole d 10)
          (quota := d2FlowCandidateQuota d 10)
          (h := depth) (i := 6) (children s) hinactive6
      have hproject'' := hproject'
      rw [hpathParent, hparent] at hproject''
      rw [hkeep] at hproject''
      have hbase' : d2FlowTreeRootDeficit (children s) =
          8192 * 8 ^ depth := by
        have hb := hbase
        change d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild before j) k) m) l) q) s) = _ at hb
        rw [hpathParent, hparent] at hb
        simpa [parent, d2FlowTreeChild] using hb
      exact hproject''.trans hbase'

set_option maxHeartbeats 10000000 in
/-- Every actual stage-nine level-five bottom-rise node is balanced: it is a
child written by stage eight's level-four ordinary cut. The entire tail below
level five is inactive at stage nine. -/
theorem d2FlowCandidateStage9_actual_levelFive_inputs
    (h : Nat) (hh : 6 ≤ h) :
    ∀ j k m l q, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 5) 9)
      (d2FlowCandidateRole (h + 5) 9)
      (d2FlowCandidateQuota (h + 5) 9)
      (fun r => d2FlowCandidateCapacity (h + 5) r 9) 5
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (h + 5)
                  (d2FlowTreeInitial 8192 (h + 5)) 9) j) k) m) l) q) := by
  intro j k m l q
  let before := d2FlowCandidateRun (h + 5)
    (d2FlowTreeInitial 8192 (h + 5)) 8
  let sourceThree := d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild before j) k) m
  let sourceFour := d2FlowTreeChild sourceThree l
  let levelFourOut := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun (h + 5)
            (d2FlowTreeInitial 8192 (h + 5)) 9) j) k) m) l
  let levelFiveOut := d2FlowTreeChild levelFourOut q
  have hfront8 := d2FlowCandidateStage8_frontiers (h + 5) (by omega)
  rcases hfront8 with ⟨_, _, _, _, hactive4, hrole4, _⟩
  have hfront9 := d2FlowCandidateStage9_frontiers (h + 5) (by omega)
  rcases hfront9 with ⟨_, _, _, _, hactive5, hrole5, _⟩
  have hinactive3 : d2FlowCandidateActive (h + 5) 8 3 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have htailInactive : ∀ r, 6 ≤ r →
      d2FlowCandidateActive (h + 5) 9 r = false := by
    intro r hr
    have hu : ¬ 3 * r < 17 := by omega
    simp [d2FlowCandidateActive, show 9 ≠ 0 by omega,
      show 9 ≠ 1 by omega, hu]
  have htail : ∀ {depth : Nat} (tree : D2FlowTree depth),
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (h + 5) 9)
        (d2FlowCandidateRole (h + 5) 9)
        (d2FlowCandidateQuota (h + 5) 9)
        (fun r => d2FlowCandidateCapacity (h + 5) r 9) 6 tree := by
    intro depth tree
    apply d2FlowStageInvInputs_all_inactive
    intro r hr
    exact htailInactive r hr
  have hpathFour := d2FlowStage_path4_projection
    (active := d2FlowCandidateActive (h + 5) 8)
    (role := d2FlowCandidateRole (h + 5) 8)
    (quota := d2FlowCandidateQuota (h + 5) 8)
    (h := h + 1) (i := 0) before j k m l
  have hproject : levelFourOut = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive (h + 5) 8)
        (d2FlowCandidateRole (h + 5) 8)
        (d2FlowCandidateQuota (h + 5) 8) (h + 2) 3 sourceThree) l := by
    change d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateStage (h + 5) 8 before) j) k) m) l = _
    unfold d2FlowCandidateStage
    simpa [sourceThree] using hpathFour
  cases hsourceThree : sourceThree with
  | node G3 low3 high3 children3 =>
      have hinactiveChild := d2FlowStage_inactive_child
        (active := d2FlowCandidateActive (h + 5) 8)
        (role := d2FlowCandidateRole (h + 5) 8)
        (quota := d2FlowCandidateQuota (h + 5) 8)
        (h := h + 1) (i := 3) (G := G3) (low := low3)
        (high := high3) children3 hinactive3 l
      have hlocalOut : levelFourOut = d2FlowStage
          (d2FlowCandidateActive (h + 5) 8)
          (d2FlowCandidateRole (h + 5) 8)
          (d2FlowCandidateQuota (h + 5) 8) (h + 1) 4 sourceFour := by
        calc
          levelFourOut = d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive (h + 5) 8)
                (d2FlowCandidateRole (h + 5) 8)
                (d2FlowCandidateQuota (h + 5) 8) (h + 2) 3
                (.node G3 low3 high3 children3)) l := by
              rw [hsourceThree] at hproject
              exact hproject
          _ = d2FlowStage (d2FlowCandidateActive (h + 5) 8)
                (d2FlowCandidateRole (h + 5) 8)
                (d2FlowCandidateQuota (h + 5) 8) (h + 1) 4 sourceFour := by
              simpa [sourceFour, hsourceThree, d2FlowTreeChild] using
                hinactiveChild
      cases hsourceFour : sourceFour with
      | node G4 low4 high4 children4 =>
          have hchildBalanced := d2FlowStage_regular_child_balanced
            (active := d2FlowCandidateActive (h + 5) 8)
            (role := d2FlowCandidateRole (h + 5) 8)
            (quota := d2FlowCandidateQuota (h + 5) 8)
            (h := h) (i := 4) (G := G4) (low := low4) (high := high4)
            children4 hactive4 (Or.inr (Or.inr hrole4)) q
          have hchildEq : levelFiveOut = d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive (h + 5) 8)
                (d2FlowCandidateRole (h + 5) 8)
                (d2FlowCandidateQuota (h + 5) 8) (h + 1) 4
                (.node G4 low4 high4 children4)) q := by
            change d2FlowTreeChild levelFourOut q = _
            rw [hlocalOut, hsourceFour]
          have hbalanceOut : (d2FlowTreeRootData levelFiveOut).2.1 +
              (d2FlowTreeRootData levelFiveOut).2.2 =
              d2FlowTreeRootDeficit levelFiveOut := by
            rw [hchildEq]
            exact hchildBalanced
          change d2FlowStageInvInputs 8192
            (d2FlowCandidateActive (h + 5) 9)
            (d2FlowCandidateRole (h + 5) 9)
            (d2FlowCandidateQuota (h + 5) 9)
            (fun r => d2FlowCandidateCapacity (h + 5) r 9) 5 levelFiveOut
          cases h with
          | zero => omega
          | succ h =>
              cases hnodeFive : levelFiveOut with
              | node G5 low5 high5 children5 =>
                  have hbalance : low5 + high5 = G5 := by
                    have hb := hbalanceOut
                    rw [hnodeFive] at hb
                    simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hb
                  have hrecursive : ∀ r, d2FlowStageInvInputs 8192
                      (d2FlowCandidateActive (h + 6) 9)
                      (d2FlowCandidateRole (h + 6) 9)
                      (d2FlowCandidateQuota (h + 6) 9)
                      (fun s => d2FlowCandidateCapacity (h + 6) s 9) 6
                      (children5 r) := by
                    intro r
                    exact htail (children5 r)
                  simp only [d2FlowStageInvInputs, hactive5, if_true, hrole5]
                  exact ⟨hrecursive, hbalance, trivial⟩

/-- The inactive stage-nine level-four predicate is discharged by the
already-verified level-five bottom-rise gates. -/
theorem d2FlowCandidateStage9_actual_levelFour_inputs
    (h : Nat) (hh : 6 ≤ h) :
    ∀ j k m l, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 5) 9)
      (d2FlowCandidateRole (h + 5) 9)
      (d2FlowCandidateQuota (h + 5) 9)
      (fun r => d2FlowCandidateCapacity (h + 5) r 9) 4
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateRun (h + 5)
                (d2FlowTreeInitial 8192 (h + 5)) 9) j) k) m) l) := by
  intro j k m l
  have hfront := d2FlowCandidateStage9_frontiers (h + 5) (by omega)
  rcases hfront with ⟨_, _, _, _, _, _, hactive7⟩
  have hactive4 : d2FlowCandidateActive (h + 5) 9 4 = false := by
    simp [d2FlowCandidateActive, tfD2]
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun (h + 5)
            (d2FlowTreeInitial 8192 (h + 5)) 9) j) k) m) l
  have hlevelFive := d2FlowCandidateStage9_actual_levelFive_inputs
    h hh j k m l
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive (h + 5) 9)
    (d2FlowCandidateRole (h + 5) 9)
    (d2FlowCandidateQuota (h + 5) 9)
    (fun r => d2FlowCandidateCapacity (h + 5) r 9) 4 tree
  cases hnode : tree with
  | node G low high children =>
      have hrecursive : ∀ q, d2FlowStageInvInputs 8192
          (d2FlowCandidateActive (h + 5) 9)
          (d2FlowCandidateRole (h + 5) 9)
          (d2FlowCandidateQuota (h + 5) 9)
          (fun r => d2FlowCandidateCapacity (h + 5) r 9) 5
          (children q) := by
        intro q
        have hq := hlevelFive q
        change d2FlowStageInvInputs 8192
          (d2FlowCandidateActive (h + 5) 9)
          (d2FlowCandidateRole (h + 5) 9)
          (d2FlowCandidateQuota (h + 5) 9)
          (fun r => d2FlowCandidateCapacity (h + 5) r 9) 5
          (d2FlowTreeChild tree q) at hq
        rw [hnode] at hq
        simpa only [d2FlowTreeChild] using hq
      simp only [d2FlowStageInvInputs, hactive4, if_false]
      exact ⟨hrecursive, trivial⟩

set_option maxHeartbeats 10000000 in
/-- Every actual stage-nine level-three mid node satisfies the full gate. Its
sender cap and balance are children of stage eight's level-two mid cut; the
two stage-eight bottom-descending endpoint quotas pay the new reserve test. -/
theorem d2FlowCandidateStage9_actual_levelThree_inputs
    (h : Nat) (hh : 6 ≤ h) :
    ∀ j k m, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 5) 9)
      (d2FlowCandidateRole (h + 5) 9)
      (d2FlowCandidateQuota (h + 5) 9)
      (fun r => d2FlowCandidateCapacity (h + 5) r 9) 3
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (h + 5)
              (d2FlowTreeInitial 8192 (h + 5)) 9) j) k) m) := by
  intro j k m
  let before := d2FlowCandidateRun (h + 5)
    (d2FlowTreeInitial 8192 (h + 5)) 8
  have hinvGlobal := d2FlowCandidateStage7_preserves_inv (h + 1) (by omega)
  have hinvTwo := d2FlowTreeInv_grandchild (h := h + 3) before hinvGlobal j k
  have hinputsTwo := d2FlowCandidateStage8_actual_levelTwo_inputs h (by omega) j k
  have hfront := d2FlowCandidateStage8_frontiers (h + 5) (by omega)
  rcases hfront with ⟨_, _, hactive2, hrole2, _, _, _⟩
  have hinactive1 : d2FlowCandidateActive (h + 5) 8 1 = false := by
    simp [d2FlowCandidateActive, tfD2]
  cases hsourceOne : d2FlowTreeChild before j with
  | node G1 low1 high1 children1 =>
      have hinactiveChild := d2FlowStage_inactive_child
        (active := d2FlowCandidateActive (h + 5) 8)
        (role := d2FlowCandidateRole (h + 5) 8)
        (quota := d2FlowCandidateQuota (h + 5) 8)
        (h := h + 3) (i := 1) (G := G1) (low := low1)
        (high := high1) children1 hinactive1 k
      have houtputTwo : d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (h + 5)
              (d2FlowTreeInitial 8192 (h + 5)) 9) j) k =
          d2FlowStage (d2FlowCandidateActive (h + 5) 8)
            (d2FlowCandidateRole (h + 5) 8)
            (d2FlowCandidateQuota (h + 5) 8) (h + 3) 2
            (children1 k) := by
        have hprojection := d2FlowStage_child_child_projection
          (active := d2FlowCandidateActive (h + 5) 8)
          (role := d2FlowCandidateRole (h + 5) 8)
          (quota := d2FlowCandidateQuota (h + 5) 8)
          (i := 0) before j k
        change d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateStage (h + 5) 8 before) j) k = _
        rw [d2FlowCandidateStage, hprojection, hsourceOne]
        exact hinactiveChild
      have hinvTwo' := hinvTwo
      change d2FlowTreeInv 8192
        (d2FlowTreeChild (d2FlowTreeChild before j) k) at hinvTwo'
      rw [hsourceOne] at hinvTwo'
      have hinputsTwo' := hinputsTwo
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (h + 5) 8)
        (d2FlowCandidateRole (h + 5) 8)
        (d2FlowCandidateQuota (h + 5) 8)
        (fun r => d2FlowCandidateCapacity (h + 5) r 8) 2
        (d2FlowTreeChild (d2FlowTreeChild before j) k) at hinputsTwo'
      rw [hsourceOne] at hinputsTwo'
      cases hsourceTwo : children1 k with
      | node G2 low2 high2 children2 =>
          have hinvTwo'' : d2FlowTreeInv 8192
              (.node G2 low2 high2 children2) := by
            rw [show d2FlowTreeChild (D2FlowTree.node G1 low1 high1 children1) k =
              .node G2 low2 high2 children2 by
                simpa only [d2FlowTreeChild] using hsourceTwo] at hinvTwo'
            exact hinvTwo'
          have hinputsTwo'' : d2FlowStageInvInputs 8192
              (d2FlowCandidateActive (h + 5) 8)
              (d2FlowCandidateRole (h + 5) 8)
              (d2FlowCandidateQuota (h + 5) 8)
              (fun r => d2FlowCandidateCapacity (h + 5) r 8) 2
              (.node G2 low2 high2 children2) := by
            rw [show d2FlowTreeChild (D2FlowTree.node G1 low1 high1 children1) k =
              .node G2 low2 high2 children2 by
                simpa only [d2FlowTreeChild] using hsourceTwo] at hinputsTwo'
            exact hinputsTwo'
          have hchildCap := d2FlowStage_regular_child_g_bound_of_tree_inputs
            (active := d2FlowCandidateActive (h + 5) 8)
            (role := d2FlowCandidateRole (h + 5) 8)
            (quota := d2FlowCandidateQuota (h + 5) 8)
            (cap := fun r => d2FlowCandidateCapacity (h + 5) r 8)
            (.node G2 low2 high2 children2) hactive2
            (Or.inr (Or.inl hrole2)) hinvTwo'' hinputsTwo''
          have hchildBalanced := d2FlowStage_regular_child_balanced
            (active := d2FlowCandidateActive (h + 5) 8)
            (role := d2FlowCandidateRole (h + 5) 8)
            (quota := d2FlowCandidateQuota (h + 5) 8)
            (h := h + 2) (i := 2) (G := G2) (low := low2) (high := high2)
            children2 hactive2 (Or.inr (Or.inl hrole2)) m
          let levelThree := d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (h + 5)
                  (d2FlowTreeInitial 8192 (h + 5)) 9) j) k) m
          have houtputThree : levelThree = d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive (h + 5) 8)
                (d2FlowCandidateRole (h + 5) 8)
                (d2FlowCandidateQuota (h + 5) 8) (h + 3) 2
                (.node G2 low2 high2 children2)) m := by
            change d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (h + 5)
                    (d2FlowTreeInitial 8192 (h + 5)) 9) j) k) m = _
            rw [houtputTwo, hsourceTwo]
          have hcapRelation : 2 * d2FlowCandidateCapacity (h + 5) 2 8 =
              d2FlowCandidateCapacity (h + 5) 3 9 := by
            have hexp : d2FlowCandidateCapacityExponent (h + 5) 3 9 =
                d2FlowCandidateCapacityExponent (h + 5) 2 8 + 1 := by
              simp [d2FlowCandidateCapacityExponent]
              omega
            unfold d2FlowCandidateCapacity
            rw [hexp, pow_succ]
            ring
          have hfront9 := d2FlowCandidateStage9_frontiers (h + 5) (by omega)
          rcases hfront9 with ⟨_, _, _, _, hactive5, hrole5, _⟩
          have hleftReserve : d2FlowCandidateCapacity (h + 5) 3 9 ≤
              128 * d2FlowTreeRootDeficit
                (d2FlowTreeChild levelThree ⟨0, by omega⟩) := by
            have hq := d2FlowCandidateStage9_levelFour_quota_lower
              h hh j k m ⟨0, by omega⟩
            have hratio : d2FlowCandidateCapacity (h + 5) 3 9 ≤
                128 * d2FlowCandidateQuota (h + 5) 8 4 .botDesc := by
              have hc : d2FlowCandidateCapacity (h + 5) 3 9 =
                  2 ^ (3 * (h + 5)) := by
                simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
              have hq' : d2FlowCandidateQuota (h + 5) 8 4 .botDesc =
                  15 * 2 ^ (3 * (h + 5) - 7) := by
                simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
                omega
              rw [hc, hq']
              have hp : 128 * 2 ^ (3 * (h + 5) - 7) =
                  2 ^ (3 * (h + 5)) := by
                rw [show (128 : Nat) = 2 ^ 7 by norm_num, ← pow_add]
                congr 1 <;> omega
              nlinarith [hp]
            exact Nat.le_trans hratio (Nat.mul_le_mul_left 128 hq)
          have hrightReserve : d2FlowCandidateCapacity (h + 5) 3 9 ≤
              128 * d2FlowTreeRootDeficit
                (d2FlowTreeChild levelThree ⟨7, by omega⟩) := by
            have hq := d2FlowCandidateStage9_levelFour_quota_lower
              h hh j k m ⟨7, by omega⟩
            exact Nat.le_trans (by
              have hc : d2FlowCandidateCapacity (h + 5) 3 9 =
                  2 ^ (3 * (h + 5)) := by
                simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
              have hq' : d2FlowCandidateQuota (h + 5) 8 4 .botDesc =
                  15 * 2 ^ (3 * (h + 5) - 7) := by
                simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
                omega
              rw [hc, hq']
              have hp : 128 * 2 ^ (3 * (h + 5) - 7) =
                  2 ^ (3 * (h + 5)) := by
                rw [show (128 : Nat) = 2 ^ 7 by norm_num, ← pow_add]
                congr 1 <;> omega
              nlinarith [hp]) (Nat.mul_le_mul_left 128 hq)
          cases hnodeThree : levelThree with
          | node G3 low3 high3 children3 =>
              have hG : 512 * G3 ≤ d2FlowCandidateCapacity (h + 5) 3 9 := by
                have hg := hchildCap m
                rw [← houtputThree, hnodeThree] at hg
                rw [hcapRelation] at hg
                exact hg
              have hbalance : low3 + high3 = G3 := by
                have hb := hchildBalanced
                rw [← houtputThree, hnodeThree] at hb
                simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hb
              have hrecursive : ∀ q, d2FlowStageInvInputs 8192
                  (d2FlowCandidateActive (h + 5) 9)
                  (d2FlowCandidateRole (h + 5) 9)
                  (d2FlowCandidateQuota (h + 5) 9)
                  (fun r => d2FlowCandidateCapacity (h + 5) r 9) 4
                  (children3 q) := by
                intro q
                have hq := d2FlowCandidateStage9_actual_levelFour_inputs
                  h hh j k m q
                change d2FlowStageInvInputs 8192
                  (d2FlowCandidateActive (h + 5) 9)
                  (d2FlowCandidateRole (h + 5) 9)
                  (d2FlowCandidateQuota (h + 5) 9)
                  (fun r => d2FlowCandidateCapacity (h + 5) r 9) 4
                  (d2FlowTreeChild levelThree q) at hq
                rw [hnodeThree] at hq
                simpa only [d2FlowTreeChild] using hq
              have hleft : d2FlowCandidateCapacity (h + 5) 3 9 ≤
                  128 * d2FlowTreeRootDeficit (children3 ⟨0, by omega⟩) := by
                have hb := hleftReserve
                rw [hnodeThree] at hb
                simpa only [d2FlowTreeChild] using hb
              have hright : d2FlowCandidateCapacity (h + 5) 3 9 ≤
                  128 * d2FlowTreeRootDeficit (children3 ⟨7, by omega⟩) := by
                have hb := hrightReserve
                rw [hnodeThree] at hb
                simpa only [d2FlowTreeChild] using hb
              have htotal := d2FlowCandidateStage9_mid_boundary_mass_suffices
                (h + 5) (by omega) G3 hG children3 hleft
              have hgate := d2FlowCandidateStage9_mid_inputs
                (h + 5) (by omega) G3 low3 high3 hbalance hG children3
                hrecursive hleft hright htotal
              simpa [levelThree, hnodeThree] using hgate

set_option maxHeartbeats 10000000 in
/-- The full concrete input predicate for stage nine follows from its actual
level-one top-rise gates and level-three mid gates. -/
theorem d2FlowCandidateStage9_actual_inputs
    (h : Nat) (hh : 6 ≤ h) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 5) 9)
      (d2FlowCandidateRole (h + 5) 9)
      (d2FlowCandidateQuota (h + 5) 9)
      (fun r => d2FlowCandidateCapacity (h + 5) r 9) 0
      (d2FlowCandidateRun (h + 5)
        (d2FlowTreeInitial 8192 (h + 5)) 9) := by
  let before := d2FlowCandidateRun (h + 5)
    (d2FlowTreeInitial 8192 (h + 5)) 9
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive (h + 5) 9)
    (d2FlowCandidateRole (h + 5) 9)
    (d2FlowCandidateQuota (h + 5) 9)
    (fun r => d2FlowCandidateCapacity (h + 5) r 9) 0 before
  have hactive0 : d2FlowCandidateActive (h + 5) 9 0 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hinactive2 : d2FlowCandidateActive (h + 5) 9 2 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hrecursive : ∀ j k, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 5) 9)
      (d2FlowCandidateRole (h + 5) 9)
      (d2FlowCandidateQuota (h + 5) 9)
      (fun r => d2FlowCandidateCapacity (h + 5) r 9) 2
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun (h + 5)
            (d2FlowTreeInitial 8192 (h + 5)) 9) j) k) := by
    intro j k
    let levelTwo := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowCandidateRun (h + 5)
          (d2FlowTreeInitial 8192 (h + 5)) 9) j) k
    have hlevelTwo : d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (h + 5) 9)
        (d2FlowCandidateRole (h + 5) 9)
        (d2FlowCandidateQuota (h + 5) 9)
        (fun r => d2FlowCandidateCapacity (h + 5) r 9) 2 levelTwo := by
      cases hnode : levelTwo with
      | node G low high children =>
          have hrecursiveThree : ∀ m, d2FlowStageInvInputs 8192
              (d2FlowCandidateActive (h + 5) 9)
              (d2FlowCandidateRole (h + 5) 9)
              (d2FlowCandidateQuota (h + 5) 9)
              (fun r => d2FlowCandidateCapacity (h + 5) r 9) 3
              (children m) := by
            intro m
            have hm := d2FlowCandidateStage9_actual_levelThree_inputs
              h hh j k m
            change d2FlowStageInvInputs 8192
              (d2FlowCandidateActive (h + 5) 9)
              (d2FlowCandidateRole (h + 5) 9)
              (d2FlowCandidateQuota (h + 5) 9)
              (fun r => d2FlowCandidateCapacity (h + 5) r 9) 3
              (d2FlowTreeChild levelTwo m) at hm
            rw [hnode] at hm
            simpa only [d2FlowTreeChild] using hm
          simp only [d2FlowStageInvInputs, hinactive2, if_false]
          exact ⟨hrecursiveThree, trivial⟩
    simpa [levelTwo] using hlevelTwo
  have hlevelOne := d2FlowCandidateStage9_levelOne_inputs h hh hrecursive
  cases hroot : before with
  | node G low high children =>
      have hchildren : ∀ j, d2FlowStageInvInputs 8192
          (d2FlowCandidateActive (h + 5) 9)
          (d2FlowCandidateRole (h + 5) 9)
          (d2FlowCandidateQuota (h + 5) 9)
          (fun r => d2FlowCandidateCapacity (h + 5) r 9) 1
          (children j) := by
        intro j
        have hj := hlevelOne j
        change d2FlowStageInvInputs 8192
          (d2FlowCandidateActive (h + 5) 9)
          (d2FlowCandidateRole (h + 5) 9)
          (d2FlowCandidateQuota (h + 5) 9)
          (fun r => d2FlowCandidateCapacity (h + 5) r 9) 1
          (d2FlowTreeChild before j) at hj
        rw [hroot] at hj
        simpa only [d2FlowTreeChild] using hj
      simp only [d2FlowStageInvInputs, hactive0, if_false]
      exact ⟨hchildren, trivial⟩

/-- Stage nine now preserves the full saturated-aware tree invariant, closing
the actual run transition from stage eight to stage nine. -/
theorem d2FlowCandidateStage9_preserves_inv
    (h : Nat) (hh : 6 ≤ h) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (h + 5)
        (d2FlowTreeInitial 8192 (h + 5)) 10) := by
  let before := d2FlowCandidateRun (h + 5)
    (d2FlowTreeInitial 8192 (h + 5)) 9
  have hinv := d2FlowCandidateStage8_preserves_inv h (by omega)
  have hinputs := d2FlowCandidateStage9_actual_inputs h hh
  have hpres := d2FlowStage_preserves_inv_of_inputs
    (active := d2FlowCandidateActive (h + 5) 9)
    (role := d2FlowCandidateRole (h + 5) 9)
    (quota := d2FlowCandidateQuota (h + 5) 9)
    (cap := fun r => d2FlowCandidateCapacity (h + 5) r 9)
    (i := 0) before hinv hinputs
  change d2FlowTreeInv 8192
    (d2FlowCandidateStage (h + 5) 9 before)
  simpa [before, d2FlowCandidateRun, d2FlowCandidateStage] using hpres

set_option maxHeartbeats 10000000 in
/-- The actual Stage 9 output meets every Stage 10 level-four bot-descending
gate. The level-three mid cut supplies the child cap and balance; Stage 9's
bottom-rise children are native and supply both endpoint reserves. -/
theorem d2FlowCandidateStage10_actual_levelFour_inputs
    (h : Nat) (hh : 6 ≤ h) :
    ∀ j k m l, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 5) 10)
      (d2FlowCandidateRole (h + 5) 10)
      (d2FlowCandidateQuota (h + 5) 10)
      (fun r => d2FlowCandidateCapacity (h + 5) r 10) 4
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateRun (h + 5)
                (d2FlowTreeInitial 8192 (h + 5)) 10) j) k) m) l) := by
  intro j k m l
  let before := d2FlowCandidateRun (h + 5)
    (d2FlowTreeInitial 8192 (h + 5)) 9
  let levelTwo := d2FlowTreeChild (d2FlowTreeChild before j) k
  let levelThree := d2FlowTreeChild levelTwo m
  let levelFourOut := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun (h + 5)
            (d2FlowTreeInitial 8192 (h + 5)) 10) j) k) m) l
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive (h + 5) 10)
    (d2FlowCandidateRole (h + 5) 10)
    (d2FlowCandidateQuota (h + 5) 10)
    (fun r => d2FlowCandidateCapacity (h + 5) r 10) 4 levelFourOut
  have hinvGlobal := d2FlowCandidateStage8_preserves_inv h (by omega)
  have hinvTwo := d2FlowTreeInv_grandchild (h := h + 3)
    before hinvGlobal j k
  have hinputsThree := d2FlowCandidateStage9_actual_levelThree_inputs
    h hh j k m
  have hfront9 := d2FlowCandidateStage9_frontiers (h + 5) (by omega)
  rcases hfront9 with ⟨_, _, hactive3, hrole3, _, _, _⟩
  have hcapRelation :
      2 * d2FlowCandidateCapacity (h + 5) 3 9 =
        d2FlowCandidateCapacity (h + 5) 4 10 := by
    have hexp : d2FlowCandidateCapacityExponent (h + 5) 4 10 =
        d2FlowCandidateCapacityExponent (h + 5) 3 9 + 1 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    unfold d2FlowCandidateCapacity
    rw [hexp, Nat.pow_succ]
    omega
  have hproject := d2FlowStage_path4_projection
    (active := d2FlowCandidateActive (h + 5) 9)
    (role := d2FlowCandidateRole (h + 5) 9)
    (quota := d2FlowCandidateQuota (h + 5) 9)
    (h := h + 1) (i := 0) before j k m l
  have hproject' : levelFourOut = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive (h + 5) 9)
        (d2FlowCandidateRole (h + 5) 9)
        (d2FlowCandidateQuota (h + 5) 9) (h + 2) 3 levelThree) l := by
    simpa [levelFourOut, d2FlowCandidateRun, d2FlowCandidateStage,
      levelThree, levelTwo] using hproject
  cases htwo : levelTwo with
  | node G2 low2 high2 children2 =>
      have hinvTwo' : d2FlowTreeInv 8192
          (.node G2 low2 high2 children2) := by
        simpa [levelTwo, htwo] using hinvTwo
      have hinvThree := hinvTwo'.2.2.2 m
      cases hthree : levelThree with
      | node G3 low3 high3 children3 =>
          have hthree' :
              d2FlowTreeChild (D2FlowTree.node G2 low2 high2 children2) m =
                .node G3 low3 high3 children3 := by
            simpa [levelThree, htwo] using hthree
          have hthree'' : children2 m = .node G3 low3 high3 children3 := by
            simpa only [d2FlowTreeChild] using hthree'
          have hinvThree' : d2FlowTreeInv 8192
              (.node G3 low3 high3 children3) := by
            rw [← hthree'']
            exact hinvThree
          have hinputsThree' := hinputsThree
          change d2FlowStageInvInputs 8192
            (d2FlowCandidateActive (h + 5) 9)
            (d2FlowCandidateRole (h + 5) 9)
            (d2FlowCandidateQuota (h + 5) 9)
            (fun r => d2FlowCandidateCapacity (h + 5) r 9) 3 levelThree
            at hinputsThree'
          rw [hthree] at hinputsThree'
          have hchildCap := d2FlowStage_regular_child_g_bound_of_tree_inputs
            (active := d2FlowCandidateActive (h + 5) 9)
            (role := d2FlowCandidateRole (h + 5) 9)
            (quota := d2FlowCandidateQuota (h + 5) 9)
            (cap := fun r => d2FlowCandidateCapacity (h + 5) r 9)
            (stageDepth := h + 1) (i := 3) (.node G3 low3 high3 children3)
            hactive3 (Or.inr (Or.inl hrole3)) hinvThree' hinputsThree'
          have hchildBalanced := d2FlowStage_regular_child_balanced
            (active := d2FlowCandidateActive (h + 5) 9)
            (role := d2FlowCandidateRole (h + 5) 9)
            (quota := d2FlowCandidateQuota (h + 5) 9)
            (h := h + 1) (i := 3) (G := G3) (low := low3) (high := high3)
            children3 hactive3 (Or.inr (Or.inl hrole3)) l
          have hGout : 512 * d2FlowTreeRootDeficit levelFourOut ≤
              d2FlowCandidateCapacity (h + 5) 4 10 := by
            have hg := hchildCap l
            have hprojectNode := hproject'
            rw [hthree] at hprojectNode
            rw [← hprojectNode, hcapRelation] at hg
            exact hg
          have hbalanceOut : (d2FlowTreeRootData levelFourOut).2.1 +
              (d2FlowTreeRootData levelFourOut).2.2 =
                d2FlowTreeRootDeficit levelFourOut := by
            have hb := hchildBalanced
            have hprojectNode := hproject'
            rw [hthree] at hprojectNode
            rw [← hprojectNode] at hb
            exact hb
          cases hnode : levelFourOut with
          | node G low high children =>
              have hbalance : low + high = G := by
                have hb := hbalanceOut
                rw [hnode] at hb
                simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hb
              have hG : 512 * G ≤ d2FlowCandidateCapacity (h + 5) 4 10 := by
                simpa [hnode, d2FlowTreeRootDeficit] using hGout
              have hreserve0 : d2FlowTreeRootDeficit
                  (children ⟨0, by omega⟩) = 8192 * 8 ^ h := by
                have hr := d2FlowCandidateStage9_actual_levelFive_native
                  h hh j k m l ⟨0, by omega⟩
                change d2FlowTreeRootDeficit
                  (d2FlowTreeChild levelFourOut ⟨0, by omega⟩) = _ at hr
                rw [hnode] at hr
                simpa only [d2FlowTreeChild] using hr
              have hreserve7 : d2FlowTreeRootDeficit
                  (children ⟨7, by omega⟩) = 8192 * 8 ^ h := by
                have hr := d2FlowCandidateStage9_actual_levelFive_native
                  h hh j k m l ⟨7, by omega⟩
                change d2FlowTreeRootDeficit
                  (d2FlowTreeChild levelFourOut ⟨7, by omega⟩) = _ at hr
                rw [hnode] at hr
                simpa only [d2FlowTreeChild] using hr
              have hcap8 := d2FlowCandidateStage8_capacity_eq_native h
              have hcapShift : 16 * d2FlowCandidateCapacity (h + 5) 4 10 =
                  d2FlowCandidateCapacity (h + 5) 4 8 := by
                have he : d2FlowCandidateCapacityExponent (h + 5) 4 8 =
                    d2FlowCandidateCapacityExponent (h + 5) 4 10 + 4 := by
                  simp [d2FlowCandidateCapacityExponent]
                  omega
                rw [show d2FlowCandidateCapacity (h + 5) 4 8 =
                    2 ^ d2FlowCandidateCapacityExponent (h + 5) 4 8 by
                      simp [d2FlowCandidateCapacity]]
                rw [show d2FlowCandidateCapacity (h + 5) 4 10 =
                    2 ^ d2FlowCandidateCapacityExponent (h + 5) 4 10 by
                      simp [d2FlowCandidateCapacity], he, pow_add]
                ring
              have hreserveCap : d2FlowCandidateCapacity (h + 5) 4 10 ≤
                  128 * (8192 * 8 ^ h) := by
                rw [hcap8] at hcapShift
                nlinarith
              have hleft : d2FlowCandidateCapacity (h + 5) 4 10 ≤
                  128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
                rw [hreserve0]
                exact hreserveCap
              have hright : d2FlowCandidateCapacity (h + 5) 4 10 ≤
                  128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩) := by
                rw [hreserve7]
                exact hreserveCap
              have htotal := d2FlowCandidateStage10_boundary_mass_suffices
                (h + 5) (by omega) G hG children hleft
              exact d2FlowCandidateStage10_botDesc_inputs
                (h + 5) (by omega) G low high hbalance hG children
                hleft hright htotal

/-- An inactive parent also preserves child-cover: it keeps its own deficit,
while the recursively staged child roots can only increase. -/
theorem d2FlowStage_inactive_child_cover {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = false)
    (hcover : G ≤ d2FlowTotal (fun j =>
      d2FlowTreeRootDeficit (children j))) :
    d2FlowTreeRootDeficit
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) ≤
      (Finset.univ.sum fun j : Fin 8 =>
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)) := by
  have hsum : (Finset.univ.sum fun j : Fin 8 =>
      d2FlowTreeRootDeficit (children j)) ≤
      (Finset.univ.sum fun j : Fin 8 =>
        d2FlowTreeRootDeficit
          (d2FlowStage active role quota h (i + 1) (children j))) := by
    apply Finset.sum_le_sum
    intro j hj
    exact d2FlowStage_root_deficit_mono active role quota (i + 1) (children j)
  have hcover' : G ≤ Finset.univ.sum (fun j : Fin 8 =>
      d2FlowTreeRootDeficit (children j)) := by
    simpa [d2FlowTotal] using hcover
  simp [d2FlowStage, d2FlowTreeRootDeficit, d2FlowTreeChild, ha]
  exact le_trans hcover' hsum

/-- Stage nine's level-three mid cut leaves its quota in every actual
level-three root of the stage-ten input tree. This supplies the endpoint
reserve needed by the next level-two sender gate. -/
theorem d2FlowCandidateStage10_levelThree_endpoint_reserve
    (h : Nat) (hh : 6 ≤ h) :
    ∀ j k m, d2FlowCandidateCapacity (h + 5) 2 10 ≤
      128 *
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateRun (h + 5)
                (d2FlowTreeInitial 8192 (h + 5)) 10) j) k) m) := by
  intro j k m
  let before := d2FlowCandidateRun (h + 5)
    (d2FlowTreeInitial 8192 (h + 5)) 9
  let sourceOne := d2FlowTreeChild before j
  let sourceTwo := d2FlowTreeChild sourceOne k
  let sourceThree := d2FlowTreeChild sourceTwo m
  let outputThree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowCandidateRun (h + 5)
          (d2FlowTreeInitial 8192 (h + 5)) 10) j) k) m
  have hfront := d2FlowCandidateStage9_frontiers (h + 5) (by omega)
  rcases hfront with ⟨_, _, hactive3, hrole3, _, _, _⟩
  have hfrontInactive : d2FlowCandidateActive (h + 5) 9 2 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hprojectRoot := d2FlowStage_child_child_projection
    (active := d2FlowCandidateActive (h + 5) 9)
    (role := d2FlowCandidateRole (h + 5) 9)
    (quota := d2FlowCandidateQuota (h + 5) 9)
    (h := h + 3) (i := 0) before j k
  have hprojectOne := d2FlowStage_child_child_projection
    (active := d2FlowCandidateActive (h + 5) 9)
    (role := d2FlowCandidateRole (h + 5) 9)
    (quota := d2FlowCandidateQuota (h + 5) 9)
    (h := h + 2) (i := 1) sourceOne k m
  cases hsourceTwo : sourceTwo with
  | node G2 low2 high2 children2 =>
      have hinactiveChild := d2FlowStage_inactive_child
        (active := d2FlowCandidateActive (h + 5) 9)
        (role := d2FlowCandidateRole (h + 5) 9)
        (quota := d2FlowCandidateQuota (h + 5) 9)
        (h := h + 2) (i := 2) (G := G2) (low := low2)
        (high := high2) children2 hfrontInactive m
      have houtput : outputThree =
          d2FlowStage (d2FlowCandidateActive (h + 5) 9)
            (d2FlowCandidateRole (h + 5) 9)
            (d2FlowCandidateQuota (h + 5) 9) (h + 2) 3 sourceThree := by
        have hroot := congrArg (fun tree => d2FlowTreeChild tree m) hprojectRoot
        change outputThree = _
        calc
          outputThree = d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive (h + 5) 9)
                  (d2FlowCandidateRole (h + 5) 9)
                  (d2FlowCandidateQuota (h + 5) 9) (h + 4) 1 sourceOne) k) m := by
                simpa [outputThree, before, sourceOne, d2FlowCandidateRun,
                  d2FlowCandidateStage] using hroot
          _ = d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive (h + 5) 9)
                (d2FlowCandidateRole (h + 5) 9)
                (d2FlowCandidateQuota (h + 5) 9) (h + 3) 2 sourceTwo) m := by
                simpa [sourceTwo] using hprojectOne
          _ = d2FlowStage (d2FlowCandidateActive (h + 5) 9)
                (d2FlowCandidateRole (h + 5) 9)
                (d2FlowCandidateQuota (h + 5) 9) (h + 2) 3 sourceThree := by
                simpa [sourceThree, hsourceTwo, d2FlowTreeChild] using hinactiveChild
      cases hsourceThree : children2 m with
      | node G3 low3 high3 children3 =>
        have hrootStep := d2FlowStage_active_node_deficit
          (active := d2FlowCandidateActive (h + 5) 9)
          (role := d2FlowCandidateRole (h + 5) 9)
          (quota := d2FlowCandidateQuota (h + 5) 9)
          (h := h + 1) (i := 3) (G := G3) (low := low3)
          (high := high3) children3 hactive3
        have hquota : d2FlowCandidateQuota (h + 5) 9 3 .mid =
            15 * 2 ^ (3 * (h + 5) - 12) := by
          simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
        have hcap : d2FlowCandidateCapacity (h + 5) 2 10 =
            2 ^ (3 * (h + 5) - 5) := by
          simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
          omega
        have hscale : 3 * (h + 5) - 5 = 7 + (3 * (h + 5) - 12) := by omega
        have hquotaReserve : d2FlowCandidateCapacity (h + 5) 2 10 ≤
            128 * d2FlowCandidateQuota (h + 5) 9 3 .mid := by
          rw [hcap, hquota, hscale, pow_add]
          norm_num
        have hrootStep' : d2FlowTreeRootDeficit
            (d2FlowStage (d2FlowCandidateActive (h + 5) 9)
              (d2FlowCandidateRole (h + 5) 9)
              (d2FlowCandidateQuota (h + 5) 9) (h + 2) 3
              (.node G3 low3 high3 children3)) =
            G3 + d2FlowCandidateQuota (h + 5) 9 3 .mid := by
          rw [hrole3] at hrootStep
          exact hrootStep
        have hsourceThree' : sourceThree = .node G3 low3 high3 children3 := by
          change d2FlowTreeChild sourceTwo m = .node G3 low3 high3 children3
          rw [hsourceTwo]
          exact hsourceThree
        change d2FlowCandidateCapacity (h + 5) 2 10 ≤ 128 *
          d2FlowTreeRootDeficit outputThree
        rw [houtput, hsourceThree', hrootStep']
        omega

set_option maxHeartbeats 10000000 in
/-- Stage nine's level-one top-rise cut supplies the sender cap and balanced
endpoints for every actual stage-ten level-two node. -/
theorem d2FlowCandidateStage10_levelTwo_inherited_state
    (h : Nat) (hh : 6 ≤ h) :
    ∀ j k, 512 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (h + 5)
              (d2FlowTreeInitial 8192 (h + 5)) 10) j) k) ≤
        d2FlowCandidateCapacity (h + 5) 2 10 ∧
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (h + 5)
              (d2FlowTreeInitial 8192 (h + 5)) 10) j) k)).2.1 +
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (h + 5)
              (d2FlowTreeInitial 8192 (h + 5)) 10) j) k)).2.2 =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (h + 5)
              (d2FlowTreeInitial 8192 (h + 5)) 10) j) k) := by
  intro j k
  let before := d2FlowCandidateRun (h + 5)
    (d2FlowTreeInitial 8192 (h + 5)) 9
  let sourceOne := d2FlowTreeChild before j
  let outputTwo := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowCandidateRun (h + 5)
        (d2FlowTreeInitial 8192 (h + 5)) 10) j) k
  have hfront := d2FlowCandidateStage9_frontiers (h + 5) (by omega)
  rcases hfront with ⟨hactive1, hrole1, _, _, _, _, _⟩
  have hinactive0 : d2FlowCandidateActive (h + 5) 9 0 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hprojection := d2FlowStage_child_child_projection
    (active := d2FlowCandidateActive (h + 5) 9)
    (role := d2FlowCandidateRole (h + 5) 9)
    (quota := d2FlowCandidateQuota (h + 5) 9)
    (h := h + 3) (i := 0) before j k
  have hrootInputs := d2FlowCandidateStage9_actual_inputs h hh
  have hrootInv := d2FlowCandidateStage8_preserves_inv h (by omega)
  cases hbefore : before with
  | node G0 low0 high0 children0 =>
      have hrootInv' : d2FlowTreeInv 8192
          (.node G0 low0 high0 children0) := by
        simpa [before, hbefore] using hrootInv
      have hrootInputs' : d2FlowStageInvInputs 8192
          (d2FlowCandidateActive (h + 5) 9)
          (d2FlowCandidateRole (h + 5) 9)
          (d2FlowCandidateQuota (h + 5) 9)
          (fun q => d2FlowCandidateCapacity (h + 5) q 9) 0
          (.node G0 low0 high0 children0) := by
        simpa [before, hbefore] using hrootInputs
      simp only [d2FlowStageInvInputs, hinactive0, if_false] at hrootInputs'
      have hinvOne := hrootInv'.2.2.2 j
      have hinputsOne := hrootInputs'.1 j
      cases hone : children0 j with
      | node G1 low1 high1 children1 =>
          have hprojection' := hprojection
          rw [hbefore] at hprojection'
          change d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive (h + 5) 9)
                  (d2FlowCandidateRole (h + 5) 9)
                  (d2FlowCandidateQuota (h + 5) 9) (h + 5) 0
                  (.node G0 low0 high0 children0)) j) k =
            d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive (h + 5) 9)
                (d2FlowCandidateRole (h + 5) 9)
                (d2FlowCandidateQuota (h + 5) 9) (h + 4) 1
                (children0 j)) k at hprojection'
          rw [hone] at hprojection'
          have hinvOne' : d2FlowTreeInv 8192
              (.node G1 low1 high1 children1) := by
            rw [hone] at hinvOne
            exact hinvOne
          have hinputsOne' : d2FlowStageInvInputs 8192
              (d2FlowCandidateActive (h + 5) 9)
              (d2FlowCandidateRole (h + 5) 9)
              (d2FlowCandidateQuota (h + 5) 9)
              (fun q => d2FlowCandidateCapacity (h + 5) q 9) 1
              (.node G1 low1 high1 children1) := by
            rw [hone] at hinputsOne
            exact hinputsOne
          have hchildCap := d2FlowStage_regular_child_g_bound_of_tree_inputs
            (active := d2FlowCandidateActive (h + 5) 9)
            (role := d2FlowCandidateRole (h + 5) 9)
            (quota := d2FlowCandidateQuota (h + 5) 9)
            (cap := fun q => d2FlowCandidateCapacity (h + 5) q 9)
            (stageDepth := h + 3) (i := 1)
            (.node G1 low1 high1 children1) hactive1
            (Or.inl hrole1) hinvOne' hinputsOne'
          have hchildBalance := d2FlowStage_regular_child_balanced
            (active := d2FlowCandidateActive (h + 5) 9)
            (role := d2FlowCandidateRole (h + 5) 9)
            (quota := d2FlowCandidateQuota (h + 5) 9)
            (h := h + 3) (i := 1) (G := G1) (low := low1)
            (high := high1) children1 hactive1 (Or.inl hrole1) k
          have hproject : outputTwo = d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive (h + 5) 9)
                (d2FlowCandidateRole (h + 5) 9)
                (d2FlowCandidateQuota (h + 5) 9) (h + 4) 1
                (.node G1 low1 high1 children1)) k := by
            calc
              outputTwo = d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowCandidateStage (h + 5) 9 before) j) k := rfl
              _ = d2FlowTreeChild
                  (d2FlowStage (d2FlowCandidateActive (h + 5) 9)
                    (d2FlowCandidateRole (h + 5) 9)
                    (d2FlowCandidateQuota (h + 5) 9) (h + 4) 1
                    (.node G1 low1 high1 children1)) k := by
                    unfold d2FlowCandidateStage
                    rw [hbefore]
                    exact hprojection'
          have hcapacity : 2 * d2FlowCandidateCapacity (h + 5) 1 9 =
              d2FlowCandidateCapacity (h + 5) 2 10 := by
            have hexp : d2FlowCandidateCapacityExponent (h + 5) 2 10 =
                d2FlowCandidateCapacityExponent (h + 5) 1 9 + 1 := by
              simp [d2FlowCandidateCapacityExponent]
              omega
            unfold d2FlowCandidateCapacity
            rw [hexp, pow_succ]
            ring
          constructor
          · change 512 * d2FlowTreeRootDeficit outputTwo ≤
              d2FlowCandidateCapacity (h + 5) 2 10
            rw [hproject]
            have hbound := hchildCap k
            rw [hcapacity] at hbound
            exact hbound
          · change (d2FlowTreeRootData outputTwo).2.1 +
                (d2FlowTreeRootData outputTwo).2.2 =
              d2FlowTreeRootDeficit outputTwo
            rw [hproject]
            exact hchildBalance

set_option maxHeartbeats 10000000 in
/-- Every actual level-two sender in the Stage 10 input tree satisfies its
complete mid gate: the inherited cap/balance, Stage 9 endpoint reserves, and
the already established level-four recursive gates meet the local contract. -/
theorem d2FlowCandidateStage10_actual_levelTwo_inputs
    (h : Nat) (hh : 6 ≤ h) :
    ∀ j k, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 5) 10)
      (d2FlowCandidateRole (h + 5) 10)
      (d2FlowCandidateQuota (h + 5) 10)
      (fun q => d2FlowCandidateCapacity (h + 5) q 10) 2
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun (h + 5)
            (d2FlowTreeInitial 8192 (h + 5)) 10) j) k) := by
  intro j k
  let outputTwo := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowCandidateRun (h + 5)
        (d2FlowTreeInitial 8192 (h + 5)) 10) j) k
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive (h + 5) 10)
    (d2FlowCandidateRole (h + 5) 10)
    (d2FlowCandidateQuota (h + 5) 10)
    (fun q => d2FlowCandidateCapacity (h + 5) q 10) 2 outputTwo
  have hstate := d2FlowCandidateStage10_levelTwo_inherited_state h hh j k
  have hreserve := d2FlowCandidateStage10_levelThree_endpoint_reserve h hh j k
  have hinactive3 : d2FlowCandidateActive (h + 5) 10 3 = false := by
    simp [d2FlowCandidateActive, tfD2]
  cases hnode : outputTwo with
  | node G low high children =>
      have hbalance : low + high = G := by
        have hb := hstate.2
        change (d2FlowTreeRootData outputTwo).2.1 +
          (d2FlowTreeRootData outputTwo).2.2 = d2FlowTreeRootDeficit outputTwo at hb
        rw [hnode] at hb
        simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hb
      have hG : 512 * G ≤ d2FlowCandidateCapacity (h + 5) 2 10 := by
        have hg := hstate.1
        change 512 * d2FlowTreeRootDeficit outputTwo ≤
          d2FlowCandidateCapacity (h + 5) 2 10 at hg
        rw [hnode] at hg
        simpa [d2FlowTreeRootDeficit] using hg
      have hrecursive : ∀ m, d2FlowStageInvInputs 8192
          (d2FlowCandidateActive (h + 5) 10)
          (d2FlowCandidateRole (h + 5) 10)
          (d2FlowCandidateQuota (h + 5) 10)
          (fun q => d2FlowCandidateCapacity (h + 5) q 10) 3
          (children m) := by
        intro m
        cases hchild : children m with
        | node G3 low3 high3 children3 =>
            have hrecursive4 : ∀ l, d2FlowStageInvInputs 8192
                (d2FlowCandidateActive (h + 5) 10)
                (d2FlowCandidateRole (h + 5) 10)
                (d2FlowCandidateQuota (h + 5) 10)
                (fun q => d2FlowCandidateCapacity (h + 5) q 10) 4
                (children3 l) := by
              intro l
              have hf := d2FlowCandidateStage10_actual_levelFour_inputs
                h hh j k m l
              change d2FlowStageInvInputs 8192
                (d2FlowCandidateActive (h + 5) 10)
                (d2FlowCandidateRole (h + 5) 10)
                (d2FlowCandidateQuota (h + 5) 10)
                (fun q => d2FlowCandidateCapacity (h + 5) q 10) 4
                (d2FlowTreeChild (d2FlowTreeChild outputTwo m) l) at hf
              have hchildOut : d2FlowTreeChild outputTwo m =
                  .node G3 low3 high3 children3 := by
                rw [hnode]
                exact hchild
              rw [hchildOut] at hf
              simpa only [d2FlowTreeChild] using hf
            simp only [d2FlowStageInvInputs, hinactive3, if_false]
            exact ⟨hrecursive4, trivial⟩
      have hleft : d2FlowCandidateCapacity (h + 5) 2 10 ≤
          128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
        have hl := hreserve ⟨0, by omega⟩
        change d2FlowCandidateCapacity (h + 5) 2 10 ≤
          128 * d2FlowTreeRootDeficit (d2FlowTreeChild outputTwo ⟨0, by omega⟩) at hl
        rw [hnode] at hl
        simpa only [d2FlowTreeChild] using hl
      have hright : d2FlowCandidateCapacity (h + 5) 2 10 ≤
          128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩) := by
        have hr := hreserve ⟨7, by omega⟩
        change d2FlowCandidateCapacity (h + 5) 2 10 ≤
          128 * d2FlowTreeRootDeficit (d2FlowTreeChild outputTwo ⟨7, by omega⟩) at hr
        rw [hnode] at hr
        simpa only [d2FlowTreeChild] using hr
      have htotal := d2FlowCandidateStage10_mid_boundary_mass_suffices
        (h + 5) (by omega) G hG children hleft
      exact d2FlowCandidateStage10_mid_inputs
        (h + 5) (by omega) G low high hbalance hG children hrecursive
        hleft hright htotal

set_option maxHeartbeats 10000000 in
/-- The Stage 10 level-four cut produces actual Stage 11 level-five
bot-descending sender inputs. Its children are the transported native
level-six reserves proved above. -/
theorem d2FlowCandidateStage11_actual_levelFive_inputs
    (depth : Nat) (hd : 6 ≤ depth) :
    ∀ j k m l q, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (depth + 6) 11)
      (d2FlowCandidateRole (depth + 6) 11)
      (d2FlowCandidateQuota (depth + 6) 11)
      (fun r => d2FlowCandidateCapacity (depth + 6) r 11) 5
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (depth + 6)
                  (d2FlowTreeInitial 8192 (depth + 6)) 11) j) k) m) l) q) := by
  intro j k m l q
  let h := Nat.succ depth
  have hh : 7 ≤ h := by dsimp [h]; omega
  let d := h + 5
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 10
  let levelTwo := d2FlowTreeChild (d2FlowTreeChild before j) k
  let levelThree := d2FlowTreeChild levelTwo m
  let levelFour := d2FlowTreeChild levelThree l
  let levelFourOut := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
                (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 11) j) k) m) l
  let levelFiveOut := d2FlowTreeChild levelFourOut q
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 11)
    (d2FlowCandidateRole d 11)
    (d2FlowCandidateQuota d 11)
    (fun r => d2FlowCandidateCapacity d r 11) 5 levelFiveOut
  have hinvGlobal := d2FlowCandidateStage9_preserves_inv h (by omega)
  have hinvTwo := d2FlowTreeInv_grandchild (h := h + 3)
    before hinvGlobal j k
  have hinvFour := d2FlowTreeInv_grandchild (h := h + 1)
    levelTwo hinvTwo m l
  have hinputsFour := d2FlowCandidateStage10_actual_levelFour_inputs
    h (by omega) j k m l
  have hfront10 := d2FlowCandidateStage10_frontiers d (by omega)
  rcases hfront10 with ⟨_, _, _, _, hactive4, hrole4, _⟩
  have hinactive3 : d2FlowCandidateActive d 10 3 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hcapRelation :
      2 * d2FlowCandidateCapacity d 4 10 =
        d2FlowCandidateCapacity d 5 11 := by
    have hexp : d2FlowCandidateCapacityExponent d 5 11 =
        d2FlowCandidateCapacityExponent d 4 10 + 1 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    unfold d2FlowCandidateCapacity
    rw [hexp, Nat.pow_succ]
    omega
  have hprojectFour := d2FlowStage_path4_projection
    (active := d2FlowCandidateActive d 10)
    (role := d2FlowCandidateRole d 10)
    (quota := d2FlowCandidateQuota d 10)
    (h := h + 1) (i := 0) before j k m l
  have hprojectFour' : levelFourOut = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 10)
        (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
        (h + 2) 3 levelThree) l := by
    simpa [levelFourOut, d, before, d2FlowCandidateRun,
      d2FlowCandidateStage, levelThree, levelTwo] using hprojectFour
  cases htwo : levelTwo with
  | node G2 low2 high2 children2 =>
      have hinvTwo' : d2FlowTreeInv 8192
          (.node G2 low2 high2 children2) := by
        simpa [levelTwo, htwo] using hinvTwo
      cases hthree : levelThree with
      | node G3 low3 high3 children3 =>
          cases hfour : levelFour with
          | node G4 low4 high4 children4 =>
              have hinvFourNode : d2FlowTreeInv 8192
                  (.node G4 low4 high4 children4) := by
                rw [← hfour]
                exact hinvFour
              have hinputsFour' := hinputsFour
              change d2FlowStageInvInputs 8192
                (d2FlowCandidateActive d 10)
                (d2FlowCandidateRole d 10)
                (d2FlowCandidateQuota d 10)
                (fun r => d2FlowCandidateCapacity d r 10) 4 levelFour
                at hinputsFour'
              rw [hfour] at hinputsFour'
              have hchildCap := d2FlowStage_regular_child_g_bound_of_tree_inputs
                (active := d2FlowCandidateActive d 10)
                (role := d2FlowCandidateRole d 10)
                (quota := d2FlowCandidateQuota d 10)
                (cap := fun r => d2FlowCandidateCapacity d r 10)
                (stageDepth := h) (i := 4)
                (.node G4 low4 high4 children4) hactive4
                (Or.inr (Or.inr hrole4)) hinvFourNode hinputsFour'
              have hchildBalanced := d2FlowStage_regular_child_balanced
                (active := d2FlowCandidateActive d 10)
                (role := d2FlowCandidateRole d 10)
                (quota := d2FlowCandidateQuota d 10)
                (h := h) (i := 4) (G := G4) (low := low4) (high := high4)
                children4 hactive4 (Or.inr (Or.inr hrole4)) q
              have hlevelFourEq : levelFour = children3 l := by
                dsimp [levelFour]
                rw [hthree]
                rfl
              have hlevelFourOutStage : levelFourOut =
                  d2FlowStage (d2FlowCandidateActive d 10)
                    (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
                    (h + 1) 4 levelFour := by
                calc
                  levelFourOut = d2FlowTreeChild
                      (d2FlowStage (d2FlowCandidateActive d 10)
                        (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
                        (h + 2) 3 levelThree) l := hprojectFour'
                  _ = d2FlowStage (d2FlowCandidateActive d 10)
                      (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
                      (h + 1) 4 (children3 l) := by
                        rw [hthree]
                        exact d2FlowStage_inactive_child
                          (active := d2FlowCandidateActive d 10)
                          (role := d2FlowCandidateRole d 10)
                          (quota := d2FlowCandidateQuota d 10)
                          (h := h + 1) (i := 3)
                          (G := G3) (low := low3) (high := high3)
                          children3 hinactive3 l
                  _ = d2FlowStage (d2FlowCandidateActive d 10)
                      (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
                      (h + 1) 4 levelFour := by
                        exact congrArg
                          (d2FlowStage (d2FlowCandidateActive d 10)
                            (d2FlowCandidateRole d 10)
                            (d2FlowCandidateQuota d 10) (h + 1) 4)
                          hlevelFourEq.symm
              have hlevelFiveOutStage : levelFiveOut =
                  d2FlowTreeChild
                    (d2FlowStage (d2FlowCandidateActive d 10)
                      (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
                      (h + 1) 4 levelFour) q := by
                have heq := congrArg (fun t => d2FlowTreeChild t q)
                  hlevelFourOutStage
                simpa [levelFiveOut] using heq
              have hlevelFiveOutStage' : levelFiveOut =
                  d2FlowTreeChild
                    (d2FlowStage (d2FlowCandidateActive d 10)
                      (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
                      (h + 1) 4 (.node G4 low4 high4 children4)) q := by
                simpa [hfour] using hlevelFiveOutStage
              have hGout : 512 * d2FlowTreeRootDeficit levelFiveOut ≤
                  d2FlowCandidateCapacity d 5 11 := by
                have hg := hchildCap q
                rw [← hlevelFiveOutStage', hcapRelation] at hg
                exact hg
              have hbalanceOut :
                  (d2FlowTreeRootData levelFiveOut).2.1 +
                    (d2FlowTreeRootData levelFiveOut).2.2 =
                    d2FlowTreeRootDeficit levelFiveOut := by
                have hb := hchildBalanced
                rw [← hlevelFiveOutStage'] at hb
                exact hb
              change D2FlowTree (depth + 1) at levelFiveOut
              cases hnode : levelFiveOut with
              | node G5 low5 high5 children5 =>
                  have hbalance : low5 + high5 = G5 := by
                    have hb := hbalanceOut
                    rw [hnode] at hb
                    simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hb
                  have hG : 512 * G5 ≤ d2FlowCandidateCapacity d 5 11 := by
                    simpa [hnode, d2FlowTreeRootDeficit] using hGout
                  have hreserve0 : d2FlowTreeRootDeficit
                      (children5 ⟨0, by omega⟩) = 8192 * 8 ^ (h - 1) := by
                    have hr := d2FlowCandidateStage10_actual_levelSix_native
                      (h - 1) (by omega) j k m l q ⟨0, by omega⟩
                    have hr' : d2FlowTreeRootDeficit
                        (d2FlowTreeChild levelFiveOut ⟨0, by omega⟩) =
                        8192 * 8 ^ (h - 1) := by
                      simpa [show (h - 1) + 6 = h + 5 by omega] using hr
                    rw [hnode] at hr'
                    simpa only [d2FlowTreeChild] using hr'
                  have hreserve7 : d2FlowTreeRootDeficit
                      (children5 ⟨7, by omega⟩) = 8192 * 8 ^ (h - 1) := by
                    have hr := d2FlowCandidateStage10_actual_levelSix_native
                      (h - 1) (by omega) j k m l q ⟨7, by omega⟩
                    have hr' : d2FlowTreeRootDeficit
                        (d2FlowTreeChild levelFiveOut ⟨7, by omega⟩) =
                        8192 * 8 ^ (h - 1) := by
                      simpa [show (h - 1) + 6 = h + 5 by omega] using hr
                    rw [hnode] at hr'
                    simpa only [d2FlowTreeChild] using hr'
                  have hcapShift : d2FlowCandidateCapacity d 5 11 =
                      d2FlowCandidateCapacity (h + 4) 4 8 := by
                    simp [d, d2FlowCandidateCapacity,
                      d2FlowCandidateCapacityExponent]
                    omega
                  have hcapNative := d2FlowCandidateStage8_capacity_eq_native
                    (h - 1)
                  have hreserveCap : d2FlowCandidateCapacity d 5 11 ≤
                      128 * (8192 * 8 ^ (h - 1)) := by
                    rw [hcapShift]
                    exact hcapNative.le
                  have hleft : d2FlowCandidateCapacity d 5 11 ≤
                      128 * d2FlowTreeRootDeficit
                        (children5 ⟨0, by omega⟩) := by
                    rw [hreserve0]
                    exact hreserveCap
                  have hright : d2FlowCandidateCapacity d 5 11 ≤
                      128 * d2FlowTreeRootDeficit
                        (children5 ⟨7, by omega⟩) := by
                    rw [hreserve7]
                    exact hreserveCap
                  have htotal := d2FlowCandidateStage11_boundary_mass_suffices
                    d (by omega) G5 hG children5 hleft
                  exact d2FlowCandidateStage11_botDesc_inputs
                    d (by omega) G5 low5 high5 hbalance hG children5
                    hleft hright htotal

set_option maxHeartbeats 10000000 in
/-- Stage 10's actual level-four bottom-descending quota supplies the endpoint
reserve required by each Stage 11 level-three mid sender. -/
theorem d2FlowCandidateStage11_levelThree_endpoint_reserve
    (depth : Nat) (hd : 6 ≤ depth) :
    ∀ j k m l, d2FlowCandidateCapacity (depth + 6) 3 11 ≤
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (depth + 6)
                  (d2FlowTreeInitial 8192 (depth + 6)) 11) j) k) m) l) := by
  intro j k m l
  let h := Nat.succ depth
  have hh : 7 ≤ h := by dsimp [h]; omega
  let d := h + 5
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 10
  let sourceThree := d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild before j) k) m
  let sourceFour := d2FlowTreeChild sourceThree l
  let outputFour := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 11) j) k) m) l
  have hfront := d2FlowCandidateStage10_frontiers d (by omega)
  rcases hfront with ⟨_, _, _, _, hactive4, hrole4, _⟩
  have hinactive3 : d2FlowCandidateActive d 10 3 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hproject := d2FlowStage_path4_projection
    (active := d2FlowCandidateActive d 10)
    (role := d2FlowCandidateRole d 10)
    (quota := d2FlowCandidateQuota d 10)
    (h := h + 1) (i := 0) before j k m l
  have hproject' : outputFour =
      d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 10)
          (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
          (h + 2) 3 sourceThree) l := by
    simpa [outputFour, d, before, d2FlowCandidateRun,
      d2FlowCandidateStage, sourceThree] using hproject
  cases hthree : sourceThree with
  | node G3 low3 high3 children3 =>
      have hsourceFour : sourceFour = children3 l := by
        dsimp [sourceFour]
        rw [hthree]
        rfl
      have houtputStage : outputFour =
          d2FlowStage (d2FlowCandidateActive d 10)
            (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
            (h + 1) 4 sourceFour := by
        calc
          outputFour = d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive d 10)
                (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
                (h + 2) 3 sourceThree) l := hproject'
          _ = d2FlowStage (d2FlowCandidateActive d 10)
              (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
              (h + 1) 4 (children3 l) := by
                rw [hthree]
                exact d2FlowStage_inactive_child
                  (active := d2FlowCandidateActive d 10)
                  (role := d2FlowCandidateRole d 10)
                  (quota := d2FlowCandidateQuota d 10)
                  (h := h + 1) (i := 3)
                  (G := G3) (low := low3) (high := high3)
                  children3 hinactive3 l
          _ = d2FlowStage (d2FlowCandidateActive d 10)
              (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
              (h + 1) 4 sourceFour := by
                exact congrArg
                  (d2FlowStage (d2FlowCandidateActive d 10)
                    (d2FlowCandidateRole d 10)
                    (d2FlowCandidateQuota d 10) (h + 1) 4)
                  hsourceFour.symm
      cases hfour : sourceFour with
      | node G4 low4 high4 children4 =>
          have hstep := d2FlowStage_active_node_deficit
            (active := d2FlowCandidateActive d 10)
            (role := d2FlowCandidateRole d 10)
            (quota := d2FlowCandidateQuota d 10)
            (h := h) (i := 4) (G := G4) (low := low4) (high := high4)
            children4 hactive4
          rw [hrole4] at hstep
          have hroot : d2FlowTreeRootDeficit outputFour =
              G4 + d2FlowCandidateQuota d 10 4 .botDesc := by
            rw [houtputStage, hfour]
            exact hstep
          have hcap : d2FlowCandidateCapacity d 3 11 =
              2 ^ (3 * d - 4) := by
            simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
            omega
          have hquota : d2FlowCandidateQuota d 10 4 .botDesc =
              15 * 2 ^ (3 * d - 11) := by
            simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
            omega
          have hscale : 3 * d - 4 = 7 + (3 * d - 11) := by omega
          have hcapQuota : d2FlowCandidateCapacity d 3 11 ≤
              128 * d2FlowCandidateQuota d 10 4 .botDesc := by
            rw [hcap, hquota, hscale, pow_add]
            norm_num
          change d2FlowCandidateCapacity d 3 11 ≤
            128 * d2FlowTreeRootDeficit outputFour
          rw [hroot]
          nlinarith

set_option maxHeartbeats 10000000 in
/-- The actual Stage 11 level-three mid sender gates follow from Stage 10's
level-two cut, the level-four quota reserves, and the Stage 11 level-five
gates for the recursive tail. -/
theorem d2FlowCandidateStage11_actual_levelThree_inputs
    (depth : Nat) (hd : 6 ≤ depth) :
    ∀ j k m, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (depth + 6) 11)
      (d2FlowCandidateRole (depth + 6) 11)
      (d2FlowCandidateQuota (depth + 6) 11)
      (fun r => d2FlowCandidateCapacity (depth + 6) r 11) 3
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (depth + 6)
              (d2FlowTreeInitial 8192 (depth + 6)) 11) j) k) m) := by
  intro j k m
  let h := Nat.succ depth
  have hh : 7 ≤ h := by dsimp [h]; omega
  let d := h + 5
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 10
  let outputTwo := d2FlowTreeChild (d2FlowTreeChild before j) k
  let outputThree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 11) j) k) m
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 11)
    (d2FlowCandidateRole d 11)
    (d2FlowCandidateQuota d 11)
    (fun r => d2FlowCandidateCapacity d r 11) 3 outputThree
  have hinvGlobal := d2FlowCandidateStage9_preserves_inv h (by omega)
  have hinvTwo := d2FlowTreeInv_grandchild (h := h + 3)
    before hinvGlobal j k
  have hinputsTwo := d2FlowCandidateStage10_actual_levelTwo_inputs
    h (by omega) j k
  have hfront10 := d2FlowCandidateStage10_frontiers d (by omega)
  rcases hfront10 with ⟨_, _, hactive2, hrole2, _, _, _⟩
  have hcapRelation :
      2 * d2FlowCandidateCapacity d 2 10 =
        d2FlowCandidateCapacity d 3 11 := by
    have hexp : d2FlowCandidateCapacityExponent d 3 11 =
        d2FlowCandidateCapacityExponent d 2 10 + 1 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    unfold d2FlowCandidateCapacity
    rw [hexp, Nat.pow_succ]
    omega
  have hproject := d2FlowStage_path3_projection
    (active := d2FlowCandidateActive d 10)
    (role := d2FlowCandidateRole d 10)
    (quota := d2FlowCandidateQuota d 10)
    (h := h + 2) (i := 0) before j k m
  have hproject' : outputThree =
      d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 10)
          (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
          (h + 3) 2 outputTwo) m := by
    simpa [outputThree, outputTwo, d, before,
      d2FlowCandidateRun, d2FlowCandidateStage] using hproject
  cases htwo : outputTwo with
  | node G2 low2 high2 children2 =>
      have hinvTwo' : d2FlowTreeInv 8192
          (.node G2 low2 high2 children2) := by
        simpa [outputTwo, htwo] using hinvTwo
      have hinputsTwo' := hinputsTwo
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 10)
        (d2FlowCandidateRole d 10)
        (d2FlowCandidateQuota d 10)
        (fun q => d2FlowCandidateCapacity d q 10) 2 outputTwo at hinputsTwo'
      rw [htwo] at hinputsTwo'
      have hchildCap := d2FlowStage_regular_child_g_bound_of_tree_inputs
        (active := d2FlowCandidateActive d 10)
        (role := d2FlowCandidateRole d 10)
        (quota := d2FlowCandidateQuota d 10)
        (cap := fun r => d2FlowCandidateCapacity d r 10)
        (stageDepth := h + 2) (i := 2)
        (.node G2 low2 high2 children2) hactive2
        (Or.inr (Or.inl hrole2)) hinvTwo' hinputsTwo'
      have hchildBalanced := d2FlowStage_regular_child_balanced
        (active := d2FlowCandidateActive d 10)
        (role := d2FlowCandidateRole d 10)
        (quota := d2FlowCandidateQuota d 10)
        (h := h + 2) (i := 2) (G := G2) (low := low2) (high := high2)
        children2 hactive2 (Or.inr (Or.inl hrole2)) m
      cases hnode : outputThree with
      | node G3 low3 high3 children3 =>
          have hprojectNode := hproject'
          rw [htwo] at hprojectNode
          have hG : 512 * G3 ≤ d2FlowCandidateCapacity d 3 11 := by
            have hg := hchildCap m
            rw [← hprojectNode, hcapRelation] at hg
            simpa [hnode, d2FlowTreeRootDeficit] using hg
          have hbalance : low3 + high3 = G3 := by
            have hb := hchildBalanced
            rw [← hprojectNode] at hb
            rw [hnode] at hb
            simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hb
          have hrecursive : ∀ a, d2FlowStageInvInputs 8192
              (d2FlowCandidateActive d 11)
              (d2FlowCandidateRole d 11)
              (d2FlowCandidateQuota d 11)
              (fun r => d2FlowCandidateCapacity d r 11) 4 (children3 a) := by
            intro a
            cases hchildFour : children3 a with
            | node G4 low4 high4 children4 =>
                have hrecursive5 : ∀ b, d2FlowStageInvInputs 8192
                    (d2FlowCandidateActive d 11)
                    (d2FlowCandidateRole d 11)
                    (d2FlowCandidateQuota d 11)
                    (fun r => d2FlowCandidateCapacity d r 11) 5
                    (children4 b) := by
                  intro b
                  have hfive := d2FlowCandidateStage11_actual_levelFive_inputs
                    depth hd j k m a b
                  change d2FlowStageInvInputs 8192
                    (d2FlowCandidateActive d 11)
                    (d2FlowCandidateRole d 11)
                    (d2FlowCandidateQuota d 11)
                    (fun r => d2FlowCandidateCapacity d r 11) 5
                    (d2FlowTreeChild
                      (d2FlowTreeChild outputThree a) b) at hfive
                  have hchildRoot : d2FlowTreeChild outputThree a =
                      .node G4 low4 high4 children4 := by
                    rw [hnode]
                    simpa only [d2FlowTreeChild] using hchildFour
                  have hpath : d2FlowTreeChild
                      (d2FlowTreeChild outputThree a) b = children4 b := by
                    rw [hchildRoot]
                    rfl
                  rw [hpath] at hfive
                  exact hfive
                have hinactive4 : d2FlowCandidateActive d 11 4 = false := by
                  simp [d2FlowCandidateActive, tfD2]
                simp only [d2FlowStageInvInputs, hinactive4, if_false]
                exact ⟨hrecursive5, trivial⟩
          have hreserve :=
            d2FlowCandidateStage11_levelThree_endpoint_reserve depth hd j k m
          have hleft : d2FlowCandidateCapacity d 3 11 ≤
              128 * d2FlowTreeRootDeficit (children3 ⟨0, by omega⟩) := by
            have hl := hreserve ⟨0, by omega⟩
            change d2FlowCandidateCapacity d 3 11 ≤
              128 * d2FlowTreeRootDeficit
                (d2FlowTreeChild outputThree ⟨0, by omega⟩) at hl
            rw [hnode] at hl
            simpa only [d2FlowTreeChild] using hl
          have hright : d2FlowCandidateCapacity d 3 11 ≤
              128 * d2FlowTreeRootDeficit (children3 ⟨7, by omega⟩) := by
            have hr := hreserve ⟨7, by omega⟩
            change d2FlowCandidateCapacity d 3 11 ≤
              128 * d2FlowTreeRootDeficit
                (d2FlowTreeChild outputThree ⟨7, by omega⟩) at hr
            rw [hnode] at hr
            simpa only [d2FlowTreeChild] using hr
          have htotal :=
            d2FlowCandidateStage11_levelThree_boundary_mass_suffices
              d (by omega) G3 hG children3 hleft
          exact d2FlowCandidateStage11_mid_inputs d (by omega)
            G3 low3 high3 hbalance hG children3 hrecursive hleft hright htotal

set_option maxHeartbeats 10000000 in
/-- Stage 10's inactive level one makes its level-two output subtrees exactly
the local Stage 10 updates at their source nodes. -/
theorem d2FlowCandidateStage10_levelTwo_projection
    (h : Nat) (hh : 10 ≤ h) :
    ∀ j k, d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun (h + 2)
            (d2FlowTreeInitial 8192 (h + 2)) 11) j) k =
      d2FlowStage (d2FlowCandidateActive (h + 2) 10)
        (d2FlowCandidateRole (h + 2) 10)
        (d2FlowCandidateQuota (h + 2) 10) h 2
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (h + 2)
              (d2FlowTreeInitial 8192 (h + 2)) 10) j) k) := by
  have hinactive1 : d2FlowCandidateActive (h + 2) 10 1 = false := by
    simp [d2FlowCandidateActive, tfD2]
  intro j k
  change d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowCandidateStage (h + 2) 10
          (d2FlowCandidateRun (h + 2)
            (d2FlowTreeInitial 8192 (h + 2)) 10)) j) k =
    d2FlowStage (d2FlowCandidateActive (h + 2) 10)
      (d2FlowCandidateRole (h + 2) 10)
      (d2FlowCandidateQuota (h + 2) 10) h 2
      (d2FlowTreeChild (d2FlowTreeChild
        (d2FlowCandidateRun (h + 2)
          (d2FlowTreeInitial 8192 (h + 2)) 10) j) k)
  cases htree : d2FlowCandidateRun (h + 2)
      (d2FlowTreeInitial 8192 (h + 2)) 10 with
  | node G low high children =>
      have hprojection := d2FlowStage_child_child_of_inactive
        (active := d2FlowCandidateActive (h + 2) 10)
        (role := d2FlowCandidateRole (h + 2) 10)
        (quota := d2FlowCandidateQuota (h + 2) 10)
        (h := h) (i := 0) (G := G) (low := low) (high := high)
        children hinactive1 j k
      change d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateStage (h + 2) 10
              (.node G low high children)) j) k =
        d2FlowStage (d2FlowCandidateActive (h + 2) 10)
          (d2FlowCandidateRole (h + 2) 10)
          (d2FlowCandidateQuota (h + 2) 10) h 2
          (d2FlowTreeChild (d2FlowTreeChild
            (.node G low high children) j) k)
      simpa [d2FlowCandidateStage] using hprojection

/-- The stage-eight root reset persists through the inactive root at stage
nine, so the stage-ten top-descending root gate sees zero deficit. -/
theorem d2FlowCandidateStage10_root_zero (h : Nat) (hh : 6 ≤ h) :
    d2FlowTreeRootDeficit
      (d2FlowCandidateRun (h + 5)
        (d2FlowTreeInitial 8192 (h + 5)) 10) = 0 := by
  let d := h + 5
  let initial := d2FlowTreeInitial 8192 d
  have hzero8 : d2FlowTreeRootDeficit (d2FlowCandidateRun d initial 8) = 0 := by
    simpa [d, initial] using d2FlowCandidateStage8_root_zero h (by omega)
  have hfront8 := d2FlowCandidateStage8_frontiers d (by omega)
  rcases hfront8 with ⟨hactive0, hrole0, _, _, _, _, _⟩
  have hzero9 : d2FlowTreeRootDeficit (d2FlowCandidateRun d initial 9) = 0 := by
    change d2FlowTreeRootDeficit
      (d2FlowCandidateStage d 8 (d2FlowCandidateRun d initial 8)) = 0
    cases htree : d2FlowCandidateRun (h + 5)
        (d2FlowTreeInitial 8192 (h + 5)) 8 with
    | node G low high children =>
        have hG : G = 0 := by
          have hz := hzero8
          rw [htree] at hz
          simpa [d2FlowTreeRootDeficit] using hz
        have hstep := d2FlowStage_active_node_deficit
          (active := d2FlowCandidateActive d 8)
          (role := d2FlowCandidateRole d 8)
          (quota := d2FlowCandidateQuota d 8)
          (h := h + 4) (i := 0) (G := G) (low := low)
          (high := high) children hactive0
        rw [hrole0] at hstep
        change d2FlowTreeRootDeficit
          (d2FlowStage (d2FlowCandidateActive d 8)
            (d2FlowCandidateRole d 8) (d2FlowCandidateQuota d 8)
            (h + 5) 0 (.node G low high children)) = 0
        simpa [d2FlowCandidateStage, hG] using hstep
  have hinactive9 : d2FlowCandidateActive d 9 0 = false := by
    simp [d2FlowCandidateActive, tfD2]
  change d2FlowTreeRootDeficit
    (d2FlowCandidateStage d 9 (d2FlowCandidateRun d initial 9)) = 0
  unfold d2FlowCandidateStage
  rw [d2FlowStage_root_deficit_of_inactive
    (active := d2FlowCandidateActive d 9)
    (role := d2FlowCandidateRole d 9)
    (quota := d2FlowCandidateQuota d 9)
    (h := d) (i := 0) (d2FlowCandidateRun d initial 9) hinactive9]
  simpa [d, initial] using hzero9

set_option maxHeartbeats 10000000 in
set_option maxHeartbeats 10000000 in
/-- The actual Stage 11 level-one top-rise gates follow from Stage 10's
top-descending root, its level-two mid quotas, and the proved Stage 11
level-three recursive inputs. -/
theorem d2FlowCandidateStage11_actual_levelOne_inputs
    (depth : Nat) (hd : 6 ≤ depth) :
    ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (depth + 6) 11)
      (d2FlowCandidateRole (depth + 6) 11)
      (d2FlowCandidateQuota (depth + 6) 11)
      (fun q => d2FlowCandidateCapacity (depth + 6) q 11) 1
      (d2FlowTreeChild
        (d2FlowCandidateRun (depth + 6)
          (d2FlowTreeInitial 8192 (depth + 6)) 11) j) := by
  let d := depth + 6
  change ∀ j, d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 11) (d2FlowCandidateRole d 11)
    (d2FlowCandidateQuota d 11)
    (fun q => d2FlowCandidateCapacity d q 11) 1
    (d2FlowTreeChild (d2FlowCandidateRun d
      (d2FlowTreeInitial 8192 d) 11) j)
  have hfront10 := d2FlowCandidateStage10_frontiers d (by omega)
  rcases hfront10 with ⟨hactive0, hrole0, hactive2, hrole2, _, _, _⟩
  have hfront11 := d2FlowCandidateStage11_frontiers d (by omega)
  rcases hfront11 with ⟨_, _, hactive3, hrole3, _, _, _⟩
  have hlevelThree := d2FlowCandidateStage11_actual_levelThree_inputs depth hd
  have hprojection := d2FlowCandidateStage10_levelTwo_projection
    (depth + 4) (by omega)
  have hrootZero := d2FlowCandidateStage10_root_zero (depth + 1) (by omega)
  have hinactive2 : d2FlowCandidateActive d 11 2 = false := by
    simp [d2FlowCandidateActive, tfD2]
  intro j
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 10
  let after := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 11
  change D2FlowTree (depth + 6) at before
  change D2FlowTree (depth + 6) at after
  have hdata : d2FlowTreeRootData (d2FlowTreeChild after j) = (0, 0, 0) := by
    change d2FlowTreeRootData
      (d2FlowTreeChild (d2FlowCandidateStage d 10 before) j) = (0, 0, 0)
    cases hroot : before with
    | node G low high children =>
        have hG : G = 0 := by
          have hz := hrootZero
          have hz' : d2FlowTreeRootDeficit before = 0 := by
            simpa [before, d, Nat.add_assoc] using hz
          rw [hroot] at hz'
          exact hz'
        simpa [d2FlowCandidateStage, d2FlowTreeInitial, hroot, hG,
          hactive0, hrole0] using
          (d2FlowStage_topDesc_child_rootdata
            (active := d2FlowCandidateActive d 10)
            (role := d2FlowCandidateRole d 10)
            (quota := d2FlowCandidateQuota d 10)
            (h := d - 1) (i := 0) (G := G) (low := low)
            (high := high) children hactive0 hrole0 j)
  cases hchild : d2FlowTreeChild after j with
  | node G1 low1 high1 children1 =>
      have hdata' := hdata
      rw [hchild] at hdata'
      simp only [d2FlowTreeRootData] at hdata'
      have hG1 : G1 = 0 := congrArg Prod.fst hdata'
      have hlow1 : low1 = 0 := congrArg (fun p : Nat × Nat × Nat => p.2.1) hdata'
      have hhigh1 : high1 = 0 := congrArg (fun p : Nat × Nat × Nat => p.2.2) hdata'
      have hbalance : low1 + high1 = 0 := by omega
      have hd2 : d - 2 = depth + 4 := by dsimp [d]; omega
      have hchildren : ∀ k : Fin 8,
          d2FlowCandidateQuota d 10 2 .mid ≤
            d2FlowTreeRootDeficit (children1 k) := by
        intro k
        cases hbefore : before with
        | node G0 low0 high0 children0 =>
         have hafter : after = d2FlowCandidateStage d 10
             (.node G0 low0 high0 children0) := by
           change d2FlowCandidateStage d 10 before = _
           rw [hbefore]
         have hprojNode := d2FlowStage_child_child_of_inactive
           (active := d2FlowCandidateActive d 10)
           (role := d2FlowCandidateRole d 10)
           (quota := d2FlowCandidateQuota d 10)
           (h := depth + 4) (i := 0) (G := G0) (low := low0)
           (high := high0) children0
           (by simp [d2FlowCandidateActive, tfD2]) j k
         have hchildNode : d2FlowTreeChild
             (d2FlowCandidateStage d 10
               (.node G0 low0 high0 children0)) j =
               .node G1 low1 high1 children1 := by
           calc
             _ = d2FlowTreeChild after j := by rw [← hafter]
             _ = .node G1 low1 high1 children1 := hchild
         have hproj' : children1 k = d2FlowStage
             (d2FlowCandidateActive d 10) (d2FlowCandidateRole d 10)
             (d2FlowCandidateQuota d 10) (depth + 4) 2
             (d2FlowTreeChild (children0 j) k) := by
           calc
             children1 k = d2FlowTreeChild (.node G1 low1 high1 children1) k := rfl
             _ = d2FlowTreeChild
                   (d2FlowTreeChild
                     (d2FlowCandidateStage d 10
                       (.node G0 low0 high0 children0)) j) k := by
                   rw [← hchildNode]
             _ = d2FlowStage (d2FlowCandidateActive d 10)
                   (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
                   (depth + 4) 2
                   (d2FlowTreeChild (children0 j) k) := hprojNode
         cases hsrc : d2FlowTreeChild (children0 j) k with
         | node G2 low2 high2 grandchildren =>
            have hpost : d2FlowTreeRootDeficit
                (d2FlowStage (d2FlowCandidateActive d 10)
                  (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
                  (depth + 4) 2 (.node G2 low2 high2 grandchildren)) =
                G2 + d2FlowCandidateQuota d 10 2 .mid := by
              simpa [hactive2, hrole2] using
                (d2FlowStage_active_node_deficit
                  (active := d2FlowCandidateActive d 10)
                  (role := d2FlowCandidateRole d 10)
                  (quota := d2FlowCandidateQuota d 10)
                  (h := depth + 3) (i := 2) (G := G2)
                  (low := low2) (high := high2) grandchildren hactive2)
            change d2FlowCandidateQuota d 10 2 .mid ≤
              d2FlowTreeRootDeficit (children1 k)
            rw [hproj', hsrc, hpost]
            omega
      have hrecursive : ∀ k : Fin 8,
          d2FlowStageInvInputs 8192
            (d2FlowCandidateActive d 11) (d2FlowCandidateRole d 11)
            (d2FlowCandidateQuota d 11)
            (fun q => d2FlowCandidateCapacity d q 11) 2 (children1 k) := by
        intro k
        have hrecursive3 : ∀ m : Fin 8,
            d2FlowStageInvInputs 8192
              (d2FlowCandidateActive d 11) (d2FlowCandidateRole d 11)
              (d2FlowCandidateQuota d 11)
              (fun q => d2FlowCandidateCapacity d q 11) 3
              (d2FlowTreeChild (children1 k) m) := by
          intro m
          have hm := hlevelThree j k m
          change d2FlowStageInvInputs 8192
            (d2FlowCandidateActive d 11) (d2FlowCandidateRole d 11)
            (d2FlowCandidateQuota d 11)
            (fun q => d2FlowCandidateCapacity d q 11) 3
            (d2FlowTreeChild (d2FlowTreeChild
              (d2FlowTreeChild after j) k) m) at hm
          rw [hchild] at hm
          simpa only [d2FlowTreeChild] using hm
        cases hchild2 : children1 k with
        | node G2 low2 high2 grandchildren =>
            rw [hchild2] at hrecursive3
            simp only [d2FlowStageInvInputs, hinactive2, if_false]
            exact ⟨hrecursive3, trivial⟩
      have htop := d2FlowCandidateStage11_topRise_inputs d (by omega)
        low1 high1 hbalance children1 hchildren hrecursive
      simpa [hchild, hG1, hlow1, hhigh1] using htop


/-- The complete Stage 10 recursive input predicate follows from its actual
level-two and level-four sender gates, with the root zero from the previous
top-descending phase. -/
theorem d2FlowCandidateStage10_actual_inputs
    (h : Nat) (hh : 6 ≤ h) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 5) 10)
      (d2FlowCandidateRole (h + 5) 10)
      (d2FlowCandidateQuota (h + 5) 10)
      (fun q => d2FlowCandidateCapacity (h + 5) q 10) 0
      (d2FlowCandidateRun (h + 5)
        (d2FlowTreeInitial 8192 (h + 5)) 10) := by
  let d := h + 5
  let tree := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 10
  have hfront := d2FlowCandidateStage10_frontiers d (by omega)
  rcases hfront with ⟨hactive0, hrole0, _, _, _, _, _⟩
  have hinactive1 : d2FlowCandidateActive d 10 1 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hrootZero := d2FlowCandidateStage10_root_zero h hh
  have hinv := d2FlowCandidateStage9_preserves_inv h hh
  change d2FlowTreeInv 8192 tree at hinv
  change d2FlowTreeRootDeficit tree = 0 at hrootZero
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 10)
    (d2FlowCandidateRole d 10)
    (d2FlowCandidateQuota d 10)
    (fun q => d2FlowCandidateCapacity d q 10) 0 tree
  have hrecursive : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 10)
      (d2FlowCandidateRole d 10)
      (d2FlowCandidateQuota d 10)
      (fun q => d2FlowCandidateCapacity d q 10) 1
      (d2FlowTreeChild tree j) := by
    intro j
    cases hnodeOne : d2FlowTreeChild tree j with
    | node G1 low1 high1 children1 =>
        have hrecursiveTwo : ∀ k, d2FlowStageInvInputs 8192
            (d2FlowCandidateActive d 10)
            (d2FlowCandidateRole d 10)
            (d2FlowCandidateQuota d 10)
            (fun q => d2FlowCandidateCapacity d q 10) 2
            (children1 k) := by
          intro k
          have hk := d2FlowCandidateStage10_actual_levelTwo_inputs h hh j k
          change d2FlowStageInvInputs 8192
            (d2FlowCandidateActive d 10)
            (d2FlowCandidateRole d 10)
            (d2FlowCandidateQuota d 10)
            (fun q => d2FlowCandidateCapacity d q 10) 2
            (d2FlowTreeChild (d2FlowTreeChild tree j) k) at hk
          rw [hnodeOne] at hk
          simpa only [d2FlowTreeChild] using hk
        simp only [d2FlowStageInvInputs, hinactive1, if_false]
        exact ⟨hrecursiveTwo, trivial⟩
  change D2FlowTree (h + 5) at tree
  cases hroot : tree with
  | node G low high children =>
      have hrootInv : d2FlowTreeInv 8192 (.node G low high children) := by
        rw [hroot] at hinv
        exact hinv
      have hG : G = 0 := by
        have hz := hrootZero
        rw [hroot] at hz
        simpa [d2FlowTreeRootDeficit] using hz
      have hbalance : low + high = G := by
        have hlt : G < 8192 * 8 ^ (h + 5) := by
          rw [hG]
          positivity
        have hb := hrootInv.2.2.1 hlt
        exact hb
      have hchildren : ∀ j, d2FlowStageInvInputs 8192
          (d2FlowCandidateActive d 10)
          (d2FlowCandidateRole d 10)
          (d2FlowCandidateQuota d 10)
          (fun q => d2FlowCandidateCapacity d q 10) 1
          (children j) := by
        intro j
        have hj := hrecursive j
        change d2FlowStageInvInputs 8192
          (d2FlowCandidateActive d 10)
          (d2FlowCandidateRole d 10)
          (d2FlowCandidateQuota d 10)
          (fun q => d2FlowCandidateCapacity d q 10) 1
          (d2FlowTreeChild tree j) at hj
        rw [hroot] at hj
        simpa only [d2FlowTreeChild] using hj
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 10)
        (d2FlowCandidateRole d 10)
        (d2FlowCandidateQuota d 10)
        (fun q => d2FlowCandidateCapacity d q 10) 0
        (.node G low high children)
      simp only [d2FlowStageInvInputs, hactive0, if_true, hrole0]
      exact ⟨hchildren, hbalance, hG⟩

set_option maxHeartbeats 10000000 in
/-- Stage ten preserves the full saturated-aware tree invariant, closing this
finite run transition for every candidate depth `d >= 11`. -/
theorem d2FlowCandidateStage10_preserves_inv
    (h : Nat) (hh : 6 ≤ h) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (h + 5)
        (d2FlowTreeInitial 8192 (h + 5)) 11) := by
  let before := d2FlowCandidateRun (h + 5)
    (d2FlowTreeInitial 8192 (h + 5)) 10
  have hinv := d2FlowCandidateStage9_preserves_inv h hh
  have hinputs := d2FlowStageInvInputs_tolerant_of_strict before
    (d2FlowCandidateStage10_actual_inputs h hh)
  have hpres := d2FlowStage_preserves_inv_of_tolerant_inputs
    (active := d2FlowCandidateActive (h + 5) 10)
    (role := d2FlowCandidateRole (h + 5) 10)
    (quota := d2FlowCandidateQuota (h + 5) 10)
    (cap := fun q => d2FlowCandidateCapacity (h + 5) q 10)
    (i := 0) before hinv hinputs
  change d2FlowTreeInv 8192
    (d2FlowCandidateStage (h + 5) 10 before)
  simpa [before, d2FlowCandidateRun, d2FlowCandidateStage] using hpres

set_option maxHeartbeats 10000000 in
/-- The full Stage 11 input contract follows from its actual level-one
top-rise gates; the root is inactive. -/
theorem d2FlowCandidateStage11_actual_inputs
    (depth : Nat) (hd : 6 ≤ depth) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (depth + 6) 11)
      (d2FlowCandidateRole (depth + 6) 11)
      (d2FlowCandidateQuota (depth + 6) 11)
      (fun q => d2FlowCandidateCapacity (depth + 6) q 11) 0
      (d2FlowCandidateRun (depth + 6)
        (d2FlowTreeInitial 8192 (depth + 6)) 11) := by
  let d := depth + 6
  let tree := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 11
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 11) (d2FlowCandidateRole d 11)
    (d2FlowCandidateQuota d 11)
    (fun q => d2FlowCandidateCapacity d q 11) 0 tree
  have hinactive0 : d2FlowCandidateActive d 11 0 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hlevelOne := d2FlowCandidateStage11_actual_levelOne_inputs depth hd
  change D2FlowTree (depth + 5 + 1) at tree
  cases hroot : tree with
  | node G low high children =>
      simp only [d2FlowStageInvInputs, hinactive0, if_false]
      refine ⟨?_, trivial⟩
      intro j
      have hj := hlevelOne j
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 11) (d2FlowCandidateRole d 11)
        (d2FlowCandidateQuota d 11)
        (fun q => d2FlowCandidateCapacity d q 11) 1
        (d2FlowTreeChild tree j) at hj
      rw [hroot] at hj
      simpa only [d2FlowTreeChild] using hj

set_option maxHeartbeats 10000000 in
/-- Stage eleven preserves the saturated-aware tree invariant through its
actual top-rise, mid, and bottom-descending gates. -/
theorem d2FlowCandidateStage11_preserves_inv
    (depth : Nat) (hd : 6 ≤ depth) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (depth + 6)
        (d2FlowTreeInitial 8192 (depth + 6)) 12) := by
  let d := depth + 6
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 11
  have hinv := d2FlowCandidateStage10_preserves_inv (depth + 1) (by omega)
  have hinputs := d2FlowStageInvInputs_tolerant_of_strict before
    (d2FlowCandidateStage11_actual_inputs depth hd)
  have hpres := d2FlowStage_preserves_inv_of_tolerant_inputs
    (active := d2FlowCandidateActive d 11)
    (role := d2FlowCandidateRole d 11)
    (quota := d2FlowCandidateQuota d 11)
    (cap := fun q => d2FlowCandidateCapacity d q 11)
    (i := 0) before hinv hinputs
  change d2FlowTreeInv 8192
    (d2FlowCandidateStage d 11 before)
  simpa [d, before, d2FlowCandidateRun, d2FlowCandidateStage] using hpres


/-! A sharpened interface for the exceptional child-quota sum. The finite
`FlowDAG` screen suggests exactly these two endpoint caps; deriving them from
the reachable-state invariant is a separate obligation. -/
theorem d2_botRise_child_quota_sum_of_endpoint_caps
    (childRho : Fin 8 → Rat)
    (hleft : childRho 0 ≤ 49 / 16384)
    (hright : childRho 7 ≤ 49 / 16384)
    (hinterior : ∀ j : Fin 8, j.val ≠ 0 → j.val ≠ 7 →
      childRho j ≤ 1 / 256) :
    32 * (Finset.univ.sum childRho) ≤ 241 / 256 := by
  have hpoint : ∀ j : Fin 8,
      childRho j ≤ if j.val = 0 ∨ j.val = 7 then 49 / 16384 else 1 / 256 := by
    intro j
    by_cases h0 : j.val = 0
    · have : j = 0 := Fin.ext h0
      subst j
      simpa using hleft
    · by_cases h7 : j.val = 7
      · have : j = 7 := Fin.ext h7
        subst j
        simpa using hright
      · have h := hinterior j h0 h7
        simpa [h0, h7] using h
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => hpoint j)
  have hconst : (Finset.univ.sum fun j : Fin 8 =>
      if j.val = 0 ∨ j.val = 7 then (49 / 16384 : Rat) else 1 / 256) =
      2 * (49 / 16384 : Rat) + 6 * (1 / 256 : Rat) := by
    norm_num [Fin.sum_univ_succ]
  rw [hconst] at hsum
  nlinarith

/-- The sharper exceptional aggregate permits the same `279/256` sender
factor with the larger old-deficit budget `23/4096`. -/
theorem d2_two_step_sender_factor_279_of_tolerant_budget
    {a c gOld gNow rhoOld : Rat} (childRho : Fin 8 → Rat)
    (hid : a / c = 16 * gOld + 16 * rhoOld +
      32 * (Finset.univ.sum childRho) - gNow)
    (hgOld : gOld ≤ 23 / 4096) (hgNow : 0 ≤ gNow)
    (hcase : (rhoOld ≤ 15 / 4096 ∧
        32 * (Finset.univ.sum childRho) ≤ 241 / 256) ∨
      (rhoOld ≤ 1 / 256 ∧
        32 * (Finset.univ.sum childRho) ≤ 15 / 16)) :
    a / c ≤ 279 / 256 := by
  rcases hcase with hex | hreg
  · rcases hex with ⟨hrho, hchildren⟩
    rw [hid]
    nlinarith
  · rcases hreg with ⟨hrho, hchildren⟩
    rw [hid]
    nlinarith

/-- The exact strong-parent block profile implies the exceptional aggregate
quota bound after the `16x` to `32x` capacity rescaling. The `low` and `high`
offsets only reduce the endpoint terms. -/
theorem d2_botRise_child_quota_sum_of_strong_parent_blocks
    {c cOld low high : Rat} (childRho : Fin 8 → Rat)
    (hc : 0 < c) (hcOld : cOld = 16 * c)
    (hlow : 0 ≤ low) (hhigh : 0 ≤ high)
    (hfirst : childRho 0 = (49 * cOld / 8192 - low) / (32 * c))
    (hlast : childRho 7 = (49 * cOld / 8192 - high) / (32 * c))
    (hmiddle : ∀ j : Fin 8, j.val ≠ 0 → j.val ≠ 7 →
      childRho j = (cOld / 128) / (32 * c)) :
    32 * (Finset.univ.sum childRho) ≤ 241 / 256 := by
  apply d2_botRise_child_quota_sum_of_endpoint_caps childRho
  · rw [hfirst, hcOld]
    apply (div_le_iff₀ (by positivity : (0 : Rat) < 32 * c)).2
    nlinarith
  · rw [hlast, hcOld]
    apply (div_le_iff₀ (by positivity : (0 : Rat) < 32 * c)).2
    nlinarith
  · intro j hj0 hj7
    rw [hmiddle j hj0 hj7, hcOld]
    apply (div_le_iff₀ (by positivity : (0 : Rat) < 32 * c)).2
    nlinarith

theorem d2FlowStage_root_deficit_eq_quota_of_zero
    {h i : Nat} {tree : D2FlowTree (h + 1)}
    (active : Nat → Bool) (role : Nat → D2Role)
    (quota : Nat → D2Role → Nat)
    (hzero : d2FlowTreeRootDeficit tree = 0)
    (ha : active i = true) (hr : role i = .topRise) :
    d2FlowTreeRootDeficit (d2FlowStage active role quota (h + 1) i tree) =
      quota i .topRise := by
  cases tree with
  | node G low high children =>
      simp only [d2FlowStage_active_node_deficit children ha, hr]
      simpa [d2FlowTreeRootDeficit] using hzero

/-! ### Top-descending two-step allocation

A top-descending node clears its children. If it is inactive at the next
stage while each child is a top-rise sender, then on the following
top-descending visit its allocation is exactly the sum of those eight
top-rise quotas. This isolates the schedule arithmetic needed for the
top-frontier case of the active-allocation bound.
-/

theorem d2FlowStage_topDesc_inactive_topRise_topDesc_allocation
    {h i G low high scale : Nat}
    (children : Fin 8 → D2FlowTree (h + 1))
    (active0 active1 : Nat → Bool)
    (role0 role1 : Nat → D2Role)
    (quota0 quota1 : Nat → D2Role → Nat)
    (ha0 : active0 i = true) (hr0 : role0 i = .topDesc)
    (ha1 : active1 i = false)
    (hac : active1 (i + 1) = true)
    (hrc : role1 (i + 1) = .topRise)
    (hG : G = 0) :
    d2FlowTreeAllocation scale
      (d2FlowStage active1 role1 quota1 (h + 2) i
        (d2FlowStage active0 role0 quota0 (h + 2) i
          (.node G low high children))) =
      8 * quota1 (i + 1) .topRise := by
  classical
  let first := d2FlowStage active0 role0 quota0 (h + 2) i
    (.node G low high children)
  let second := d2FlowStage active1 role1 quota1 (h + 2) i first
  have hfirstChild (j : Fin 8) :
      d2FlowTreeRootDeficit (d2FlowTreeChild first j) = 0 := by
    simp [first, d2FlowStage, ha0, hr0, d2FlowTreeChild,
      d2FlowTreeSetRoot_deficit]
  have hsecondChild (j : Fin 8) :
      d2FlowTreeRootDeficit (d2FlowTreeChild second j) =
        quota1 (i + 1) .topRise := by
    have hroot := d2FlowStage_root_deficit_eq_quota_of_zero
      (active := active1) (role := role1) (quota := quota1)
      (tree := d2FlowTreeChild first j) (hfirstChild j) hac hrc
    change d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active1 role1 quota1 (h + 2) i first) j) = _
    cases hf : first with
    | node G' low' high' children' =>
        rw [d2FlowStage_inactive_child children' ha1 j]
        simpa [hf] using hroot
  have hsecondRoot : d2FlowTreeRootDeficit second = 0 := by
    calc
      d2FlowTreeRootDeficit second = d2FlowTreeRootDeficit first := by
        simpa [second] using d2FlowStage_root_deficit_of_inactive
          (active := active1) (role := role1) (quota := quota1)
          (tree := first) ha1
      _ = 0 := by
        simp [first, d2FlowStage, ha0, hr0, hG, d2FlowTreeRootDeficit]
  have hsum : d2FlowTotal (fun j : Fin 8 =>
      d2FlowTreeRootDeficit (d2FlowTreeChild second j)) =
      8 * quota1 (i + 1) .topRise := by
    simp [d2FlowTotal, hsecondChild]
  have halloc : d2FlowTreeAllocation scale second =
      d2FlowTotal (fun j : Fin 8 =>
        d2FlowTreeRootDeficit (d2FlowTreeChild second j)) -
        d2FlowTreeRootDeficit second := by
    cases second with
    | node G' low' high' children' => rfl
  rw [halloc, hsum, hsecondRoot]
  simp

/-- In the repeated-frontier top-descending case, each top-rise child quota
is exactly one eighth of the parent's capacity two stages later. -/
theorem d2FlowCandidate_topRise_child_quota_eq_parent_capacity
    {d i t : Nat} (ht : 4 ≤ t) (hd : 7 ≤ d)
    (ha : active d (tfD2 d) i t) :
    8 * d2FlowCandidateQuota d (t - 1) (i + 1) .topRise =
      d2FlowCandidateCapacity d i t := by
  let e := d2FlowCandidateCapacityExponent d i t
  have hne : Not (t = 1) := by omega
  have hparts : 2 ≤ t := by
    unfold active at ha
    simp only [if_neg hne] at ha
    exact ha.1
  have hbound : 2 * t + 11 ≤ 3 * d + 3 * i := by
    unfold active at ha
    simp only [if_neg hne] at ha
    omega
  have he20 : 20 ≤ e := by
    dsimp [e]
    exact d2FlowCandidateCapacityExponent_ge_twenty hd ha
  have hden : 2 * t + 4 ≤ 13 + 3 * d + 3 * i := by omega
  have hchildExp :
      d2FlowCandidateCapacityExponent d (i + 1) (t - 1) = e + 5 := by
    dsimp [d2FlowCandidateCapacityExponent, e]
    omega
  have hchildSub :
      d2FlowCandidateCapacityExponent d (i + 1) (t - 1) - 8 = e - 3 := by
    omega
  have hpow : 8 * 2 ^ (e - 3) = 2 ^ e := by
    have heq : e = (e - 3) + 3 := by omega
    rw [heq, pow_add]
    norm_num
    ring
  change 8 * 2 ^ (d2FlowCandidateCapacityExponent d (i + 1) (t - 1) - 8) =
    2 ^ d2FlowCandidateCapacityExponent d i t
  rw [hchildSub]
  exact hpow

theorem alpha_parity_of_ge_two {d t : Nat} (ht : 2 ≤ t) :
    alpha d t % 2 = t % 2 := by
  have ht0 : t ≠ 0 := by omega
  have ht1 : t ≠ 1 := by omega
  simp only [alpha, if_neg ht0, if_neg ht1]
  unfold ceilParity
  split_ifs <;> omega

theorem ceilParity_step_reverse_le {m n s t : Nat}
    (hmn : m ≤ n) (hnm : n ≤ m + 1)
    (hpar : s % 2 ≠ t % 2) :
    ceilParity n t ≤ ceilParity m s + 1 := by
  unfold ceilParity
  split_ifs <;> omega

/-- The parity-rounded top frontier changes by exactly one level per step
once both times are past startup. -/
theorem alpha_step_reverse_le {d t : Nat} (ht : 3 ≤ t) :
    alpha d t ≤ alpha d (t - 1) + 1 := by
  have hstarMono : alphaStar d (t - 1) ≤ alphaStar d t :=
    alphaStar_mono (by omega)
  have hstarStep : alphaStar d t ≤ alphaStar d (t - 1) + 1 := by
    have h := alphaStar_succ_le (d := d) (t := t - 1)
    simpa only [Nat.sub_add_cancel (show 1 ≤ t by omega)] using h
  have hpar : (t - 1) % 2 ≠ t % 2 := by omega
  have hceil := ceilParity_step_reverse_le hstarMono hstarStep hpar
  have hnow : alpha d t = ceilParity (alphaStar d t) t := by
    simp [alpha, show t ≠ 0 by omega, show t ≠ 1 by omega]
  have hprev : alpha d (t - 1) =
      ceilParity (alphaStar d (t - 1)) (t - 1) := by
    have ht0 : t - 1 ≠ 0 := by omega
    have ht1 : t - 1 ≠ 1 := by omega
    simp [alpha, ht0, ht1]
  rw [hnow, hprev]
  exact hceil

/-- A top-descending time has only three two-step predecessor patterns. The
case where the lower frontier returns to the same level and rose in the
intermediate step is the reset/top-rise case handled by
`d2FlowStage_topDesc_inactive_topRise_topDesc_allocation`. -/
theorem alpha_topDesc_two_step_patterns {d t : Nat} (ht : 4 ≤ t)
    (hdesc : alpha d t < alpha d (t + 1)) :
    alpha d (t + 1) = alpha d t + 1 ∧
      ((alpha d (t - 2) = alpha d t ∧ alpha d (t - 1) = alpha d t + 1) ∨
       (alpha d (t - 2) = alpha d t ∧ alpha d (t - 1) + 1 = alpha d t) ∨
       (alpha d (t - 2) + 2 = alpha d t ∧ alpha d (t - 1) + 1 = alpha d t)) := by
  have hnext : alpha d (t + 1) ≤ alpha d t + 1 := by
    exact alpha_step_reverse_le (d := d) (t := t + 1) (by omega)
  have hnextEq : alpha d (t + 1) = alpha d t + 1 := by omega
  have hprevUp : alpha d (t - 1) ≤ alpha d t + 1 :=
    alpha_prev_le_succ (d := d) (by omega)
  have hprevDown : alpha d t ≤ alpha d (t - 1) + 1 :=
    alpha_step_reverse_le (d := d) (by omega)
  have hprevParity : alpha d (t - 1) % 2 ≠ alpha d t % 2 := by
    rw [alpha_parity_of_ge_two (d := d) (by omega),
      alpha_parity_of_ge_two (d := d) (by omega)]
    omega
  have hprevCases :
      alpha d (t - 1) = alpha d t + 1 ∨
        alpha d (t - 1) + 1 = alpha d t := by omega
  have hgapLow : alpha d (t - 2) ≤ alpha d t := by
    apply alpha_mono_same_parity (d := d) (by omega) (by omega)
    omega
  have hstep0 : alpha d (t - 1) ≤ alpha d (t - 2) + 1 :=
    alpha_step_reverse_le (d := d) (t := t - 1) (by omega)
  have hgapHigh : alpha d t ≤ alpha d (t - 2) + 2 := by omega
  have hgapParity : alpha d (t - 2) % 2 = alpha d t % 2 := by
    rw [alpha_parity_of_ge_two (d := d) (by omega),
      alpha_parity_of_ge_two (d := d) (by omega)]
    omega
  have hgapCases :
      alpha d (t - 2) = alpha d t ∨
        alpha d (t - 2) + 2 = alpha d t := by omega
  refine ⟨hnextEq, ?_⟩
  rcases hprevCases with hprevUp' | hprevDown' <;>
    rcases hgapCases with hgapSame | hgapTwo <;> omega

/- Full-tree projection and Stage-12 balance. -/

/-- Full-tree projection through six levels: the level-six subtree after a
stage is the last child action of its level-five ancestor. -/
theorem d2FlowStage_path6_tree_projection
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i : Nat}
    (tree : D2FlowTree (h + 6)) (j k m l q s : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowStage active role quota (h + 6) i tree) j) k) m) l) q) s =
    d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) (i + 5)
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild tree j) k) m) l) q)) s := by
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]

/-- Every actual level-six node after stage eleven is balanced, including
nodes at native capacity. Stage eleven's level-five `botDesc` cut explicitly
writes balanced data into each immediate child. -/
theorem d2FlowCandidateStage12_actual_levelSix_balanced
    (depth : Nat) (hd : 6 ≤ depth) :
    ∀ j k m l q s,
      let output := d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (depth + 6)
                    (d2FlowTreeInitial 8192 (depth + 6)) 12) j) k) m) l) q) s
      (d2FlowTreeRootData output).2.1 + (d2FlowTreeRootData output).2.2 =
        d2FlowTreeRootDeficit output := by
  intro j k m l q s
  let d := depth + 6
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 11
  let parent := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild before j) k) m) l) q
  have hfront := d2FlowCandidateStage11_frontiers d (by omega)
  rcases hfront with ⟨_, _, _, _, hactive5, hrole5, _⟩
  have hregular : d2FlowCandidateRole d 11 5 = .topRise ∨
      d2FlowCandidateRole d 11 5 = .mid ∨
      d2FlowCandidateRole d 11 5 = .botDesc :=
    Or.inr (Or.inr hrole5)
  cases hparent : parent with
  | node G low high children =>
      have hproject := d2FlowStage_path6_tree_projection
        (active := d2FlowCandidateActive d 11)
        (role := d2FlowCandidateRole d 11)
        (quota := d2FlowCandidateQuota d 11)
        (h := depth) (i := 0)
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 11)
        j k m l q s
      have hproject' :
          d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 12) j) k) m) l) q) s =
            d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive d 11)
                (d2FlowCandidateRole d 11) (d2FlowCandidateQuota d 11)
                (depth + 1) 5 parent) s := by
        simpa [before, d, d2FlowCandidateRun, d2FlowCandidateStage, parent]
          using hproject
      rw [hparent] at hproject'
      rw [hproject']
      exact d2FlowStage_regular_child_balanced children hactive5 hregular s


end Chvatal.D2Reserve

namespace Chvatal.D2Reserve

/-- Stage twelve adds one more interior mid sender and the next bottom-rise
sender to the even-stage frontier. -/
theorem d2FlowCandidateStage12_frontiers (d : Nat) (hd : 13 ≤ d) :
    d2FlowCandidateActive d 12 0 = true ∧
      d2FlowCandidateRole d 12 0 = .topDesc ∧
      d2FlowCandidateActive d 12 2 = true ∧
      d2FlowCandidateRole d 12 2 = .mid ∧
      d2FlowCandidateActive d 12 4 = true ∧
      d2FlowCandidateRole d 12 4 = .mid ∧
      d2FlowCandidateActive d 12 6 = true ∧
      d2FlowCandidateRole d 12 6 = .botRise ∧
      d2FlowCandidateActive d 12 8 = false := by
  have hactive0 : d2FlowCandidateActive d 12 0 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive2 : d2FlowCandidateActive d 12 2 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive4 : d2FlowCandidateActive d 12 4 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive6 : d2FlowCandidateActive d 12 6 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hinactive8 : d2FlowCandidateActive d 12 8 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have ha12 : alpha d 12 = 0 := by
    have h : 35 ≤ 3 * d := by omega
    simp [alpha, alphaStar, h, ceilParity]
  have ha13 : alpha d 13 = 1 := by
    have h : 37 ≤ 3 * d := by omega
    simp [alpha, alphaStar, h, ceilParity]
  have ho12 : omega 12 = 6 := by norm_num [omega, ceilParity]
  have ho13 : omega 13 = 5 := by norm_num [omega, ceilParity]
  have hrole0 : d2FlowCandidateRole d 12 0 = .topDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha12, ha13]
  have hrole2 : d2FlowCandidateRole d 12 2 = .mid := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha12, ho12]
  have hrole4 : d2FlowCandidateRole d 12 4 = .mid := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha12, ho12]
  have hrole6 : d2FlowCandidateRole d 12 6 = .botRise := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha12, ho12, ho13]
  exact ⟨hactive0, hrole0, hactive2, hrole2,
    hactive4, hrole4, hactive6, hrole6, hinactive8⟩

/-- The actual capacity and quota at the Stage-12 level-four mid sender. -/
theorem d2FlowCandidateStage12_levelFour_parameters
    (d : Nat) (hd : 13 ≤ d) :
    d2FlowCandidateCapacity d 4 12 = 2 ^ (3 * d - 3) ∧
      d2FlowCandidateQuota d 12 4 .mid = 15 * 2 ^ (3 * d - 15) := by
  constructor
  · simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  · simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega

/-- A Stage-12 level-four mid sender's cap and one endpoint reserve pay its
quota from the children. -/
theorem d2FlowCandidateStage12_levelFour_boundary_mass_suffices
    (d : Nat) (hd : 13 ≤ d) (G : Nat)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 4 12) {r : Nat}
    (children : Fin 8 → D2FlowTree r)
    (hleft : d2FlowCandidateCapacity d 4 12 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩)) :
    d2FlowCandidateQuota d 12 4 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
  rcases d2FlowCandidateStage12_levelFour_parameters d hd with ⟨hcap, hquota⟩
  have hGsmall : G ≤ 2 ^ (3 * d - 12) := by
    rw [hcap] at hG
    have hp : 512 * 2 ^ (3 * d - 12) = 2 ^ (3 * d - 3) := by
      rw [show (512 : Nat) = 2 ^ 9 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hroot : 2 ^ (3 * d - 10) ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hcap] at hleft
    have hp : 128 * 2 ^ (3 * d - 10) = 2 ^ (3 * d - 3) := by
      rw [show (128 : Nat) = 2 ^ 7 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hrootTotal : d2FlowTreeRootDeficit (children ⟨0, by omega⟩) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    let f : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
    change f ⟨0, by omega⟩ ≤ Finset.univ.sum f
    exact Finset.single_le_sum
      (fun j hj => Nat.zero_le (f j))
      (Finset.mem_univ (⟨0, by omega⟩ : Fin 8))
  have hpG : 2 ^ (3 * d - 12) = 8 * 2 ^ (3 * d - 15) := by
    rw [show 3 * d - 12 = 3 + (3 * d - 15) by omega, pow_add]
    norm_num
  have hpRoot : 2 ^ (3 * d - 10) = 32 * 2 ^ (3 * d - 15) := by
    rw [show 3 * d - 10 = 5 + (3 * d - 15) by omega, pow_add]
    norm_num
  have hmass : G + d2FlowCandidateQuota d 12 4 .mid ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hquota]
    rw [hpG] at hGsmall
    rw [hpRoot] at hroot
    nlinarith
  have hmassTotal : G + d2FlowCandidateQuota d 12 4 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) :=
    le_trans hmass hrootTotal
  omega

/-- Complete local recursive input gate for a Stage-12 level-four mid
sender. -/
theorem d2FlowCandidateStage12_mid_inputs
    (d : Nat) (hd : 13 ≤ d) (G low high : Nat) {r : Nat}
    (hbalance : low + high = G)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 4 12)
    (children : Fin 8 → D2FlowTree r)
    (hrecursive : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 12)
      (d2FlowCandidateRole d 12)
      (d2FlowCandidateQuota d 12)
      (fun k => d2FlowCandidateCapacity d k 12) 5 (children j))
    (hleft : d2FlowCandidateCapacity d 4 12 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hright : d2FlowCandidateCapacity d 4 12 ≤
      128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩))
    (htotal : d2FlowCandidateQuota d 12 4 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 12)
      (d2FlowCandidateRole d 12)
      (d2FlowCandidateQuota d 12)
      (fun k => d2FlowCandidateCapacity d k 12) 4
      (.node G low high children) := by
  rcases d2FlowCandidateStage12_frontiers d hd with
    ⟨_, _, _, _, hactive, hrole, _, _, _⟩
  have ⟨hcap, hquota⟩ := d2FlowCandidateStage12_levelFour_parameters d hd
  have hquotaEven : d2FlowCandidateQuota d 12 4 .mid % 2 = 0 := by
    rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 15 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 12 4 .mid ≤
      d2FlowCandidateCapacity d 4 12 := by
    rw [hquota, hcap]
    have hp : 256 * 15 * 2 ^ (3 * d - 15) =
        3840 * 2 ^ (3 * d - 15) := by norm_num
    have hpCap : 2 ^ (3 * d - 3) = 4096 * 2 ^ (3 * d - 15) := by
      rw [show 3 * d - 3 = 12 + (3 * d - 15) by omega, pow_add]
      norm_num
    nlinarith [hp, hpCap]
  simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
  exact ⟨hrecursive, ⟨hbalance, hG, hquotaCap, htotal,
    hquotaEven, hleft, hright⟩⟩

/-- Every subtree rooted at level seven or below has vacuous stage-twelve
input obligations: the active band ends at level six. -/
theorem d2FlowCandidateAny_stage12_inactive_inputs
    {d h i : Nat} (hi : 7 ≤ i) (tree : D2FlowTree h) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 12)
      (d2FlowCandidateRole d 12)
      (d2FlowCandidateQuota d 12)
      (fun k => d2FlowCandidateCapacity d k 12) i tree := by
  induction tree generalizing i with
  | leaf G low high => trivial
  | node G low high children ih =>
      simp only [d2FlowStageInvInputs]
      constructor
      · intro j
        exact ih j (i := i + 1) (by omega)
      · have hfalse : d2FlowCandidateActive d 12 i = false := by
          have hnot : ¬ (2 ≤ 12 ∧ 12 ≤ tfD2 d ∧ i % 2 = 12 % 2 ∧
              3 * i + 3 * d ≥ 2 * 12 + 11 ∧ 3 * i < 12 + 8) := by omega
          simp [d2FlowCandidateActive, hnot]
          omega
        simp [hfalse]

/-- The stage-twelve bottom-rise sender needs only balance at its root; all
descendant sender gates are inactive. The remaining actual-state obligation is
to derive `low + high = G` for each live level-six node after stage eleven. -/
theorem d2FlowCandidateStage12_botRise_inputs
    {d h G low high : Nat} (hd : 13 ≤ d)
    (children : Fin 8 → D2FlowTree h) (hbal : low + high = G) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 12)
      (d2FlowCandidateRole d 12)
      (d2FlowCandidateQuota d 12)
      (fun k => d2FlowCandidateCapacity d k 12) 6
      (.node G low high children) := by
  rcases d2FlowCandidateStage12_frontiers d hd with
    ⟨_, _, _, _, _, _, hactive6, hrole6, _⟩
  simp only [d2FlowStageInvInputs]
  constructor
  · intro j
    exact d2FlowCandidateAny_stage12_inactive_inputs
      (d := d) (i := 7) (by omega) (children j)
  · rw [hactive6]
    simp only [if_true]
    constructor
    · exact hbal
    · rw [hrole6]
      trivial

end Chvatal.D2Reserve

namespace Chvatal.D2Reserve

/-- Package a balanced non-leaf level-six tree as a complete Stage-12 sender
input. This avoids unfolding the global run when applying the local gate. -/
theorem d2FlowCandidateStage12_botRise_inputs_of_balanced_tree
    {d height : Nat} (hd : 13 ≤ d) (hpos : 1 ≤ height)
    (tree : D2FlowTree height)
    (hbal : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 12)
      (d2FlowCandidateRole d 12)
      (d2FlowCandidateQuota d 12)
      (fun r => d2FlowCandidateCapacity d r 12) 6 tree := by
  cases tree with
  | leaf G low high => omega
  | node G low high children =>
      have hbal' : low + high = G := by
        simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hbal
      exact d2FlowCandidateStage12_botRise_inputs hd children hbal'

/-- The actual Run-12 level-six subtrees satisfy the complete bottom-rise
input predicate, including saturated states. -/
theorem d2FlowCandidateStage12_actual_levelSix_inputs
    (depth : Nat) (hd : 7 ≤ depth) :
    ∀ j k m l q s, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (depth + 6) 12)
      (d2FlowCandidateRole (depth + 6) 12)
      (d2FlowCandidateQuota (depth + 6) 12)
      (fun r => d2FlowCandidateCapacity (depth + 6) r 12) 6
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (depth + 6)
                    (d2FlowTreeInitial 8192 (depth + 6)) 12) j) k) m) l) q) s) := by
  intro j k m l q s
  have hbal := d2FlowCandidateStage12_actual_levelSix_balanced depth
    (by omega) j k m l q s
  exact d2FlowCandidateStage12_botRise_inputs_of_balanced_tree
    (d := depth + 6) (height := depth) (by omega) (by omega)
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (depth + 6)
                  (d2FlowTreeInitial 8192 (depth + 6)) 12) j) k) m) l) q) s)
    hbal

end Chvatal.D2Reserve
namespace Chvatal.D2Reserve

/-- The actual Run-12 root has zero deficit: Stage 10 descends at the root,
then the inactive root in Stage 11 preserves that reset. -/
theorem d2FlowCandidateStage12_root_zero
    (depth : Nat) (hd : 7 ≤ depth) :
    d2FlowTreeRootDeficit
      (d2FlowCandidateRun (depth + 6)
        (d2FlowTreeInitial 8192 (depth + 6)) 12) = 0 := by
  let d := depth + 6
  let initial := d2FlowTreeInitial 8192 d
  let before := d2FlowCandidateRun d initial 10
  have hzero10 : d2FlowTreeRootDeficit before = 0 := by
    simpa [d, initial, before] using
      d2FlowCandidateStage10_root_zero (depth + 1) (by omega)
  have hfront10 := d2FlowCandidateStage10_frontiers d (by omega)
  rcases hfront10 with ⟨hactive0, hrole0, _, _, _, _, _⟩
  have hzero11 : d2FlowTreeRootDeficit
      (d2FlowCandidateRun d initial 11) = 0 := by
    change d2FlowTreeRootDeficit
      (d2FlowCandidateStage (depth + 6) 10
        (d2FlowCandidateRun (depth + 6)
          (d2FlowTreeInitial 8192 (depth + 6)) 10)) = 0
    cases htree : d2FlowCandidateRun (depth + 6)
        (d2FlowTreeInitial 8192 (depth + 6)) 10 with
    | node G low high children =>
        have hG : G = 0 := by
          have hz : d2FlowTreeRootDeficit
              (d2FlowCandidateRun (depth + 6)
                (d2FlowTreeInitial 8192 (depth + 6)) 10) = 0 := by
            simpa [d, initial, before] using hzero10
          rw [htree] at hz
          simpa [d2FlowTreeRootDeficit] using hz
        have hstep := d2FlowStage_active_node_deficit
          (active := d2FlowCandidateActive d 10)
          (role := d2FlowCandidateRole d 10)
          (quota := d2FlowCandidateQuota d 10)
          (h := depth + 5) (i := 0) (G := G) (low := low)
          (high := high) children hactive0
        rw [hrole0] at hstep
        change d2FlowTreeRootDeficit
          (d2FlowStage (d2FlowCandidateActive d 10)
            (d2FlowCandidateRole d 10) (d2FlowCandidateQuota d 10)
            (depth + 6) 0 (.node G low high children)) = 0
        simpa [d2FlowCandidateStage, hG] using hstep
  have hinactive0 : d2FlowCandidateActive d 11 0 = false := by
    simp [d2FlowCandidateActive, tfD2]
  change d2FlowTreeRootDeficit
    (d2FlowCandidateStage d 11 (d2FlowCandidateRun d initial 11)) = 0
  unfold d2FlowCandidateStage
  rw [d2FlowStage_root_deficit_of_inactive
    (active := d2FlowCandidateActive d 11)
    (role := d2FlowCandidateRole d 11)
    (quota := d2FlowCandidateQuota d 11)
    (h := d) (i := 0) (d2FlowCandidateRun d initial 11) hinactive0]
  simpa [d, initial] using hzero11

/-- Since level five is inactive in Stage 12, its recursive input contract
follows directly from the actual level-six bottom-rise gates. -/
theorem d2FlowCandidateStage12_actual_levelFive_inputs
    (depth : Nat) (hd : 7 ≤ depth) :
    ∀ j k m l q, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (depth + 6) 12)
      (d2FlowCandidateRole (depth + 6) 12)
      (d2FlowCandidateQuota (depth + 6) 12)
      (fun r => d2FlowCandidateCapacity (depth + 6) r 12) 5
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (depth + 6)
                  (d2FlowTreeInitial 8192 (depth + 6)) 12) j) k) m) l) q) := by
  have hlevelSix := d2FlowCandidateStage12_actual_levelSix_inputs depth hd
  have hinactive5 : d2FlowCandidateActive (depth + 6) 12 5 = false := by
    simp [d2FlowCandidateActive, tfD2]
  intro j k m l q
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (depth + 6)
              (d2FlowTreeInitial 8192 (depth + 6)) 12) j) k) m) l) q
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive (depth + 6) 12)
    (d2FlowCandidateRole (depth + 6) 12)
    (d2FlowCandidateQuota (depth + 6) 12)
    (fun r => d2FlowCandidateCapacity (depth + 6) r 12) 5 tree
  cases htree : tree with
  | node G low high children =>
      simp only [d2FlowStageInvInputs, hinactive5, if_false]
      constructor
      · intro s
        have hactual := hlevelSix j k m l q s
        change d2FlowStageInvInputs 8192
          (d2FlowCandidateActive (depth + 6) 12)
          (d2FlowCandidateRole (depth + 6) 12)
          (d2FlowCandidateQuota (depth + 6) 12)
          (fun r => d2FlowCandidateCapacity (depth + 6) r 12) 6
          (d2FlowTreeChild tree s) at hactual
        rw [htree] at hactual
        simpa only [d2FlowTreeChild] using hactual
      · trivial

/-- Stage 11's level-five bot-descending quota supplies both endpoint
reserves for the following Stage-12 level-four mid sender. -/
theorem d2FlowCandidateStage12_levelFour_endpoint_reserve
    (depth : Nat) (hd : 7 ≤ depth) :
    ∀ j k m l q, d2FlowCandidateCapacity (depth + 6) 4 12 ≤
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (depth + 6)
                    (d2FlowTreeInitial 8192 (depth + 6)) 12) j) k) m) l) q) := by
  intro j k m l q
  let d := depth + 6
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 11
  let sourceFour := d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild before j) k) m) l
  let outputFive := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 12) j) k) m) l) q
  have hfront := d2FlowCandidateStage11_frontiers d (by omega)
  rcases hfront with ⟨_, _, _, _, hactive5, hrole5, _⟩
  have hproject := d2FlowStage_path5_projection
    (active := d2FlowCandidateActive d 11)
    (role := d2FlowCandidateRole d 11)
    (quota := d2FlowCandidateQuota d 11)
    (h := depth + 1) (i := 0) before j k m l q
  have hproject' : d2FlowTreeRootDeficit outputFive =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 11)
            (d2FlowCandidateRole d 11) (d2FlowCandidateQuota d 11)
            (depth + 2) 4 sourceFour) q) := by
    simpa [outputFive, before, sourceFour, d,
      d2FlowCandidateRun, d2FlowCandidateStage] using hproject
  have hinactive4 : d2FlowCandidateActive d 11 4 = false := by
    simp [d2FlowCandidateActive, tfD2]
  cases hfour : sourceFour with
  | node G4 low4 high4 children4 =>
      have hchild := d2FlowStage_inactive_child
        (active := d2FlowCandidateActive d 11)
        (role := d2FlowCandidateRole d 11)
        (quota := d2FlowCandidateQuota d 11)
        (h := depth + 1) (i := 4) (G := G4) (low := low4)
        (high := high4) children4 hinactive4 q
      have hfiveProj :
          d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 11)
              (d2FlowCandidateRole d 11) (d2FlowCandidateQuota d 11)
              (depth + 2) 4 (.node G4 low4 high4 children4)) q =
          d2FlowStage (d2FlowCandidateActive d 11)
            (d2FlowCandidateRole d 11) (d2FlowCandidateQuota d 11)
            (depth + 1) 5 (children4 q) := by
        exact hchild
      rw [hfour, hfiveProj] at hproject'
      cases hfive : children4 q with
      | node G5 low5 high5 children5 =>
          have hstep := d2FlowStage_active_node_deficit
            (active := d2FlowCandidateActive d 11)
            (role := d2FlowCandidateRole d 11)
            (quota := d2FlowCandidateQuota d 11)
            (h := depth) (i := 5) (G := G5) (low := low5)
            (high := high5) children5 hactive5
          rw [hrole5] at hstep
          have hquota : d2FlowCandidateQuota d 11 5 .botDesc =
              15 * 2 ^ (3 * d - 10) := by
            simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
            omega
          have hcap : d2FlowCandidateCapacity d 4 12 =
              2 ^ (3 * d - 3) := by
            rcases d2FlowCandidateStage12_levelFour_parameters d (by omega)
              with ⟨hcap, _⟩
            exact hcap
          have hscale : 3 * d - 3 = 7 + (3 * d - 10) := by omega
          have hquotaReserve : d2FlowCandidateCapacity d 4 12 ≤
              128 * d2FlowCandidateQuota d 11 5 .botDesc := by
            rw [hcap, hquota, hscale, pow_add]
            norm_num
          have hroot : d2FlowTreeRootDeficit
              (d2FlowStage (d2FlowCandidateActive d 11)
                (d2FlowCandidateRole d 11) (d2FlowCandidateQuota d 11)
                (depth + 1) 5 (.node G5 low5 high5 children5)) =
              G5 + d2FlowCandidateQuota d 11 5 .botDesc := by
            simpa [hrole5] using hstep
          change d2FlowCandidateCapacity d 4 12 ≤
            128 * d2FlowTreeRootDeficit outputFive
          rw [hproject', hfive, hroot]
          exact hquotaReserve.trans
            (Nat.mul_le_mul_left 128 (Nat.le_add_left _ _))

set_option maxHeartbeats 10000000 in
/-- The actual Run-12 level-four mid-sender gates follow from the Stage-11
level-three cut, Stage-11's level-five bottom-descending endpoint writes, and
the already established level-six gates. -/
theorem d2FlowCandidateStage12_actual_levelFour_inputs
    (depth : Nat) (hd : 7 ≤ depth) :
    ∀ j k m l, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (depth + 6) 12)
      (d2FlowCandidateRole (depth + 6) 12)
      (d2FlowCandidateQuota (depth + 6) 12)
      (fun r => d2FlowCandidateCapacity (depth + 6) r 12) 4
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateRun (depth + 6)
                (d2FlowTreeInitial 8192 (depth + 6)) 12) j) k) m) l) := by
  intro j k m l
  let d := depth + 6
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 11
  let sourceThree := d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild before j) k) m
  let outputFour := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 12) j) k) m) l
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 12)
    (d2FlowCandidateRole d 12)
    (d2FlowCandidateQuota d 12)
    (fun r => d2FlowCandidateCapacity d r 12) 4 outputFour
  have hfront := d2FlowCandidateStage11_frontiers d (by omega)
  rcases hfront with ⟨_, _, hactive3, hrole3, _, _, _⟩
  have hinputsThree := d2FlowCandidateStage11_actual_levelThree_inputs
    depth (by omega) j k m
  have hinvGlobal := d2FlowCandidateStage10_preserves_inv
    (depth + 1) (by omega)
  have hinvTwo := d2FlowTreeInv_grandchild
    (h := depth + 4) before hinvGlobal j k
  have hprojection := d2FlowStage_path4_projection
    (active := d2FlowCandidateActive d 11)
    (role := d2FlowCandidateRole d 11)
    (quota := d2FlowCandidateQuota d 11)
    (h := depth + 2) (i := 0) before j k m l
  have hprojection' : outputFour =
      d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 11)
          (d2FlowCandidateRole d 11) (d2FlowCandidateQuota d 11)
          (depth + 3) 3 sourceThree) l := by
    simpa [outputFour, before, sourceThree, d,
      d2FlowCandidateRun, d2FlowCandidateStage] using hprojection
  cases htwo : d2FlowTreeChild (d2FlowTreeChild before j) k with
  | node G2 low2 high2 children2 =>
      have hinvTwo' : d2FlowTreeInv 8192
          (.node G2 low2 high2 children2) := by
        simpa [htwo] using hinvTwo
      have hinvThree := hinvTwo'.2.2.2 m
      cases hthree : sourceThree with
      | node G3 low3 high3 children3 =>
          have hinvThree' : d2FlowTreeInv 8192
              (.node G3 low3 high3 children3) := by
            have hsrc : children2 m = .node G3 low3 high3 children3 := by
              have hh := hthree
              change d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild before j) k) m = _ at hh
              rw [htwo] at hh
              simpa only [d2FlowTreeChild] using hh
            have hgrandInv : d2FlowTreeInv 8192 (children2 m) := hinvThree
            rw [hsrc] at hgrandInv
            exact hgrandInv
          have hinputsThree' := hinputsThree
          change d2FlowStageInvInputs 8192
            (d2FlowCandidateActive d 11)
            (d2FlowCandidateRole d 11)
            (d2FlowCandidateQuota d 11)
            (fun r => d2FlowCandidateCapacity d r 11) 3 sourceThree
            at hinputsThree'
          rw [hthree] at hinputsThree'
          have hchildCap := d2FlowStage_regular_child_g_bound_of_tree_inputs
            (active := d2FlowCandidateActive d 11)
            (role := d2FlowCandidateRole d 11)
            (quota := d2FlowCandidateQuota d 11)
            (cap := fun r => d2FlowCandidateCapacity d r 11)
            (stageDepth := depth + 2) (i := 3)
            (.node G3 low3 high3 children3) hactive3
            (Or.inr (Or.inl hrole3)) hinvThree' hinputsThree'
          have hchildBalanced := d2FlowStage_regular_child_balanced
            (active := d2FlowCandidateActive d 11)
            (role := d2FlowCandidateRole d 11)
            (quota := d2FlowCandidateQuota d 11)
            (h := depth + 2) (i := 3) (G := G3)
            (low := low3) (high := high3) children3 hactive3
            (Or.inr (Or.inl hrole3)) l
          have hprojectionNode : outputFour =
              d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive d 11)
                  (d2FlowCandidateRole d 11) (d2FlowCandidateQuota d 11)
                  (depth + 3) 3 (.node G3 low3 high3 children3)) l := by
            simpa [hthree] using hprojection'
          have hcapRelation :
              2 * d2FlowCandidateCapacity d 3 11 =
                d2FlowCandidateCapacity d 4 12 := by
            have hexp : d2FlowCandidateCapacityExponent d 4 12 =
                d2FlowCandidateCapacityExponent d 3 11 + 1 := by
              simp [d2FlowCandidateCapacityExponent]
              omega
            unfold d2FlowCandidateCapacity
            rw [hexp, Nat.pow_succ]
            omega
          have hreserve := d2FlowCandidateStage12_levelFour_endpoint_reserve
            depth hd j k m l
          have hrecursive : ∀ q : Fin 8, d2FlowStageInvInputs 8192
              (d2FlowCandidateActive d 12)
              (d2FlowCandidateRole d 12)
              (d2FlowCandidateQuota d 12)
              (fun r => d2FlowCandidateCapacity d r 12) 5
              (d2FlowTreeChild outputFour q) := by
            intro q
            have hq := d2FlowCandidateStage12_actual_levelFive_inputs
              depth hd j k m l q
            change d2FlowStageInvInputs 8192
              (d2FlowCandidateActive d 12)
              (d2FlowCandidateRole d 12)
              (d2FlowCandidateQuota d 12)
              (fun r => d2FlowCandidateCapacity d r 12) 5
              (d2FlowTreeChild outputFour q) at hq
            exact hq
          cases hfour : outputFour with
          | node G4 low4 high4 children4 =>
              have hG : 512 * G4 ≤
                  d2FlowCandidateCapacity d 4 12 := by
                have hg := hchildCap l
                rw [← hprojectionNode, hcapRelation] at hg
                simpa [hfour, d2FlowTreeRootDeficit] using hg
              have hbalance : low4 + high4 = G4 := by
                have hb := hchildBalanced
                rw [← hprojectionNode] at hb
                rw [hfour] at hb
                simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hb
              have hleft : d2FlowCandidateCapacity d 4 12 ≤
                  128 * d2FlowTreeRootDeficit (children4 ⟨0, by omega⟩) := by
                have hl := hreserve ⟨0, by omega⟩
                change d2FlowCandidateCapacity d 4 12 ≤
                  128 * d2FlowTreeRootDeficit
                    (d2FlowTreeChild outputFour ⟨0, by omega⟩) at hl
                rw [hfour] at hl
                simpa only [d2FlowTreeChild] using hl
              have hright : d2FlowCandidateCapacity d 4 12 ≤
                  128 * d2FlowTreeRootDeficit (children4 ⟨7, by omega⟩) := by
                have hr := hreserve ⟨7, by omega⟩
                change d2FlowCandidateCapacity d 4 12 ≤
                  128 * d2FlowTreeRootDeficit
                    (d2FlowTreeChild outputFour ⟨7, by omega⟩) at hr
                rw [hfour] at hr
                simpa only [d2FlowTreeChild] using hr
              have htotal :=
                d2FlowCandidateStage12_levelFour_boundary_mass_suffices
                  d (by omega) G4 hG children4 hleft
              have hrecursive' : ∀ q : Fin 8, d2FlowStageInvInputs 8192
                  (d2FlowCandidateActive d 12)
                  (d2FlowCandidateRole d 12)
                  (d2FlowCandidateQuota d 12)
                  (fun r => d2FlowCandidateCapacity d r 12) 5
                  (children4 q) := by
                intro q
                have hq := hrecursive q
                rw [hfour] at hq
                simpa only [d2FlowTreeChild] using hq
              simpa [hfour] using
                (d2FlowCandidateStage12_mid_inputs d (by omega)
                  G4 low4 high4 hbalance hG children4 hrecursive'
                  hleft hright htotal)

/-- The actual Stage-12 level-two mid sender's capacity and quota. -/
theorem d2FlowCandidateStage12_levelTwo_parameters
    (d : Nat) (hd : 13 ≤ d) :
    d2FlowCandidateCapacity d 2 12 = 2 ^ (3 * d - 9) ∧
      d2FlowCandidateQuota d 12 2 .mid = 15 * 2 ^ (3 * d - 21) := by
  constructor
  · simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  · simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega

/-- A level-two sender cap and one endpoint reserve pay the Stage-12
level-two mid quota from the child pool. -/
theorem d2FlowCandidateStage12_levelTwo_boundary_mass_suffices
    (d : Nat) (hd : 13 ≤ d) (G : Nat)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 2 12) {r : Nat}
    (children : Fin 8 → D2FlowTree r)
    (hleft : d2FlowCandidateCapacity d 2 12 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩)) :
    d2FlowCandidateQuota d 12 2 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
  rcases d2FlowCandidateStage12_levelTwo_parameters d hd with ⟨hcap, hquota⟩
  have hGsmall : G ≤ 2 ^ (3 * d - 18) := by
    rw [hcap] at hG
    have hp : 512 * 2 ^ (3 * d - 18) = 2 ^ (3 * d - 9) := by
      rw [show (512 : Nat) = 2 ^ 9 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hroot : 2 ^ (3 * d - 16) ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hcap] at hleft
    have hp : 128 * 2 ^ (3 * d - 16) = 2 ^ (3 * d - 9) := by
      rw [show (128 : Nat) = 2 ^ 7 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hrootTotal : d2FlowTreeRootDeficit (children ⟨0, by omega⟩) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    let f : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
    change f ⟨0, by omega⟩ ≤ Finset.univ.sum f
    exact Finset.single_le_sum
      (fun j hj => Nat.zero_le (f j))
      (Finset.mem_univ (⟨0, by omega⟩ : Fin 8))
  have hpG : 2 ^ (3 * d - 18) = 8 * 2 ^ (3 * d - 21) := by
    rw [show 3 * d - 18 = 3 + (3 * d - 21) by omega, pow_add]
    norm_num
  have hpRoot : 2 ^ (3 * d - 16) = 32 * 2 ^ (3 * d - 21) := by
    rw [show 3 * d - 16 = 5 + (3 * d - 21) by omega, pow_add]
    norm_num
  have hmass : G + d2FlowCandidateQuota d 12 2 .mid ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hquota]
    rw [hpG] at hGsmall
    rw [hpRoot] at hroot
    nlinarith
  have hmassTotal : G + d2FlowCandidateQuota d 12 2 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) :=
    le_trans hmass hrootTotal
  omega

/-- Complete local recursive input gate for a Stage-12 level-two mid
sender. -/
theorem d2FlowCandidateStage12_levelTwo_mid_inputs
    (d : Nat) (hd : 13 ≤ d) (G low high : Nat) {r : Nat}
    (hbalance : low + high = G)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 2 12)
    (children : Fin 8 → D2FlowTree r)
    (hrecursive : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 12)
      (d2FlowCandidateRole d 12)
      (d2FlowCandidateQuota d 12)
      (fun k => d2FlowCandidateCapacity d k 12) 3 (children j))
    (hleft : d2FlowCandidateCapacity d 2 12 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hright : d2FlowCandidateCapacity d 2 12 ≤
      128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩))
    (htotal : d2FlowCandidateQuota d 12 2 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 12)
      (d2FlowCandidateRole d 12)
      (d2FlowCandidateQuota d 12)
      (fun k => d2FlowCandidateCapacity d k 12) 2
      (.node G low high children) := by
  rcases d2FlowCandidateStage12_frontiers d hd with
    ⟨_, _, hactive, hrole, _, _, _, _, _⟩
  have ⟨hcap, hquota⟩ := d2FlowCandidateStage12_levelTwo_parameters d hd
  have hquotaEven : d2FlowCandidateQuota d 12 2 .mid % 2 = 0 := by
    rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 21 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 12 2 .mid ≤
      d2FlowCandidateCapacity d 2 12 := by
    rw [hquota, hcap]
    have hp : 256 * 15 * 2 ^ (3 * d - 21) =
        3840 * 2 ^ (3 * d - 21) := by norm_num
    have hpCap : 2 ^ (3 * d - 9) = 4096 * 2 ^ (3 * d - 21) := by
      rw [show 3 * d - 9 = 12 + (3 * d - 21) by omega, pow_add]
      norm_num
    nlinarith [hp, hpCap]
  simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
  exact ⟨hrecursive, ⟨hbalance, hG, hquotaCap, htotal,
    hquotaEven, hleft, hright⟩⟩

set_option maxHeartbeats 10000000 in
/-- The inactive Stage-12 level-three contract follows recursively from the
actual level-four mid-sender gates. -/
theorem d2FlowCandidateStage12_actual_levelThree_inputs
    (depth : Nat) (hd : 7 ≤ depth) :
    ∀ j k m, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (depth + 6) 12)
      (d2FlowCandidateRole (depth + 6) 12)
      (d2FlowCandidateQuota (depth + 6) 12)
      (fun r => d2FlowCandidateCapacity (depth + 6) r 12) 3
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (depth + 6)
              (d2FlowTreeInitial 8192 (depth + 6)) 12) j) k) m) := by
  have hlevelFour := d2FlowCandidateStage12_actual_levelFour_inputs depth hd
  have hinactive3 : d2FlowCandidateActive (depth + 6) 12 3 = false := by
    simp [d2FlowCandidateActive, tfD2]
  intro j k m
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowCandidateRun (depth + 6)
          (d2FlowTreeInitial 8192 (depth + 6)) 12) j) k) m
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive (depth + 6) 12)
    (d2FlowCandidateRole (depth + 6) 12)
    (d2FlowCandidateQuota (depth + 6) 12)
    (fun r => d2FlowCandidateCapacity (depth + 6) r 12) 3 tree
  cases htree : tree with
  | node G low high children =>
      simp only [d2FlowStageInvInputs, hinactive3, if_false]
      constructor
      · intro l
        have hactual := hlevelFour j k m l
        change d2FlowStageInvInputs 8192
          (d2FlowCandidateActive (depth + 6) 12)
          (d2FlowCandidateRole (depth + 6) 12)
          (d2FlowCandidateQuota (depth + 6) 12)
          (fun r => d2FlowCandidateCapacity (depth + 6) r 12) 4
          (d2FlowTreeChild tree l) at hactual
        rw [htree] at hactual
        simpa only [d2FlowTreeChild] using hactual
      · trivial

set_option maxHeartbeats 10000000 in
/-- Stage 11's level-three mid sender adds enough root quota to each
level-three output to supply the next Stage-12 level-two endpoint reserve. -/
theorem d2FlowCandidateStage12_levelTwo_endpoint_reserve
    (depth : Nat) (hd : 7 ≤ depth) :
    ∀ j k m, d2FlowCandidateCapacity (depth + 6) 2 12 ≤
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateRun (depth + 6)
                (d2FlowTreeInitial 8192 (depth + 6)) 12) j) k) m) := by
  intro j k m
  let d := depth + 6
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 11
  let sourceTwo := d2FlowTreeChild (d2FlowTreeChild before j) k
  let outputThree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 12) j) k) m
  change d2FlowCandidateCapacity d 2 12 ≤
    128 * d2FlowTreeRootDeficit outputThree
  have hfront := d2FlowCandidateStage11_frontiers d (by omega)
  rcases hfront with ⟨_, _, hactive3, hrole3, _, _, _⟩
  have hinactive2 : d2FlowCandidateActive d 11 2 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hprojection := d2FlowStage_path3_projection
    (active := d2FlowCandidateActive d 11)
    (role := d2FlowCandidateRole d 11)
    (quota := d2FlowCandidateQuota d 11)
    (h := depth + 3) (i := 0) before j k m
  have hprojectionRoot := congrArg d2FlowTreeRootDeficit hprojection
  have hprojection' : d2FlowTreeRootDeficit outputThree =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 11)
            (d2FlowCandidateRole d 11) (d2FlowCandidateQuota d 11)
            (depth + 4) 2 sourceTwo) m) := by
    simpa [outputThree, before, sourceTwo, d,
      d2FlowCandidateRun, d2FlowCandidateStage] using hprojectionRoot
  cases htwo : sourceTwo with
  | node G2 low2 high2 children2 =>
      have hchild := d2FlowStage_inactive_child
        (active := d2FlowCandidateActive d 11)
        (role := d2FlowCandidateRole d 11)
        (quota := d2FlowCandidateQuota d 11)
        (h := depth + 3) (i := 2) (G := G2) (low := low2)
        (high := high2) children2 hinactive2 m
      have hsource : children2 m =
          d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild before j) k) m := by
        have hh := htwo
        simp only [sourceTwo] at hh
        rw [hh]
        rfl
      cases hthree : children2 m with
      | node G3 low3 high3 children3 =>
          have hquota : d2FlowCandidateQuota d 11 3 .mid =
              15 * 2 ^ (3 * d - 16) := by
            simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
            omega
          have hcap : d2FlowCandidateCapacity d 2 12 =
              2 ^ (3 * d - 9) := by
            rcases d2FlowCandidateStage12_levelTwo_parameters d (by omega)
              with ⟨hcap, _⟩
            exact hcap
          have hscale : 3 * d - 9 = 7 + (3 * d - 16) := by omega
          have hquotaReserve : d2FlowCandidateCapacity d 2 12 ≤
              128 * d2FlowCandidateQuota d 11 3 .mid := by
            rw [hcap, hquota, hscale, pow_add]
            norm_num
          have hroot := d2FlowStage_active_node_deficit
            (active := d2FlowCandidateActive d 11)
            (role := d2FlowCandidateRole d 11)
            (quota := d2FlowCandidateQuota d 11)
            (h := depth + 2) (i := 3) (G := G3)
            (low := low3) (high := high3) children3
            hactive3
          have hpost : d2FlowTreeRootDeficit
              (d2FlowStage (d2FlowCandidateActive d 11)
                (d2FlowCandidateRole d 11) (d2FlowCandidateQuota d 11)
                (depth + 3) 3 (.node G3 low3 high3 children3)) =
              G3 + d2FlowCandidateQuota d 11 3 .mid := by
            simpa [hrole3] using hroot
          rw [htwo, hchild, hthree] at hprojection'
          change d2FlowCandidateCapacity d 2 12 ≤
            128 * d2FlowTreeRootDeficit outputThree
          rw [hprojection', hpost]
          exact hquotaReserve.trans
            (Nat.mul_le_mul_left 128 (Nat.le_add_left _ _))

set_option maxHeartbeats 10000000 in
/-- The actual Run-12 level-two mid-sender gates follow from Stage 11's
level-one top-rise update, the level-three endpoint reserves, and the proved
level-four recursive gates. -/
theorem d2FlowCandidateStage12_actual_levelTwo_inputs
    (depth : Nat) (hd : 7 ≤ depth) :
    ∀ j k, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (depth + 6) 12)
      (d2FlowCandidateRole (depth + 6) 12)
      (d2FlowCandidateQuota (depth + 6) 12)
      (fun r => d2FlowCandidateCapacity (depth + 6) r 12) 2
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun (depth + 6)
            (d2FlowTreeInitial 8192 (depth + 6)) 12) j) k) := by
  intro j k
  let d := depth + 6
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 11
  let sourceOne := d2FlowTreeChild before j
  let outputTwo := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 12) j) k
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 12)
    (d2FlowCandidateRole d 12)
    (d2FlowCandidateQuota d 12)
    (fun r => d2FlowCandidateCapacity d r 12) 2 outputTwo
  have hfront := d2FlowCandidateStage11_frontiers d (by omega)
  rcases hfront with ⟨hactive1, hrole1, _, _, _, _, _⟩
  have hinputsOne := d2FlowCandidateStage11_actual_levelOne_inputs
    depth (by omega) j
  have hinvGlobal := d2FlowCandidateStage10_preserves_inv
    (depth + 1) (by omega)
  have hreserve := d2FlowCandidateStage12_levelTwo_endpoint_reserve
    depth hd j k
  have hrecursiveThree := d2FlowCandidateStage12_actual_levelThree_inputs
    depth hd j k
  have hinactive0 : d2FlowCandidateActive d 11 0 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hcapRelation :
      2 * d2FlowCandidateCapacity d 1 11 =
        d2FlowCandidateCapacity d 2 12 := by
    have hexp : d2FlowCandidateCapacityExponent d 2 12 =
        d2FlowCandidateCapacityExponent d 1 11 + 1 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    unfold d2FlowCandidateCapacity
    rw [hexp, Nat.pow_succ]
    omega
  cases hroot : d2FlowCandidateRun (depth + 6)
      (d2FlowTreeInitial 8192 (depth + 6)) 11 with
  | node G0 low0 high0 children0 =>
      have hrootChild := d2FlowStage_inactive_child
        (active := d2FlowCandidateActive d 11)
        (role := d2FlowCandidateRole d 11)
        (quota := d2FlowCandidateQuota d 11)
        (h := depth + 5) (i := 0) (G := G0) (low := low0)
        (high := high0) children0 hinactive0 j
      have hsourceRoot : sourceOne = children0 j := by
        change d2FlowTreeChild
          (d2FlowCandidateRun (depth + 6)
            (d2FlowTreeInitial 8192 (depth + 6)) 11) j = children0 j
        rw [hroot]
        rfl
      have hprojection : outputTwo =
          d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 11)
              (d2FlowCandidateRole d 11) (d2FlowCandidateQuota d 11)
              (depth + 5) 1 (children0 j)) k := by
        have hproj := congrArg (fun tree => d2FlowTreeChild tree k) hrootChild
        have hrun12 : d2FlowCandidateRun (depth + 6)
            (d2FlowTreeInitial 8192 (depth + 6)) 12 =
            d2FlowCandidateStage (depth + 6) 11
              (d2FlowCandidateRun (depth + 6)
                (d2FlowTreeInitial 8192 (depth + 6)) 11) := by
          rfl
        change d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (depth + 6)
              (d2FlowTreeInitial 8192 (depth + 6)) 12) j) k = _
        rw [hrun12, hroot]
        simpa [d2FlowCandidateStage] using hproj
      have hinvOne : d2FlowTreeInv 8192 sourceOne := by
        have hrootInv := hinvGlobal
        change d2FlowTreeInv 8192
          (d2FlowCandidateRun (depth + 6)
            (d2FlowTreeInitial 8192 (depth + 6)) 11) at hrootInv
        rw [hroot] at hrootInv
        have hchildInv := hrootInv.2.2.2 j
        exact Eq.mp (congrArg (d2FlowTreeInv 8192) hsourceRoot.symm) hchildInv
      have hinputsOne' := hinputsOne
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 11)
        (d2FlowCandidateRole d 11)
        (d2FlowCandidateQuota d 11)
        (fun r => d2FlowCandidateCapacity d r 11) 1 sourceOne
        at hinputsOne'
      cases hparent : sourceOne with
      | node G1 low1 high1 children1 =>
          have hinvOne' : d2FlowTreeInv 8192
              (.node G1 low1 high1 children1) := by
            simpa [hparent] using hinvOne
          rw [hparent] at hinputsOne'
          have hchildCap := d2FlowStage_regular_child_g_bound_of_tree_inputs
            (active := d2FlowCandidateActive d 11)
            (role := d2FlowCandidateRole d 11)
            (quota := d2FlowCandidateQuota d 11)
            (cap := fun r => d2FlowCandidateCapacity d r 11)
            (stageDepth := depth + 4) (i := 1)
            (.node G1 low1 high1 children1) hactive1
            (Or.inl hrole1) hinvOne' hinputsOne'
          have hchildBalanced := d2FlowStage_regular_child_balanced
            (active := d2FlowCandidateActive d 11)
            (role := d2FlowCandidateRole d 11)
            (quota := d2FlowCandidateQuota d 11)
            (h := depth + 4) (i := 1) (G := G1)
            (low := low1) (high := high1) children1 hactive1
            (Or.inl hrole1) k
          have hsourceOne : children0 j =
              .node G1 low1 high1 children1 := by
            exact hsourceRoot.symm.trans hparent
          have hprojectionParent : outputTwo =
              d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive d 11)
                  (d2FlowCandidateRole d 11) (d2FlowCandidateQuota d 11)
                  (depth + 5) 1 (.node G1 low1 high1 children1)) k := by
            simpa [hsourceOne] using hprojection
          cases htwo : outputTwo with
          | node G2 low2 high2 children2 =>
              have hG : 512 * G2 ≤
                  d2FlowCandidateCapacity d 2 12 := by
                have hg := hchildCap k
                rw [← hprojectionParent, hcapRelation] at hg
                simpa [htwo, d2FlowTreeRootDeficit] using hg
              have hbalance : low2 + high2 = G2 := by
                have hb := hchildBalanced
                rw [← hprojectionParent, htwo] at hb
                simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hb
              have hleft : d2FlowCandidateCapacity d 2 12 ≤
                  128 * d2FlowTreeRootDeficit (children2 ⟨0, by omega⟩) := by
                have hl := hreserve ⟨0, by omega⟩
                change d2FlowCandidateCapacity d 2 12 ≤
                  128 * d2FlowTreeRootDeficit
                    (d2FlowTreeChild outputTwo ⟨0, by omega⟩) at hl
                rw [htwo] at hl
                simpa only [d2FlowTreeChild] using hl
              have hright : d2FlowCandidateCapacity d 2 12 ≤
                  128 * d2FlowTreeRootDeficit (children2 ⟨7, by omega⟩) := by
                have hr := hreserve ⟨7, by omega⟩
                change d2FlowCandidateCapacity d 2 12 ≤
                  128 * d2FlowTreeRootDeficit
                    (d2FlowTreeChild outputTwo ⟨7, by omega⟩) at hr
                rw [htwo] at hr
                simpa only [d2FlowTreeChild] using hr
              have hrecursive : ∀ q : Fin 8,
                  d2FlowStageInvInputs 8192
                    (d2FlowCandidateActive d 12)
                    (d2FlowCandidateRole d 12)
                    (d2FlowCandidateQuota d 12)
                    (fun r => d2FlowCandidateCapacity d r 12) 3
                    (children2 q) := by
                intro q
                have hq := hrecursiveThree q
                change d2FlowStageInvInputs 8192
                  (d2FlowCandidateActive d 12)
                  (d2FlowCandidateRole d 12)
                  (d2FlowCandidateQuota d 12)
                  (fun r => d2FlowCandidateCapacity d r 12) 3
                  (d2FlowTreeChild outputTwo q) at hq
                rw [htwo] at hq
                simpa only [d2FlowTreeChild] using hq
              have htotal :=
                d2FlowCandidateStage12_levelTwo_boundary_mass_suffices
                  d (by omega) G2 hG children2 hleft
              simpa [htwo] using
                (d2FlowCandidateStage12_levelTwo_mid_inputs d (by omega)
                  G2 low2 high2 hbalance hG children2 hrecursive
                  hleft hright htotal)

set_option maxHeartbeats 10000000 in
/-- Assemble the complete recursive input predicate for the actual Stage-12
root from its root reset and the proved level-two sender gates. -/
theorem d2FlowCandidateStage12_actual_inputs
    (depth : Nat) (hd : 7 <= depth) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (depth + 6) 12)
      (d2FlowCandidateRole (depth + 6) 12)
      (d2FlowCandidateQuota (depth + 6) 12)
      (fun q => d2FlowCandidateCapacity (depth + 6) q 12) 0
      (d2FlowCandidateRun (depth + 6)
        (d2FlowTreeInitial 8192 (depth + 6)) 12) := by
  let d := depth + 6
  let tree := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 12
  have hfront := d2FlowCandidateStage12_frontiers d (by omega)
  rcases hfront with ⟨hactive0, hrole0, _, _, _, _, _, _, _⟩
  have hinactive1 : d2FlowCandidateActive d 12 1 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hrootZero := d2FlowCandidateStage12_root_zero depth hd
  have hinv := d2FlowCandidateStage11_preserves_inv depth (by omega)
  change d2FlowTreeInv 8192 tree at hinv
  change d2FlowTreeRootDeficit tree = 0 at hrootZero
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 12)
    (d2FlowCandidateRole d 12)
    (d2FlowCandidateQuota d 12)
    (fun q => d2FlowCandidateCapacity d q 12) 0 tree
  have hrecursive : forall j,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 12)
        (d2FlowCandidateRole d 12)
        (d2FlowCandidateQuota d 12)
        (fun q => d2FlowCandidateCapacity d q 12) 1
        (d2FlowTreeChild tree j) := by
    intro j
    cases hnodeOne : d2FlowTreeChild tree j with
    | node G1 low1 high1 children1 =>
        have hrecursiveTwo : forall k,
            d2FlowStageInvInputs 8192
              (d2FlowCandidateActive d 12)
              (d2FlowCandidateRole d 12)
              (d2FlowCandidateQuota d 12)
              (fun q => d2FlowCandidateCapacity d q 12) 2
              (children1 k) := by
          intro k
          have hk := d2FlowCandidateStage12_actual_levelTwo_inputs
            depth hd j k
          change d2FlowStageInvInputs 8192
            (d2FlowCandidateActive d 12)
            (d2FlowCandidateRole d 12)
            (d2FlowCandidateQuota d 12)
            (fun q => d2FlowCandidateCapacity d q 12) 2
            (d2FlowTreeChild (d2FlowTreeChild tree j) k) at hk
          rw [hnodeOne] at hk
          simpa only [d2FlowTreeChild] using hk
        simp only [d2FlowStageInvInputs, hinactive1, if_false]
        exact And.intro hrecursiveTwo trivial
  change D2FlowTree (depth + 6) at tree
  cases hroot : tree with
  | node G low high children =>
      have hrootInv : d2FlowTreeInv 8192 (.node G low high children) := by
        rw [hroot] at hinv
        exact hinv
      have hG : G = 0 := by
        have hz := hrootZero
        rw [hroot] at hz
        simpa [d2FlowTreeRootDeficit] using hz
      have hbalance : low + high = G := by
        have hlt : G < 8192 * 8 ^ (depth + 6) := by
          rw [hG]
          positivity
        exact hrootInv.2.2.1 hlt
      have hchildren : forall j,
          d2FlowStageInvInputs 8192
            (d2FlowCandidateActive d 12)
            (d2FlowCandidateRole d 12)
            (d2FlowCandidateQuota d 12)
            (fun q => d2FlowCandidateCapacity d q 12) 1
            (children j) := by
        intro j
        have hj := hrecursive j
        change d2FlowStageInvInputs 8192
          (d2FlowCandidateActive d 12)
          (d2FlowCandidateRole d 12)
          (d2FlowCandidateQuota d 12)
          (fun q => d2FlowCandidateCapacity d q 12) 1
          (d2FlowTreeChild tree j) at hj
        rw [hroot] at hj
        simpa only [d2FlowTreeChild] using hj
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 12)
        (d2FlowCandidateRole d 12)
        (d2FlowCandidateQuota d 12)
        (fun q => d2FlowCandidateCapacity d q 12) 0
        (.node G low high children)
      simp only [d2FlowStageInvInputs, hactive0, if_true, hrole0]
      exact And.intro hchildren (And.intro hbalance hG)

set_option maxHeartbeats 10000000 in
/-- The Stage-12 local gates preserve the invariant through its actual
finite-run transition. -/
theorem d2FlowCandidateStage12_preserves_inv
    (depth : Nat) (hd : 7 <= depth) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (depth + 6)
        (d2FlowTreeInitial 8192 (depth + 6)) 13) := by
  let d := depth + 6
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 12
  have hinv := d2FlowCandidateStage11_preserves_inv depth (by omega)
  have hinputs := d2FlowStageInvInputs_tolerant_of_strict before
    (d2FlowCandidateStage12_actual_inputs depth hd)
  have hpres := d2FlowStage_preserves_inv_of_tolerant_inputs
    (active := d2FlowCandidateActive d 12)
    (role := d2FlowCandidateRole d 12)
    (quota := d2FlowCandidateQuota d 12)
    (cap := fun q => d2FlowCandidateCapacity d q 12)
    (i := 0) before hinv hinputs
  change d2FlowTreeInv 8192
    (d2FlowCandidateStage d 12 before)
  simpa [d, before, d2FlowCandidateRun, d2FlowCandidateStage] using hpres

/-- Stage 13 repeats the odd-stage top-rise/mid/bottom-descending frontier.
This is the first role repetition after the Stage 12 finite bootstrap. -/
theorem d2FlowCandidateStage13_frontiers (d : Nat) (hd : 13 ≤ d) :
    d2FlowCandidateActive d 13 1 = true ∧
      d2FlowCandidateRole d 13 1 = .topRise ∧
      d2FlowCandidateActive d 13 3 = true ∧
      d2FlowCandidateRole d 13 3 = .mid ∧
      d2FlowCandidateActive d 13 5 = true ∧
      d2FlowCandidateRole d 13 5 = .botDesc ∧
      d2FlowCandidateActive d 13 7 = false := by
  have hactive1 : d2FlowCandidateActive d 13 1 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive3 : d2FlowCandidateActive d 13 3 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive5 : d2FlowCandidateActive d 13 5 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hinactive7 : d2FlowCandidateActive d 13 7 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have ha13 : alpha d 13 = 1 := by
    have h : 37 ≤ 3 * d := by omega
    simp [alpha, alphaStar, h, ceilParity]
  have ha14 : alpha d 14 = 0 := by
    have h : 39 ≤ 3 * d := by omega
    simp [alpha, alphaStar, h, ceilParity]
  have ho13 : omega 13 = 5 := by norm_num [omega, ceilParity]
  have ho14 : omega 14 = 6 := by norm_num [omega, ceilParity]
  have hrole1 : d2FlowCandidateRole d 13 1 = .topRise := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha13, ha14]
  have hrole3 : d2FlowCandidateRole d 13 3 = .mid := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha13, ho13]
  have hrole5 : d2FlowCandidateRole d 13 5 = .botDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha13, ho13, ho14]
  exact ⟨hactive1, hrole1, hactive3, hrole3,
    hactive5, hrole5, hinactive7⟩


theorem d2FlowCandidateStage13_levelThree_boundary_mass_suffices
    (d : Nat) (hd : 13 ≤ d) (G : Nat)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 3 13) {r : Nat}
    (children : Fin 8 → D2FlowTree r)
    (hleft : d2FlowCandidateCapacity d 3 13 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩)) :
    d2FlowCandidateQuota d 13 3 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
  have hcap : d2FlowCandidateCapacity d 3 13 = 2 ^ (3 * d - 8) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 13 3 .mid =
      15 * 2 ^ (3 * d - 20) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hGsmall : G ≤ 2 ^ (3 * d - 17) := by
    rw [hcap] at hG
    have hp : 512 * 2 ^ (3 * d - 17) = 2 ^ (3 * d - 8) := by
      rw [show (512 : Nat) = 2 ^ 9 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hroot : 2 ^ (3 * d - 15) ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hcap] at hleft
    have hp : 128 * 2 ^ (3 * d - 15) = 2 ^ (3 * d - 8) := by
      rw [show (128 : Nat) = 2 ^ 7 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hrootTotal : d2FlowTreeRootDeficit (children ⟨0, by omega⟩) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    let f : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
    change f ⟨0, by omega⟩ ≤ Finset.univ.sum f
    exact Finset.single_le_sum
      (fun j hj => Nat.zero_le (f j))
      (Finset.mem_univ (⟨0, by omega⟩ : Fin 8))
  have hpG : 2 ^ (3 * d - 17) = 8 * 2 ^ (3 * d - 20) := by
    rw [show 3 * d - 17 = 3 + (3 * d - 20) by omega, pow_add]
    norm_num
  have hpRoot : 2 ^ (3 * d - 15) = 32 * 2 ^ (3 * d - 20) := by
    rw [show 3 * d - 15 = 5 + (3 * d - 20) by omega, pow_add]
    norm_num
  have hmass : G + d2FlowCandidateQuota d 13 3 .mid ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hquota]
    rw [hpG] at hGsmall
    rw [hpRoot] at hroot
    nlinarith
  have hmassTotal : G + d2FlowCandidateQuota d 13 3 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) :=
    le_trans hmass hrootTotal
  omega


theorem d2FlowCandidateStage13_mid_inputs
    (d : Nat) (hd : 13 ≤ d) (G low high : Nat) {r : Nat}
    (hbalance : low + high = G)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 3 13)
    (children : Fin 8 → D2FlowTree r)
    (hrecursive : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 13)
      (d2FlowCandidateRole d 13)
      (d2FlowCandidateQuota d 13)
      (fun k => d2FlowCandidateCapacity d k 13) 4 (children j))
    (hleft : d2FlowCandidateCapacity d 3 13 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hright : d2FlowCandidateCapacity d 3 13 ≤
      128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩))
    (htotal : d2FlowCandidateQuota d 13 3 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 13)
      (d2FlowCandidateRole d 13)
      (d2FlowCandidateQuota d 13)
      (fun k => d2FlowCandidateCapacity d k 13) 3
      (.node G low high children) := by
  rcases d2FlowCandidateStage13_frontiers d hd with
    ⟨_, _, hactive, hrole, _, _, _⟩
  have hcap : d2FlowCandidateCapacity d 3 13 = 2 ^ (3 * d - 8) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 13 3 .mid =
      15 * 2 ^ (3 * d - 20) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hquotaEven : d2FlowCandidateQuota d 13 3 .mid % 2 = 0 := by
    rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 20 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 13 3 .mid ≤
      d2FlowCandidateCapacity d 3 13 := by
    rw [hquota, hcap]
    have hp : 256 * 2 ^ (3 * d - 20) = 2 ^ (3 * d - 12) := by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_add]
      congr 1 <;> omega
    have hpCap : 2 ^ (3 * d - 8) = 16 * 2 ^ (3 * d - 12) := by
      rw [show 3 * d - 8 = 4 + (3 * d - 12) by omega, pow_add]
      norm_num
    nlinarith [hp, hpCap]
  simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
  exact ⟨hrecursive, ⟨hbalance, hG, hquotaCap, htotal, hquotaEven,
    hleft, hright⟩⟩

/-- A stage-ten level-two endpoint reserve and sender cap suffice for its
mid-sender allocation inequality. -/

theorem d2FlowCandidateStage13_levelThree_endpoint_reserve
    (depth : Nat) (hd : 7 ≤ depth) :
    ∀ j k m l, d2FlowCandidateCapacity (depth + 6) 3 13 ≤
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (depth + 6)
                (d2FlowTreeInitial 8192 (depth + 6)) 13) j) k) m) l) := by
  intro j k m l
  let h := Nat.succ depth
  have hh : 7 ≤ h := by dsimp [h]; omega
  let d := h + 5
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 12
  let sourceThree := d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild before j) k) m
  let sourceFour := d2FlowTreeChild sourceThree l
  let outputFour := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 13) j) k) m) l
  have hfront := d2FlowCandidateStage12_frontiers d (by omega)
  rcases hfront with ⟨_, _, _, _, hactive4, hrole4, _⟩
  have hinactive3 : d2FlowCandidateActive d 12 3 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hproject := d2FlowStage_path4_projection
    (active := d2FlowCandidateActive d 12)
    (role := d2FlowCandidateRole d 12)
    (quota := d2FlowCandidateQuota d 12)
    (h := h + 1) (i := 0) before j k m l
  have hproject' : outputFour =
      d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 12)
          (d2FlowCandidateRole d 12) (d2FlowCandidateQuota d 12)
          (h + 2) 3 sourceThree) l := by
    simpa [outputFour, d, before, d2FlowCandidateRun,
      d2FlowCandidateStage, sourceThree] using hproject
  cases hthree : sourceThree with
  | node G3 low3 high3 children3 =>
      have hsourceFour : sourceFour = children3 l := by
        dsimp [sourceFour]
        rw [hthree]
        rfl
      have houtputStage : outputFour =
          d2FlowStage (d2FlowCandidateActive d 12)
            (d2FlowCandidateRole d 12) (d2FlowCandidateQuota d 12)
            (h + 1) 4 sourceFour := by
        calc
          outputFour = d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive d 12)
                (d2FlowCandidateRole d 12) (d2FlowCandidateQuota d 12)
                (h + 2) 3 sourceThree) l := hproject'
          _ = d2FlowStage (d2FlowCandidateActive d 12)
              (d2FlowCandidateRole d 12) (d2FlowCandidateQuota d 12)
              (h + 1) 4 (children3 l) := by
                rw [hthree]
                exact d2FlowStage_inactive_child
                  (active := d2FlowCandidateActive d 12)
                  (role := d2FlowCandidateRole d 12)
                  (quota := d2FlowCandidateQuota d 12)
                  (h := h + 1) (i := 3)
                  (G := G3) (low := low3) (high := high3)
                  children3 hinactive3 l
          _ = d2FlowStage (d2FlowCandidateActive d 12)
              (d2FlowCandidateRole d 12) (d2FlowCandidateQuota d 12)
              (h + 1) 4 sourceFour := by
                exact congrArg
                  (d2FlowStage (d2FlowCandidateActive d 12)
                    (d2FlowCandidateRole d 12)
                    (d2FlowCandidateQuota d 12) (h + 1) 4)
                  hsourceFour.symm
      cases hfour : sourceFour with
      | node G4 low4 high4 children4 =>
          have hstep := d2FlowStage_active_node_deficit
            (active := d2FlowCandidateActive d 12)
            (role := d2FlowCandidateRole d 12)
            (quota := d2FlowCandidateQuota d 12)
            (h := h) (i := 4) (G := G4) (low := low4) (high := high4)
            children4 hactive4
          rw [hrole4] at hstep
          have hroot : d2FlowTreeRootDeficit outputFour =
              G4 + d2FlowCandidateQuota d 12 4 .mid := by
            rw [houtputStage, hfour]
            exact hstep
          have hcap : d2FlowCandidateCapacity d 3 13 =
              2 ^ (3 * d - 8) := by
            simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
            omega
          have hquota : d2FlowCandidateQuota d 12 4 .mid =
              15 * 2 ^ (3 * d - 15) := by
            simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
            omega
          have hscale : 3 * d - 8 = 7 + (3 * d - 15) := by omega
          have hcapQuota : d2FlowCandidateCapacity d 3 13 ≤
              128 * d2FlowCandidateQuota d 12 4 .mid := by
            rw [hcap, hquota, hscale, pow_add]
            norm_num
          change d2FlowCandidateCapacity d 3 13 ≤
            128 * d2FlowTreeRootDeficit outputFour
          rw [hroot]
          nlinarith

/-- Half of Stage 11's level-five bottom-descending quota exceeds the
endpoint reserve needed by Stage 13's level-five sender. -/
theorem d2FlowCandidateStage13_levelFive_halfQuota_covers_capacity
    (d : Nat) (hd : 13 ≤ d) :
    d2FlowCandidateCapacity d 5 13 ≤
      128 * (d2FlowCandidateQuota d 11 5 .botDesc / 2) := by
  have hcap : d2FlowCandidateCapacity d 5 13 = 2 ^ (3 * d - 2) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 11 5 .botDesc =
      15 * 2 ^ (3 * d - 10) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hhalf : d2FlowCandidateQuota d 11 5 .botDesc / 2 =
      15 * 2 ^ (3 * d - 11) := by
    rw [hquota, show 3 * d - 10 = 1 + (3 * d - 11) by omega, pow_add]
    omega
  have hscale : 3 * d - 2 = 9 + (3 * d - 11) := by omega
  rw [hcap, hhalf, hscale, pow_add]
  nlinarith [show 0 < 2 ^ (3 * d - 11) by positivity]

/-- The Stage-13 bottom-descending quota fits in the child pool when one
endpoint reserve and the normalized sender cap hold. -/
theorem d2FlowCandidateStage13_levelFive_boundary_mass_suffices
    (d : Nat) (hd : 13 ≤ d) (G : Nat)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 5 13) {r : Nat}
    (children : Fin 8 → D2FlowTree r)
    (hleft : d2FlowCandidateCapacity d 5 13 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩)) :
    d2FlowCandidateQuota d 13 5 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
  have hcap : d2FlowCandidateCapacity d 5 13 = 2 ^ (3 * d - 2) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 13 5 .botDesc =
      15 * 2 ^ (3 * d - 14) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hGsmall : G ≤ 2 ^ (3 * d - 11) := by
    rw [hcap] at hG
    have hp : 512 * 2 ^ (3 * d - 11) = 2 ^ (3 * d - 2) := by
      rw [show (512 : Nat) = 2 ^ 9 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hroot : 2 ^ (3 * d - 9) ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hcap] at hleft
    have hp : 128 * 2 ^ (3 * d - 9) = 2 ^ (3 * d - 2) := by
      rw [show (128 : Nat) = 2 ^ 7 by norm_num, ← pow_add]
      congr 1 <;> omega
    nlinarith
  have hrootTotal : d2FlowTreeRootDeficit (children ⟨0, by omega⟩) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    let f : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
    change f ⟨0, by omega⟩ ≤ Finset.univ.sum f
    exact Finset.single_le_sum
      (fun j hj => Nat.zero_le (f j))
      (Finset.mem_univ (⟨0, by omega⟩ : Fin 8))
  have hpG : 2 ^ (3 * d - 11) = 8 * 2 ^ (3 * d - 14) := by
    rw [show 3 * d - 11 = 3 + (3 * d - 14) by omega, pow_add]
    norm_num
  have hpRoot : 2 ^ (3 * d - 9) = 32 * 2 ^ (3 * d - 14) := by
    rw [show 3 * d - 9 = 5 + (3 * d - 14) by omega, pow_add]
    norm_num
  have hmass : G + d2FlowCandidateQuota d 13 5 .botDesc ≤
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
    rw [hquota]
    rw [hpG] at hGsmall
    rw [hpRoot] at hroot
    nlinarith
  have hmassTotal : G + d2FlowCandidateQuota d 13 5 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) :=
    le_trans hmass hrootTotal
  omega

/-- Complete local recursive gate for a Stage-13 level-five
bottom-descending sender. -/
theorem d2FlowCandidateStage13_levelFive_botDesc_inputs
    (d : Nat) (hd : 13 ≤ d) (G low high : Nat)
    (hbalance : low + high = G)
    (hG : 512 * G ≤ d2FlowCandidateCapacity d 5 13)
    {r : Nat} (children : Fin 8 → D2FlowTree r)
    (hrecursive : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 13)
      (d2FlowCandidateRole d 13)
      (d2FlowCandidateQuota d 13)
      (fun k => d2FlowCandidateCapacity d k 13) 6 (children j))
    (hleft : d2FlowCandidateCapacity d 5 13 ≤
      128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hright : d2FlowCandidateCapacity d 5 13 ≤
      128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩))
    (htotal : d2FlowCandidateQuota d 13 5 .botDesc ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 13)
      (d2FlowCandidateRole d 13)
      (d2FlowCandidateQuota d 13)
      (fun k => d2FlowCandidateCapacity d k 13) 5
      (.node G low high children) := by
  rcases d2FlowCandidateStage13_frontiers d hd with
    ⟨_, _, _, _, hactive, hrole, _⟩
  have hcap : d2FlowCandidateCapacity d 5 13 = 2 ^ (3 * d - 2) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 13 5 .botDesc =
      15 * 2 ^ (3 * d - 14) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hquotaEven : d2FlowCandidateQuota d 13 5 .botDesc % 2 = 0 := by
    rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 14 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 13 5 .botDesc ≤
      d2FlowCandidateCapacity d 5 13 := by
    rw [hquota, hcap]
    have hp : 256 * 15 * 2 ^ (3 * d - 14) =
        3840 * 2 ^ (3 * d - 14) := by norm_num
    have hpCap : 2 ^ (3 * d - 2) = 4096 * 2 ^ (3 * d - 14) := by
      rw [show 3 * d - 2 = 12 + (3 * d - 14) by omega, pow_add]
      norm_num
    nlinarith [hp, hpCap]
  simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
  exact ⟨hrecursive,
    ⟨hbalance, hG, hquotaCap, htotal, hquotaEven, hleft, hright⟩⟩

/-- Past the Stage-13 active band, every recursive input obligation is
vacuous. -/
theorem d2FlowCandidateAny_stage13_inactive_inputs
    {d h i : Nat} (hd : 13 ≤ d) (hi : 6 ≤ i)
    (tree : D2FlowTree h) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 13)
      (d2FlowCandidateRole d 13)
      (d2FlowCandidateQuota d 13)
      (fun k => d2FlowCandidateCapacity d k 13) i tree := by
  induction tree generalizing i with
  | leaf G low high => trivial
  | node G low high children ih =>
      simp only [d2FlowStageInvInputs]
      constructor
      · intro j
        exact ih j (i := i + 1) (by omega)
      · have hfalse : d2FlowCandidateActive d 13 i = false := by
          have hnot : ¬ (2 ≤ 13 ∧ 13 ≤ tfD2 d ∧ i % 2 = 13 % 2 ∧
              3 * i + 3 * d ≥ 2 * 13 + 11 ∧ 3 * i < 13 + 8) := by omega
          simp [d2FlowCandidateActive, hnot]
          omega
        simp [hfalse]

set_option maxHeartbeats 10000000
/-- Actual endpoint reserves for Stage 13 level-five senders. Stage 11's
bottom-descending cut leaves at least half its quota at each endpoint; the
intervening Stage 12 level-five node is inactive, and its level-six update
cannot decrease either deficit. -/
theorem d2FlowCandidateStage13_actual_levelSix_endpoint_reserves
    (depth : Nat) (hd : 7 ≤ depth) :
    ∀ j k m l q,
      d2FlowCandidateCapacity (depth + 6) 5 13 ≤
        128 * d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowCandidateRun (depth + 6)
                        (d2FlowTreeInitial 8192 (depth + 6)) 13) j) k) m) l) q)
            ⟨0, by omega⟩) ∧
      d2FlowCandidateCapacity (depth + 6) 5 13 ≤
        128 * d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowCandidateRun (depth + 6)
                        (d2FlowTreeInitial 8192 (depth + 6)) 13) j) k) m) l) q)
            ⟨7, by omega⟩) := by
  intro j k m l q
  let d := depth + 6
  let initial := d2FlowTreeInitial 8192 d
  let run11 := d2FlowCandidateRun d initial 11
  let run12 := d2FlowCandidateRun d initial 12
  let run13 := d2FlowCandidateRun d initial 13
  let source5 := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild run11 j) k) m) l) q
  have hgate := d2FlowCandidateStage11_actual_levelFive_inputs
    depth (by omega) j k m l q
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 11)
    (d2FlowCandidateRole d 11)
    (d2FlowCandidateQuota d 11)
    (fun r => d2FlowCandidateCapacity d r 11) 5 source5 at hgate
  have hfront11 := d2FlowCandidateStage11_frontiers d (by omega)
  rcases hfront11 with ⟨_, _, _, _, hactive5, hrole5, _⟩
  cases hnode : source5 with
  | node G5 low5 high5 children5 =>
      rw [hnode] at hgate
      simp only [d2FlowStageInvInputs, hactive5, if_true] at hgate
      rcases hgate with ⟨_, hlocal⟩
      rw [hrole5] at hlocal
      rcases hlocal with ⟨hbalance, hrest⟩
      rcases hrest with ⟨hG, hquotaCap, hquotaAlloc, heven, hleft, hright⟩
      let sizes : Fin 8 → Nat := fun s =>
        d2FlowTreeRootDeficit (children5 s)
      let total := d2FlowTotal sizes
      let allocation := total - G5
      have hquotaAlloc' : d2FlowCandidateQuota d 11 5 .botDesc ≤ total - G5 := by
        simpa [total, sizes] using hquotaAlloc
      have hconserve : allocation + G5 = total := by
        dsimp [allocation, total]
        have hnonzero : 0 < d2FlowCandidateQuota d 11 5 .botDesc := by
          simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
        omega
      have hevenEq : d2FlowCandidateQuota d 11 5 .botDesc =
          2 * (d2FlowCandidateQuota d 11 5 .botDesc / 2) := by omega
      have hGweak : 4096 * G5 ≤
          23 * d2FlowCandidateCapacity d 5 11 := by
        nlinarith [hG, show 0 ≤ d2FlowCandidateCapacity d 5 11 by positivity]
      have hlow : low5 ≤ G5 := by omega
      have hhigh : high5 ≤ G5 := by omega
      have hprofile := d2FlowStage_regular_child_profile_tolerant
        (active := d2FlowCandidateActive d 11)
        (role := d2FlowCandidateRole d 11)
        (quota := d2FlowCandidateQuota d 11)
        (children := children5)
        (h := depth) (i := 5) (G := G5) (low := low5) (high := high5)
        (a := allocation) (c := d2FlowCandidateCapacity d 5 11)
        hactive5 (Or.inr (Or.inr hrole5)) hbalance hconserve
        (by simpa [hrole5, allocation, total, sizes] using hquotaAlloc)
        (by simpa [hrole5] using hevenEq) hGweak hlow hhigh
        (by simpa [hrole5] using hquotaCap) hleft hright
      rw [hrole5] at hprofile
      have hprofile0Fin :
          d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive d 11)
                (d2FlowCandidateRole d 11) (d2FlowCandidateQuota d 11)
                (depth + 1) 5 (.node G5 low5 high5 children5))
              ⟨0, by omega⟩) =
            low5 + d2FlowCandidateQuota d 11 5 .botDesc / 2 := by
        simpa using hprofile.1
      have hprofile7Fin :
          d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive d 11)
                (d2FlowCandidateRole d 11) (d2FlowCandidateQuota d 11)
                (depth + 1) 5 (.node G5 low5 high5 children5))
              ⟨7, by omega⟩) =
            high5 + d2FlowCandidateQuota d 11 5 .botDesc / 2 := by
        simpa using hprofile.2.1
      have hproject11 (s : Fin 8) :
          d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowTreeChild run12 j) k) m) l) q) s) =
          d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive d 11)
                (d2FlowCandidateRole d 11) (d2FlowCandidateQuota d 11)
                (depth + 1) 5 source5) s) := by
        have hp := d2FlowStage_path6_projection
          (active := d2FlowCandidateActive d 11)
          (role := d2FlowCandidateRole d 11)
          (quota := d2FlowCandidateQuota d 11)
          (h := depth) (i := 0) run11 j k m l q s
        simpa [run11, run12, d, initial, source5,
          d2FlowCandidateRun, d2FlowCandidateStage] using hp
      have hquotaReserve :=
        d2FlowCandidateStage13_levelFive_halfQuota_covers_capacity
          d (by omega)
      have hsource0 : d2FlowCandidateCapacity d 5 13 ≤
          128 * d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowTreeChild run12 j) k) m) l) q)
              ⟨0, by omega⟩) := by
        rw [hproject11 ⟨0, by omega⟩, hnode, hprofile0Fin]
        nlinarith [hquotaReserve]
      have hsource7 : d2FlowCandidateCapacity d 5 13 ≤
          128 * d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowTreeChild run12 j) k) m) l) q)
              ⟨7, by omega⟩) := by
        rw [hproject11 ⟨7, by omega⟩, hnode, hprofile7Fin]
        nlinarith [hquotaReserve]
      have htransport (s : Fin 8) :
          d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowTreeChild run12 j) k) m) l) q) s) ≤
          d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowTreeChild run13 j) k) m) l) q) s) := by
        let parent12 := d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run12 j) k) m) l) q
        have hinactive5 : d2FlowCandidateActive d 12 5 = false := by
          simp [d2FlowCandidateActive, tfD2]
        have hp := d2FlowStage_path6_projection
          (active := d2FlowCandidateActive d 12)
          (role := d2FlowCandidateRole d 12)
          (quota := d2FlowCandidateQuota d 12)
          (h := depth) (i := 0) run12 j k m l q s
        have hproject12 :
            d2FlowTreeRootDeficit
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowTreeChild
                        (d2FlowTreeChild run13 j) k) m) l) q) s) =
            d2FlowTreeRootDeficit
              (d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive d 12)
                  (d2FlowCandidateRole d 12) (d2FlowCandidateQuota d 12)
                  (depth + 1) 5 parent12) s) := by
          simpa [parent12, run12, run13, d, initial,
            d2FlowCandidateRun, d2FlowCandidateStage] using hp
        cases hparent12 : parent12 with
        | node G low high children12 =>
            have hchild := d2FlowStage_inactive_child
              (active := d2FlowCandidateActive d 12)
              (role := d2FlowCandidateRole d 12)
              (quota := d2FlowCandidateQuota d 12)
              (h := depth) (i := 5) (G := G) (low := low)
              (high := high) children12 hinactive5 s
            have hmono := d2FlowStage_root_deficit_mono
              (d2FlowCandidateActive d 12)
              (d2FlowCandidateRole d 12)
              (d2FlowCandidateQuota d 12) (h := depth) 6 (children12 s)
            change d2FlowTreeRootDeficit
                (d2FlowTreeChild parent12 s) ≤
              d2FlowTreeRootDeficit
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowTreeChild
                        (d2FlowTreeChild
                          (d2FlowTreeChild run13 j) k) m) l) q) s)
            rw [hparent12]
            change d2FlowTreeRootDeficit (children12 s) ≤ _
            rw [hproject12, hparent12, hchild]
            exact hmono
      constructor
      · exact le_trans hsource0 (Nat.mul_le_mul_left 128 (htransport ⟨0, by omega⟩))
      · exact le_trans hsource7 (Nat.mul_le_mul_left 128 (htransport ⟨7, by omega⟩))



set_option maxHeartbeats 10000000 in
/-- The actual Stage-13 level-five senders inherit their normalized cap and
balance from the Stage-12 level-four mid cut, while the two endpoint reserves
are transported through the inactive level-five projection. -/
theorem d2FlowCandidateStage13_actual_levelFive_inputs
    (depth : Nat) (hd : 7 ≤ depth) :
    ∀ j k m l q, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (depth + 6) 13)
      (d2FlowCandidateRole (depth + 6) 13)
      (d2FlowCandidateQuota (depth + 6) 13)
      (fun r => d2FlowCandidateCapacity (depth + 6) r 13) 5
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (depth + 6)
                  (d2FlowTreeInitial 8192 (depth + 6)) 13) j) k) m) l) q) := by
  intro j k m l q
  let d := depth + 6
  let run12 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 12
  let run13 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 13
  let sourceThree := d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild run12 j) k) m
  let sourceFour := d2FlowTreeChild sourceThree l
  let outputFour := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild run13 j) k) m) l
  let outputFive := d2FlowTreeChild outputFour q
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 13) (d2FlowCandidateRole d 13)
    (d2FlowCandidateQuota d 13)
    (fun r => d2FlowCandidateCapacity d r 13) 5 outputFive
  have hparentInputs := d2FlowCandidateStage12_actual_levelFour_inputs
    depth hd j k m l
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 12) (d2FlowCandidateRole d 12)
    (d2FlowCandidateQuota d 12)
    (fun r => d2FlowCandidateCapacity d r 12) 4 sourceFour
    at hparentInputs
  have hinvRoot := d2FlowCandidateStage11_preserves_inv depth (by omega)
  let hlevelTwo := d2FlowTreeChild (d2FlowTreeChild run12 j) k
  have hinvTwo := d2FlowTreeInv_grandchild
    (h := depth + 4) run12 hinvRoot j k
  have hinvFour := d2FlowTreeInv_grandchild
    (h := depth + 2) hlevelTwo
      (by simpa [hlevelTwo] using hinvTwo) m l
  have hinvParent : d2FlowTreeInv 8192 sourceFour := by
    simpa [hlevelTwo, sourceFour] using hinvFour
  have hprojection := d2FlowStage_path4_projection
    (active := d2FlowCandidateActive d 12)
    (role := d2FlowCandidateRole d 12)
    (quota := d2FlowCandidateQuota d 12)
    (h := depth + 2) (i := 0) run12 j k m l
  have hprojection' : outputFour =
      d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 12)
          (d2FlowCandidateRole d 12) (d2FlowCandidateQuota d 12)
          (depth + 3) 3 sourceThree) l := by
    simpa [outputFour, run12, run13, d, d2FlowCandidateRun,
      d2FlowCandidateStage, sourceThree] using hprojection
  have hinactive3 : d2FlowCandidateActive d 12 3 = false := by
    simp [d2FlowCandidateActive, tfD2]
  cases hthree : sourceThree with
  | node G3 low3 high3 children3 =>
      have hsourceFour : sourceFour = children3 l := by
        dsimp [sourceFour]
        rw [hthree]
        rfl
      have hchildProjection :
          d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 12)
              (d2FlowCandidateRole d 12) (d2FlowCandidateQuota d 12)
              (depth + 3) 3 (.node G3 low3 high3 children3)) l =
          d2FlowStage (d2FlowCandidateActive d 12)
            (d2FlowCandidateRole d 12) (d2FlowCandidateQuota d 12)
            (depth + 2) 4 sourceFour := by
        rw [hsourceFour]
        exact d2FlowStage_inactive_child
          (active := d2FlowCandidateActive d 12)
          (role := d2FlowCandidateRole d 12)
          (quota := d2FlowCandidateQuota d 12)
          (h := depth + 2) (i := 3) (G := G3)
          (low := low3) (high := high3) children3 hinactive3 l
      have hprojectionNode := hprojection'
      rw [hthree] at hprojectionNode
      have houtputFour : outputFour =
          d2FlowStage (d2FlowCandidateActive d 12)
            (d2FlowCandidateRole d 12) (d2FlowCandidateQuota d 12)
            (depth + 2) 4 sourceFour :=
        hprojectionNode.trans hchildProjection
      cases hsource : sourceFour with
      | node G4 low4 high4 children4 =>
          have hparentInputs' := hparentInputs
          rw [hsource] at hparentInputs'
          have hinvParent' := hinvParent
          rw [hsource] at hinvParent'
          rcases d2FlowCandidateStage12_frontiers d (by omega) with
            ⟨_, _, _, _, hactive4, hrole4, _, _, _⟩
          have hchildCap := d2FlowStage_regular_child_g_bound_of_tree_inputs
            (stageDepth := depth + 1)
            (.node G4 low4 high4 children4) hactive4
            (Or.inr (Or.inl hrole4)) hinvParent' hparentInputs'
          have hchildBalanced := d2FlowStage_regular_child_balanced
            (active := d2FlowCandidateActive d 12)
            (role := d2FlowCandidateRole d 12)
            (quota := d2FlowCandidateQuota d 12)
            (h := depth + 1) (i := 4) (G := G4)
            (low := low4) (high := high4) children4 hactive4
            (Or.inr (Or.inl hrole4)) q
          have houtputFive : outputFive =
              d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive d 12)
                  (d2FlowCandidateRole d 12) (d2FlowCandidateQuota d 12)
                  (depth + 2) 4 (.node G4 low4 high4 children4)) q := by
            change d2FlowTreeChild outputFour q =
              d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive d 12)
                  (d2FlowCandidateRole d 12) (d2FlowCandidateQuota d 12)
                  (depth + 2) 4 (.node G4 low4 high4 children4)) q
            rw [houtputFour, hsource]
          have hcapRelation :
              d2FlowCandidateCapacity d 5 13 =
                2 * d2FlowCandidateCapacity d 4 12 := by
            exact d2FlowCandidateCapacity_succ_level_next_stage d 4 12
              (by simp [d2FlowCandidateCapacityExponent]; omega)
          cases hnode : outputFive with
          | node G5 low5 high5 children5 =>
              have hG : 512 * G5 ≤
                  d2FlowCandidateCapacity d 5 13 := by
                have hg := hchildCap q
                rw [← houtputFive, ← hcapRelation] at hg
                rw [hnode] at hg
                simpa [d2FlowTreeRootDeficit] using hg
              have hbalance : low5 + high5 = G5 := by
                have hb := hchildBalanced
                rw [← houtputFive, hnode] at hb
                simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hb
              have hendpoint :=
                d2FlowCandidateStage13_actual_levelSix_endpoint_reserves
                  depth hd j k m l q
              have hleft : d2FlowCandidateCapacity d 5 13 ≤
                  128 * d2FlowTreeRootDeficit (children5 ⟨0, by omega⟩) := by
                have hl := hendpoint.1
                change d2FlowCandidateCapacity d 5 13 ≤
                  128 * d2FlowTreeRootDeficit
                    (d2FlowTreeChild outputFive ⟨0, by omega⟩) at hl
                rw [hnode] at hl
                simpa only [d2FlowTreeChild] using hl
              have hright : d2FlowCandidateCapacity d 5 13 ≤
                  128 * d2FlowTreeRootDeficit (children5 ⟨7, by omega⟩) := by
                have hr := hendpoint.2
                change d2FlowCandidateCapacity d 5 13 ≤
                  128 * d2FlowTreeRootDeficit
                    (d2FlowTreeChild outputFive ⟨7, by omega⟩) at hr
                rw [hnode] at hr
                simpa only [d2FlowTreeChild] using hr
              have hrecursive : ∀ s, d2FlowStageInvInputs 8192
                  (d2FlowCandidateActive d 13)
                  (d2FlowCandidateRole d 13)
                  (d2FlowCandidateQuota d 13)
                  (fun r => d2FlowCandidateCapacity d r 13) 6
                  (children5 s) := by
                intro s
                exact d2FlowCandidateAny_stage13_inactive_inputs
                  (by omega) (by omega) (children5 s)
              have htotal :=
                d2FlowCandidateStage13_levelFive_boundary_mass_suffices
                  d (by omega) G5 hG children5 hleft
              simpa [hnode] using
                (d2FlowCandidateStage13_levelFive_botDesc_inputs
                  d (by omega) G5 low5 high5 hbalance hG children5
                  hrecursive hleft hright htotal)


set_option maxHeartbeats 10000000 in
/-- Stage 13 is inactive at level four, so its actual level-four contracts
are exactly the actual level-five contracts below each child. -/
theorem d2FlowCandidateStage13_actual_levelFour_inputs
    (depth : Nat) (hd : 7 ≤ depth) :
    ∀ j k m l, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (depth + 6) 13)
      (d2FlowCandidateRole (depth + 6) 13)
      (d2FlowCandidateQuota (depth + 6) 13)
      (fun r => d2FlowCandidateCapacity (depth + 6) r 13) 4
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateRun (depth + 6)
                (d2FlowTreeInitial 8192 (depth + 6)) 13) j) k) m) l) := by
  intro j k m l
  let d := depth + 6
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 13) j) k) m) l
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 13) (d2FlowCandidateRole d 13)
    (d2FlowCandidateQuota d 13)
    (fun r => d2FlowCandidateCapacity d r 13) 4 tree
  have hinactive4 : d2FlowCandidateActive d 13 4 = false := by
    simp [d2FlowCandidateActive, tfD2]
  cases htree : tree with
  | node G low high children =>
      simp only [d2FlowStageInvInputs, hinactive4, if_false]
      constructor
      · intro q
        have hq := d2FlowCandidateStage13_actual_levelFive_inputs
          depth hd j k m l q
        change d2FlowStageInvInputs 8192
          (d2FlowCandidateActive d 13) (d2FlowCandidateRole d 13)
          (d2FlowCandidateQuota d 13)
          (fun r => d2FlowCandidateCapacity d r 13) 5
          (d2FlowTreeChild tree q) at hq
        rw [htree] at hq
        simpa only [d2FlowTreeChild] using hq
      · trivial

set_option maxHeartbeats 10000000 in
/-- The actual Stage-13 level-three mid gates follow from the Stage-12
level-two cut, the endpoint reserves, and the actual level-five inputs. -/
theorem d2FlowCandidateStage13_actual_levelThree_inputs
    (depth : Nat) (hd : 7 ≤ depth) :
    ∀ j k m, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (depth + 6) 13)
      (d2FlowCandidateRole (depth + 6) 13)
      (d2FlowCandidateQuota (depth + 6) 13)
      (fun r => d2FlowCandidateCapacity (depth + 6) r 13) 3
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (depth + 6)
              (d2FlowTreeInitial 8192 (depth + 6)) 13) j) k) m) := by
  intro j k m
  let d := depth + 6
  let run12 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 12
  let run13 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 13
  let sourceTwo := d2FlowTreeChild (d2FlowTreeChild run12 j) k
  let outputThree := d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild run13 j) k) m
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 13) (d2FlowCandidateRole d 13)
    (d2FlowCandidateQuota d 13)
    (fun r => d2FlowCandidateCapacity d r 13) 3 outputThree
  have hparentInputs := d2FlowCandidateStage12_actual_levelTwo_inputs
    depth hd j k
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 12) (d2FlowCandidateRole d 12)
    (d2FlowCandidateQuota d 12)
    (fun r => d2FlowCandidateCapacity d r 12) 2 sourceTwo
    at hparentInputs
  have hinvRoot := d2FlowCandidateStage11_preserves_inv depth (by omega)
  have hinvParent := d2FlowTreeInv_grandchild
    (h := depth + 4) run12 hinvRoot j k
  have hprojection := d2FlowStage_path3_projection
    (active := d2FlowCandidateActive d 12)
    (role := d2FlowCandidateRole d 12)
    (quota := d2FlowCandidateQuota d 12)
    (h := depth + 3) (i := 0) run12 j k m
  have hprojection' : outputThree =
      d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 12)
          (d2FlowCandidateRole d 12) (d2FlowCandidateQuota d 12)
          (depth + 4) 2 sourceTwo) m := by
    simpa [outputThree, run12, run13, d,
      d2FlowCandidateRun, d2FlowCandidateStage, sourceTwo] using hprojection
  cases hsource : sourceTwo with
  | node G2 low2 high2 children2 =>
      have hparentInputs' := hparentInputs
      rw [hsource] at hparentInputs'
      have hinvParent' : d2FlowTreeInv 8192
          (.node G2 low2 high2 children2) := by
        rw [← hsource]
        exact hinvParent
      rcases d2FlowCandidateStage12_frontiers d (by omega) with
        ⟨_, _, hactive2, hrole2, _, _, _, _, _⟩
      have hchildCap := d2FlowStage_regular_child_g_bound_of_tree_inputs
        (stageDepth := depth + 3)
        (.node G2 low2 high2 children2) hactive2
        (Or.inr (Or.inl hrole2)) hinvParent' hparentInputs'
      have hchildBalanced := d2FlowStage_regular_child_balanced
        (active := d2FlowCandidateActive d 12)
        (role := d2FlowCandidateRole d 12)
        (quota := d2FlowCandidateQuota d 12)
        (h := depth + 3) (i := 2) (G := G2)
        (low := low2) (high := high2) children2 hactive2
        (Or.inr (Or.inl hrole2)) m
      have houtputThree : outputThree =
          d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 12)
              (d2FlowCandidateRole d 12) (d2FlowCandidateQuota d 12)
              (depth + 4) 2 (.node G2 low2 high2 children2)) m := by
        rw [hsource] at hprojection'
        exact hprojection'
      have hcapRelation : d2FlowCandidateCapacity d 3 13 =
          2 * d2FlowCandidateCapacity d 2 12 := by
        exact d2FlowCandidateCapacity_succ_level_next_stage d 2 12
          (by simp [d2FlowCandidateCapacityExponent]; omega)
      cases hnode : outputThree with
      | node G3 low3 high3 children3 =>
          have hG : 512 * G3 ≤ d2FlowCandidateCapacity d 3 13 := by
            have hg := hchildCap m
            rw [← houtputThree, ← hcapRelation] at hg
            rw [hnode] at hg
            simpa [d2FlowTreeRootDeficit] using hg
          have hbalance : low3 + high3 = G3 := by
            have hb := hchildBalanced
            rw [← houtputThree, hnode] at hb
            simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hb
          have hleft : d2FlowCandidateCapacity d 3 13 ≤
              128 * d2FlowTreeRootDeficit (children3 ⟨0, by omega⟩) := by
            have hl := d2FlowCandidateStage13_levelThree_endpoint_reserve
              depth hd j k m ⟨0, by omega⟩
            change d2FlowCandidateCapacity d 3 13 ≤
              128 * d2FlowTreeRootDeficit
                (d2FlowTreeChild outputThree ⟨0, by omega⟩) at hl
            rw [hnode] at hl
            simpa only [d2FlowTreeChild] using hl
          have hright : d2FlowCandidateCapacity d 3 13 ≤
              128 * d2FlowTreeRootDeficit (children3 ⟨7, by omega⟩) := by
            have hr := d2FlowCandidateStage13_levelThree_endpoint_reserve
              depth hd j k m ⟨7, by omega⟩
            change d2FlowCandidateCapacity d 3 13 ≤
              128 * d2FlowTreeRootDeficit
                (d2FlowTreeChild outputThree ⟨7, by omega⟩) at hr
            rw [hnode] at hr
            simpa only [d2FlowTreeChild] using hr
          have hrecursive : ∀ s, d2FlowStageInvInputs 8192
              (d2FlowCandidateActive d 13)
              (d2FlowCandidateRole d 13)
              (d2FlowCandidateQuota d 13)
              (fun r => d2FlowCandidateCapacity d r 13) 4
              (children3 s) := by
            intro s
            have hs := d2FlowCandidateStage13_actual_levelFour_inputs
              depth hd j k m s
            change d2FlowStageInvInputs 8192
              (d2FlowCandidateActive d 13)
              (d2FlowCandidateRole d 13)
              (d2FlowCandidateQuota d 13)
              (fun r => d2FlowCandidateCapacity d r 13) 4
              (d2FlowTreeChild outputThree s) at hs
            rw [hnode] at hs
            simpa only [d2FlowTreeChild] using hs
          have htotal :=
            d2FlowCandidateStage13_levelThree_boundary_mass_suffices
              d (by omega) G3 hG children3 hleft
          simpa [hnode] using
            (d2FlowCandidateStage13_mid_inputs d (by omega)
              G3 low3 high3 hbalance hG children3 hrecursive
              hleft hright htotal)

set_option maxHeartbeats 10000000 in
/-- Stage 12's inactive level one exposes its level-two updates unchanged
under the Stage 13 tree. -/
theorem d2FlowCandidateStage12_levelTwo_projection
    (h : Nat) (hh : 12 ≤ h) :
    ∀ j k, d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun (h + 2)
            (d2FlowTreeInitial 8192 (h + 2)) 13) j) k =
      d2FlowStage (d2FlowCandidateActive (h + 2) 12)
        (d2FlowCandidateRole (h + 2) 12)
        (d2FlowCandidateQuota (h + 2) 12) h 2
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (h + 2)
              (d2FlowTreeInitial 8192 (h + 2)) 12) j) k) := by
  have hinactive1 : d2FlowCandidateActive (h + 2) 12 1 = false := by
    simp [d2FlowCandidateActive, tfD2]
  intro j k
  change d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowCandidateStage (h + 2) 12
          (d2FlowCandidateRun (h + 2)
            (d2FlowTreeInitial 8192 (h + 2)) 12)) j) k =
    d2FlowStage (d2FlowCandidateActive (h + 2) 12)
      (d2FlowCandidateRole (h + 2) 12)
      (d2FlowCandidateQuota (h + 2) 12) h 2
      (d2FlowTreeChild (d2FlowTreeChild
        (d2FlowCandidateRun (h + 2)
          (d2FlowTreeInitial 8192 (h + 2)) 12) j) k)
  cases htree : d2FlowCandidateRun (h + 2)
      (d2FlowTreeInitial 8192 (h + 2)) 12 with
  | node G low high children =>
      have hprojection := d2FlowStage_child_child_of_inactive
        (active := d2FlowCandidateActive (h + 2) 12)
        (role := d2FlowCandidateRole (h + 2) 12)
        (quota := d2FlowCandidateQuota (h + 2) 12)
        (h := h) (i := 0) (G := G) (low := low) (high := high)
        children hinactive1 j k
      change d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateStage (h + 2) 12
              (.node G low high children)) j) k = _
      simpa [d2FlowCandidateStage] using hprojection

/-- The Stage-13 level-one top-rise gate follows from the quota created at
each level-two mid sender in Stage 12. -/
theorem d2FlowCandidateStage13_topRise_inputs
    (d : Nat) (hd : 13 ≤ d) (low high : Nat)
    (hbalance : low + high = 0)
    (children : Fin 8 → D2FlowTree (d - 2))
    (hchildren : ∀ j,
      d2FlowCandidateQuota d 12 2 .mid ≤
        d2FlowTreeRootDeficit (children j))
    (hrec : ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 13)
      (d2FlowCandidateRole d 13)
      (d2FlowCandidateQuota d 13)
      (fun k => d2FlowCandidateCapacity d k 13) 2 (children j)) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 13)
      (d2FlowCandidateRole d 13)
      (d2FlowCandidateQuota d 13)
      (fun k => d2FlowCandidateCapacity d k 13) 1
      (.node 0 low high children) := by
  rcases d2FlowCandidateStage13_frontiers d hd with
    ⟨hactive, hrole, _, _, _, _, _⟩
  have hcap : d2FlowCandidateCapacity d 1 13 = 2 ^ (3 * d - 14) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 13 1 .topRise =
      2 ^ (3 * d - 22) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hmid : d2FlowCandidateQuota d 12 2 .mid =
      15 * 2 ^ (3 * d - 21) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hquotaEven : d2FlowCandidateQuota d 13 1 .topRise % 2 = 0 := by
    rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 22 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 13 1 .topRise ≤
      d2FlowCandidateCapacity d 1 13 := by
    rw [hquota, hcap]
    have hp : 256 * 2 ^ (3 * d - 22) = 2 ^ (3 * d - 14) := by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_add]
      congr 1 <;> omega
    exact le_of_eq hp
  have hreserve : ∀ j, d2FlowCandidateCapacity d 1 13 ≤
      128 * d2FlowTreeRootDeficit (children j) := by
    intro j
    have hbase : d2FlowCandidateCapacity d 1 13 =
        128 * 2 ^ (3 * d - 21) := by
      rw [hcap]
      have hp : 2 ^ (3 * d - 14) = 128 * 2 ^ (3 * d - 21) := by
        rw [show 3 * d - 14 = 7 + (3 * d - 21) by omega, pow_add]
        norm_num
      exact hp
    have hchild : 2 ^ (3 * d - 21) ≤
        d2FlowTreeRootDeficit (children j) := by
      have hj := hchildren j
      rw [hmid] at hj
      omega
    rw [hbase]
    exact Nat.mul_le_mul_left 128 hchild
  have htotal : 8 * d2FlowCandidateQuota d 12 2 .mid ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    unfold d2FlowTotal
    calc
      8 * d2FlowCandidateQuota d 12 2 .mid =
          ∑ j : Fin 8, d2FlowCandidateQuota d 12 2 .mid := by simp
      _ ≤ ∑ j : Fin 8, d2FlowTreeRootDeficit (children j) :=
        Finset.sum_le_sum fun j _ => hchildren j
  have halloc : d2FlowCandidateQuota d 13 1 .topRise ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    have hsmall : d2FlowCandidateQuota d 13 1 .topRise ≤
        8 * d2FlowCandidateQuota d 12 2 .mid := by
      rw [hquota, hmid]
      have he : 2 ^ (3 * d - 21) = 2 * 2 ^ (3 * d - 22) := by
        rw [show 3 * d - 21 = 1 + (3 * d - 22) by omega, pow_add]
        norm_num
      rw [he]
      omega
    exact le_trans hsmall htotal
  simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
  refine ⟨hrec, ⟨hbalance, ?_, hquotaCap, halloc, hquotaEven, ?_, ?_⟩⟩
  · simp
  · exact hreserve ⟨0, by omega⟩
  · exact hreserve ⟨7, by omega⟩

set_option maxHeartbeats 10000000 in
/-- Actual Stage-13 level-one inputs are inherited from Stage 12's root reset,
its level-two mid quotas, and the checked Stage-13 level-three gates. -/
theorem d2FlowCandidateStage13_actual_levelOne_inputs
    (depth : Nat) (hd : 8 ≤ depth) :
    ∀ j, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (depth + 6) 13)
      (d2FlowCandidateRole (depth + 6) 13)
      (d2FlowCandidateQuota (depth + 6) 13)
      (fun q => d2FlowCandidateCapacity (depth + 6) q 13) 1
      (d2FlowTreeChild
        (d2FlowCandidateRun (depth + 6)
          (d2FlowTreeInitial 8192 (depth + 6)) 13) j) := by
  let d := depth + 6
  change ∀ j, d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 13) (d2FlowCandidateRole d 13)
    (d2FlowCandidateQuota d 13)
    (fun q => d2FlowCandidateCapacity d q 13) 1
    (d2FlowTreeChild (d2FlowCandidateRun d
      (d2FlowTreeInitial 8192 d) 13) j)
  have hfront12 := d2FlowCandidateStage12_frontiers d (by omega)
  rcases hfront12 with ⟨hactive0, hrole0, hactive2, hrole2, _, _, _, _, _⟩
  have hfront13 := d2FlowCandidateStage13_frontiers d (by omega)
  rcases hfront13 with ⟨_, _, hactive3, hrole3, _, _, _⟩
  have hlevelThree := d2FlowCandidateStage13_actual_levelThree_inputs depth (by omega)
  have hprojection := d2FlowCandidateStage12_levelTwo_projection
    (depth + 4) (by omega)
  have hrootZero := d2FlowCandidateStage12_root_zero depth (by omega)
  have hinactive2 : d2FlowCandidateActive d 13 2 = false := by
    simp [d2FlowCandidateActive, tfD2]
  intro j
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 12
  let after := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 13
  change D2FlowTree (depth + 6) at before
  change D2FlowTree (depth + 6) at after
  have hdata : d2FlowTreeRootData (d2FlowTreeChild after j) = (0, 0, 0) := by
    change d2FlowTreeRootData
      (d2FlowTreeChild (d2FlowCandidateStage d 12 before) j) = (0, 0, 0)
    cases hroot : before with
    | node G low high children =>
        have hG : G = 0 := by
          have hz := hrootZero
          have hz' : d2FlowTreeRootDeficit before = 0 := by
            simpa [before, d, Nat.add_assoc] using hz
          rw [hroot] at hz'
          exact hz'
        simpa [d2FlowCandidateStage, d2FlowTreeInitial, hroot, hG,
          hactive0, hrole0] using
          (d2FlowStage_topDesc_child_rootdata
            (active := d2FlowCandidateActive d 12)
            (role := d2FlowCandidateRole d 12)
            (quota := d2FlowCandidateQuota d 12)
            (h := d - 1) (i := 0) (G := G) (low := low)
            (high := high) children hactive0 hrole0 j)
  cases hchild : d2FlowTreeChild after j with
  | node G1 low1 high1 children1 =>
      have hdata' := hdata
      rw [hchild] at hdata'
      simp only [d2FlowTreeRootData] at hdata'
      have hG1 : G1 = 0 := congrArg Prod.fst hdata'
      have hlow1 : low1 = 0 := congrArg (fun p : Nat × Nat × Nat => p.2.1) hdata'
      have hhigh1 : high1 = 0 := congrArg (fun p : Nat × Nat × Nat => p.2.2) hdata'
      have hbalance : low1 + high1 = 0 := by omega
      have hd2 : d - 2 = depth + 4 := by dsimp [d]; omega
      have hchildren : ∀ k : Fin 8,
          d2FlowCandidateQuota d 12 2 .mid ≤
            d2FlowTreeRootDeficit (children1 k) := by
        intro k
        cases hbefore : before with
        | node G0 low0 high0 children0 =>
         have hafter : after = d2FlowCandidateStage d 12
             (.node G0 low0 high0 children0) := by
           change d2FlowCandidateStage d 12 before = _
           rw [hbefore]
         have hprojNode := d2FlowStage_child_child_of_inactive
           (active := d2FlowCandidateActive d 12)
           (role := d2FlowCandidateRole d 12)
           (quota := d2FlowCandidateQuota d 12)
           (h := depth + 4) (i := 0) (G := G0) (low := low0)
           (high := high0) children0
           (by simp [d2FlowCandidateActive, tfD2]) j k
         have hchildNode : d2FlowTreeChild
             (d2FlowCandidateStage d 12
               (.node G0 low0 high0 children0)) j =
               .node G1 low1 high1 children1 := by
           calc
             _ = d2FlowTreeChild after j := by rw [← hafter]
             _ = .node G1 low1 high1 children1 := hchild
         have hproj' : children1 k = d2FlowStage
             (d2FlowCandidateActive d 12) (d2FlowCandidateRole d 12)
             (d2FlowCandidateQuota d 12) (depth + 4) 2
             (d2FlowTreeChild (children0 j) k) := by
           calc
             children1 k = d2FlowTreeChild (.node G1 low1 high1 children1) k := rfl
             _ = d2FlowTreeChild
                   (d2FlowTreeChild
                     (d2FlowCandidateStage d 12
                       (.node G0 low0 high0 children0)) j) k := by
                   rw [← hchildNode]
             _ = d2FlowStage (d2FlowCandidateActive d 12)
                   (d2FlowCandidateRole d 12) (d2FlowCandidateQuota d 12)
                   (depth + 4) 2
                   (d2FlowTreeChild (children0 j) k) := hprojNode
         cases hsrc : d2FlowTreeChild (children0 j) k with
         | node G2 low2 high2 grandchildren =>
            have hpost : d2FlowTreeRootDeficit
                (d2FlowStage (d2FlowCandidateActive d 12)
                  (d2FlowCandidateRole d 12) (d2FlowCandidateQuota d 12)
                  (depth + 4) 2 (.node G2 low2 high2 grandchildren)) =
                G2 + d2FlowCandidateQuota d 12 2 .mid := by
              simpa [hactive2, hrole2] using
                (d2FlowStage_active_node_deficit
                  (active := d2FlowCandidateActive d 12)
                  (role := d2FlowCandidateRole d 12)
                  (quota := d2FlowCandidateQuota d 12)
                  (h := depth + 3) (i := 2) (G := G2)
                  (low := low2) (high := high2) grandchildren hactive2)
            change d2FlowCandidateQuota d 12 2 .mid ≤
              d2FlowTreeRootDeficit (children1 k)
            rw [hproj', hsrc, hpost]
            omega
      have hrecursive : ∀ k : Fin 8,
          d2FlowStageInvInputs 8192
            (d2FlowCandidateActive d 13) (d2FlowCandidateRole d 13)
            (d2FlowCandidateQuota d 13)
            (fun q => d2FlowCandidateCapacity d q 13) 2 (children1 k) := by
        intro k
        have hrecursive3 : ∀ m : Fin 8,
            d2FlowStageInvInputs 8192
              (d2FlowCandidateActive d 13) (d2FlowCandidateRole d 13)
              (d2FlowCandidateQuota d 13)
              (fun q => d2FlowCandidateCapacity d q 13) 3
              (d2FlowTreeChild (children1 k) m) := by
          intro m
          have hm := hlevelThree j k m
          change d2FlowStageInvInputs 8192
            (d2FlowCandidateActive d 13) (d2FlowCandidateRole d 13)
            (d2FlowCandidateQuota d 13)
            (fun q => d2FlowCandidateCapacity d q 13) 3
            (d2FlowTreeChild (d2FlowTreeChild
              (d2FlowTreeChild after j) k) m) at hm
          rw [hchild] at hm
          simpa only [d2FlowTreeChild] using hm
        cases hchild2 : children1 k with
        | node G2 low2 high2 grandchildren =>
            rw [hchild2] at hrecursive3
            simp only [d2FlowStageInvInputs, hinactive2, if_false]
            exact ⟨hrecursive3, trivial⟩
      have htop := d2FlowCandidateStage13_topRise_inputs d (by omega)
        low1 high1 hbalance children1 hchildren hrecursive
      simpa [hchild, hG1, hlow1, hhigh1] using htop

/-- The complete Stage-13 recursive input predicate is exactly its actual
level-one contract because level zero is inactive. -/
theorem d2FlowCandidateStage13_actual_inputs
    (depth : Nat) (hd : 8 ≤ depth) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (depth + 6) 13)
      (d2FlowCandidateRole (depth + 6) 13)
      (d2FlowCandidateQuota (depth + 6) 13)
      (fun q => d2FlowCandidateCapacity (depth + 6) q 13) 0
      (d2FlowCandidateRun (depth + 6)
        (d2FlowTreeInitial 8192 (depth + 6)) 13) := by
  let d := depth + 6
  let tree := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 13
  have hinactive0 : d2FlowCandidateActive d 13 0 = false := by
    simp [d2FlowCandidateActive, tfD2]
  have hlevelOne := d2FlowCandidateStage13_actual_levelOne_inputs depth hd
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 13)
    (d2FlowCandidateRole d 13)
    (d2FlowCandidateQuota d 13)
    (fun q => d2FlowCandidateCapacity d q 13) 0 tree
  change D2FlowTree (depth + 6) at tree
  cases hroot : tree with
  | node G low high children =>
      simp only [d2FlowStageInvInputs, hinactive0, if_false]
      refine ⟨?_, trivial⟩
      intro j
      have hj := hlevelOne j
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 13)
        (d2FlowCandidateRole d 13)
        (d2FlowCandidateQuota d 13)
        (fun q => d2FlowCandidateCapacity d q 13) 1
        (d2FlowTreeChild tree j) at hj
      rw [hroot] at hj
      simpa only [d2FlowTreeChild] using hj

set_option maxHeartbeats 10000000 in
/-- The Stage-13 local gates preserve the invariant through its actual
finite-run transition. -/
theorem d2FlowCandidateStage13_preserves_inv
    (depth : Nat) (hd : 8 ≤ depth) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (depth + 6)
        (d2FlowTreeInitial 8192 (depth + 6)) 14) := by
  let d := depth + 6
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 13
  have hinv := d2FlowCandidateStage12_preserves_inv depth (by omega)
  have hinputs := d2FlowStageInvInputs_tolerant_of_strict before
    (d2FlowCandidateStage13_actual_inputs depth hd)
  have hpres := d2FlowStage_preserves_inv_of_tolerant_inputs
    (active := d2FlowCandidateActive d 13)
    (role := d2FlowCandidateRole d 13)
    (quota := d2FlowCandidateQuota d 13)
    (cap := fun q => d2FlowCandidateCapacity d q 13)
    (i := 0) before hinv hinputs
  change d2FlowTreeInv 8192
    (d2FlowCandidateStage d 13 before)
  simpa [d, before, d2FlowCandidateRun, d2FlowCandidateStage] using hpres

end Chvatal.D2Reserve
