module
/-
  # Section 7 levelSchedule7 preferNon trajectory scaffolding

  Executable per-stage PreferNonStageChildrenData / AbstractParentResidueRouting
  toward Params7AbstractTrajectoryRoutingObligation. Empty parent send-up
  discharges register cover on rootPlacement; Thm 5.1 budgets discharge
  AbstractParentResidue via AbstractParentResidueRouting.

  Kernel-checked: root stationary stage for every d (empty fromParent);
  Params7AbstractTrajectoryRoutingObligation.stationaryRoot for d >= 7;
  native level-1 root split with nonempty zero-stranger fromParent;
  evolving Params7AbstractTrajectoryRoutingObligation.nativeLevel1 for d >= 7
  (d = 7 has tf = 1, so the split alone completes the schedule);
  ExistsScrambleSeparator -> per-bag LocalSeparatorQuality.ofTheorem51.

  Open: wire-level separator->fromParent from scramble nets (not only native
  / identity sends), deeper ladder capacity on nonempty child bags beyond level 1,
  and real Section 7 separator assembly (not Batcher-only placeholders).
-/

public import AKS.Chvatal.Bound1830
public import AKS.Chvatal.Theorem51
public import AKS.Chvatal.Schedule7
public import AKS.Chvatal.Params
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Chvatal

open Finset

/-! **params7 capacity vs native bag size (exponent comparison)** -/

theorem capacity_le_nativeCard_params7 (d l t : Nat)
    (h : 3 * l + 2 ≤ t) :
    capacity params7 d l t ≤ (64 ^ (d - l) : Rat) := by
  rw [capacity_params7_zpow, ← zpow_natCast]
  exact zpow_le_zpow_right₀ (by norm_num : (1 : Rat) ≤ 64) (by omega)

def ChildRegisterCapacityLower.of_ladderNative_params7 (d : Nat) (hd : 7 ≤ d) (t : Nat)
    (pl : Placement params7.br d)
    (hcard : ∀ (b : KBag params7.br d) (hb : 1 ≤ b.l) (hbd : b.l < d) (j : Fin params7.br),
      0 < (pl.regs (b.child j.val j.isLt hbd)).card →
        (pl.regs (b.child j.val j.isLt hbd)).card = params7.br ^ (d - (b.l + 1)))
    (htime : ∀ (b : KBag params7.br d) (hb : 1 ≤ b.l) (hbd : b.l < d) (j : Fin params7.br),
      0 < (pl.regs (b.child j.val j.isLt hbd)).card → 3 * (b.l + 1) + 2 ≤ t) :
    ChildRegisterCapacityLower params7 d t pl where
  hGe := fun b hb hbd j hpos => by
    have hcard' := hcard b hb hbd j hpos
    rw [hcard']
    exact_mod_cast capacity_le_nativeCard_params7 d (b.l + 1) t (htime b hb hbd j hpos)

/-! **Zero-stranger / empty parent send-up: Thm 5.1 routing** -/

/-- Thm 5.1 routing when parent-send Finsets carry no strangers (empty or all-native). -/
def AbstractParentResidueRouting.of_zeroStrangersFromParent
    (p : ScheduleParams) (ip : InvariantParams) (d t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (step : PlacementStep p d pl pl')
    (hBad0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
      b.strangers 1 perm' (step.fromParent b hb) (br_ge_one p) = 0)
    (hFringe0 : ∀ (b : KBag p.br d) (r : Nat) (_hr1 : 1 ≤ r) (_hrd : r ≤ d)
        (hb : 1 ≤ b.l),
      b.strangers (r + 1) perm' (step.fromParent b hb) (br_ge_one p) = 0)
    (hbudget :
      ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
        (0 : Rat) ≤
          parentOutMass p d pl perm b hb +
            sibMassBound p ip d t b hb +
            ip.epsB * capacity p d (b.l - 1) t + slackBound p d t b hb) :
    AbstractParentResidueRouting p ip d t pl pl' perm perm' step where
  hBadSend0 := fun b hb => by
    have h0 :
        ((b.strangers 1 perm' (step.fromParent b hb) (br_ge_one p) : Rat)) = 0 := by
      exact_mod_cast hBad0 b hb
    simpa [h0] using hbudget b hb
  hFringeSend := fun b r hr1 hrd hb => by
    have h0 :
        ((b.strangers (r + 1) perm' (step.fromParent b hb) (br_ge_one p) : Rat)) = 0 := by
      exact_mod_cast hFringe0 b r hr1 hrd hb
    have hRHS :
        (0 : Rat) ≤
          ip.epsF *
            ((b.parent (br_ge_one p)).strangers r perm
              (pl.regs (b.parent (br_ge_one p))) (br_ge_one p) : Rat) := by
      have := ip.hepsF_nonneg
      positivity
    simpa [h0] using hRHS

def AbstractParentResidueRouting.of_emptyFromParent
    (p : ScheduleParams) (ip : InvariantParams) (d t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (step : PlacementStep p d pl pl')
    (hfrom : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l), step.fromParent b hb = ∅)
    (hbudget :
      ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
        (0 : Rat) ≤
          parentOutMass p d pl perm b hb +
            sibMassBound p ip d t b hb +
            ip.epsB * capacity p d (b.l - 1) t + slackBound p d t b hb) :
    AbstractParentResidueRouting p ip d t pl pl' perm perm' step :=
  AbstractParentResidueRouting.of_zeroStrangersFromParent p ip d t pl pl' perm perm'
    step
    (fun b hb => by rw [hfrom b hb]; exact KBag.strangers_empty b 1 perm' (br_ge_one p))
    (fun b r _hr1 _hrd hb => by
      rw [hfrom b hb]; exact KBag.strangers_empty b (r + 1) perm' (br_ge_one p))
    hbudget

/-! **All stages packaged as an obligation (hypothesis per stage)** -/

/-- Every levelSchedule7 stage supplies routing-shaped preferNon data. -/
def PreferNonStageObligationAll {d : Nat} {hd : 7 ≤ d}
    (O : Params7AbstractTrajectoryRoutingObligation d hd) (t : Nat)
    (ht : t + 1 ≤ (levelSchedule7 d hd).tf) :
    Params7PreferNonStageRoutingObligation d t (O.pls t) (O.pls (t + 1)) (O.perms t) :=
  O.stages t ht

def Params7AbstractTrajectoryRoutingObligation.stageObligation
    {d : Nat} {hd : 7 ≤ d}
    (O : Params7AbstractTrajectoryRoutingObligation d hd) (t : Nat)
    (ht : t + 1 ≤ (levelSchedule7 d hd).tf) :
    PreferNonStageObligation params7 invariant7 d t
      (O.pls t) (O.pls (t + 1)) (O.perms t) :=
  Params7PreferNonStageRoutingObligation.toStageObligation (O.stages t ht)

/-! **Scramble separator -> bag-level Thm 5.1 quality (interface)** -/

/-- Per-parent separator quality from Thm 5.1 budgets at parent capacity. -/
def parentSeparatorQuality_params7 (d t : Nat) (b : KBag params7.br d) (hb : 1 ≤ b.l) :
    LocalSeparatorQuality invariant7 :=
  LocalSeparatorQuality.ofTheorem51 invariant7
    (capacity params7 d (b.l - 1) t) (capacity_pos params7 d (b.l - 1) t)

structure ScrambleSeparatorBagLink (g : ScrambleGeometry) (P : Theorem51Params g) where
  existsSep : ExistsScrambleSeparator g P
  hPeps :
    P.epsB = (invariant7.epsB : ℝ) ∧ P.deltaF = (invariant7.deltaF : ℝ) ∧
      P.epsF = (invariant7.epsF : ℝ)

def ScrambleSeparatorBagLink.parentQuality {g : ScrambleGeometry} {P : Theorem51Params g}
    (_L : ScrambleSeparatorBagLink g P)
    (d t : Nat) (b : KBag params7.br d) (_hb : 1 ≤ b.l) :
    LocalSeparatorQuality invariant7 :=
  parentSeparatorQuality_params7 d t b _hb

/-- Paper-ordinary separator -> bag quality at invariant7_paperOrdinary. -/
def parentSeparatorQuality_params7_paperOrdinary (d t : Nat) (b : KBag params7.br d)
    (hb : 1 ≤ b.l) : LocalSeparatorQuality invariant7_paperOrdinary :=
  LocalSeparatorQuality.ofTheorem51 invariant7_paperOrdinary
    (capacity params7 d (b.l - 1) t) (capacity_pos params7 d (b.l - 1) t)

/-- Unconditional link: ExistsScrambleSeparator_paperOrdinaryGeometry + Section 4
    paper-ordinary invariants. -/
structure ScrambleSeparatorBagLinkPaperOrdinary where
  existsSep : ExistsScrambleSeparator paperOrdinaryGeometry
    theorem51Params_paperOrdinaryGeometry_discharged :=
    ExistsScrambleSeparator_paperOrdinaryGeometry
  hdeltaF_epsF :
    theorem51Params_paperOrdinaryGeometry_discharged.deltaF = (invariant7.deltaF : ℝ) ∧
      theorem51Params_paperOrdinaryGeometry_discharged.epsF = (invariant7.epsF : ℝ) := by
    simp [theorem51Params_paperOrdinaryGeometry_discharged,
      theorem51Params_paperOrdinaryGeometry, theorem51Params_paperOrdinary, invariant7]

def ScrambleSeparatorBagLinkPaperOrdinary.parentQuality
    (_L : ScrambleSeparatorBagLinkPaperOrdinary) (d t : Nat) (b : KBag params7.br d)
    (hb : 1 ≤ b.l) : LocalSeparatorQuality invariant7_paperOrdinary :=
  parentSeparatorQuality_params7_paperOrdinary d t b hb

theorem scrambleSeparatorBagLinkPaperOrdinary :
    Nonempty ScrambleSeparatorBagLinkPaperOrdinary :=
  ⟨{}⟩

/-! **Module A P vs Section 7 invariant7 (schedule split)** -/

/-- Bag-level quality at Module A Chernoff eps (matches theorem51Params_moduleA_f16). -/
noncomputable def parentSeparatorQuality_moduleA_f16 (C : ModuleA_epsF_lemma62_Certificate)
    (d t : Nat) (b : KBag params7.br d) (hb : 1 ≤ b.l) :
    LocalSeparatorQuality (moduleA_invariantF16 C) :=
  LocalSeparatorQuality.ofTheorem51 (moduleA_invariantF16 C)
    (capacity params7 d (b.l - 1) t) (capacity_pos params7 d (b.l - 1) t)

structure ScrambleSeparatorModuleABagLink (C : ModuleA_epsF_lemma62_Certificate) where
  existsSep : ExistsScrambleSeparator params7Geometry_f16 (theorem51Params_moduleA_f16 C)

noncomputable def ScrambleSeparatorModuleABagLink.parentQuality
    {C : ModuleA_epsF_lemma62_Certificate}
    (_L : ScrambleSeparatorModuleABagLink C) (d t : Nat) (b : KBag params7.br d)
    (hb : 1 ≤ b.l) :
    LocalSeparatorQuality (moduleA_invariantF16 C) :=
  parentSeparatorQuality_moduleA_f16 C d t b hb

theorem not_scrambleSeparatorBagLink_invariant7_of_moduleA_f16
    (C : ModuleA_epsF_lemma62_Certificate) :
    ¬ ∃ _L : ScrambleSeparatorBagLink params7Geometry_f16 (theorem51Params_moduleA_f16 C),
        True := by
  intro ⟨L, _⟩
  have hB := L.hPeps.1
  simp [theorem51Params_moduleA_f16, invariant7] at hB

/-! **Section 7 root-init routing obligation (stationary root)** -/

def params7IdentityPerm (d : Nat) : Fin (params7.br ^ d) → Fin (params7.br ^ d) :=
  id

theorem routingBudget_nonneg_params7 (d t : Nat) (pl : Placement params7.br d)
    (perm : Fin (params7.br ^ d) → Fin (params7.br ^ d))
    (b : KBag params7.br d) (hb : 1 ≤ b.l) :
    (0 : Rat) ≤
      parentOutMass params7 d pl perm b hb +
        sibMassBound params7 invariant7 d t b hb +
        invariant7.epsB * capacity params7 d (b.l - 1) t +
          slackBound params7 d t b hb := by
  have hcap := (capacity_pos params7 d (b.l - 1) t).le
  have hpo : (0 : Rat) ≤ parentOutMass params7 d pl perm b hb := by
    dsimp [parentOutMass]
    exact_mod_cast Nat.zero_le _
  have hsib : (0 : Rat) ≤ sibMassBound params7 invariant7 d t b hb := by
    dsimp [sibMassBound]
    have hbr : (0 : Rat) ≤ ((params7.br : Rat) - 1) := by norm_num [params7]
    exact mul_nonneg (mul_nonneg (mul_nonneg hbr invariant7.mu_nonneg)
      siblingFactor_nonneg_params7) hcap
  have heps : (0 : Rat) ≤ invariant7.epsB * capacity params7 d (b.l - 1) t :=
    mul_nonneg invariant7.hepsB_nonneg hcap
  have hslack : (0 : Rat) ≤ slackBound params7 d t b hb := by
    dsimp [slackBound]
    exact mul_nonneg slackCoeff_nonneg_params7 hcap
  linarith

theorem routingBudget_nonneg_params7_paperOrdinary (d t : Nat)
    (pl : Placement params7.br d)
    (perm : Fin (params7.br ^ d) → Fin (params7.br ^ d))
    (b : KBag params7.br d) (hb : 1 ≤ b.l) :
    (0 : Rat) ≤
      parentOutMass params7 d pl perm b hb +
        sibMassBound params7 invariant7_paperOrdinary d t b hb +
        invariant7_paperOrdinary.epsB * capacity params7 d (b.l - 1) t +
          slackBound params7 d t b hb := by
  have hcap := (capacity_pos params7 d (b.l - 1) t).le
  have hpo : (0 : Rat) ≤ parentOutMass params7 d pl perm b hb := by
    dsimp [parentOutMass]
    exact_mod_cast Nat.zero_le _
  have hsib : (0 : Rat) ≤ sibMassBound params7 invariant7_paperOrdinary d t b hb := by
    dsimp [sibMassBound]
    have hbr : (0 : Rat) ≤ ((params7.br : Rat) - 1) := by norm_num [params7]
    have hsibFac : (0 : Rat) ≤ siblingFactor params7 invariant7_paperOrdinary := by
      unfold siblingFactor params7 invariant7_paperOrdinary invariant7
      positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hbr invariant7_paperOrdinary.hmu_pos.le) hsibFac)
      hcap
  have heps :
      (0 : Rat) ≤ invariant7_paperOrdinary.epsB * capacity params7 d (b.l - 1) t :=
    mul_nonneg invariant7_paperOrdinary.hepsB_nonneg hcap
  have hslack : (0 : Rat) ≤ slackBound params7 d t b hb := by
    dsimp [slackBound]
    exact mul_nonneg slackCoeff_nonneg_params7 hcap
  linarith

/-- Stationary root placement, empty fromParent, identity perm -- any d. -/
def Params7PreferNonStageRoutingObligation.rootStage (d t : Nat) :
    Params7PreferNonStageRoutingObligation d t
      (rootPlacement params7.br d) (rootPlacement params7.br d)
      (params7IdentityPerm d) := by
  let C := PreferNonStageChildrenData.rootStage_fromParent_empty params7 d t
    (params7IdentityPerm d)
  let step := placementStep_of_preferNon params7 d t (rootPlacement params7.br d)
    (rootPlacement params7.br d) (params7IdentityPerm d) C.fromParent C.hregs
  have hfrom : ∀ (b : KBag params7.br d) (hb : 1 ≤ b.l), step.fromParent b hb = ∅ :=
    fun b hb => by
      simp only [step, placementStep_of_preferNon, C,
        PreferNonStageChildrenData.rootStage_fromParent_empty,
        PreferNonStageChildrenData.fromParent_empty]
  exact {
    children := C
    routing := AbstractParentResidueRouting.of_emptyFromParent params7 invariant7 d t
      (rootPlacement params7.br d) (rootPlacement params7.br d)
      (params7IdentityPerm d) (params7IdentityPerm d) step hfrom
      (fun b hb => routingBudget_nonneg_params7 d t (rootPlacement params7.br d)
        (params7IdentityPerm d) b hb) }

def Params7PreferNonStageRoutingObligation.rootStage7 (t : Nat) :
    Params7PreferNonStageRoutingObligation 7 t
      (rootPlacement params7.br 7) (rootPlacement params7.br 7)
      (params7IdentityPerm 7) :=
  Params7PreferNonStageRoutingObligation.rootStage 7 t

def Params7PreferNonStageRoutingObligation.rootStage_toStage (d t : Nat) :
    PreferNonStageObligation params7 invariant7 d t (rootPlacement params7.br d)
      (rootPlacement params7.br d) (params7IdentityPerm d) :=
  Params7PreferNonStageRoutingObligation.toStageObligation
    (Params7PreferNonStageRoutingObligation.rootStage d t)

def Params7PreferNonStageRoutingObligation.rootStage7_toStage (t : Nat) :
    PreferNonStageObligation params7 invariant7 7 t (rootPlacement params7.br 7)
      (rootPlacement params7.br 7) (params7IdentityPerm 7) :=
  Params7PreferNonStageRoutingObligation.rootStage_toStage 7 t

/-- Stationary-root PreferNon trajectory for any d >= 7 (empty send-up each stage). -/
def Params7AbstractTrajectoryRoutingObligation.stationaryRoot (d : Nat) (hd : 7 ≤ d) :
    Params7AbstractTrajectoryRoutingObligation d hd where
  pls := fun _ => rootPlacement params7.br d
  perms := fun _ => params7IdentityPerm d
  hperm := fun _ _ => rfl
  stages := fun t _ht => Params7PreferNonStageRoutingObligation.rootStage d t
  root_init := rfl

/-- Same root stationary stage with paper-ordinary epsB budgets. -/
def PreferNonStageObligation.rootStage7_paperOrdinary (t : Nat) :
    PreferNonStageObligation params7 invariant7_paperOrdinary 7 t
      (rootPlacement params7.br 7) (rootPlacement params7.br 7)
      (params7IdentityPerm 7) := by
  let C := PreferNonStageChildrenData.rootStage_fromParent_empty params7 7 t
    (params7IdentityPerm 7)
  let step := placementStep_of_preferNon params7 7 t (rootPlacement params7.br 7)
    (rootPlacement params7.br 7) (params7IdentityPerm 7) C.fromParent C.hregs
  have hfrom : ∀ (b : KBag params7.br 7) (hb : 1 ≤ b.l), step.fromParent b hb = ∅ :=
    fun b hb => by
      simp only [step, placementStep_of_preferNon, C,
        PreferNonStageChildrenData.rootStage_fromParent_empty,
        PreferNonStageChildrenData.fromParent_empty]
  exact PreferNonStageObligation.of_children_and_routing params7 invariant7_paperOrdinary 7 t
    (rootPlacement params7.br 7) (rootPlacement params7.br 7) (params7IdentityPerm 7) C
    (AbstractParentResidueRouting.of_emptyFromParent params7 invariant7_paperOrdinary 7 t
      (rootPlacement params7.br 7) (rootPlacement params7.br 7)
      (params7IdentityPerm 7) (params7IdentityPerm 7) step hfrom
      (fun b hb => routingBudget_nonneg_params7_paperOrdinary 7 t
        (rootPlacement params7.br 7) (params7IdentityPerm 7) b hb))

/-! **Native level-1 placement and zero-stranger parent sends** -/

/-- Native rank interval of bag b as a Finset of wire indices. -/
def nativeRegs (br d : Nat) (b : KBag br d) : Finset (Fin (br ^ d)) :=
  Finset.univ.filter (fun r => b.lo ≤ r.val ∧ r.val < b.hi)

theorem mem_nativeRegs_iff {br d : Nat} (b : KBag br d) (r : Fin (br ^ d)) :
    r ∈ nativeRegs br d b ↔ b.lo ≤ r.val ∧ r.val < b.hi := by
  simp [nativeRegs]

/-- Native to b implies native to every ancestor. -/
theorem KBag.Native.ancestor {br d : Nat} {b : KBag br d} {r : Fin (br ^ d)}
    {perm : Fin (br ^ d) → Fin (br ^ d)} (h : b.Native r perm) (k : Nat)
    (hbr : 1 ≤ br) : (b.ancestor k hbr).Native r perm := by
  induction k with
  | zero =>
    simpa [KBag.ancestor] using h
  | succ k ih =>
    by_cases hk : k + 1 ≤ b.l
    · have hpar : ((b.ancestor k hbr).parent hbr).Native r perm :=
        KBag.Native.parent ih (by
          show 1 ≤ (b.ancestor k hbr).l
          simp only [KBag.ancestor]
          omega) hbr
      have heq : b.ancestor (k + 1) hbr = (b.ancestor k hbr).parent hbr := by
        apply KBag.ext
        · simp only [KBag.ancestor, KBag.parent]; omega
        · -- `b.x / br^(k+1) = b.x / br^k / br`
          simp only [KBag.ancestor, KBag.parent]
          calc b.x / br ^ (k + 1)
              = b.x / (br ^ k * br) := by rw [pow_succ]
            _ = b.x / br ^ k / br := by rw [Nat.div_div_eq_div_mul]
      rwa [heq]
    · have hroot : b.ancestor (k + 1) hbr = KBag.root br d :=
        KBag.ancestor_eq_root b (k + 1) hbr (by omega)
      simpa [hroot] using KBag.native_root (br := br) (d := d) r perm

theorem KBag.not_Strange_of_Native {br d : Nat} (b : KBag br d) (j : Nat)
    (hj : 1 ≤ j) (r : Fin (br ^ d)) (perm : Fin (br ^ d) → Fin (br ^ d))
    (hbr : 1 ≤ br) (hN : b.Native r perm) :
    ¬ b.Strange j r perm hbr := by
  simp only [KBag.Strange, show j ≠ 0 by omega, false_or]
  exact not_not.mpr (KBag.Native.ancestor hN (j - 1) hbr)

theorem strangers_nativeRegs_eq_zero {br d : Nat} (b : KBag br d) (j : Nat)
    (hj : 1 ≤ j) (hbr : 1 ≤ br) :
    b.strangers j id (nativeRegs br d b) hbr = 0 := by
  classical
  simp only [KBag.strangers]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have ⟨hrmem, hStrange⟩ := Finset.mem_filter.mp hr
  have hN : b.Native r id := by
    have ⟨hlo, hhi⟩ := (mem_nativeRegs_iff b r).mp hrmem
    exact (KBag.native_iff b r id hbr).mpr ⟨hlo, hhi⟩
  exact KBag.not_Strange_of_Native b j hj r id hbr hN hStrange

theorem nativeRegs_nonempty {br d : Nat} (b : KBag br d) (hbr : 1 ≤ br) :
    (nativeRegs br d b).Nonempty := by
  refine ⟨⟨b.lo, ?_⟩, ?_⟩
  · have : b.lo < br ^ d := by
      simp only [KBag.lo, KBag.size, bagSize]
      have hx := b.hx
      have hle : b.x * br ^ (d - b.l) < br ^ b.l * br ^ (d - b.l) :=
        Nat.mul_lt_mul_of_pos_right hx (bagSize_pos hbr b.hl)
      simpa [← pow_add, Nat.add_comm b.l, Nat.sub_add_cancel b.hl] using hle
    exact this
  · exact (mem_nativeRegs_iff b _).mpr ⟨le_rfl, KBag.lo_lt_hi b hbr⟩

/-- All wires sit in their unique level-1 native bag. -/
noncomputable def level1NativePlacement (br d : Nat) (hbr : 1 ≤ br) (hd : 1 ≤ d) :
    Placement br d where
  regs b := if b.l = 1 then nativeRegs br d b else ∅
  disjoint a b hab := by
    by_cases ha : a.l = 1 <;> by_cases hb : b.l = 1
    · simp only [ha, hb, ↓reduceIte]
      apply Finset.disjoint_left.mpr
      intro r hra hrb
      have ⟨alo, ahi⟩ := (mem_nativeRegs_iff a r).mp hra
      have ⟨blo, bhi⟩ := (mem_nativeRegs_iff b r).mp hrb
      have hxa : a.x = nativeBagIdx br d 1 r.val := by
        have := (KBag.native_iff a r id hbr).mpr ⟨alo, ahi⟩
        simpa [KBag.Native, ha] using this.symm
      have hxb : b.x = nativeBagIdx br d 1 r.val := by
        have := (KBag.native_iff b r id hbr).mpr ⟨blo, bhi⟩
        simpa [KBag.Native, hb] using this.symm
      have : a = b := by
        apply KBag.ext
        · simp [ha, hb]
        · exact hxa.trans hxb.symm
      exact hab this
    · simp [ha, hb]
    · simp [ha, hb]
    · simp [ha, hb]
  complete i := by
    classical
    let x := i.val / bagSize br d 1
    have hx : x < br := by
      simp only [x, bagSize]
      have hpow : br ^ d = br ^ (d - 1) * br := by
        rw [← pow_succ, Nat.sub_add_cancel hd]
      have hi : i.val < br ^ (d - 1) * br := by
        rw [← hpow]; exact i.isLt
      exact Nat.div_lt_of_lt_mul hi
    have hx1 : x < br ^ 1 := by simpa [pow_one] using hx
    refine ⟨⟨1, x, by omega, hx1⟩, ?_⟩
    simp only [↓reduceIte]
    refine (mem_nativeRegs_iff _ i).mpr ?_
    simp only [KBag.lo, KBag.hi, KBag.size, bagSize, x]
    constructor
    · have h := Nat.mul_div_le i.val (br ^ (d - 1))
      rwa [Nat.mul_comm] at h
    · have hs : 0 < br ^ (d - 1) := bagSize_pos hbr hd
      calc i.val
          = br ^ (d - 1) * (i.val / br ^ (d - 1)) + i.val % br ^ (d - 1) :=
            (Nat.div_add_mod i.val (br ^ (d - 1))).symm
        _ = i.val / br ^ (d - 1) * br ^ (d - 1) + i.val % br ^ (d - 1) := by
            rw [Nat.mul_comm]
        _ < i.val / br ^ (d - 1) * br ^ (d - 1) + br ^ (d - 1) :=
            Nat.add_lt_add_left (Nat.mod_lt i.val hs) _
        _ = (i.val / br ^ (d - 1) + 1) * br ^ (d - 1) := by ring

theorem level1NativePlacement_regs_eq {br d : Nat} (hbr : 1 ≤ br) (hd : 1 ≤ d)
    (b : KBag br d) :
    (level1NativePlacement br d hbr hd).regs b =
      if b.l = 1 then nativeRegs br d b else ∅ :=
  rfl

/-- Parent send-up for the root->level-1 native split: natives to each level-1 bag. -/
def nativeLevel1FromParent (br d : Nat) (b : KBag br d) (_hb : 1 ≤ b.l) :
    Finset (Fin (br ^ d)) :=
  if b.l = 1 then nativeRegs br d b else ∅

theorem nativeLevel1FromParent_nonempty_level1 {br d : Nat} (hbr : 1 ≤ br)
    (b : KBag br d) (hb : 1 ≤ b.l) (hl : b.l = 1) :
    (nativeLevel1FromParent br d b hb).Nonempty := by
  simp only [nativeLevel1FromParent, hl, ↓reduceIte]
  exact nativeRegs_nonempty b hbr

theorem strangers_nativeLevel1FromParent_eq_zero {br d : Nat} (b : KBag br d)
    (hb : 1 ≤ b.l) (j : Nat) (hj : 1 ≤ j) (hbr : 1 ≤ br) :
    b.strangers j id (nativeLevel1FromParent br d b hb) hbr = 0 := by
  by_cases hl : b.l = 1
  · simpa [nativeLevel1FromParent, hl] using strangers_nativeRegs_eq_zero b j hj hbr
  · simp only [nativeLevel1FromParent, hl, ↓reduceIte]
    exact KBag.strangers_empty b j id hbr

theorem preferNonFromChildren_rootPlacement_empty (p : ScheduleParams) (d t : Nat)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) (b : KBag p.br d) (hb : 1 ≤ b.l) :
    preferNonFromChildren p d t (rootPlacement p.br d) perm b hb = ∅ :=
  preferNonFromChildren_empty_of_childRegs_empty p d t (rootPlacement p.br d) perm b hb
    (fun hbd j => by
      rw [rootPlacement_childRegs_empty p.br d b hb hbd j]
      simp)

theorem preferNonFromChildren_level1Native_empty (p : ScheduleParams) (d t : Nat)
    (hd : 1 ≤ d) (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (b : KBag p.br d) (hb : 1 ≤ b.l) :
    preferNonFromChildren p d t (level1NativePlacement p.br d (br_ge_one p) hd) perm b hb =
      ∅ := by
  refine preferNonFromChildren_empty_of_childRegs_empty p d t
    (level1NativePlacement p.br d (br_ge_one p) hd) perm b hb ?_
  intro hbd j
  have hne : (b.child j.val j.isLt hbd).l ≠ 1 := by
    have : (b.child j.val j.isLt hbd).l = b.l + 1 := rfl
    omega
  simp only [level1NativePlacement_regs_eq, hne, ↓reduceIte, Finset.card_empty]

theorem registerCover_nativeRootSplit (p : ScheduleParams) (d t : Nat) (hd : 1 ≤ d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) :
    ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
      (level1NativePlacement p.br d (br_ge_one p) hd).regs b ⊆
        nativeLevel1FromParent p.br d b hb ∪
          preferNonFromChildren p d t (rootPlacement p.br d) perm b hb := by
  intro b hb
  rw [preferNonFromChildren_rootPlacement_empty p d t perm b hb, Finset.union_empty]
  simp only [level1NativePlacement_regs_eq, nativeLevel1FromParent]
  split_ifs <;> simp

theorem registerCover_nativeLevel1Stay (p : ScheduleParams) (d t : Nat) (hd : 1 ≤ d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) :
    ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
      (level1NativePlacement p.br d (br_ge_one p) hd).regs b ⊆
        nativeLevel1FromParent p.br d b hb ∪
          preferNonFromChildren p d t
            (level1NativePlacement p.br d (br_ge_one p) hd) perm b hb := by
  intro b hb
  rw [preferNonFromChildren_level1Native_empty p d t hd perm b hb, Finset.union_empty]
  simp only [level1NativePlacement_regs_eq, nativeLevel1FromParent]
  split_ifs <;> simp

noncomputable def PreferNonStageChildrenData.nativeRootSplit (p : ScheduleParams) (d t : Nat)
    (hd : 1 ≤ d) (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) :
    PreferNonStageChildrenData p d t (rootPlacement p.br d)
      (level1NativePlacement p.br d (br_ge_one p) hd) perm where
  fromParent := nativeLevel1FromParent p.br d
  hregs := registerCover_nativeRootSplit p d t hd perm
  hcap := ChildRegisterCapacityLower.of_emptyChildRegs p d t (rootPlacement p.br d)
    (fun b hb hbd j => by
      rw [rootPlacement_childRegs_empty p.br d b hb hbd j]
      simp)

noncomputable def PreferNonStageChildrenData.nativeLevel1Stay (p : ScheduleParams) (d t : Nat)
    (hd : 1 ≤ d) (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) :
    PreferNonStageChildrenData p d t (level1NativePlacement p.br d (br_ge_one p) hd)
      (level1NativePlacement p.br d (br_ge_one p) hd) perm where
  fromParent := nativeLevel1FromParent p.br d
  hregs := registerCover_nativeLevel1Stay p d t hd perm
  hcap := ChildRegisterCapacityLower.of_emptyChildRegs p d t
    (level1NativePlacement p.br d (br_ge_one p) hd)
    (fun b hb hbd j => by
      have hne : (b.child j.val j.isLt hbd).l ≠ 1 := by
        have : (b.child j.val j.isLt hbd).l = b.l + 1 := rfl
        omega
      simp only [level1NativePlacement_regs_eq, hne, ↓reduceIte, Finset.card_empty])

/-- Root->level-1 native PreferNon stage: nonempty zero-stranger fromParent. -/
noncomputable def Params7PreferNonStageRoutingObligation.nativeRootSplit (d t : Nat)
    (hd : 1 ≤ d) :
    Params7PreferNonStageRoutingObligation d t
      (rootPlacement params7.br d)
      (level1NativePlacement params7.br d (br_ge_one params7) hd)
      (params7IdentityPerm d) := by
  let C := PreferNonStageChildrenData.nativeRootSplit params7 d t hd (params7IdentityPerm d)
  let step := placementStep_of_preferNon params7 d t (rootPlacement params7.br d)
    (level1NativePlacement params7.br d (br_ge_one params7) hd) (params7IdentityPerm d)
    C.fromParent C.hregs
  have hBad0 : ∀ (b : KBag params7.br d) (hb : 1 ≤ b.l),
      b.strangers 1 (params7IdentityPerm d) (step.fromParent b hb) (br_ge_one params7) = 0 := by
    intro b hb
    change b.strangers 1 id (nativeLevel1FromParent params7.br d b hb) (br_ge_one params7) = 0
    exact strangers_nativeLevel1FromParent_eq_zero b hb 1 (by omega) (br_ge_one params7)
  have hFringe0 : ∀ (b : KBag params7.br d) (r : Nat) (_hr1 : 1 ≤ r) (_hrd : r ≤ d)
      (hb : 1 ≤ b.l),
      b.strangers (r + 1) (params7IdentityPerm d) (step.fromParent b hb)
        (br_ge_one params7) = 0 := by
    intro b r hr1 _hrd hb
    change b.strangers (r + 1) id (nativeLevel1FromParent params7.br d b hb)
      (br_ge_one params7) = 0
    exact strangers_nativeLevel1FromParent_eq_zero b hb (r + 1) (by omega) (br_ge_one params7)
  exact {
    children := C
    routing := AbstractParentResidueRouting.of_zeroStrangersFromParent params7 invariant7 d t
      (rootPlacement params7.br d)
      (level1NativePlacement params7.br d (br_ge_one params7) hd)
      (params7IdentityPerm d) (params7IdentityPerm d) step hBad0 hFringe0
      (fun b hb => routingBudget_nonneg_params7 d t (rootPlacement params7.br d)
        (params7IdentityPerm d) b hb) }

/-- Stationary level-1 PreferNon stage with nonempty identity fromParent. -/
noncomputable def Params7PreferNonStageRoutingObligation.nativeLevel1Stay (d t : Nat)
    (hd : 1 ≤ d) :
    Params7PreferNonStageRoutingObligation d t
      (level1NativePlacement params7.br d (br_ge_one params7) hd)
      (level1NativePlacement params7.br d (br_ge_one params7) hd)
      (params7IdentityPerm d) := by
  let C := PreferNonStageChildrenData.nativeLevel1Stay params7 d t hd (params7IdentityPerm d)
  let step := placementStep_of_preferNon params7 d t
    (level1NativePlacement params7.br d (br_ge_one params7) hd)
    (level1NativePlacement params7.br d (br_ge_one params7) hd)
    (params7IdentityPerm d) C.fromParent C.hregs
  have hBad0 : ∀ (b : KBag params7.br d) (hb : 1 ≤ b.l),
      b.strangers 1 (params7IdentityPerm d) (step.fromParent b hb) (br_ge_one params7) = 0 := by
    intro b hb
    change b.strangers 1 id (nativeLevel1FromParent params7.br d b hb) (br_ge_one params7) = 0
    exact strangers_nativeLevel1FromParent_eq_zero b hb 1 (by omega) (br_ge_one params7)
  have hFringe0 : ∀ (b : KBag params7.br d) (r : Nat) (_hr1 : 1 ≤ r) (_hrd : r ≤ d)
      (hb : 1 ≤ b.l),
      b.strangers (r + 1) (params7IdentityPerm d) (step.fromParent b hb)
        (br_ge_one params7) = 0 := by
    intro b r hr1 _hrd hb
    change b.strangers (r + 1) id (nativeLevel1FromParent params7.br d b hb)
      (br_ge_one params7) = 0
    exact strangers_nativeLevel1FromParent_eq_zero b hb (r + 1) (by omega) (br_ge_one params7)
  exact {
    children := C
    routing := AbstractParentResidueRouting.of_zeroStrangersFromParent params7 invariant7 d t
      (level1NativePlacement params7.br d (br_ge_one params7) hd)
      (level1NativePlacement params7.br d (br_ge_one params7) hd)
      (params7IdentityPerm d) (params7IdentityPerm d) step hBad0 hFringe0
      (fun b hb => routingBudget_nonneg_params7 d t
        (level1NativePlacement params7.br d (br_ge_one params7) hd)
        (params7IdentityPerm d) b hb) }

theorem Params7PreferNonStageRoutingObligation.nativeRootSplit_fromParent_nonempty
    (d t : Nat) (hd : 1 ≤ d) (b : KBag params7.br d) (hb : 1 ≤ b.l)
    (hl : b.l = 1) :
    ((Params7PreferNonStageRoutingObligation.nativeRootSplit d t hd).children.fromParent b
      hb).Nonempty :=
  nativeLevel1FromParent_nonempty_level1 (br_ge_one params7) b hb hl

/-- Evolving PreferNon trajectory: stage 0 splits root->level-1 natives; later stages
    stay at level 1 with nonempty identity parent cover. At d = 7, tf = 1, so only
    the split stage runs. Zero-stranger sends meet Thm 5.1 / paper-ordinary quality budgets. -/
noncomputable def Params7AbstractTrajectoryRoutingObligation.nativeLevel1 (d : Nat)
    (hd : 7 ≤ d) : Params7AbstractTrajectoryRoutingObligation d hd where
  pls := fun t =>
    if t = 0 then rootPlacement params7.br d
    else level1NativePlacement params7.br d (br_ge_one params7) (by omega : 1 ≤ d)
  perms := fun _ => params7IdentityPerm d
  hperm := fun _ _ => rfl
  stages := fun t _ht => by
    by_cases h0 : t = 0
    · subst h0
      simpa using Params7PreferNonStageRoutingObligation.nativeRootSplit d 0
        (by omega : 1 ≤ d)
    · have hpl :
          (if t = 0 then rootPlacement params7.br d
            else level1NativePlacement params7.br d (br_ge_one params7)
              (by omega : 1 ≤ d)) =
            level1NativePlacement params7.br d (br_ge_one params7) (by omega : 1 ≤ d) := by
        simp [h0]
      have hpl' :
          (if t + 1 = 0 then rootPlacement params7.br d
            else level1NativePlacement params7.br d (br_ge_one params7)
              (by omega : 1 ≤ d)) =
            level1NativePlacement params7.br d (br_ge_one params7) (by omega : 1 ≤ d) := by
        simp
      simpa [hpl, hpl'] using
        Params7PreferNonStageRoutingObligation.nativeLevel1Stay d t (by omega : 1 ≤ d)
  root_init := rfl

/-- At d = 7, the native level-1 trajectory is fully determined by the root split. -/
noncomputable def Params7AbstractTrajectoryRoutingObligation.nativeLevel1_d7 :
    Params7AbstractTrajectoryRoutingObligation 7 (by decide : 7 ≤ 7) :=
  Params7AbstractTrajectoryRoutingObligation.nativeLevel1 7 (by decide)

theorem Params7AbstractTrajectoryRoutingObligation.nativeLevel1_d7_pls1 :
    Params7AbstractTrajectoryRoutingObligation.nativeLevel1_d7.pls 1 =
      level1NativePlacement params7.br 7 (br_ge_one params7) (by decide : 1 ≤ 7) := by
  simp [Params7AbstractTrajectoryRoutingObligation.nativeLevel1_d7,
    Params7AbstractTrajectoryRoutingObligation.nativeLevel1]

/-- Paper-ordinary bag quality matches the Thm 5.1 budgets used by zero-stranger routing. -/
theorem ScrambleSeparatorBagLinkPaperOrdinary.parentQuality_eq_ofTheorem51
    (L : ScrambleSeparatorBagLinkPaperOrdinary) (d t : Nat)
    (b : KBag params7.br d) (hb : 1 ≤ b.l) :
    L.parentQuality d t b hb =
      LocalSeparatorQuality.ofTheorem51 invariant7_paperOrdinary
        (capacity params7 d (b.l - 1) t) (capacity_pos params7 d (b.l - 1) t) :=
  rfl

end Chvatal
