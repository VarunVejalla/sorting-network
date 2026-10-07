module
/-
  # Chvatal 1830 endpoint package

  Source: V. Chvatal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §4 + §7.

  **Kernel-checked (no extra axioms):** §7 `SeparatorConds` at `params7`;
  paper `levelSchedule7` with Lemma 3.2 from the envelope (no snap hyp);
  outsider induction from `AbstractChildSendTrajectory` + root init;
  meeting-level purity from `P` + the checked purity envelope; same-perm
  cross-perm discharge; §7 depth arithmetic (`totalDepth`, padded
  `1830·log₂ n − 58657`); Thm 5.1 *statement*, Lemma 6.1 closing numeric,
  B/F → `AbstractParentResidue` routing bridge; Module A Lemma 6.1/6.2 fail
  unions → combinatorial B/F when `ModuleACombinatorialObligation` is assumed.

  **Hypothesis-dependent (honest residual):** `Sorting1830Obligation` bundles
  (1) a full §7 abstract trajectory, (2) residual scramble side
  (`Theorem51Obligation`, `ModuleACombinatorialObligation` + combinatorial→matrix
  bridge, or combinatorial-only Module A), (3) a
  final-sorter depth `≤ 903` (discharged via Batcher `p(p+1)/2` at `p = 42`),
  and (4) a `NetworkDepthAssemblyObligation`: root / ordinary / final stage
  networks with §7 paper depth budgets, kernel-checked depth `≤ totalDepth d`,
  and residual `Sorts` on the assembled network. The endpoint
  `network_depth_le_1830_of_sorting1830Obligation` is proved from (4) plus
  `clog₆₄ n = d`; it does *not* construct stage nets from the trajectory or
  from Thm 5.1. Unconditional `D(n) ≤ 1830 log₂ n` remains open.
-/

public import AKS.Chvatal.AbstractPlacement
public import AKS.Chvatal.PropertyBF
public import AKS.Chvatal.Theorem51
public import AKS.Chvatal.ModuleA
public import AKS.Chvatal.ModuleABridge
public import AKS.Chvatal.MatrixBridge
public import AKS.Chvatal.Schedule7
public import AKS.Chvatal.Params
public import AKS.Chvatal.DepthSkeleton
public import AKS.Chvatal.SchedulerLemmas
public import AKS.Bitonic.TightDepth
public import AKS.Sort.Defs
public import AKS.Sort.Depth
public import AKS.Sort.Monotone

@[expose] public section

namespace Chvatal

/-- Trajectory of child-send kernels for the outsider induction. -/
structure ChildSendTrajectory (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d)
    (pls : Nat → Placement p.br d)
    (perms : Nat → (Fin (p.br ^ d) → Fin (p.br ^ d))) where
  kernels : ∀ t, t + 1 ≤ sched.tf →
    StageKernelWithChildren p ip d sched t (pls t) (perms t)
      (pls (t + 1)) (perms (t + 1))

/-- Final outsider bound from a child-send trajectory. -/
theorem outsiderBound_induction_of_childSend (p : ScheduleParams)
    (ip : InvariantParams) (d : Nat) (sched : LevelSchedule p d)
    (pls : Nat → Placement p.br d)
    (perms : Nat → (Fin (p.br ^ d) → Fin (p.br ^ d)))
    (hconds : SeparatorConds p ip)
    (traj : ChildSendTrajectory p ip d sched pls perms)
    (h0 : OutsiderBoundLe p ip d sched 0 (pls 0) (perms 0)) :
    OutsiderBoundLe p ip d sched sched.tf (pls sched.tf) (perms sched.tf) := by
  have step : ∀ t, t ≤ sched.tf →
      OutsiderBoundLe p ip d sched t (pls t) (perms t) := by
    intro t ht
    induction t with
    | zero => exact h0
    | succ t ih =>
      have ht' : t + 1 ≤ sched.tf := ht
      have ht0 : t ≤ sched.tf := by omega
      exact outsiderBound_step_of_childSend p ip d sched t (pls t) (pls (t + 1))
        (perms t) (perms (t + 1)) hconds (ih ht0) (traj.kernels t ht')
  exact step sched.tf le_rfl

/-- Abstract trajectory: children-send data + parent-send residue per stage.
    Same-perm stages (`hperm`) discharge cross-perm fair mono. -/
structure AbstractChildSendTrajectory (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d)
    (pls : Nat → Placement p.br d)
    (perms : Nat → (Fin (p.br ^ d) → Fin (p.br ^ d)))
    (steps : ∀ t, t + 1 ≤ sched.tf →
      PlacementStep p d (pls t) (pls (t + 1))) where
  hperm : ∀ t (_ht : t + 1 ≤ sched.tf), perms (t + 1) = perms t
  childSend : ∀ t (ht : t + 1 ≤ sched.tf),
    AbstractChildSend p d t (pls t) (pls (t + 1)) (steps t ht) (perms t)
  parent : ∀ t (ht : t + 1 ≤ sched.tf),
    AbstractParentResidue p ip d t (pls t) (perms t) (pls (t + 1)) (perms t)
      (steps t ht)

/-- Assemble a `ChildSendTrajectory` from abstract children-send + parent residue. -/
def ChildSendTrajectory.ofAbstract (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d)
    (pls : Nat → Placement p.br d)
    (perms : Nat → (Fin (p.br ^ d) → Fin (p.br ^ d)))
    (steps : ∀ t, t + 1 ≤ sched.tf →
      PlacementStep p d (pls t) (pls (t + 1)))
    (traj : AbstractChildSendTrajectory p ip d sched pls perms steps) :
    ChildSendTrajectory p ip d sched pls perms where
  kernels := fun t ht => by
    have hpeq := traj.hperm t ht
    exact hpeq ▸
      StageKernelWithChildren.ofAbstractChildSend p ip d sched t
        (pls t) (pls (t + 1)) (perms t) (steps t ht) ht
        (traj.childSend t ht) (traj.parent t ht)

/-- Outsider induction from abstract children-send trajectory + parent residue. -/
theorem outsiderBound_induction_of_abstract (p : ScheduleParams)
    (ip : InvariantParams) (d : Nat) (sched : LevelSchedule p d)
    (pls : Nat → Placement p.br d)
    (perms : Nat → (Fin (p.br ^ d) → Fin (p.br ^ d)))
    (steps : ∀ t, t + 1 ≤ sched.tf →
      PlacementStep p d (pls t) (pls (t + 1)))
    (hconds : SeparatorConds p ip)
    (traj : AbstractChildSendTrajectory p ip d sched pls perms steps)
    (h0 : OutsiderBoundLe p ip d sched 0 (pls 0) (perms 0)) :
    OutsiderBoundLe p ip d sched sched.tf (pls sched.tf) (perms sched.tf) :=
  outsiderBound_induction_of_childSend p ip d sched pls perms hconds
    (ChildSendTrajectory.ofAbstract p ip d sched pls perms steps traj) h0

/-- Assemble `AbstractChildSendTrajectory` when every stage supplies
    `PreferNonStageObligation` (children-send kernel-checked; parent residue
    remains the per-stage mathematical obligation). -/
def AbstractChildSendTrajectory.of_preferNonStages
    (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (sched : LevelSchedule p d)
    (pls : Nat → Placement p.br d)
    (perms : Nat → (Fin (p.br ^ d) → Fin (p.br ^ d)))
    (hperm : ∀ t (_ht : t + 1 ≤ sched.tf), perms (t + 1) = perms t)
    (stages : ∀ t (ht : t + 1 ≤ sched.tf),
      PreferNonStageObligation p ip d t (pls t) (pls (t + 1)) (perms t)) :
    AbstractChildSendTrajectory p ip d sched pls perms
      (fun t ht => (stages t ht).step) where
  hperm := hperm
  childSend := fun t ht => (stages t ht).childSend
  parent := fun t ht => (stages t ht).parent

/-- §7 depth accounting at `N = 64^d`: `1830 · lg N - 69637`. -/
theorem depth_pow_eq_1830 (d : Nat) (hd : 7 ≤ d) :
    (totalDepth d : ℝ) =
      1830 * Real.logb 2 ((64 ^ d : ℕ) : ℝ) - 69637 :=
  totalDepth_pow_eq d hd

/-- Padded form used for general `n` with `clog 64 n = d`. -/
theorem depth_logb_le_1830 {n d : Nat} (hd : 7 ≤ d) (hclog : Nat.clog 64 n = d)
    (hn : 1 < n) :
    (totalDepth d : ℝ) ≤ 1830 * Real.logb 2 (n : ℝ) - 58657 :=
  totalDepth_logb_le hd hclog hn

/-- Full §7 separator conditions (4.1)–(4.5). -/
theorem params7_separatorConds : SeparatorConds params7 invariant7 :=
  separatorConds_params7

/-- §7 conditions with paper-ordinary `ε_B = 1/8·10⁷` (matches DCS-TR-294 ordinary separators). -/
theorem params7_separatorConds_paperOrdinary :
    SeparatorConds params7 invariant7_paperOrdinary :=
  separatorConds_params7_paperOrdinary

/-- Unconditional Thm 5.1 obligation at paper-ordinary geometry. -/
theorem Theorem51Obligation_paperOrdinaryGeometry :
    Theorem51Obligation paperOrdinaryGeometry
      theorem51Params_paperOrdinaryGeometry_discharged :=
  ⟨ExistsScrambleSeparator_paperOrdinaryGeometry⟩

/-- Unconditional Thm 5.1 obligation at paper-root geometry. -/
theorem Theorem51Obligation_paperRootGeometry :
    Theorem51Obligation paperRootGeometry
      theorem51Params_paperRootGeometry_discharged :=
  ⟨ExistsScrambleSeparator_paperRootGeometry⟩

/-- Residual §7 outsider induction with paper-ordinary invariant scalars. -/
theorem outsiderBound_params7_paperOrdinary_of_abstract (d : Nat)
    (sched : LevelSchedule params7 d)
    (pls : Nat → Placement params7.br d)
    (perms : Nat → (Fin (params7.br ^ d) → Fin (params7.br ^ d)))
    (steps : ∀ t, t + 1 ≤ sched.tf →
      PlacementStep params7 d (pls t) (pls (t + 1)))
    (traj : AbstractChildSendTrajectory params7 invariant7_paperOrdinary d sched pls perms
      steps)
    (h0 : OutsiderBoundLe params7 invariant7_paperOrdinary d sched 0 (pls 0) (perms 0)) :
    OutsiderBoundLe params7 invariant7_paperOrdinary d sched sched.tf
      (pls sched.tf) (perms sched.tf) :=
  outsiderBound_induction_of_abstract params7 invariant7_paperOrdinary d sched pls perms steps
    params7_separatorConds_paperOrdinary traj h0

/-- Lemma 3.2 on `levelSchedule7` from the paper envelope (no snap hyp). -/
theorem lemma32_params7 (d : Nat) (hd : 7 ≤ d) (t : Nat)
    (hasc : (levelSchedule7 d hd).alpha t <
      (levelSchedule7 d hd).alpha (t + 1)) :
    (levelSchedule7 d hd).alpha t = 0 ∨
      capacity params7 d ((levelSchedule7 d hd).alpha t) t ≤
        params7.A * (params7.br : Rat) ^ 2 / params7.nu :=
  lemma32_levelSchedule7 d hd t hasc

/-- Initial `P` at `params7` on the root placement. -/
theorem outsiderBoundLe_params7_root (d : Nat) (sched : LevelSchedule params7 d)
    (perm : Fin (params7.br ^ d) → Fin (params7.br ^ d)) :
    OutsiderBoundLe params7 invariant7 d sched 0
      (rootPlacement params7.br d) perm :=
  outsiderBoundLe_rootPlacement params7 invariant7 d sched perm

/-- Residual §7 outsider induction on any schedule. -/
theorem outsiderBound_params7_of_abstract (d : Nat)
    (sched : LevelSchedule params7 d)
    (pls : Nat → Placement params7.br d)
    (perms : Nat → (Fin (params7.br ^ d) → Fin (params7.br ^ d)))
    (steps : ∀ t, t + 1 ≤ sched.tf →
      PlacementStep params7 d (pls t) (pls (t + 1)))
    (traj : AbstractChildSendTrajectory params7 invariant7 d sched pls perms
      steps)
    (h0 : OutsiderBoundLe params7 invariant7 d sched 0 (pls 0) (perms 0)) :
    OutsiderBoundLe params7 invariant7 d sched sched.tf
      (pls sched.tf) (perms sched.tf) :=
  outsiderBound_induction_of_abstract params7 invariant7 d sched pls perms steps
    params7_separatorConds traj h0

/-- Outsider induction on the concrete §7 schedule. -/
theorem outsiderBound_params7_schedule7 (d : Nat) (hd : 7 ≤ d)
    (pls : Nat → Placement params7.br d)
    (perms : Nat → (Fin (params7.br ^ d) → Fin (params7.br ^ d)))
    (steps : ∀ t, t + 1 ≤ (levelSchedule7 d hd).tf →
      PlacementStep params7 d (pls t) (pls (t + 1)))
    (traj : AbstractChildSendTrajectory params7 invariant7 d
      (levelSchedule7 d hd) pls perms steps)
    (h0 : OutsiderBoundLe params7 invariant7 d (levelSchedule7 d hd) 0
      (pls 0) (perms 0)) :
    OutsiderBoundLe params7 invariant7 d (levelSchedule7 d hd)
      (levelSchedule7 d hd).tf (pls (levelSchedule7 d hd).tf)
      (perms (levelSchedule7 d hd).tf) :=
  outsiderBound_params7_of_abstract d (levelSchedule7 d hd) pls perms steps traj h0

/-- Top-level purity at `levelSchedule7` under an abstract trajectory.
    Envelope `μ δ^r c(d−6, tf) < 1` is kernel-checked for `r ≥ 1`. -/
theorem params7_purity_of_abstract (d : Nat) (hd : 7 ≤ d)
    (pls : Nat → Placement params7.br d)
    (perms : Nat → (Fin (params7.br ^ d) → Fin (params7.br ^ d)))
    (steps : ∀ t, t + 1 ≤ (levelSchedule7 d hd).tf →
      PlacementStep params7 d (pls t) (pls (t + 1)))
    (traj : AbstractChildSendTrajectory params7 invariant7 d
      (levelSchedule7 d hd) pls perms steps)
    (h0 : OutsiderBoundLe params7 invariant7 d (levelSchedule7 d hd) 0
      (pls 0) (perms 0))
    (r : Nat) (hr1 : 1 ≤ r) (hr : r ≤ d)
    (b : KBag params7.br d)
    (hb : b.l = (levelSchedule7 d hd).alpha ((levelSchedule7 d hd).tf)) :
    b.strangers (r + 1) (perms ((levelSchedule7 d hd).tf))
      ((pls ((levelSchedule7 d hd).tf)).regs b) (br_ge_one params7) = 0 := by
  have hP := outsiderBound_params7_schedule7 d hd pls perms steps traj h0
  have henv := purityEnvelope7_sched d hd r hr1
  have hle := hP b r hr
  have hbound :
      (b.strangers (r + 1) (perms ((levelSchedule7 d hd).tf))
        ((pls ((levelSchedule7 d hd).tf)).regs b) (br_ge_one params7) : Rat) < 1 := by
    calc (b.strangers (r + 1) (perms ((levelSchedule7 d hd).tf))
            ((pls ((levelSchedule7 d hd).tf)).regs b) (br_ge_one params7) : Rat)
        ≤ invariant7.mu * invariant7.delta ^ r *
            capacity params7 d b.l ((levelSchedule7 d hd).tf) := hle
      _ = invariant7.mu * invariant7.delta ^ r *
            capacity params7 d
              ((levelSchedule7 d hd).alpha ((levelSchedule7 d hd).tf))
              ((levelSchedule7 d hd).tf) := by rw [hb]
      _ < 1 := henv
  have hnat :
      b.strangers (r + 1) (perms ((levelSchedule7 d hd).tf))
        ((pls ((levelSchedule7 d hd).tf)).regs b) (br_ge_one params7) < 1 := by
    exact_mod_cast hbound
  omega

/-- Same-perm fair discharges cross-perm mono (`hPermLe` is reflexivity). -/
theorem crossPerm_discharged_of_hperm (p : ScheduleParams) (d : Nat)
    (pl pl' : Placement p.br d) (step : PlacementStep p d pl pl')
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (cover : ChildSendCover p d pl pl' step)
    (hSame : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d)
        (j : Fin p.br),
      (((b.child j.val j.isLt hbd).strangers 2 perm
          (cover.sendUp b hb hbd j) (br_ge_one p) : Rat)) *
          ((pl.regs (b.child j.val j.isLt hbd)).card : Rat) ≤
        (((b.child j.val j.isLt hbd).strangers 2 perm
            (pl.regs (b.child j.val j.isLt hbd)) (br_ge_one p) : Rat)) *
          ((cover.sendUp b hb hbd j).card : Rat)) :
    ChildSendFair p d pl pl' step perm perm cover :=
  childSendFair_of_same_perm p d pl pl' step perm cover hSame

/-- Conditional depth link: a sorting network of depth `≤ totalDepth d` has
    depth bounded by the §7 padded `1830 lg n − 58657` form. -/
theorem network_depth_le_1830_logb_of_totalDepth
    {n d : Nat} (hd : 7 ≤ d) (hclog : Nat.clog 64 n = d) (hn : 1 < n)
    (net : ComparatorNetwork (64 ^ d))
    (_hs : ComparatorNetwork.Sorts net)
    (hdep : net.depth ≤ totalDepth d) :
    (net.depth : ℝ) ≤ 1830 * Real.logb 2 (n : ℝ) - 58657 := by
  have h1 : (net.depth : ℝ) ≤ (totalDepth d : ℝ) := by exact_mod_cast hdep
  exact h1.trans (depth_logb_le_1830 hd hclog hn)

/-- Conditional purity→sort package: zero strangers at the meeting level plus an
    executable sorter of depth `≤ totalDepth` yields the §7 depth bound.
    Scramble-separator existence (Thm 5.1) is still required to produce `net`. -/
theorem depth_bound_of_purity_network
    {n d : Nat} (hd : 7 ≤ d) (hclog : Nat.clog 64 n = d) (hn : 1 < n)
    (net : ComparatorNetwork (64 ^ d))
    (hs : ComparatorNetwork.Sorts net)
    (hdep : net.depth ≤ totalDepth d) :
    (net.depth : ℝ) ≤ 1830 * Real.logb 2 (n : ℝ) - 58657 :=
  network_depth_le_1830_logb_of_totalDepth hd hclog hn net hs hdep

/-! **§7 sorting obligation package (1830 endpoint)** -/

theorem clog64_pow_eq (d : Nat) : Nat.clog 64 (64 ^ d) = d :=
  Nat.clog_pow 64 d (by norm_num : 1 < 64)

/-- Abstract child-send trajectory on paper `levelSchedule7` with root init. -/
structure Params7AbstractTrajectory (d : Nat) (hd : 7 ≤ d) where
  pls : Nat → Placement params7.br d
  perms : Nat → (Fin (params7.br ^ d) → Fin (params7.br ^ d))
  steps : ∀ t, t + 1 ≤ (levelSchedule7 d hd).tf →
    PlacementStep params7 d (pls t) (pls (t + 1))
  traj : AbstractChildSendTrajectory params7 invariant7 d
    (levelSchedule7 d hd) pls perms steps
  root_init : pls 0 = rootPlacement params7.br d

theorem Params7AbstractTrajectory.outsiderBoundLe_init
    {d : Nat} {hd : 7 ≤ d} (O : Params7AbstractTrajectory d hd) :
    OutsiderBoundLe params7 invariant7 d (levelSchedule7 d hd) 0 (O.pls 0)
      (O.perms 0) := by
  rw [O.root_init]
  exact outsiderBoundLe_params7_root d (levelSchedule7 d hd) (O.perms 0)

theorem Params7AbstractTrajectory.outsiderBoundLe_tf
    {d : Nat} {hd : 7 ≤ d} (O : Params7AbstractTrajectory d hd) :
    OutsiderBoundLe params7 invariant7 d (levelSchedule7 d hd)
      (levelSchedule7 d hd).tf (O.pls (levelSchedule7 d hd).tf)
      (O.perms (levelSchedule7 d hd).tf) :=
  outsiderBound_params7_schedule7 d hd O.pls O.perms O.steps O.traj
    O.outsiderBoundLe_init

theorem Params7AbstractTrajectory.purity_at_meet
    {d : Nat} {hd : 7 ≤ d} (O : Params7AbstractTrajectory d hd) (r : Nat)
    (hr1 : 1 ≤ r) (hr : r ≤ d)
    (b : KBag params7.br d)
    (hb : b.l = (levelSchedule7 d hd).alpha ((levelSchedule7 d hd).tf)) :
    b.strangers (r + 1) (O.perms ((levelSchedule7 d hd).tf))
      ((O.pls ((levelSchedule7 d hd).tf)).regs b) (br_ge_one params7) = 0 :=
  params7_purity_of_abstract d hd O.pls O.perms O.steps O.traj
    O.outsiderBoundLe_init r hr1 hr b hb

/-- Residual data for a full §7 abstract trajectory after preferNon children-send
    discharge. Supply per-stage `fromParent` + register cover + capacity + parent
    residue; same-perm and outsider induction then follow from
    `Params7AbstractTrajectory.of_preferNonObligation` (or
    `of_routingObligation` when only Thm 5.1 routing bounds are assumed).
    Still open globally: construct those stages from Thm 5.1 / executable
    routing, and assemble a sorting network with depth `≤ totalDepth d`. -/
structure Params7AbstractTrajectoryObligation (d : Nat) (hd : 7 ≤ d) where
  pls : Nat → Placement params7.br d
  perms : Nat → (Fin (params7.br ^ d) → Fin (params7.br ^ d))
  hperm : ∀ t (_ht : t + 1 ≤ (levelSchedule7 d hd).tf),
    perms (t + 1) = perms t
  stages : ∀ t (ht : t + 1 ≤ (levelSchedule7 d hd).tf),
    PreferNonStageObligation params7 invariant7 d t
      (pls t) (pls (t + 1)) (perms t)
  root_init : pls 0 = rootPlacement params7.br d

def Params7AbstractTrajectory.of_preferNonObligation {d : Nat} {hd : 7 ≤ d}
    (O : Params7AbstractTrajectoryObligation d hd) :
    Params7AbstractTrajectory d hd where
  pls := O.pls
  perms := O.perms
  steps := fun t ht => (O.stages t ht).step
  traj :=
    AbstractChildSendTrajectory.of_preferNonStages params7 invariant7 d
      (levelSchedule7 d hd) O.pls O.perms O.hperm O.stages
  root_init := O.root_init

/-- Residual final-layer depth (paper `903` comparators in §7 accounting). -/
structure FinalSorterDepthBudget where
  depth : Nat
  hle903 : depth ≤ 903

/-- Batcher depth on `2^42` wires: `bitonicSort 42` has depth `≤ 903` (`42·43/2`). -/
theorem batcher_depth_le_903 : (bitonicSort 42).depth ≤ 903 :=
  bitonicSort_42_depth_le_903

/-- §7 final-sorter budget at `42·43/2 = 903`, linked to `batcher_depth_le_903`. -/
def FinalSorterDepthBudget.of_batcher42 : FinalSorterDepthBudget where
  depth := 903
  hle903 := le_rfl

theorem FinalSorterDepthBudget.of_batcher42_sorts :
    (bitonicSort 42).depth ≤ FinalSorterDepthBudget.of_batcher42.depth :=
  batcher_depth_le_903

/-- §7 stage networks: root separator, one ordinary round template, final sorter. -/
def assembledChvatalNetwork {d : Nat}
    (rootNet ordinaryNet finalNet : ComparatorNetwork (64 ^ d)) :
    ComparatorNetwork (64 ^ d) :=
  rootNet.append (ordinaryNet.appendRepeated (ordinaryRounds d) |>.append finalNet)

/-- §7 stage assembly sorts when each stage sorts (ordinary round repeated `ordinaryRounds d`). -/
theorem assembledChvatalNetwork_sorts {d : Nat}
    (rootNet ordinaryNet finalNet : ComparatorNetwork (64 ^ d))
    (hroot : ComparatorNetwork.Sorts.{0} rootNet)
    (hord : ComparatorNetwork.Sorts.{0} ordinaryNet)
    (hfinal : ComparatorNetwork.Sorts.{0} finalNet) :
    ComparatorNetwork.Sorts.{0} (assembledChvatalNetwork rootNet ordinaryNet finalNet) := by
  unfold assembledChvatalNetwork
  set ord := ordinaryNet.appendRepeated (ordinaryRounds d)
  by_cases hr : ordinaryRounds d = 0
  · simp only [ord, hr, ComparatorNetwork.appendRepeated, ComparatorNetwork.append]
    exact ComparatorNetwork.sorts_append rootNet finalNet hroot hfinal
  · have hk : 0 < ordinaryRounds d := by omega
    have hordRep : ComparatorNetwork.Sorts.{0} ord :=
      ComparatorNetwork.sorts_appendRepeated_of_pos (ordinaryRounds d) hk ordinaryNet hord
    exact ComparatorNetwork.sorts_append rootNet (ord.append finalNet) hroot
      (ComparatorNetwork.sorts_append ord finalNet hordRep hfinal)

/-- Residual assembly: stage networks + depth budgets; sorting of the composed
    network remains explicit. Depth `≤ totalDepth d` is discharged from budgets. -/
structure NetworkDepthAssemblyObligation (d : Nat) where
  budget : StageDepthBudget d
  rootNet : ComparatorNetwork (64 ^ d)
  ordinaryNet : ComparatorNetwork (64 ^ d)
  finalNet : ComparatorNetwork (64 ^ d)
  hroot : rootNet.depth ≤ budget.rootSepDepth
  hord : ordinaryNet.depth ≤ budget.ordinaryStageDepth
  hfinal : finalNet.depth ≤ budget.finalSorterDepth
  sorts : ComparatorNetwork.Sorts.{0}
    (assembledChvatalNetwork rootNet ordinaryNet finalNet)

def NetworkDepthAssemblyObligation.composed {d : Nat}
    (O : NetworkDepthAssemblyObligation d) : ComparatorNetwork (64 ^ d) :=
  assembledChvatalNetwork O.rootNet O.ordinaryNet O.finalNet

theorem NetworkDepthAssemblyObligation.composed_sorts {d : Nat}
    (O : NetworkDepthAssemblyObligation d) : ComparatorNetwork.Sorts.{0} O.composed :=
  O.sorts

/-- Build assembly obligation from §7 stage depth budgets and per-stage sorting. -/
def NetworkDepthAssemblyObligation.of_stage_sorts {d : Nat}
    (budget : StageDepthBudget d)
    (rootNet ordinaryNet finalNet : ComparatorNetwork (64 ^ d))
    (hroot : rootNet.depth ≤ budget.rootSepDepth)
    (hord : ordinaryNet.depth ≤ budget.ordinaryStageDepth)
    (hfinal : finalNet.depth ≤ budget.finalSorterDepth)
    (hrootSorts : ComparatorNetwork.Sorts.{0} rootNet)
    (hordSorts : ComparatorNetwork.Sorts.{0} ordinaryNet)
    (hfinalSorts : ComparatorNetwork.Sorts.{0} finalNet) :
    NetworkDepthAssemblyObligation d where
  budget := budget
  rootNet := rootNet
  ordinaryNet := ordinaryNet
  finalNet := finalNet
  hroot := hroot
  hord := hord
  hfinal := hfinal
  sorts := assembledChvatalNetwork_sorts rootNet ordinaryNet finalNet
    hrootSorts hordSorts hfinalSorts

theorem assembledChvatalNetwork_depth_le {d : Nat}
    (B : StageDepthBudget d)
    (rootNet ordinaryNet finalNet : ComparatorNetwork (64 ^ d))
    (hroot : rootNet.depth ≤ B.rootSepDepth)
    (hord : ordinaryNet.depth ≤ B.ordinaryStageDepth)
    (hfinal : finalNet.depth ≤ B.finalSorterDepth) :
    (assembledChvatalNetwork rootNet ordinaryNet finalNet).depth ≤
      B.rootSepDepth + ordinaryRounds d * B.ordinaryStageDepth + B.finalSorterDepth := by
  unfold assembledChvatalNetwork
  set ord := ordinaryNet.appendRepeated (ordinaryRounds d)
  have hord' : ord.depth ≤ ordinaryRounds d * B.ordinaryStageDepth :=
    ComparatorNetwork.depth_appendRepeated (ordinaryRounds d) ordinaryNet hord
  have hdepth :
      (rootNet.append (ord.append finalNet)).depth ≤
        rootNet.depth + ord.depth + finalNet.depth := by
    calc
      _ ≤ rootNet.depth + (ord.append finalNet).depth :=
        ComparatorNetwork.depth_append_le _ _
      _ ≤ rootNet.depth + (ord.depth + finalNet.depth) := by
        simpa [Nat.add_comm, Nat.add_assoc] using
          add_le_add_right (ComparatorNetwork.depth_append_le ord finalNet) rootNet.depth
      _ ≤ rootNet.depth + ord.depth + finalNet.depth := le_of_eq (by ring)
  have hsum :
      rootNet.depth + ord.depth + finalNet.depth ≤
        B.rootSepDepth + ordinaryRounds d * B.ordinaryStageDepth + B.finalSorterDepth :=
    add_le_add (add_le_add hroot hord') hfinal
  exact hdepth.trans hsum

theorem NetworkDepthAssemblyObligation.depth_le_totalDepth {d : Nat}
    (O : NetworkDepthAssemblyObligation d) :
    O.composed.depth ≤ totalDepth d :=
  (assembledChvatalNetwork_depth_le O.budget O.rootNet O.ordinaryNet O.finalNet
    O.hroot O.hord O.hfinal).trans (StageDepthBudget.depth_sum_le d O.budget)

theorem NetworkDepthAssemblyObligation.depth_le {d : Nat}
    (O : NetworkDepthAssemblyObligation d) : O.composed.depth ≤ totalDepth d :=
  O.depth_le_totalDepth

/-- Three sequential networks: depth is at most the sum (from `ComparatorNetwork.depth_append3`). -/
theorem comparatorNetwork_depth_append3 {n : Nat}
    (net₁ net₂ net₃ : ComparatorNetwork n) :
    (net₁.append net₂ |>.append net₃).depth ≤
      net₁.depth + net₂.depth + net₃.depth :=
  ComparatorNetwork.depth_append3 net₁ net₂ net₃

/-- Link paper final-sorter budget `903` to `FinalSorterDepthBudget.of_batcher42`. -/
theorem StageDepthBudget.ofPaper_final_le_batcher42 (d : Nat) :
    (StageDepthBudget.ofPaper d).finalSorterDepth ≤
      FinalSorterDepthBudget.of_batcher42.depth := by
  unfold StageDepthBudget.ofPaper FinalSorterDepthBudget.of_batcher42
  exact le_rfl

/-- Residual scramble side: full Thm 5.1 or discharged Module A counting. -/
inductive ScrambleSeparatorResidual where
  | theorem51 (g : ScrambleGeometry) (P : Theorem51Params g)
      (h : Theorem51Obligation g P)
  | moduleA (epsB : ℝ) (f : Nat) (hf : Even f) (deltaF epsF : ℝ)
      (h : ModuleACombinatorialObligation 100 16 epsB f hf deltaF epsF)
  | moduleA_bridge (g : ScrambleGeometry) (P : Theorem51Params g)
      (O : ModuleACombinatorialObligation 100 16 P.epsB g.f g.hfeven P.deltaF P.epsF)
      (hαβ : ModuleACombinedFailFraction_m100)
      (hinner : O.F.inner = Lemma62InnerBound.thirty)
      (hExist : ModuleACombinatorialExistence_onPipeline_m100 g.f g.hfeven P.epsB P.deltaF P.epsF)
      (bridge : CombinatorialToMatrixObligation g.m g.n g.f (scrambleGeometry_hn g) g.hfeven
        (scrambleGeometry_f_le_m g) P.epsB P.deltaF P.epsF)
      (rowScramble : ∀ σ : Scramble g.m g.n, RowScrambleNetwork g.m g.n σ)
      (h : Theorem51Obligation g P)

/-- Unconditional separator residual at paper-ordinary geometry. -/
noncomputable def ScrambleSeparatorResidual.paperOrdinary : ScrambleSeparatorResidual :=
  .theorem51 paperOrdinaryGeometry theorem51Params_paperOrdinaryGeometry_discharged
    Theorem51Obligation_paperOrdinaryGeometry

/-- Unconditional separator residual at paper-root geometry (`m = 2^79`). -/
noncomputable def ScrambleSeparatorResidual.paperRoot : ScrambleSeparatorResidual :=
  .theorem51 paperRootGeometry theorem51Params_paperRootGeometry_discharged
    Theorem51Obligation_paperRootGeometry

theorem existsCombinatorialPropertyB_onPipeline_of_moduleA_m100
    {epsB : ℝ} {f : Nat} {hf : Even f} {deltaF epsF : ℝ}
    (obl : ModuleACombinatorialObligation 100 16 epsB f hf deltaF epsF) :
    ExistsCombinatorialPropertyBOnPipeline 100 16 epsB :=
  ExistsCombinatorialPropertyBOnPipeline_of_ModuleA_m100 obl

theorem existsCombinatorialPropertyB_of_moduleA
    {m n : Nat} {epsB : ℝ} {f : Nat} {hf : Even f} {deltaF epsF : ℝ}
    (havg : AvgRowOnesLeOne m n)
    (obl : ModuleACombinatorialObligation m n epsB f hf deltaF epsF) :
    ExistsCombinatorialPropertyB m n epsB :=
  ExistsCombinatorialPropertyB_of_ModuleA havg obl

theorem existsCombinatorialPropertyF_of_moduleA
    {m n : Nat} {epsB : ℝ} {f : Nat} {hf : Even f} {deltaF epsF : ℝ}
    (obl : ModuleACombinatorialObligation m n epsB f hf deltaF epsF) :
    ExistsCombinatorialPropertyF m n f hf deltaF epsF :=
  ExistsCombinatorialPropertyF_of_ModuleA obl

theorem existsScrambleSeparator_of_theorem51
    {g : ScrambleGeometry} {P : Theorem51Params g}
    (obl : Theorem51Obligation g P) :
    ExistsScrambleSeparator g P :=
  obl.exists_separator

theorem existsScrambleSeparator_of_moduleA_bridge
    {g : ScrambleGeometry} {P : Theorem51Params g}
    (hm : g.m = 100) (hn : g.n = 16)
    (O : ModuleACombinatorialObligation g.m g.n P.epsB g.f g.hfeven P.deltaF P.epsF)
    (hαβ : ModuleACombinedFailFraction_m100)
    (hinner : O.F.inner = Lemma62InnerBound.thirty)
    (hExist : ModuleACombinatorialExistence_onPipeline_m100 g.f g.hfeven P.epsB P.deltaF P.epsF)
    (bridge : CombinatorialToMatrixObligation g.m g.n g.f (scrambleGeometry_hn g) g.hfeven
      (scrambleGeometry_f_le_m g) P.epsB P.deltaF P.epsF)
    (rowScramble : ∀ σ : Scramble g.m g.n, RowScrambleNetwork g.m g.n σ)
    (hRes : ModuleAPipelineBFImpliesScrambleSeparator_m100 g P) :
    ExistsScrambleSeparator g P :=
  ExistsScrambleSeparator_of_moduleA_and_bridge hm hn O hαβ hinner hExist bridge rowScramble hRes


/-- Bundled §7 obligation toward depth `≤ 1830 log₂ n` (hypothesis-dependent). -/
structure Sorting1830Obligation (d : Nat) (hd : 7 ≤ d) where
  abstract : Params7AbstractTrajectory d hd
  finalSorter : FinalSorterDepthBudget
  separator : ScrambleSeparatorResidual
  assembly : NetworkDepthAssemblyObligation d
  hfinalBudget : assembly.budget.finalSorterDepth ≤ finalSorter.depth

/-- Bundle §7 sorting obligation from trajectory stages + separator residual + assembly. -/
def Sorting1830Obligation.of_components {d : Nat} {hd : 7 ≤ d}
    (traj : Params7AbstractTrajectoryObligation d hd)
    (finalSorter : FinalSorterDepthBudget)
    (separator : ScrambleSeparatorResidual)
    (assembly : NetworkDepthAssemblyObligation d)
    (hfinalBudget : assembly.budget.finalSorterDepth ≤ finalSorter.depth) :
    Sorting1830Obligation d hd where
  abstract := Params7AbstractTrajectory.of_preferNonObligation traj
  finalSorter := finalSorter
  separator := separator
  assembly := assembly
  hfinalBudget := hfinalBudget

/-- Same with default Batcher final-sorter budget (`903`). -/
def Sorting1830Obligation.of_preferNonAssembly {d : Nat} {hd : 7 ≤ d}
    (traj : Params7AbstractTrajectoryObligation d hd)
    (separator : ScrambleSeparatorResidual)
    (assembly : NetworkDepthAssemblyObligation d)
    (hfinalBudget :
      assembly.budget.finalSorterDepth ≤ FinalSorterDepthBudget.of_batcher42.depth) :
    Sorting1830Obligation d hd :=
  Sorting1830Obligation.of_components traj FinalSorterDepthBudget.of_batcher42 separator
    assembly hfinalBudget

def Sorting1830Obligation.net {d : Nat} {hd : 7 ≤ d}
    (O : Sorting1830Obligation d hd) : ComparatorNetwork (64 ^ d) :=
  O.assembly.composed

def Sorting1830Obligation.sorts {d : Nat} {hd : 7 ≤ d}
    (O : Sorting1830Obligation d hd) : ComparatorNetwork.Sorts.{0} O.net :=
  O.assembly.composed_sorts

theorem Sorting1830Obligation.depth_le {d : Nat} {hd : 7 ≤ d}
    (O : Sorting1830Obligation d hd) : O.net.depth ≤ totalDepth d :=
  O.assembly.depth_le_totalDepth

theorem Sorting1830Obligation.outsiderBoundLe_tf {d : Nat} {hd : 7 ≤ d}
    (O : Sorting1830Obligation d hd) :
    OutsiderBoundLe params7 invariant7 d (levelSchedule7 d hd)
      (levelSchedule7 d hd).tf
      (O.abstract.pls (levelSchedule7 d hd).tf)
      (O.abstract.perms (levelSchedule7 d hd).tf) :=
  O.abstract.outsiderBoundLe_tf

theorem Sorting1830Obligation.purity_at_meet {d : Nat} {hd : 7 ≤ d}
    (O : Sorting1830Obligation d hd)
    (r : Nat) (hr1 : 1 ≤ r) (hr : r ≤ d) (b : KBag params7.br d)
    (hb : b.l = (levelSchedule7 d hd).alpha ((levelSchedule7 d hd).tf)) :
    b.strangers (r + 1) (O.abstract.perms ((levelSchedule7 d hd).tf))
      ((O.abstract.pls ((levelSchedule7 d hd).tf)).regs b)
      (br_ge_one params7) = 0 :=
  O.abstract.purity_at_meet r hr1 hr b hb

theorem Sorting1830Obligation.scrambleSeparator_of_theorem51 {d : Nat} {hd : 7 ≤ d}
    (O : Sorting1830Obligation d hd) :
    match O.separator with
    | ScrambleSeparatorResidual.theorem51 g P _ => ExistsScrambleSeparator g P
    | ScrambleSeparatorResidual.moduleA_bridge g P _ _ _ _ _ _ _ => ExistsScrambleSeparator g P
    | ScrambleSeparatorResidual.moduleA _ _ _ _ _ _ => True := by
  cases O.separator with
  | theorem51 g P obl => exact existsScrambleSeparator_of_theorem51 obl
  | moduleA_bridge _g _P _O' _hαβ _hinner _hExist _bridge _rowScramble h =>
    exact existsScrambleSeparator_of_theorem51 h
  | moduleA _ _ _ _ _ _ => trivial

theorem Sorting1830Obligation.combinatorialBF_of_moduleA {d : Nat} {hd : 7 ≤ d}
    (O : Sorting1830Obligation d hd) :
    match O.separator with
    | ScrambleSeparatorResidual.moduleA epsB f hf deltaF epsF _ =>
        ExistsCombinatorialPropertyBOnPipeline 100 16 epsB ∧
          ExistsCombinatorialPropertyF 100 16 f hf deltaF epsF
    | ScrambleSeparatorResidual.moduleA_bridge g P _ _ _ _ _ _ _ =>
        ModuleACombinatorialExistence_onPipeline_m100 g.f g.hfeven P.epsB P.deltaF P.epsF
    | ScrambleSeparatorResidual.theorem51 _ _ _ => True := by
  cases O.separator with
  | theorem51 _ _ _ => trivial
  | moduleA_bridge g P O' hαβ hinner _hExist _ _ _ =>
    exact exists_combinatorialScrambleBF_onPipeline_of_ModuleA_m100 O' hinner
  | moduleA epsB f hf deltaF epsF obl =>
    exact ⟨ExistsCombinatorialPropertyBOnPipeline_of_ModuleA_m100 obl,
      existsCombinatorialPropertyF_of_moduleA obl⟩

theorem network_depth_le_1830_pow_of_sorting1830Obligation
    (d : Nat) (hd : 7 ≤ d) (O : Sorting1830Obligation d hd)
    (hn : 1 < 64 ^ d) :
    (O.net.depth : ℝ) ≤
      1830 * Real.logb 2 ((64 ^ d : ℕ) : ℝ) - 58657 :=
  network_depth_le_1830_logb_of_totalDepth hd (clog64_pow_eq d) hn O.net O.sorts O.depth_le

/-- Main padded depth endpoint from the §7 obligation package. -/
theorem network_depth_le_1830_of_sorting1830Obligation {n d : Nat} (hd : 7 ≤ d)
    (hclog : Nat.clog 64 n = d) (hn : 1 < n) (O : Sorting1830Obligation d hd) :
    (O.net.depth : ℝ) ≤ 1830 * Real.logb 2 (n : ℝ) - 58657 :=
  network_depth_le_1830_logb_of_totalDepth hd hclog hn O.net O.sorts O.depth_le

theorem depth_bound_of_sorting1830Obligation {n d : Nat} (hd : 7 ≤ d)
    (hclog : Nat.clog 64 n = d) (hn : 1 < n) (O : Sorting1830Obligation d hd) :
    (O.net.depth : ℝ) ≤ 1830 * Real.logb 2 (n : ℝ) - 58657 :=
  network_depth_le_1830_of_sorting1830Obligation hd hclog hn O

/-- §7 parent residue from Thm 5.1 routing bounds (capacity positivity discharged). -/
def abstractParentResidue_params7_ofTheorem51Routing
    (d t : Nat) (pl pl' : Placement params7.br d)
    (perm perm' : Fin (params7.br ^ d) → Fin (params7.br ^ d))
    (step : PlacementStep params7 d pl pl')
    (R : AbstractParentResidueRouting params7 invariant7 d t pl pl' perm perm'
      step) :
    AbstractParentResidue params7 invariant7 d t pl perm pl' perm' step :=
  AbstractParentResidue.ofTheorem51BudgetRouting params7 invariant7 d t pl pl'
    perm perm' step R

/-- One §7 scheduler stage: preferNon children (kernel-checked) + Thm 5.1 routing. -/
structure Params7PreferNonStageRoutingObligation (d : Nat) (t : Nat)
    (pl pl' : Placement params7.br d)
    (perm : Fin (params7.br ^ d) → Fin (params7.br ^ d)) where
  children : PreferNonStageChildrenData params7 d t pl pl' perm
  routing : AbstractParentResidueRouting params7 invariant7 d t pl pl' perm perm
    (placementStep_of_preferNon params7 d t pl pl' perm
      children.fromParent children.hregs)

def Params7PreferNonStageRoutingObligation.toStageObligation
    {d t : Nat} {pl pl' : Placement params7.br d}
    {perm : Fin (params7.br ^ d) → Fin (params7.br ^ d)}
    (O : Params7PreferNonStageRoutingObligation d t pl pl' perm) :
    PreferNonStageObligation params7 invariant7 d t pl pl' perm :=
  PreferNonStageObligation.of_children_and_routing params7 invariant7 d t pl pl'
    perm O.children O.routing

/-- Residual §7 trajectory as routing obligations per stage (children + Thm 5.1). -/
structure Params7AbstractTrajectoryRoutingObligation (d : Nat) (hd : 7 ≤ d) where
  pls : Nat → Placement params7.br d
  perms : Nat → (Fin (params7.br ^ d) → Fin (params7.br ^ d))
  hperm : ∀ t (_ht : t + 1 ≤ (levelSchedule7 d hd).tf),
    perms (t + 1) = perms t
  stages : ∀ t (ht : t + 1 ≤ (levelSchedule7 d hd).tf),
    Params7PreferNonStageRoutingObligation d t (pls t) (pls (t + 1)) (perms t)
  root_init : pls 0 = rootPlacement params7.br d

def Params7AbstractTrajectoryObligation.of_routing
    {d : Nat} {hd : 7 ≤ d}
    (O : Params7AbstractTrajectoryRoutingObligation d hd) :
    Params7AbstractTrajectoryObligation d hd where
  pls := O.pls
  perms := O.perms
  hperm := O.hperm
  stages := fun t ht =>
    Params7PreferNonStageRoutingObligation.toStageObligation (O.stages t ht)
  root_init := O.root_init

def Params7AbstractTrajectory.of_routingObligation {d : Nat} {hd : 7 ≤ d}
    (O : Params7AbstractTrajectoryRoutingObligation d hd) :
    Params7AbstractTrajectory d hd :=
  Params7AbstractTrajectory.of_preferNonObligation
    (Params7AbstractTrajectoryObligation.of_routing O)

/-- Bundle from routing-shaped trajectory obligations (children + Thm 5.1 per stage). -/
def Sorting1830Obligation.of_routingAssembly {d : Nat} {hd : 7 ≤ d}
    (traj : Params7AbstractTrajectoryRoutingObligation d hd)
    (separator : ScrambleSeparatorResidual)
    (assembly : NetworkDepthAssemblyObligation d)
    (hfinalBudget :
      assembly.budget.finalSorterDepth ≤ FinalSorterDepthBudget.of_batcher42.depth) :
    Sorting1830Obligation d hd :=
  Sorting1830Obligation.of_preferNonAssembly
    (Params7AbstractTrajectoryObligation.of_routing traj) separator assembly hfinalBudget

theorem Params7AbstractTrajectory.of_routingObligation_outsiderBoundLe_tf
    {d : Nat} {hd : 7 ≤ d}
    (O : Params7AbstractTrajectoryRoutingObligation d hd) :
    OutsiderBoundLe params7 invariant7 d (levelSchedule7 d hd)
      (levelSchedule7 d hd).tf
      ((Params7AbstractTrajectory.of_routingObligation O).pls
        (levelSchedule7 d hd).tf)
      ((Params7AbstractTrajectory.of_routingObligation O).perms
        (levelSchedule7 d hd).tf) :=
  (Params7AbstractTrajectory.of_routingObligation O).outsiderBoundLe_tf

theorem Params7AbstractTrajectory.of_routingObligation_purity_at_meet
    {d : Nat} {hd : 7 ≤ d}
    (O : Params7AbstractTrajectoryRoutingObligation d hd)
    (r : Nat) (hr1 : 1 ≤ r) (hr : r ≤ d) (b : KBag params7.br d)
    (hb : b.l = (levelSchedule7 d hd).alpha ((levelSchedule7 d hd).tf)) :
    b.strangers (r + 1)
        ((Params7AbstractTrajectory.of_routingObligation O).perms
          ((levelSchedule7 d hd).tf))
        (((Params7AbstractTrajectory.of_routingObligation O).pls
            ((levelSchedule7 d hd).tf)).regs b)
        (br_ge_one params7) = 0 :=
  (Params7AbstractTrajectory.of_routingObligation O).purity_at_meet r hr1 hr b hb

end Chvatal
