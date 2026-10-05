module
/-
  # Chvatal 1830 endpoint package

  Source: V. Chvatal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §4 + §7.

  Status: packages the kernel-checked outsider induction under a full
  `StageKernelWithChildren` trajectory with the §7 depth accounting. This is
  NOT yet a sorting theorem: separator existence (Thm 5.1), concrete
  placement/routing Finsets, fair send-up density, and purity ⇒ sortedness
  remain open. Separator conditions (4.1)–(4.5) hold at `params7`.
-/

public import AKS.Chvatal.ChildSend
public import AKS.Chvatal.StageCountsFill
public import AKS.Chvatal.Params
public import AKS.Chvatal.DepthSkeleton

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

end Chvatal
