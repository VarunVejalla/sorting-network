module
/-
  # Chvatal §4 inductive preservation of the outsider bound

  Source: V. Chvatal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §4.

  Status: proves `OutsiderBoundLe` at `t` + `SeparatorConds` + `StageModel`
  implies `OutsiderBoundLe` at `t+1`, and purity when the top capacity envelope
  is `< 1`. The `StageModel` fields package combinatorial stage-dynamics facts
  (wire counts, separator routing, source splits); discharging them from an
  executable scheduler is deferred.
-/

public import AKS.Chvatal.OutsiderLemmas
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Chvatal

/-! **Non-strict outsider bound (inductive form)** -/

/-- Non-strict form of proposition `P`, used for induction. Paper's strict
    `<` is recovered for purity when the envelope itself is `< 1`. -/
def OutsiderBoundLe (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (_sched : LevelSchedule p d) (t : Nat)
    (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) : Prop :=
  ∀ (b : KBag p.br d) (r : Nat), r ≤ d →
    ((b.strangers (r + 1) perm (pl.regs b) (br_ge_one p) : Rat)) ≤
      ip.mu * ip.delta ^ r * capacity p d b.l t

theorem OutsiderBound.to_le (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (sched : LevelSchedule p d) (t : Nat)
    (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (h : OutsiderBound p ip d sched t pl perm) :
    OutsiderBoundLe p ip d sched t pl perm := by
  intro b r hr
  exact le_of_lt (h b r hr)

/-! **One-step preservation** -/

/-- Order-0 step for non-root bags. -/
theorem outsiderBound_step_order0 (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hconds : SeparatorConds p ip)
    (M : StageModel p ip d sched t pl perm pl' perm')
    (b : KBag p.br d) (hb : 1 ≤ b.l) :
    ((b.strangers 1 perm' (pl'.regs b) (br_ge_one p) : Rat)) ≤
      ip.mu * capacity p d b.l (t + 1) := by
  obtain ⟨_, h42, _, _, _⟩ := hconds
  have hc : 0 < capacity p d (b.l - 1) t := M.hcap_pos b hb
  have hbound := lemma43_of_sources p ip (capacity p d (b.l - 1) t) hc
    (M.order0 b hb) (M.order0_parent b hb) (M.order0_child b hb) h42
  have hcap : capacity p d b.l (t + 1) =
      p.A * p.nu * capacity p d (b.l - 1) t := by
    rw [show b.l = (b.l - 1) + 1 by omega]
    exact capacity_child_stage p d (b.l - 1) t
  calc ((b.strangers 1 perm' (pl'.regs b) (br_ge_one p) : Rat))
      ≤ (M.order0 b hb).total := M.order0_total b hb
    _ ≤ ip.mu * (p.A * p.nu * capacity p d (b.l - 1) t) := hbound
    _ = ip.mu * capacity p d b.l (t + 1) := by rw [hcap]

/-- Order-`r` step (`r ≥ 1`) for non-root bags. -/
theorem outsiderBound_step_orderr (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hconds : SeparatorConds p ip)
    (M : StageModel p ip d sched t pl perm pl' perm')
    (b : KBag p.br d) (hb : 1 ≤ b.l)
    (r : Nat) (hr1 : 1 ≤ r) (hrd : r ≤ d) :
    ((b.strangers (r + 1) perm' (pl'.regs b) (br_ge_one p) : Rat)) ≤
      ip.mu * ip.delta ^ r * capacity p d b.l (t + 1) := by
  obtain ⟨_, _, _, _, h45⟩ := hconds
  have hc : 0 < capacity p d (b.l - 1) t := M.hcap_pos b hb
  have hbound := lemma44_of_sources p ip (capacity p d (b.l - 1) t) hc r hr1
    (M.orderR b r hr1 hrd hb) (M.orderR_parent b r hr1 hrd hb)
    (M.orderR_child b r hr1 hrd hb) h45
  have hcap : capacity p d b.l (t + 1) =
      p.A * p.nu * capacity p d (b.l - 1) t := by
    rw [show b.l = (b.l - 1) + 1 by omega]
    exact capacity_child_stage p d (b.l - 1) t
  calc ((b.strangers (r + 1) perm' (pl'.regs b) (br_ge_one p) : Rat))
      ≤ (M.orderR b r hr1 hrd hb).total := M.orderR_total b r hr1 hrd hb
    _ ≤ ip.mu * ip.delta ^ r *
          (p.A * p.nu * capacity p d (b.l - 1) t) := hbound
    _ = ip.mu * ip.delta ^ r * capacity p d b.l (t + 1) := by rw [hcap]

/-- Full one-step preservation of `OutsiderBoundLe`. -/
theorem outsiderBound_step (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hconds : SeparatorConds p ip)
    (M : StageModel p ip d sched t pl perm pl' perm')
    (_hP : OutsiderBoundLe p ip d sched t pl perm) :
    OutsiderBoundLe p ip d sched (t + 1) pl' perm' := by
  intro b r hr
  by_cases hb0 : b.l = 0
  · simpa [hb0] using M.level0 b r hb0 hr
  · have hb : 1 ≤ b.l := by omega
    by_cases hr0 : r = 0
    · subst hr0
      have h := outsiderBound_step_order0 p ip d sched t pl pl' perm perm'
        hconds M b hb
      simpa [pow_zero, mul_one] using h
    · have hr1 : 1 ≤ r := by omega
      exact outsiderBound_step_orderr p ip d sched t pl pl' perm perm'
        hconds M b hb r hr1 hr

/-! **Induction and purity** -/

/-- A trajectory of stage models across `0 … tf-1`. -/
structure StageTrajectory (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (sched : LevelSchedule p d)
    (pls : Nat → Placement p.br d)
    (perms : Nat → (Fin (p.br ^ d) → Fin (p.br ^ d))) where
  models : ∀ t, t + 1 ≤ sched.tf →
    StageModel p ip d sched t (pls t) (perms t) (pls (t + 1)) (perms (t + 1))

/-- Induction along a trajectory: `P(0)` and stage models yield `P(tf)`. -/
theorem outsiderBound_induction (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d)
    (pls : Nat → Placement p.br d)
    (perms : Nat → (Fin (p.br ^ d) → Fin (p.br ^ d)))
    (hconds : SeparatorConds p ip)
    (traj : StageTrajectory p ip d sched pls perms)
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
      have M := traj.models t ht'
      exact outsiderBound_step p ip d sched t (pls t) (pls (t + 1))
        (perms t) (perms (t + 1)) hconds M (ih ht0)
  exact step sched.tf le_rfl

/-- Purity at the final top level under a strict capacity envelope. -/
theorem outsider_purity_of_model (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d)
    (pls : Nat → Placement p.br d)
    (perms : Nat → (Fin (p.br ^ d) → Fin (p.br ^ d)))
    (hconds : SeparatorConds p ip)
    (traj : StageTrajectory p ip d sched pls perms)
    (h0 : OutsiderBoundLe p ip d sched 0 (pls 0) (perms 0))
    (r : Nat) (hr : r ≤ d)
    (b : KBag p.br d) (hb : b.l = sched.alpha sched.tf)
    (hcap : ip.mu * ip.delta ^ r *
        capacity p d (sched.alpha sched.tf) sched.tf < 1) :
    b.strangers (r + 1) (perms sched.tf) ((pls sched.tf).regs b)
      (br_ge_one p) = 0 := by
  have hP := outsiderBound_induction p ip d sched pls perms hconds traj h0
  have hle := hP b r hr
  have hbound :
      (b.strangers (r + 1) (perms sched.tf) ((pls sched.tf).regs b)
        (br_ge_one p) : Rat) < 1 := by
    calc (b.strangers (r + 1) (perms sched.tf) ((pls sched.tf).regs b)
            (br_ge_one p) : Rat)
        ≤ ip.mu * ip.delta ^ r * capacity p d b.l sched.tf := hle
      _ = ip.mu * ip.delta ^ r *
            capacity p d (sched.alpha sched.tf) sched.tf := by rw [hb]
      _ < 1 := hcap
  have hnat :
      b.strangers (r + 1) (perms sched.tf) ((pls sched.tf).regs b)
        (br_ge_one p) < 1 := by
    exact_mod_cast hbound
  omega

/-- Root order-0 bound from the exceptional separator (Lemma 4.3 root). -/
theorem outsiderBound_root_order0 (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat)
    (pl' : Placement p.br d)
    (perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hconds : SeparatorConds p ip)
    (root : RootSeparatorQuality ip)
    (hcap : capacity p d 1 1 = root.N / (p.br : Rat))
    (b : KBag p.br d) (_hb : b.l = 1)
    (hsent : ((b.strangers 1 perm' (pl'.regs b) (br_ge_one p) : Rat)) ≤
      root.childOutsiders) :
    ((b.strangers 1 perm' (pl'.regs b) (br_ge_one p) : Rat)) ≤
      ip.mu * capacity p d 1 1 := by
  obtain ⟨h41, _, _, _, _⟩ := hconds
  have hlt := lemma43_root_of_star p ip d root h41 hcap
  linarith [hsent, hlt]

end Chvatal
