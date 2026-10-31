import D2StrongFlowStage
import D2BotRiseRunBridge

namespace Chvatal.D2Reserve

/-- The affine sender envelope is inherited by every child of an ordinary
parent update. This is the arithmetic form needed when lifting the bound
through an arbitrary path in the scheduled tree. -/
theorem d2_regular_update_preserves_child_affine_profile
    {role : D2Role} (hrole : role = .topRise \/ role = .mid \/ role = .botDesc)
    {a G total low high pi half c : Nat} (size pos : Fin 8 → Nat)
    (hcpos : 0 < c)
    (hbalance : low + high = G)
    (hconserve : a + G = total)
    (hpiAlloc : pi ≤ a)
    (heven : pi = 2 * half)
    (hlow : low ≤ G) (hhigh : high ≤ G)
    (hprofileCap : (G = 0 ∧ 256 * pi ≤ c) ∨
      (8192 * G + 7 ≤ 15 * c ∧ 4096 * pi ≤ 15 * c))
    (hleftReserve : c ≤ 128 * size 0)
    (hrightReserve : c ≤ 128 * size 7)
    (hstart : pos 0 = 0)
    (hcontig : ∀ k : Nat, (hk : k < 7) →
      pos ⟨k + 1, by omega⟩ = pos ⟨k, by omega⟩ + size ⟨k, by omega⟩)
    (htotal : pos 7 + size 7 = total) :
    ∀ j : Fin 8,
      8192 * d2LocalChildDeficitUpdate role (pos j) (size j)
        (low + half) (total - high - half) + 7 ≤ 30 * c := by
  have hmid := d2_ordinary_update_preserves_affine_15over8192 size pos
    hcpos hbalance hconserve hpiAlloc heven hlow hhigh
    hprofileCap hleftReserve hrightReserve hstart hcontig htotal
  intro j
  rw [d2LocalChildDeficitUpdate_regular_eq_mid hrole]
  exact hmid j

/-- Re-express the child estimate in the next sender's scheduled capacity.
This isolates the exact scale arithmetic needed by a path induction. -/
theorem d2_parent_affine_profile_to_child_capacity
    {role : D2Role} (hrole : role = .topRise \/ role = .mid \/ role = .botDesc)
    {a G total low high pi half c childCap childG : Nat}
    (size pos : Fin 8 → Nat) (j : Fin 8)
    (hcpos : 0 < c) (hchildCap : childCap = 2 * c)
    (hchild : childG = d2LocalChildDeficitUpdate role (pos j) (size j)
      (low + half) (total - high - half))
    (hbalance : low + high = G) (hconserve : a + G = total)
    (hpiAlloc : pi ≤ a) (heven : pi = 2 * half)
    (hlow : low ≤ G) (hhigh : high ≤ G)
    (hprofileCap : (G = 0 ∧ 256 * pi ≤ c) ∨
      (8192 * G + 7 ≤ 15 * c ∧ 4096 * pi ≤ 15 * c))
    (hleftReserve : c ≤ 128 * size 0)
    (hrightReserve : c ≤ 128 * size 7)
    (hstart : pos 0 = 0)
    (hcontig : ∀ k : Nat, (hk : k < 7) →
      pos ⟨k + 1, by omega⟩ = pos ⟨k, by omega⟩ + size ⟨k, by omega⟩)
    (htotal : pos 7 + size 7 = total) :
    8192 * childG + 7 ≤ 15 * childCap := by
  have hchildren := d2_regular_update_preserves_child_affine_profile
    hrole size pos hcpos hbalance hconserve hpiAlloc heven hlow hhigh hprofileCap
    hleftReserve hrightReserve hstart hcontig htotal
  rw [hchild, hchildCap]
  nlinarith [hchildren j]

/-- One actual subtree-history step transports the ordinary affine child
profile through the concrete recursive update. The arbitrary overwrite of
the selected parent's root is harmless because it leaves its child subtrees
unchanged. -/
theorem d2FlowTreeRunWithParentOverwrites_child_affine_deficit
    {h i n G low high : Nat}
    (initial : D2FlowTree (h + 1))
    (active : Nat → Nat → Bool) (role : Nat → Nat → D2Role)
    (quota : Nat → Nat → D2Role → Nat)
    (overwrite : Nat → Nat × Nat × Nat)
    (children : Fin 8 → D2FlowTree h)
    (hnode : d2FlowTreeRunWithParentOverwrites initial i active role quota
      overwrite n = .node G low high children)
    (ha : active n i = true)
    (hr : role n i = .topRise ∨ role n i = .mid ∨ role n i = .botDesc)
    {allocation c : Nat}
    (hcpos : 0 < c)
    (hbalance : low + high = G)
    (hconserve : allocation + G = d2FlowTotal (fun j =>
      d2FlowTreeRootDeficit (children j)))
    (hpiAlloc : quota n i (role n i) ≤ allocation)
    (heven : quota n i (role n i) = 2 * (quota n i (role n i) / 2))
    (hlow : low ≤ G) (hhigh : high ≤ G)
    (hprofileCap : (G = 0 ∧ 256 * quota n i (role n i) ≤ c) ∨
      (8192 * G + 7 ≤ 15 * c ∧
        4096 * quota n i (role n i) ≤ 15 * c))
    (hleftReserve : c ≤ 128 * d2FlowTreeRootDeficit (children 0))
    (hrightReserve : c ≤ 128 * d2FlowTreeRootDeficit (children 7)) :
    ∀ j, 8192 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeRunWithParentOverwrites initial i active role quota
          overwrite (n + 1)) j) + 7 ≤ 30 * c := by
  have hlocal := d2FlowStage_regular_child_affine_deficit
    (active := active n) (role := role n) (quota := quota n)
    (h := h) (i := i) (G := G) (low := low) (high := high)
    (allocation := allocation) (c := c)
    children
    ha hr hcpos hbalance hconserve hpiAlloc heven hlow hhigh hprofileCap
    hleftReserve hrightReserve
  intro j
  change 8192 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeSetRoot
          (d2FlowStage (active n) (role n) (quota n) (h + 1) i
            (d2FlowTreeRunWithParentOverwrites initial i active role quota
              overwrite n))
          (overwrite n).1 (overwrite n).2.1 (overwrite n).2.2) j) + 7
      ≤ 30 * c
  rw [d2FlowTreeChild_setRoot, hnode]
  exact hlocal j

/-- Arbitrary-path version for the concrete D2 candidate: an ordinary active
parent satisfying its affine inputs writes child roots with the exact profile
at the next level/stage capacity. Ancestor writes are included through the
path-history context. -/
theorem d2FlowCandidateRun_path_parent_affine_child
    {h i t G low high : Nat} (path : D2FlowPath i)
    (children : Fin 8 → D2FlowTree h)
    (hnode : d2FlowTreeAtPath i
      (d2FlowCandidateRun (h + 1 + i)
        (d2FlowTreeInitial 8192 (h + 1 + i)) t) path =
      .node G low high children)
    (ha : d2FlowCandidateActive (h + 1 + i) t i = true)
    (hr : d2FlowCandidateRole (h + 1 + i) t i = .topRise ∨
      d2FlowCandidateRole (h + 1 + i) t i = .mid ∨
      d2FlowCandidateRole (h + 1 + i) t i = .botDesc)
    {allocation c : Nat} (hcpos : 0 < c)
    (hbalance : low + high = G)
    (hconserve : allocation + G = d2FlowTotal (fun j =>
      d2FlowTreeRootDeficit (children j)))
    (hpiAlloc : d2FlowCandidateQuota (h + 1 + i) t i
      (d2FlowCandidateRole (h + 1 + i) t i) ≤ allocation)
    (heven : d2FlowCandidateQuota (h + 1 + i) t i
      (d2FlowCandidateRole (h + 1 + i) t i) =
        2 * (d2FlowCandidateQuota (h + 1 + i) t i
          (d2FlowCandidateRole (h + 1 + i) t i) / 2))
    (hlow : low ≤ G) (hhigh : high ≤ G)
    (hprofileCap : (G = 0 ∧ 256 * d2FlowCandidateQuota (h + 1 + i) t i
        (d2FlowCandidateRole (h + 1 + i) t i) ≤ c) ∨
      (8192 * G + 7 ≤ 15 * c ∧
        4096 * d2FlowCandidateQuota (h + 1 + i) t i
          (d2FlowCandidateRole (h + 1 + i) t i) ≤ 15 * c))
    (hleftReserve : c ≤ 128 * d2FlowTreeRootDeficit (children 0))
    (hrightReserve : c ≤ 128 * d2FlowTreeRootDeficit (children 7))
    (hchildCap : d2FlowCandidateCapacity (h + 1 + i) (i + 1) (t + 1) =
      2 * c) :
    ∀ j, 8192 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath i
          (d2FlowCandidateRun (h + 1 + i)
            (d2FlowTreeInitial 8192 (h + 1 + i)) (t + 1)) path) j) + 7 ≤
      15 * d2FlowCandidateCapacity (h + 1 + i) (i + 1) (t + 1) := by
  let d := h + 1 + i
  let initial := d2FlowTreeInitial 8192 d
  let runActive := d2FlowCandidateRunActive d
  let runRole := d2FlowCandidateRunRole d
  let runQuota := d2FlowCandidateRunQuota d
  let overwrite := d2FlowCandidateRunOverwrite d initial
  let ctx := d2FlowTreePathContext i initial path 0
    runActive runRole runQuota overwrite
  have hlevel : ctx.level = i := by
    simpa [ctx, runActive, runRole, runQuota, overwrite, d, initial] using
      d2FlowTreePathContext_level initial path 0 runActive runRole runQuota
        overwrite
  have hpath (s : Nat) :
      d2FlowTreeAtPath i (d2FlowCandidateRun d initial s) path =
        d2FlowTreeRunWithParentOverwrites ctx.initial ctx.level
          runActive runRole runQuota ctx.overwrite s := by
    rw [d2FlowCandidateRun_path_as_history]
    exact d2FlowTreePathHistory_eq_context_run initial path 0
      (d2FlowCandidateRunActive d) (d2FlowCandidateRunRole d)
      (d2FlowCandidateRunQuota d) (d2FlowCandidateRunOverwrite d initial) s
  have hnodeHistory :
      d2FlowTreeRunWithParentOverwrites ctx.initial ctx.level runActive
        runRole runQuota ctx.overwrite t = .node G low high children := by
    calc
      _ = d2FlowTreeAtPath i (d2FlowCandidateRun d initial t) path :=
        (hpath t).symm
      _ = .node G low high children := hnode
  have haHistory : runActive t ctx.level = true := by
    simpa [runActive, hlevel, d] using ha
  have hrHistory : runRole t ctx.level = .topRise ∨
      runRole t ctx.level = .mid ∨ runRole t ctx.level = .botDesc := by
    simpa [runRole, hlevel, d] using hr
  have hstep := d2FlowTreeRunWithParentOverwrites_child_affine_deficit
    (h := h) (i := ctx.level) (n := t) (G := G) (low := low) (high := high)
    ctx.initial runActive runRole runQuota ctx.overwrite children hnodeHistory
    haHistory hrHistory hcpos hbalance hconserve (by
      simpa [runQuota, hlevel, d] using hpiAlloc) (by
      simpa [runQuota, hlevel, d] using heven) hlow hhigh (by
      simpa [runQuota, hlevel, d] using hprofileCap) hleftReserve hrightReserve
  intro j
  rw [hpath (t + 1)]
  have hj := hstep j
  rw [hchildCap]
  nlinarith [hj]

/-- Ordinary active parents write balanced root data into every child,
independently of the ancestor overwrite history. -/
theorem d2FlowTreeRunWithParentOverwrites_child_balanced
    {h i n G low high : Nat}
    (initial : D2FlowTree (h + 1))
    (active : Nat → Nat → Bool) (role : Nat → Nat → D2Role)
    (quota : Nat → Nat → D2Role → Nat)
    (overwrite : Nat → Nat × Nat × Nat)
    (children : Fin 8 → D2FlowTree h)
    (hnode : d2FlowTreeRunWithParentOverwrites initial i active role quota
      overwrite n = .node G low high children)
    (ha : active n i = true)
    (hr : role n i = .topRise ∨ role n i = .mid ∨ role n i = .botDesc)
    (j : Fin 8) :
    (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowTreeRunWithParentOverwrites initial i active role quota
          overwrite (n + 1)) j)).2.1 +
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowTreeRunWithParentOverwrites initial i active role quota
            overwrite (n + 1)) j)).2.2 =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeRunWithParentOverwrites initial i active role quota
            overwrite (n + 1)) j) := by
  change (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowTreeSetRoot
          (d2FlowStage (active n) (role n) (quota n) (h + 1) i
            (d2FlowTreeRunWithParentOverwrites initial i active role quota
              overwrite n))
          (overwrite n).1 (overwrite n).2.1 (overwrite n).2.2) j)).2.1 +
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowTreeSetRoot
            (d2FlowStage (active n) (role n) (quota n) (h + 1) i
              (d2FlowTreeRunWithParentOverwrites initial i active role quota
                overwrite n))
            (overwrite n).1 (overwrite n).2.1 (overwrite n).2.2) j)).2.2 =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeSetRoot
            (d2FlowStage (active n) (role n) (quota n) (h + 1) i
              (d2FlowTreeRunWithParentOverwrites initial i active role quota
                overwrite n))
            (overwrite n).1 (overwrite n).2.1 (overwrite n).2.2) j)
  rw [d2FlowTreeChild_setRoot]
  rw [hnode]
  exact d2FlowStage_regular_child_balanced children ha hr j

end Chvatal.D2Reserve
