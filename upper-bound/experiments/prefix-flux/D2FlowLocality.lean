import D2ScheduleReserve

namespace Chvatal.D2Reserve

/-! Local state observations for the recursive D2 flow.

The root data after one stage depends only on the old root data, the eight
child root deficits, and this node's schedule callback. This is the radius-one
to radius-zero locality step needed when composing a finite-depth profile
through several stages.
-/

def d2FlowStageRootProfile {h : Nat}
    (tree : D2FlowTree (h + 1)) :
    (Nat × Nat × Nat) × (Fin 8 → Nat) :=
  (d2FlowTreeRootData tree,
    fun j => d2FlowTreeRootDeficit (d2FlowTreeChild tree j))

def d2FlowStageRootSecondProfile {h : Nat}
    (tree : D2FlowTree (h + 2)) :
    ((Nat × Nat × Nat) × (Fin 8 → Nat)) ×
      (Fin 8 → ((Nat × Nat × Nat) × (Fin 8 → Nat))) :=
  (d2FlowStageRootProfile tree,
    fun j => d2FlowStageRootProfile (d2FlowTreeChild tree j))

def d2FlowRootDataAfterLocalStage
    (profile : (Nat × Nat × Nat) × (Fin 8 → Nat))
    (isActive : Bool) (r : D2Role) (q : Nat) : Nat × Nat × Nat :=
  let G := profile.1.1
  let low := profile.1.2.1
  let high := profile.1.2.2
  let total := d2FlowTotal profile.2
  if isActive then
    let pi := match r with
      | .topDesc => 0
      | .botRise => total - G
      | _ => q
    (G + pi, low + pi / 2, high + pi - pi / 2)
  else
    profile.1

theorem d2FlowStage_rootData_eq_localResult
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i : Nat}
    (G low high : Nat) (children : Fin 8 → D2FlowTree h) :
    d2FlowTreeRootData
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) =
      d2FlowRootDataAfterLocalStage
        (d2FlowStageRootProfile (.node G low high children))
        (active i) (role i) (quota i (role i)) := by
  cases ha : active i
  · simp [d2FlowRootDataAfterLocalStage, d2FlowStageRootProfile,
      d2FlowStage, d2FlowTreeChild, d2FlowTreeRootData,
      d2FlowTreeRootDeficit, ha]
  · simp [d2FlowRootDataAfterLocalStage, d2FlowStageRootProfile,
      d2FlowStage, d2FlowTreeChild, d2FlowTreeRootData,
      d2FlowTreeRootDeficit, ha]
    exact ⟨rfl, rfl, rfl⟩

/-- Equal radius-one root profiles and equal local callbacks give equal root
data after one recursive stage, even when the two subtrees have different
heights. The descendants only affect this layer through the eight child-root
deficits recorded in the profile. -/
theorem d2FlowStage_rootData_eq_of_rootProfile_eq
    {active₁ active₂ : Nat → Bool}
    {role₁ role₂ : Nat → D2Role}
    {quota₁ quota₂ : Nat → D2Role → Nat}
    {h₁ h₂ i₁ i₂ : Nat}
    (tree₁ : D2FlowTree (h₁ + 1))
    (tree₂ : D2FlowTree (h₂ + 1))
    (hprofile : d2FlowStageRootProfile tree₁ =
      d2FlowStageRootProfile tree₂)
    (hactive : active₁ i₁ = active₂ i₂)
    (hrole : role₁ i₁ = role₂ i₂)
    (hquota : quota₁ i₁ (role₁ i₁) = quota₂ i₂ (role₂ i₂)) :
    d2FlowTreeRootData
      (d2FlowStage active₁ role₁ quota₁ (h₁ + 1) i₁ tree₁) =
    d2FlowTreeRootData
      (d2FlowStage active₂ role₂ quota₂ (h₂ + 1) i₂ tree₂) := by
  cases tree₁ with
  | node G₁ low₁ high₁ children₁ =>
    cases tree₂ with
    | node G₂ low₂ high₂ children₂ =>
      rw [d2FlowStage_rootData_eq_localResult,
        d2FlowStage_rootData_eq_localResult]
      rw [hprofile, hactive, hquota, hrole]

def d2FlowParentCutFromProfile
    (profile : (Nat × Nat × Nat) × (Fin 8 → Nat))
    (r : D2Role) (q : Nat) (j : Fin 8) : Nat :=
  let G := profile.1.1
  let low := profile.1.2.1
  let high := profile.1.2.2
  let sizes := profile.2
  let total := d2FlowTotal sizes
  match r with
  | .topDesc => 0
  | r =>
      let pi := if r = .botRise then total - G else q
      (d2FlowCutChild (d2FlowPosition sizes j) (sizes j)
        (low + pi / 2) (total - high - pi / 2)).1

theorem d2FlowStageParentCutChildDeficit_eq_profile
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (role : Nat → D2Role) (quota : Nat → D2Role → Nat) (j : Fin 8) :
    d2FlowStageParentCutChildDeficit (i := i) (G := G) (low := low)
      (high := high) children role quota j =
    d2FlowParentCutFromProfile
      (d2FlowStageRootProfile (.node G low high children))
      (role i) (quota i (role i)) j := by
  cases hr : role i <;>
    simp [d2FlowStageParentCutChildDeficit, d2FlowParentCutFromProfile,
      d2FlowStageRootProfile, d2FlowTreeChild, d2FlowTreeRootData,
      d2FlowTreeRootDeficit, hr]

/-- One recursive layer of locality: the post-stage root profile
`(root data, eight child deficits)` is determined by the input profile one
level deeper and the schedule callbacks at the root and its children. This
is the inductive step needed to propagate finite-depth observations through
the actual recursive stage, including parent root overwrites. -/
theorem d2FlowStage_rootProfile_eq_of_rootSecondProfile_eq
    {active₁ active₂ : Nat → Bool}
    {role₁ role₂ : Nat → D2Role}
    {quota₁ quota₂ : Nat → D2Role → Nat}
    {h₁ h₂ i₁ i₂ : Nat}
    (tree₁ : D2FlowTree (h₁ + 2))
    (tree₂ : D2FlowTree (h₂ + 2))
    (hprofile : d2FlowStageRootSecondProfile tree₁ =
      d2FlowStageRootSecondProfile tree₂)
    (hactive : active₁ i₁ = active₂ i₂)
    (hrole : role₁ i₁ = role₂ i₂)
    (hquota : quota₁ i₁ (role₁ i₁) = quota₂ i₂ (role₂ i₂))
    (hchildActive : active₁ (i₁ + 1) = active₂ (i₂ + 1))
    (hchildRole : role₁ (i₁ + 1) = role₂ (i₂ + 1))
    (hchildQuota : quota₁ (i₁ + 1) (role₁ (i₁ + 1)) =
      quota₂ (i₂ + 1) (role₂ (i₂ + 1))) :
    d2FlowStageRootProfile
      (d2FlowStage active₁ role₁ quota₁ (h₁ + 2) i₁ tree₁) =
    d2FlowStageRootProfile
      (d2FlowStage active₂ role₂ quota₂ (h₂ + 2) i₂ tree₂) := by
  cases tree₁ with
  | node G₁ low₁ high₁ children₁ =>
    cases tree₂ with
    | node G₂ low₂ high₂ children₂ =>
      have hparentProfile :
          d2FlowStageRootProfile (.node G₁ low₁ high₁ children₁) =
            d2FlowStageRootProfile (.node G₂ low₂ high₂ children₂) := by
        simpa [d2FlowStageRootSecondProfile] using congrArg Prod.fst hprofile
      have hchildrenProfiles :
          (fun j => d2FlowStageRootProfile (children₁ j)) =
            (fun j => d2FlowStageRootProfile (children₂ j)) := by
        simpa [d2FlowStageRootSecondProfile] using congrArg Prod.snd hprofile
      have hrootData := d2FlowStage_rootData_eq_of_rootProfile_eq
        (.node G₁ low₁ high₁ children₁) (.node G₂ low₂ high₂ children₂)
        hparentProfile hactive hrole hquota
      change
        (d2FlowTreeRootData
          (d2FlowStage active₁ role₁ quota₁ (h₁ + 2) i₁
            (.node G₁ low₁ high₁ children₁)),
          fun j => d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowStage active₁ role₁ quota₁ (h₁ + 2) i₁
                (.node G₁ low₁ high₁ children₁)) j)) =
        (d2FlowTreeRootData
          (d2FlowStage active₂ role₂ quota₂ (h₂ + 2) i₂
            (.node G₂ low₂ high₂ children₂)),
          fun j => d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowStage active₂ role₂ quota₂ (h₂ + 2) i₂
                (.node G₂ low₂ high₂ children₂)) j))
      apply Prod.ext
      · exact hrootData
      · funext j
        have hchildProfile :
            d2FlowStageRootProfile (children₁ j) =
              d2FlowStageRootProfile (children₂ j) :=
          congrFun hchildrenProfiles j
        have hchildData := d2FlowStage_rootData_eq_of_rootProfile_eq
          (children₁ j) (children₂ j) hchildProfile
          hchildActive hchildRole hchildQuota
        have hselfDeficitData := congrArg (fun data : Nat × Nat × Nat => data.1)
          hchildData
        have hselfDeficit :
            d2FlowTreeRootDeficit
                (d2FlowStage active₁ role₁ quota₁ (h₁ + 1) (i₁ + 1)
                  (children₁ j)) =
              d2FlowTreeRootDeficit
                (d2FlowStage active₂ role₂ quota₂ (h₂ + 1) (i₂ + 1)
                  (children₂ j)) := by
          simpa only [d2FlowTreeRootData_fst_eq_deficit] using hselfDeficitData
        have hcut :
            d2FlowStageParentCutChildDeficit (i := i₁) (G := G₁)
                (low := low₁) (high := high₁) children₁ role₁ quota₁ j =
              d2FlowStageParentCutChildDeficit (i := i₂) (G := G₂)
                (low := low₂) (high := high₂) children₂ role₂ quota₂ j := by
          have hquota' := hquota
          rw [hrole] at hquota'
          rw [d2FlowStageParentCutChildDeficit_eq_profile,
            d2FlowStageParentCutChildDeficit_eq_profile,
            hparentProfile, hrole, hquota']
        have hrec₁ := d2FlowStage_child_root_parent_recurrence
          (active := active₁) (role := role₁) (quota := quota₁)
          (i := i₁) (G := G₁) (low := low₁) (high := high₁)
          children₁ j
        have hrec₂ := d2FlowStage_child_root_parent_recurrence
          (active := active₂) (role := role₂) (quota := quota₂)
          (i := i₂) (G := G₂) (low := low₂) (high := high₂)
          children₂ j
        change d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowStage active₁ role₁ quota₁ (h₁ + 2) i₁
                (.node G₁ low₁ high₁ children₁)) j) =
          d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowStage active₂ role₂ quota₂ (h₂ + 2) i₂
                (.node G₂ low₂ high₂ children₂)) j)
        rw [hrec₁, hrec₂, hactive, hrole, hselfDeficit, hcut]

/-- The recursive stage is extensional in the callbacks on every level of
the input tree. This lets schedule symmetries transfer a concrete subtree
transition without unfolding the flow arithmetic again. -/
theorem d2FlowStage_eq_of_callbacks_agree
    {active₁ active₂ : Nat → Bool}
    {role₁ role₂ : Nat → D2Role}
    {quota₁ quota₂ : Nat → D2Role → Nat}
    {h i₁ i₂ : Nat} (tree : D2FlowTree h)
    (hactive : ∀ k, k ≤ h → active₁ (i₁ + k) = active₂ (i₂ + k))
    (hrole : ∀ k, k ≤ h → role₁ (i₁ + k) = role₂ (i₂ + k))
    (hquota : ∀ k, k ≤ h → ∀ r,
      quota₁ (i₁ + k) r = quota₂ (i₂ + k) r) :
    d2FlowStage active₁ role₁ quota₁ h i₁ tree =
      d2FlowStage active₂ role₂ quota₂ h i₂ tree := by
  induction tree generalizing i₁ i₂ with
  | leaf G low high => rfl
  | @node h G low high children ih =>
      have hactive0 : active₁ i₁ = active₂ i₂ := by
        simpa using hactive 0 (by omega)
      have hrole0 : role₁ i₁ = role₂ i₂ := by
        simpa using hrole 0 (by omega)
      have hquota0 : ∀ r, quota₁ i₁ r = quota₂ i₂ r := by
        intro r
        simpa using hquota 0 (by omega) r
      have hquotaRole : quota₁ i₁ (role₂ i₂) = quota₂ i₂ (role₂ i₂) := by
        rw [← hrole0]
        exact hquota0 (role₁ i₁)
      have hchildren :
          (fun j => d2FlowStage active₁ role₁ quota₁ h (i₁ + 1)
            (children j)) =
          (fun j => d2FlowStage active₂ role₂ quota₂ h (i₂ + 1)
            (children j)) := by
        funext j
        apply ih j (i₁ := i₁ + 1) (i₂ := i₂ + 1)
        · intro k hk
          have hx := hactive (k + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hx
        · intro k hk
          have hx := hrole (k + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hx
        · intro k hk r
          have hx := hquota (k + 1) (by omega) r
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hx
      have hstageChild (j : Fin 8) :
          d2FlowStage active₁ role₁ quota₁ h (i₁ + 1) (children j) =
            d2FlowStage active₂ role₂ quota₂ h (i₂ + 1) (children j) :=
        congrFun hchildren j
      rw [d2FlowStage, d2FlowStage]
      rw [hactive0]
      cases ha : active₂ i₂
      · simp [ha, hstageChild]
      · simp [ha, hrole0, hquotaRole, hstageChild]

end Chvatal.D2Reserve
