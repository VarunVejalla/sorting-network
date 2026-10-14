import RaggedWireOwnership
import AKS.Chvatal.ExecPlacement
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- Actual wire ownership, with no requirement that counts be uniform at a
given level. This replaces the ownership part of the old `FlowSizes` model. -/
structure RaggedWirePartition (d : Nat) where
  sets : KBag 64 d → Finset (Fin (64 ^ d))
  disjoint : ∀ b c, b ≠ c → Disjoint (sets b) (sets c)
  complete : ∀ w, ∃ b, w ∈ sets b

noncomputable def RaggedWirePartition.initial (d : Nat) : RaggedWirePartition d where
  sets := fun b => if b = KBag.root 64 d then Finset.univ else ∅
  disjoint := by
    intro b c hne
    by_cases hb : b = KBag.root 64 d <;> by_cases hc : c = KBag.root 64 d
    · exact False.elim (hne (hb.trans hc.symm))
    all_goals simp [hb, hc]
  complete := by intro w; exact ⟨KBag.root 64 d, by simp⟩

/-- Routing an actual partition through conserved ragged splits preserves
wire ownership. Numerical capacity invariants are separate obligations. -/
noncomputable def RaggedWirePartition.route {d : Nat} (P : RaggedWirePartition d)
    (splits : ∀ b, RaggedWireSplit (P.sets b))
    (destination : KBag 64 d → Option (Fin 64) → KBag 64 d) : RaggedWirePartition d where
  sets := routeRaggedWires P.sets splits destination
  disjoint := routeRaggedWires_disjoint P.sets splits destination P.disjoint
  complete := routeRaggedWires_complete P.sets splits destination P.complete

/-- Actual global stage execution on an address-dependent ownership sequence.
Its numerical and tree-routing invariants must be established by the scheduler. -/
noncomputable def raggedX {d : Nat} (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) : Nat → Fin (64 ^ d) → Fin (64 ^ d)
  | 0 => v
  | t + 1 => (stageNet (P t).sets (nets t)).exec (raggedX P nets v t)

theorem raggedX_eq_comp_perm {d : Nat} (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) :
    ∀ t, ∃ ρ : Equiv.Perm (Fin (64 ^ d)), raggedX P nets v t = v ∘ ρ
  | 0 => ⟨1, rfl⟩
  | t + 1 => by
      obtain ⟨ρ, hρ⟩ := raggedX_eq_comp_perm P nets v t
      obtain ⟨σ, hσ⟩ := ComparatorNetwork.exec_eq_comp_perm
        (stageNet (P t).sets (nets t)) (raggedX P nets v t)
      refine ⟨ρ * σ, ?_⟩
      change (stageNet (P t).sets (nets t)).exec (raggedX P nets v t) = _
      rw [hσ, hρ]
      rfl

theorem raggedX_injective {d : Nat} (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) : Function.Injective (raggedX P nets v t) := by
  obtain ⟨ρ, hρ⟩ := raggedX_eq_comp_perm P nets v t
  rw [hρ]
  exact v.injective.comp ρ.injective

noncomputable def raggedPlacement {d : Nat} (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) : Placement 64 d where
  regs b := ((P t).sets b).image (raggedX P nets v t)
  disjoint := by
    intro b c hne
    rw [Finset.disjoint_image (raggedX_injective P nets v t)]
    exact (P t).disjoint b c hne
  complete := by
    intro κ
    obtain ⟨w, rfl⟩ := Finite.injective_iff_surjective.mp (raggedX_injective P nets v t) κ
    obtain ⟨b, hb⟩ := (P t).complete w
    exact ⟨b, Finset.mem_image_of_mem _ hb⟩

theorem raggedPlacement_card {d : Nat} (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (b : KBag 64 d) :
    ((raggedPlacement P nets v t).regs b).card = ((P t).sets b).card := by
  exact Finset.card_image_of_injective _ (raggedX_injective P nets v t)

/-- Parallel local networks retain their maximum depth even with unequal
address-dependent register sizes. -/
theorem ragged_stage_depth_le {d D : Nat} (P : RaggedWirePartition d)
    (nets : (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (hD : ∀ b, (nets b (P.sets b).card).depth ≤ D) :
    (stageNet P.sets nets).depth ≤ D := stageNet_depth_le P.sets P.disjoint nets hD

end Tapered945
