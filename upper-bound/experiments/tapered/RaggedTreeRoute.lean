import RaggedRouteCard
import AKS.Chvatal.StageKernel

namespace Tapered945

open Chvatal

/-- Up ports go to parents; down ports go to their indicated child when that
child exists. The fallback makes the map total at terminal bags. -/
def raggedTreeDestination {d : Nat} (b : KBag 64 d) :
    Option (Fin 64) → KBag 64 d
  | none => b.parent (by norm_num)
  | some j => if h : b.l < d then b.child j.val j.isLt h else b

@[simp] theorem raggedTreeDestination_up {d : Nat} (b : KBag 64 d) :
    raggedTreeDestination b none = b.parent (by norm_num) := rfl

theorem raggedTreeDestination_down {d : Nat} (b : KBag 64 d)
    (j : Fin 64) (h : b.l < d) :
    raggedTreeDestination b (some j) = b.child j.val j.isLt h := by
  simp [raggedTreeDestination, h]

theorem raggedTreeDestination_parent_slot {d : Nat}
    (c : KBag 64 d) (hc : 1 ≤ c.l) (j : Fin 64)
    (hj : j.val = c.x % 64) :
    raggedTreeDestination (c.parent (by norm_num)) (some j) = c := by
  have hparent : (c.parent (by norm_num)).l < d := by
    change c.l - 1 < d
    have hcle : c.l ≤ d := c.hl
    omega
  rw [raggedTreeDestination_down (c.parent (by norm_num)) j hparent]
  have heq := KBag.parent_child c hc (by norm_num)
  have hj' : j = ⟨c.x % 64, Nat.mod_lt _ (by norm_num)⟩ := Fin.ext hj
  rw [hj']
  exact heq

theorem raggedTreeDestination_child_up {d : Nat}
    (c : KBag 64 d) (hcd : c.l < d) (j : Fin 64) :
    raggedTreeDestination (c.child j.val j.isLt hcd) none = c := by
  rw [raggedTreeDestination_up]
  exact KBag.child_parent c j.val j.isLt hcd (by norm_num)

/-- Exact source classification for an ordinary interior address. -/
theorem raggedTreeDestination_eq_iff_incoming {d : Nat}
    (c : KBag 64 d) (hc : 1 ≤ c.l) (hcd : c.l < d)
    (b : KBag 64 d) (p : Option (Fin 64)) :
    raggedTreeDestination b p = c ↔
      (b = c.parent (by norm_num) ∧
        ∃ j : Fin 64, j.val = c.x % 64 ∧ p = some j) ∨
      (p = none ∧ ∃ j : Fin 64, b = c.child j.val j.isLt hcd) := by
  cases p with
  | none =>
      simp only [raggedTreeDestination_up]
      constructor
      · intro h
        have hl : b.l - 1 = c.l := by
          have := congrArg KBag.l h
          simpa [KBag.parent] using this
        have hbpos : 1 ≤ b.l := by omega
        have hparentChild : (b.parent (by norm_num)).child (b.x % 64)
            (Nat.mod_lt _ (by norm_num))
            (by change b.l - 1 < d; omega) = b :=
          KBag.parent_child b hbpos (by norm_num)
            (by change b.l - 1 < d; omega)
        have hparentChild' : c.child (b.x % 64) (Nat.mod_lt _ (by norm_num)) hcd = b := by
          simpa only [h] using hparentChild
        exact Or.inr ⟨trivial, ⟨⟨b.x % 64, Nat.mod_lt _ (by norm_num)⟩,
          hparentChild'.symm⟩⟩
      · rintro (⟨_, _, _, hp⟩ | ⟨_, j, rfl⟩)
        · cases hp
        · exact raggedTreeDestination_child_up c hcd j
  | some k =>
      constructor
      · intro h
        have hb : b.l < d := by
          by_contra hnot
          have heq : b = c := by
            simpa [raggedTreeDestination, hnot] using h
          have := congrArg KBag.l heq
          omega
        have hdown : b.child k.val k.isLt hb = c := by
          simpa [raggedTreeDestination, hb] using h
        have hback := KBag.child_parent b k.val k.isLt hb (by norm_num)
        rw [hdown] at hback
        have hbp : b = c.parent (by norm_num) := hback.symm
        have hindexEq := congrArg KBag.x hbp
        have hslotEq := congrArg KBag.x hdown
        simp only [KBag.parent] at hindexEq
        simp only [KBag.child] at hslotEq
        have hmod := Nat.mod_add_div c.x 64
        have hj : k.val = c.x % 64 := by omega
        exact Or.inl ⟨hbp, ⟨k, hj, rfl⟩⟩
      · rintro (⟨hb, j, hj, hp⟩ | ⟨hp, j, rfl⟩)
        · subst b
          have hkj : k = j := Option.some.inj hp
          subst k
          exact raggedTreeDestination_parent_slot c hc j hj
        · cases hp

/-- Set-level form of the classification: the routed child consists exactly
of its selected parent block and the up-fringes routed by its own children. -/
theorem routeRaggedWires_eq_parent_and_child_up {d : Nat}
    (P : RaggedWirePartition d)
    (splits : ∀ b, RaggedWireSplit (P.sets b))
    (c : KBag 64 d) (hc : 1 ≤ c.l) (hcd : c.l < d) :
    routeRaggedWires P.sets splits raggedTreeDestination c =
      raggedWirePort (splits (c.parent (by norm_num)))
          (some ⟨c.x % 64, Nat.mod_lt _ (by norm_num)⟩) ∪
        (Finset.univ : Finset (Fin 64)).biUnion (fun j =>
          raggedWirePort (splits (c.child j.val j.isLt hcd)) none) := by
  classical
  ext w
  rw [mem_routeRaggedWires]
  constructor
  · rintro ⟨b, p, hd, hw⟩
    rcases (raggedTreeDestination_eq_iff_incoming c hc hcd b p).mp hd with hpar | hchild
    · rcases hpar with ⟨hb, j, hj, hp⟩
      subst b
      subst p
      have hji : j = ⟨c.x % 64, Nat.mod_lt _ (by norm_num)⟩ := Fin.ext hj
      subst j
      exact Finset.mem_union_left _ hw
    · rcases hchild with ⟨hp, j, hb⟩
      subst p
      subst b
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hw⟩)
  · intro hw
    rcases Finset.mem_union.mp hw with hparent | hchildren
    · refine ⟨c.parent (by norm_num),
        some ⟨c.x % 64, Nat.mod_lt _ (by norm_num)⟩,
        raggedTreeDestination_parent_slot c hc _ rfl, hparent⟩
    · obtain ⟨j, hj, hwire⟩ := Finset.mem_biUnion.mp hchildren
      exact ⟨c.child j.val j.isLt hcd, none,
        raggedTreeDestination_child_up c hcd j, hwire⟩

/-- The selected down-port from a parent is physically included in the routed
register of its child. This supplies the ownership premise for aggregating
that parent's slot errors into descendant mass. -/
theorem raggedTreeRoute_parent_port_subset {d : Nat}
    (P : RaggedWirePartition d)
    (splits : ∀ b, RaggedWireSplit (P.sets b))
    (c : KBag 64 d) (hc : 1 ≤ c.l) (hcd : c.l < d) :
    raggedWirePort (splits (c.parent (by norm_num)))
      (some ⟨c.x % 64, Nat.mod_lt _ (by norm_num)⟩) ⊆
        routeRaggedWires P.sets splits raggedTreeDestination c := by
  rw [routeRaggedWires_eq_parent_and_child_up P splits c hc hcd]
  exact Finset.subset_union_left

/-- The selected parent down-port is routed into a child even when the child
is terminal. This direct membership proof avoids classifying the terminal
child's own outgoing ports. -/
theorem raggedTreeRoute_parent_port_subset_all_depth {d : Nat}
    (P : RaggedWirePartition d)
    (splits : ∀ b, RaggedWireSplit (P.sets b))
    (c : KBag 64 d) (hc : 1 ≤ c.l) :
    raggedWirePort (splits (c.parent (by norm_num)))
      (some ⟨c.x % 64, Nat.mod_lt _ (by norm_num)⟩) ⊆
        routeRaggedWires P.sets splits raggedTreeDestination c := by
  intro w hw
  rw [mem_routeRaggedWires]
  refine ⟨c.parent (by norm_num), some ⟨c.x % 64, Nat.mod_lt _ (by norm_num)⟩,
    raggedTreeDestination_parent_slot c hc _ rfl, ?_⟩
  exact hw

/-- Turn the physical tree routing into the register-cover part of a
`PlacementStep`.  The residual port is deliberately defined as the exact
complement of the parent send in the routed register.  At interior nodes it
is precisely the child up-ports (by
`routeRaggedWires_eq_parent_and_child_up`); at terminal nodes it also absorbs
the terminal bag's retained down-ports.  This theorem supplies ownership and
coverage, but makes no numerical claim about that residual. -/
def raggedTreePlacementStep {d : Nat}
    (pl pl' : Placement 64 d) (P : RaggedWirePartition d)
    (splits : ∀ b, RaggedWireSplit (P.sets b))
    (x : Fin (64 ^ d) → Fin (64 ^ d))
    (hplace : ∀ b, pl'.regs b =
      ((P.route splits raggedTreeDestination).sets b).image x) :
    PlacementStep d pl pl' where
  fromParent := fun b _ =>
    (raggedWirePort (splits (b.parent (by norm_num)))
      (some ⟨b.x % 64, Nat.mod_lt _ (by norm_num)⟩)).image x
  fromChildren := fun b hb =>
    pl'.regs b \ (raggedWirePort (splits (b.parent (by norm_num)))
      (some ⟨b.x % 64, Nat.mod_lt _ (by norm_num)⟩)).image x
  hregs := by
    intro b hb
    have hparent : (raggedWirePort (splits (b.parent (by norm_num)))
        (some ⟨b.x % 64, Nat.mod_lt _ (by norm_num)⟩)).image x ⊆ pl'.regs b := by
      rw [hplace]
      apply Finset.image_subset_image
      exact raggedTreeRoute_parent_port_subset_all_depth P splits b hb
    rw [Finset.union_sdiff_of_subset hparent]

/-- The actual routed child size is exactly its parent's selected width plus
the up-widths of all its children. This is the exact ordinary-node count
recurrence, now stated for the physical wire partition. -/
theorem routeRaggedWires_card_eq_tree_recurrence {d : Nat}
    (P : RaggedWirePartition d)
    (splits : ∀ b, RaggedWireSplit (P.sets b))
    (c : KBag 64 d) (hc : 1 ≤ c.l) (hcd : c.l < d) :
    (routeRaggedWires P.sets splits raggedTreeDestination c).card =
      (splits (c.parent (by norm_num))).widths (c.x % 64) +
        ∑ j : Fin 64, (splits (c.child j.val j.isLt hcd)).up := by
  classical
  rw [routeRaggedWires_eq_parent_and_child_up P splits c hc hcd]
  let p := raggedWirePort (splits (c.parent (by norm_num)))
    (some ⟨c.x % 64, Nat.mod_lt _ (by norm_num)⟩)
  let q := fun j : Fin 64 => raggedWirePort (splits (c.child j.val j.isLt hcd)) none
  have hdisj : Disjoint p ((Finset.univ : Finset (Fin 64)).biUnion q) := by
    rw [Finset.disjoint_left]
    intro w hp hq
    obtain ⟨j, hj, hqj⟩ := Finset.mem_biUnion.mp hq
    apply Finset.disjoint_left.mp
      (Finset.disjoint_of_subset_left (raggedWirePort_subset _ _)
        (Finset.disjoint_of_subset_right (raggedWirePort_subset _ _)
          (P.disjoint _ _ (by
            intro heq
            have hl := congrArg KBag.l heq
            simp [KBag.parent, KBag.child] at hl)))) hp hqj
  have hpair : ((Finset.univ : Finset (Fin 64)) : Set (Fin 64)).PairwiseDisjoint q := by
    intro i hi j hj hij
    apply Finset.disjoint_of_subset_left (raggedWirePort_subset _ _)
    apply Finset.disjoint_of_subset_right (raggedWirePort_subset _ _)
    apply P.disjoint
    intro heq
    apply hij
    apply Fin.ext
    have hx := congrArg KBag.x heq
    simp [KBag.child] at hx
    omega
  have hcardUnion := Finset.card_union_of_disjoint hdisj
  have hcardBi := Finset.card_biUnion hpair
  change (p ∪ (Finset.univ : Finset (Fin 64)).biUnion q).card = _
  rw [hcardUnion, hcardBi]
  simp [p, q, raggedWirePort_card]

/-- Route-cardinality formula for the canonical tree map. -/
theorem raggedTreeRoute_card_eq_port_sum {d : Nat}
    (P : RaggedWirePartition d)
    (splits : ∀ b, RaggedWireSplit (P.sets b)) (target : KBag 64 d) :
    ((P.route splits raggedTreeDestination).sets target).card =
      ∑ x ∈ (Finset.univ : Finset (KBag 64 d × Option (Fin 64))).filter
        (fun x => raggedTreeDestination x.1 x.2 = target),
          (raggedWirePort (splits x.1) x.2).card := by
  exact P.route_card_eq_port_sum splits raggedTreeDestination target

end Tapered945
