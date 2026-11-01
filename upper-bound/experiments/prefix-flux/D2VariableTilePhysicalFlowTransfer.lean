import D2PhysicalFlowProfileTransfer
import D2FlowRankBridge
import D2CutAlignment
import D2StaticWireSets

open scoped BigOperators

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace Chvatal.D2VariableTilePhysicalFlowTransfer

open Chvatal.D2RankAlignment
open Chvatal.D2ClippedFlowProfileTransfer
open Chvatal.D2PhysicalFlowProfileTransfer
open Chvatal.D2Reserve
open Chvatal.D2ColumnRebatchBridge
open Chvatal.D2PhysicalProfileMass
open Chvatal.D2ReflectedPhysicalPack
open Chvatal.D2BandRepair4096Network
open Chvatal.D2StaticWireSets

abbrev Col := Fin 64

private theorem countDistance_rat_eq_abs_local (a b : Nat) :
    (countDistance a b : Rat) = abs ((a : Rat) - (b : Rat)) := by
  by_cases hab : a <= b
  · unfold countDistance
    rw [Nat.sub_eq_zero_of_le hab]
    have hsub : ((b - a : Nat) : Rat) = (b : Rat) - (a : Rat) := Nat.cast_sub hab
    push_cast
    rw [hsub]
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hab))]
    ring
  · have hba : b <= a := Nat.le_of_not_ge hab
    unfold countDistance
    rw [Nat.sub_eq_zero_of_le hba]
    have hsub : ((a - b : Nat) : Rat) = (a : Rat) - (b : Rat) := Nat.cast_sub hba
    push_cast
    rw [hsub]
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hba))]
    ring

private theorem nat_dvd_sub_of_dvd_of_le {m a b : Nat}
    (ha : m ∣ a) (hb : m ∣ b) (hle : b <= a) : m ∣ a - b := by
  rcases ha with ⟨x, rfl⟩
  rcases hb with ⟨y, rfl⟩
  by_cases hm : m = 0
  · subst m
    simp at hle ⊢
  · have hyx : y <= x := Nat.le_of_mul_le_mul_left hle (Nat.pos_of_ne_zero hm)
    refine ⟨x - y, ?_⟩
    rw [Nat.mul_sub_left_distrib]

/-- Both clipped fronts preserve any common divisibility grid across a child
interval. This is the arithmetic core of the 4096-cell alignment invariant. -/
theorem d2FlowCutChild_preserves_divisibility_grid
    (m pos size left right : Nat)
    (hpos : m ∣ pos) (hsize : m ∣ size)
    (hleft : m ∣ left) (hright : m ∣ right) :
    m ∣ (d2FlowCutChild pos size left right).1 /\
    m ∣ (d2FlowCutChild pos size left right).2.1 /\
    m ∣ (d2FlowCutChild pos size left right).2.2 := by
  have hsum : m ∣ pos + size := dvd_add hpos hsize
  have hleftMin : m ∣ min (pos + size) left := by
    by_cases hle : pos + size <= left
    · rw [Nat.min_eq_left hle]
      exact hsum
    · rw [Nat.min_eq_right (by omega : left <= pos + size)]
      exact hleft
  have hleftCut : m ∣ d2LeftCut pos size left := by
    by_cases hle : pos <= left
    · have hposMin : pos <= min (pos + size) left :=
        (Nat.le_min).2 ⟨by omega, hle⟩
      exact nat_dvd_sub_of_dvd_of_le hleftMin hpos hposMin
    · have heq : min (pos + size) left = left :=
        Nat.min_eq_right (by omega)
      unfold d2LeftCut
      rw [heq]
      simp [Nat.sub_eq_zero_of_le (by omega : left <= pos)]
  have hrightMax : m ∣ max pos right := by
    by_cases hle : pos <= right
    · rw [Nat.max_eq_right hle]
      exact hright
    · rw [Nat.max_eq_left (by omega : right <= pos)]
      exact hpos
  have hrightCut : m ∣ d2RightCut pos size right := by
    by_cases hle : max pos right <= pos + size
    · exact nat_dvd_sub_of_dvd_of_le hsum hrightMax hle
    · unfold d2RightCut
      simp [Nat.sub_eq_zero_of_le (le_of_not_ge hle)]
  refine ⟨?_, hleftCut, hrightCut⟩
  dsimp [d2FlowCutChild]
  exact dvd_add hleftCut hrightCut

theorem d2FlowRankBoundary_dvd_of_widths
    (m : Nat) (widths : Fin 8 -> Nat)
    (hwidth : forall j, m ∣ widths j) :
    forall i, i <= 8 -> m ∣ d2FlowRankBoundary widths i := by
  intro i
  induction i with
  | zero =>
      intro _
      rw [d2FlowRankBoundary_zero]
      exact dvd_zero m
  | succ i ih =>
      intro hi
      have hilt : i < 8 := by omega
      rw [d2FlowRankBoundary_succ widths i hilt]
      exact dvd_add (ih (by omega)) (hwidth ⟨i, hilt⟩)

/-- Ten ordered ports for one ordinary D2 sender: its left parent half,
eight child intervals, and its right parent half. -/
def d2SenderPortBoundaryNat (pi senderCard : Nat) (widths : Fin 8 -> Nat)
    (i : Nat) : Nat :=
  if i = 0 then 0
  else if i = 10 then senderCard
  else pi / 2 + d2FlowRankBoundary widths (i - 1)

def d2SenderPortBoundary (pi senderCard : Nat) (widths : Fin 8 -> Nat)
    (i : Fin 11) : Nat :=
  d2SenderPortBoundaryNat pi senderCard widths i.val

/-- If the quota half, every child width, and sender endpoint are on the
same grid, then all ten cumulative sender-port boundaries are on that grid. -/
theorem d2SenderPortBoundaryNat_dvd_of_parts
    (m pi senderCard : Nat) (widths : Fin 8 -> Nat)
    (hhalf : m ∣ pi / 2)
    (hwidth : forall j, m ∣ widths j)
    (hcard : m ∣ senderCard) :
    forall i, i <= 10 -> m ∣ d2SenderPortBoundaryNat pi senderCard widths i := by
  have hflow i (hi : i <= 8) : m ∣ d2FlowRankBoundary widths i :=
    d2FlowRankBoundary_dvd_of_widths m widths hwidth i hi
  intro i hi
  by_cases hzero : i = 0
  · simp [d2SenderPortBoundaryNat, hzero]
  · by_cases hlast : i = 10
    · simp [d2SenderPortBoundaryNat, hlast]
      exact hcard
    · have hindex : i - 1 <= 8 := by omega
      simp [d2SenderPortBoundaryNat, hzero, hlast]
      exact dvd_add hhalf (hflow (i - 1) hindex)

/-- Stage form of the grid lemma. If the parent deficit and every old/new
child deficit are multiples of `m`, and the quota half is aligned, the
actual ordinary sender's ten rank-port boundaries are all multiples of `m`.
The stage hypotheses supply monotonicity of each child deficit. -/
theorem d2FlowStage_regular_sender_boundary_dvd
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h i G low high m : Nat}
    (children : Fin 8 -> D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise \/ role i = .mid \/ role i = .botDesc)
    (hcuts : low + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2)
    (hG : m ∣ G)
    (hhalf : m ∣ quota i (role i) / 2)
    (hold : forall j, m ∣ d2FlowTreeRootDeficit (children j))
    (hpost : forall j, m ∣ d2FlowTreeRootDeficit
      (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) j))
    (hGle : G <= d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j))) :
    forall p, p <= 10 ->
      m ∣ d2SenderPortBoundaryNat (quota i (role i))
        (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G)
        (fun j => d2FlowTreeRootDeficit (children j) -
          d2FlowTreeRootDeficit
            (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)) p := by
  let sizes : Fin 8 -> Nat := fun j => d2FlowTreeRootDeficit (children j)
  let post : Fin 8 -> Nat := fun j => d2FlowTreeRootDeficit
    (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
      (.node G low high children)) j)
  let widths : Fin 8 -> Nat := fun j => sizes j - post j
  have htotal : m ∣ d2FlowTotal sizes := by
    unfold d2FlowTotal
    apply Finset.dvd_sum
    intro j hj
    exact hold j
  have hcard : m ∣ d2FlowTotal sizes - G :=
    nat_dvd_sub_of_dvd_of_le htotal hG hGle
  have hpostLe (j : Fin 8) : post j <= sizes j := by
    dsimp [post, sizes]
    rw [d2FlowStage_regular_child_deficit children ha hr j]
    exact d2FlowCutChild_le_native (Nat.le_refl _) (by
      omega)
  have hwidth (j : Fin 8) : m ∣ widths j := by
    exact nat_dvd_sub_of_dvd_of_le (hold j) (hpost j) (hpostLe j)
  intro p hp
  exact d2SenderPortBoundaryNat_dvd_of_parts m (quota i (role i))
    (d2FlowTotal sizes - G) widths hhalf hwidth hcard p hp

/-- A concrete aligned D2 stage reduces the sender-port grid claim to the
schedule's quota divisibility, aligned child outputs, and ordinary
cut-validity inequalities. The candidate schedule supplies the stronger
8192-divisibility of its active ordinary quota; its coupled stage invariant
can supply the child-output alignment premise. -/
theorem d2FlowStage_regular_sender_boundary_dvd_of_aligned
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h i G low high : Nat}
    (children : Fin 8 -> D2FlowTree h)
    (htile : d2FlowTileAligned (.node G low high children))
    (hpostTile : forall j, d2FlowTileAligned
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j))
    (ha : active i = true)
    (hr : role i = .topRise \/ role i = .mid \/ role i = .botDesc)
    (hquota : 8192 ∣ quota i (role i))
    (hcuts : low + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2)
    (hGle : G <= d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j))) :
    forall p, p <= 10 ->
      4096 ∣ d2SenderPortBoundaryNat (quota i (role i))
        (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G)
        (fun j => d2FlowTreeRootDeficit (children j) -
          d2FlowTreeRootDeficit
            (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)) p := by
  have hhalf : 4096 ∣ quota i (role i) / 2 := by
    rcases hquota with ⟨k, hk⟩
    rw [hk]
    refine ⟨k, ?_⟩
    omega
  apply d2FlowStage_regular_sender_boundary_dvd children ha hr hcuts
  · exact htile.1
  · exact hhalf
  · intro j
    exact d2FlowTileAligned_root_dvd (children j) (htile.2.2.2 j)
  · intro j
    exact d2FlowTileAligned_root_dvd _ (hpostTile j)
  · exact hGle

/-- A row-aligned recursive tree exposes row-aligned immediate children. -/
theorem d2FlowTileAligned_children {h : Nat} (tree : D2FlowTree (h + 1))
    (htile : d2FlowTileAligned tree) :
    forall j, d2FlowTileAligned (d2FlowTreeChild tree j) := by
  cases tree with
  | node G low high children =>
      rcases htile with ⟨_, _, _, hchildren⟩
      exact hchildren

/-- Port-grid conclusion at every node of a recursive stage, with the same
tree shape as the flow recursion. Inactive and nonordinary nodes contribute
no sender-boundary obligation. -/
def d2FlowStagePortGrid (m : Nat) (active : Nat -> Bool)
    (role : Nat -> D2Role) (quota : Nat -> D2Role -> Nat) :
    {h : Nat} -> Nat -> D2FlowTree h -> Prop
  | 0, _, .leaf _ _ _ => True
  | h + 1, i, .node G low high children =>
      (active i = true -> d2OrdinaryRole (role i) ->
        forall p, p <= 10 ->
          m ∣ d2SenderPortBoundaryNat (quota i (role i))
            (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G)
            (fun j => d2FlowTreeRootDeficit (children j) -
              d2FlowTreeRootDeficit
                (d2FlowTreeChild
                  (d2FlowStage active role quota (h + 1) i
                    (.node G low high children)) j)) p) /\
      forall j, d2FlowStagePortGrid m active role quota (i + 1)
        (children j)

theorem d2FlowStagePortGrid_atPath
    {m : Nat} {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h n i : Nat}
    (tree : D2FlowTree (h + n)) (path : D2FlowPath n)
    (hgrid : d2FlowStagePortGrid m active role quota i tree) :
    d2FlowStagePortGrid m active role quota (i + n)
      (d2FlowTreeAtPath n tree path) := by
  induction path generalizing h i with
  | nil => simpa [d2FlowTreeAtPath] using hgrid
  | @cons n j tail ih =>
      cases tree with
      | node G low high children =>
          simp only [d2FlowStagePortGrid] at hgrid
          have hchild := ih (h := h) (i := i + 1)
            (tree := children j) (hgrid.2 j)
          simpa [d2FlowTreeAtPath, show i + 1 + n = i + (n + 1) by omega]
            using hchild

/-- The existing recursive stage-input contract exposes exactly the local
balance, quota-reserve, and parity facts needed to prove the two sender fronts
are disjoint. -/
theorem d2FlowStageInvInputs_regular_root_data
    {scale h i G low high : Nat} {active : Nat -> Bool}
    {role : Nat -> D2Role} {quota : Nat -> D2Role -> Nat}
    {cap : Nat -> Nat}
    (children : Fin 8 -> D2FlowTree h)
    (hinputs : d2FlowStageInvInputs scale active role quota cap i
      (.node G low high children))
    (ha : active i = true)
    (hr : d2OrdinaryRole (role i)) :
    low + high = G /\
      quota i (role i) <=
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G /\
      quota i (role i) % 2 = 0 := by
  rcases hinputs with ⟨_, hlocal⟩
  simp only [ha] at hlocal
  rcases hlocal with ⟨hbalance, hroleInput⟩
  rcases hr with htop | hmid | hbot
  · simp only [htop] at hroleInput
    rcases hroleInput with ⟨_, _, hreserve, heven, _, _⟩
    exact ⟨hbalance, by simpa [htop] using hreserve,
      by simpa [htop] using heven⟩
  · simp only [hmid] at hroleInput
    rcases hroleInput with ⟨_, _, hreserve, heven, _, _⟩
    exact ⟨hbalance, by simpa [hmid] using hreserve,
      by simpa [hmid] using heven⟩
  · simp only [hbot] at hroleInput
    rcases hroleInput with ⟨_, _, hreserve, heven, _, _⟩
    exact ⟨hbalance, by simpa [hbot] using hreserve,
      by simpa [hbot] using heven⟩

/-- With the candidate's recursive reserve inputs and the coupled grid
invariant, every active ordinary sender at every recursive level has all of
its rank-port boundaries on the physical 4096 grid. -/
theorem d2FlowStage_sender_boundary_dvd_all
    {h i : Nat} {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat}
    (tree : D2FlowTree h)
    (htile : d2FlowTileAligned tree)
    (hinv : d2FlowTreeInv 8192 tree)
    (hcontract : d2FlowStageTileContract active role quota (h := h) i tree)
    (hinputs : d2FlowStageInvInputs 8192 active role quota cap i tree)
    (hquotaGrid : forall k, active k = true -> d2OrdinaryRole (role k) ->
      8192 ∣ quota k (role k)) :
    d2FlowStagePortGrid 4096 active role quota i tree := by
  induction tree generalizing i with
  | leaf G low high =>
      simp [d2FlowStagePortGrid]
  | @node h G low high children ih =>
      change (active i = true -> d2OrdinaryRole (role i) ->
        forall p, p <= 10 ->
          4096 ∣ d2SenderPortBoundaryNat (quota i (role i))
            (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G)
            (fun j => d2FlowTreeRootDeficit (children j) -
              d2FlowTreeRootDeficit
                (d2FlowTreeChild
                  (d2FlowStage active role quota (h + 1) i
                    (.node G low high children)) j)) p) /\
        forall j, d2FlowStagePortGrid 4096 active role quota (i + 1)
          (children j)
      have hrootInputs := hinputs
      have hrootTile := htile
      have hpost := d2FlowStage_preserves_tileAligned i
        (.node G low high children) hcontract htile
      have hpostChildren := d2FlowTileAligned_children
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) hpost
      rcases htile with ⟨_, _, _, htileChildren⟩
      rcases hinv with ⟨_, hGle, _, hinvChildren⟩
      rcases hcontract with ⟨hcontractChildren, _, _⟩
      rcases hinputs with ⟨hinputChildren, _⟩
      constructor
      · intro ha hr
        have hdata := d2FlowStageInvInputs_regular_root_data children
          hrootInputs ha hr
        rcases hdata with ⟨hbalance, hreserve, heven⟩
        have hquota := hquotaGrid i ha hr
        have hreserve' := hreserve
        simp only [d2FlowTotal] at hreserve'
        have htotal : G + quota i (role i) <=
            (Finset.univ.sum fun j => d2FlowTreeRootDeficit (children j)) := by
          omega
        have hquotaHalf : quota i (role i) = 2 * (quota i (role i) / 2) := by
          omega
        have hcuts' : low + quota i (role i) / 2 <=
          (Finset.univ.sum fun j => d2FlowTreeRootDeficit (children j)) -
            high - quota i (role i) / 2 := by
          rw [hquotaHalf, ← hbalance] at htotal
          omega
        have hcuts : low + quota i (role i) / 2 <=
          d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
            high - quota i (role i) / 2 := by
          simpa [d2FlowTotal] using hcuts'
        exact d2FlowStage_regular_sender_boundary_dvd_of_aligned
          children hrootTile hpostChildren ha hr hquota hcuts hGle
      · intro j
        exact ih j (i := i + 1) (htileChildren j) (hinvChildren j)
          (hcontractChildren j) (hinputChildren j)

/-- At the actual candidate root, the all-stage alignment induction supplies
the old and new child-grid facts needed by the sender-boundary theorem. The
remaining cut-validity hypotheses are stated explicitly, since they are also
needed for the physical flow conservation argument. -/
theorem d2FlowCandidateRun_root_sender_boundary_dvd
    {h t G low high : Nat} (hd : 7 <= h + 1) (ht : 0 < t)
    {children : Fin 8 -> D2FlowTree h}
    (hnode : d2FlowCandidateRun (h + 1) (d2FlowTreeInitial 8192 (h + 1)) t =
      .node G low high children)
    (ha : d2FlowCandidateActive (h + 1) t 0 = true)
    (hr : d2OrdinaryRole (d2FlowCandidateRole (h + 1) t 0))
    (hinv : d2FlowTreeInv 8192
      (d2FlowCandidateRun (h + 1) (d2FlowTreeInitial 8192 (h + 1)) t))
    (hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 1) t)
      (d2FlowCandidateRole (h + 1) t)
      (d2FlowCandidateQuota (h + 1) t)
      (fun k => d2FlowCandidateCapacity (h + 1) k t) 0
      (d2FlowCandidateRun (h + 1) (d2FlowTreeInitial 8192 (h + 1)) t)) :
    forall p, p <= 10 ->
      4096 ∣ d2SenderPortBoundaryNat
        (d2FlowCandidateQuota (h + 1) t 0
          (d2FlowCandidateRole (h + 1) t 0))
        (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G)
        (fun j => d2FlowTreeRootDeficit (children j) -
          d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowCandidateRun (h + 1)
                (d2FlowTreeInitial 8192 (h + 1)) (t + 1)) j)) p := by
  have hbefore : d2FlowTileAligned
      (d2FlowCandidateRun (h + 1) (d2FlowTreeInitial 8192 (h + 1)) t) := by
    rcases d2FlowCandidateRun_alignment_all hd t (by omega) with ⟨ha', _, _⟩
    exact ha'
  have hafter : d2FlowTileAligned
      (d2FlowCandidateRun (h + 1)
        (d2FlowTreeInitial 8192 (h + 1)) (t + 1)) := by
    rcases d2FlowCandidateRun_alignment_all hd (t + 1) (by omega) with
      ⟨ha', _, _⟩
    exact ha'
  have hpostTile := d2FlowTileAligned_children
    (d2FlowCandidateRun (h + 1)
      (d2FlowTreeInitial 8192 (h + 1)) (t + 1)) hafter
  have hpostTile' : forall j, d2FlowTileAligned
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive (h + 1) t)
          (d2FlowCandidateRole (h + 1) t)
          (d2FlowCandidateQuota (h + 1) t) (h + 1) 0
          (.node G low high children)) j) := by
    intro j
    simpa [d2FlowCandidateRun, d2FlowCandidateStage, hnode] using
      hpostTile j
  have hquota : 8192 ∣ d2FlowCandidateQuota (h + 1) t 0
      (d2FlowCandidateRole (h + 1) t 0) :=
    d2FlowCandidateQuota_dvd_8192 hd ht ha hr
  have hinvNode : d2FlowTreeInv 8192 (.node G low high children) := by
    simpa [hnode] using hinv
  have hGle : G <= d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) := by
    have hinv' := hinvNode
    simp only [d2FlowTreeInv] at hinv'
    exact hinv'.2.1
  have hinpNode := hinputs
  rw [hnode] at hinpNode
  rcases hinpNode with ⟨_, hlocal⟩
  simp only [ha] at hlocal
  rcases hlocal with ⟨hbalance, hroleInput⟩
  have hspec :
      512 * G <= d2FlowCandidateCapacity (h + 1) 0 t /\
      256 * d2FlowCandidateQuota (h + 1) t 0
        (d2FlowCandidateRole (h + 1) t 0) <=
          d2FlowCandidateCapacity (h + 1) 0 t /\
      d2FlowCandidateQuota (h + 1) t 0
        (d2FlowCandidateRole (h + 1) t 0) <=
          d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G /\
      d2FlowCandidateQuota (h + 1) t 0
        (d2FlowCandidateRole (h + 1) t 0) % 2 = 0 /\
      d2FlowCandidateCapacity (h + 1) 0 t <=
        128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩) /\
      d2FlowCandidateCapacity (h + 1) 0 t <=
        128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩) := by
    rcases hr with htop | hmid | hbot
    · simpa [htop] using hroleInput
    · simpa [hmid] using hroleInput
    · simpa [hbot] using hroleInput
  have hquotaReserve : d2FlowCandidateQuota (h + 1) t 0
      (d2FlowCandidateRole (h + 1) t 0) <=
    d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
    exact hspec.2.2.1
  have heven : d2FlowCandidateQuota (h + 1) t 0
      (d2FlowCandidateRole (h + 1) t 0) % 2 = 0 := by
    exact hspec.2.2.2.1
  have hcuts : low + d2FlowCandidateQuota (h + 1) t 0
      (d2FlowCandidateRole (h + 1) t 0) / 2 <=
    d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - high -
      d2FlowCandidateQuota (h + 1) t 0
        (d2FlowCandidateRole (h + 1) t 0) / 2 := by
    omega
  have hresult := d2FlowStage_regular_sender_boundary_dvd_of_aligned
    (active := d2FlowCandidateActive (h + 1) t)
    (role := d2FlowCandidateRole (h + 1) t)
    (quota := d2FlowCandidateQuota (h + 1) t)
    (children := children) (by simpa [hnode] using hbefore) hpostTile'
    ha (by simpa [d2OrdinaryRole] using hr) hquota hcuts hGle
  simpa [d2FlowCandidateRun, d2FlowCandidateStage, hnode] using hresult

/-- Candidate-level all-sender form. The independently proved scheduler
alignment results supply the tile and front contracts at every stage; only
the recursive saturated-aware invariant and its exact stage-input reserves
remain as hypotheses. -/
theorem d2FlowCandidateRun_sender_boundary_grid_of_invariants
    {d t : Nat} (hd : 7 <= d)
    (hinv : d2FlowTreeInv 8192
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t))
    (hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
      (d2FlowCandidateQuota d t)
      (fun k => d2FlowCandidateCapacity d k t) 0
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)) :
    d2FlowStagePortGrid 4096 (d2FlowCandidateActive d t)
      (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t) 0
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) := by
  have htile : d2FlowTileAligned
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) := by
    by_cases ht0 : t = 0
    · subst t
      exact d2FlowTreeInitial_tileAligned 8192 d ⟨2, rfl⟩
    · have htpos : 1 <= t := by omega
      rcases d2FlowCandidateRun_alignment_all hd t htpos with ⟨h, _, _⟩
      exact h
  have hfronts := d2FlowCandidateRun_frontContract_all hd
  have hfront := hfronts t
  have hcontract := d2FlowStageFrontContract_to_tileContract hd
    0 (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) hfront
  have hquotaGrid : forall k, d2FlowCandidateActive d t k = true ->
      d2OrdinaryRole (d2FlowCandidateRole d t k) ->
      8192 ∣ d2FlowCandidateQuota d t k (d2FlowCandidateRole d t k) := by
    intro k ha hr
    by_cases ht0 : t = 0
    · subst t
      have hk : k = 0 := by
        simpa [d2FlowCandidateActive] using ha
      subst k
      have hf : False := by
        simpa [d2FlowCandidateRole, d2OrdinaryRole] using hr
      exact hf.elim
    · exact d2FlowCandidateQuota_dvd_8192 hd (by omega) ha hr
  exact d2FlowStage_sender_boundary_dvd_all
    (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)
    htile hinv hcontract hinputs hquotaGrid

/-- One universal stage-input provider suffices to certify every candidate
run state and, consequently, every active sender's physical-grid port
boundaries for all time. This isolates the remaining arithmetic schedule gate
from the already-proved alignment and flow-tree induction. -/
theorem d2FlowCandidateRun_sender_boundary_grid_of_all_stage_inputs
    {d : Nat} (hd : 7 <= d)
    (hinputs : forall t, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
      (d2FlowCandidateQuota d t)
      (fun k => d2FlowCandidateCapacity d k t) 0
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)) :
    forall t, d2FlowStagePortGrid 4096 (d2FlowCandidateActive d t)
      (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t) 0
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) := by
  have hinv : forall t, d2FlowTreeInv 8192
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) := by
    intro t
    induction t with
    | zero =>
        simpa [d2FlowCandidateRun] using d2FlowTreeInitial_inv 8192 d
    | succ t ih =>
        have hpres := d2FlowStage_preserves_inv_of_inputs
          (active := d2FlowCandidateActive d t)
          (role := d2FlowCandidateRole d t)
          (quota := d2FlowCandidateQuota d t)
          (cap := fun k => d2FlowCandidateCapacity d k t)
          (i := 0) (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)
          ih (hinputs t)
        simpa [d2FlowCandidateRun, d2FlowCandidateStage] using hpres
  intro t
  exact d2FlowCandidateRun_sender_boundary_grid_of_invariants hd
    (hinv t) (hinputs t)

theorem d2SenderPortBoundaryNat_mono
    (pi senderCard : Nat) (widths : Fin 8 -> Nat)
    (heven : pi % 2 = 0)
    (hconserve : pi + d2FlowTotal widths = senderCard)
    {i : Nat} (hi : i < 10) :
    d2SenderPortBoundaryNat pi senderCard widths i <=
      d2SenderPortBoundaryNat pi senderCard widths (i + 1) := by
  have hpi : pi = 2 * (pi / 2) := by omega
  by_cases hzero : i = 0
  · simp [d2SenderPortBoundaryNat, hzero, d2FlowRankBoundary_zero]
  · by_cases hlast : i = 9
    · simp [d2SenderPortBoundaryNat, hzero, hlast, d2FlowRankBoundary_end]
      omega

    · have hmid : 1 <= i /\ i < 9 := by omega
      have hbound := d2FlowRankBoundary_mono widths (i - 1) (by omega)
      have hidx : i - 1 + 1 = i := by omega
      rw [hidx] at hbound
      simp only [d2SenderPortBoundaryNat,
        if_neg hzero, if_neg (by omega : i ≠ 10),
        if_neg (by omega : i + 1 ≠ 0),
        if_neg (by omega : i + 1 ≠ 10)]
      exact Nat.add_le_add_left hbound (pi / 2)

private theorem nat_dvd_mul_left_of_dvd {m a b : Nat} (hb : m ∣ b) :
    m ∣ a * b := by
  rcases hb with ⟨k, hk⟩
  refine ⟨a * k, ?_⟩
  rw [hk]
  ring

private theorem nat_dvd_trunc_sub_of_dvd {m a b : Nat}
    (ha : m ∣ a) (hb : m ∣ b) : m ∣ a - b := by
  by_cases hba : b <= a
  · exact nat_dvd_sub_of_dvd_of_le ha hb hba
  · simp [Nat.sub_eq_zero_of_le (le_of_not_ge hba)]

/-- Static child-hole endpoints stay on a common address grid when the parent
origin, child width, exposed fronts, and recursive child fronts are aligned.
This is the endpoint arithmetic needed to turn aligned flow cuts into actual
whole-column receiver pieces. -/
theorem d2EightChildHole_endpoints_dvd
    {m base width left right : Nat}
    (deficit low high : Fin 8 → Nat)
    (hbase : m ∣ base) (hwidth : m ∣ width)
    (hleft : m ∣ left) (hright : m ∣ right)
    (hlow : ∀ j, m ∣ low j) (hhigh : ∀ j, m ∣ high j)
    (j : Fin 8) :
    m ∣ (d2EightChildHole base width left right deficit low high j).1 ∧
      m ∣ (d2EightChildHole base width left right deficit low high j).2 := by
  by_cases hsat : deficit j = width
  · by_cases hj0 : j.val = 0
    · have haddr : m ∣ base + left := dvd_add hbase hleft
      simp [d2EightChildHole, hsat, hj0, haddr]
    · by_cases hj7 : j.val = 7
      · have h8width : m ∣ 8 * width := nat_dvd_mul_left_of_dvd hwidth
        have haddr : m ∣ base + 8 * width - right :=
          nat_dvd_trunc_sub_of_dvd (dvd_add hbase h8width) hright
        simp [d2EightChildHole, hsat, hj0, hj7, haddr]
      · have hmj : m ∣ j.val * width := nat_dvd_mul_left_of_dvd hwidth
        have haddr : m ∣ base + j.val * width := dvd_add hbase hmj
        simp [d2EightChildHole, hsat, hj0, hj7, haddr]
  · have hmj : m ∣ j.val * width := nat_dvd_mul_left_of_dvd hwidth
    have hmj1 : m ∣ (j.val + 1) * width :=
      nat_dvd_mul_left_of_dvd hwidth
    have hloAddr : m ∣ base + j.val * width + low j :=
      dvd_add (dvd_add hbase hmj) (hlow j)
    have hhiAddr : m ∣ base + (j.val + 1) * width - high j :=
      nat_dvd_trunc_sub_of_dvd (dvd_add hbase hmj1) (hhigh j)
    simp [d2EightChildHole, hsat, hloAddr, hhiAddr]

/-- Every interval in the static hole list inherits endpoint divisibility from
its generating endpoint functions. -/
theorem staticHoleList_endpoints_dvd {m count : Nat}
    (lo hi : Fin count → Nat)
    (hlo : ∀ j, m ∣ lo j) (hhi : ∀ j, m ∣ hi j) :
    ∀ hole, hole ∈ staticHoleList count lo hi ->
      m ∣ hole.1 ∧ m ∣ hole.2 := by
  induction count with
  | zero =>
      intro hole hmem
      simp [staticHoleList] at hmem
  | succ count ih =>
      intro hole hmem
      simp only [staticHoleList, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · cases hhead
        exact ⟨hlo ⟨0, by omega⟩, hhi ⟨0, by omega⟩⟩
      · exact ih (fun j => lo j.succ) (fun j => hi j.succ)
          (fun j => hlo j.succ) (fun j => hhi j.succ) hole htail

/-- An ordinary aligned D2 sender creates only 4096-aligned static child
holes. This connects the flow stage's actual clipped child fronts to the
physical address intervals used by the sender scheduler. -/
theorem d2FlowStage_ordinary_staticHoleList_endpoints_dvd
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat}
    {h i G low high base width : Nat}
    (children : Fin 8 -> D2FlowTree h)
    (ha : active i = true)
    (hr : d2OrdinaryRole (role i))
    (hquota : 8192 ∣ quota i (role i))
    (hbase : 4096 ∣ base) (hwidth : 4096 ∣ width)
    (hlow : 4096 ∣ low) (hhigh : 4096 ∣ high)
    (hchildren : ∀ j, d2FlowTileAligned (children j)) :
    let sizes : Fin 8 -> Nat := fun j => d2FlowTreeRootDeficit (children j)
    let left := low + quota i (role i) / 2
    let right := high + quota i (role i) / 2
    let newLow : Fin 8 -> Nat := fun j =>
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j)).2.1
    let newHigh : Fin 8 -> Nat := fun j =>
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j)).2.2
    forall hole, hole ∈ staticHoleList 8
      (fun j => (d2EightChildHole base width left right sizes newLow newHigh j).1)
      (fun j => (d2EightChildHole base width left right sizes newLow newHigh j).2) ->
      4096 ∣ hole.1 ∧ 4096 ∣ hole.2 := by
  dsimp
  let sizes : Fin 8 -> Nat := fun j => d2FlowTreeRootDeficit (children j)
  let left := low + quota i (role i) / 2
  let right := high + quota i (role i) / 2
  let newLow : Fin 8 -> Nat := fun j =>
    (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j)).2.1
  let newHigh : Fin 8 -> Nat := fun j =>
    (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j)).2.2
  have hhalf : 4096 ∣ quota i (role i) / 2 := by
    rcases hquota with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    omega
  have hleft : 4096 ∣ left := by
    exact dvd_add hlow hhalf
  have hright : 4096 ∣ right := by
    exact dvd_add hhigh hhalf
  have hchildRoots := d2FlowStage_ordinary_child_rootAligned (G := G)
    children ha hr hquota hlow hhigh hchildren
  have hnewLow : ∀ j, 4096 ∣ newLow j := by
    intro j
    simpa [newLow] using (hchildRoots j).2.1
  have hnewHigh : ∀ j, 4096 ∣ newHigh j := by
    intro j
    simpa [newHigh] using (hchildRoots j).2.2
  have hholeLo : ∀ j, 4096 ∣
      (d2EightChildHole base width left right sizes newLow newHigh j).1 := by
    intro j
    exact (d2EightChildHole_endpoints_dvd sizes newLow newHigh
      hbase hwidth hleft hright hnewLow hnewHigh j).1
  have hholeHi : ∀ j, 4096 ∣
      (d2EightChildHole base width left right sizes newLow newHigh j).2 := by
    intro j
    exact (d2EightChildHole_endpoints_dvd sizes newLow newHigh
      hbase hwidth hleft hright hnewLow hnewHigh j).2
  have hlist := staticHoleList_endpoints_dvd (m := 4096) (count := 8)
    (fun j => (d2EightChildHole base width left right sizes newLow newHigh j).1)
    (fun j => (d2EightChildHole base width left right sizes newLow newHigh j).2)
    hholeLo hholeHi
  simpa [sizes, left, right, newLow, newHigh] using hlist

private theorem dvd4096_min {a b : Nat}
    (ha : 4096 ∣ a) (hb : 4096 ∣ b) : 4096 ∣ min a b := by
  by_cases hab : a <= b
  · rw [Nat.min_eq_left hab]
    exact ha
  · rw [Nat.min_eq_right (by omega)]
    exact hb

private theorem dvd4096_max {a b : Nat}
    (ha : 4096 ∣ a) (hb : 4096 ∣ b) : 4096 ∣ max a b := by
  by_cases hab : a <= b
  · rw [Nat.max_eq_right hab]
    exact hb
  · rw [Nat.max_eq_left (by omega)]
    exact ha

/-- A grid-aligned static interval either misses a 4096-cell or contains the
whole cell. -/
theorem staticWireInterval_inter_4096_cell
    {n lo hi cellLo cellHi : Nat}
    (hlo : 4096 ∣ lo) (hhi : 4096 ∣ hi)
    (hcellLo : 4096 ∣ cellLo)
    (hcellWidth : cellHi = cellLo + 4096) :
    staticWireInterval (n := n) lo hi ∩
        staticWireInterval cellLo cellHi = ∅ ∨
      staticWireInterval (n := n) lo hi ∩
        staticWireInterval cellLo cellHi =
          staticWireInterval cellLo cellHi := by
  have hcellHi : 4096 ∣ cellHi := by
    rw [hcellWidth]
    exact dvd_add hcellLo (dvd_refl 4096)
  by_cases hdisj : hi <= cellLo ∨ cellHi <= lo
  · left
    ext w
    simp [staticWireInterval]
    rcases hdisj with h | h <;> omega
  · right
    have hcellBeforeHi : cellLo < hi := by omega
    have hloBeforeCell : lo < cellHi := by omega
    have hloBound : lo <= cellLo := by
      rcases hlo with ⟨a, rfl⟩
      rcases hcellLo with ⟨b, rfl⟩
      omega
    have hhiBound : cellHi <= hi := by
      rcases hhi with ⟨a, rfl⟩
      rcases hcellLo with ⟨b, rfl⟩
      omega
    ext w
    simp only [Finset.mem_inter, staticWireInterval, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hwl, hwh⟩, hwcell⟩
      exact hwcell
    · intro hwcell
      exact ⟨⟨by omega, by omega⟩, hwcell⟩

/-- A rank fragment of one aligned static run is either an entire physical
4096-cell or empty whenever both local rank cuts lie on the 4096 grid. -/
theorem blockOf_staticWireInterval_inter_4096_cell
    {n lo hi start stop cellLo cellHi : Nat}
    (hlohi : lo <= hi) (hstop : stop <= hi - lo)
    (hlo : 4096 ∣ lo) (hstart : 4096 ∣ start)
    (hstopGrid : 4096 ∣ stop) (hcellLo : 4096 ∣ cellLo)
    (hcellWidth : cellHi = cellLo + 4096) :
    Chvatal.blockOf (staticWireInterval (n := n) lo hi) start stop ∩
        staticWireInterval cellLo cellHi = ∅ ∨
      Chvatal.blockOf (staticWireInterval (n := n) lo hi) start stop ∩
        staticWireInterval cellLo cellHi =
          staticWireInterval cellLo cellHi := by
  rw [blockOf_staticWireInterval_intersect_cell hlohi hstop]
  have hcellHi : 4096 ∣ cellHi := by
    rw [hcellWidth]
    exact dvd_add hcellLo (dvd_refl 4096)
  have hinter := staticWireInterval_inter_4096_cell (n := n)
    (dvd4096_max (dvd_add hlo hstart) hcellLo)
    (dvd4096_min (dvd_add hlo hstopGrid) hcellHi)
    hcellLo hcellWidth
  have hsubset :
      staticWireInterval (n := n) (max (lo + start) cellLo)
        (min (lo + stop) cellHi) ∩
          staticWireInterval (n := n) cellLo cellHi =
      staticWireInterval (n := n) (max (lo + start) cellLo)
        (min (lo + stop) cellHi) := by
    ext w
    simp [staticWireInterval]
    omega
  rcases hinter with hempty | hwhole
  · left
    exact hsubset.symm.trans hempty
  · right
    exact hsubset.symm.trans hwhole

/-- Every run is a contiguous static address interval with 4096-aligned
endpoints and lies within the global wire range. -/
def GridAlignedStaticRuns {n : Nat} : List (Finset (Fin n)) → Prop
  | [] => True
  | s :: runs =>
      (∃ lo hi, s = staticWireInterval lo hi ∧ lo <= hi ∧ hi <= n ∧
        4096 ∣ lo ∧ 4096 ∣ hi) ∧ GridAlignedStaticRuns runs

/-- If all static run endpoints and all cumulative rank cuts are 4096-aligned,
the slice of ordered runs inside a physical 4096-cell is either the whole cell
or empty. This is the local whole-column receiver-label theorem. -/
theorem orderedRunSliceInCell_grid_uniform {n : Nat}
    (runs : List (Finset (Fin n)))
    (hruns : GridAlignedStaticRuns runs)
    (start finish cellLo cellHi : Nat)
    (hstart : 4096 ∣ start) (hfinish : 4096 ∣ finish)
    (hcellLo : 4096 ∣ cellLo) (hcellWidth : cellHi = cellLo + 4096) :
    orderedRunSliceInCell runs start finish cellLo cellHi = ∅ ∨
      orderedRunSliceInCell runs start finish cellLo cellHi =
        staticWireInterval cellLo cellHi := by
  induction runs generalizing start finish with
  | nil =>
      left
      rfl
  | cons s runs ih =>
      rcases hruns with ⟨⟨lo, hi, hs, hlohi, hhin, hlo, hhi⟩, htailRuns⟩
      have hcard : s.card = hi - lo := by
        rw [hs]
        exact staticWireInterval_card hhin
      have hcardGrid : 4096 ∣ s.card := by
        rw [hcard]
        exact nat_dvd_trunc_sub_of_dvd hhi hlo
      have hstop : min finish s.card <= hi - lo := by
        rw [← hcard]
        exact Nat.min_le_right _ _
      have hstopGrid : 4096 ∣ min finish s.card :=
        dvd4096_min hfinish hcardGrid
      have hhead := blockOf_staticWireInterval_inter_4096_cell
        (n := n) (lo := lo) (hi := hi) (start := start)
        (stop := min finish s.card) (cellLo := cellLo) (cellHi := cellHi)
        hlohi hstop hlo hstart hstopGrid hcellLo hcellWidth
      have hhead' :
          Chvatal.blockOf s start (min finish s.card) ∩
            staticWireInterval cellLo cellHi = ∅ ∨
          Chvatal.blockOf s start (min finish s.card) ∩
            staticWireInterval cellLo cellHi =
              staticWireInterval cellLo cellHi := by
        simpa [hs] using hhead
      have hstartTail : 4096 ∣ start - s.card :=
        nat_dvd_trunc_sub_of_dvd hstart hcardGrid
      have hfinishTail : 4096 ∣ finish - s.card :=
        nat_dvd_trunc_sub_of_dvd hfinish hcardGrid
      have htail := ih htailRuns (start - s.card) (finish - s.card)
        hstartTail hfinishTail
      simp only [orderedRunSliceInCell]
      rcases hhead' with hhead | hhead <;>
        rcases htail with htail | htail
      · left
        simp [hhead, htail]
      · right
        simp [hhead, htail]
      · right
        simp [hhead, htail]
      · right
        simp [hhead, htail]

/-- Numeric interval endpoints underlying the recursive static-gap run list. -/
def staticGapIntervalBounds : Nat → List (Nat × Nat) → Nat → List (Nat × Nat)
  | cursor, [], stop => [(cursor, stop)]
  | cursor, (lo, hi) :: holes, stop =>
      (cursor, lo) :: staticGapIntervalBounds hi holes stop

/-- If the parent interval and every hole endpoint lie on a grid, every
complementary static run has grid-aligned endpoints. -/
theorem staticGapIntervalBounds_endpoints_dvd {m cursor stop : Nat}
    (holes : List (Nat × Nat))
    (hcursor : m ∣ cursor) (hstop : m ∣ stop)
    (hholes : ∀ hole, hole ∈ holes -> m ∣ hole.1 ∧ m ∣ hole.2) :
    ∀ run, run ∈ staticGapIntervalBounds cursor holes stop ->
      m ∣ run.1 ∧ m ∣ run.2 := by
  induction holes generalizing cursor with
  | nil =>
      intro run hmem
      simp only [staticGapIntervalBounds, List.mem_singleton] at hmem
      cases hmem
      exact ⟨hcursor, hstop⟩
  | cons hole holes ih =>
      rcases hole with ⟨lo, hi⟩
      have hhead := hholes (lo, hi) (by simp)
      intro run hmem
      simp only [staticGapIntervalBounds, List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · cases hmem
        exact ⟨hcursor, hhead.1⟩
      · have hholesTail : ∀ hole, hole ∈ holes ->
            m ∣ hole.1 ∧ m ∣ hole.2 := by
          intro hole hhole
          exact hholes hole (by simp [hhole])
        exact ih (cursor := hi) hhead.2 hholesTail run hmem

/-- The numeric bounds are exactly the intervals whose finsets form
`staticGapRuns`; this lets endpoint arithmetic be reused with ordered rank
slices of the actual static address sets. -/
theorem staticGapRuns_eq_map_intervalBounds {n cursor stop : Nat}
    (holes : List (Nat × Nat)) :
    staticGapRuns (n := n) cursor holes stop =
      (staticGapIntervalBounds cursor holes stop).map
        (fun run => staticWireInterval run.1 run.2) := by
  induction holes generalizing cursor with
  | nil => rfl
  | cons hole holes ih =>
      rcases hole with ⟨lo, hi⟩
      simp [staticGapRuns, staticGapIntervalBounds, ih]

/-- A fitted static-hole list with grid-aligned endpoints produces grid-aligned
complementary runs. The upper bound on `stop` ensures every run is a valid
interval in the finite wire universe. -/
theorem staticGapRuns_gridAligned_of_endpoints {n cursor stop : Nat}
    (holes : List (Nat × Nat))
    (hfit : StaticHolesFit cursor holes stop)
    (hcursor : 4096 ∣ cursor) (hstop : 4096 ∣ stop) (hstopBound : stop ≤ n)
    (hholes : ∀ hole, hole ∈ holes → 4096 ∣ hole.1 ∧ 4096 ∣ hole.2) :
    GridAlignedStaticRuns (staticGapRuns (n := n) cursor holes stop) := by
  induction holes generalizing cursor with
  | nil =>
      simp only [staticGapRuns, GridAlignedStaticRuns]
      exact ⟨⟨cursor, stop, rfl, hfit, hstopBound, hcursor, hstop⟩, trivial⟩
  | cons hole holes ih =>
      rcases hole with ⟨lo, hi⟩
      rcases hfit with ⟨hcursorLo, hlohi, hihistop, htailFit⟩
      have hgrid := hholes (lo, hi) (by simp)
      have htailGrid : ∀ hole, hole ∈ holes → 4096 ∣ hole.1 ∧ 4096 ∣ hole.2 := by
        intro hole hmem
        exact hholes hole (by simp [hmem])
      have htail := ih htailFit hgrid.2 htailGrid
      simp only [staticGapRuns, GridAlignedStaticRuns]
      refine ⟨⟨cursor, lo, rfl, hcursorLo, ?_, hcursor, hgrid.1⟩, htail⟩
      omega

/-- A rank slice of the actual fitted static-gap runs occupies either all or
none of each physical 4096-cell when the run endpoints and rank cuts share
that grid. -/
theorem staticGapRuns_rankSlice_wholeCell {n cursor stop : Nat}
    (holes : List (Nat × Nat))
    (hfit : StaticHolesFit cursor holes stop)
    (hcursor : 4096 ∣ cursor) (hstop : 4096 ∣ stop) (hstopBound : stop ≤ n)
    (hholes : ∀ hole, hole ∈ holes → 4096 ∣ hole.1 ∧ 4096 ∣ hole.2)
    (start finish cellLo cellHi : Nat)
    (hstart : 4096 ∣ start) (hfinish : 4096 ∣ finish)
    (hcellLo : 4096 ∣ cellLo) (hcellWidth : cellHi = cellLo + 4096) :
    orderedRunSliceInCell (staticGapRuns (n := n) cursor holes stop)
      start finish cellLo cellHi = ∅ ∨
    orderedRunSliceInCell (staticGapRuns (n := n) cursor holes stop)
      start finish cellLo cellHi = staticWireInterval cellLo cellHi := by
  exact orderedRunSliceInCell_grid_uniform
    (staticGapRuns (n := n) cursor holes stop)
    (staticGapRuns_gridAligned_of_endpoints holes hfit hcursor hstop
      hstopBound hholes)
    start finish cellLo cellHi hstart hfinish hcellLo hcellWidth

/-- Every 4096-rank fragment of a grid-aligned static-gap sender is one
physical 4096-cell. This turns the local all-or-empty intersection fact into
an exact cell-to-cell routing statement for each aligned rank fragment. -/
theorem staticGapRankFragment_eq_staticCell
    {n cursor stop start finish : Nat} (holes : List (Nat × Nat))
    (hn : 4096 ∣ n) (hfit : StaticHolesFit cursor holes stop)
    (hcursor : 4096 ∣ cursor) (hstop : 4096 ∣ stop)
    (hstopBound : stop ≤ n)
    (hholes : ∀ hole, hole ∈ holes → 4096 ∣ hole.1 ∧ 4096 ∣ hole.2)
    (hstart : 4096 ∣ start) (hfinish : 4096 ∣ finish)
    (hlen : finish = start + 4096)
    (hbound : finish ≤
      (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes).card) :
    ∃ cellLo, 4096 ∣ cellLo ∧ cellLo + 4096 ≤ n ∧
      Chvatal.blockOf
        (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes)
        start finish = staticWireInterval cellLo (cellLo + 4096) := by
  have hcard :
      (Chvatal.blockOf
        (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes)
        start finish).card = 4096 := by
    rw [Chvatal.blockOf_card hbound]
    omega
  apply rankFragment_eq_staticCell_of_wholeCell_intersections
    (n := n) (S := Chvatal.blockOf
      (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes)
      start finish) hn hcard
  intro cellLo hcellLo hcellHi
  have hlocal := staticGapRuns_rankSlice_wholeCell holes hfit hcursor hstop
    hstopBound hholes start finish cellLo (cellLo + 4096)
    hstart hfinish hcellLo rfl
  have hidentity := blockOf_staticGapRuns (n := n) cursor stop holes hfit
    start finish
  rw [hidentity, orderedRunSlice_inter_cell]
  exact hlocal
/-- A grid-aligned rank port of a static-gap sender decomposes into exactly
one physical cell for each 4096 wires of port capacity. This is the form used
to lift the recursive scheduler's aligned port cuts to the cell-incidence
state. -/
theorem staticGapRankPort_cells
    {n cursor stop start finish : Nat} (holes : List (Nat × Nat))
    (q : Nat) (hn : 4096 ∣ n)
    (hfit : StaticHolesFit cursor holes stop)
    (hcursor : 4096 ∣ cursor) (hstop : 4096 ∣ stop)
    (hstopBound : stop ≤ n)
    (hholes : ∀ hole, hole ∈ holes → 4096 ∣ hole.1 ∧ 4096 ∣ hole.2)
    (hstart : 4096 ∣ start) (hfinish : 4096 ∣ finish)
    (hlen : finish = start + q * 4096)
    (hbound : finish ≤
      (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes).card) :
    ∀ j : Fin q, ∃ cellLo, 4096 ∣ cellLo ∧ cellLo + 4096 ≤ n ∧
      Chvatal.blockOf
        (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes)
        (start + j.val * 4096) (start + (j.val + 1) * 4096) =
          staticWireInterval cellLo (cellLo + 4096) := by
  intro j
  have hstartJ : 4096 ∣ start + j.val * 4096 := by
    exact dvd_add hstart (⟨j.val, by ring⟩)
  have hfinishJ : 4096 ∣ start + (j.val + 1) * 4096 := by
    exact dvd_add hstart (⟨j.val + 1, by ring⟩)
  have hlenJ : start + (j.val + 1) * 4096 =
      (start + j.val * 4096) + 4096 := by
    ring
  have hboundJ : start + (j.val + 1) * 4096 <=
      (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes).card := by
    have hj : j.val + 1 ≤ q := by omega
    calc
      start + (j.val + 1) * 4096 ≤ start + q * 4096 := by omega
      _ = finish := hlen.symm
      _ ≤ _ := hbound
  exact staticGapRankFragment_eq_staticCell holes hn hfit hcursor hstop
    hstopBound hholes hstartJ hfinishJ hlenJ hboundJ

/-- Distinct 4096-rank fragments of one aligned sender port map to distinct
physical cells. Thus the preceding cell witnesses form an injective spatial
map and preserve the number of wire-cells in each port. -/
theorem staticGapRankPort_cells_injective
    {n cursor stop start finish : Nat} (holes : List (Nat × Nat))
    (q : Nat) (hn : 4096 ∣ n)
    (hfit : StaticHolesFit cursor holes stop)
    (hcursor : 4096 ∣ cursor) (hstop : 4096 ∣ stop)
    (hstopBound : stop ≤ n)
    (hholes : ∀ hole, hole ∈ holes → 4096 ∣ hole.1 ∧ 4096 ∣ hole.2)
    (hstart : 4096 ∣ start) (hfinish : 4096 ∣ finish)
    (hlen : finish = start + q * 4096)
    (hbound : finish ≤
      (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes).card) :
    ∃ cells : Fin q → Nat,
      (∀ j, 4096 ∣ cells j ∧ cells j + 4096 ≤ n ∧
        Chvatal.blockOf
          (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes)
          (start + j.val * 4096) (start + (j.val + 1) * 4096) =
            staticWireInterval (cells j) (cells j + 4096)) ∧
      Function.Injective cells := by
  have hfrags := staticGapRankPort_cells holes q hn hfit hcursor hstop
    hstopBound hholes hstart hfinish hlen hbound
  let cells : Fin q → Nat := fun j => Classical.choose (hfrags j)
  have hcells : ∀ j, 4096 ∣ cells j ∧ cells j + 4096 ≤ n ∧
      Chvatal.blockOf
        (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes)
        (start + j.val * 4096) (start + (j.val + 1) * 4096) =
          staticWireInterval (cells j) (cells j + 4096) := by
    intro j
    exact Classical.choose_spec (hfrags j)
  refine ⟨cells, hcells, ?_⟩
  intro j k hjk
  by_contra hne
  let S := staticWireInterval (n := n) cursor stop \ staticHoleUnion holes
  have hdisj : Disjoint
      (Chvatal.blockOf S (start + j.val * 4096)
        (start + (j.val + 1) * 4096))
      (Chvatal.blockOf S (start + k.val * 4096)
        (start + (k.val + 1) * 4096)) := by
    by_cases hjk' : j.val < k.val
    · apply Chvatal.disjoint_blockOf
      omega
    · have hkj : k.val < j.val := by omega
      exact (Chvatal.disjoint_blockOf (show
        start + (k.val + 1) * 4096 ≤ start + j.val * 4096 by omega)).symm
  have hsame :
      Chvatal.blockOf S (start + j.val * 4096)
          (start + (j.val + 1) * 4096) =
        Chvatal.blockOf S (start + k.val * 4096)
          (start + (k.val + 1) * 4096) := by
    calc
      _ = staticWireInterval (cells j) (cells j + 4096) := (hcells j).2.2
      _ = staticWireInterval (cells k) (cells k + 4096) :=
        congrArg (fun x : Nat => staticWireInterval (n := n) x (x + 4096)) hjk
      _ = _ := (hcells k).2.2.symm
  have hboundJ : start + (j.val + 1) * 4096 ≤ S.card := by
    have hjq : j.val + 1 ≤ q := by omega
    calc
      start + (j.val + 1) * 4096 ≤ start + q * 4096 := by omega
      _ = finish := hlen.symm
      _ ≤ S.card := hbound
  have hcardJ :
      (Chvatal.blockOf S (start + j.val * 4096)
        (start + (j.val + 1) * 4096)).card = 4096 := by
    rw [Chvatal.blockOf_card hboundJ]
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by rw [hcardJ]; norm_num)
  have hw' : w ∈ Chvatal.blockOf S
      (start + k.val * 4096) (start + (k.val + 1) * 4096) := by
    rw [← hsame]
    exact hw
  exact (Finset.disjoint_left.mp hdisj hw hw').elim
/-- The D2 ordinary-sender conservation equation makes those ten ports a
monotone partition of the sender's rank interval. -/
theorem d2SenderPortBoundary_valid
    (pi senderCard : Nat) (widths : Fin 8 -> Nat)
    (heven : pi % 2 = 0)
    (hconserve : pi + d2FlowTotal widths = senderCard) :
    d2SenderPortBoundary pi senderCard widths 0 = 0 /\
    d2SenderPortBoundary pi senderCard widths (Fin.last 10) = senderCard /\
    (forall i : Fin 10,
      d2SenderPortBoundary pi senderCard widths (Fin.castSucc i) <=
        d2SenderPortBoundary pi senderCard widths (Fin.succ i)) := by
  have hpi : pi = 2 * (pi / 2) := by omega
  constructor
  · simp [d2SenderPortBoundary, d2SenderPortBoundaryNat]
  constructor
  · simp [d2SenderPortBoundary, d2SenderPortBoundaryNat]
  · intro i
    simpa [d2SenderPortBoundary, Fin.val_castSucc, Fin.val_succ] using
      d2SenderPortBoundaryNat_mono pi senderCard widths heven hconserve i.isLt

/-- Each adjacent interval in the ten-port partition has exactly its intended
rank length: the outside intervals are the two quota halves, and the eight
interior intervals have the stage's child widths. -/
theorem d2SenderPortBoundaryNat_succ
    (pi senderCard : Nat) (widths : Fin 8 -> Nat)
    (heven : pi % 2 = 0)
    (hconserve : pi + d2FlowTotal widths = senderCard)
    {i : Nat} (hi : i < 10) :
    d2SenderPortBoundaryNat pi senderCard widths (i + 1) =
      d2SenderPortBoundaryNat pi senderCard widths i +
        if i = 0 then pi / 2 else if i = 9 then pi / 2
        else d2FlowRankBoundary widths i - d2FlowRankBoundary widths (i - 1) := by
  have hpi : pi = 2 * (pi / 2) := by omega
  by_cases hzero : i = 0
  · simp [d2SenderPortBoundaryNat, hzero, d2FlowRankBoundary_zero]
  · by_cases hlast : i = 9
    · simp [d2SenderPortBoundaryNat, hzero, hlast, d2FlowRankBoundary_end]
      omega
    · have hmid : 1 <= i /\ i < 9 := by omega
      have hidx : i - 1 < 8 := by omega
      have hstep := d2FlowRankBoundary_succ widths (i - 1) hidx
      have hidx' : i - 1 + 1 = i := by omega
      rw [hidx'] at hstep
      have hnotTen : i ≠ 10 := by omega
      have hnextZero : i + 1 ≠ 0 := by omega
      have hnextTen : i + 1 ≠ 10 := by omega
      simp only [d2SenderPortBoundaryNat, if_neg hzero, if_neg hnotTen,
        if_neg hnextZero, if_neg hnextTen, if_neg hlast]
      rw [show i + 1 - 1 = i by omega]
      omega

/-- The concrete ordinary D2 stage supplies a valid ten-port boundary map
for each sender bag. The eight interior widths are the actual reductions in
the child deficits; the two outside ports are the quota halves sent upward.
This packages the flow conservation theorem in the interface consumed by
tile clipping. -/
theorem d2FlowStage_regular_sender_boundary_valid
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h i G low high n : Nat}
    (children : Fin 8 -> D2FlowTree h) (s : Finset (Fin n))
    (ha : active i = true)
    (hr : role i = .topRise \/ role i = .mid \/ role i = .botDesc)
    (hbal : G = low + high)
    (heven : quota i (role i) % 2 = 0)
    (hleft : low + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hright : high + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hdisjoint : low + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2)
    (hsender : s.card = d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    let widths : Fin 8 -> Nat := fun j =>
      d2FlowTreeRootDeficit (children j) -
        d2FlowTreeRootDeficit
          (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j)
    d2SenderPortBoundary (quota i (role i)) s.card widths 0 = 0 /\
    d2SenderPortBoundary (quota i (role i)) s.card widths (Fin.last 10) = s.card /\
    (forall j : Fin 10,
      d2SenderPortBoundary (quota i (role i)) s.card widths (Fin.castSucc j) <=
        d2SenderPortBoundary (quota i (role i)) s.card widths (Fin.succ j)) := by
  dsimp
  let widths : Fin 8 -> Nat := fun j =>
    d2FlowTreeRootDeficit (children j) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j)
  have hconserve : quota i (role i) + d2FlowTotal widths =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
    simpa [widths, d2FlowTotal] using
      d2FlowStage_regular_rank_port_conservation children ha hr hbal heven
        hleft hright hdisjoint
  have hsenderConserve : quota i (role i) + d2FlowTotal widths = s.card := by
    rw [hsender]
    exact hconserve
  exact d2SenderPortBoundary_valid (quota i (role i)) s.card widths heven
    hsenderConserve

/-- Exact interval-length contract for an actual ordinary D2 sender. For
ports 1 through 8, the rank interval has the child deficit reduction as its
length; ports 0 and 9 each have length half the upward quota. -/
theorem d2FlowStage_regular_sender_port_length
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h i G low high n : Nat}
    (children : Fin 8 -> D2FlowTree h) (s : Finset (Fin n))
    (ha : active i = true)
    (hr : role i = .topRise \/ role i = .mid \/ role i = .botDesc)
    (hbal : G = low + high)
    (heven : quota i (role i) % 2 = 0)
    (hleft : low + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hright : high + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hdisjoint : low + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2)
    (hsender : s.card = d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) - G)
    {p : Nat} (hp : p < 10) :
    d2SenderPortBoundaryNat (quota i (role i)) s.card
        (fun j => d2FlowTreeRootDeficit (children j) -
          d2FlowTreeRootDeficit
            (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)) (p + 1) =
      d2SenderPortBoundaryNat (quota i (role i)) s.card
        (fun j => d2FlowTreeRootDeficit (children j) -
          d2FlowTreeRootDeficit
            (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)) p +
        if p = 0 then quota i (role i) / 2
        else if p = 9 then quota i (role i) / 2
        else d2FlowRankBoundary
            (fun j => d2FlowTreeRootDeficit (children j) -
              d2FlowTreeRootDeficit
                (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
                  (.node G low high children)) j)) p -
          d2FlowRankBoundary
            (fun j => d2FlowTreeRootDeficit (children j) -
              d2FlowTreeRootDeficit
                (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
                  (.node G low high children)) j)) (p - 1) := by
  let widths : Fin 8 -> Nat := fun j =>
    d2FlowTreeRootDeficit (children j) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j)
  have hconserve : quota i (role i) + d2FlowTotal widths = s.card := by
    have hflow : quota i (role i) + d2FlowTotal widths =
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
      simpa [widths, d2FlowTotal] using
        d2FlowStage_regular_rank_port_conservation children ha hr hbal heven
          hleft hright hdisjoint
    rw [hsender]
    exact hflow
  simpa [widths] using d2SenderPortBoundaryNat_succ
    (quota i (role i)) s.card widths heven hconserve hp

/-- A schedule may give each input tile its own cumulative rank-port cuts.
The existing global transfer theorem used one shared cut map for all tiles;
this family wrapper records the receiver profile produced by the actual
tile-specific cuts. -/
noncomputable def variableTileGroupedActual
    {ports tiles : Nat} {J : Type*} [DecidableEq J]
    (m : Nat) (bounds : Fin tiles -> Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J) (j : J) : Nat :=
  Finset.univ.sum fun t : Fin tiles =>
    physicalFlowGroupedActual m (bounds t)
      (fun _ : Fin 1 => sourceHeight t)
      (fun _ cell => tag t cell) j

/-- The corresponding ideal rank profile, grouped by the same actual
tile-specific destination tags. -/
noncomputable def variableTileGroupedIdeal
    {ports tiles : Nat} {J : Type*} [DecidableEq J]
    (m : Nat) (bounds : Fin tiles -> Fin (ports + 1) -> Nat)
    (idealTileMass : Fin tiles -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J) (j : J) : Nat :=
  Finset.univ.sum fun t : Fin tiles =>
    clippedFlowGroupedRank m (bounds t)
      (fun _ : Fin 1 => idealTileMass t)
      (fun _ cell => tag t cell) j

/-- Physical post-core cell count when each tile and column has its own
monotone port cuts. This is more general than clipping one tile-wide rank
boundary and is the form needed when static D2 sender boundaries meet a tile
at different columns. -/
noncomputable def variableColumnGroupedActual
    {ports tiles : Nat} {J : Type*} [DecidableEq J]
    (sourceHeight : Fin tiles -> Col -> Nat)
    (cuts : Fin tiles -> Col -> Nat -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J) (j : J) : Nat :=
  (Finset.univ.filter fun x : Prod (Fin tiles) (Prod Col (Fin ports)) =>
    tag x.1 x.2 = j).sum fun x => prefixIntervalMass
      (physicalTwoGridRepairHeight (sourceHeight x.1) reflectedCombinedSigma x.2.1)
      (cuts x.1 x.2.1 x.2.2.val) (cuts x.1 x.2.1 (x.2.2.val + 1))

/-- Exact row-major reference count for the same tile/column/port tags. -/
noncomputable def variableColumnGroupedIdeal
    {ports tiles : Nat} {J : Type*} [DecidableEq J]
    (tileMass : Fin tiles -> Nat)
    (cuts : Fin tiles -> Col -> Nat -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J) (j : J) : Nat :=
  (Finset.univ.filter fun x : Prod (Fin tiles) (Prod Col (Fin ports)) =>
    tag x.1 x.2 = j).sum fun x =>
      prefixIntervalMass (exactRankColumnHeight (tileMass x.1) x.2.1)
        (cuts x.1 x.2.1 x.2.2.val) (cuts x.1 x.2.1 (x.2.2.val + 1))

/-- The 448 physical provider and exact-rank mass transfer compose for
arbitrary per-column cuts. Thus different columns in the same physical tile
may follow different sender-port boundaries, while the parent mass error is
still charged only once and each tile pays 448 fresh error. -/
theorem variable_column_physical_profile_error_le_parent_add_448
    {ports tiles : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (m : Nat)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (cuts : Fin tiles -> Col -> Nat -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J)
    (parentError : Nat)
    (hports : 0 < ports) (hm : m <= 4096)
    (hH : forall t, tileMass t <= 262144)
    (hI : forall t, idealTileMass t <= 262144)
    (hinput : forall t c, sourceHeight t c <= m)
    (hHsum : forall t, tileMass t = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle (sourceHeight t) c)
    (hzero : forall t c, cuts t c 0 = 0)
    (hend : forall t c, cuts t c ports = m)
    (hmono : forall t c i, i < ports -> cuts t c i <= cuts t c (i + 1))
    (hcutBound : forall t c i, i <= ports -> cuts t c i <= m)
    (hMacroParent : (Finset.univ.sum fun t : Fin tiles =>
      countDistance (tileMass t) (idealTileMass t)) <= parentError) :
    (Finset.univ.sum fun j : J =>
      countDistance
        (variableColumnGroupedActual sourceHeight cuts tag j)
        (variableColumnGroupedIdeal idealTileMass cuts tag j)) <=
      parentError + 448 * tiles := by
  let actual : Prod (Fin tiles) (Prod Col (Fin ports)) -> Nat := fun x =>
    prefixIntervalMass
      (physicalTwoGridRepairHeight (sourceHeight x.1) reflectedCombinedSigma x.2.1)
      (cuts x.1 x.2.1 x.2.2.val) (cuts x.1 x.2.1 (x.2.2.val + 1))
  let reference : Prod (Fin tiles) (Prod Col (Fin ports)) -> Nat := fun x =>
    prefixIntervalMass (exactRankColumnHeight (tileMass x.1) x.2.1)
      (cuts x.1 x.2.1 x.2.2.val) (cuts x.1 x.2.1 (x.2.2.val + 1))
  let ideal : Prod (Fin tiles) (Prod Col (Fin ports)) -> Nat := fun x =>
    prefixIntervalMass (exactRankColumnHeight (idealTileMass x.1) x.2.1)
      (cuts x.1 x.2.1 x.2.2.val) (cuts x.1 x.2.1 (x.2.2.val + 1))
  let transfer : Prod (Fin tiles) (Prod Col (Fin ports)) -> Nat := fun x =>
    countDistance (actual x) (reference x)
  let group : Prod (Fin tiles) (Prod Col (Fin ports)) -> J := fun x =>
    tag x.1 x.2
  have hlocalRat :
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun cell : Prod Col (Fin ports) =>
          abs ((actual (t, cell) : Rat) - (reference (t, cell) : Rat))) <=
        448 * tiles := by
    calc
      _ <= Finset.univ.sum fun _ : Fin tiles => (448 : Rat) := by
        apply Finset.sum_le_sum
        intro t ht
        have hphysicalMass : tileMass t = Finset.univ.sum fun c : Col =>
            physicalTwoGridRepairHeight (sourceHeight t) reflectedCombinedSigma c := by
          calc
            tileMass t = Finset.univ.sum fun c : Col =>
                fullHeightTwoShuffle (sourceHeight t) c := hHsum t
            _ = Finset.univ.sum fun c : Col =>
                physicalTwoGridRepairHeight (sourceHeight t) reflectedCombinedSigma c :=
              (physical_profile_sum_eq_semantic_sum (sourceHeight t)
                (fun c => le_trans (hinput t c) hm) reflectedCombinedSigma).symm
        have htile := physical_profile_partial_rows_rebinned_l1_le_448
          (sourceHeight t) reflectedCombinedSigma m ports (tileMass t) (cuts t)
          hm hports (hinput t) hphysicalMass
          (fun c => hzero t c) (fun c => hend t c)
          (fun c i hi => hmono t c i hi)
          (fun c i hi => hcutBound t c i hi)
        simpa [actual, reference] using htile
      _ = 448 * tiles := by norm_num [Rat.mul_comm]
  have hlocalCast :
      ((Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun cell : Prod Col (Fin ports) =>
          countDistance (actual (t, cell)) (reference (t, cell)) : Nat) : Rat) =
        Finset.univ.sum fun t : Fin tiles =>
          Finset.univ.sum fun cell : Prod Col (Fin ports) =>
            abs ((actual (t, cell) : Rat) - (reference (t, cell) : Rat)) := by
    simp only [Nat.cast_sum, countDistance_rat_eq_abs_local]
  have hlocalNat :
      (Finset.univ.sum fun t : Fin tiles =>
        Finset.univ.sum fun cell : Prod Col (Fin ports) =>
          countDistance (actual (t, cell)) (reference (t, cell))) <= 448 * tiles := by
    have hbound :
        ((Finset.univ.sum fun t : Fin tiles =>
          Finset.univ.sum fun cell : Prod Col (Fin ports) =>
            countDistance (actual (t, cell)) (reference (t, cell)) : Nat) : Rat) <=
          (448 * tiles : Nat) := by
      rw [hlocalCast]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlocalRat
    exact_mod_cast hbound
  have hparentTile (t : Fin tiles) :
      (Finset.univ.sum fun c : Col =>
        Finset.univ.sum fun p : Fin ports =>
          countDistance (reference (t, (c, p))) (ideal (t, (c, p)))) <=
        countDistance (tileMass t) (idealTileMass t) := by
    simpa [reference, ideal] using
      exactRankColumnPorts_distance_le_mass
        (tileMass t) (idealTileMass t) m ports (cuts t)
        (hH t) (hI t)
        (fun c => hzero t c) (fun c => hend t c)
        (fun c i hi => hmono t c i hi)
  have hParentProduct :
      (Finset.univ.sum fun x : Prod (Fin tiles) (Prod Col (Fin ports)) =>
        countDistance (reference x) (ideal x)) <= parentError := by
    calc
      _ = Finset.univ.sum fun t : Fin tiles =>
          Finset.univ.sum fun c : Col =>
            Finset.univ.sum fun p : Fin ports =>
              countDistance (reference (t, (c, p))) (ideal (t, (c, p))) := by
        rw [Fintype.sum_prod_type' (fun t cell =>
          countDistance (reference (t, cell)) (ideal (t, cell)))]
        apply Finset.sum_congr rfl
        intro t ht
        rw [Fintype.sum_prod_type' (fun c p =>
          countDistance (reference (t, (c, p))) (ideal (t, (c, p))))]
      _ <= Finset.univ.sum fun t : Fin tiles =>
          countDistance (tileMass t) (idealTileMass t) :=
        Finset.sum_le_sum (fun t ht => hparentTile t)
      _ <= parentError := hMacroParent
  have hTransferProduct :
      (Finset.univ.sum fun x : Prod (Fin tiles) (Prod Col (Fin ports)) =>
        transfer x) <= 448 * tiles := by
    rw [Fintype.sum_prod_type' (fun t cell => transfer (t, cell))]
    simpa [transfer] using hlocalNat
  have hUpper : forall x, actual x <= reference x + transfer x := by
    intro x
    simp [transfer, countDistance]
    omega
  have hLower : forall x, reference x <= actual x + transfer x := by
    intro x
    simp [transfer, countDistance]
    omega
  calc
    _ <= parentError + Finset.univ.sum fun x : Prod (Fin tiles) (Prod Col (Fin ports)) =>
          transfer x := by
      simpa [variableColumnGroupedActual, variableColumnGroupedIdeal,
        actual, ideal, group] using
        grouped_child_rank_error_le_parent_add_transfer
          group actual reference ideal transfer parentError hUpper hLower hParentProduct
    _ <= parentError + 448 * tiles := by omega

/-- The arbitrary-column recurrence preserves the 512-per-output-tile
budget whenever the number of physical tiles doubles. -/
theorem variable_column_physical_profile_error_le_next_budget
    {ports tiles outputTiles : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (m : Nat)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (cuts : Fin tiles -> Col -> Nat -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J)
    (hports : 0 < ports) (hm : m <= 4096)
    (hH : forall t, tileMass t <= 262144)
    (hI : forall t, idealTileMass t <= 262144)
    (hinput : forall t c, sourceHeight t c <= m)
    (hHsum : forall t, tileMass t = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle (sourceHeight t) c)
    (hzero : forall t c, cuts t c 0 = 0)
    (hend : forall t c, cuts t c ports = m)
    (hmono : forall t c i, i < ports -> cuts t c i <= cuts t c (i + 1))
    (hcutBound : forall t c i, i <= ports -> cuts t c i <= m)
    (hOutputTiles : outputTiles = 2 * tiles)
    (hMacroParent : (Finset.univ.sum fun t : Fin tiles =>
      countDistance (tileMass t) (idealTileMass t)) <= 512 * tiles) :
    (Finset.univ.sum fun j : J =>
      countDistance
        (variableColumnGroupedActual sourceHeight cuts tag j)
        (variableColumnGroupedIdeal idealTileMass cuts tag j)) <=
      512 * outputTiles := by
  have hstep := variable_column_physical_profile_error_le_parent_add_448
    m sourceHeight tileMass idealTileMass cuts tag (512 * tiles)
    hports hm hH hI hinput hHsum hzero hend hmono hcutBound hMacroParent
  rw [hOutputTiles]
  calc
    _ <= 512 * tiles + 448 * tiles := hstep
    _ <= 512 * tiles + 512 * tiles := by omega
    _ = 512 * (2 * tiles) := by ring

/-- The checked physical 448 transfer composes across tiles even when each
sender has different rank cuts and receiver labels. If parent tile masses
already have aggregate error at most `parentError`, regrouping the tilewise
outputs by their actual receivers costs at most that parent error plus 448
fresh units per input tile.

This is the variable-cut interface needed by a concrete schedule: it removes
the artificial requirement that unrelated senders share one common boundary
map. It does not by itself identify a schedule's physical tags. -/
theorem variable_tile_physical_profile_error_le_parent_add_448
    {ports tiles : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (m : Nat)
    (bounds : Fin tiles -> Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J)
    (parentError : Nat)
    (hports : 0 < ports)
    (hm : m <= 4096)
    (hfirst : forall t, bounds t 0 = 0)
    (hlast : forall t, bounds t (Fin.last ports) = 64 * m)
    (hmono : forall t, forall i : Fin ports,
      bounds t (Fin.castSucc i) <= bounds t (Fin.succ i))
    (hH : forall t, tileMass t <= 262144)
    (hI : forall t, idealTileMass t <= 262144)
    (hinput : forall t c, sourceHeight t c <= m)
    (hHsum : forall t, tileMass t = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle (sourceHeight t) c)
    (hMacroParent : (Finset.univ.sum fun t : Fin tiles =>
      countDistance (tileMass t) (idealTileMass t)) <= parentError) :
    (Finset.univ.sum fun j : J =>
      countDistance
        (variableTileGroupedActual m bounds sourceHeight tag j)
        (variableTileGroupedIdeal m bounds idealTileMass tag j)) <=
      parentError + 448 * tiles := by
  let localActual : Fin tiles -> J -> Nat := fun t j =>
    physicalFlowGroupedActual m (bounds t)
      (fun _ : Fin 1 => sourceHeight t)
      (fun _ cell => tag t cell) j
  let localIdeal : Fin tiles -> J -> Nat := fun t j =>
    clippedFlowGroupedRank m (bounds t)
      (fun _ : Fin 1 => idealTileMass t)
      (fun _ cell => tag t cell) j
  have hlocal (t : Fin tiles) :
      (Finset.univ.sum fun j : J =>
        countDistance (localActual t j) (localIdeal t j)) <=
        countDistance (tileMass t) (idealTileMass t) + 448 := by
    have hparent :
        (Finset.univ.sum fun u : Fin 1 =>
          countDistance (tileMass t) (idealTileMass t)) <=
          countDistance (tileMass t) (idealTileMass t) := by simp
    have h := clipped_global_physical_profile_error_le_parent_add_448
      m (bounds t)
      (fun _ : Fin 1 => sourceHeight t)
      (fun _ : Fin 1 => tileMass t)
      (fun _ : Fin 1 => idealTileMass t)
      (fun _ cell => tag t cell)
      (countDistance (tileMass t) (idealTileMass t))
      hports hm (hfirst t) (by simpa using hlast t)
      (by
        intro i
        simpa using hmono t i)
      (by intro u; simpa using hH t)
      (by intro u; simpa using hI t)
      (by intro u c; exact hinput t c)
      (by intro u; simpa using hHsum t)
      hparent
    simpa [localActual, localIdeal] using h
  calc
    _ <= Finset.univ.sum fun j : J =>
          Finset.univ.sum fun t : Fin tiles =>
            countDistance (localActual t j) (localIdeal t j) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa [variableTileGroupedActual, variableTileGroupedIdeal,
        localActual, localIdeal] using
        (countDistance_sum_le Finset.univ
          (fun t : Fin tiles => localActual t j)
          (fun t : Fin tiles => localIdeal t j))
    _ = Finset.univ.sum fun t : Fin tiles =>
          Finset.univ.sum fun j : J =>
            countDistance (localActual t j) (localIdeal t j) := by
      rw [Finset.sum_comm]
    _ <= Finset.univ.sum fun t : Fin tiles =>
          (countDistance (tileMass t) (idealTileMass t) + 448) := by
      apply Finset.sum_le_sum
      intro t ht
      exact hlocal t
    _ = (Finset.univ.sum fun t : Fin tiles =>
          countDistance (tileMass t) (idealTileMass t)) + 448 * tiles := by
      simp [Finset.sum_add_distrib, Nat.mul_comm]
    _ <= parentError + 448 * tiles := Nat.add_le_add_right hMacroParent _

/-- Once the schedule really doubles the number of destination tiles, the
variable-cut transfer preserves the same 512-error-per-output-tile
invariant. -/
theorem variable_tile_physical_profile_error_le_next_budget
    {ports tiles outputTiles : Nat} {J : Type*}
    [Fintype J] [DecidableEq J]
    (m : Nat)
    (bounds : Fin tiles -> Fin (ports + 1) -> Nat)
    (sourceHeight : Fin tiles -> Col -> Nat)
    (tileMass idealTileMass : Fin tiles -> Nat)
    (tag : Fin tiles -> Prod Col (Fin ports) -> J)
    (hports : 0 < ports)
    (hm : m <= 4096)
    (hfirst : forall t, bounds t 0 = 0)
    (hlast : forall t, bounds t (Fin.last ports) = 64 * m)
    (hmono : forall t, forall i : Fin ports,
      bounds t (Fin.castSucc i) <= bounds t (Fin.succ i))
    (hH : forall t, tileMass t <= 262144)
    (hI : forall t, idealTileMass t <= 262144)
    (hinput : forall t c, sourceHeight t c <= m)
    (hHsum : forall t, tileMass t = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle (sourceHeight t) c)
    (hOutputTiles : outputTiles = 2 * tiles)
    (hMacroParent : (Finset.univ.sum fun t : Fin tiles =>
      countDistance (tileMass t) (idealTileMass t)) <= 512 * tiles) :
    (Finset.univ.sum fun j : J =>
      countDistance
        (variableTileGroupedActual m bounds sourceHeight tag j)
        (variableTileGroupedIdeal m bounds idealTileMass tag j)) <=
      512 * outputTiles := by
  have hstep := variable_tile_physical_profile_error_le_parent_add_448
    m bounds sourceHeight tileMass idealTileMass tag (512 * tiles)
    hports hm hfirst hlast hmono hH hI hinput hHsum hMacroParent
  rw [hOutputTiles]
  calc
    _ <= 512 * tiles + 448 * tiles := hstep
    _ <= 512 * tiles + 512 * tiles := by omega
    _ = 512 * (2 * tiles) := by ring

end Chvatal.D2VariableTilePhysicalFlowTransfer
