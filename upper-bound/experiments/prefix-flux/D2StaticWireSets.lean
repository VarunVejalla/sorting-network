import D2OrdinaryRankRouting
import AKS.Chvatal.ExecPlacement

namespace Chvatal.D2StaticWireSets

open Chvatal
open Chvatal.D2Reserve
open Chvatal.D2OrdinaryRankRouting

/-- Static addresses in the half-open interval `[lo, hi)`. -/
def staticWireInterval {n : Nat} (lo hi : Nat) : Finset (Fin n) :=
  Finset.univ.filter fun w => lo ≤ w.val ∧ w.val < hi

theorem staticWireInterval_card {n lo hi : Nat} (hhi : hi ≤ n) :
    (staticWireInterval (n := n) lo hi).card = hi - lo := by
  classical
  by_cases hn : 0 < n
  · let embed (x : Nat) : Fin n := ⟨x % n, Nat.mod_lt _ hn⟩
    have himage : (Finset.Ico lo hi).image embed =
        staticWireInterval (n := n) lo hi := by
      ext w
      simp only [Finset.mem_image, Finset.mem_Ico, staticWireInterval,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨x, ⟨hlo, hhi'⟩, rfl⟩
        have hx : x < n := lt_of_lt_of_le hhi' hhi
        have hembed : embed x = (⟨x, hx⟩ : Fin n) := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt hx
        rw [hembed]
        exact ⟨hlo, hhi'⟩
      · rintro ⟨hlo, hhi'⟩
        refine ⟨w.val, ⟨hlo, hhi'⟩, ?_⟩
        apply Fin.ext
        exact Nat.mod_eq_of_lt (lt_of_lt_of_le hhi' hhi)
    rw [← himage, Finset.card_image_of_injOn (f := embed)
      (s := Finset.Ico lo hi) (by
        intro a ha b hb hab
        have ha' := (Finset.mem_Ico.mp ha).2
        have hb' := (Finset.mem_Ico.mp hb).2
        have hv := congrArg Fin.val hab
        change a % n = b % n at hv
        rw [Nat.mod_eq_of_lt (lt_of_lt_of_le ha' hhi),
          Nat.mod_eq_of_lt (lt_of_lt_of_le hb' hhi)] at hv
        exact hv)]
    rw [Nat.card_Ico]
  · have hn0 : n = 0 := by omega
    subst n
    have hi0 : hi = 0 := by omega
    subst hi
    simp [staticWireInterval]

/-- A 4096-wire rank fragment that intersects every aligned static cell in
either none or all of that cell must itself be exactly one static cell. -/
theorem rankFragment_eq_staticCell_of_wholeCell_intersections
    {n : Nat} (S : Finset (Fin n)) (hn : 4096 ∣ n)
    (hcard : S.card = 4096)
    (hwhole : ∀ lo, 4096 ∣ lo → lo + 4096 ≤ n →
      S ∩ staticWireInterval lo (lo + 4096) = ∅ ∨
        S ∩ staticWireInterval lo (lo + 4096) =
          staticWireInterval lo (lo + 4096)) :
    ∃ lo, 4096 ∣ lo ∧ lo + 4096 ≤ n ∧
      S = staticWireInterval lo (lo + 4096) := by
  classical
  have hnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨w, hw⟩ := hnonempty
  let lo := (w.val / 4096) * 4096
  have hmod : w.val % 4096 < 4096 := Nat.mod_lt _ (by norm_num)
  have hdecomp : w.val % 4096 + lo = w.val := by
    dsimp [lo]
    omega
  have hlo : 4096 ∣ lo := by
    refine ⟨w.val / 4096, ?_⟩
    dsimp [lo]
    omega
  have hloLE : lo ≤ w.val := by
    rw [← hdecomp]
    omega
  have hwLT : w.val < lo + 4096 := by
    rw [← hdecomp]
    omega
  have hhi : lo + 4096 ≤ n := by
    rcases hn with ⟨m, hm⟩
    have hwN : w.val < 4096 * m := by omega
    rcases hlo with ⟨k, hk⟩
    rw [hk]
    omega
  have hwcell : w ∈ staticWireInterval lo (lo + 4096) := by
    simp only [staticWireInterval, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨hloLE, hwLT⟩
  have hinter : S ∩ staticWireInterval lo (lo + 4096) ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨w, Finset.mem_inter.mpr ⟨hw, hwcell⟩⟩
  rcases hwhole lo hlo hhi with hempty | hfull
  · exact (hinter hempty).elim
  · have hsub : staticWireInterval lo (lo + 4096) ⊆ S := by
      intro x hx
      have hx' : x ∈ S ∩ staticWireInterval lo (lo + 4096) := by
        rw [hfull]
        exact hx
      exact (Finset.mem_inter.mp hx').1
    have hcellCard : (staticWireInterval (n := n) lo (lo + 4096)).card = 4096 := by
      rw [staticWireInterval_card hhi]
      omega
    have heq : staticWireInterval lo (lo + 4096) = S :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcellCard])
    exact ⟨lo, hlo, hhi, heq.symm⟩

theorem rankIn_univ_eq_val {n : Nat} (w : Fin n) :
    Chvatal.rankIn Finset.univ w = w.val := by
  classical
  change (Finset.univ.filter (fun x : Fin n => x < w)).card = w.val
  rw [← Finset.card_subtype]
  have huniv : Finset.univ.subtype (fun x : Fin n => x < w) =
      (Finset.univ : Finset {x : Fin n // x < w}) := by
    ext x
    simp only [Finset.mem_subtype, Finset.mem_univ]
  rw [huniv, Finset.card_univ]
  let e : {x : Fin n // x < w} ≃ Fin w.val :=
    { toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun y => ⟨⟨y.val, Nat.lt_trans y.isLt w.isLt⟩, y.isLt⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro y; apply Fin.ext; rfl }
  simpa using Fintype.card_congr e

/-- `orderEmbOfFin` is the rank-to-address map for any finite sender set. -/
theorem rankIn_orderEmbOfFin {n : Nat} (s : Finset (Fin n))
    (c : Fin s.card) :
    Chvatal.rankIn s (s.orderEmbOfFin rfl c) = c.val := by
  exact Chvatal.rankIn_orderEmb c

/-- The wires in a rank interval of a sender, used for the sender's fixed-size
physical tiles. -/
def rankChunk {n : Nat} (sender : Finset (Fin n))
    (chunkSize index : Nat) : Finset (Fin n) :=
  Chvatal.blockOf sender (index * chunkSize) ((index + 1) * chunkSize)

private theorem rank_order_reflects_address {n : Nat}
    (sender : Finset (Fin n)) {a b : Fin n}
    (hb : b ∈ sender)
    (hrank : Chvatal.rankIn sender a < Chvatal.rankIn sender b) :
    a.val < b.val := by
  by_contra h
  have hba : b.val ≤ a.val := by omega
  by_cases heq : b.val = a.val
  · have hab : b = a := Fin.ext heq
    subst b
    omega
  · have hlt : b.val < a.val := by omega
    have hrev := Chvatal.rankIn_lt_rankIn hb (Fin.lt_def.mpr hlt)
    omega

/-- Among disjoint consecutive rank chunks of any sender, at most one chunk
can contain wires on both sides of a fixed physical-address prefix. -/
theorem rankChunks_at_most_one_crossing_prefix
    {n count chunkSize cut : Nat} (sender : Finset (Fin n)) :
    (Finset.univ.filter fun i : Fin count =>
      (∃ a ∈ rankChunk sender chunkSize i.val, a.val < cut) ∧
      (∃ b ∈ rankChunk sender chunkSize i.val, cut ≤ b.val)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  rcases hi with ⟨⟨a, ha, haCut⟩, ⟨b, hb, hbCut⟩⟩
  rcases hj with ⟨⟨c, hc, hcCut⟩, ⟨d, hd, hdCut⟩⟩
  by_contra hne
  have hval : i.val ≠ j.val := by
    intro heq
    apply hne
    exact Fin.ext heq
  rcases lt_or_gt_of_ne hval with hij | hji
  · have hbi := (Chvatal.mem_blockOf.mp hb).2.2
    have hci := (Chvatal.mem_blockOf.mp hc).2.1
    have hbetween : (i.val + 1) * chunkSize ≤ j.val * chunkSize := by
      have hstep : i.val + 1 ≤ j.val := by omega
      exact Nat.mul_le_mul_right chunkSize hstep
    have hbrank : Chvatal.rankIn sender b < (i.val + 1) * chunkSize := by
      simpa [rankChunk] using hbi
    have hcrank : j.val * chunkSize ≤ Chvatal.rankIn sender c := by
      simpa [rankChunk] using hci
    have hordered : Chvatal.rankIn sender b < Chvatal.rankIn sender c := by omega
    have hbc := rank_order_reflects_address sender (Chvatal.mem_blockOf.mp hc).1
      hordered
    omega
  · have hdj := (Chvatal.mem_blockOf.mp hd).2.2
    have hai := (Chvatal.mem_blockOf.mp ha).2.1
    have hbetween : (j.val + 1) * chunkSize ≤ i.val * chunkSize := by
      have hstep : j.val + 1 ≤ i.val := by omega
      exact Nat.mul_le_mul_right chunkSize hstep
    have hdrank : Chvatal.rankIn sender d < (j.val + 1) * chunkSize := by
      simpa [rankChunk] using hdj
    have hairank : i.val * chunkSize ≤ Chvatal.rankIn sender a := by
      simpa [rankChunk] using hai
    have hordered : Chvatal.rankIn sender d < Chvatal.rankIn sender a := by omega
    have hda := rank_order_reflects_address sender (Chvatal.mem_blockOf.mp ha).1
      hordered
    omega

/-- Ranking the complete wire universe by address turns a rank block into
the corresponding static address interval. -/
theorem blockOf_univ_eq_staticWireInterval {n : Nat} (lo hi : Nat) :
    Chvatal.blockOf (Finset.univ : Finset (Fin n)) lo hi =
      staticWireInterval lo hi := by
  ext w
  simp [staticWireInterval, Chvatal.mem_blockOf, rankIn_univ_eq_val]

/-- In a contiguous address interval, the rank of a wire is its offset from
the left endpoint. -/
theorem rankIn_staticWireInterval {n lo hi : Nat}
    {w : Fin n} (hw : w.val < hi) :
    Chvatal.rankIn (staticWireInterval lo hi) w = w.val - lo := by
  classical
  unfold Chvatal.rankIn staticWireInterval
  have hn : 0 < n := by omega
  let embed (x : Nat) : Fin n := ⟨x % n, Nat.mod_lt _ hn⟩
  have himage :
      (Finset.univ.filter (fun x : Fin n => lo ≤ x.val ∧ x.val < hi)).filter
          (fun x => x < w) =
        (Finset.Ico lo w.val).image (fun x : Nat => embed x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hxl, hxh⟩, hxw⟩
      refine ⟨x.val, ⟨?_, ?_⟩, ?_⟩
      · exact hxl
      · simpa using hxw
      · apply Fin.ext
        change x.val % n = x.val
        exact Nat.mod_eq_of_lt (by omega : x.val < n)
    · rintro ⟨y, ⟨hyl, hyw⟩, hEq⟩
      have hyN : y < n := by omega
      have hEmbed : embed y = (⟨y, hyN⟩ : Fin n) := by
        apply Fin.ext
        change y % n = y
        exact Nat.mod_eq_of_lt hyN
      have hEmbedVal : (embed y).val = y := by
        dsimp [embed]
        exact Nat.mod_eq_of_lt hyN
      refine ⟨?_, ?_⟩
      · rw [← hEq]
        rw [hEmbedVal]
        exact ⟨hyl, by omega⟩
      · rw [← hEq]
        rw [hEmbed]
        simpa using hyw
  rw [himage, Finset.card_image_of_injOn (f := embed) (s := Finset.Ico lo w.val)
    (by
      intro a ha b hb hab
      have ha' := (Finset.mem_Ico.mp ha).2
      have hb' := (Finset.mem_Ico.mp hb).2
      have hv := congrArg Fin.val hab
      change a % n = b % n at hv
      rw [Nat.mod_eq_of_lt (by omega : a < n),
        Nat.mod_eq_of_lt (by omega : b < n)] at hv
      exact hv)]
  rw [Nat.card_Ico]

/-- Two disjoint address intervals, listed in increasing wire order. -/
def staticWirePair {n : Nat} (lo₁ hi₁ lo₂ hi₂ : Nat) : Finset (Fin n) :=
  staticWireInterval lo₁ hi₁ ∪ staticWireInterval lo₂ hi₂

/-- On the first component of an ordered two-interval sender, global rank is
the same as rank within that component. -/
theorem rankIn_staticWirePair_left {n lo₁ hi₁ lo₂ hi₂ : Nat}
    (horder : hi₁ ≤ lo₂) (w : Fin n)
    (hhi : w.val < hi₁) :
    Chvatal.rankIn (staticWirePair (n := n) lo₁ hi₁ lo₂ hi₂) w =
      w.val - lo₁ := by
  classical
  have hsecond :
      (staticWireInterval (n := n) lo₂ hi₂).filter (fun x => x < w) = ∅ := by
    ext x
    simp only [staticWireInterval, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hlt⟩
      omega
    · simp
  rw [Chvatal.rankIn, staticWirePair, Finset.filter_union, hsecond,
    Finset.union_empty]
  exact rankIn_staticWireInterval (n := n) (lo := lo₁) (hi := hi₁) hhi

/-- On the second component, the first interval contributes its full length
to the local rank offset. -/
theorem rankIn_staticWirePair_right {n lo₁ hi₁ lo₂ hi₂ : Nat}
    (horder : hi₁ ≤ lo₂) (hcap : hi₁ ≤ n) (w : Fin n)
    (hlo : lo₂ ≤ w.val) (hhi : w.val < hi₂) :
    Chvatal.rankIn (staticWirePair (n := n) lo₁ hi₁ lo₂ hi₂) w =
      (hi₁ - lo₁) + (w.val - lo₂) := by
  classical
  have hfirst :
      (staticWireInterval (n := n) lo₁ hi₁).filter (fun x => x < w) =
        staticWireInterval (n := n) lo₁ hi₁ := by
    ext x
    simp only [Finset.mem_filter, staticWireInterval, Finset.mem_univ,
      true_and]
    constructor
    · exact And.left
    · intro hx
      refine ⟨hx, ?_⟩
      omega
  have hdisj : Disjoint (staticWireInterval (n := n) lo₁ hi₁)
      ((staticWireInterval (n := n) lo₂ hi₂).filter (fun x => x < w)) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [Finset.mem_filter] at hxB
    simp only [staticWireInterval, Finset.mem_filter, Finset.mem_univ,
      true_and] at hxA hxB
    omega
  rw [Chvatal.rankIn, staticWirePair, Finset.filter_union, hfirst,
    Finset.card_union_of_disjoint hdisj]
  rw [staticWireInterval_card hcap]
  have htail := rankIn_staticWireInterval (n := n) (lo := lo₂) (hi := hi₂) hhi
  simpa [Chvatal.rankIn] using congrArg (fun z => (hi₁ - lo₁) + z) htail

/-- The earlier ordered component contributes no ranks below a point in the
later component. The components need not themselves be intervals. -/
theorem rankIn_union_ordered_left {n : Nat} (s t : Finset (Fin n))
    (horder : ∀ a ∈ s, ∀ b ∈ t, a < b) {w : Fin n} (hw : w ∈ s) :
    Chvatal.rankIn (s ∪ t) w = Chvatal.rankIn s w := by
  classical
  unfold Chvatal.rankIn
  rw [Finset.filter_union]
  have ht : t.filter (fun x => x < w) = ∅ := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hxt, hxw⟩
      exact False.elim ((not_lt_of_ge (le_of_lt (horder w hw x hxt))) hxw)
    · intro hx
      simp at hx
  rw [ht, Finset.union_empty]

/-- The earlier ordered component contributes no ranks below a point in the
 later component. The components need not themselves be intervals. -/
theorem rankIn_union_ordered_right {n : Nat} (s t : Finset (Fin n))
    (horder : ∀ a ∈ s, ∀ b ∈ t, a < b) {w : Fin n} (hw : w ∈ t) :
    Chvatal.rankIn (s ∪ t) w = s.card + Chvatal.rankIn t w := by
  classical
  unfold Chvatal.rankIn
  rw [Finset.filter_union]
  have hs : s.filter (fun x => x < w) = s := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · exact And.left
    · intro hx
      exact ⟨hx, horder x hx w hw⟩
  have hdisj : Disjoint s (t.filter (fun x => x < w)) := by
    rw [Finset.disjoint_left]
    intro x hxs hxt
    simp only [Finset.mem_filter] at hxt
    exact (lt_irrefl x (horder x hxs x hxt.1))
  rw [hs, Finset.card_union_of_disjoint hdisj]

/-- An ordered union of two finite components can be sliced in global rank by
splitting at the size of the first component. This applies recursively to
static bags represented as a bounded list of ordered wire intervals. -/
theorem blockOf_union_ordered {n : Nat} (s t : Finset (Fin n))
    (horder : ∀ a ∈ s, ∀ b ∈ t, a < b) (start stop : Nat) :
    Chvatal.blockOf (s ∪ t) start stop =
      Chvatal.blockOf s start (min stop s.card) ∪
        Chvatal.blockOf t (start - s.card) (stop - s.card) := by
  classical
  ext w
  simp only [Chvatal.mem_blockOf, Finset.mem_union]
  by_cases hws : w ∈ s
  · have hwt : w ∉ t := by
      intro h
      exact lt_irrefl w (horder w hws w h)
    have hglobal : Chvatal.rankIn (s ∪ t) w = Chvatal.rankIn s w := by
      unfold Chvatal.rankIn
      rw [Finset.filter_union]
      have hfilter : t.filter (fun x => x < w) = ∅ := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_filter.mp hx with ⟨hxt, hxw⟩
          exact False.elim ((not_lt_of_ge (le_of_lt (horder w hws x hxt))) hxw)
        · intro h
          simp at h
      rw [hfilter, Finset.union_empty]
    have hbelow : Chvatal.rankIn s w < s.card := Chvatal.rankIn_lt_card hws
    simp only [hws, hwt, true_or, true_and, false_and, hglobal]
    simp only [or_false]
    constructor
    · rintro ⟨hstart, hstop⟩
      exact ⟨hstart, lt_min hstop hbelow⟩
    · rintro ⟨hstart, hstop⟩
      exact ⟨hstart, lt_of_lt_of_le hstop (min_le_left _ _)⟩
  · by_cases hwt : w ∈ t
    · have hglobal : Chvatal.rankIn (s ∪ t) w =
          s.card + Chvatal.rankIn t w :=
        rankIn_union_ordered_right s t horder hwt
      have hws' : w ∉ s := hws
      simp only [hws', hwt, false_or, true_and, false_and, hglobal]
      constructor
      · rintro ⟨hstart, hstop⟩
        exact ⟨by omega, by omega⟩
      · rintro ⟨hstart, hstop⟩
        exact ⟨by omega, by omega⟩
    · simp only [hws, hwt, false_or, false_and]

/-- The address set represented by an ordered list of disjoint wire runs. -/
def orderedRunUnion {n : Nat} : List (Finset (Fin n)) → Finset (Fin n)
  | [] => ∅
  | s :: runs => s ∪ orderedRunUnion runs

/-- The rank slice on each component of an ordered run list, with each
component's slice translated by the total sizes of the preceding runs. -/
def orderedRunSlice {n : Nat} : List (Finset (Fin n)) → Nat → Nat → Finset (Fin n)
  | [], _, _ => ∅
  | s :: runs, start, stop =>
      Chvatal.blockOf s start (min stop s.card) ∪
        orderedRunSlice runs (start - s.card) (stop - s.card)

/-- Intersecting a rank slice of an ordered run list with an address cell
distributes over its per-run fragments. -/
theorem orderedRunSlice_inter_cell_cons {n : Nat}
    (s : Finset (Fin n)) (runs : List (Finset (Fin n)))
    (start stop cellLo cellHi : Nat) :
    orderedRunSlice (s :: runs) start stop ∩
        staticWireInterval cellLo cellHi =
      (Chvatal.blockOf s start (min stop s.card) ∩
          staticWireInterval cellLo cellHi) ∪
        (orderedRunSlice runs (start - s.card) (stop - s.card) ∩
          staticWireInterval cellLo cellHi) := by
  simp only [orderedRunSlice, Finset.union_inter_distrib_right]

/-- Every run precedes all later runs in address order. -/
def OrderedRuns {n : Nat} : List (Finset (Fin n)) → Prop
  | [] => True
  | s :: runs =>
      (∀ a ∈ s, ∀ b ∈ orderedRunUnion runs, a < b) ∧ OrderedRuns runs

/-- Rank in an ordered wire-run union is the local rank in the containing
run plus the sizes of the earlier runs. This identifies exact core-output
indices for the physical address fragments. -/
theorem rankIn_orderedRunUnion_cons {n : Nat}
    (s : Finset (Fin n)) (runs : List (Finset (Fin n)))
    (hordered : OrderedRuns (s :: runs)) {w : Fin n}
    (hw : w ∈ orderedRunUnion (s :: runs)) :
    Chvatal.rankIn (orderedRunUnion (s :: runs)) w =
      if w ∈ s then Chvatal.rankIn s w
      else s.card + Chvatal.rankIn (orderedRunUnion runs) w := by
  change w ∈ s ∪ orderedRunUnion runs at hw
  rcases hordered with ⟨horder, _⟩
  by_cases hws : w ∈ s
  · simp only [if_pos hws]
    exact rankIn_union_ordered_left s (orderedRunUnion runs) horder hws
  · have hwt : w ∈ orderedRunUnion runs := (Finset.mem_union.mp hw).resolve_left hws
    simp only [if_neg hws]
    exact rankIn_union_ordered_right s (orderedRunUnion runs) horder hwt

/-- A rank slice of a finite ordered run list is the union of its component
slices. In particular, this applies to the D2 bags' at-most-nine wire runs. -/
theorem blockOf_orderedRuns {n : Nat} (runs : List (Finset (Fin n)))
    (hordered : OrderedRuns runs) (start stop : Nat) :
    Chvatal.blockOf (orderedRunUnion runs) start stop =
      orderedRunSlice runs start stop := by
  induction runs generalizing start stop with
  | nil =>
      simp [orderedRunUnion, orderedRunSlice, Chvatal.blockOf, Chvatal.rankIn]
  | cons s runs ih =>
      rcases hordered with ⟨hhead, htail⟩
      simp only [orderedRunUnion, orderedRunSlice]
      rw [blockOf_union_ordered s (orderedRunUnion runs) hhead start stop]
      rw [ih htail]

/-- The occupied child intervals in one native parent interval. -/
def staticHoleUnion {n : Nat} : List (Nat × Nat) → Finset (Fin n)
  | [] => ∅
  | (lo, hi) :: holes =>
      staticWireInterval lo hi ∪ staticHoleUnion holes

/-- The complementary runs obtained by scanning the holes from left to right.
Empty runs are retained, which makes the run count exactly one more than the
number of listed holes. -/
def staticGapRuns {n : Nat} : Nat → List (Nat × Nat) → Nat → List (Finset (Fin n))
  | cursor, [], stop => [staticWireInterval cursor stop]
  | cursor, (lo, hi) :: holes, stop =>
      staticWireInterval cursor lo :: staticGapRuns hi holes stop

theorem staticGapRuns_length {n : Nat} (cursor stop : Nat)
    (holes : List (Nat × Nat)) :
    (staticGapRuns (n := n) cursor holes stop).length = holes.length + 1 := by
  induction holes generalizing cursor with
  | nil => simp [staticGapRuns]
  | cons hole holes ih => simp [staticGapRuns, ih]

/-- Each hole is contained in the remaining parent interval, and holes are
listed in nonoverlapping address order. -/
def StaticHolesFit : Nat → List (Nat × Nat) → Nat → Prop
  | cursor, [], stop => cursor ≤ stop
  | cursor, (lo, hi) :: holes, stop =>
      cursor ≤ lo ∧ lo ≤ hi ∧ hi ≤ stop ∧ StaticHolesFit hi holes stop

/-- Convert a fixed-length family of interval endpoints to the ordered list
used by `StaticHolesFit`. -/
def staticHoleList : (m : Nat) → (Fin m → Nat) → (Fin m → Nat) → List (Nat × Nat)
  | 0, _, _ => []
  | m + 1, lo, hi =>
      (lo ⟨0, by omega⟩, hi ⟨0, by omega⟩) ::
        staticHoleList m (fun j => lo j.succ) (fun j => hi j.succ)

theorem staticHoleList_fits {m : Nat} (cursor stop : Nat)
    (lo hi : Fin m → Nat)
    (hparent : cursor ≤ stop)
    (hstart : ∀ j, cursor ≤ lo j)
    (hwidth : ∀ j, lo j ≤ hi j)
    (hend : ∀ j, hi j ≤ stop)
    (hordered : ∀ i j, i.val < j.val → hi i ≤ lo j) :
    StaticHolesFit cursor (staticHoleList m lo hi) stop := by
  induction m generalizing cursor with
  | zero => simpa [staticHoleList, StaticHolesFit] using hparent
  | succ m ih =>
      let first : Fin (m + 1) := ⟨0, by omega⟩
      have htail : StaticHolesFit (hi first)
          (staticHoleList m (fun j => lo j.succ) (fun j => hi j.succ)) stop := by
        apply ih (cursor := hi first)
        · exact hend first
        · intro j
          exact hordered first j.succ (by simp [first])
        · intro j
          exact hwidth j.succ
        · intro j
          exact hend j.succ
        · intro i j hij
          exact hordered i.succ j.succ (by simpa using hij)
      have hhead : cursor ≤ lo first ∧ lo first ≤ hi first ∧ hi first ≤ stop :=
        ⟨hstart first, hwidth first, hend first⟩
      simpa [staticHoleList, StaticHolesFit, first] using
        (show cursor ≤ lo first ∧ lo first ≤ hi first ∧ hi first ≤ stop ∧
          StaticHolesFit (hi first)
            (staticHoleList m (fun j => lo j.succ) (fun j => hi j.succ)) stop
          from ⟨hhead.1, hhead.2.1, hhead.2.2, htail⟩)

/-- Child holes contained in ordered native slots are automatically an
ordered hole list. This isolates the parent-containment obligation from the
routine ordering of the eight child slots. -/
theorem staticHoleList_fits_of_slots {m : Nat} (cursor stop : Nat)
    (lo hi slotLo slotHi : Fin m → Nat) (hparent : cursor ≤ stop)
    (hcontainLo : ∀ j, cursor ≤ lo j)
    (hwidth : ∀ j, lo j ≤ hi j)
    (hcontainHi : ∀ j, hi j ≤ stop)
    (hslotLo : ∀ j, slotLo j ≤ lo j)
    (hslotHi : ∀ j, hi j ≤ slotHi j)
    (hslots : ∀ i j, i.val < j.val → slotHi i ≤ slotLo j) :
    StaticHolesFit cursor (staticHoleList m lo hi) stop := by
  apply staticHoleList_fits cursor stop lo hi hparent hcontainLo hwidth hcontainHi
  intro i j hij
  exact le_trans (hslotHi i) (le_trans (hslots i j hij) (hslotLo j))

/-- For eight equal native child slots, containment of the two endpoint
children plus a parent fringe shorter than one slot forces containment of all
child intervals. The ordinary D2 cut equations make the endpoint conditions
equalities when the two fronts fit. -/
theorem d2EightChildHolesFit {base width left right : Nat}
    (lo hi : Fin 8 → Nat)
    (hleft : left ≤ width) (hright : right ≤ width)
    (hparent : base + left ≤ base + 8 * width - right)
    (hslots : ∀ j, base + j.val * width ≤ lo j ∧ lo j ≤ hi j ∧
      hi j ≤ base + (j.val + 1) * width)
    (hfirst : base + left ≤ lo ⟨0, by omega⟩)
    (hlast : hi ⟨7, by omega⟩ ≤ base + 8 * width - right) :
    StaticHolesFit (base + left)
      (staticHoleList 8 lo hi) (base + 8 * width - right) := by
  apply staticHoleList_fits_of_slots (base + left)
    (base + 8 * width - right) lo hi
    (fun j => base + j.val * width)
    (fun j => base + (j.val + 1) * width)
    hparent
  · intro j
    by_cases hj : j.val = 0
    · have hjEq : j = ⟨0, by omega⟩ := Fin.ext hj
      rw [hjEq]
      exact hfirst
    · have hjpos : 1 ≤ j.val := by omega
      have hbase : base + left ≤ base + j.val * width := by
        have hmul := Nat.mul_le_mul_right width hjpos
        omega
      exact le_trans hbase (hslots j).1
  · intro j
    exact (hslots j).2.1
  · intro j
    by_cases hj : j.val = 7
    · have hjEq : j = ⟨7, by omega⟩ := Fin.ext hj
      rw [hjEq]
      exact hlast
    · have hjend : j.val + 1 ≤ 7 := by omega
      have hmul := Nat.mul_le_mul_right width hjend
      have hslot := (hslots j).2.2
      omega
  · intro j
    exact (hslots j).1
  · intro j
    exact (hslots j).2.2
  · intro i j hij
    have hindex : i.val + 1 ≤ j.val := by omega
    have hmul := Nat.mul_le_mul_right width hindex
    omega

/-- Address interval for one child subtree. Saturated children have no
occupied interval; assigning them a point at the parent edge keeps them in the
ordered hole list without changing its set union. -/
def d2EightChildHole (base width left right : Nat)
    (deficit low high : Fin 8 → Nat) (j : Fin 8) : Nat × Nat :=
  if deficit j = width then
    if j.val = 0 then (base + left, base + left)
    else if j.val = 7 then
      (base + 8 * width - right, base + 8 * width - right)
    else (base + j.val * width, base + j.val * width)
  else
    (base + j.val * width + low j,
      base + (j.val + 1) * width - high j)

theorem d2EightChildHole_within_slot {base width left right : Nat}
    (deficit low high : Fin 8 → Nat) (hleft : left ≤ width)
    (hright : right ≤ width) (j : Fin 8)
    (hcap : deficit j ≤ width)
    (hbalance : deficit j < width → low j + high j = deficit j) :
    base + j.val * width ≤ (d2EightChildHole base width left right
        deficit low high j).1 ∧
      (d2EightChildHole base width left right deficit low high j).1 ≤
        (d2EightChildHole base width left right deficit low high j).2 ∧
      (d2EightChildHole base width left right deficit low high j).2 ≤
        base + (j.val + 1) * width := by
  by_cases hsat : deficit j = width
  · by_cases hj0 : j.val = 0
    · simp [d2EightChildHole, hsat, hj0]
      omega
    · by_cases hj7 : j.val = 7
      · simp [d2EightChildHole, hsat, hj7]
        omega
      · have hjpos : 1 ≤ j.val := by omega
        have hjmul : width ≤ j.val * width := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_right width hjpos
        have hnext : j.val * width ≤ (j.val + 1) * width := by
          have h := Nat.mul_le_mul_right width (Nat.le_succ j.val)
          simpa [Nat.succ_eq_add_one] using h
        simp [d2EightChildHole, hsat, hj0, hj7]
        omega
  · have hlt : deficit j < width := by omega
    have hbal := hbalance hlt
    have hlow : low j ≤ deficit j := by omega
    have hhigh : high j ≤ deficit j := by omega
    have hsum : low j + high j ≤ width := by omega
    have hnext : (j.val + 1) * width = j.val * width + width := by
      rw [Nat.add_mul, Nat.one_mul]
    have hslotbase : base + j.val * width ≤ base + j.val * width + low j := by omega
    have hslotend : base + (j.val + 1) * width - high j ≤
        base + (j.val + 1) * width := by omega
    simp [d2EightChildHole, hsat]
    omega

/-- The endpoint reserve inequalities, child native bounds, and balanced
nonsaturated child endpoints imply the full eight-child `StaticHolesFit`
condition. -/
theorem d2EightChildHolesFit_of_child_profile
    {base width left right : Nat}
    (deficit low high : Fin 8 → Nat)
    (hleft : left ≤ width) (hright : right ≤ width)
    (hparent : base + left ≤ base + 8 * width - right)
    (hcap : ∀ j, deficit j ≤ width)
    (hbalance : ∀ j, deficit j < width → low j + high j = deficit j)
    (hfirst : deficit ⟨0, by omega⟩ < width → left ≤ low ⟨0, by omega⟩)
    (hlast : deficit ⟨7, by omega⟩ < width → right ≤ high ⟨7, by omega⟩) :
    StaticHolesFit (base + left)
      (staticHoleList 8
        (fun j => (d2EightChildHole base width left right deficit low high j).1)
        (fun j => (d2EightChildHole base width left right deficit low high j).2))
      (base + 8 * width - right) := by
  apply d2EightChildHolesFit
  · exact hleft
  · exact hright
  · exact hparent
  · intro j
    exact d2EightChildHole_within_slot deficit low high hleft hright j
      (hcap j) (hbalance j)
  · let j0 : Fin 8 := ⟨0, by omega⟩
    change base + left ≤ (d2EightChildHole base width left right deficit low high j0).1
    by_cases hsat : deficit j0 = width
    · have hsat0 : deficit 0 = width := by simpa using hsat
      simp [d2EightChildHole, j0, hsat0]
    · have hlt : deficit j0 < width := by have hc := hcap j0; omega
      have hlt0 : deficit (⟨0, by omega⟩ : Fin 8) < width := by
        simpa [j0] using hlt
      have hlow := hfirst hlt0
      have hlow0 : left ≤ low 0 := by simpa using hlow
      have hneq0 : deficit 0 ≠ width := by
        simpa [j0] using (ne_of_lt hlt)
      simp [d2EightChildHole, j0, hneq0]
      exact hlow0
  · let j7 : Fin 8 := ⟨7, by omega⟩
    change (d2EightChildHole base width left right deficit low high j7).2 ≤
      base + 8 * width - right
    by_cases hsat : deficit j7 = width
    · have hsat7 : deficit 7 = width := by simpa using hsat
      simp [d2EightChildHole, j7, hsat7]
    · have hlt : deficit j7 < width := by have hc := hcap j7; omega
      have hlt7 : deficit (⟨7, by omega⟩ : Fin 8) < width := by
        simpa [j7] using hlt
      have hhigh := hlast hlt7
      have hhigh7 : right ≤ high 7 := by simpa using hhigh
      have hneq7 : deficit 7 ≠ width := by
        simpa [j7] using (ne_of_lt hlt)
      simp [d2EightChildHole, j7, hneq7]
      omega

/-- The concrete two-front D2 cut satisfies the endpoint hypotheses of the
static-hole criterion whenever the left front fits in the first child, the
right tail fits in the last child, and the fronts do not overlap. This is the
local flow-to-address geometry adapter; the schedule must still establish
these three size inequalities and connect the resulting intervals to its
next-stage address map. -/
theorem d2EightChildHolesFit_of_two_front_cut
    {base width left tail : Nat} (sizes : Fin 8 → Nat)
    (hleftWidth : left ≤ width) (htailWidth : tail ≤ width)
    (hparent : base + left ≤ base + 8 * width - tail)
    (hsize : ∀ j, sizes j ≤ width)
    (hfronts : left ≤ d2FlowTotal sizes - tail)
    (hfirst : left ≤ sizes ⟨0, by omega⟩)
    (hlast : tail ≤ sizes ⟨7, by omega⟩) :
    StaticHolesFit (base + left)
      (staticHoleList 8
        (fun j => (d2EightChildHole base width left tail
          (fun k => (d2FlowCutChild (d2FlowPosition sizes k) (sizes k)
            left (d2FlowTotal sizes - tail)).1)
          (fun k => (d2FlowCutChild (d2FlowPosition sizes k) (sizes k)
            left (d2FlowTotal sizes - tail)).2.1)
          (fun k => (d2FlowCutChild (d2FlowPosition sizes k) (sizes k)
            left (d2FlowTotal sizes - tail)).2.2) j).1)
        (fun j => (d2EightChildHole base width left tail
          (fun k => (d2FlowCutChild (d2FlowPosition sizes k) (sizes k)
            left (d2FlowTotal sizes - tail)).1)
          (fun k => (d2FlowCutChild (d2FlowPosition sizes k) (sizes k)
            left (d2FlowTotal sizes - tail)).2.1)
          (fun k => (d2FlowCutChild (d2FlowPosition sizes k) (sizes k)
            left (d2FlowTotal sizes - tail)).2.2) j).2))
      (base + 8 * width - tail) := by
  let cut : Fin 8 → Nat × Nat × Nat := fun j =>
    d2FlowCutChild (d2FlowPosition sizes j) (sizes j)
      left (d2FlowTotal sizes - tail)
  have hcutBalance : ∀ j, (cut j).1 = (cut j).2.1 + (cut j).2.2 := by
    intro j
    simp [cut, d2FlowCutChild]
  have hcutCap : ∀ j, (cut j).1 ≤ width := by
    intro j
    exact d2FlowCutChild_le_native (hsize j) hfronts
  have hfirstCut : (cut ⟨0, by omega⟩).2.1 = left := by
    have hpos := d2FlowPosition_zero sizes
    change d2LeftCut (d2FlowPosition sizes ⟨0, by omega⟩)
      (sizes ⟨0, by omega⟩) left = left
    have hpos' : d2FlowPosition sizes (⟨0, by omega⟩ : Fin 8) = 0 := by
      simpa using hpos
    have hfirst' : left ≤ sizes 0 := by simpa using hfirst
    rw [hpos']
    unfold d2LeftCut
    simp [Nat.min_eq_right hfirst']
  have hlastCut : (cut ⟨7, by omega⟩).2.2 = tail := by
    have hend := d2FlowPosition_last_end sizes
    change d2RightCut (d2FlowPosition sizes ⟨7, by omega⟩)
      (sizes ⟨7, by omega⟩) (d2FlowTotal sizes - tail) = tail
    have hpos : d2FlowPosition sizes ⟨7, by omega⟩ ≤
        d2FlowTotal sizes - tail := by omega
    unfold d2RightCut
    rw [Nat.max_eq_right hpos]
    rw [show d2FlowPosition sizes ⟨7, by omega⟩ +
      sizes ⟨7, by omega⟩ = d2FlowTotal sizes by exact hend]
    omega
  apply d2EightChildHolesFit_of_child_profile
    (deficit := fun j => (cut j).1)
    (low := fun j => (cut j).2.1)
    (high := fun j => (cut j).2.2)
    hleftWidth htailWidth hparent hcutCap (fun j hj => (hcutBalance j).symm)
  · intro _
    rw [hfirstCut]
  · intro _
    rw [hlastCut]

/-- The ordinary-sender invariant's capacity and endpoint reserves imply the
two-front hypotheses needed by the concrete static-address cut lemma. This
packages the local reserve arithmetic with the physical child cut geometry. -/
theorem d2EightChildHolesFit_of_flow_reserves
    {base width G low high pi : Nat} (sizes : Fin 8 → Nat)
    (hbalance : G = low + high)
    (hG : 512 * G ≤ 8 * width)
    (hquota : 256 * pi ≤ 8 * width) (heven : pi % 2 = 0)
    (hleftReserve : 8 * width ≤ 128 * sizes ⟨0, by omega⟩)
    (hrightReserve : 8 * width ≤ 128 * sizes ⟨7, by omega⟩)
    (hsize : ∀ j, sizes j ≤ width) :
    StaticHolesFit (base + low + pi / 2)
      (staticHoleList 8
        (fun j => (d2EightChildHole base width (low + pi / 2)
          (high + pi / 2)
          (fun k => (d2FlowCutChild (d2FlowPosition sizes k) (sizes k)
            (low + pi / 2) (d2FlowTotal sizes - (high + pi / 2))).1)
          (fun k => (d2FlowCutChild (d2FlowPosition sizes k) (sizes k)
            (low + pi / 2) (d2FlowTotal sizes - (high + pi / 2))).2.1)
          (fun k => (d2FlowCutChild (d2FlowPosition sizes k) (sizes k)
            (low + pi / 2) (d2FlowTotal sizes - (high + pi / 2))).2.2) j).1)
        (fun j => (d2EightChildHole base width (low + pi / 2)
          (high + pi / 2)
          (fun k => (d2FlowCutChild (d2FlowPosition sizes k) (sizes k)
            (low + pi / 2) (d2FlowTotal sizes - (high + pi / 2))).1)
          (fun k => (d2FlowCutChild (d2FlowPosition sizes k) (sizes k)
            (low + pi / 2) (d2FlowTotal sizes - (high + pi / 2))).2.1)
          (fun k => (d2FlowCutChild (d2FlowPosition sizes k) (sizes k)
            (low + pi / 2) (d2FlowTotal sizes - (high + pi / 2))).2.2) j).2))
      (base + 8 * width - (high + pi / 2)) := by
  have hlow : low ≤ G := by omega
  have hhigh : high ≤ G := by omega
  have hevenEq : pi = 2 * (pi / 2) := by omega
  have hreserve := d2_endpoint_fronts_fit_of_reserve
    hG hlow hhigh hquota hevenEq hleftReserve hrightReserve
  have hpair : sizes ⟨0, by omega⟩ + sizes ⟨7, by omega⟩ ≤
      d2FlowTotal sizes := by
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({⟨0, by omega⟩, ⟨7, by omega⟩} : Finset (Fin 8)))
      (fun j _ _ => Nat.zero_le (sizes j))
    simpa [d2FlowTotal] using hsum
  have hfrontSum : (low + pi / 2) + (high + pi / 2) ≤
      d2FlowTotal sizes := by
    calc
      _ ≤ sizes ⟨0, by omega⟩ + sizes ⟨7, by omega⟩ := Nat.add_le_add hreserve.1 hreserve.2
      _ ≤ d2FlowTotal sizes := hpair
  have hfronts : low + pi / 2 ≤
      d2FlowTotal sizes - (high + pi / 2) := by omega
  have hleftWidth : low + pi / 2 ≤ width :=
    le_trans hreserve.1 (hsize ⟨0, by omega⟩)
  have htailWidth : high + pi / 2 ≤ width :=
    le_trans hreserve.2 (hsize ⟨7, by omega⟩)
  have hparent : base + (low + pi / 2) ≤
      base + 8 * width - (high + pi / 2) := by
    have hsumWidth : (low + pi / 2) + (high + pi / 2) ≤ 8 * width := by
      calc
        _ ≤ d2FlowTotal sizes := hfrontSum
        _ ≤ 8 * width := by
          unfold d2FlowTotal
          calc
            _ ≤ ∑ _j : Fin 8, width := Finset.sum_le_sum fun j _ => hsize j
            _ = 8 * width := by simp
    omega
  have hfit := d2EightChildHolesFit_of_two_front_cut sizes
    hleftWidth htailWidth hparent hsize hfronts hreserve.1 hreserve.2
  simpa [Nat.add_assoc] using hfit

/-- The actual recursive tree invariant supplies the native child caps, and
the ordinary-sender stage-input contract supplies the reserve inequalities.
Under the scheduled capacity identity `cap i = scale * 8^(h+1)`, the complete
eight-child static-hole fit follows for every active ordinary sender. -/
theorem d2FlowStageInvInputs_static_holes
    {h scale i : Nat} {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {cap : Nat → Nat} (base G low high : Nat)
    (children : Fin 8 → D2FlowTree h)
    (htree : d2FlowTreeInv scale (.node G low high children))
    (hinputs : d2FlowStageInvInputs scale active role quota cap
      (h := h + 1) i (.node G low high children))
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hcapacity : cap i = scale * 8 ^ (h + 1)) :
    StaticHolesFit (base + low + quota i (role i) / 2)
      (staticHoleList 8
        (fun j => (d2EightChildHole base (scale * 8 ^ h)
          (low + quota i (role i) / 2) (high + quota i (role i) / 2)
          (fun k => (d2FlowCutChild (d2FlowPosition
            (fun q => d2FlowTreeRootDeficit (children q)) k)
            (d2FlowTreeRootDeficit (children k)) (low + quota i (role i) / 2)
            (d2FlowTotal (fun q => d2FlowTreeRootDeficit (children q)) -
              (high + quota i (role i) / 2))).1)
          (fun k => (d2FlowCutChild (d2FlowPosition
            (fun q => d2FlowTreeRootDeficit (children q)) k)
            (d2FlowTreeRootDeficit (children k)) (low + quota i (role i) / 2)
            (d2FlowTotal (fun q => d2FlowTreeRootDeficit (children q)) -
              (high + quota i (role i) / 2))).2.1)
          (fun k => (d2FlowCutChild (d2FlowPosition
            (fun q => d2FlowTreeRootDeficit (children q)) k)
            (d2FlowTreeRootDeficit (children k)) (low + quota i (role i) / 2)
            (d2FlowTotal (fun q => d2FlowTreeRootDeficit (children q)) -
              (high + quota i (role i) / 2))).2.2) j).1)
        (fun j => (d2EightChildHole base (scale * 8 ^ h)
          (low + quota i (role i) / 2) (high + quota i (role i) / 2)
          (fun k => (d2FlowCutChild (d2FlowPosition
            (fun q => d2FlowTreeRootDeficit (children q)) k)
            (d2FlowTreeRootDeficit (children k)) (low + quota i (role i) / 2)
            (d2FlowTotal (fun q => d2FlowTreeRootDeficit (children q)) -
              (high + quota i (role i) / 2))).1)
          (fun k => (d2FlowCutChild (d2FlowPosition
            (fun q => d2FlowTreeRootDeficit (children q)) k)
            (d2FlowTreeRootDeficit (children k)) (low + quota i (role i) / 2)
            (d2FlowTotal (fun q => d2FlowTreeRootDeficit (children q)) -
              (high + quota i (role i) / 2))).2.1)
          (fun k => (d2FlowCutChild (d2FlowPosition
            (fun q => d2FlowTreeRootDeficit (children q)) k)
            (d2FlowTreeRootDeficit (children k)) (low + quota i (role i) / 2)
            (d2FlowTotal (fun q => d2FlowTreeRootDeficit (children q)) -
              (high + quota i (role i) / 2))).2.2) j).2))
      (base + 8 * (scale * 8 ^ h) - (high + quota i (role i) / 2)) := by
  have htree' := htree
  simp only [d2FlowTreeInv] at htree'
  have hchildInv : ∀ j, d2FlowTreeInv scale (children j) := htree'.2.2.2
  have hsize : ∀ j, d2FlowTreeRootDeficit (children j) ≤ scale * 8 ^ h := by
    intro j
    exact d2FlowTreeInv_root_native_bound (children j) (hchildInv j)
  have hcapEq : cap i = 8 * (scale * 8 ^ h) := by
    rw [hcapacity, Nat.pow_succ]
    ring
  have hstage := hinputs.2
  simp [ha] at hstage
  cases hrole : role i with
  | topDesc => simp [hrole] at hr
  | botRise => simp [hrole] at hr
  | topRise =>
      simp [hrole] at hstage
      rcases hstage with ⟨hbalance, hG, hquota, _, heven, hleft, hright⟩
      have hG' : 512 * G ≤ 8 * (scale * 8 ^ h) := by
        rw [← hcapEq]
        exact hG
      have hquota' : 256 * quota i .topRise ≤ 8 * (scale * 8 ^ h) := by
        rw [← hcapEq]
        exact hquota
      have hleft' : 8 * (scale * 8 ^ h) ≤
          128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
        rw [← hcapEq]
        exact hleft
      have hright' : 8 * (scale * 8 ^ h) ≤
          128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩) := by
        rw [← hcapEq]
        exact hright
      have hfit := d2EightChildHolesFit_of_flow_reserves
        (sizes := fun j => d2FlowTreeRootDeficit (children j))
        (base := base) (width := scale * 8 ^ h) (G := G)
        (low := low) (high := high) (pi := quota i .topRise)
        hbalance.symm hG' hquota' heven hleft' hright' hsize
      simpa [hrole] using hfit
  | mid =>
      simp [hrole] at hstage
      rcases hstage with ⟨hbalance, hG, hquota, _, heven, hleft, hright⟩
      have hG' : 512 * G ≤ 8 * (scale * 8 ^ h) := by
        rw [← hcapEq]
        exact hG
      have hquota' : 256 * quota i .mid ≤ 8 * (scale * 8 ^ h) := by
        rw [← hcapEq]
        exact hquota
      have hleft' : 8 * (scale * 8 ^ h) ≤
          128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
        rw [← hcapEq]
        exact hleft
      have hright' : 8 * (scale * 8 ^ h) ≤
          128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩) := by
        rw [← hcapEq]
        exact hright
      have hfit := d2EightChildHolesFit_of_flow_reserves
        (sizes := fun j => d2FlowTreeRootDeficit (children j))
        (base := base) (width := scale * 8 ^ h) (G := G)
        (low := low) (high := high) (pi := quota i .mid)
        hbalance.symm hG' hquota' heven hleft' hright' hsize
      simpa [hrole] using hfit
  | botDesc =>
      simp [hrole] at hstage
      rcases hstage with ⟨hbalance, hG, hquota, _, heven, hleft, hright⟩
      have hG' : 512 * G ≤ 8 * (scale * 8 ^ h) := by
        rw [← hcapEq]
        exact hG
      have hquota' : 256 * quota i .botDesc ≤ 8 * (scale * 8 ^ h) := by
        rw [← hcapEq]
        exact hquota
      have hleft' : 8 * (scale * 8 ^ h) ≤
          128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
        rw [← hcapEq]
        exact hleft
      have hright' : 8 * (scale * 8 ^ h) ≤
          128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩) := by
        rw [← hcapEq]
        exact hright
      have hfit := d2EightChildHolesFit_of_flow_reserves
        (sizes := fun j => d2FlowTreeRootDeficit (children j))
        (base := base) (width := scale * 8 ^ h) (G := G)
        (low := low) (high := high) (pi := quota i .botDesc)
        hbalance.symm hG' hquota' heven hleft' hright' hsize
      simpa [hrole] using hfit

theorem staticHoleUnion_lower_bound {n : Nat} (cursor stop : Nat)
    (holes : List (Nat × Nat)) (hfit : StaticHolesFit cursor holes stop)
    {w : Fin n} (hw : w ∈ staticHoleUnion holes) : cursor ≤ w.val := by
  induction holes generalizing cursor with
  | nil => simp [staticHoleUnion] at hw
  | cons hole holes ih =>
      rcases hole with ⟨lo, hi⟩
      rcases hfit with ⟨hcursor, hlohi, hstop, htail⟩
      simp only [staticHoleUnion, Finset.mem_union] at hw
      rcases hw with hw | hw
      · simp only [staticWireInterval, Finset.mem_filter,
          Finset.mem_univ, true_and] at hw
        omega
      · exact le_trans (le_trans hcursor hlohi) (ih hi htail hw)

/-- Removing an ordered family of occupied child intervals from a parent
interval leaves exactly the ordered address runs scanned by `staticGapRuns`.
This is the geometric fact behind the D2 nine-run representation. -/
theorem staticGapRuns_union_eq_complement {n : Nat} (cursor stop : Nat)
    (holes : List (Nat × Nat)) (hfit : StaticHolesFit cursor holes stop) :
    orderedRunUnion (staticGapRuns (n := n) cursor holes stop) =
      staticWireInterval cursor stop \ staticHoleUnion holes := by
  induction holes generalizing cursor with
  | nil =>
      simp [staticGapRuns, staticHoleUnion, orderedRunUnion]
  | cons hole holes ih =>
      rcases hole with ⟨lo, hi⟩
      rcases hfit with ⟨hcursor, hlohi, hstop, htail⟩
      change staticWireInterval cursor lo ∪
          orderedRunUnion (staticGapRuns (n := n) hi holes stop) =
        staticWireInterval cursor stop \ (staticWireInterval lo hi ∪
          staticHoleUnion holes)
      rw [ih hi htail]
      ext w
      by_cases htailMem : w ∈ staticHoleUnion holes
      · have htailLower := staticHoleUnion_lower_bound (n := n) hi stop holes htail htailMem
        simp [htailMem, staticWireInterval]
        omega
      · simp [htailMem, staticWireInterval]
        omega

theorem staticGapRuns_lower_bound {n : Nat} (cursor stop : Nat)
    (holes : List (Nat × Nat)) (hfit : StaticHolesFit cursor holes stop)
    {w : Fin n} (hw : w ∈ orderedRunUnion
      (staticGapRuns (n := n) cursor holes stop)) :
    cursor ≤ w.val := by
  induction holes generalizing cursor with
  | nil =>
      have heq : orderedRunUnion (staticGapRuns (n := n) cursor [] stop) =
          staticWireInterval cursor stop := by
        simp [orderedRunUnion, staticGapRuns]
      rw [heq] at hw
      simp only [staticWireInterval, Finset.mem_filter,
        Finset.mem_univ, true_and] at hw
      exact hw.1
  | cons hole holes ih =>
      rcases hole with ⟨lo, hi⟩
      rcases hfit with ⟨hcursor, hlohi, hstop, htail⟩
      simp only [staticGapRuns, orderedRunUnion, Finset.mem_union] at hw
      rcases hw with hw | hw
      · simp only [staticWireInterval, Finset.mem_filter,
          Finset.mem_univ, true_and] at hw
        exact hw.1
      · exact le_trans (le_trans hcursor hlohi) (ih hi htail hw)

/-- The complementary runs are strictly ordered in wire address. -/
theorem staticGapRuns_ordered {n : Nat} (cursor stop : Nat)
    (holes : List (Nat × Nat)) (hfit : StaticHolesFit cursor holes stop) :
    OrderedRuns (staticGapRuns (n := n) cursor holes stop) := by
  induction holes generalizing cursor with
  | nil => simp [staticGapRuns, OrderedRuns, orderedRunUnion]
  | cons hole holes ih =>
      rcases hole with ⟨lo, hi⟩
      rcases hfit with ⟨hcursor, hlohi, hstop, htail⟩
      change (∀ a ∈ staticWireInterval (n := n) cursor lo,
          ∀ b ∈ orderedRunUnion (staticGapRuns (n := n) hi holes stop), a < b) ∧
        OrderedRuns (staticGapRuns (n := n) hi holes stop)
      constructor
      · intro a ha b hb
        have hblow := staticGapRuns_lower_bound hi stop holes htail hb
        simp only [staticWireInterval, Finset.mem_filter,
          Finset.mem_univ, true_and] at ha
        exact Fin.lt_def.mpr (by omega)
      · exact ih hi htail

/-- A rank slice of the parent interval after removing ordered child
intervals is obtained by slicing its ordered complementary runs. -/
theorem blockOf_staticGapRuns {n : Nat} (cursor stop : Nat)
    (holes : List (Nat × Nat)) (hfit : StaticHolesFit cursor holes stop)
    (start finish : Nat) :
    Chvatal.blockOf
        (staticWireInterval cursor stop \ staticHoleUnion holes) start finish =
      orderedRunSlice (staticGapRuns (n := n) cursor holes stop) start finish := by
  rw [← staticGapRuns_union_eq_complement cursor stop holes hfit]
  exact blockOf_orderedRuns (staticGapRuns cursor holes stop)
    (staticGapRuns_ordered cursor stop holes hfit) start finish

/-- Direct port-slicing interface for a finite family of ordered address
holes, stated by endpoint functions rather than a preconstructed list. -/
theorem blockOf_staticHoleList {n m : Nat} (cursor stop : Nat)
    (lo hi : Fin m → Nat) (hparent : cursor ≤ stop)
    (hstart : ∀ j, cursor ≤ lo j) (hwidth : ∀ j, lo j ≤ hi j)
    (hend : ∀ j, hi j ≤ stop)
    (hordered : ∀ i j, i.val < j.val → hi i ≤ lo j)
    (start finish : Nat) :
    Chvatal.blockOf
        (staticWireInterval cursor stop \ staticHoleUnion (staticHoleList m lo hi))
        start finish =
      orderedRunSlice (staticGapRuns (n := n) cursor
        (staticHoleList m lo hi) stop) start finish := by
  exact blockOf_staticGapRuns cursor stop (staticHoleList m lo hi)
    (staticHoleList_fits cursor stop lo hi hparent hstart hwidth hend hordered)
    start finish

/-- The fragments of an ordered-run rank slice lying in one static address
cell. Each fragment retains its rank offset in the concatenated sender. -/
def orderedRunSliceInCell {n : Nat} : List (Finset (Fin n)) -> Nat -> Nat -> Nat -> Nat -> Finset (Fin n)
  | [], _, _, _, _ => Finset.empty
  | s :: runs, start, finish, cellLo, cellHi =>
      (Chvatal.blockOf s start (min finish s.card) ∩
        staticWireInterval cellLo cellHi) ∪
      orderedRunSliceInCell runs (start - s.card) (finish - s.card) cellLo cellHi

/-- Intersecting an ordered-run rank slice with a static destination cell
distributes exactly over its address fragments. -/
theorem orderedRunSlice_inter_cell {n : Nat} (runs : List (Finset (Fin n)))
    (start finish cellLo cellHi : Nat) :
    orderedRunSlice runs start finish ∩ staticWireInterval cellLo cellHi =
      orderedRunSliceInCell runs start finish cellLo cellHi := by
  induction runs generalizing start finish with
  | nil => rfl
  | cons s runs ih =>
      simp only [orderedRunSlice, orderedRunSliceInCell,
        Finset.union_inter_distrib_right]
      rw [ih]

/-- A D2 sender with ordered child holes can be rank-sliced and split by any
static destination cell in one exact identity. This is the refinement needed
to group local tile-port errors by their next-stage physical addresses. -/
theorem blockOf_staticHoleList_inter_cell {n m : Nat} (cursor stop : Nat)
    (lo hi : Fin m -> Nat) (hparent : cursor <= stop)
    (hstart : forall j, cursor <= lo j) (hwidth : forall j, lo j <= hi j)
    (hend : forall j, hi j <= stop)
    (hordered : forall i j, i.val < j.val -> hi i <= lo j)
    (start finish cellLo cellHi : Nat) :
    Chvatal.blockOf
        (staticWireInterval cursor stop \ staticHoleUnion (staticHoleList m lo hi))
        start finish ∩ staticWireInterval cellLo cellHi =
      orderedRunSliceInCell
        (staticGapRuns (n := n) cursor (staticHoleList m lo hi) stop)
        start finish cellLo cellHi := by
  rw [blockOf_staticHoleList cursor stop lo hi hparent hstart hwidth hend
    hordered start finish]
  exact orderedRunSlice_inter_cell
    (staticGapRuns (n := n) cursor (staticHoleList m lo hi) stop)
    start finish cellLo cellHi

/-- An ordinary D2 child piece cut from a sender with ordered static holes,
intersected with one static destination interval, is exactly the union of its
per-gap-run rank fragments. This composes the flow's concrete rank port with
the static-address representation used by tile/column rebatching. -/
theorem destinationPiece_staticHoleList_child_inter_cell
    {n m ports : Nat} (cursor stop : Nat)
    (lo hi : Fin m -> Nat) (boundary : Nat -> Nat)
    (left rightStart : Nat) (j : Fin ports)
    (hparent : cursor <= stop)
    (hstart : forall k, cursor <= lo k)
    (hwidth : forall k, lo k <= hi k)
    (hend : forall k, hi k <= stop)
    (hordered : forall i k, i.val < k.val -> hi i <= lo k)
    (cellLo cellHi : Nat) :
    ((destinationPiece (ports := ports)
        (staticWireInterval cursor stop \ staticHoleUnion (staticHoleList m lo hi))
        boundary left rightStart (some j)) ∩
      (staticWireInterval cellLo cellHi)) =
      orderedRunSliceInCell
        (staticGapRuns (n := n) cursor (staticHoleList m lo hi) stop)
        (left + boundary j.val) (left + boundary (j.val + 1)) cellLo cellHi := by
  simpa only [destinationPiece] using
    (blockOf_staticHoleList_inter_cell cursor stop lo hi hparent hstart
      hwidth hend hordered (left + boundary j.val)
      (left + boundary (j.val + 1)) cellLo cellHi)

/-- The eight-child address decomposition follows from the native-slot
geometry and the two endpoint containment gates. This is the local bridge
from D2 front-fit facts to rank-sliced physical addresses. -/
theorem d2EightChildBlockOf {n base width left right : Nat}
    (lo hi : Fin 8 → Nat)
    (hleft : left ≤ width) (hright : right ≤ width)
    (hparent : base + left ≤ base + 8 * width - right)
    (hslots : ∀ j, base + j.val * width ≤ lo j ∧ lo j ≤ hi j ∧
      hi j ≤ base + (j.val + 1) * width)
    (hfirst : base + left ≤ lo ⟨0, by omega⟩)
    (hlast : hi ⟨7, by omega⟩ ≤ base + 8 * width - right)
    (start finish : Nat) :
    Chvatal.blockOf
        (staticWireInterval (n := n) (base + left)
          (base + 8 * width - right) \ staticHoleUnion (staticHoleList 8 lo hi))
        start finish =
      orderedRunSlice (staticGapRuns (n := n) (base + left)
        (staticHoleList 8 lo hi) (base + 8 * width - right)) start finish := by
  exact blockOf_staticGapRuns (base + left) (base + 8 * width - right)
    (staticHoleList 8 lo hi)
    (d2EightChildHolesFit lo hi hleft hright hparent hslots hfirst hlast)
    start finish

/-- Rank slicing an ordered pair of address intervals splits at the length of
the first component. This is the two-component case of the address adapter
needed for general D2 bags, which are finite unions of ordered intervals. -/
theorem blockOf_staticWirePair {n lo₁ hi₁ lo₂ hi₂ start stop : Nat}
    (horder : hi₁ ≤ lo₂) (hcap : hi₁ ≤ n) :
    Chvatal.blockOf (staticWirePair (n := n) lo₁ hi₁ lo₂ hi₂) start stop =
      Chvatal.blockOf (staticWireInterval (n := n) lo₁ hi₁) start
          (min stop (hi₁ - lo₁)) ∪
        Chvatal.blockOf (staticWireInterval (n := n) lo₂ hi₂)
          (start - (hi₁ - lo₁)) (stop - (hi₁ - lo₁)) := by
  classical
  let A := staticWireInterval (n := n) lo₁ hi₁
  let B := staticWireInterval (n := n) lo₂ hi₂
  have hcard : A.card = hi₁ - lo₁ := by
    dsimp [A]
    exact staticWireInterval_card (n := n) (lo := lo₁) (hi := hi₁) hcap
  have horder' : ∀ a ∈ A, ∀ b ∈ B, a < b := by
    intro a ha b hb
    simp only [A, B, staticWireInterval, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha hb
    exact Fin.lt_def.mpr (by omega)
  rw [show staticWirePair (n := n) lo₁ hi₁ lo₂ hi₂ = A ∪ B by rfl]
  rw [blockOf_union_ordered A B horder' start stop, hcard]

/-- A rank slice of a contiguous sender interval is the corresponding
translated static-address interval. This is the interval case needed to turn
the next D2 stage's local rank ports into actual wire addresses. -/
theorem blockOf_staticWireInterval {n lo hi start stop : Nat}
    (hlohi : lo ≤ hi) (hstop : stop ≤ hi - lo) :
    Chvatal.blockOf (staticWireInterval (n := n) lo hi) start stop =
      staticWireInterval (n := n) (lo + start) (lo + stop) := by
  ext w
  rw [Chvatal.mem_blockOf]
  constructor
  · rintro ⟨hmem, hranklo, hrankhi⟩
    simp only [staticWireInterval, Finset.mem_filter, Finset.mem_univ,
      true_and] at hmem
    rcases hmem with ⟨hlo, hhi⟩
    have hrank := rankIn_staticWireInterval (n := n) (lo := lo) (hi := hi) hhi
    rw [hrank] at hranklo hrankhi
    simp only [staticWireInterval, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨by omega, by omega⟩
  · intro hmem'
    simp only [staticWireInterval, Finset.mem_filter, Finset.mem_univ,
      true_and] at hmem'
    rcases hmem' with ⟨hlo', hhi'⟩
    have hbound : lo + stop ≤ hi := by omega
    have hw : w.val < hi := lt_of_lt_of_le hhi' hbound
    have hrank := rankIn_staticWireInterval (n := n) (lo := lo) (hi := hi) hw
    refine ⟨?_, ?_, ?_⟩
    · simp only [staticWireInterval, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨by omega, hw⟩
    · rw [hrank]
      omega
    · rw [hrank]
      omega

/-- Intersecting a rank slice of a contiguous sender run with a destination
address cell produces exactly the physical overlap interval. This is the
fragment identity used when a D2 port crosses tile or column boundaries. -/
theorem blockOf_staticWireInterval_intersect_cell
    {n lo hi start stop cellLo cellHi : Nat}
    (hlohi : lo ≤ hi) (hstop : stop ≤ hi - lo) :
    Chvatal.blockOf (staticWireInterval (n := n) lo hi) start stop ∩
        staticWireInterval cellLo cellHi =
      staticWireInterval (max (lo + start) cellLo)
        (min (lo + stop) cellHi) := by
  rw [blockOf_staticWireInterval hlohi hstop]
  ext w
  simp only [staticWireInterval, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hleft, hright⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨hlo', hhi'⟩
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- For an interval sender, a child-tagged routing piece is the corresponding
static interval after translating its local rank endpoints. -/
theorem destinationPiece_interval_child {n lo hi ports : Nat}
    (boundary : Nat → Nat) (left rightStart : Nat) (j : Fin ports)
    (hlohi : lo ≤ hi)
    (hstop : left + boundary (j.val + 1) ≤ hi - lo) :
    destinationPiece (ports := ports)
        (staticWireInterval (n := n) lo hi) boundary left rightStart (some j) =
      staticWireInterval (n := n)
        (lo + left + boundary j.val) (lo + left + boundary (j.val + 1)) := by
  simp only [destinationPiece]
  simpa [Nat.add_assoc] using
    (blockOf_staticWireInterval (n := n) (lo := lo) (hi := hi)
      (start := left + boundary j.val)
      (stop := left + boundary (j.val + 1)) hlohi hstop)

/-- For an interval sender, its two end ports become the corresponding left
and right static intervals. -/
theorem destinationPiece_interval_parent {n lo hi ports : Nat}
    (boundary : Nat → Nat) (left rightStart : Nat)
    (hlohi : lo ≤ hi) (hcapacity : hi ≤ n) (hleft : left ≤ hi - lo) :
    destinationPiece (ports := ports)
        (staticWireInterval (n := n) lo hi) boundary left rightStart none =
      staticWireInterval (n := n) lo (lo + left) ∪
        staticWireInterval (n := n) (lo + rightStart) hi := by
  simp only [destinationPiece]
  have hcard := staticWireInterval_card (n := n) (lo := lo) (hi := hi)
    hcapacity
  rw [blockOf_staticWireInterval hlohi hleft]
  rw [blockOf_staticWireInterval (n := n) (lo := lo) (hi := hi)
    (start := rightStart) (stop := (staticWireInterval (n := n) lo hi).card)
    hlohi (by rw [hcard])]
  rw [hcard, Nat.add_sub_of_le hlohi]
  simp only [Nat.add_zero]

theorem d2FlowRankBoundary_const (width i : Nat) (hi : i ≤ 8) :
    d2FlowRankBoundary (fun _ : Fin 8 => width) i = i * width := by
  induction i with
  | zero => simp [d2FlowRankBoundary, d2FlowPosition_zero]
  | succ i ih =>
      have hlt : i < 8 := by omega
      calc
        d2FlowRankBoundary (fun _ : Fin 8 => width) (i + 1) =
            d2FlowRankBoundary (fun _ : Fin 8 => width) i + width := by
          rw [d2FlowRankBoundary_succ _ i hlt]
        _ = i * width + width := by rw [ih (by omega)]
        _ = (i + 1) * width := by
          simp [Nat.succ_mul, Nat.add_comm]

/-- At the initial top-descending root, each child port is exactly that
child's contiguous static address interval. This verifies the first concrete
address-to-destination instance of the local rank-routing interface. -/
theorem initial_top_desc_child_piece_is_static_interval
    (scale h : Nat) (j : Fin 8) :
    let tree := d2FlowTreeInitial scale (h + 1)
    let children := fun k : Fin 8 => d2FlowTreeChild tree k
    let after := d2FlowStage (fun _ => true) (fun _ => .topDesc)
      (fun _ _ => 0) (h + 1) 0 tree
    let widths : Fin 8 → Nat := fun k =>
      d2FlowTreeRootDeficit (children k) -
        d2FlowTreeRootDeficit (d2FlowTreeChild after k)
    let boundary : Nat → Nat := d2FlowRankBoundary widths
    destinationPiece (ports := 8)
      (Finset.univ : Finset (Fin (scale * 8 ^ (h + 1))))
      boundary 0 (scale * 8 ^ (h + 1)) (some j) =
      staticWireInterval
        (j.val * (scale * 8 ^ h)) ((j.val + 1) * (scale * 8 ^ h)) := by
  dsimp
  have hw : (fun k : Fin 8 =>
      d2FlowTreeRootDeficit
          (d2FlowTreeChild (d2FlowTreeInitial scale (h + 1)) k) -
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage (fun _ => true) (fun _ => .topDesc)
              (fun _ _ => 0) (h + 1) 0 (d2FlowTreeInitial scale (h + 1))) k)) =
      (fun _ : Fin 8 => scale * 8 ^ h) := by
    funext k
    change d2FlowTreeRootDeficit (d2FlowTreeFull scale h) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (fun _ => true) (fun _ => .topDesc)
            (fun _ _ => 0) (h + 1) 0
            (.node 0 0 0 (fun _ => d2FlowTreeFull scale h))) k) = _
    rw [d2FlowStage_topDesc_child_deficit (fun _ => d2FlowTreeFull scale h)
      rfl rfl k]
    simp [d2FlowTreeFull_root_deficit]
  have hb (i : Nat) (hi : i ≤ 8) :
      d2FlowRankBoundary
          (fun k : Fin 8 =>
            d2FlowTreeRootDeficit
                (d2FlowTreeChild (d2FlowTreeInitial scale (h + 1)) k) -
              d2FlowTreeRootDeficit
                (d2FlowTreeChild
                  (d2FlowStage (fun _ => true) (fun _ => .topDesc)
                    (fun _ _ => 0) (h + 1) 0
                    (d2FlowTreeInitial scale (h + 1))) k)) i =
        i * (scale * 8 ^ h) := by
    rw [hw]
    exact d2FlowRankBoundary_const (scale * 8 ^ h) i hi
  simp only [destinationPiece]
  rw [blockOf_univ_eq_staticWireInterval]
  congr 1
  · rw [hb j.val (by omega)]
    simp
  · rw [hb (j.val + 1) (by omega)]
    simp

/-- At one fixed tree level, pairwise disjoint native address intervals have
at most one interval that straddles a given global prefix cut. This isolates
the schedule geometry needed to turn the local boundary-only error charge
into an O(depth) per-stage bound. -/
theorem disjointIntervals_at_most_one_crossing_cut
    {m : Nat} (lo hi : Fin m → Nat) (cut : Nat)
    (hdisjoint : ∀ i j, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i) :
    (Finset.univ.filter fun i : Fin m => lo i < cut ∧ cut < hi i).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hiI j hjJ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiI hjJ
  by_contra hne
  rcases hdisjoint i j hne with hleft | hright
  · omega
  · omega

/-- Summed over tree levels, the crossing-interval count is at most the
number of levels. This is the finite combinatorial bound needed when the
fixed-core prefix error is charged only to boundary-crossing senders. -/
theorem sum_disjointInterval_crossings_le_levels
    {levels nodes : Nat} (lo hi : Fin levels → Fin nodes → Nat) (cut : Nat)
    (hdisjoint : ∀ ℓ i j, i ≠ j →
      hi ℓ i ≤ lo ℓ j ∨ hi ℓ j ≤ lo ℓ i) :
    (Finset.univ.sum fun ℓ : Fin levels =>
      (Finset.univ.filter fun i : Fin nodes =>
        lo ℓ i < cut ∧ cut < hi ℓ i).card) ≤ levels := by
  calc
    _ ≤ Finset.univ.sum fun _ : Fin levels => 1 := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      exact disjointIntervals_at_most_one_crossing_cut
        (lo ℓ) (hi ℓ) cut (hdisjoint ℓ)
    _ = levels := by simp

/-- A static-gap sender is contained in its native parent interval, so if its
physical addresses straddle a prefix cut then that native interval straddles
the same cut. This is the bridge from sender-port variation to the interval
count above. -/
theorem staticGapSender_cross_implies_parent_cross
    {n cursor stop cut : Nat} (holes : List (Nat × Nat))
    (hcross : (∃ a ∈ staticWireInterval (n := n) cursor stop \
        staticHoleUnion holes, a.val < cut) ∧
      (∃ b ∈ staticWireInterval (n := n) cursor stop \
        staticHoleUnion holes, cut ≤ b.val)) :
    cursor < cut ∧ cut < stop := by
  rcases hcross with ⟨⟨a, ha, hacut⟩, ⟨b, hb, hbcut⟩⟩
  have ha' := (Finset.mem_sdiff.mp ha).1
  have hb' := (Finset.mem_sdiff.mp hb).1
  simp only [staticWireInterval, Finset.mem_filter, Finset.mem_univ,
    true_and] at ha' hb'
  exact ⟨by omega, by omega⟩

/-- If each sender's prefix-error charge is at most 896 and vanishes unless
its native interval crosses the global cut, disjointness at each level gives
an aggregate charge of at most 896 per level. -/
theorem sum_boundary_sender_error_le_896_mul_levels
    {levels nodes : Nat} (lo hi : Fin levels → Fin nodes → Nat) (cut : Nat)
    (error : Fin levels → Fin nodes → Nat)
    (hdisjoint : ∀ ℓ i j, i ≠ j →
      hi ℓ i ≤ lo ℓ j ∨ hi ℓ j ≤ lo ℓ i)
    (herror : ∀ ℓ i, error ℓ i ≤
      if lo ℓ i < cut ∧ cut < hi ℓ i then 896 else 0) :
    (Finset.univ.sum fun ℓ : Fin levels =>
      Finset.univ.sum fun i : Fin nodes => error ℓ i) ≤ 896 * levels := by
  have hstage (ℓ : Fin levels) :
      (Finset.univ.sum fun i : Fin nodes => error ℓ i) ≤ 896 := by
    calc
      _ ≤ Finset.univ.sum fun i : Fin nodes =>
            if lo ℓ i < cut ∧ cut < hi ℓ i then 896 else 0 :=
          Finset.sum_le_sum fun i _ => herror ℓ i
      _ = (Finset.univ.filter fun i : Fin nodes =>
            lo ℓ i < cut ∧ cut < hi ℓ i).card * 896 := by
          rw [← Finset.sum_filter]
          simp
      _ ≤ 1 * 896 := Nat.mul_le_mul_right 896
          (disjointIntervals_at_most_one_crossing_cut
            (lo ℓ) (hi ℓ) cut (hdisjoint ℓ))
      _ = 896 := by omega
  calc
    _ ≤ Finset.univ.sum fun _ : Fin levels => 896 :=
      Finset.sum_le_sum fun ℓ _ => hstage ℓ
    _ = 896 * levels := by simp [Nat.mul_comm]

end Chvatal.D2StaticWireSets
