import D2LocalRankDisplacement
import D2FlowRankBridge

namespace Chvatal.D2RankCutSeamBound

open Chvatal.D2LocalRankDisplacement
open Chvatal.D2Reserve
open Classical

/-- An output slot crosses the rank cut `q` when its sender-rank and slot lie
on opposite sides of that cut. -/
def crossesRankCut {M : Nat} (rankAt : Fin M -> Fin M)
    (q : Nat) (p : Fin M) : Prop :=
  (p.val <= q /\ q < (rankAt p).val) \/
    ((rankAt p).val <= q /\ q < p.val)

/-- A rank is assigned to a port by the number of port seams at or before it.
Repeated seams are permitted, so empty ports need no special case. -/
def portLabel {K : Nat} (cuts : Fin K -> Nat) (x : Nat) : Nat :=
  (Finset.univ.filter fun k : Fin K => cuts k < x).card

/-- Different ordered-port labels imply crossing at least one seam. This is
the local bridge from rank displacement to receiver-label disagreement. -/
theorem portLabel_ne_implies_crosses_seam {K : Nat}
    (cuts : Fin K -> Nat) {a b : Nat}
    (hne : portLabel cuts a != portLabel cuts b) :
    exists k : Fin K,
      ((a <= cuts k /\ cuts k < b) \/ (b <= cuts k /\ cuts k < a)) := by
  by_contra h
  push_neg at h
  have hsame :
      (Finset.univ.filter fun k : Fin K => cuts k < a) =
      (Finset.univ.filter fun k : Fin K => cuts k < b) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hka
      by_contra hkb
      have hcross := h k
      omega
    · intro hkb
      by_contra hka
      have hcross := h k
      omega
  have hcard := congrArg Finset.card hsame
  simp [portLabel] at hne
  exact hne hcard

/-- The number of slots whose physical port label disagrees with the port of
their sender-rank is bounded by total seam-crossing incidences. -/
theorem portLabel_mismatches_le_crossers {M K : Nat}
    (rankAt : Fin M -> Fin M) (cuts : Fin K -> Nat) :
    (Finset.univ.filter fun p : Fin M =>
      portLabel cuts p.val != portLabel cuts (rankAt p).val).card <=
      Finset.univ.sum fun k : Fin K =>
        (Finset.univ.filter (crossesRankCut rankAt (cuts k))).card := by
  classical
  let mismatch := Finset.univ.filter fun p : Fin M =>
    portLabel cuts p.val != portLabel cuts (rankAt p).val
  let crossingSigma :=
    Sigma fun k : Fin K => {p : Fin M // crossesRankCut rankAt (cuts k) p}
  let chooseCrossing : {p : Fin M // p ∈ mismatch} -> crossingSigma := fun p =>
    let hlabel : portLabel cuts p.val.val !=
        portLabel cuts (rankAt p.val).val := by
      have hp := Finset.mem_filter.mp p.property
      exact hp.2
    let k := Classical.choose
      (portLabel_ne_implies_crosses_seam cuts hlabel)
    ⟨k, ⟨p.val, Classical.choose_spec
      (portLabel_ne_implies_crosses_seam cuts hlabel)⟩⟩
  have hinj : Function.Injective chooseCrossing := by
    intro p q hpq
    apply Subtype.ext
    have hslot := congrArg (fun x : crossingSigma => x.2.1) hpq
    exact hslot
  have hcard := Fintype.card_le_of_injective chooseCrossing hinj
  have hleft : Fintype.card {p : Fin M // p ∈ mismatch} = mismatch.card := by
    simpa using (Finset.card_subtype (fun p : Fin M => p ∈ mismatch)
      (Finset.univ : Finset (Fin M)))
  have hright : Fintype.card crossingSigma =
      Finset.univ.sum fun k : Fin K =>
        (Finset.univ.filter (crossesRankCut rankAt (cuts k))).card := by
    simp only [crossingSigma, Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro k hk
    simpa using (Finset.card_subtype (crossesRankCut rankAt (cuts k))
      (Finset.univ : Finset (Fin M)))
  rw [hleft, hright] at hcard
  simpa [mismatch] using hcard

/-- If every output slot is within `C` of its sender-rank, at most `2*C+1`
slots cross any one rank cut. The bound is independent of sender width. -/
theorem rankCut_crossers_le {M C : Nat} (rankAt : Fin M -> Fin M)
    (hdisp : forall p, (rankAt p).val <= p.val + C /\
      p.val <= (rankAt p).val + C) (q : Nat) :
    (Finset.univ.filter (crossesRankCut rankAt q)).card <= 2 * C + 1 := by
  classical
  let crossers := Finset.univ.filter (crossesRankCut rankAt q)
  let offset : {p : Fin M // p ∈ crossers} -> Fin (2 * C + 1) :=
    fun p => Fin.mk (p.val.val + C - q) (by
      have hp := Finset.mem_filter.mp p.property
      rcases hp.2 with hleft | hright
      · have h := hdisp p.val
        omega
      · have h := hdisp p.val
        omega)
  have hinj : Function.Injective offset := by
    intro p r hpr
    have hpCross : crossesRankCut rankAt q p.val := by
      have hp : p.val ∈ Finset.univ.filter (crossesRankCut rankAt q) := p.property
      exact (Finset.mem_filter.mp hp).2
    have hrCross : crossesRankCut rankAt q r.val := by
      have hr : r.val ∈ Finset.univ.filter (crossesRankCut rankAt q) := r.property
      exact (Finset.mem_filter.mp hr).2
    apply Subtype.ext
    apply Fin.ext
    have hv := congrArg Fin.val hpr
    change p.val.val + C - q = r.val.val + C - q at hv
    have hplower : q ≤ p.val.val + C := by
      rcases hpCross with hpLeft | hpRight
      · have hd := hdisp p.val
        omega
      · have hd := hdisp p.val
        omega
    have hrlower : q ≤ r.val.val + C := by
      rcases hrCross with hrLeft | hrRight
      · have hd := hdisp r.val
        omega
      · have hd := hdisp r.val
        omega
    omega
  have hcard := Fintype.card_le_of_injective offset hinj
  have hsubtype :
      Fintype.card {p : Fin M // crossesRankCut rankAt q p} = crossers.card := by
    simpa [crossers] using
      (Finset.card_subtype (crossesRankCut rankAt q)
        (Finset.univ : Finset (Fin M)))
  have hcard' :
      Fintype.card {p : Fin M // crossesRankCut rankAt q p} ≤ 2 * C + 1 := by
    simpa only [crossers, Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.card_fin] using hcard
  rw [hsubtype] at hcard'
  simpa [crossers] using hcard'

/-- Across any fixed family of P rank cuts, the total number of
slot/cut crossings is at most P*(2*C+1). -/
theorem rankCuts_total_crossers_le {M C P : Nat}
    (rankAt : Fin M -> Fin M)
    (hdisp : forall p, (rankAt p).val <= p.val + C /\
      p.val <= (rankAt p).val + C) (cuts : Fin P -> Nat) :
    (Finset.univ.sum fun k : Fin P =>
      (Finset.univ.filter (crossesRankCut rankAt (cuts k))).card) <=
      P * (2 * C + 1) := by
  calc
    _ <= Finset.univ.sum fun _ : Fin P => 2 * C + 1 := by
      apply Finset.sum_le_sum
      intro k hk
      exact rankCut_crossers_le rankAt hdisp (cuts k)
    _ = P * (2 * C + 1) := by simp

/-- The fixed D2 local macro therefore has at most 1665 output slots crossing
any sender-rank boundary. This count does not control global displacement
across physical address gaps. -/
theorem localCore_rank_cut_crossers_le
    (v : Wire -> Wire) (perm : Row -> Equiv.Perm Col)
    (hbij : Function.Bijective v)
    (hdesc : forall (c : Col) (r s : Row), r.val <= s.val ->
      (v (Chvatal.matrixWire 4096 64 s c)).val <=
        (v (Chvatal.matrixWire 4096 64 r c)).val)
    (q : Nat) :
    (Finset.univ.filter
      (crossesRankCut (localCore v perm) q)).card <= 1665 := by
  have hdisp := localCore_rank_displacement v hbij perm hdesc
  have h := rankCut_crossers_le (localCore v perm) hdisp q
  norm_num at h ⊢
  exact h

/-- For the nine internal boundaries between the two parent half-ports and
eight child ports, the fixed local macro has at most 14,985 port-boundary
crossings in total. -/
theorem localCore_nine_port_seams_le
    (v : Wire -> Wire) (perm : Row -> Equiv.Perm Col)
    (hbij : Function.Bijective v)
    (hdesc : forall (c : Col) (r s : Row), r.val <= s.val ->
      (v (Chvatal.matrixWire 4096 64 s c)).val <=
        (v (Chvatal.matrixWire 4096 64 r c)).val)
    (cuts : Fin 9 -> Nat) :
    (Finset.univ.sum fun k : Fin 9 =>
      (Finset.univ.filter
        (crossesRankCut (localCore v perm) (cuts k))).card) <= 14985 := by
  have hdisp := localCore_rank_displacement v hbij perm hdesc
  have h := rankCuts_total_crossers_le (localCore v perm) hdisp cuts
  norm_num at h ⊢
  exact h

/-- The nine ordinary D2 sender seams: after the left half-up port and after
each successive child down-port. -/
def d2SenderPortSeamCuts (pi : Nat) (widths : Fin 8 -> Nat) :
    Fin 9 -> Nat :=
  fun k => pi / 2 + d2FlowRankBoundary widths k.val

/-- Applying the fixed-core seam estimate to the actual cumulative boundaries
of an ordinary D2 sender still costs at most 14,985 crossed sender-rank slots,
independently of its allocation and child-port sizes. -/
theorem localCore_actual_d2_sender_seams_le
    (v : Wire -> Wire) (perm : Row -> Equiv.Perm Col)
    (hbij : Function.Bijective v)
    (hdesc : forall (c : Col) (r s : Row), r.val <= s.val ->
      (v (Chvatal.matrixWire 4096 64 s c)).val <=
        (v (Chvatal.matrixWire 4096 64 r c)).val)
    (pi : Nat) (widths : Fin 8 -> Nat) :
    (Finset.univ.sum fun k : Fin 9 =>
      (Finset.univ.filter
        (crossesRankCut (localCore v perm)
          (d2SenderPortSeamCuts pi widths k))).card) <= 14985 := by
  exact localCore_nine_port_seams_le v perm hbij hdesc
    (d2SenderPortSeamCuts pi widths)

/-- Consequently, at most 14,985 local output slots have a physical port label
different from the label of their sender-rank. This is the precise counting
form of the seam estimate for grouped receiver profiles. -/
theorem localCore_actual_d2_sender_port_mismatches_le
    (v : Wire -> Wire) (perm : Row -> Equiv.Perm Col)
    (hbij : Function.Bijective v)
    (hdesc : forall (c : Col) (r s : Row), r.val <= s.val ->
      (v (Chvatal.matrixWire 4096 64 s c)).val <=
        (v (Chvatal.matrixWire 4096 64 r c)).val)
    (pi : Nat) (widths : Fin 8 -> Nat) :
    (Finset.univ.filter fun p : Fin (64 * 4096) =>
      portLabel (d2SenderPortSeamCuts pi widths) p.val !=
        portLabel (d2SenderPortSeamCuts pi widths)
          ((localCore v perm p).val)).card <= 14985 := by
  calc
    _ <= Finset.univ.sum fun k : Fin 9 =>
        (Finset.univ.filter
          (crossesRankCut (localCore v perm)
            (d2SenderPortSeamCuts pi widths k))).card :=
      portLabel_mismatches_le_crossers (localCore v perm)
        (d2SenderPortSeamCuts pi widths)
    _ <= 14985 := localCore_actual_d2_sender_seams_le
      v perm hbij hdesc pi widths

end Chvatal.D2RankCutSeamBound
