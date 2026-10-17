import OddEvenMerge64
import AKS.Sort.Untangle

/-! Support-aware packet merging in the repository's generalized comparator
model. An arbitrary injective wire placement preserves execution and depth.
The final sorting theorem must still satisfy `Untangle.untangle` before this
can imply an ordinary sorting-network bound. -/

namespace Chvatal.PacketAlignment

open Untangle

def genScatterComparator {m N : Nat} (e : Fin m ↪ Fin N) (c : Comparator m) :
    GenComparator N := ⟨e c.i, e c.j, fun h => (ne_of_lt c.h) (e.injective h)⟩

def genScatter {m N : Nat} (net : ComparatorNetwork m) (e : Fin m ↪ Fin N) :
    GenNetwork N := ⟨net.comparators.map (genScatterComparator e)⟩

theorem genScatter_exec_inside {m N : Nat} {α : Type} [LinearOrder α]
    (net : ComparatorNetwork m) (e : Fin m ↪ Fin N) (v : Fin N → α) (i : Fin m) :
    (genScatter net e).exec v (e i) = net.exec (v ∘ e) i := by
  suffices hf : ∀ (cs : List (Comparator m)) (v : Fin N → α),
      (fun j => (cs.map (genScatterComparator e)).foldl
        (fun acc c => GenComparator.apply c acc) v (e j)) =
        cs.foldl (fun acc c => Comparator.apply c acc) (v ∘ e) from
    congrFun (hf net.comparators v) i
  intro cs
  induction cs with
  | nil => intro v; rfl
  | cons c cs ih =>
    intro v
    simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    congr 1
    funext j
    simp only [genScatterComparator, GenComparator.apply, Comparator.apply,
      Function.comp, e.injective.eq_iff]

theorem genScatter_exec_outside {m N : Nat} {α : Type} [LinearOrder α]
    (net : ComparatorNetwork m) (e : Fin m ↪ Fin N) (v : Fin N → α)
    (w : Fin N) (hw : w ∉ Set.range e) : (genScatter net e).exec v w = v w := by
  have hf : ∀ (cs : List (Comparator m)) (v : Fin N → α),
      (cs.map (genScatterComparator e)).foldl (fun acc c => GenComparator.apply c acc) v w = v w := by
    intro cs
    induction cs with
    | nil => intro v; rfl
    | cons c cs ih =>
      intro v
      simp only [List.map_cons, List.foldl_cons]
      rw [ih]
      have hwi : w ≠ e c.i := fun h => hw ⟨c.i, h.symm⟩
      have hwj : w ≠ e c.j := fun h => hw ⟨c.j, h.symm⟩
      simp [genScatterComparator, GenComparator.apply, hwi, hwj]
  exact hf net.comparators v

private theorem genScatter_foldl_depth {m N : Nat} (cs : List (Comparator m))
    (e : Fin m ↪ Fin N) (wt₀ : Fin m → Nat) (wt : Fin N → Nat) (dm : Nat)
    (hwt : ∀ j, wt (e j) = wt₀ j) :
    ((cs.map (genScatterComparator e)).foldl genDepthStep (wt, dm)).2 =
      (cs.foldl depthStep (wt₀, dm)).2 := by
  induction cs generalizing wt₀ wt dm with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hnext := ih (depthStep (wt₀, dm) c).1
      (genDepthStep (wt, dm) (genScatterComparator e c)).1
      (genDepthStep (wt, dm) (genScatterComparator e c)).2 (fun j => by
        simp only [genScatterComparator, genDepthStep, depthStep,
          Function.update_apply, hwt, e.injective.eq_iff])
    simp only [genScatterComparator, genDepthStep, depthStep, hwt] at hnext ⊢
    exact hnext

/-- No physical-order hypothesis is needed for generalized scattering. -/
theorem genScatter_depth {m N : Nat} (net : ComparatorNetwork m) (e : Fin m ↪ Fin N) :
    (genScatter net e).depth = net.depth :=
  genScatter_foldl_depth net.comparators e (fun _ => 0) (fun _ => 0) 0 (fun _ => rfl)

private theorem genMergeWidthEq (k : Nat) : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
  rw [pow_succ]
  omega

theorem genMerge_sorts_two_runs {N : Nat} {α : Type} [LinearOrder α]
    (k : Nat) (e : Fin (2 ^ (k + 1)) ↪ Fin N) (v : Fin N → α)
    (hA : Monotone (fun i : Fin (2 ^ k) =>
      v (e (Fin.cast (genMergeWidthEq k) (Fin.castAdd (2 ^ k) i)))))
    (hB : Monotone (fun i : Fin (2 ^ k) =>
      v (e (Fin.cast (genMergeWidthEq k) (Fin.natAdd (2 ^ k) i))))) :
    Monotone (fun i => (genScatter (oddEvenMergeNet (k + 1)) e).exec v (e i)) := by
  have hs := oddEvenMergeNet_sorts_two_runs k (v ∘ e) ⟨hA, hB⟩
  simpa only [genScatter_exec_inside] using hs

theorem genMerge_depth_le {N : Nat} (k : Nat) (e : Fin (2 ^ k) ↪ Fin N) :
    (genScatter (oddEvenMergeNet k) e).depth ≤ k := by
  rw [genScatter_depth]
  exact oddEvenMergeNet_depth_le k

theorem genSorted_dealt_counts {m N : Nat} (net : ComparatorNetwork (2 * m))
    (e : Fin (2 * m) ↪ Fin N) (v : Fin N → Bool)
    (hs : Monotone (net.exec (v ∘ e))) :
    boolTrueCount (fun i : Fin m => (genScatter net e).exec v (e (evenWire m i))) =
        boolTrueCount (v ∘ e) / 2 ∧
      boolTrueCount (fun i : Fin m => (genScatter net e).exec v (e (oddWire m i))) =
        (boolTrueCount (v ∘ e) + 1) / 2 := by
  have hc := sorted_bool_parity_counts (net.exec (v ∘ e)) hs
  rw [boolTrueCount_exec] at hc
  simpa only [genScatter_exec_inside] using hc

/-- Two ascending 64-wire packets, placed on any injective list of 128 wires,
are merged in seven generalized-comparator layers. -/
theorem genMerge128_sorts {N : Nat} {α : Type} [LinearOrder α]
    (e : Fin 128 ↪ Fin N) (v : Fin N → α)
    (hA : Monotone (fun i : Fin 64 => v (e (Fin.castAdd 64 i))))
    (hB : Monotone (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))) :
    Monotone (fun i => (genScatter (oddEvenMergeNet 7) e).exec v (e i)) := by
  have hs : Monotone ((oddEvenMergeNet 7).exec (v ∘ e)) := by
    apply oddEvenMergeNet_sorts_two_runs 6
    constructor
    · simpa using hA
    · simpa using hB
  simpa only [genScatter_exec_inside] using hs

theorem genMerge128_depth_le {N : Nat} (e : Fin 128 ↪ Fin N) :
    (genScatter (oddEvenMergeNet 7) e).depth ≤ 7 := by
  rw [genScatter_depth]
  exact oddEvenMergeNet_depth_le 7

/-- Alternating ranks are fixed output packet supports, ready for the next
round's packet embedding. Both packets are ascending. -/
theorem genMerge128_dealt_lanes_sorted {N : Nat} {α : Type} [LinearOrder α]
    (e : Fin 128 ↪ Fin N) (v : Fin N → α)
    (hA : Monotone (fun i : Fin 64 => v (e (Fin.castAdd 64 i))))
    (hB : Monotone (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))) :
    Monotone (fun i : Fin 64 => (genScatter (oddEvenMergeNet 7) e).exec v
      (e ⟨2 * i.val, by omega⟩)) ∧
    Monotone (fun i : Fin 64 => (genScatter (oddEvenMergeNet 7) e).exec v
      (e ⟨2 * i.val + 1, by omega⟩)) := by
  have hs := genMerge128_sorts e v hA hB
  constructor <;> intro i j hij <;> apply hs <;> apply Fin.mk_le_mk.mpr <;>
    have hv := Fin.le_def.mp hij <;> omega

/-- The exact integer averaging law on arbitrary packet placements. For true
counts the even packet receives the floor and the odd packet the ceiling;
zero counts have the opposite orientation. -/
theorem genMerge128_dealt_counts {N : Nat} (e : Fin 128 ↪ Fin N) (v : Fin N → Bool)
    (hA : Monotone (fun i : Fin 64 => v (e (Fin.castAdd 64 i))))
    (hB : Monotone (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))) :
    let H := boolTrueCount (fun i : Fin 64 => v (e (Fin.castAdd 64 i))) +
      boolTrueCount (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))
    boolTrueCount (fun i : Fin 64 => (genScatter (oddEvenMergeNet 7) e).exec v
      (e (evenWire 64 i))) = H / 2 ∧
    boolTrueCount (fun i : Fin 64 => (genScatter (oddEvenMergeNet 7) e).exec v
      (e (oddWire 64 i))) = (H + 1) / 2 := by
  have hs : Monotone ((oddEvenMergeNet 7).exec (v ∘ e)) := by
    apply oddEvenMergeNet_sorts_two_runs 6
    constructor
    · simpa using hA
    · simpa using hB
  have hc := sorted_bool_parity_counts (m := 64) ((oddEvenMergeNet 7).exec (v ∘ e)) hs
  rw [boolTrueCount_exec] at hc
  have hsum := boolTrueCount_halves (m := 64) (v ∘ e)
  rw [hsum] at hc
  simpa only [genScatter_exec_inside, Function.comp_apply] using hc

/-- One merge-and-deal step cannot increase the two packets' squared count
deviation from any shared real target: it replaces their counts by floor and
ceiling of their average. This isolates the exact rounding residue of a pair. -/
theorem floorCeilAverage_centered_energy_le (x y : Nat) (μ : Real) :
    let a := (x + y) / 2
    let b := (x + y + 1) / 2
    ((a : Real) - μ) ^ 2 + ((b : Real) - μ) ^ 2 ≤
      ((x : Real) - μ) ^ 2 + ((y : Real) - μ) ^ 2 := by
  dsimp
  have hab : (x + y) / 2 + (x + y + 1) / 2 = x + y := by omega
  have hfloorle : (x + y) / 2 ≤ (x + y + 1) / 2 := by omega
  have hceille : (x + y + 1) / 2 ≤ (x + y) / 2 + 1 := by omega
  have hsum : (((x + y) / 2 : Nat) : Real) +
      (((x + y + 1) / 2 : Nat) : Real) = (x : Real) + y := by
    exact_mod_cast hab
  have hout0 : (0 : Real) ≤
      (((x + y + 1) / 2 : Nat) : Real) - ((x + y) / 2 : Nat) := by
    have hcast : (((x + y) / 2 : Nat) : Real) ≤
        (((x + y + 1) / 2 : Nat) : Real) := by exact_mod_cast hfloorle
    linarith
  have hout1 :
      (((x + y + 1) / 2 : Nat) : Real) - ((x + y) / 2 : Nat) ≤ 1 := by
    have hcast : (((x + y + 1) / 2 : Nat) : Real) ≤
        (((x + y) / 2 : Nat) + 1) := by exact_mod_cast hceille
    linarith
  have hsq :
      ((((x + y) / 2 : Nat) : Real) ^ 2 +
        (((x + y + 1) / 2 : Nat) : Real) ^ 2) ≤
      (x : Real) ^ 2 + (y : Real) ^ 2 := by
    by_cases hxy : x = y
    · subst y
      have ha : (x + x) / 2 = x := by omega
      have hb : (x + x + 1) / 2 = x := by omega
      simp [ha, hb]
    · by_cases hlt : x < y
      · have hin : (1 : Real) ≤ (y - x : Nat) := by
          exact_mod_cast (show 1 ≤ y - x by omega)
        let outGap : Real :=
          (((x + y + 1) / 2 : Nat) : Real) - ((x + y) / 2 : Nat)
        let inGap : Real := (y - x : Nat)
        have hgapOrd : outGap ≤ inGap := by
          dsimp [outGap, inGap]
          exact le_trans hout1 hin
        have hfactor : 0 ≤ (inGap - outGap) * (inGap + outGap) :=
          mul_nonneg (sub_nonneg.mpr hgapOrd) (by linarith [hin, hout0])
        have hgap : outGap ^ 2 ≤ inGap ^ 2 := by nlinarith [hfactor]
        have hcast : inGap = (y : Real) - x := by
          dsimp [inGap]
          rw [Nat.cast_sub (by omega)]
        dsimp [outGap] at hgap
        nlinarith [hgap, hsum, hcast]
      · have hlt' : y < x := by omega
        have hin : (1 : Real) ≤ (x - y : Nat) := by
          exact_mod_cast (show 1 ≤ x - y by omega)
        let outGap : Real :=
          (((x + y + 1) / 2 : Nat) : Real) - ((x + y) / 2 : Nat)
        let inGap : Real := (x - y : Nat)
        have hgapOrd : outGap ≤ inGap := by
          dsimp [outGap, inGap]
          exact le_trans hout1 hin
        have hfactor : 0 ≤ (inGap - outGap) * (inGap + outGap) :=
          mul_nonneg (sub_nonneg.mpr hgapOrd) (by linarith [hin, hout0])
        have hgap : outGap ^ 2 ≤ inGap ^ 2 := by nlinarith [hfactor]
        have hcast : inGap = (x : Real) - y := by
          dsimp [inGap]
          rw [Nat.cast_sub (by omega)]
        dsimp [outGap] at hgap
        nlinarith [hgap, hsum, hcast]
  have hcross := congrArg (fun z : Real => -2 * μ * z) hsum
  nlinarith [hsq, hsum, hcross]

/-- The actual generalized 128-wire merge-and-deal network contracts the
two input packet counts' centered quadratic energy at every Boolean threshold. -/
theorem genMerge128_dealt_centered_energy_le {N : Nat}
    (e : Fin 128 ↪ Fin N) (v : Fin N → Bool)
    (hA : Monotone (fun i : Fin 64 => v (e (Fin.castAdd 64 i))))
    (hB : Monotone (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))) (μ : Real) :
    let x := boolTrueCount (fun i : Fin 64 => v (e (Fin.castAdd 64 i)))
    let y := boolTrueCount (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))
    let x' := boolTrueCount (fun i : Fin 64 =>
      (genScatter (oddEvenMergeNet 7) e).exec v (e (evenWire 64 i)))
    let y' := boolTrueCount (fun i : Fin 64 =>
      (genScatter (oddEvenMergeNet 7) e).exec v (e (oddWire 64 i)))
    ((x' : Real) - μ) ^ 2 + ((y' : Real) - μ) ^ 2 ≤
      ((x : Real) - μ) ^ 2 + ((y : Real) - μ) ^ 2 := by
  dsimp
  have hcounts := genMerge128_dealt_counts e v hA hB
  rcases hcounts with ⟨he, ho⟩
  simpa [he, ho] using floorCeilAverage_centered_energy_le
    (boolTrueCount (fun i : Fin 64 => v (e (Fin.castAdd 64 i))))
    (boolTrueCount (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))) μ

/-- Exact energy drop of one pair: it is half the decrease in squared count
gap. The target cancels because merge-and-deal preserves the pair sum. -/
theorem floorCeilAverage_energy_drop (x y : Nat) (μ : Real) :
    let a := (x + y) / 2
    let b := (x + y + 1) / 2
    (((x : Real) - μ) ^ 2 + ((y : Real) - μ) ^ 2) -
      (((a : Real) - μ) ^ 2 + ((b : Real) - μ) ^ 2) =
      (((x : Real) - y) ^ 2 - ((a : Real) - b) ^ 2) / 2 := by
  dsimp
  have hsumNat : (x + y) / 2 + (x + y + 1) / 2 = x + y := by omega
  have hsum : (((x + y) / 2 : Nat) : Real) +
      (((x + y + 1) / 2 : Nat) : Real) = (x : Real) + y := by
    exact_mod_cast hsumNat
  have hb : (((x + y + 1) / 2 : Nat) : Real) =
      (x : Real) + y - ((x + y) / 2 : Nat) := by linarith
  rw [hb]
  ring

/-- The exact pair-drop identity loses at most one half unit to integer
rounding, so its decrease dominates half the input squared gap minus 1/2. -/
theorem floorCeilAverage_energy_drop_ge (x y : Nat) (μ : Real) :
    let a := (x + y) / 2
    let b := (x + y + 1) / 2
    (((x : Real) - μ) ^ 2 + ((y : Real) - μ) ^ 2) -
      (((a : Real) - μ) ^ 2 + ((b : Real) - μ) ^ 2) ≥
        (((x : Real) - y) ^ 2 - 1) / 2 := by
  dsimp
  have hdrop := floorCeilAverage_energy_drop x y μ
  have hfloorle : (x + y) / 2 ≤ (x + y + 1) / 2 := by omega
  have hceille : (x + y + 1) / 2 ≤ (x + y) / 2 + 1 := by omega
  have hzlo : (-1 : Real) ≤
      (((x + y) / 2 : Nat) : Real) - ((x + y + 1) / 2 : Nat) := by
    have hc : (((x + y + 1) / 2 : Nat) : Real) ≤
        (((x + y) / 2 : Nat) : Real) + 1 := by exact_mod_cast hceille
    linarith
  have hzhi : (((x + y) / 2 : Nat) : Real) -
      ((x + y + 1) / 2 : Nat) ≤ 0 := by
    have hc : (((x + y) / 2 : Nat) : Real) ≤
        (((x + y + 1) / 2 : Nat) : Real) := by exact_mod_cast hfloorle
    linarith
  have hfactor : 0 ≤
      ((((x + y) / 2 : Nat) : Real) - ((x + y + 1) / 2 : Nat) + 1) *
        (-((((x + y) / 2 : Nat) : Real) - ((x + y + 1) / 2 : Nat))) :=
    mul_nonneg (by linarith) (by linarith)
  rw [hdrop]
  nlinarith [hfactor]

/-- Counts on the even and odd packet slots after a parallel matching round.
The input Fin `(m+m)` is laid out as its left and right endpoint lists. -/
def mergeDealEvenCount {m : Nat} (x : Fin (m + m) → Nat) (i : Fin m) : Nat :=
  (x (Fin.castAdd m i) + x (Fin.natAdd m i)) / 2

def mergeDealOddCount {m : Nat} (x : Fin (m + m) → Nat) (i : Fin m) : Nat :=
  (x (Fin.castAdd m i) + x (Fin.natAdd m i) + 1) / 2

/-- Sum the edgewise pair estimate over an arbitrary parallel matching round.
This is the interface for replacing a spectral edge-disagreement bound by the
actual merge-and-deal energy decrease. -/
theorem mergeDealMatching_energy_drop_ge {m : Nat}
    (x : Fin (m + m) → Nat) (μ : Real) :
    ((Finset.univ : Finset (Fin m)).sum (fun i =>
      ((x (Fin.castAdd m i) : Real) - μ) ^ 2 +
        ((x (Fin.natAdd m i) : Real) - μ) ^ 2)) -
      ((Finset.univ : Finset (Fin m)).sum (fun i =>
        ((mergeDealEvenCount (m := m) x i : Real) - μ) ^ 2 +
          ((mergeDealOddCount (m := m) x i : Real) - μ) ^ 2)) ≥
      (Finset.univ : Finset (Fin m)).sum (fun i =>
        (((x (Fin.castAdd m i) : Real) - x (Fin.natAdd m i)) ^ 2 - 1) / 2) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simpa [mergeDealEvenCount, mergeDealOddCount] using
    floorCeilAverage_energy_drop_ge (x (Fin.castAdd m i))
      (x (Fin.natAdd m i)) μ

/-- Pairwise energy decrement also works with different source targets when
both dealt outputs inherit the average of those targets. The useful edge
quantity is the disagreement between the two source errors, rather than the
raw count gap. -/
theorem floorCeilAverage_energy_drop_ge_targetAverage (x y : Nat)
    (μx μy : Real) :
    let a := (x + y) / 2
    let b := (x + y + 1) / 2
    (((x : Real) - μx) ^ 2 + ((y : Real) - μy) ^ 2) -
      (((a : Real) - (μx + μy) / 2) ^ 2 +
        ((b : Real) - (μx + μy) / 2) ^ 2) ≥
      ((((x : Real) - μx) - ((y : Real) - μy)) ^ 2 - 1) / 2 := by
  dsimp
  let a : Nat := (x + y) / 2
  let b : Nat := (x + y + 1) / 2
  have hdrop :
      (((x : Real) - μx) ^ 2 + ((y : Real) - μy) ^ 2) -
        ((a - (μx + μy) / 2) ^ 2 + (b - (μx + μy) / 2) ^ 2) =
        ((((x : Real) - μx) - ((y : Real) - μy)) ^ 2 - (a - b) ^ 2) / 2 := by
    have hsumNat : a + b = x + y := by
      dsimp [a, b]
      omega
    have hsum : (a : Real) + (b : Real) = (x : Real) + y := by
      exact_mod_cast hsumNat
    have hb : (b : Real) = (x : Real) + y - a := by linarith
    rw [hb]
    ring
  have hfloorle : (x + y) / 2 ≤ (x + y + 1) / 2 := by omega
  have hceille : (x + y + 1) / 2 ≤ (x + y) / 2 + 1 := by omega
  have hzlo : (-1 : Real) ≤ (a : Real) - b := by
    have hc : (b : Real) ≤ (a : Real) + 1 := by
      dsimp [a, b]
      exact_mod_cast hceille
    linarith
  have hzhi : (a : Real) - b ≤ 0 := by
    have hc : (a : Real) ≤ (b : Real) := by
      dsimp [a, b]
      exact_mod_cast hfloorle
    linarith
  have hfactor : 0 ≤ ((a : Real) - b + 1) * (-( (a : Real) - b)) :=
    mul_nonneg (by linarith) (by linarith)
  rw [hdrop]
  nlinarith [hfactor]

/-- Summed form of the heterogeneous-target decrement for a parallel
matching. Each edge replaces its two source targets by their common average
on the even and odd dealt outputs. -/
theorem mergeDealMatching_energy_drop_ge_targetAverage {m : Nat}
    (x : Fin (m + m) → Nat) (μ : Fin (m + m) → Real) :
    ((Finset.univ : Finset (Fin m)).sum (fun i =>
      ((x (Fin.castAdd m i) : Real) - μ (Fin.castAdd m i)) ^ 2 +
        ((x (Fin.natAdd m i) : Real) - μ (Fin.natAdd m i)) ^ 2)) -
      ((Finset.univ : Finset (Fin m)).sum (fun i =>
        ((mergeDealEvenCount (m := m) x i : Real) -
            (μ (Fin.castAdd m i) + μ (Fin.natAdd m i)) / 2) ^ 2 +
          ((mergeDealOddCount (m := m) x i : Real) -
            (μ (Fin.castAdd m i) + μ (Fin.natAdd m i)) / 2) ^ 2)) ≥
      (Finset.univ : Finset (Fin m)).sum (fun i =>
        ((((x (Fin.castAdd m i) : Real) - μ (Fin.castAdd m i)) -
          ((x (Fin.natAdd m i) : Real) - μ (Fin.natAdd m i))) ^ 2 - 1) / 2) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simpa [mergeDealEvenCount, mergeDealOddCount] using
    floorCeilAverage_energy_drop_ge_targetAverage
      (x (Fin.castAdd m i)) (x (Fin.natAdd m i))
      (μ (Fin.castAdd m i)) (μ (Fin.natAdd m i))

/-- The actual 128-wire merge-and-deal network decreases centered threshold
energy by at least half the input squared count gap, up to a 1/2 rounding
allowance. -/
theorem genMerge128_dealt_energy_drop_ge {N : Nat}
    (e : Fin 128 ↪ Fin N) (v : Fin N → Bool)
    (hA : Monotone (fun i : Fin 64 => v (e (Fin.castAdd 64 i))))
    (hB : Monotone (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))) (μ : Real) :
    let x := boolTrueCount (fun i : Fin 64 => v (e (Fin.castAdd 64 i)))
    let y := boolTrueCount (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))
    let x' := boolTrueCount (fun i : Fin 64 =>
      (genScatter (oddEvenMergeNet 7) e).exec v (e (evenWire 64 i)))
    let y' := boolTrueCount (fun i : Fin 64 =>
      (genScatter (oddEvenMergeNet 7) e).exec v (e (oddWire 64 i)))
    ((x : Real) - μ) ^ 2 + ((y : Real) - μ) ^ 2 -
      ((x' : Real) - μ) ^ 2 - ((y' : Real) - μ) ^ 2 ≥
        (((x : Real) - y) ^ 2 - 1) / 2 := by
  dsimp
  have hcounts := genMerge128_dealt_counts e v hA hB
  rcases hcounts with ⟨he, ho⟩
  have hpair := floorCeilAverage_energy_drop_ge
    (boolTrueCount (fun i : Fin 64 => v (e (Fin.castAdd 64 i))))
    (boolTrueCount (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))) μ
  rw [he, ho]
  nlinarith [hpair]

/-- The actual generalized 128-wire merge-and-deal network supports
heterogeneous packet targets: both output packet targets are the average of
the two input targets, and the energy decrement is controlled by the
disagreement between the input target-relative errors. -/
theorem genMerge128_dealt_energy_drop_ge_targetAverage {N : Nat}
    (e : Fin 128 ↪ Fin N) (v : Fin N → Bool)
    (hA : Monotone (fun i : Fin 64 => v (e (Fin.castAdd 64 i))))
    (hB : Monotone (fun i : Fin 64 => v (e (Fin.natAdd 64 i))))
    (μx μy : Real) :
    let x := boolTrueCount (fun i : Fin 64 => v (e (Fin.castAdd 64 i)))
    let y := boolTrueCount (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))
    let x' := boolTrueCount (fun i : Fin 64 =>
      (genScatter (oddEvenMergeNet 7) e).exec v (e (evenWire 64 i)))
    let y' := boolTrueCount (fun i : Fin 64 =>
      (genScatter (oddEvenMergeNet 7) e).exec v (e (oddWire 64 i)))
    ((x : Real) - μx) ^ 2 + ((y : Real) - μy) ^ 2 -
      ((x' : Real) - (μx + μy) / 2) ^ 2 -
        ((y' : Real) - (μx + μy) / 2) ^ 2 ≥
      ((((x : Real) - μx) - ((y : Real) - μy)) ^ 2 - 1) / 2 := by
  dsimp
  have hcounts := genMerge128_dealt_counts e v hA hB
  rcases hcounts with ⟨he, ho⟩
  have hpair := floorCeilAverage_energy_drop_ge_targetAverage
    (boolTrueCount (fun i : Fin 64 => v (e (Fin.castAdd 64 i))))
    (boolTrueCount (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))) μx μy
  rw [he, ho]
  nlinarith [hpair]

theorem genScatter_exec_threshold {m N : Nat} {α : Type} [LinearOrder α]
    (net : ComparatorNetwork m) (e : Fin m ↪ Fin N) (v : Fin N → α) (t : α) :
    (genScatter net e).exec (fun w => decide (t ≤ v w)) =
      fun w => decide (t ≤ (genScatter net e).exec v w) := by
  funext w
  by_cases hw : w ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hw
    rw [genScatter_exec_inside, genScatter_exec_inside]
    exact congrFun (exec_threshold net (v ∘ e) t) i
  · rw [genScatter_exec_outside net e _ w hw, genScatter_exec_outside net e v w hw]

/-- The exact count law holds simultaneously at every value threshold of a
sorted output, not only for Boolean input values. -/
theorem genSorted_threshold_counts {m N : Nat} {α : Type} [LinearOrder α]
    (net : ComparatorNetwork (2 * m)) (e : Fin (2 * m) ↪ Fin N)
    (v : Fin N → α) (hs : Monotone (net.exec (v ∘ e))) (t : α) :
    let H := boolTrueCount (fun i : Fin (2 * m) => decide (t ≤ v (e i)))
    boolTrueCount (fun i : Fin m => decide
      (t ≤ (genScatter net e).exec v (e (evenWire m i)))) = H / 2 ∧
    boolTrueCount (fun i : Fin m => decide
      (t ≤ (genScatter net e).exec v (e (oddWire m i)))) = (H + 1) / 2 := by
  let b : Fin N → Bool := fun w => decide (t ≤ v w)
  have hm : Monotone (fun x : α => decide (t ≤ x)) := by
    intro x y hxy
    by_cases hx : t ≤ x
    · have hy : t ≤ y := hx.trans hxy
      simp [hx, hy]
    · simp [hx]
  have hb : Monotone (net.exec (b ∘ e)) := by
    change Monotone (net.exec (fun i => decide (t ≤ (v ∘ e) i)))
    rw [exec_threshold]
    exact hm.comp hs
  have hc := genSorted_dealt_counts net e b hb
  simpa only [b, genScatter_exec_threshold, Function.comp_apply] using hc

private def sumPacketEmbedding {m N : Nat} (a b : Fin m ↪ Fin N)
    (hdis : ∀ i j, a i ≠ b j) : Fin m ⊕ Fin m ↪ Fin N :=
  ⟨Sum.elim a b, by
    intro x y hxy
    cases x with
    | inl i => cases y with
      | inl j => exact congrArg Sum.inl (a.injective hxy)
      | inr j => exact False.elim (hdis i j hxy)
    | inr i => cases y with
      | inl j => exact False.elim (hdis j i hxy.symm)
      | inr j => exact congrArg Sum.inr (b.injective hxy)⟩

/-- Join two disjoint packet embeddings by their logical packet order. No
condition compares the physical positions of the two packets. -/
def joinPacketEmbedding {m N : Nat} (a b : Fin m ↪ Fin N)
    (hdis : ∀ i j, a i ≠ b j) : Fin (m + m) ↪ Fin N :=
  (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)).symm.toEmbedding.trans
    (sumPacketEmbedding a b hdis)

@[simp] theorem joinPacketEmbedding_left {m N : Nat} (a b : Fin m ↪ Fin N)
    (hdis : ∀ i j, a i ≠ b j) (i : Fin m) :
    joinPacketEmbedding a b hdis (Fin.castAdd m i) = a i := by
  change Sum.elim a b (finSumFinEquiv.symm (Fin.castAdd m i)) = a i
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

@[simp] theorem joinPacketEmbedding_right {m N : Nat} (a b : Fin m ↪ Fin N)
    (hdis : ∀ i j, a i ≠ b j) (i : Fin m) :
    joinPacketEmbedding a b hdis (Fin.natAdd m i) = b i := by
  change Sum.elim a b (finSumFinEquiv.symm (Fin.natAdd m i)) = b i
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem joinPacketEmbedding_range {m N : Nat} (a b : Fin m ↪ Fin N)
    (hdis : ∀ i j, a i ≠ b j) :
    Set.range (joinPacketEmbedding a b hdis) = Set.range a ∪ Set.range b := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : i.val < m
    · let j : Fin m := ⟨i.val, hi⟩
      have hij : i = Fin.castAdd m j := Fin.ext rfl
      rw [hij, joinPacketEmbedding_left]
      exact Or.inl ⟨j, rfl⟩
    · let j : Fin m := ⟨i.val - m, by have := i.isLt; omega⟩
      have hij : i = Fin.natAdd m j := Fin.ext (by simp [j]; omega)
      rw [hij, joinPacketEmbedding_right]
      exact Or.inr ⟨j, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Fin.castAdd m i, joinPacketEmbedding_left a b hdis i⟩
    · exact ⟨Fin.natAdd m i, joinPacketEmbedding_right a b hdis i⟩

/-- Assemble the logical packet pairs of a matching into 128-wire supports. -/
def genJoinMatching {N : Nat}
    (matching : List ((Fin 64 ↪ Fin N) × (Fin 64 ↪ Fin N)))
    (hwithin : ∀ e : (Fin 64 ↪ Fin N) × (Fin 64 ↪ Fin N),
      ∀ i j, e.1 i ≠ e.2 j) :
    List (Fin 128 ↪ Fin N) :=
  matching.map fun e => joinPacketEmbedding e.1 e.2 (hwithin e)

theorem genJoinMatching_edges_disjoint {N : Nat}
    (matching : List ((Fin 64 ↪ Fin N) × (Fin 64 ↪ Fin N)))
    (hwithin : ∀ e : (Fin 64 ↪ Fin N) × (Fin 64 ↪ Fin N),
      ∀ i j, e.1 i ≠ e.2 j)
    (hmatching : ∀ e ∈ matching, ∀ f ∈ matching, e ≠ f → ∀ i j,
      e.1 i ≠ f.1 j ∧ e.1 i ≠ f.2 j ∧
      e.2 i ≠ f.1 j ∧ e.2 i ≠ f.2 j)
    (a b : (Fin 64 ↪ Fin N) × (Fin 64 ↪ Fin N))
    (ha : a ∈ matching) (hb : b ∈ matching) (hab : a ≠ b) :
    ∀ i j, joinPacketEmbedding a.1 a.2 (hwithin a) i ≠
      joinPacketEmbedding b.1 b.2 (hwithin b) j := by
  intro i j
  have hleft : joinPacketEmbedding a.1 a.2 (hwithin a) i ∈
      Set.range a.1 ∪ Set.range a.2 := by
    rw [← joinPacketEmbedding_range a.1 a.2 (hwithin a)]
    exact ⟨i, rfl⟩
  have hright : joinPacketEmbedding b.1 b.2 (hwithin b) j ∈
      Set.range b.1 ∪ Set.range b.2 := by
    rw [← joinPacketEmbedding_range b.1 b.2 (hwithin b)]
    exact ⟨j, rfl⟩
  have hsep := hmatching a ha b hb hab
  rcases hleft with ⟨ia, hia⟩ | ⟨ia, hia⟩ <;>
    rcases hright with ⟨ib, hib⟩ | ⟨ib, hib⟩
  · intro heq
    exact (hsep ia ib).1 (hia.trans (heq.trans hib.symm))
  · intro heq
    exact (hsep ia ib).2.1 (hia.trans (heq.trans hib.symm))
  · intro heq
    exact (hsep ia ib).2.2.1 (hia.trans (heq.trans hib.symm))
  · intro heq
    exact (hsep ia ib).2.2.2 (hia.trans (heq.trans hib.symm))

theorem genJoinMatching_disjoint {N : Nat}
    (matching : List ((Fin 64 ↪ Fin N) × (Fin 64 ↪ Fin N)))
    (hwithin : ∀ e : (Fin 64 ↪ Fin N) × (Fin 64 ↪ Fin N),
      ∀ i j, e.1 i ≠ e.2 j)
    (hmatching : ∀ e ∈ matching, ∀ f ∈ matching, e ≠ f → ∀ i j,
      e.1 i ≠ f.1 j ∧ e.1 i ≠ f.2 j ∧
      e.2 i ≠ f.1 j ∧ e.2 i ≠ f.2 j) :
    ∀ e ∈ genJoinMatching matching hwithin,
      ∀ f ∈ genJoinMatching matching hwithin, e ≠ f → ∀ i j, e i ≠ f j := by
  intro e he f hf hne i j
  simp only [genJoinMatching, List.mem_map] at he hf
  obtain ⟨a, ha, rfl⟩ := he
  obtain ⟨b, hb, rfl⟩ := hf
  have hab : a ≠ b := by
    intro h
    apply hne
    subst b
    rfl
  exact genJoinMatching_edges_disjoint matching hwithin hmatching a b ha hb hab i j

theorem genJoinMatching_nodup {N : Nat}
    (matching : List ((Fin 64 ↪ Fin N) × (Fin 64 ↪ Fin N)))
    (hwithin : ∀ e : (Fin 64 ↪ Fin N) × (Fin 64 ↪ Fin N),
      ∀ i j, e.1 i ≠ e.2 j)
    (hnodup : matching.Nodup)
    (hmatching : ∀ e ∈ matching, ∀ f ∈ matching, e ≠ f → ∀ i j,
      e.1 i ≠ f.1 j ∧ e.1 i ≠ f.2 j ∧
      e.2 i ≠ f.1 j ∧ e.2 i ≠ f.2 j) :
    (genJoinMatching matching hwithin).Nodup := by
  apply List.Nodup.map_on
  · intro a ha b hb hab
    by_contra hne
    have hsep := genJoinMatching_edges_disjoint matching hwithin hmatching a b ha hb hne
      (0 : Fin 128) (0 : Fin 128)
    exact hsep (congrArg (fun e : Fin 128 ↪ Fin N => e 0) hab)
  · exact hnodup

/-- Build the joined supports directly from a matching on packet indices.
The endpoint-disjointness proof is attached to each edge, so no premise is
needed for pairs that are not in the matching. -/
def genIndexedPairSupports {m N : Nat}
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m))
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2) : List (Fin 128 ↪ Fin N) :=
  edges.attach.map fun e => joinPacketEmbedding (packets e.1.1) (packets e.1.2)
    (hpacketDisjoint e.1.1 e.1.2 (hnoFixed e.1 e.2))

theorem genIndexedPairSupports_edges_disjoint {m N : Nat}
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m))
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2)
    (hvertexDisjoint : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) :
    ∀ e, ∀ he : e ∈ edges, ∀ f, ∀ hf : f ∈ edges, e ≠ f → ∀ i j,
      joinPacketEmbedding (packets e.1) (packets e.2)
        (hpacketDisjoint e.1 e.2 (hnoFixed e he)) i ≠
      joinPacketEmbedding (packets f.1) (packets f.2)
        (hpacketDisjoint f.1 f.2 (hnoFixed f hf)) j := by
  intro edge hedge edge' hedge' hedgeNe i j
  have hids := hvertexDisjoint edge hedge edge' hedge' hedgeNe
  have hwithin : ∀ x y : Fin 64,
      packets edge.1 x ≠ packets edge.2 y :=
    hpacketDisjoint edge.1 edge.2 (hnoFixed edge hedge)
  have hwithin' : ∀ x y : Fin 64,
      packets edge'.1 x ≠ packets edge'.2 y :=
    hpacketDisjoint edge'.1 edge'.2 (hnoFixed edge' hedge')
  have hleft : joinPacketEmbedding (packets edge.1) (packets edge.2)
      (hpacketDisjoint edge.1 edge.2 (hnoFixed edge hedge)) i ∈
      Set.range (packets edge.1) ∪ Set.range (packets edge.2) := by
    rw [← joinPacketEmbedding_range _ _ hwithin]
    exact ⟨i, rfl⟩
  have hright : joinPacketEmbedding (packets edge'.1) (packets edge'.2)
      (hpacketDisjoint edge'.1 edge'.2 (hnoFixed edge' hedge')) j ∈
      Set.range (packets edge'.1) ∪ Set.range (packets edge'.2) := by
    rw [← joinPacketEmbedding_range _ _ hwithin']
    exact ⟨j, rfl⟩
  rcases hleft with ⟨x, hx⟩ | ⟨x, hx⟩ <;>
    rcases hright with ⟨y, hy⟩ | ⟨y, hy⟩
  · intro heq
    exact (hpacketDisjoint edge.1 edge'.1 hids.1 x y) (hx.trans (heq.trans hy.symm))
  · intro heq
    exact (hpacketDisjoint edge.1 edge'.2 hids.2.1 x y) (hx.trans (heq.trans hy.symm))
  · intro heq
    exact (hpacketDisjoint edge.2 edge'.1 hids.2.2.1 x y) (hx.trans (heq.trans hy.symm))
  · intro heq
    exact (hpacketDisjoint edge.2 edge'.2 hids.2.2.2 x y) (hx.trans (heq.trans hy.symm))

theorem genIndexedPairSupports_disjoint {m N : Nat}
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m))
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2)
    (hvertexDisjoint : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) :
    ∀ e ∈ genIndexedPairSupports packets hpacketDisjoint edges hnoFixed,
      ∀ f ∈ genIndexedPairSupports packets hpacketDisjoint edges hnoFixed,
        e ≠ f → ∀ i j, e i ≠ f j := by
  intro e he f hf hne i j
  simp only [genIndexedPairSupports, List.mem_map, List.mem_attach] at he hf
  obtain ⟨edge, hedge, rfl⟩ := he
  obtain ⟨edge', hedge', rfl⟩ := hf
  have hedgeNe : edge.1 ≠ edge'.1 := by
    intro h
    apply hne
    have heq : edge = edge' := Subtype.ext h
    subst edge'
    rfl
  exact genIndexedPairSupports_edges_disjoint packets hpacketDisjoint edges hnoFixed
    hvertexDisjoint edge.1 edge.2 edge'.1 edge'.2 hedgeNe i j

theorem genIndexedPairSupports_nodup {m N : Nat}
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m)) (hedges : edges.Nodup)
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2)
    (hvertexDisjoint : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) :
    (genIndexedPairSupports packets hpacketDisjoint edges hnoFixed).Nodup := by
  apply List.Nodup.map_on
  · intro e he f hf heq
    let ee := joinPacketEmbedding (packets e.1.1) (packets e.1.2)
      (hpacketDisjoint e.1.1 e.1.2 (hnoFixed e.1 e.2))
    let ff := joinPacketEmbedding (packets f.1.1) (packets f.1.2)
      (hpacketDisjoint f.1.1 f.1.2 (hnoFixed f.1 f.2))
    by_cases hval : e.1 = f.1
    · exact Subtype.ext hval
    · have hsep := genIndexedPairSupports_edges_disjoint packets hpacketDisjoint edges
        hnoFixed hvertexDisjoint e.1 e.2 f.1 f.2 hval 0 0
      exact False.elim (hsep (congrArg (fun p : Fin 128 ↪ Fin N => p 0) heq))
  · simpa using hedges.attach

def dealEvenEmbedding {N : Nat} (e : Fin 128 ↪ Fin N) : Fin 64 ↪ Fin N :=
  ⟨fun i => e (evenWire 64 i), by
    intro i j hij
    have hv := congrArg Fin.val (e.injective hij)
    change 2 * i.val = 2 * j.val at hv
    exact Fin.ext (by omega)⟩

def dealOddEmbedding {N : Nat} (e : Fin 128 ↪ Fin N) : Fin 64 ↪ Fin N :=
  ⟨fun i => e (oddWire 64 i), by
    intro i j hij
    have hv := congrArg Fin.val (e.injective hij)
    change 2 * i.val + 1 = 2 * j.val + 1 at hv
    exact Fin.ext (by omega)⟩

/-- Even/odd dealing preserves increasing physical wire order when the joined
128-wire embedding itself is increasing. -/
theorem dealEvenEmbedding_strictMono {N : Nat} (e : Fin 128 ↪ Fin N)
    (he : StrictMono e) : StrictMono (dealEvenEmbedding e) := by
  intro i j hij
  exact he ((by
    apply Fin.lt_iff_val_lt_val.mpr
    simp [evenWire]
    omega) : evenWire 64 i < evenWire 64 j)

theorem dealOddEmbedding_strictMono {N : Nat} (e : Fin 128 ↪ Fin N)
    (he : StrictMono e) : StrictMono (dealOddEmbedding e) := by
  intro i j hij
  exact he ((by
    apply Fin.lt_iff_val_lt_val.mpr
    simp [oddWire]
    omega) : oddWire 64 i < oddWire 64 j)

/-- Even/odd dealing preserves order within each output packet but interleaves
their physical supports, even when the joined input occupies one increasing
128-wire interval. Thus an induction that matches only wholly separated
individual output packets cannot pair these two outputs on the next round. -/
theorem dealEmbeddings_interleave_of_strictMono {N : Nat}
    (e : Fin 128 ↪ Fin N) (he : StrictMono e) :
    dealEvenEmbedding e 0 < dealOddEmbedding e 0 ∧
      dealOddEmbedding e 0 < dealEvenEmbedding e 1 := by
  have h01 : (⟨0, by omega⟩ : Fin 128) < ⟨1, by omega⟩ := by decide
  have h12 : (⟨1, by omega⟩ : Fin 128) < ⟨2, by omega⟩ := by decide
  constructor
  · simpa [dealEvenEmbedding, dealOddEmbedding, evenWire, oddWire] using he h01
  · simpa [dealEvenEmbedding, dealOddEmbedding, evenWire, oddWire] using he h12

/-- Concatenating two increasing packet embeddings remains increasing when
the entire first support lies below the entire second support. -/
theorem joinPacketEmbedding_strictMono {m N : Nat}
    (a b : Fin m ↪ Fin N) (hdis : ∀ i j, a i ≠ b j)
    (ha : StrictMono a) (hb : StrictMono b)
    (hab : ∀ i j, a i < b j) :
    StrictMono (joinPacketEmbedding a b hdis) := by
  intro i j hij
  have hijv : i.val < j.val := Fin.lt_iff_val_lt_val.mp hij
  by_cases hi : i.val < m
  · let i' : Fin m := ⟨i.val, hi⟩
    have hieq : i = Fin.castAdd m i' := Fin.ext rfl
    rw [hieq]
    by_cases hj : j.val < m
    · let j' : Fin m := ⟨j.val, hj⟩
      have hjeq : j = Fin.castAdd m j' := Fin.ext rfl
      rw [hjeq, joinPacketEmbedding_left, joinPacketEmbedding_left]
      apply ha
      apply Fin.lt_iff_val_lt_val.mpr
      exact hijv
    · let j' : Fin m := ⟨j.val - m, by have := j.isLt; omega⟩
      have hjeq : j = Fin.natAdd m j' := Fin.ext (by simp [j']; omega)
      rw [hjeq, joinPacketEmbedding_left, joinPacketEmbedding_right]
      exact hab i' j'
  · by_cases hj : j.val < m
    · omega
    · let i' : Fin m := ⟨i.val - m, by have := i.isLt; omega⟩
      let j' : Fin m := ⟨j.val - m, by have := j.isLt; omega⟩
      have hieq : i = Fin.natAdd m i' := Fin.ext (by simp [i']; omega)
      have hjeq : j = Fin.natAdd m j' := Fin.ext (by simp [j']; omega)
      rw [hieq, hjeq, joinPacketEmbedding_right, joinPacketEmbedding_right]
      apply hb
      apply (Fin.natAdd_lt_natAdd_iff m).mp
      rw [← hieq, ← hjeq]
      exact hij

theorem dealEmbeddings_disjoint {N : Nat} (e : Fin 128 ↪ Fin N) :
    ∀ i j, dealEvenEmbedding e i ≠ dealOddEmbedding e j := by
  intro i j heq
  have hv := congrArg Fin.val (e.injective heq)
  change 2 * i.val = 2 * j.val + 1 at hv
  omega

/-- The two fixed output packet supports partition the consumed support. -/
theorem dealEmbeddings_partition {N : Nat} (e : Fin 128 ↪ Fin N) :
    Set.range (dealEvenEmbedding e) ∪ Set.range (dealOddEmbedding e) = Set.range e := by
  ext w
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨evenWire 64 i, rfl⟩
    · exact ⟨oddWire 64 i, rfl⟩
  · rintro ⟨j, rfl⟩
    let i : Fin 64 := ⟨j.val / 2, by have := j.isLt; omega⟩
    by_cases he : j.val % 2 = 0
    · left
      refine ⟨i, congrArg e ?_⟩
      apply Fin.ext
      change 2 * (j.val / 2) = j.val
      omega
    · right
      refine ⟨i, congrArg e ?_⟩
      apply Fin.ext
      change 2 * (j.val / 2) + 1 = j.val
      omega

/-- A composable local packet step: arbitrary disjoint sorted packets in,
arbitrary disjoint sorted packets out, with all embeddings input-independent. -/
theorem genPacketPair_lanes_sorted {N : Nat} {α : Type} [LinearOrder α]
    (a b : Fin 64 ↪ Fin N) (hdis : ∀ i j, a i ≠ b j) (v : Fin N → α)
    (ha : Monotone (v ∘ a)) (hb : Monotone (v ∘ b)) :
    let e := joinPacketEmbedding a b hdis
    let G := genScatter (oddEvenMergeNet 7) e
    Monotone (G.exec v ∘ dealEvenEmbedding e) ∧
      Monotone (G.exec v ∘ dealOddEmbedding e) := by
  apply genMerge128_dealt_lanes_sorted (joinPacketEmbedding a b hdis) v
  · intro i j hij
    dsimp only
    rw [joinPacketEmbedding_left, joinPacketEmbedding_left]
    exact ha hij
  · intro i j hij
    dsimp only
    rw [joinPacketEmbedding_right, joinPacketEmbedding_right]
    exact hb hij

/-! ### Disjoint matching-round execution

The local pair theorem becomes useful to an induction only after all pairs in
one matching can be run on the same ambient wires. The following family
network scatters the same seven-layer merge onto each listed 128-wire support.
Its execution on one support agrees with that pair's local execution; hence
other disjoint pairs cannot disturb either dealt output packet. -/

def genPacketRound {N : Nat} (pairs : List (Fin 128 ↪ Fin N)) : GenNetwork N :=
  ⟨pairs.flatMap fun e => (genScatter (oddEvenMergeNet 7) e).comparators⟩

@[simp] theorem genPacketRound_cons {N : Nat} (e : Fin 128 ↪ Fin N)
    (es : List (Fin 128 ↪ Fin N)) :
    genPacketRound (e :: es) =
      ⟨(genScatter (oddEvenMergeNet 7) e).comparators ++
        (genPacketRound es).comparators⟩ := rfl

private theorem genNetwork_exec_append {N : Nat} {α : Type*} [LinearOrder α]
    (G H : GenNetwork N) (v : Fin N → α) :
    (⟨G.comparators ++ H.comparators⟩ : GenNetwork N).exec v = H.exec (G.exec v) := by
  simp [GenNetwork.exec, List.foldl_append]

private theorem genFoldlDmLe {N : Nat} (cs : List (GenComparator N))
    (wt : Fin N → Nat) (dm : Nat) :
    dm ≤ (cs.foldl genDepthStep (wt, dm)).2 := by
  induction cs generalizing wt dm with
  | nil => exact le_rfl
  | cons c cs ih => exact (le_max_left _ _).trans (ih _ _)

private theorem genFoldlUntouched {N : Nat} (cs : List (GenComparator N))
    (wt : Fin N → Nat) (dm : Nat) (k : Fin N)
    (hk : ∀ c ∈ cs, k ≠ c.a ∧ k ≠ c.b) :
    (cs.foldl genDepthStep (wt, dm)).1 k = wt k := by
  induction cs generalizing wt dm with
  | nil => rfl
  | cons c cs ih =>
      have hkc := hk c (by simp)
      simp only [List.foldl_cons]
      rw [ih _ _ (fun c' hc' => hk c' (List.mem_cons_of_mem c hc'))]
      simp [genDepthStep, hkc.1, hkc.2]

private theorem genFoldlDepthMax {N : Nat} (cs : List (GenComparator N))
    (wt wt₀ : Fin N → Nat) (dm dm₀ : Nat)
    (hwt : ∀ c ∈ cs, wt c.a = wt₀ c.a ∧ wt c.b = wt₀ c.b) :
    (cs.foldl genDepthStep (wt, dm)).2 ≤
      max dm (cs.foldl genDepthStep (wt₀, dm₀)).2 := by
  induction cs generalizing wt wt₀ dm dm₀ with
  | nil => exact le_max_left _ _
  | cons c cs ih =>
      have htime := hwt c (by simp)
      have htail := ih
        (genDepthStep (wt, dm) c).1 (genDepthStep (wt₀, dm₀) c).1
        (genDepthStep (wt, dm) c).2 (genDepthStep (wt₀, dm₀) c).2
        (fun c' hc' => by
          have h := hwt c' (List.mem_cons_of_mem c hc')
          simp only [genDepthStep, Function.update_apply]
          split_ifs <;> simp_all)
      have hbase := genFoldlDmLe cs
        (genDepthStep (wt₀, dm₀) c).1 (genDepthStep (wt₀, dm₀) c).2
      have hct : max (wt c.a) (wt c.b) + 1 ≤
          (cs.foldl genDepthStep (genDepthStep (wt₀, dm₀) c)).2 := by
        rw [htime.1, htime.2]
        dsimp [genDepthStep]
        exact (le_max_right _ _).trans hbase
      simp only [List.foldl_cons]
      dsimp only [genDepthStep] at htail ⊢
      exact htail.trans (by
        apply max_le
        · exact max_le (le_max_left _ _) (hct.trans (le_max_right _ _))
        · exact le_max_right _ _)

/-- Generalized comparators on pairwise disjoint supports have parallel depth:
the sequential list concatenation costs only the maximum component depth. -/
private theorem genDepth_flatMap_disjoint {N : Nat} {ι : Type*}
    (chunks : List ι) (f : ι → List (GenComparator N)) (D : Nat)
    (hD : ∀ x ∈ chunks, (⟨f x⟩ : GenNetwork N).depth ≤ D)
    (hdis : chunks.Pairwise (fun x y =>
      ∀ c ∈ f x, ∀ d ∈ f y,
        c.a ≠ d.a ∧ c.a ≠ d.b ∧ c.b ≠ d.a ∧ c.b ≠ d.b)) :
    (⟨chunks.flatMap f⟩ : GenNetwork N).depth ≤ D := by
  simp only [GenNetwork.depth]
  induction chunks with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.foldl_append]
      have hxdis := (List.pairwise_cons.mp hdis).1
      have hag : ∀ c ∈ xs.flatMap f,
          ((f x).foldl genDepthStep (fun _ => 0, 0)).1 c.a = 0 ∧
          ((f x).foldl genDepthStep (fun _ => 0, 0)).1 c.b = 0 := by
        intro c hc
        obtain ⟨y, hy, hcy⟩ := List.mem_flatMap.mp hc
        have hxy := hxdis y hy
        exact ⟨genFoldlUntouched (f x) (fun _ => 0) 0 c.a
            (fun z hz => ⟨(hxy z hz c hcy).1.symm, (hxy z hz c hcy).2.2.1.symm⟩),
          genFoldlUntouched (f x) (fun _ => 0) 0 c.b
            (fun z hz => ⟨(hxy z hz c hcy).2.1.symm, (hxy z hz c hcy).2.2.2.symm⟩)⟩
      have htail := genFoldlDepthMax (xs.flatMap f)
        ((f x).foldl genDepthStep (fun _ => 0, 0)).1 (fun _ => 0)
        ((f x).foldl genDepthStep (fun _ => 0, 0)).2 0 hag
      exact htail.trans (max_le (hD x (by simp))
        (ih (fun y hy => hD y (List.mem_cons_of_mem x hy))
          (List.pairwise_cons.mp hdis).2))

/-- Scatter one fixed local network independently onto a finite family of
pairwise disjoint supports. The resulting comparator list is sequentially
stored, but disjointness makes its generalized-network depth the local depth. -/
def genScatterBatch {M N : Nat} (net : ComparatorNetwork M)
    (supports : List (Fin M ↪ Fin N)) : GenNetwork N :=
  ⟨supports.flatMap fun e => (genScatter net e).comparators⟩

theorem genScatterBatch_comparator_endpoints {M N : Nat}
    (net : ComparatorNetwork M) (supports : List (Fin M ↪ Fin N))
    (c : GenComparator N) (hc : c ∈ (genScatterBatch net supports).comparators) :
    (∃ e ∈ supports, ∃ i, e i = c.a) ∧
      (∃ e ∈ supports, ∃ i, e i = c.b) := by
  change c ∈ supports.flatMap (fun e => (genScatter net e).comparators) at hc
  obtain ⟨e, he, hlocal⟩ := List.mem_flatMap.mp hc
  change c ∈ net.comparators.map (genScatterComparator e) at hlocal
  obtain ⟨c₀, _, rfl⟩ := List.mem_map.mp hlocal
  exact ⟨⟨e, he, c₀.i, rfl⟩, ⟨e, he, c₀.j, rfl⟩⟩

theorem genScatter_comparator_endpoints {M N : Nat} (net : ComparatorNetwork M)
    (e : Fin M ↪ Fin N) (c : GenComparator N)
    (hc : c ∈ (genScatter net e).comparators) :
    (∃ i, e i = c.a) ∧ (∃ i, e i = c.b) := by
  change c ∈ net.comparators.map (genScatterComparator e) at hc
  obtain ⟨c₀, _, rfl⟩ := List.mem_map.mp hc
  exact ⟨⟨c₀.i, rfl⟩, ⟨c₀.j, rfl⟩⟩

theorem genScatterBatch_genScatter_comparators_disjoint {M K N : Nat}
    (net : ComparatorNetwork M) (supports : List (Fin M ↪ Fin N))
    (tailNet : ComparatorNetwork K) (tail : Fin K ↪ Fin N)
    (hsep : ∀ e ∈ supports, ∀ i j, e i ≠ tail j)
    (c : GenComparator N) (hc : c ∈ (genScatterBatch net supports).comparators)
    (d : GenComparator N) (hd : d ∈ (genScatter tailNet tail).comparators) :
    c.a ≠ d.a ∧ c.a ≠ d.b ∧ c.b ≠ d.a ∧ c.b ≠ d.b := by
  obtain ⟨e, he, i, hca⟩ := (genScatterBatch_comparator_endpoints net supports c hc).1
  obtain ⟨e', he', i', hcb⟩ := (genScatterBatch_comparator_endpoints net supports c hc).2
  have htail := genScatter_comparator_endpoints tailNet tail d hd
  obtain ⟨j, hda⟩ := htail.1
  obtain ⟨j', hdb⟩ := htail.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro heq
    exact (hsep e he i j) (hca.trans (heq.trans hda.symm))
  · intro heq
    exact (hsep e he i j') (hca.trans (heq.trans hdb.symm))
  · intro heq
    exact (hsep e' he' i' j) (hcb.trans (heq.trans hda.symm))
  · intro heq
    exact (hsep e' he' i' j') (hcb.trans (heq.trans hdb.symm))

@[simp] theorem genScatterBatch_cons {M N : Nat} (net : ComparatorNetwork M)
    (e : Fin M ↪ Fin N) (supports : List (Fin M ↪ Fin N)) :
    genScatterBatch net (e :: supports) =
      ⟨(genScatter net e).comparators ++
        (genScatterBatch net supports).comparators⟩ := rfl

theorem genScatterBatch_depth_le {M N : Nat} (net : ComparatorNetwork M)
    (supports : List (Fin M ↪ Fin N)) (hnd : supports.Nodup)
    (hdis : ∀ e ∈ supports, ∀ f ∈ supports, e ≠ f → ∀ i j, e i ≠ f j) :
    (genScatterBatch net supports).depth ≤ net.depth := by
  have hchunks : supports.Pairwise (fun e f =>
      ∀ c ∈ (genScatter net e).comparators,
        ∀ d ∈ (genScatter net f).comparators,
          c.a ≠ d.a ∧ c.a ≠ d.b ∧ c.b ≠ d.a ∧ c.b ≠ d.b) := by
    have haux : ∀ (es : List (Fin M ↪ Fin N)), es.Nodup →
        (∀ e ∈ es, ∀ f ∈ es, e ≠ f → ∀ i j, e i ≠ f j) →
        es.Pairwise (fun e f =>
          ∀ c ∈ (genScatter net e).comparators,
            ∀ d ∈ (genScatter net f).comparators,
              c.a ≠ d.a ∧ c.a ≠ d.b ∧ c.b ≠ d.a ∧ c.b ≠ d.b) := by
      intro es
      induction es with
      | nil => intro _ _; simp
      | cons e es ih =>
          intro hnd' hdis'
          have hnd'' := List.nodup_cons.mp hnd'
          have hdisTail : ∀ a ∈ es, ∀ b ∈ es, a ≠ b → ∀ i j, a i ≠ b j := by
            intro a ha b hb hne i j
            exact hdis' a (List.mem_cons_of_mem e ha) b
              (List.mem_cons_of_mem e hb) hne i j
          refine List.pairwise_cons.mpr ⟨?_, ih hnd''.2 hdisTail⟩
          intro f hf c hc d hd
          have hef : e ≠ f := by
            intro heq
            subst f
            exact hnd''.1 hf
          have hwire := hdis' e (by simp) f (List.mem_cons_of_mem e hf) hef
          change c ∈ net.comparators.map (genScatterComparator e) at hc
          change d ∈ net.comparators.map (genScatterComparator f) at hd
          obtain ⟨c₀, _, rfl⟩ := List.mem_map.mp hc
          obtain ⟨d₀, _, rfl⟩ := List.mem_map.mp hd
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [genScatterComparator] using hwire c₀.i d₀.i
          · simpa [genScatterComparator] using hwire c₀.i d₀.j
          · simpa [genScatterComparator] using hwire c₀.j d₀.i
          · simpa [genScatterComparator] using hwire c₀.j d₀.j
    exact haux supports hnd hdis
  have hbound : ∀ e ∈ supports,
      (⟨(genScatter net e).comparators⟩ : GenNetwork N).depth ≤ net.depth := by
    intro e he
    rw [genScatter_depth]
  exact genDepth_flatMap_disjoint supports
    (fun e => (genScatter net e).comparators) net.depth hbound hchunks

theorem genScatterBatch_exec_outside {M N : Nat} {α : Type} [LinearOrder α]
    (net : ComparatorNetwork M) (supports : List (Fin M ↪ Fin N))
    (w : Fin N) (hw : ∀ e ∈ supports, w ∉ Set.range e) (v : Fin N → α) :
    (genScatterBatch net supports).exec v w = v w := by
  induction supports generalizing v with
  | nil => rfl
  | cons e es ih =>
      have hwHead : w ∉ Set.range e := hw e (by simp)
      have hwTail : ∀ f ∈ es, w ∉ Set.range f := by
        intro f hf
        exact hw f (List.mem_cons_of_mem e hf)
      rw [genScatterBatch_cons, genNetwork_exec_append]
      rw [ih hwTail ((genScatter net e).exec v)]
      exact genScatter_exec_outside net e v w hwHead

/-- On each member support, a batch acts exactly as that support's local
network. Other batch members cannot alter its inputs or outputs. -/
theorem genScatterBatch_exec_inside {M N : Nat} {α : Type} [LinearOrder α]
    (net : ComparatorNetwork M) (supports : List (Fin M ↪ Fin N))
    (hnd : supports.Nodup)
    (hdis : ∀ e ∈ supports, ∀ f ∈ supports, e ≠ f → ∀ i j, e i ≠ f j)
    (v : Fin N → α) (e : Fin M ↪ Fin N) (he : e ∈ supports) (i : Fin M) :
    (genScatterBatch net supports).exec v (e i) =
      (genScatter net e).exec v (e i) := by
  induction supports generalizing v with
  | nil => simp at he
  | cons f fs ih =>
      have hnd' := List.nodup_cons.mp hnd
      by_cases hef : e = f
      · subst e
        have hwTail : ∀ g ∈ fs, f i ∉ Set.range g := by
          intro g hg hmem
          obtain ⟨j, hj⟩ := hmem
          have hfg : f ≠ g := by
            intro h
            exact hnd'.1 (h ▸ hg)
          exact (hdis f (by simp) g (List.mem_cons_of_mem f hg) hfg i j) hj.symm
        have hdisTail : ∀ g ∈ fs, ∀ h ∈ fs, g ≠ h → ∀ a b, g a ≠ h b := by
          intro g hg h hh hne
          exact hdis g (List.mem_cons_of_mem f hg) h
            (List.mem_cons_of_mem f hh) hne
        rw [genScatterBatch_cons, genNetwork_exec_append]
        rw [genScatterBatch_exec_outside net fs (f i) hwTail
          ((genScatter net f).exec v)]
      · have hefFs : e ∈ fs := by simpa [hef] using he
        have hdisFs : ∀ g ∈ fs, ∀ h ∈ fs, g ≠ h → ∀ a b, g a ≠ h b := by
          intro g hg h hh hne
          exact hdis g (List.mem_cons_of_mem f hg) h
            (List.mem_cons_of_mem f hh) hne
        have hcomp : (genScatter net f).exec v ∘ e = v ∘ e := by
          funext a
          exact genScatter_exec_outside net f v (e a) (by
            rintro ⟨j, hj⟩
            exact (hdis e he f (by simp) hef a j) hj.symm)
        rw [genScatterBatch_cons, genNetwork_exec_append]
        rw [ih hnd'.2 hdisFs ((genScatter net f).exec v) hefFs]
        rw [genScatter_exec_inside net e ((genScatter net f).exec v) i,
          genScatter_exec_inside net e v i]
        exact congrArg (fun x => net.exec x i) hcomp

/-- Sequentially store two networks on disjoint comparator supports; their
generalized-network depth is at most the larger component depth. -/
theorem genDisjointAppend_depth_le {N : Nat} (G H : GenNetwork N) (D : Nat)
    (hG : G.depth ≤ D) (hH : H.depth ≤ D)
    (hdis : ∀ c ∈ G.comparators, ∀ d ∈ H.comparators,
      c.a ≠ d.a ∧ c.a ≠ d.b ∧ c.b ≠ d.a ∧ c.b ≠ d.b) :
    (⟨G.comparators ++ H.comparators⟩ : GenNetwork N).depth ≤ D := by
  have hD : ∀ b ∈ ([true, false] : List Bool),
      (⟨(if b then G.comparators else H.comparators)⟩ : GenNetwork N).depth ≤ D := by
    intro b hb
    have hb' : b = true ∨ b = false := by simpa using hb
    rcases hb' with rfl | rfl <;> simp [hG, hH]
  have hpair : ([true, false] : List Bool).Pairwise
      (fun b c => ∀ x ∈ (if b then G.comparators else H.comparators),
        ∀ y ∈ (if c then G.comparators else H.comparators),
          x.a ≠ y.a ∧ x.a ≠ y.b ∧ x.b ≠ y.a ∧ x.b ≠ y.b) := by
    apply List.pairwise_cons.mpr
    constructor
    · intro b hb x hx y hy
      have hb' : b = false := by simpa using hb
      subst b
      simpa using hdis x hx y hy
    · simp
  simpa using genDepth_flatMap_disjoint ([true, false] : List Bool)
    (fun b => if b then G.comparators else H.comparators) D hD hpair

theorem genPacketRound_depth_le {N : Nat}
    (pairs : List (Fin 128 ↪ Fin N))
    (hnodup : pairs.Nodup)
    (hdis : ∀ e ∈ pairs, ∀ f ∈ pairs, e ≠ f →
      ∀ i j, e i ≠ f j) :
    (genPacketRound pairs).depth ≤ 7 := by
  have hchunks_aux : ∀ (ps : List (Fin 128 ↪ Fin N)), ps.Nodup →
      (∀ e ∈ ps, ∀ f ∈ ps, e ≠ f → ∀ i j, e i ≠ f j) →
      ps.Pairwise (fun e f =>
        ∀ c ∈ (genScatter (oddEvenMergeNet 7) e).comparators,
        ∀ d ∈ (genScatter (oddEvenMergeNet 7) f).comparators,
          c.a ≠ d.a ∧ c.a ≠ d.b ∧ c.b ≠ d.a ∧ c.b ≠ d.b) := by
    intro ps
    induction ps with
    | nil => intro hnodup' hdis'; simp
    | cons e es ih =>
        intro hnodup' hdis'
        have hnd := List.nodup_cons.mp hnodup'
        have hdisTail : ∀ a ∈ es, ∀ b ∈ es, a ≠ b → ∀ i j, a i ≠ b j := by
          intro a ha b hb hne i j
          exact hdis' a (List.mem_cons_of_mem e ha) b (List.mem_cons_of_mem e hb) hne i j
        refine List.pairwise_cons.mpr ⟨?_, ih hnd.2 hdisTail⟩
        intro f hf c hc d hd
        have hef : e ≠ f := by
          intro heq
          subst f
          exact hnd.1 hf
        have hwire := hdis' e (by simp) f (List.mem_cons_of_mem e hf) hef
        change c ∈ (oddEvenMergeNet 7).comparators.map (genScatterComparator e) at hc
        change d ∈ (oddEvenMergeNet 7).comparators.map (genScatterComparator f) at hd
        obtain ⟨c₀, _, rfl⟩ := List.mem_map.mp hc
        obtain ⟨d₀, _, rfl⟩ := List.mem_map.mp hd
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [genScatterComparator] using hwire c₀.i d₀.i
        · simpa [genScatterComparator] using hwire c₀.i d₀.j
        · simpa [genScatterComparator] using hwire c₀.j d₀.i
        · simpa [genScatterComparator] using hwire c₀.j d₀.j
  have hchunks := hchunks_aux pairs hnodup hdis
  have hbound : ∀ e ∈ pairs,
      (⟨(genScatter (oddEvenMergeNet 7) e).comparators⟩ : GenNetwork N).depth ≤ 7 := by
    intro e he
    exact genMerge128_depth_le e
  exact genDepth_flatMap_disjoint pairs
    (fun e => (genScatter (oddEvenMergeNet 7) e).comparators) 7 hbound hchunks

theorem genPacketRound_exec_outside {N : Nat} {α : Type} [LinearOrder α]
    (pairs : List (Fin 128 ↪ Fin N))
    (hnodup : pairs.Nodup)
    (hdis : ∀ e ∈ pairs, ∀ f ∈ pairs, e ≠ f →
      ∀ i j, e i ≠ f j)
    (w : Fin N)
    (hw : ∀ e ∈ pairs, w ∉ Set.range e)
    (v : Fin N → α) :
    (genPacketRound pairs).exec v w = v w := by
  induction pairs generalizing v with
  | nil => rfl
  | cons e es ih =>
      have hnodup' := List.nodup_cons.mp hnodup
      have hwHead : w ∉ Set.range e := hw e (by simp)
      have hwTail : ∀ f ∈ es, w ∉ Set.range f := by
        intro f hf
        exact hw f (List.mem_cons_of_mem e hf)
      have hdisTail : ∀ f ∈ es, ∀ g ∈ es, f ≠ g → ∀ i j, f i ≠ g j := by
        intro f hf g hg hne
        exact hdis f (List.mem_cons_of_mem e hf) g (List.mem_cons_of_mem e hg) hne
      rw [genPacketRound_cons, genNetwork_exec_append]
      rw [ih hnodup'.2 hdisTail hwTail ((genScatter (oddEvenMergeNet 7) e).exec v)]
      exact genScatter_exec_outside (oddEvenMergeNet 7) e v w hwHead

theorem genPacketRound_exec_inside {N : Nat} {α : Type} [LinearOrder α]
    (pairs : List (Fin 128 ↪ Fin N))
    (hnodup : pairs.Nodup)
    (hdis : ∀ e ∈ pairs, ∀ f ∈ pairs, e ≠ f →
      ∀ i j, e i ≠ f j)
    (v : Fin N → α) (e : Fin 128 ↪ Fin N) (he : e ∈ pairs)
    (i : Fin 128) :
    (genPacketRound pairs).exec v (e i) =
      (genScatter (oddEvenMergeNet 7) e).exec v (e i) := by
  induction pairs generalizing v with
  | nil => simp at he
  | cons f fs ih =>
      have hnodup' := List.nodup_cons.mp hnodup
      by_cases hfe : e = f
      · subst e
        have hwTail : ∀ g ∈ fs, f i ∉ Set.range g := by
          intro g hg hmem
          obtain ⟨j, hj⟩ := hmem
          have hfg : f ≠ g := by
            intro h
            exact hnodup'.1 (h ▸ hg)
          exact (hdis f (by simp) g (List.mem_cons_of_mem f hg)
            hfg i j) hj.symm
        have hdisTail : ∀ g ∈ fs, ∀ h ∈ fs, g ≠ h → ∀ a b, g a ≠ h b := by
          intro g hg h hh hne
          exact hdis g (List.mem_cons_of_mem f hg) h (List.mem_cons_of_mem f hh) hne
        rw [genPacketRound_cons, genNetwork_exec_append]
        rw [genPacketRound_exec_outside fs hnodup'.2 hdisTail (f i) hwTail
          ((genScatter (oddEvenMergeNet 7) f).exec v)]
      · have hefs : e ∈ fs := by simpa [hfe] using he
        have hdisFs : ∀ g ∈ fs, ∀ h ∈ fs, g ≠ h → ∀ a b, g a ≠ h b := by
          intro g hg h hh hne
          exact hdis g (List.mem_cons_of_mem f hg) h (List.mem_cons_of_mem f hh) hne
        have hcomp : (genScatter (oddEvenMergeNet 7) f).exec v ∘ e = v ∘ e := by
          funext a
          exact genScatter_exec_outside (oddEvenMergeNet 7) f v (e a) (by
            rintro ⟨j, hj⟩
            exact (hdis e he f (by simp) hfe a j) hj.symm)
        rw [genPacketRound_cons, genNetwork_exec_append]
        rw [ih hnodup'.2 hdisFs ((genScatter (oddEvenMergeNet 7) f).exec v) hefs]
        rw [genScatter_exec_inside (oddEvenMergeNet 7) e ((genScatter (oddEvenMergeNet 7) f).exec v) i,
          genScatter_exec_inside (oddEvenMergeNet 7) e v i]
        exact congrArg (fun x => (oddEvenMergeNet 7).exec x i) hcomp

theorem genPacketRound_dealt_lanes_sorted {N : Nat} {α : Type} [LinearOrder α]
    (pairs : List (Fin 128 ↪ Fin N))
    (hnodup : pairs.Nodup)
    (hdis : ∀ e ∈ pairs, ∀ f ∈ pairs, e ≠ f →
      ∀ i j, e i ≠ f j)
    (v : Fin N → α)
    (hsorted : ∀ e ∈ pairs,
      Monotone (fun i : Fin 64 => v (e (Fin.castAdd 64 i))) ∧
      Monotone (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))) :
    ∀ e ∈ pairs,
      Monotone (fun i : Fin 64 =>
        (genPacketRound pairs).exec v (dealEvenEmbedding e i)) ∧
      Monotone (fun i : Fin 64 =>
        (genPacketRound pairs).exec v (dealOddEmbedding e i)) := by
  intro e he
  have hlocal := genMerge128_dealt_lanes_sorted e v (hsorted e he).1 (hsorted e he).2
  constructor
  · intro i j hij
    change (genPacketRound pairs).exec v (e (evenWire 64 i)) ≤
      (genPacketRound pairs).exec v (e (evenWire 64 j))
    rw [genPacketRound_exec_inside pairs hnodup hdis v e he (evenWire 64 i),
      genPacketRound_exec_inside pairs hnodup hdis v e he (evenWire 64 j)]
    exact hlocal.1 hij
  · intro i j hij
    change (genPacketRound pairs).exec v (e (oddWire 64 i)) ≤
      (genPacketRound pairs).exec v (e (oddWire 64 j))
    rw [genPacketRound_exec_inside pairs hnodup hdis v e he (oddWire 64 i),
      genPacketRound_exec_inside pairs hnodup hdis v e he (oddWire 64 j)]
    exact hlocal.2 hij

theorem genPacketRound_dealt_supports_disjoint {N : Nat}
    (pairs : List (Fin 128 ↪ Fin N))
    (hdis : ∀ e ∈ pairs, ∀ f ∈ pairs, e ≠ f →
      ∀ i j, e i ≠ f j) :
    (∀ e ∈ pairs, ∀ i j,
      dealEvenEmbedding e i ≠ dealOddEmbedding e j) ∧
    (∀ e ∈ pairs, ∀ f ∈ pairs, e ≠ f → ∀ i j,
      dealEvenEmbedding e i ≠ dealEvenEmbedding f j ∧
      dealEvenEmbedding e i ≠ dealOddEmbedding f j ∧
      dealOddEmbedding e i ≠ dealEvenEmbedding f j ∧
      dealOddEmbedding e i ≠ dealOddEmbedding f j) := by
  constructor
  · intro e he i j
    exact dealEmbeddings_disjoint e i j
  · intro e he f hf hef i j
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hdis e he f hf hef (evenWire 64 i) (evenWire 64 j)
    · exact hdis e he f hf hef (evenWire 64 i) (oddWire 64 j)
    · exact hdis e he f hf hef (oddWire 64 i) (evenWire 64 j)
    · exact hdis e he f hf hef (oddWire 64 i) (oddWire 64 j)

/-- The explicit packet family available as input to the next matching round. -/
def genPacketRound_outputPackets {N : Nat} (pairs : List (Fin 128 ↪ Fin N)) :
    List (Fin 64 ↪ Fin N) :=
  pairs.flatMap fun e => [dealEvenEmbedding e, dealOddEmbedding e]

theorem genPacketRound_outputPackets_sorted {N : Nat} {α : Type} [LinearOrder α]
    (pairs : List (Fin 128 ↪ Fin N))
    (hnodup : pairs.Nodup)
    (hdis : ∀ e ∈ pairs, ∀ f ∈ pairs, e ≠ f →
      ∀ i j, e i ≠ f j)
    (v : Fin N → α)
    (hsorted : ∀ e ∈ pairs,
      Monotone (fun i : Fin 64 => v (e (Fin.castAdd 64 i))) ∧
      Monotone (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))) :
    ∀ p ∈ genPacketRound_outputPackets pairs,
      Monotone (fun i => (genPacketRound pairs).exec v (p i)) := by
  intro p hp
  simp [genPacketRound_outputPackets] at hp
  obtain ⟨e, he, hp⟩ := hp
  rcases hp with rfl | rfl
  · exact (genPacketRound_dealt_lanes_sorted pairs hnodup hdis v hsorted e he).1
  · exact (genPacketRound_dealt_lanes_sorted pairs hnodup hdis v hsorted e he).2

theorem genPacketRound_outputPackets_support {N : Nat}
    (pairs : List (Fin 128 ↪ Fin N)) (w : Fin N) :
    (∃ p ∈ genPacketRound_outputPackets pairs, w ∈ Set.range p) ↔
      ∃ e ∈ pairs, w ∈ Set.range e := by
  constructor
  · rintro ⟨p, hp, ⟨i, rfl⟩⟩
    simp [genPacketRound_outputPackets] at hp
    obtain ⟨e, he, hp⟩ := hp
    rcases hp with rfl | rfl
    · exact ⟨e, he, ⟨evenWire 64 i, rfl⟩⟩
    · exact ⟨e, he, ⟨oddWire 64 i, rfl⟩⟩
  · rintro ⟨e, he, ⟨i, rfl⟩⟩
    have hw : e i ∈ Set.range (dealEvenEmbedding e) ∪ Set.range (dealOddEmbedding e) := by
      rw [dealEmbeddings_partition e]
      exact ⟨i, rfl⟩
    rcases hw with hw | hw
    · obtain ⟨j, hj⟩ := hw
      refine ⟨dealEvenEmbedding e, ?_, ⟨j, hj⟩⟩
      change dealEvenEmbedding e ∈ List.flatMap
        (fun f => [dealEvenEmbedding f, dealOddEmbedding f]) pairs
      rw [List.mem_flatMap]
      exact ⟨e, he, by simp⟩
    · obtain ⟨j, hj⟩ := hw
      refine ⟨dealOddEmbedding e, ?_, ⟨j, hj⟩⟩
      change dealOddEmbedding e ∈ List.flatMap
        (fun f => [dealEvenEmbedding f, dealOddEmbedding f]) pairs
      rw [List.mem_flatMap]
      exact ⟨e, he, by simp⟩

theorem genPacketRound_outputPackets_disjoint {N : Nat}
    (pairs : List (Fin 128 ↪ Fin N))
    (hnodup : pairs.Nodup)
    (hdis : ∀ e ∈ pairs, ∀ f ∈ pairs, e ≠ f →
      ∀ i j, e i ≠ f j) :
    List.Pairwise (fun p q : Fin 64 ↪ Fin N => ∀ i j, p i ≠ q j)
      (genPacketRound_outputPackets pairs) := by
  have aux : ∀ (ps : List (Fin 128 ↪ Fin N)), ps.Nodup →
      (∀ e ∈ ps, ∀ f ∈ ps, e ≠ f → ∀ i j, e i ≠ f j) →
      List.Pairwise (fun p q : Fin 64 ↪ Fin N => ∀ i j, p i ≠ q j)
        (genPacketRound_outputPackets ps) := by
    intro ps
    induction ps with
    | nil => intro hnodup' hdis'; simp [genPacketRound_outputPackets]
    | cons e es ih =>
        intro hnodup' hdis'
        have hnd := List.nodup_cons.mp hnodup'
        have hdisTail : ∀ a ∈ es, ∀ b ∈ es, a ≠ b → ∀ i j, a i ≠ b j := by
          intro a ha b hb hne i j
          exact hdis' a (List.mem_cons_of_mem e ha) b (List.mem_cons_of_mem e hb) hne i j
        have hcross : ∀ f ∈ es, ∀ i j,
            (dealEvenEmbedding e i ≠ dealEvenEmbedding f j ∧
             dealEvenEmbedding e i ≠ dealOddEmbedding f j) ∧
            (dealOddEmbedding e i ≠ dealEvenEmbedding f j ∧
             dealOddEmbedding e i ≠ dealOddEmbedding f j) := by
          intro f hf i j
          have hef : e ≠ f := by
            intro heq
            subst f
            exact hnd.1 hf
          have hwire := hdis' e (by simp) f (List.mem_cons_of_mem e hf) hef
          exact ⟨⟨hwire (evenWire 64 i) (evenWire 64 j),
              hwire (evenWire 64 i) (oddWire 64 j)⟩,
            ⟨hwire (oddWire 64 i) (evenWire 64 j),
              hwire (oddWire 64 i) (oddWire 64 j)⟩⟩
        change List.Pairwise (fun p q : Fin 64 ↪ Fin N => ∀ i j, p i ≠ q j)
          (dealEvenEmbedding e :: dealOddEmbedding e ::
            genPacketRound_outputPackets es)
        refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_,
          ih hnd.2 hdisTail⟩⟩
        · intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · intro i j
            exact dealEmbeddings_disjoint e i j
          · simp [genPacketRound_outputPackets] at hp
            obtain ⟨f, hf, rfl | rfl⟩ := hp
            · intro i j
              exact (hcross f hf i j).1.1
            · intro i j
              exact (hcross f hf i j).1.2
        · intro p hp
          simp [genPacketRound_outputPackets] at hp
          obtain ⟨f, hf, rfl | rfl⟩ := hp
          · intro i j
            exact (hcross f hf i j).2.1
          · intro i j
            exact (hcross f hf i j).2.2
  exact aux pairs hnodup hdis

theorem genJoinMatching_round_depth_le {N : Nat}
    (matching : List ((Fin 64 ↪ Fin N) × (Fin 64 ↪ Fin N)))
    (hwithin : ∀ e : (Fin 64 ↪ Fin N) × (Fin 64 ↪ Fin N),
      ∀ i j, e.1 i ≠ e.2 j)
    (hnodup : matching.Nodup)
    (hmatching : ∀ e ∈ matching, ∀ f ∈ matching, e ≠ f → ∀ i j,
      e.1 i ≠ f.1 j ∧ e.1 i ≠ f.2 j ∧
      e.2 i ≠ f.1 j ∧ e.2 i ≠ f.2 j) :
    (genPacketRound (genJoinMatching matching hwithin)).depth ≤ 7 := by
  exact genPacketRound_depth_le (genJoinMatching matching hwithin)
    (genJoinMatching_nodup matching hwithin hnodup hmatching)
    (genJoinMatching_disjoint matching hwithin hmatching)

theorem genJoinMatching_round_outputPackets_sorted {N : Nat} {α : Type}
    [LinearOrder α]
    (matching : List ((Fin 64 ↪ Fin N) × (Fin 64 ↪ Fin N)))
    (hwithin : ∀ e : (Fin 64 ↪ Fin N) × (Fin 64 ↪ Fin N),
      ∀ i j, e.1 i ≠ e.2 j)
    (hnodup : matching.Nodup)
    (hmatching : ∀ e ∈ matching, ∀ f ∈ matching, e ≠ f → ∀ i j,
      e.1 i ≠ f.1 j ∧ e.1 i ≠ f.2 j ∧
      e.2 i ≠ f.1 j ∧ e.2 i ≠ f.2 j)
    (v : Fin N → α)
    (hsorted : ∀ e ∈ matching,
      Monotone (fun i : Fin 64 => v (e.1 i)) ∧
      Monotone (fun i : Fin 64 => v (e.2 i))) :
    ∀ p ∈ genPacketRound_outputPackets (genJoinMatching matching hwithin),
      Monotone (fun i =>
        (genPacketRound (genJoinMatching matching hwithin)).exec v (p i)) := by
  apply genPacketRound_outputPackets_sorted
    (genJoinMatching matching hwithin)
    (genJoinMatching_nodup matching hwithin hnodup hmatching)
    (genJoinMatching_disjoint matching hwithin hmatching) v
  intro e he
  simp only [genJoinMatching, List.mem_map] at he
  obtain ⟨edge, hedge, rfl⟩ := he
  constructor
  · intro i j hij
    change v (joinPacketEmbedding edge.1 edge.2 (hwithin edge) (Fin.castAdd 64 i)) ≤
      v (joinPacketEmbedding edge.1 edge.2 (hwithin edge) (Fin.castAdd 64 j))
    have hi := joinPacketEmbedding_left edge.1 edge.2 (hwithin edge) i
    have hj := joinPacketEmbedding_left edge.1 edge.2 (hwithin edge) j
    rw [hi, hj]
    exact (hsorted edge hedge).1 hij
  · intro i j hij
    change v (joinPacketEmbedding edge.1 edge.2 (hwithin edge) (Fin.natAdd 64 i)) ≤
      v (joinPacketEmbedding edge.1 edge.2 (hwithin edge) (Fin.natAdd 64 j))
    have hi := joinPacketEmbedding_right edge.1 edge.2 (hwithin edge) i
    have hj := joinPacketEmbedding_right edge.1 edge.2 (hwithin edge) j
    rw [hi, hj]
    exact (hsorted edge hedge).2 hij

theorem genJoinMatching_round_outputPackets_disjoint {N : Nat}
    (matching : List ((Fin 64 ↪ Fin N) × (Fin 64 ↪ Fin N)))
    (hwithin : ∀ e : (Fin 64 ↪ Fin N) × (Fin 64 ↪ Fin N),
      ∀ i j, e.1 i ≠ e.2 j)
    (hnodup : matching.Nodup)
    (hmatching : ∀ e ∈ matching, ∀ f ∈ matching, e ≠ f → ∀ i j,
      e.1 i ≠ f.1 j ∧ e.1 i ≠ f.2 j ∧
      e.2 i ≠ f.1 j ∧ e.2 i ≠ f.2 j) :
    List.Pairwise (fun p q : Fin 64 ↪ Fin N => ∀ i j, p i ≠ q j)
      (genPacketRound_outputPackets (genJoinMatching matching hwithin)) := by
  exact genPacketRound_outputPackets_disjoint _
    (genJoinMatching_nodup matching hwithin hnodup hmatching)
    (genJoinMatching_disjoint matching hwithin hmatching)

theorem genJoinMatching_round_outputPackets_support {N : Nat}
    (matching : List ((Fin 64 ↪ Fin N) × (Fin 64 ↪ Fin N)))
    (hwithin : ∀ e : (Fin 64 ↪ Fin N) × (Fin 64 ↪ Fin N),
      ∀ i j, e.1 i ≠ e.2 j)
    (w : Fin N) :
    (∃ p ∈ genPacketRound_outputPackets (genJoinMatching matching hwithin),
      w ∈ Set.range p) ↔
    ∃ e ∈ matching, w ∈ Set.range e.1 ∨ w ∈ Set.range e.2 := by
  rw [genPacketRound_outputPackets_support]
  constructor
  · rintro ⟨e, he, hw⟩
    simp only [genJoinMatching, List.mem_map] at he
    obtain ⟨edge, hedge, rfl⟩ := he
    rw [joinPacketEmbedding_range edge.1 edge.2 (hwithin edge)] at hw
    exact ⟨edge, hedge, hw⟩
  · rintro ⟨edge, hedge, hw⟩
    refine ⟨joinPacketEmbedding edge.1 edge.2 (hwithin edge), ?_, ?_⟩
    · change joinPacketEmbedding edge.1 edge.2 (hwithin edge) ∈
        matching.map (fun p => joinPacketEmbedding p.1 p.2 (hwithin p))
      rw [List.mem_map]
      exact ⟨edge, hedge, rfl⟩
    · rw [joinPacketEmbedding_range edge.1 edge.2 (hwithin edge)]
      exact hw

/-- Execute one generalized odd-even merge round on an indexed packet matching. -/
def genIndexedPacketRound {m N : Nat}
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m))
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2) : GenNetwork N :=
  genPacketRound (genIndexedPairSupports packets hpacketDisjoint edges hnoFixed)

def genIndexedPacketRoundOutput {m N : Nat}
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m))
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2) : List (Fin 64 ↪ Fin N) :=
  genPacketRound_outputPackets (genIndexedPairSupports packets hpacketDisjoint edges hnoFixed)

theorem genIndexedPacketRound_depth_le {m N : Nat}
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m)) (hedges : edges.Nodup)
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2)
    (hvertexDisjoint : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) :
    (genIndexedPacketRound packets hpacketDisjoint edges hnoFixed).depth ≤ 7 := by
  change (genPacketRound (genIndexedPairSupports packets hpacketDisjoint edges hnoFixed)).depth ≤ 7
  exact genPacketRound_depth_le _
    (genIndexedPairSupports_nodup packets hpacketDisjoint edges hedges hnoFixed hvertexDisjoint)
    (by
      intro e he f hf hne i j
      exact genIndexedPairSupports_disjoint packets hpacketDisjoint edges hnoFixed
        hvertexDisjoint e he f hf hne i j)

theorem genIndexedPacketRound_output_sorted {m N : Nat} {α : Type}
    [LinearOrder α]
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m)) (hedges : edges.Nodup)
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2)
    (hvertexDisjoint : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)
    (v : Fin N → α)
    (hsorted : ∀ i, Monotone (fun k : Fin 64 => v (packets i k))) :
    ∀ p ∈ genIndexedPacketRoundOutput packets hpacketDisjoint edges hnoFixed,
      Monotone (fun k => (genIndexedPacketRound packets hpacketDisjoint edges hnoFixed).exec v (p k)) := by
  change ∀ p ∈ genPacketRound_outputPackets
      (genIndexedPairSupports packets hpacketDisjoint edges hnoFixed),
    Monotone (fun k => (genPacketRound
      (genIndexedPairSupports packets hpacketDisjoint edges hnoFixed)).exec v (p k))
  apply genPacketRound_outputPackets_sorted _
    (genIndexedPairSupports_nodup packets hpacketDisjoint edges hedges hnoFixed hvertexDisjoint)
    (by
      intro e he f hf hne i j
      exact genIndexedPairSupports_disjoint packets hpacketDisjoint edges hnoFixed
        hvertexDisjoint e he f hf hne i j) v
  intro e he
  simp only [genIndexedPairSupports, List.mem_map, List.mem_attach] at he
  obtain ⟨edge, hedge, rfl⟩ := he
  have hwithin := hpacketDisjoint edge.1.1 edge.1.2 (hnoFixed edge.1 edge.2)
  constructor
  · intro i j hij
    change v (joinPacketEmbedding (packets edge.1.1) (packets edge.1.2) hwithin
      (Fin.castAdd 64 i)) ≤
      v (joinPacketEmbedding (packets edge.1.1) (packets edge.1.2) hwithin
      (Fin.castAdd 64 j))
    rw [joinPacketEmbedding_left, joinPacketEmbedding_left]
    exact hsorted edge.1.1 hij
  · intro i j hij
    change v (joinPacketEmbedding (packets edge.1.1) (packets edge.1.2) hwithin
      (Fin.natAdd 64 i)) ≤
      v (joinPacketEmbedding (packets edge.1.1) (packets edge.1.2) hwithin
      (Fin.natAdd 64 j))
    rw [joinPacketEmbedding_right, joinPacketEmbedding_right]
    exact hsorted edge.1.2 hij

/- A physically ordered matched pair produces physically increasing dealt
packets, so this condition can be tested independently of value sortedness. -/
theorem genIndexedPacketRound_output_strictMono {m N : Nat}
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m))
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2)
    (hpacketMono : ∀ i, StrictMono (packets i))
    (hordered : ∀ e ∈ edges, ∀ x y, packets e.1 x < packets e.2 y) :
    ∀ p ∈ genIndexedPacketRoundOutput packets hpacketDisjoint edges hnoFixed,
      StrictMono p := by
  intro p hp
  change p ∈ genPacketRound_outputPackets
    (genIndexedPairSupports packets hpacketDisjoint edges hnoFixed) at hp
  simp only [genPacketRound_outputPackets, List.mem_flatMap] at hp
  obtain ⟨joined, hjoined, hp⟩ := hp
  simp only [genIndexedPairSupports, List.mem_map, List.mem_attach] at hjoined
  obtain ⟨edge, hedge, rfl⟩ := hjoined
  have hjoinedMono : StrictMono
      (joinPacketEmbedding (packets edge.1.1) (packets edge.1.2)
        (hpacketDisjoint edge.1.1 edge.1.2 (hnoFixed edge.1 edge.2))) :=
    joinPacketEmbedding_strictMono _ _ _ (hpacketMono edge.1.1)
      (hpacketMono edge.1.2) (hordered edge.1 edge.2)
  rcases (by simpa [genPacketRound_outputPackets] using hp) with hp | hp
  · rw [hp]
    exact dealEvenEmbedding_strictMono _ hjoinedMono
  · rw [hp]
    exact dealOddEmbedding_strictMono _ hjoinedMono

theorem genIndexedPacketRound_output_support {m N : Nat}
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m))
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2)
    (hcover : ∀ i, ∃ e ∈ edges, e.1 = i ∨ e.2 = i)
    (w : Fin N) :
    (∃ p ∈ genIndexedPacketRoundOutput packets hpacketDisjoint edges hnoFixed,
      w ∈ Set.range p) ↔ ∃ i, w ∈ Set.range (packets i) := by
  change (∃ p ∈ genPacketRound_outputPackets
      (genIndexedPairSupports packets hpacketDisjoint edges hnoFixed),
        w ∈ Set.range p) ↔ ∃ i, w ∈ Set.range (packets i)
  rw [genPacketRound_outputPackets_support]
  constructor
  · rintro ⟨e, he, hw⟩
    simp only [genIndexedPairSupports, List.mem_map, List.mem_attach] at he
    obtain ⟨edge, hedge, rfl⟩ := he
    rw [joinPacketEmbedding_range _ _
      (hpacketDisjoint edge.1.1 edge.1.2 (hnoFixed edge.1 edge.2))] at hw
    rcases hw with hw | hw
    · exact ⟨edge.1.1, hw⟩
    · exact ⟨edge.1.2, hw⟩
  · rintro ⟨i, hi⟩
    obtain ⟨edge, hedge, hside⟩ := hcover i
    let joined := joinPacketEmbedding (packets edge.1) (packets edge.2)
      (hpacketDisjoint edge.1 edge.2 (hnoFixed edge hedge))
    have hmem : joined ∈ genIndexedPairSupports packets hpacketDisjoint edges hnoFixed := by
      simp only [genIndexedPairSupports, List.mem_map, List.mem_attach]
      exact ⟨⟨edge, hedge⟩, trivial, rfl⟩
    refine ⟨joined, hmem, ?_⟩
    rw [joinPacketEmbedding_range]
    rcases hside with hleft | hright
    · exact Or.inl (hleft ▸ hi)
    · exact Or.inr (hright ▸ hi)

theorem genIndexedPacketRound_output_disjoint {m N : Nat}
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m)) (hedges : edges.Nodup)
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2)
    (hvertexDisjoint : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) :
    List.Pairwise (fun p q : Fin 64 ↪ Fin N => ∀ i j, p i ≠ q j)
      (genIndexedPacketRoundOutput packets hpacketDisjoint edges hnoFixed) := by
  change List.Pairwise (fun p q : Fin 64 ↪ Fin N => ∀ i j, p i ≠ q j)
    (genPacketRound_outputPackets
      (genIndexedPairSupports packets hpacketDisjoint edges hnoFixed))
  exact genPacketRound_outputPackets_disjoint _
    (genIndexedPairSupports_nodup packets hpacketDisjoint edges hedges hnoFixed hvertexDisjoint)
    (genIndexedPairSupports_disjoint packets hpacketDisjoint edges hnoFixed hvertexDisjoint)

/-- The canonical matching of adjacent packet IDs in an even-sized family. -/
def adjacentPacketMatching (k : Nat) : List (Fin (2 * k) × Fin (2 * k)) :=
  (List.finRange k).map fun i =>
    (⟨2 * i.val, by omega⟩, ⟨2 * i.val + 1, by omega⟩)

theorem adjacentPacketMatching_nodup (k : Nat) :
    (adjacentPacketMatching k).Nodup := by
  unfold adjacentPacketMatching
  apply List.Nodup.map_on
  · intro i hi j hj heq
    have hv := congrArg (fun e : Fin (2 * k) × Fin (2 * k) => e.1.val) heq
    simp at hv
    apply Fin.ext
    omega
  · exact List.nodup_finRange k

theorem adjacentPacketMatching_noFixed (k : Nat) :
    ∀ e ∈ adjacentPacketMatching k, e.1 ≠ e.2 := by
  intro e he
  simp only [adjacentPacketMatching, List.mem_map, List.mem_finRange] at he
  obtain ⟨i, hi, heq⟩ := he
  rw [← heq]
  intro h
  have hv := congrArg Fin.val h
  simp at hv
  all_goals omega

theorem adjacentPacketMatching_vertexDisjoint (k : Nat) :
    ∀ e ∈ adjacentPacketMatching k, ∀ f ∈ adjacentPacketMatching k, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
  intro e he f hf hne
  simp only [adjacentPacketMatching, List.mem_map, List.mem_finRange] at he hf
  obtain ⟨i, hi, rfl⟩ := he
  obtain ⟨j, hj, rfl⟩ := hf
  have hij : i ≠ j := by
    intro h
    apply hne
    subst j
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega

theorem adjacentPacketMatching_covers (k : Nat) (i : Fin (2 * k)) :
    ∃ e ∈ adjacentPacketMatching k, e.1 = i ∨ e.2 = i := by
  by_cases heven : i.val % 2 = 0
  · let j : Fin k := ⟨i.val / 2, by have := i.isLt; omega⟩
    refine ⟨(⟨2 * j.val, by omega⟩, ⟨2 * j.val + 1, by omega⟩), ?_, Or.inl ?_⟩
    · simp only [adjacentPacketMatching, List.mem_map]
      exact ⟨j, by simpa using j.isLt, rfl⟩
    · apply Fin.ext
      simp [j]
      omega
  · let j : Fin k := ⟨i.val / 2, by have := i.isLt; omega⟩
    refine ⟨(⟨2 * j.val, by omega⟩, ⟨2 * j.val + 1, by omega⟩), ?_, Or.inr ?_⟩
    · simp only [adjacentPacketMatching, List.mem_map]
      exact ⟨j, by simpa using j.isLt, rfl⟩
    · apply Fin.ext
      simp [j]
      omega


end Chvatal.PacketAlignment
