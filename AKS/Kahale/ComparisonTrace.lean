module

public import AKS.Sort.Displaced

/-! # Reconstruction from comparator decisions

The output and the list of swap decisions determine the input. This is the
structural basis for bounding rank-fiber entropy by the number of comparator
decisions. It does not establish an improved asymptotic lower bound.
-/

@[expose] public section

namespace Kahale

def undoComparator {n : ℕ} {α : Type*} (c : Comparator n) (swapped : Bool)
    (v : Fin n → α) : Fin n → α :=
  if swapped then fun i ↦ v (Equiv.swap c.i c.j i) else v

def comparisonTrace {n : ℕ} {α : Type*} [LinearOrder α] :
    List (Comparator n) → (Fin n → α) → List Bool
  | [], _ => []
  | c :: cs, v => decide (v c.j < v c.i) :: comparisonTrace cs (c.apply v)

def restoreTrace {n : ℕ} {α : Type*} :
    List (Comparator n) → List Bool → (Fin n → α) → (Fin n → α)
  | [], _, v => v
  | _ :: _, [], v => v
  | c :: cs, swapped :: rest, v => undoComparator c swapped (restoreTrace cs rest v)

theorem undoComparator_apply {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) :
    undoComparator c (decide (v c.j < v c.i)) (c.apply v) = v := by
  by_cases h : v c.j < v c.i
  · funext i
    simp [undoComparator, h, c.apply_eq_swap v h]
  · have hle : v c.i ≤ v c.j := le_of_not_gt h
    simp [undoComparator, h, c.apply_eq_of_le v hle]

theorem comparisonTrace_length {n : ℕ} {α : Type*} [LinearOrder α]
    (cs : List (Comparator n)) (v : Fin n → α) :
    (comparisonTrace cs v).length = cs.length := by
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih => simp [comparisonTrace, ih]

theorem comparator_strict_preimages {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (w v : Fin n → α) (hw : w c.i < w c.j) :
    c.apply v = w ↔ v = w ∨ v = fun i ↦ w (Equiv.swap c.i c.j i) := by
  constructor
  · intro hv
    have hu := undoComparator_apply c v
    rw [hv] at hu
    by_cases h : v c.j < v c.i
    · right
      simpa [undoComparator, h] using hu.symm
    · left
      simpa [undoComparator, h] using hu.symm
  · intro hv
    rcases hv with rfl | rfl
    · exact c.apply_eq_of_le v hw.le
    · funext i
      have hswap : (fun j ↦ w (Equiv.swap c.i c.j j)) c.j <
          (fun j ↦ w (Equiv.swap c.i c.j j)) c.i := by simpa using hw
      rw [c.apply_eq_swap _ hswap]
      simp

theorem restoreTrace_exec {n : ℕ} {α : Type*} [LinearOrder α]
    (cs : List (Comparator n)) (v : Fin n → α) :
    restoreTrace cs (comparisonTrace cs v) (ComparatorNetwork.mk cs |>.exec v) = v := by
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih =>
    change undoComparator c (decide (v c.j < v c.i))
      (restoreTrace cs (comparisonTrace cs (c.apply v))
        ((ComparatorNetwork.mk cs).exec (c.apply v))) = v
    rw [ih]
    exact undoComparator_apply c v

theorem exec_trace_injective {n : ℕ} {α : Type*} [LinearOrder α]
    (cs : List (Comparator n)) :
    Function.Injective (fun v : Fin n → α ↦
      ((ComparatorNetwork.mk cs).exec v, comparisonTrace cs v)) := by
  intro v w h
  have he := congrArg Prod.fst h
  have ht := congrArg Prod.snd h
  change (ComparatorNetwork.mk cs).exec v = (ComparatorNetwork.mk cs).exec w at he
  change comparisonTrace cs v = comparisonTrace cs w at ht
  calc
    v = restoreTrace cs (comparisonTrace cs v) ((ComparatorNetwork.mk cs).exec v) :=
      (restoreTrace_exec cs v).symm
    _ = restoreTrace cs (comparisonTrace cs w) ((ComparatorNetwork.mk cs).exec w) := by
      rw [he, ht]
    _ = w := restoreTrace_exec cs w

end Kahale
