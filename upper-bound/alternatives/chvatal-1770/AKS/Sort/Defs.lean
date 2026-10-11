module
/- Comparator network definitions: comparators, networks, execution, embeddings. -/

public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.Basic

@[expose] public section

open Finset BigOperators

/-- A comparator on `n` wires swaps positions `i` and `j` if out of order. -/
structure Comparator (n : ℕ) where
  i : Fin n
  j : Fin n
  h : i < j

/-- Apply a single comparator to a vector. -/
def Comparator.apply {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) : Fin n → α :=
  fun k ↦
    if k = c.i then min (v c.i) (v c.j)
    else if k = c.j then max (v c.i) (v c.j)
    else v k

/-- A comparator network is a sequence of comparators applied in order. -/
@[ext] structure ComparatorNetwork (n : ℕ) where
  comparators : List (Comparator n)

/-- Execute an entire comparator network on an input vector. -/
def ComparatorNetwork.exec {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) : Fin n → α :=
  net.comparators.foldl (fun acc c ↦ c.apply acc) v

/-- When `w(c.i) ≤ w(c.j)`, the comparator is the identity. -/
lemma Comparator.apply_eq_of_le {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (w : Fin n → α) (h : w c.i ≤ w c.j) :
    c.apply w = w := by
  ext pos; unfold Comparator.apply
  split_ifs with h1 h2
  · rw [h1, min_eq_left h]
  · rw [h2, max_eq_right h]
  · rfl

/-- When `w(c.j) < w(c.i)`, the comparator swaps positions `i` and `j`. -/
lemma Comparator.apply_eq_swap {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (w : Fin n → α) (h : w c.j < w c.i) (pos : Fin n) :
    c.apply w pos = w (Equiv.swap c.i c.j pos) := by
  unfold Comparator.apply
  split_ifs with h1 h2
  · rw [h1, min_eq_right h.le, Equiv.swap_apply_left]
  · rw [h2, max_eq_left h.le, Equiv.swap_apply_right]
  · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- A single comparator preserves injectivity. -/
theorem Comparator.apply_injective {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) {v : Fin n → α} (hv : Function.Injective v) :
    Function.Injective (c.apply v) := by
  by_cases h : v c.i ≤ v c.j
  · rwa [c.apply_eq_of_le v h]
  · rw [show c.apply v = v ∘ Equiv.swap c.i c.j from
      funext (c.apply_eq_swap v (not_le.1 h))]
    exact hv.comp (Equiv.injective _)

/-- Executing a comparator network preserves injectivity. -/
theorem ComparatorNetwork.exec_injective {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) {v : Fin n → α} (hv : Function.Injective v) :
    Function.Injective (net.exec v) := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing v with
  | nil => exact hv
  | cons c cs ih => exact ih (c.apply_injective hv)

/-- Executing a concatenated comparator list equals sequential execution. -/
theorem ComparatorNetwork.exec_append {n : ℕ} {α : Type*} [LinearOrder α]
    (net₁ net₂ : ComparatorNetwork n) (v : Fin n → α) :
    (⟨net₁.comparators ++ net₂.comparators⟩ : ComparatorNetwork n).exec v =
    net₂.exec (net₁.exec v) := by
  simp [ComparatorNetwork.exec, List.foldl_append]

/-- Relabel wire indices by a permutation (output at `w` reads input at `π w`). -/
def permuteWireValues {n : ℕ} (π : Equiv.Perm (Fin n)) {α : Type*} (v : Fin n → α) :
    Fin n → α :=
  fun w ↦ v (π w)

/-- Folding comparators that do not touch position `j` leaves `v j` unchanged. -/
theorem foldl_comparators_outside {n : ℕ} {α : Type*} [LinearOrder α]
    (cs : List (Comparator n)) (v : Fin n → α) (j : Fin n)
    (hj : ∀ c ∈ cs, j ≠ c.i ∧ j ≠ c.j) :
    cs.foldl (fun acc c ↦ c.apply acc) v j = v j := by
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih =>
    have ⟨hji, hjj⟩ := hj c (.head cs)
    simp only [List.foldl_cons]
    rw [ih _ fun c' hc' => hj c' (.tail c hc')]
    simp [Comparator.apply, hji, hjj]

/-- Embed a network on `m` wires into `n` wires via an order embedding. -/
def ComparatorNetwork.scatterEmbed {m : ℕ} (net : ComparatorNetwork m)
    (n : ℕ) (f : Fin m ↪o Fin n) : ComparatorNetwork n where
  comparators := net.comparators.map fun c ↦
    { i := f c.i, j := f c.j, h := f.lt_iff_lt.mpr c.h }

/-- A scatter-embedded network does not modify positions outside the embedding's range. -/
theorem ComparatorNetwork.scatterEmbed_exec_outside {m : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork m) (n : ℕ) (f : Fin m ↪o Fin n)
    (v : Fin n → α) (j : Fin n) (hj : j ∉ Set.range f) :
    (net.scatterEmbed n f).exec v j = v j := by
  unfold scatterEmbed exec
  apply foldl_comparators_outside
  intro c' hc'
  simp only [List.mem_map] at hc'
  obtain ⟨c, _, rfl⟩ := hc'
  exact ⟨fun heq ↦ hj ⟨c.i, heq.symm⟩, fun heq ↦ hj ⟨c.j, heq.symm⟩⟩

/-- A scatter-embedded network acts on positions `f i` exactly as the original on `v ∘ f`. -/
theorem ComparatorNetwork.scatterEmbed_exec_inside {m : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork m) (n : ℕ) (f : Fin m ↪o Fin n)
    (v : Fin n → α) (i : Fin m) :
    (net.scatterEmbed n f).exec v (f i) = net.exec (v ∘ f) i := by
  suffices hfun : ∀ (cs : List (Comparator m)) (v : Fin n → α),
      (fun (j : Fin m) ↦
        (cs.map fun c ↦ (⟨f c.i, f c.j, f.lt_iff_lt.mpr c.h⟩ : Comparator n)).foldl
        (fun acc c ↦ c.apply acc) v (f j)) =
      cs.foldl (fun acc c ↦ c.apply acc) (v ∘ f) from
    congr_fun (hfun net.comparators v) i
  intro cs
  induction cs with
  | nil => intro v; rfl
  | cons c cs ih =>
    intro v
    simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    congr 1
    funext j
    simp only [Comparator.apply, Function.comp, f.injective.eq_iff]

/-- The order embedding `j ↦ offset + j`. -/
def shiftEmb {m n : ℕ} (offset : ℕ) (h : offset + m ≤ n) : Fin m ↪o Fin n :=
  OrderEmbedding.ofStrictMono (fun j ↦ ⟨offset + j.val, by have := j.isLt; omega⟩)
    fun a b hab ↦ by
      change offset + a.val < offset + b.val
      have : a.val < b.val := hab
      omega

/-- Shift all comparator indices by `offset` and embed into a larger network. -/
def ComparatorNetwork.shiftEmbed {m : ℕ} (net : ComparatorNetwork m)
    (n offset : ℕ) (h : offset + m ≤ n) : ComparatorNetwork n :=
  net.scatterEmbed n (shiftEmb offset h)

/-- A shifted+embedded network does not modify positions outside its range. -/
theorem ComparatorNetwork.shiftEmbed_exec_outside {m : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork m) (n offset : ℕ) (h : offset + m ≤ n)
    (v : Fin n → α) (j : Fin n) (hj : j.val < offset ∨ offset + m ≤ j.val) :
    (net.shiftEmbed n offset h).exec v j = v j := by
  apply scatterEmbed_exec_outside
  rintro ⟨i, rfl⟩
  have := i.isLt
  simp only [shiftEmb, OrderEmbedding.coe_ofStrictMono] at hj
  omega

/-- A shifted+embedded network acts on `[offset, offset+m)` as the original on the local view. -/
theorem ComparatorNetwork.shiftEmbed_exec_inside {m : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork m) (n offset : ℕ) (h : offset + m ≤ n)
    (v : Fin n → α) (i : Fin m) :
    (net.shiftEmbed n offset h).exec v ⟨offset + i.val, by have := i.isLt; omega⟩ =
    net.exec (fun (j : Fin m) ↦ v ⟨offset + j.val, by have := j.isLt; omega⟩) i :=
  scatterEmbed_exec_inside net n (shiftEmb offset h) v i

/-- Executing a flatMap of networks equals sequential execution. -/
theorem ComparatorNetwork.exec_flatMap {n : ℕ} {α : Type*} [LinearOrder α]
    {ι : Type*} (xs : List ι) (f : ι → ComparatorNetwork n) (v : Fin n → α) :
    (⟨xs.flatMap fun i ↦ (f i).comparators⟩ : ComparatorNetwork n).exec v =
    xs.foldl (fun v' i ↦ (f i).exec v') v := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.foldl_cons]
    rw [← ih]
    exact exec_append (f x) ⟨xs.flatMap fun i ↦ (f i).comparators⟩ v

/-- Folding execution of networks that do not touch j leaves j unchanged. -/
theorem ComparatorNetwork.foldl_exec_outside {n : ℕ} {α : Type*} [LinearOrder α]
    {ι : Type*} (xs : List ι) (f : ι → ComparatorNetwork n) (v : Fin n → α)
    (j : Fin n) (hj : ∀ a ∈ xs, ∀ c ∈ (f a).comparators, j ≠ c.i ∧ j ≠ c.j) :
    xs.foldl (fun v' a ↦ (f a).exec v') v j = v j := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih _ fun a ha ↦ hj a (List.mem_cons_of_mem x ha)]
    exact foldl_comparators_outside (f x).comparators v j (hj x List.mem_cons_self)

/-- Folding execution of networks that do not touch any position in S preserves S. -/
theorem ComparatorNetwork.foldl_exec_outside_set {n : ℕ} {α : Type*} [LinearOrder α]
    {ι : Type*} (xs : List ι) (f : ι → ComparatorNetwork n) (v : Fin n → α)
    (S : Finset (Fin n)) (hS : ∀ a ∈ xs, ∀ s ∈ S, ∀ c ∈ (f a).comparators, s ≠ c.i ∧ s ≠ c.j) :
    ∀ s ∈ S, xs.foldl (fun v' a ↦ (f a).exec v') v s = v s :=
  fun s hs ↦ foldl_exec_outside xs f v s fun a ha c hc ↦ hS a ha s hs c hc

/-- A scatter-embedded network's comparators don't touch positions outside the range. -/
theorem ComparatorNetwork.scatterEmbed_comparators_outside {m : ℕ}
    (net : ComparatorNetwork m) (n : ℕ) (f : Fin m ↪o Fin n)
    (j : Fin n) (hj : j ∉ Set.range f) (c : Comparator n)
    (hc : c ∈ (net.scatterEmbed n f).comparators) :
    j ≠ c.i ∧ j ≠ c.j := by
  simp only [scatterEmbed, List.mem_map] at hc
  obtain ⟨c', _, rfl⟩ := hc
  exact ⟨fun heq ↦ hj ⟨c'.i, heq.symm⟩, fun heq ↦ hj ⟨c'.j, heq.symm⟩⟩

end
