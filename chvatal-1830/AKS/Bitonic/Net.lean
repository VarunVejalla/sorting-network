module
/-
  # Batcher's bitonic sorting network on `2^k` wires

  Everything is built from *parallel layers*: `layer σ` compares lower wire `i` with upper wire
  `σ i` of an `N + N` wire network (`σ = 1`: half-cleaner, `σ = Fin.revPerm`: flip), and `par`
  places two networks side by side on the two halves.

  - `bitonicMerge (k+1) = layer 1 ; par (bitonicMerge k) (bitonicMerge k)`
  - `bitonicSort (k+1) = par S S ; layer revPerm ; par (bitonicMerge k) (bitonicMerge k)`

  Depth is `≤ bitonicDepthBudget k = 1 + 2 + ⋯ + k` (Batcher, 1968).
-/

public import AKS.Sort.Depth

@[expose] public section

/-- Batcher's triangular depth budget `1 + 2 + ⋯ + k`. -/
def bitonicDepthBudget : ℕ → ℕ
  | 0 => 0
  | k + 1 => bitonicDepthBudget k + (k + 1)

open ComparatorNetwork

namespace Bitonic
variable {N n : ℕ}


/-- Lower half of a vector on `n = N + N` wires. -/
def lowH (hn : N + N = n) {α : Type*} (w : Fin n → α) : Fin N → α :=
  fun j => w ⟨j, by have := j.2; omega⟩

/-- Upper half of a vector on `n = N + N` wires. -/
def upH (hn : N + N = n) {α : Type*} (w : Fin n → α) : Fin N → α :=
  fun j => w ⟨N + j, by have := j.2; omega⟩

/-- Two networks on the lower and upper halves, side by side. -/
def par (hn : N + N = n) (A B : ComparatorNetwork N) : ComparatorNetwork n :=
  ⟨(A.shiftEmbed n 0 (by omega)).comparators ++ (B.shiftEmbed n N (by omega)).comparators⟩

theorem par_exec {α : Type*} [LinearOrder α] (hn : N + N = n) (A B : ComparatorNetwork N)
    (w : Fin n → α) :
    lowH hn ((par hn A B).exec w) = A.exec (lowH hn w) ∧
    upH hn ((par hn A B).exec w) = B.exec (upH hn w) := by
  unfold par
  rw [exec_append]
  constructor
  · funext i
    have h1 := shiftEmbed_exec_outside B n N (by omega) ((A.shiftEmbed n 0 (by omega)).exec w)
      ⟨i, by have := i.2; omega⟩ (Or.inl i.2)
    have h2 := shiftEmbed_exec_inside A n 0 (by omega) w i
    simp only [zero_add] at h2
    exact h1.trans h2
  · funext i
    have h1 := shiftEmbed_exec_inside B n N (by omega) ((A.shiftEmbed n 0 (by omega)).exec w) i
    refine h1.trans ?_
    congr 1
    funext j
    exact shiftEmbed_exec_outside A n 0 (by omega) w ⟨N + j, by have := j.2; omega⟩
      (Or.inr (by simp))


/-! ### One layer: wire `i` of the lower half against wire `σ i` of the upper half -/

/-- Parallel layer pairing lower wire `i` with upper wire `σ i`. -/
def layer (hn : N + N = n) (σ : Equiv.Perm (Fin N)) : ComparatorNetwork n :=
  ⟨(List.finRange N).map fun i : Fin N =>
    ⟨⟨i, by have := i.2; omega⟩, ⟨N + σ i, by have := (σ i).2; omega⟩,
      Fin.mk_lt_mk.2 (by have := i.2; omega)⟩⟩

theorem layer_parallel (hn : N + N = n) (σ : Equiv.Perm (Fin N)) :
    IsParallelLayer (layer hn σ).comparators := by
  unfold IsParallelLayer layer
  rw [List.pairwise_map]
  refine (List.nodup_finRange N).imp fun {a b} hab => ?_
  have h1 : (σ a).val ≠ (σ b).val := fun h => hab (σ.injective (Fin.ext h))
  have h2 : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have := a.2; have := b.2; have := (σ a).2; have := (σ b).2
  simp only [Comparator.overlaps, Fin.ext_iff]
  omega

/-- Comparators of a parallel layer act independently. -/
theorem foldl_parallel {α : Type*} [LinearOrder α] :
    ∀ (cs : List (Comparator n)), IsParallelLayer cs → ∀ (w : Fin n → α), ∀ c ∈ cs,
      (cs.foldl (fun a c => c.apply a) w) c.i = min (w c.i) (w c.j) ∧
      (cs.foldl (fun a c => c.apply a) w) c.j = max (w c.i) (w c.j) := by
  intro cs
  induction cs with
  | nil => intro _ w c hc; simp at hc
  | cons c cs ih =>
    intro hp w c' hc'
    obtain ⟨hno, hp'⟩ := List.pairwise_cons.1 hp
    have hd : ∀ d ∈ cs, c.i ≠ d.i ∧ c.i ≠ d.j ∧ c.j ≠ d.i ∧ c.j ≠ d.j := fun d hd => by
      simpa [Comparator.overlaps, not_or] using hno d hd
    rcases List.mem_cons.1 hc' with rfl | hc'
    · simp only [List.foldl_cons]
      rw [foldl_comparators_outside cs _ c'.i (fun d hd' => ⟨(hd d hd').1, (hd d hd').2.1⟩),
        foldl_comparators_outside cs _ c'.j (fun d hd' => ⟨(hd d hd').2.2.1, (hd d hd').2.2.2⟩)]
      simp [Comparator.apply, c'.h.ne']
    · simp only [List.foldl_cons]
      obtain ⟨h1, h2, h3, h4⟩ := hd c' hc'
      have := ih hp' (c.apply w) c' hc'
      simpa [Comparator.apply, h1.symm, h2.symm, h3.symm, h4.symm] using this

theorem layer_exec {α : Type*} [LinearOrder α] (hn : N + N = n) (σ : Equiv.Perm (Fin N))
    (w : Fin n → α) :
    lowH hn ((layer hn σ).exec w) = (fun i => min (lowH hn w i) (upH hn w (σ i))) ∧
    upH hn ((layer hn σ).exec w) = (fun j => max (lowH hn w (σ.symm j)) (upH hn w j)) := by
  have key := foldl_parallel _ (layer_parallel hn σ) w
  constructor
  · funext i
    exact (key _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)).1
  · funext j
    have := (key _ (List.mem_map.2 ⟨σ.symm j, List.mem_finRange _, rfl⟩)).2
    simpa using this

theorem layer_depth_le (hn : N + N = n) (σ : Equiv.Perm (Fin N)) : (layer hn σ).depth ≤ 1 :=
  depth_le_of_decomposition _ [(layer hn σ).comparators]
    ⟨fun l hl => by simp at hl; subst hl; exact layer_parallel hn σ, by simp⟩

theorem depth_par (hn : N + N = n) (A B : ComparatorNetwork N) (d : ℕ)
    (hA : A.depth ≤ d) (hB : B.depth ≤ d) : (par hn A B).depth ≤ d := by
  have := depth_flatMap_disjoint [false, true]
    (fun b => (cond b (B.shiftEmbed n N (by omega)) (A.shiftEmbed n 0 (by omega))).comparators) d
    (fun x _ => by
      cases x
      · exact (depth_shiftEmbed_le A n 0 _).trans hA
      · exact (depth_shiftEmbed_le B n N _).trans hB)
    (by
      refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
      intro b hb
      obtain rfl : b = true := by simpa using hb
      intro c₁ h₁ c₂ h₂
      simp only [cond, ComparatorNetwork.shiftEmbed, ComparatorNetwork.scatterEmbed,
        List.mem_map] at h₁ h₂
      obtain ⟨a₁, -, rfl⟩ := h₁
      obtain ⟨a₂, -, rfl⟩ := h₂
      have := a₁.i.2; have := a₁.j.2; have := a₂.i.2; have := a₂.j.2
      simp only [shiftEmb, OrderEmbedding.coe_ofStrictMono, ne_eq, Fin.ext_iff]
      omega)
  simpa [par] using this

/-! ### The networks -/

theorem two_pow_succ' (k : ℕ) : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega

/-- Bitonic merge on `2^k` wires: half-cleaner layer, then merge both halves. -/
def bitonicMerge : (k : ℕ) → ComparatorNetwork (2 ^ k)
  | 0 => ⟨[]⟩
  | k + 1 => (layer (two_pow_succ' k) 1).append
      (par (two_pow_succ' k) (bitonicMerge k) (bitonicMerge k))

/-- Bitonic sort on `2^k` wires: sort both halves, flip-compare, merge both halves. -/
def bitonicSort : (k : ℕ) → ComparatorNetwork (2 ^ k)
  | 0 => ⟨[]⟩
  | k + 1 => (par (two_pow_succ' k) (bitonicSort k) (bitonicSort k)).append
      ((layer (two_pow_succ' k) Fin.revPerm).append
        (par (two_pow_succ' k) (bitonicMerge k) (bitonicMerge k)))


theorem bitonicMerge_depth_le : ∀ k, (bitonicMerge k).depth ≤ k
  | 0 => by simp [bitonicMerge, depth_nil]
  | k + 1 =>
    (depth_append_le _ _).trans (by
      have := depth_par (two_pow_succ' k) (bitonicMerge k) (bitonicMerge k) k
        (bitonicMerge_depth_le k) (bitonicMerge_depth_le k)
      have := layer_depth_le (two_pow_succ' k) 1
      omega)

theorem bitonicSort_depth_le_budget : ∀ k, (bitonicSort k).depth ≤ bitonicDepthBudget k
  | 0 => by simp [bitonicSort, depth_nil, bitonicDepthBudget]
  | k + 1 =>
    (depth_append_le _ _).trans (by
      have h1 := depth_par (two_pow_succ' k) (bitonicSort k) (bitonicSort k) _
        (bitonicSort_depth_le_budget k) (bitonicSort_depth_le_budget k)
      have h2 := layer_depth_le (two_pow_succ' k) Fin.revPerm
      have h3 := depth_append_le (layer (two_pow_succ' k) Fin.revPerm)
        (par (two_pow_succ' k) (bitonicMerge k) (bitonicMerge k))
      have h4 := depth_par (two_pow_succ' k) (bitonicMerge k) (bitonicMerge k) k
        (bitonicMerge_depth_le k) (bitonicMerge_depth_le k)
      simp only [bitonicDepthBudget]
      omega)


end Bitonic

end
