module
/- Depth (greedy critical-path scheduling) of a comparator network. -/

public import AKS.Sort.Defs

@[expose] public section

open Finset BigOperators

/-- Two comparators overlap if they share a wire. -/
def Comparator.overlaps {n : ℕ} (c₁ c₂ : Comparator n) : Prop :=
  c₁.i = c₂.i ∨ c₁.i = c₂.j ∨ c₁.j = c₂.i ∨ c₁.j = c₂.j

def depthStep {n : ℕ} (state : (Fin n → ℕ) × ℕ) (c : Comparator n) :
    (Fin n → ℕ) × ℕ :=
  let wt := state.1
  let t := max (wt c.i) (wt c.j) + 1
  (Function.update (Function.update wt c.i t) c.j t, max state.2 t)

/-- The depth of a comparator network, via greedy critical-path scheduling: each comparator
    gets time `max(wireTime c.i, wireTime c.j) + 1`, both wires are updated to it, and the
    depth is the maximum time assigned. -/
def ComparatorNetwork.depth {n : ℕ} (net : ComparatorNetwork n) : ℕ :=
  (net.comparators.foldl depthStep (fun _ ↦ 0, 0)).2

/-- The empty network has depth 0. -/
theorem depth_nil {n : ℕ} : (⟨[]⟩ : ComparatorNetwork n).depth = 0 := by
  simp [ComparatorNetwork.depth]

/-- A layer is a list of pairwise non-overlapping comparators. -/
def IsParallelLayer {n : ℕ} (layer : List (Comparator n)) : Prop :=
  layer.Pairwise (fun c₁ c₂ ↦ ¬c₁.overlaps c₂)

/-- Processing one non-overlapping layer from wire times `≤ d` (on the layer's wires) gives
    wire times and running max `≤ d + 1`. -/
lemma layer_foldl_bound {n : ℕ} (cs : List (Comparator n))
    (hcs : IsParallelLayer cs)
    (wt : Fin n → ℕ) (d dm : ℕ)
    (hwt_layer : ∀ c ∈ cs, wt c.i ≤ d ∧ wt c.j ≤ d)
    (hwt_all : ∀ k, wt k ≤ d + 1)
    (hdm : dm ≤ d + 1) :
    (∀ k, (cs.foldl depthStep (wt, dm)).1 k ≤ d + 1) ∧
    (cs.foldl depthStep (wt, dm)).2 ≤ d + 1 := by
  induction cs generalizing wt dm with
  | nil => exact ⟨hwt_all, hdm⟩
  | cons c cs ih =>
    obtain ⟨hno, hcs'⟩ := List.pairwise_cons.mp hcs
    have ⟨hci, hcj⟩ := hwt_layer c (by simp)
    refine ih hcs' _ _ (fun c' hc' ↦ ?_) (fun k ↦ ?_) (by dsimp only [depthStep]; omega)
    · have := hno c' hc'
      simp only [Comparator.overlaps, not_or] at this
      have := hwt_layer c' (List.mem_cons_of_mem c hc')
      simp only [Function.update_apply]
      refine ⟨?_, ?_⟩ <;> split_ifs <;> simp_all
    · have := hwt_all k
      simp only [Function.update_apply]
      split_ifs <;> omega

/-- **Any parallel decomposition upper-bounds depth.** -/
theorem depth_le_of_decomposition {n : ℕ} (net : ComparatorNetwork n)
    (layers : List (List (Comparator n)))
    (hd : (∀ layer ∈ layers, IsParallelLayer layer) ∧ layers.flatten = net.comparators) :
    net.depth ≤ layers.length := by
  unfold ComparatorNetwork.depth
  rw [← hd.2]
  suffices ∀ (layers : List (List (Comparator n))), (∀ layer ∈ layers, IsParallelLayer layer) →
      ∀ (wt : Fin n → ℕ) (d dm : ℕ), (∀ k, wt k ≤ d) → dm ≤ d →
      (layers.flatten.foldl depthStep (wt, dm)).2 ≤ d + layers.length by
    simpa using this layers hd.1 (fun _ ↦ 0) 0 0 (fun _ ↦ le_rfl) le_rfl
  intro layers
  induction layers with
  | nil => intro _ wt d dm _ h; simpa using h
  | cons layer layers ih =>
    intro hl wt d dm hwt hdm
    have bound := layer_foldl_bound layer (hl layer (by simp)) wt d dm (fun c _ ↦ ⟨hwt _, hwt _⟩)
      (fun k ↦ (hwt k).trans (Nat.le_succ d)) (hdm.trans (Nat.le_succ d))
    have step := ih (fun l hl' ↦ hl l (List.mem_cons_of_mem layer hl')) _ (d + 1) _
      bound.1 bound.2
    rw [Prod.mk.eta] at step
    simp only [List.flatten_cons, List.foldl_append, List.length_cons]
    omega

/-- Wire times are bounded by the running max throughout the fold. -/
lemma wt_le_running_max {n : ℕ} (cs : List (Comparator n))
    (wt : Fin n → ℕ) (dm : ℕ) (hwt : ∀ k, wt k ≤ dm) :
    ∀ k, (cs.foldl depthStep (wt, dm)).1 k ≤ (cs.foldl depthStep (wt, dm)).2 := by
  induction cs generalizing wt dm with
  | nil => exact hwt
  | cons c cs ih =>
    refine ih _ _ fun k ↦ ?_
    have := hwt k
    simp only [Function.update_apply]
    split_ifs <;> omega

/-- Pointwise shift bound: if initial wire times and running max are offset by `d`
    from a reference state, then so are the outputs. -/
lemma foldl_depth_pointwise_shift {n : ℕ} (cs : List (Comparator n))
    (wt wt₀ : Fin n → ℕ) (dm dm₀ d : ℕ)
    (hwt : ∀ k, wt k ≤ d + wt₀ k) (hdm : dm ≤ d + dm₀) :
    (cs.foldl depthStep (wt, dm)).2 ≤ d + (cs.foldl depthStep (wt₀, dm₀)).2 := by
  induction cs generalizing wt wt₀ dm dm₀ with
  | nil => exact hdm
  | cons c cs ih =>
    refine ih _ _ _ _ (fun k ↦ ?_) ?_
    · have := hwt k; have := hwt c.i; have := hwt c.j
      simp only [Function.update_apply]
      split_ifs <;> omega
    · have := hwt c.i; have := hwt c.j
      dsimp only [depthStep]; omega

/-- Concatenate two comparator networks (sequential composition). -/
def ComparatorNetwork.append {n : ℕ} (net₁ net₂ : ComparatorNetwork n) :
    ComparatorNetwork n :=
  ⟨net₁.comparators ++ net₂.comparators⟩

/-- **Depth of concatenated networks.** -/
theorem ComparatorNetwork.depth_append_le {n : ℕ} (net₁ net₂ : ComparatorNetwork n) :
    (net₁.append net₂).depth ≤ net₁.depth + net₂.depth := by
  simp only [ComparatorNetwork.depth, ComparatorNetwork.append, List.foldl_append]
  have := foldl_depth_pointwise_shift net₂.comparators
    (net₁.comparators.foldl depthStep (fun _ ↦ 0, 0)).1 (fun _ ↦ 0) _ 0
    (net₁.comparators.foldl depthStep (fun _ ↦ 0, 0)).2
    (fun k ↦ by simpa using wt_le_running_max net₁.comparators (fun _ ↦ 0) 0 (fun _ ↦ le_rfl) k)
    le_rfl
  simpa using this

/-- Processing scatter-embedded comparators maintains the running max (`depthStep` only
    cares about which wires coincide). -/
lemma foldl_scatterEmbed_eq {m n : ℕ} (cs : List (Comparator m))
    (f : Fin m ↪o Fin n) (wt₀ : Fin m → ℕ) (wt : Fin n → ℕ) (dm : ℕ)
    (hwt : ∀ j : Fin m, wt (f j) = wt₀ j) :
    let scattered := cs.map fun c ↦
      ({ i := f c.i, j := f c.j, h := f.lt_iff_lt.mpr c.h } : Comparator n)
    (scattered.foldl depthStep (wt, dm)).2 = (cs.foldl depthStep (wt₀, dm)).2 := by
  induction cs generalizing wt₀ wt dm with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have key := ih (depthStep (wt₀, dm) c).1
      (depthStep (wt, dm) ⟨f c.i, f c.j, f.lt_iff_lt.mpr c.h⟩).1
      (depthStep (wt, dm) ⟨f c.i, f c.j, f.lt_iff_lt.mpr c.h⟩).2 fun j ↦ by
        simp only [depthStep, Function.update_apply, hwt, f.injective.eq_iff]
    simp only [depthStep, hwt] at key ⊢
    exact key

/-- **Depth is preserved by scatter embedding.** -/
theorem depth_scatterEmbed_le {m : ℕ} (net : ComparatorNetwork m)
    (n : ℕ) (f : Fin m ↪o Fin n) :
    (net.scatterEmbed n f).depth ≤ net.depth :=
  (foldl_scatterEmbed_eq net.comparators f (fun _ ↦ 0) (fun _ ↦ 0) 0 fun _ ↦ rfl).le

theorem depth_shiftEmbed_le {m : ℕ} (net : ComparatorNetwork m)
    (n offset : ℕ) (h : offset + m ≤ n) :
    (net.shiftEmbed n offset h).depth ≤ net.depth :=
  depth_scatterEmbed_le net n _

/-- Running max is monotone through foldl. -/
lemma foldl_dm_le {n : ℕ} (cs : List (Comparator n))
    (wt : Fin n → ℕ) (dm : ℕ) :
    dm ≤ (cs.foldl depthStep (wt, dm)).2 := by
  induction cs generalizing wt dm with
  | nil => exact le_rfl
  | cons c cs ih => exact (le_max_left _ _).trans (ih _ _)

/-- Wire times are unchanged for positions not touched by any comparator. -/
lemma foldl_untouched_wire {n : ℕ} (cs : List (Comparator n))
    (wt : Fin n → ℕ) (dm : ℕ) (k : Fin n)
    (hk : ∀ c ∈ cs, k ≠ c.i ∧ k ≠ c.j) :
    (cs.foldl depthStep (wt, dm)).1 k = wt k := by
  induction cs generalizing wt dm with
  | nil => rfl
  | cons c cs ih =>
    have ⟨hki, hkj⟩ := hk c (by simp)
    simp only [List.foldl_cons]
    rw [ih _ _ fun c' hc' ↦ hk c' (List.mem_cons_of_mem c hc')]
    simp [depthStep, hki, hkj]

/-- When wire times agree on all wires of `cs`, the running max is bounded by
    `max dm (standalone result)`. -/
lemma foldl_dm_max_of_agree {n : ℕ} (cs : List (Comparator n))
    (wt wt₀ : Fin n → ℕ) (dm dm₀ : ℕ)
    (hwt : ∀ c ∈ cs, wt c.i = wt₀ c.i ∧ wt c.j = wt₀ c.j) :
    (cs.foldl depthStep (wt, dm)).2 ≤
      max dm (cs.foldl depthStep (wt₀, dm₀)).2 := by
  induction cs generalizing wt wt₀ dm dm₀ with
  | nil => exact le_max_left dm dm₀
  | cons c cs ih =>
    have ⟨hci, hcj⟩ := hwt c (by simp)
    have step := ih (depthStep (wt, dm) c).1 (depthStep (wt₀, dm₀) c).1
      (depthStep (wt, dm) c).2 (depthStep (wt₀, dm₀) c).2 fun c' hc' ↦ by
        have ⟨h1, h2⟩ := hwt c' (List.mem_cons_of_mem c hc')
        simp only [depthStep, Function.update_apply, hci, hcj]
        refine ⟨?_, ?_⟩ <;> split_ifs <;> first | rfl | assumption
    rw [Prod.mk.eta, Prod.mk.eta] at step
    have h1 := foldl_dm_le cs (depthStep (wt₀, dm₀) c).1 (depthStep (wt₀, dm₀) c).2
    have ht : max (wt c.i) (wt c.j) + 1 ≤ (cs.foldl depthStep (depthStep (wt₀, dm₀) c)).2 := by
      rw [hci, hcj]; exact (le_max_right _ _).trans h1
    simp only [List.foldl_cons]
    refine step.trans (max_le ?_ (le_max_right _ _))
    exact max_le (le_max_left _ _) (ht.trans (le_max_right _ _))

/-- **Depth of wire-disjoint flatMap.** If chunks have pairwise wire-disjoint comparators
    and each chunk has depth ≤ `d`, the concatenation has depth ≤ `d`. -/
theorem depth_flatMap_disjoint {n : ℕ} {ι : Type*}
    (chunks : List ι) (f : ι → List (Comparator n)) (d : ℕ)
    (hd : ∀ x ∈ chunks, (⟨f x⟩ : ComparatorNetwork n).depth ≤ d)
    (hdisj : chunks.Pairwise (fun a b ↦ ∀ c₁ ∈ f a, ∀ c₂ ∈ f b,
        (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j))) :
    (⟨chunks.flatMap f⟩ : ComparatorNetwork n).depth ≤ d := by
  simp only [ComparatorNetwork.depth]
  induction chunks with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.foldl_append]
    have hx_disj := (List.pairwise_cons.mp hdisj).1
    have hag : ∀ c ∈ xs.flatMap f,
        ((f x).foldl depthStep (fun _ ↦ 0, 0)).1 c.i = (fun _ : Fin n ↦ 0) c.i ∧
        ((f x).foldl depthStep (fun _ ↦ 0, 0)).1 c.j = (fun _ : Fin n ↦ 0) c.j := by
      intro c hc
      obtain ⟨y, hy, hcfy⟩ := List.mem_flatMap.mp hc
      have hxy := hx_disj y hy
      exact ⟨foldl_untouched_wire _ _ _ _ fun c₁ hc₁ ↦
          ⟨(hxy c₁ hc₁ c hcfy).1.1.symm, (hxy c₁ hc₁ c hcfy).2.1.symm⟩,
        foldl_untouched_wire _ _ _ _ fun c₁ hc₁ ↦
          ⟨(hxy c₁ hc₁ c hcfy).1.2.symm, (hxy c₁ hc₁ c hcfy).2.2.symm⟩⟩
    have h_bound := foldl_dm_max_of_agree (xs.flatMap f)
      ((f x).foldl depthStep (fun _ ↦ 0, 0)).1 (fun _ ↦ 0)
      ((f x).foldl depthStep (fun _ ↦ 0, 0)).2 0 hag
    rw [Prod.mk.eta] at h_bound
    exact h_bound.trans (max_le (hd x (by simp))
      (ih (fun y hy ↦ hd y (List.mem_cons_of_mem x hy)) (List.pairwise_cons.mp hdisj).2))

end
