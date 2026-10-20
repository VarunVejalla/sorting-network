module
/-
  # Physical sort–scramble–sort network

  The semantic map `semanticExec` relabels wires in the middle stage. Here we build a genuine standard comparator network on the
  `m·n` row-major wires: first column sorter, then the second column sorter with every
  comparator relabeled through `wirePerm.symm`. Row preservation of the scramble keeps each
  relabeled comparator standard (`i < j`).

  Direction: `relabelNet π net` has `(relabelNet π net).exec x = (net.exec (x ∘ π)) ∘ π.symm`.
  The semantic output is `C (u ∘ wirePerm.symm)` for `u = C v`, so we relabel by
  `π = wirePerm.symm` and get `physical = semantic ∘ wirePerm`.
-/

public import AKS.Chvatal.SeparatorDepth

@[expose] public section

namespace Chvatal

/-! ## Relabeling a network by a wire permutation -/

/-- Relabel each comparator `(i, j)` to `(π i, π j)`, given that this stays standard. -/
def relabelNet {N : ℕ} (π : Equiv.Perm (Fin N)) (net : ComparatorNetwork N)
    (h : ∀ c ∈ net.comparators, π c.i < π c.j) : ComparatorNetwork N :=
  ⟨net.comparators.pmap (fun c hc => (⟨π c.i, π c.j, h c hc⟩ : Comparator N))
    (fun _ hc => hc)⟩

theorem Comparator.apply_relabel_comp {N : ℕ} {α : Type*} [LinearOrder α]
    (π : Equiv.Perm (Fin N)) (c : Comparator N) (hc : π c.i < π c.j) (x : Fin N → α) :
    (Comparator.apply ⟨π c.i, π c.j, hc⟩ x) ∘ π = c.apply (x ∘ π) := by
  funext a
  simp only [Function.comp, Comparator.apply, EmbeddingLike.apply_eq_iff_eq]

private theorem foldl_pmap_relabel {N : ℕ} {α : Type*} [LinearOrder α]
    (π : Equiv.Perm (Fin N)) (P : Comparator N → Prop) (h : ∀ c, P c → π c.i < π c.j)
    (cs : List (Comparator N)) (hcs : ∀ c ∈ cs, P c) (x : Fin N → α) :
    (cs.pmap (fun c hc => (⟨π c.i, π c.j, h c hc⟩ : Comparator N)) hcs).foldl
        (fun acc c => c.apply acc) x ∘ π
      = cs.foldl (fun acc c => c.apply acc) (x ∘ π) := by
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.pmap_cons, List.foldl_cons]
    refine (ih (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) _).trans ?_
    rw [Comparator.apply_relabel_comp π c (h c (hcs c List.mem_cons_self)) x]

/-- `(relabelNet π net).exec x = (net.exec (x ∘ π)) ∘ π.symm`: the comparator `(π i, π j)` acts
on the values at wires `π i, π j`, i.e. on `x ∘ π` at `i, j`. -/
theorem relabelNet_exec {N : ℕ} {α : Type*} [LinearOrder α]
    (π : Equiv.Perm (Fin N)) (net : ComparatorNetwork N)
    (h : ∀ c ∈ net.comparators, π c.i < π c.j) (x : Fin N → α) :
    (relabelNet π net h).exec x = fun w => net.exec (x ∘ π) (π.symm w) := by
  funext w
  have := congrFun (foldl_pmap_relabel π (· ∈ net.comparators) h net.comparators
    (fun c hc => hc) x) (π.symm w)
  simpa [relabelNet, ComparatorNetwork.exec] using this

private theorem foldl_depth_relabel {N : ℕ} (π : Equiv.Perm (Fin N))
    (P : Comparator N → Prop) (h : ∀ c, P c → π c.i < π c.j)
    (cs : List (Comparator N)) (hcs : ∀ c ∈ cs, P c) (wt : Fin N → ℕ) (d : ℕ) :
    ((cs.pmap (fun c hc => (⟨π c.i, π c.j, h c hc⟩ : Comparator N)) hcs).foldl
        depthStep (wt ∘ π.symm, d)) =
      ((cs.foldl depthStep (wt, d)).1 ∘ π.symm, (cs.foldl depthStep (wt, d)).2) := by
  induction cs generalizing wt d with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.pmap_cons, List.foldl_cons]
    have hstep : depthStep (wt ∘ π.symm, d) ⟨π c.i, π c.j, h c (hcs c List.mem_cons_self)⟩
        = ((depthStep (wt, d) c).1 ∘ π.symm, (depthStep (wt, d) c).2) := by
      simp only [depthStep, Function.comp, Equiv.symm_apply_apply]
      refine Prod.ext ?_ rfl
      show _ = (Function.update (Function.update wt c.i _) c.j _) ∘ π.symm
      rw [Function.update_comp_equiv, Function.update_comp_equiv]
      rfl
    rw [hstep]
    have := ih (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
      (depthStep (wt, d) c).1 (depthStep (wt, d) c).2
    rw [Prod.mk.eta] at this
    exact this

theorem relabelNet_depth {N : ℕ} (π : Equiv.Perm (Fin N)) (net : ComparatorNetwork N)
    (h : ∀ c ∈ net.comparators, π c.i < π c.j) :
    (relabelNet π net h).depth = net.depth := by
  have := foldl_depth_relabel π (· ∈ net.comparators) h net.comparators (fun c hc => hc)
    (fun _ => 0) 0
  have h0 : ((fun _ => 0 : Fin N → ℕ) ∘ π.symm) = fun _ => 0 := rfl
  rw [h0] at this
  simp only [ComparatorNetwork.depth, relabelNet]
  rw [this]

/-! ## Row-major order is dominated by the row -/

theorem wire_lt_of_matrixRow_lt {m n : ℕ} (hn : 0 < n) {w w' : Fin (m * n)}
    (h : matrixRow m n hn w < matrixRow m n hn w') : w < w' := by
  by_contra hc
  have hle : w'.val ≤ w.val := not_lt.mp hc
  have := Nat.div_le_div_right (c := n) hle
  have h2 : w.val / n < w'.val / n := h
  omega

/-- Column-sorter comparators join different rows `r < r'` (same column). -/
theorem columnSortNetwork_comparator_rows {m n : ℕ} (hn : 0 < n)
    (c : Comparator (m * n)) (hc : c ∈ (columnSortNetwork m n hn).comparators) :
    matrixRow m n hn c.i < matrixRow m n hn c.j := by
  obtain ⟨j, r, k, hi, hk⟩ := columnSortNetwork_columnLocal m n hn c hc
  have hrk : r < k := (matrixWire_row_lt_iff hn j).mp (by rw [← hi, ← hk]; exact c.h)
  rw [hi, hk, (matrixWire_row_col hn r j).1, (matrixWire_row_col hn k j).1]
  exact hrk

theorem columnSortNetwork_relabel_lt {m n : ℕ} (hn : 0 < n) (σ : Scramble m n)
    (c : Comparator (m * n)) (hc : c ∈ (columnSortNetwork m n hn).comparators) :
    (rowScrambleWirePerm m n hn σ).symm c.i < (rowScrambleWirePerm m n hn σ).symm c.j := by
  apply wire_lt_of_matrixRow_lt hn
  rw [matrixRow_rowScrambleWirePerm_symm, matrixRow_rowScrambleWirePerm_symm]
  exact columnSortNetwork_comparator_rows hn c hc

/-! ## The physical network -/

/-- Physical sort–scramble–sort: column sorter, then the column sorter relabeled by
`wirePerm.symm` of the canonical row scramble. -/
def physicalPackNet (m n : ℕ) (hn : 0 < n) (σ : Scramble m n) : ComparatorNetwork (m * n) :=
  ⟨(columnSortNetwork m n hn).comparators ++
    (relabelNet (rowScrambleWirePerm m n hn σ).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel_lt hn σ)).comparators⟩

/-- Main theorem: physical output = semantic output with columns permuted within rows by
`ρ = wirePerm`. -/
theorem physicalPackNet_exec {m n : ℕ} (hn : 0 < n) (σ : Scramble m n)
    {α : Type*} [LinearOrder α] (v : Fin (m * n) → α) :
    (physicalPackNet m n hn σ).exec v =
      (semanticExec hn σ v) ∘ rowScrambleWirePerm m n hn σ := by
  have hx := ComparatorNetwork.exec_append (columnSortNetwork m n hn)
    (relabelNet (rowScrambleWirePerm m n hn σ).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel_lt hn σ)) v
  unfold physicalPackNet
  rw [hx, relabelNet_exec]
  rfl

/-- Count form: for every predicate `P` on values and every set of rows `R`, the number of
wires in rows of `R` whose value satisfies `P` agrees between physical and semantic output. -/
theorem physicalPackNet_rowRegion_card {m n : ℕ} (hn : 0 < n) (σ : Scramble m n)
    {α : Type*} [LinearOrder α] (v : Fin (m * n) → α) (R : Finset (Fin m))
    (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter fun w : Fin (m * n) =>
        matrixRow m n hn w ∈ R ∧ P ((physicalPackNet m n hn σ).exec v w)).card =
    (Finset.univ.filter fun w : Fin (m * n) =>
        matrixRow m n hn w ∈ R ∧
          P (semanticExec hn σ v w)).card := by
  set ρ := rowScrambleWirePerm m n hn σ with hρ
  refine Finset.card_bij (fun w _ => ρ w) ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [hρ, matrixRow_rowScrambleWirePerm hn σ]
    refine ⟨hw.1, ?_⟩
    have := hw.2
    rwa [physicalPackNet_exec] at this
  · intro a _ b _ h; exact ρ.injective h
  · intro w hw
    refine ⟨ρ.symm w, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [hρ, matrixRow_rowScrambleWirePerm_symm hn σ, physicalPackNet_exec]
    exact ⟨hw.1, by simpa using hw.2⟩

/-! ## Depth -/

theorem physicalPackNet_depth_le (m n : ℕ) (hn : 0 < n) (σ : Scramble m n) :
    (physicalPackNet m n hn σ).depth ≤ 2 * (columnSortNetwork m n hn).depth := by
  have h := ComparatorNetwork.depth_append_le (columnSortNetwork m n hn)
    (relabelNet (rowScrambleWirePerm m n hn σ).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel_lt hn σ))
  rw [relabelNet_depth] at h
  have e : physicalPackNet m n hn σ = ((columnSortNetwork m n hn).append
    (relabelNet (rowScrambleWirePerm m n hn σ).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel_lt hn σ))) := rfl
  rw [e]
  omega

theorem physicalPackNet_depth_le_budget (m n : ℕ) (hn : 0 < n) (σ : Scramble m n) :
    (physicalPackNet m n hn σ).depth ≤ 2 * bitonicDepthBudget (Nat.clog 2 m) :=
  (physicalPackNet_depth_le m n hn σ).trans
    (Nat.mul_le_mul_left 2 (columnSortNetwork_depth_le_budget m n hn))

end Chvatal
