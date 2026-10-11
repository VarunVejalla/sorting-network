module
/- Restrict a network from `n` to `m ≤ n` wires by keeping the comparators inside `[0, m)`. -/

public import AKS.Sort.Depth
public import AKS.Sort.ZeroOne

@[expose] public section

/-- The filter used by `restrictWires`: keep comparators with both endpoints in `[0, m)`. -/
def restrictFilter {n : ℕ} (m : ℕ) (c : Comparator n) : Option (Comparator m) :=
  if hi : c.i.val < m then
    if hj : c.j.val < m then
      some ⟨⟨c.i.val, hi⟩, ⟨c.j.val, hj⟩, by exact c.h⟩
    else none
  else none

/-- Restrict a network from `n` wires to `m ≤ n` wires by keeping only
    comparators where both endpoints are in `[0, m)`. -/
def ComparatorNetwork.restrictWires {n : ℕ} (net : ComparatorNetwork n)
    (m : ℕ) (_hm : m ≤ n) : ComparatorNetwork m :=
  ⟨net.comparators.filterMap (restrictFilter m)⟩

private lemma restrictWires_depth_foldl {n m : ℕ} (hm : m ≤ n)
    (cs : List (Comparator n))
    (wt_n : Fin n → ℕ) (dm_n : ℕ) (wt_m : Fin m → ℕ) (dm_m : ℕ)
    (hwt : ∀ i : Fin m, wt_m i ≤ wt_n ⟨i.val, by omega⟩)
    (hdm : dm_m ≤ dm_n) :
    (cs.filterMap (restrictFilter m) |>.foldl depthStep (wt_m, dm_m)).2 ≤
    (cs.foldl depthStep (wt_n, dm_n)).2 := by
  induction cs generalizing wt_n dm_n wt_m dm_m with
  | nil => simpa
  | cons c cs ih =>
    have hc := c.h
    rw [Fin.lt_def] at hc
    simp only [List.foldl_cons, List.filterMap_cons]
    by_cases hi : c.i.val < m <;> by_cases hj : c.j.val < m
    · simp only [restrictFilter, hi, hj, dite_true, List.foldl_cons]
      have h1 : wt_m ⟨c.i.val, hi⟩ ≤ wt_n c.i := hwt ⟨c.i.val, hi⟩
      have h2 : wt_m ⟨c.j.val, hj⟩ ≤ wt_n c.j := hwt ⟨c.j.val, hj⟩
      refine ih _ _ _ _ (fun k ↦ ?_) (by dsimp only [depthStep]; omega)
      have := hwt k
      simp only [Function.update_apply, Fin.ext_iff]
      split_ifs <;> omega
    · simp only [restrictFilter, hi, hj, dite_true, dite_false]
      refine ih _ _ _ _ (fun k ↦ ?_) (hdm.trans (le_max_left _ _))
      have := k.isLt
      simp only [Function.update_apply]
      split_ifs with h1 h2
      · have := congrArg Fin.val h1; simp at this; omega
      · have := hwt k; rw [h2] at this; omega
      · exact hwt k
    · omega
    · simp only [restrictFilter, hi, dite_false]
      refine ih _ _ _ _ (fun k ↦ ?_) (hdm.trans (le_max_left _ _))
      have := hwt k
      have := k.isLt
      simp only [Function.update_apply, Fin.ext_iff]
      split_ifs <;> omega

theorem restrictWires_depth_le {n : ℕ} (net : ComparatorNetwork n)
    (m : ℕ) (hm : m ≤ n) :
    (net.restrictWires m hm).depth ≤ net.depth :=
  restrictWires_depth_foldl hm net.comparators _ _ _ _ (fun _ ↦ le_rfl) le_rfl

/-- Execution invariant for Bool inputs: positions `< m` agree with the restricted
    execution, and positions `≥ m` remain `true`. -/
private lemma restrictWires_exec_foldl {n m : ℕ} (hm : m ≤ n)
    (cs : List (Comparator n))
    (w_n : Fin n → Bool) (w_m : Fin m → Bool)
    (hinv_lo : ∀ i : Fin m, w_n ⟨i.val, by omega⟩ = w_m i)
    (hinv_hi : ∀ i : Fin n, m ≤ i.val → w_n i = true) :
    (∀ i : Fin m,
      cs.foldl (fun acc c ↦ c.apply acc) w_n ⟨i.val, by omega⟩ =
      (cs.filterMap (restrictFilter m)).foldl (fun acc c ↦ c.apply acc) w_m i) ∧
    (∀ i : Fin n, m ≤ i.val →
      cs.foldl (fun acc c ↦ c.apply acc) w_n i = true) := by
  induction cs generalizing w_n w_m with
  | nil => exact ⟨hinv_lo, hinv_hi⟩
  | cons c cs ih =>
    have hc := c.h
    rw [Fin.lt_def] at hc
    simp only [List.foldl_cons, List.filterMap_cons]
    by_cases hi : c.i.val < m <;> by_cases hj : c.j.val < m
    · simp only [restrictFilter, hi, hj, dite_true, List.foldl_cons]
      have h1 : w_n c.i = w_m ⟨c.i.val, hi⟩ := hinv_lo ⟨c.i.val, hi⟩
      have h2 : w_n c.j = w_m ⟨c.j.val, hj⟩ := hinv_lo ⟨c.j.val, hj⟩
      refine ih _ _ (fun k ↦ ?_) (fun i him ↦ ?_)
      · have := hinv_lo k
        simp only [Comparator.apply, Fin.ext_iff, h1, h2]
        split_ifs <;> simp_all
      · have := hinv_hi i him
        simp only [Comparator.apply, Fin.ext_iff]
        split_ifs <;> first | assumption | omega
    · simp only [restrictFilter, hi, hj, dite_true, dite_false]
      have h2 := hinv_hi c.j (by omega)
      refine ih _ _ (fun k ↦ ?_) (fun i him ↦ ?_)
      · have := hinv_lo k
        have := k.isLt
        simp only [Comparator.apply, Fin.ext_iff, h2]
        split_ifs <;> simp_all
      · have := hinv_hi i him
        simp only [Comparator.apply, Fin.ext_iff, h2]
        split_ifs <;> first | assumption | omega | simp
    · omega
    · simp only [restrictFilter, hi, dite_false]
      have h1 := hinv_hi c.i (by omega)
      have h2 := hinv_hi c.j (by omega)
      refine ih _ _ (fun k ↦ ?_) (fun i him ↦ ?_)
      · have := hinv_lo k
        have := k.isLt
        simp only [Comparator.apply, Fin.ext_iff]
        split_ifs <;> first | assumption | omega
      · have := hinv_hi i him
        simp only [Comparator.apply, h1, h2]
        split_ifs <;> first | assumption | simp

/-- Sorting is preserved by wire restriction (0-1 principle plus padding with `true`). -/
theorem restrictWires_sorts {n : ℕ} (net : ComparatorNetwork n)
    (m : ℕ) (hm : m ≤ n)
    (hsort : ∀ v : Fin n → Bool, Monotone (net.exec v)) :
    (net.restrictWires m hm).Sorts := by
  apply zero_one_principle
  intro v i j hij
  let v' : Fin n → Bool := fun i ↦ if h : i.val < m then v ⟨i.val, h⟩ else true
  have hrestr := (restrictWires_exec_foldl hm net.comparators v' v
    (fun i ↦ by simp [v', i.isLt]) (fun i him ↦ by simp [v', show ¬(i.val < m) by omega])).1
  simp only [ComparatorNetwork.exec, ComparatorNetwork.restrictWires] at hrestr hsort ⊢
  rw [← hrestr i, ← hrestr j]
  exact hsort v' hij

end
