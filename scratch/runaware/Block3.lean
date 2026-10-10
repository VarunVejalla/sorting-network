import AKS.Bitonic.Shrink
open ComparatorNetwork

namespace Bitonic

/-- Bitonic sort with blocks of size `2^s` already sorted: recursion cut at size `2^s`. -/
def bitonicBlockSort (s : ℕ) : (k : ℕ) → ComparatorNetwork (2 ^ k)
  | 0 => ⟨[]⟩
  | k + 1 =>
    if k + 1 ≤ s then ⟨[]⟩ else
    (par (two_pow_succ' k) (bitonicBlockSort s k) (bitonicBlockSort s k)).append
      ((layer (two_pow_succ' k) Fin.revPerm).append
        (par (two_pow_succ' k) (bitonicMerge k) (bitonicMerge k)))

theorem bitonicBlockSort_depth_le (s : ℕ) :
    ∀ k, (bitonicBlockSort s k).depth ≤ bitonicDepthBudget k - bitonicDepthBudget s
  | 0 => by simp [bitonicBlockSort, depth_nil]
  | k + 1 => by
    unfold bitonicBlockSort
    split_ifs with h
    · have := bitonicDepthBudget_mono h
      simp [depth_nil]
    · have ih := bitonicBlockSort_depth_le s k
      have hs : bitonicDepthBudget s ≤ bitonicDepthBudget k := bitonicDepthBudget_mono (by omega)
      refine (depth_append_le _ _).trans ?_
      have h1 := depth_par (two_pow_succ' k) (bitonicBlockSort s k) (bitonicBlockSort s k) _ ih ih
      have h2 := layer_depth_le (two_pow_succ' k) Fin.revPerm
      have h3 := depth_append_le (layer (two_pow_succ' k) Fin.revPerm)
        (par (two_pow_succ' k) (bitonicMerge k) (bitonicMerge k))
      have h4 := depth_par (two_pow_succ' k) (bitonicMerge k) (bitonicMerge k) k
        (bitonicMerge_depth_le k) (bitonicMerge_depth_le k)
      simp only [bitonicDepthBudget]
      omega


/-- Block monotone: within each aligned block of size `2^s`, the vector is monotone. -/
def BlockMono {α : Type*} [LinearOrder α] (s : ℕ) {n : ℕ} (v : Fin n → α) : Prop :=
  ∀ a b : Fin n, a ≤ b → a.val / 2 ^ s = b.val / 2 ^ s → v a ≤ v b

/-- 0-1 principle for block-monotone inputs. -/
theorem lift_blockMono {n : ℕ} (net : ComparatorNetwork n) (s : ℕ)
    (h : ∀ v : Fin n → Bool, BlockMono s v → Monotone (net.exec v))
    {α : Type*} [LinearOrder α] (v : Fin n → α) (hv : BlockMono s v) :
    Monotone (net.exec v) := by
  by_contra h_not_mono
  simp only [Monotone, not_forall, not_le] at h_not_mono
  obtain ⟨i, j, hij, hlt⟩ := h_not_mono
  have hf : Monotone fun x : α ↦ decide ((net.exec v) j < x) := fun a b hab ↦ by
    by_cases ha : (net.exec v) j < a
    · simp [ha, lt_of_lt_of_le ha hab]
    · simp [ha]
  have hb : BlockMono s ((fun x : α ↦ decide ((net.exec v) j < x)) ∘ v) :=
    fun a b hab hd => hf (hv a b hab hd)
  have h_sorted := h _ hb hij
  have hcomm := congr_fun (net.exec_comp_monotone hf v)
  simp only [Function.comp] at hcomm
  rw [← hcomm i, ← hcomm j] at h_sorted
  simp [hlt] at h_sorted
  exact absurd h_sorted (by decide)

theorem BlockMono.low {α : Type*} [LinearOrder α] {s k : ℕ} (hn : 2 ^ k + 2 ^ k = N)
    {v : Fin N → α} (hv : BlockMono s v) : BlockMono s (lowH hn v) := by
  intro a b hab hd
  exact hv _ _ hab hd

theorem BlockMono.up {α : Type*} [LinearOrder α] {s k : ℕ} (hsk : s ≤ k)
    (hn : 2 ^ k + 2 ^ k = N)
    {v : Fin N → α} (hv : BlockMono s v) : BlockMono s (upH hn v) := by
  intro a b hab hd
  have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
  have e : 2 ^ k = 2 ^ s * 2 ^ (k - s) := by rw [← pow_add]; congr 1; omega
  refine hv _ _ (by exact Nat.add_le_add_left hab _) ?_
  show (2 ^ k + a.val) / 2 ^ s = (2 ^ k + b.val) / 2 ^ s
  have key : ∀ x : ℕ, (2 ^ k + x) / 2 ^ s = 2 ^ (k - s) + x / 2 ^ s := fun x => by
    rw [e, Nat.mul_add_div hpos]
  rw [key, key, hd]

theorem bitonicBlockSort_sorts_bool (s : ℕ) : ∀ (k : ℕ) (v : Fin (2 ^ k) → Bool),
    BlockMono s v → Monotone ((bitonicBlockSort s k).exec v)
  | 0, v, _ => fun a b _ => by
    have := a.2; have := b.2
    rw [show a = b from Fin.ext (by rw [Nat.pow_zero] at *; omega)]
  | k + 1, v, hv => by
    by_cases h : k + 1 ≤ s
    · have e : bitonicBlockSort s (k + 1) = ⟨[]⟩ := by simp [bitonicBlockSort, h]
      rw [e]
      show Monotone v
      intro a b hab
      refine hv a b hab ?_
      have hlt : 2 ^ (k + 1) ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) h
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le a.2 hlt), Nat.div_eq_of_lt (lt_of_lt_of_le b.2 hlt)]
    · have hsk : s ≤ k := by omega
      have e : bitonicBlockSort s (k + 1) =
          (par (two_pow_succ' k) (bitonicBlockSort s k) (bitonicBlockSort s k)).append
          ((layer (two_pow_succ' k) Fin.revPerm).append
            (par (two_pow_succ' k) (bitonicMerge k) (bitonicMerge k))) := by
        simp [bitonicBlockSort, h]
      have hn := two_pow_succ' k
      obtain ⟨q1, q2⟩ := par_exec hn (bitonicBlockSort s k) (bitonicBlockSort s k) v
      obtain ⟨hl, hu, hord⟩ := cross_props hn _
        (by rw [q1]; exact bitonicBlockSort_sorts_bool s k _ (hv.low hn))
        (by rw [q2]; exact bitonicBlockSort_sorts_bool s k _ (hv.up hsk hn))
      obtain ⟨r1, r2⟩ := par_exec hn (bitonicMerge k) (bitonicMerge k)
        ((layer hn Fin.revPerm).exec ((par hn (bitonicBlockSort s k) (bitonicBlockSort s k)).exec v))
      rw [e, show ((par hn (bitonicBlockSort s k) (bitonicBlockSort s k)).append
          ((layer hn Fin.revPerm).append (par hn (bitonicMerge k) (bitonicMerge k)))).exec v =
          (par hn (bitonicMerge k) (bitonicMerge k)).exec
          ((layer hn Fin.revPerm).exec ((par hn (bitonicBlockSort s k) (bitonicBlockSort s k)).exec v))
          from (exec_append _ _ v).trans (exec_append _ _ _)]
      refine glue hn _ (by rw [r1]; exact bitonicMerge_sorts k _ hl)
        (by rw [r2]; exact bitonicMerge_sorts k _ hu) ?_
      rcases hord with h | h
      · left; rw [r1, h]; exact ((bitonicMerge k).exec_eq_of_monotone monotone_const)
      · right; rw [r2, h]; exact ((bitonicMerge k).exec_eq_of_monotone monotone_const)

theorem bitonicBlockSort_sorts (s k : ℕ) {α : Type*} [LinearOrder α] (v : Fin (2 ^ k) → α)
    (hv : BlockMono s v) : Monotone ((bitonicBlockSort s k).exec v) :=
  lift_blockMono _ s (bitonicBlockSort_sorts_bool s k) v hv

end Bitonic
/-- Execution invariant for Bool inputs: positions `< m` agree with the restricted
    execution, and positions `≥ m` remain `true`. -/
theorem restrictWires_exec_foldl' {n m : ℕ} (hm : m ≤ n)
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


/-- Block-aligned bitonic sort on `n` wires (blocks of `2^s` already sorted). -/
def bitonicBlockNetwork (s n : ℕ) : ComparatorNetwork n :=
  (Bitonic.bitonicBlockSort s (Nat.clog 2 n)).restrictWires n (Nat.le_pow_clog (by omega) n)

theorem bitonicBlockNetwork_sorts_bool (s n : ℕ) (v : Fin n → Bool)
    (hv : Bitonic.BlockMono s v) : Monotone ((bitonicBlockNetwork s n).exec v) := by
  have hm : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by omega) n
  let v' : Fin (2 ^ Nat.clog 2 n) → Bool := fun i ↦ if h : i.val < n then v ⟨i.val, h⟩ else true
  have hv' : Bitonic.BlockMono s v' := by
    intro a b hab hd
    by_cases hb : b.val < n
    · have ha : a.val < n := lt_of_le_of_lt hab hb
      simp only [v', ha, hb, dite_true]
      exact hv _ _ hab hd
    · simp only [v', hb, dite_false]
      exact Bool.le_true _
  have hrestr := (restrictWires_exec_foldl' hm (Bitonic.bitonicBlockSort s (Nat.clog 2 n)).comparators v' v
    (fun i ↦ by simp [v', i.isLt]) (fun i him ↦ by simp [v', show ¬(i.val < n) by omega])).1
  have hsort := Bitonic.bitonicBlockSort_sorts_bool s _ v' hv'
  simp only [ComparatorNetwork.exec, ComparatorNetwork.restrictWires, bitonicBlockNetwork] at hrestr hsort ⊢
  intro i j hij
  rw [← hrestr i, ← hrestr j]
  exact hsort hij

theorem bitonicBlockNetwork_sorts (s n : ℕ) {α : Type*} [LinearOrder α] (v : Fin n → α)
    (hv : Bitonic.BlockMono s v) : Monotone ((bitonicBlockNetwork s n).exec v) :=
  Bitonic.lift_blockMono _ s (bitonicBlockNetwork_sorts_bool s n) v hv

theorem bitonicBlockNetwork_depth_le (s n : ℕ) :
    (bitonicBlockNetwork s n).depth ≤
      bitonicDepthBudget (Nat.clog 2 n) - bitonicDepthBudget s :=
  (restrictWires_depth_le _ _ _).trans (Bitonic.bitonicBlockSort_depth_le s _)

#print axioms bitonicBlockNetwork_sorts
#print axioms bitonicBlockNetwork_depth_le
