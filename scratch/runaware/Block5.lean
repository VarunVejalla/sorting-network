import AKS.Chvatal.PhysicalPack
import Mathlib.Data.Fin.Tuple.Sort
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


/-! ### Execution of a network is a rearrangement -/

theorem exec_eq_comp_perm {n : ℕ} {α : Type*} [LinearOrder α] (net : ComparatorNetwork n)
    (v : Fin n → α) : ∃ π : Equiv.Perm (Fin n), net.exec v = v ∘ π := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing v with
  | nil => exact ⟨1, rfl⟩
  | cons c cs ih =>
    obtain ⟨π, hπ⟩ := ih (c.apply v)
    simp only [List.foldl_cons]
    rw [hπ]
    by_cases h : v c.i ≤ v c.j
    · rw [c.apply_eq_of_le v h]; exact ⟨π, rfl⟩
    · refine ⟨Equiv.swap c.i c.j * π, ?_⟩
      rw [show c.apply v = v ∘ Equiv.swap c.i c.j from
        funext (c.apply_eq_swap v (not_le.1 h))]
      rfl

/-- The sorted rearrangement of a vector is unique: two networks whose outputs are monotone
agree. -/
theorem exec_eq_of_monotone_both {n : ℕ} {α : Type*} [LinearOrder α]
    (A B : ComparatorNetwork n) (v : Fin n → α)
    (hA : Monotone (A.exec v)) (hB : Monotone (B.exec v)) : A.exec v = B.exec v := by
  obtain ⟨π, hπ⟩ := exec_eq_comp_perm A v
  obtain ⟨τ, hτ⟩ := exec_eq_comp_perm B v
  rw [hπ, hτ]
  rw [hπ] at hA; rw [hτ] at hB
  exact Tuple.unique_monotone hA hB

theorem bitonicBlockNetwork_exec_eq (s m : ℕ) {α : Type*} [LinearOrder α] (u : Fin m → α)
    (hu : Bitonic.BlockMono s u) :
    (bitonicBlockNetwork s m).exec u = (bitonicNetwork m).exec u :=
  exec_eq_of_monotone_both _ _ u (bitonicBlockNetwork_sorts s m u hu)
    (bitonicNetwork_sorts m α u)

namespace Chvatal

/-! ### Column network of an arbitrary column network `B` (generalising `columnSortNetwork`) -/

section Col
variable {m n : ℕ}

def colNet (B : ComparatorNetwork m) (hn : 0 < n) (j : Fin n) : ComparatorNetwork (m * n) :=
  B.scatterEmbed (m * n) (columnWireEmbed m n hn j)

def colSort (B : ComparatorNetwork m) (hn : 0 < n) : ComparatorNetwork (m * n) :=
  ⟨(List.finRange n).flatMap fun j : Fin n => (colNet B hn j).comparators⟩

theorem columnSortNetwork_eq_colSort (hn : 0 < n) :
    columnSortNetwork m n hn = colSort (bitonicNetwork m) hn := rfl

theorem colNet_scatter_wire (B : ComparatorNetwork m) (hn : 0 < n) (j : Fin n)
    (c : Comparator (m * n)) (hc : c ∈ (colNet B hn j).comparators) :
    ∃ r k : Fin m, c.i = matrixWire m n r j ∧ c.j = matrixWire m n k j := by
  dsimp [colNet, ComparatorNetwork.scatterEmbed] at hc
  rw [List.mem_map] at hc
  obtain ⟨d, _, heq⟩ := hc
  subst heq
  exact ⟨d.i, d.j, rfl, rfl⟩

theorem colNet_not_in_other_column (B : ComparatorNetwork m) (hn : 0 < n)
    {j j' : Fin n} (hne : j ≠ j') (c : Comparator (m * n))
    (hc : c ∈ (colNet B hn j').comparators) {w : Fin (m * n)}
    (hw : w ∈ columnWires m n hn j) : w ≠ c.i ∧ w ≠ c.j := by
  obtain ⟨r, k, hi, hk⟩ := colNet_scatter_wire B hn j' c hc
  have hwcol : matrixCol m n hn w = j := (mem_columnWires (m := m) (n := n) hn j w).mp hw
  have hicol : matrixCol m n hn c.i = j' := by rw [hi, (matrixWire_row_col hn r j').2]
  have hkcol : matrixCol m n hn c.j = j' := by rw [hk, (matrixWire_row_col hn k j').2]
  exact ⟨fun heq => hne (by rw [← hwcol, heq, hicol]), fun heq => hne (by rw [← hwcol, heq, hkcol])⟩

theorem colNet_foldl_outside_column (B : ComparatorNetwork m) (hn : 0 < n)
    (cols : List (Fin n)) (j : Fin n) {α : Type*} [LinearOrder α] (v : Fin (m * n) → α)
    (hdisj : ∀ col ∈ cols, col ≠ j) (w : Fin (m * n)) (hw : w ∈ columnWires m n hn j) :
    (cols.foldl (fun acc col => (colNet B hn col).exec acc) v) w = v w := by
  exact (ComparatorNetwork.foldl_exec_outside_set cols (colNet B hn) v
    (columnWires m n hn j) fun col hj' s hs c hc =>
      colNet_not_in_other_column B hn (j := j) (j' := col)
        (hne := (hdisj col hj').symm) c hc hs) w hw

theorem colNet_exec_outside_column (B : ComparatorNetwork m) (hn : 0 < n)
    {j j' : Fin n} (hne : j' ≠ j) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) (w : Fin (m * n)) (hw : w ∈ columnWires m n hn j) :
    ((colNet B hn j').exec v) w = v w := by
  unfold colNet ComparatorNetwork.exec
  refine foldl_comparators_outside _ v w ?_
  intro c hc
  exact colNet_not_in_other_column B hn (j := j) (j' := j') hne.symm c hc hw

theorem foldl_colNet (B : ComparatorNetwork m) (hn : 0 < n) {α : Type*} [LinearOrder α] :
    ∀ (cols : List (Fin n)), cols.Nodup → ∀ (v : Fin (m * n) → α) (r : Fin m) (j : Fin n),
      j ∈ cols →
      (cols.foldl (fun acc col => (colNet B hn col).exec acc) v) (matrixWire m n r j) =
        B.exec (v ∘ columnWireEmbed m n hn j) r := by
  intro cols
  induction cols with
  | nil => simp
  | cons c cs ih =>
    intro hnd v r j hj
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons]
    by_cases hjc : j = c
    · subst hjc
      rw [colNet_foldl_outside_column B hn cs j _ (fun col hcol h => hnd.1 (h ▸ hcol))
        _ (matrixWire_mem_columnWires hn r j)]
      have := ComparatorNetwork.scatterEmbed_exec_inside B (m * n)
        (columnWireEmbed m n hn j) v r
      rwa [columnWireEmbed_apply] at this
    · rw [ih hnd.2 _ r j ((List.mem_cons.mp hj).resolve_left hjc)]
      exact congrArg (fun u => B.exec u r) (funext fun s =>
        colNet_exec_outside_column B hn (Ne.symm hjc) v _
          (matrixWire_mem_columnWires hn s j))

theorem colSort_exec_matrixWire (B : ComparatorNetwork m) (hn : 0 < n) (j : Fin n) {α : Type*}
    [LinearOrder α] (v : Fin (m * n) → α) (r : Fin m) :
    (colSort B hn).exec v (matrixWire m n r j) = B.exec (v ∘ columnWireEmbed m n hn j) r := by
  dsimp [colSort]
  rw [ComparatorNetwork.exec_flatMap]
  exact foldl_colNet B hn _ (List.nodup_finRange n) v r j (List.mem_finRange j)

theorem colNet_depth_le (B : ComparatorNetwork m) (hn : 0 < n) (j : Fin n) :
    (colNet B hn j).depth ≤ B.depth := by
  simpa [colNet] using depth_scatterEmbed_le B (m * n) (columnWireEmbed m n hn j)

theorem colNet_wire_disjoint (B : ComparatorNetwork m) (hn : 0 < n)
    {a b : Fin n} (hne : a ≠ b)
    (c₁ : Comparator (m * n)) (hc₁ : c₁ ∈ (colNet B hn a).comparators)
    (c₂ : Comparator (m * n)) (hc₂ : c₂ ∈ (colNet B hn b).comparators) :
    (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j) := by
  obtain ⟨r₁, k₁, hi₁, hk₁⟩ := colNet_scatter_wire B hn a c₁ hc₁
  obtain ⟨r₂, k₂, hi₂, hk₂⟩ := colNet_scatter_wire B hn b c₂ hc₂
  have ha_i : matrixCol m n hn c₁.i = a := by rw [hi₁, (matrixWire_row_col hn r₁ a).2]
  have ha_j : matrixCol m n hn c₁.j = a := by rw [hk₁, (matrixWire_row_col hn k₁ a).2]
  have hb_i : matrixCol m n hn c₂.i = b := by rw [hi₂, (matrixWire_row_col hn r₂ b).2]
  have hb_j : matrixCol m n hn c₂.j = b := by rw [hk₂, (matrixWire_row_col hn k₂ b).2]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h; exact hne (by rw [← ha_i, h, hb_i])
  · intro h; exact hne (by rw [← ha_i, h, hb_j])
  · intro h; exact hne (by rw [← ha_j, h, hb_i])
  · intro h; exact hne (by rw [← ha_j, h, hb_j])

theorem colSort_depth_le (B : ComparatorNetwork m) (hn : 0 < n) :
    (colSort B hn).depth ≤ B.depth := by
  dsimp [colSort]
  refine depth_flatMap_disjoint (List.finRange n)
    (fun j => (colNet B hn j).comparators) B.depth ?hchunk ?hdisj
  · intro j _
    simpa using colNet_depth_le B hn j
  · refine List.Pairwise.imp ?_ ((List.nodup_iff_pairwise_ne).mp (List.nodup_finRange n))
    intro a b hne c₁ hc₁ c₂ hc₂
    exact colNet_wire_disjoint B hn hne c₁ hc₁ c₂ hc₂

end Col

/-! ### Block column sorter -/

/-- Block-aware column sorter: `bitonicBlockNetwork s m` on every column. -/
def blockColumnSortNetwork (s m n : ℕ) (hn : 0 < n) : ComparatorNetwork (m * n) :=
  colSort (bitonicBlockNetwork s m) hn

theorem blockColumnSortNetwork_depth_le (s m n : ℕ) (hn : 0 < n) :
    (blockColumnSortNetwork s m n hn).depth ≤
      bitonicDepthBudget (Nat.clog 2 m) - bitonicDepthBudget s :=
  (colSort_depth_le _ hn).trans (bitonicBlockNetwork_depth_le s m)

/-- Every column of `v` is block monotone. -/
def ColumnsBlockMono (s m n : ℕ) (hn : 0 < n) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) : Prop :=
  ∀ (j : Fin n) (r r' : Fin m), r ≤ r' → r.val / 2 ^ s = r'.val / 2 ^ s →
    v (matrixWire m n r j) ≤ v (matrixWire m n r' j)

theorem columnsBlockMono_col {s m n : ℕ} {hn : 0 < n} {α : Type*} [LinearOrder α]
    {v : Fin (m * n) → α} (hv : ColumnsBlockMono s m n hn v) (j : Fin n) :
    Bitonic.BlockMono s (v ∘ columnWireEmbed m n hn j) :=
  fun a b hab hd => hv j a b hab hd

theorem blockColumnSortNetwork_exec_eq (s m n : ℕ) (hn : 0 < n) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) (hv : ColumnsBlockMono s m n hn v) :
    (blockColumnSortNetwork s m n hn).exec v = (columnSortNetwork m n hn).exec v := by
  funext w
  rw [← matrixWire_matrixRow_col hn w]
  unfold blockColumnSortNetwork
  rw [columnSortNetwork_eq_colSort, colSort_exec_matrixWire, colSort_exec_matrixWire,
    bitonicBlockNetwork_exec_eq s m _ (columnsBlockMono_col hv _)]

end Chvatal


namespace Chvatal

/-- Physical sort-scramble-sort where the first column sort is block-aware. -/
def physicalPackNetBlock (s m n : ℕ) (hn : 0 < n) (σ : Scramble m n) :
    ComparatorNetwork (m * n) :=
  ⟨(blockColumnSortNetwork s m n hn).comparators ++
    (relabelNet (rowScrambleWirePerm m n hn σ).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel_lt hn σ)).comparators⟩

theorem physicalPackNetBlock_exec (s m n : ℕ) (hn : 0 < n) (σ : Scramble m n)
    {α : Type*} [LinearOrder α] (v : Fin (m * n) → α) (hv : ColumnsBlockMono s m n hn v) :
    (physicalPackNetBlock s m n hn σ).exec v = (physicalPackNet m n hn σ).exec v := by
  have h1 := ComparatorNetwork.exec_append (blockColumnSortNetwork s m n hn)
    (relabelNet (rowScrambleWirePerm m n hn σ).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel_lt hn σ)) v
  have h2 := ComparatorNetwork.exec_append (columnSortNetwork m n hn)
    (relabelNet (rowScrambleWirePerm m n hn σ).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel_lt hn σ)) v
  unfold physicalPackNetBlock physicalPackNet
  rw [h1, h2, blockColumnSortNetwork_exec_eq s m n hn v hv]

theorem physicalPackNetBlock_depth_le (s m n : ℕ) (hn : 0 < n) (σ : Scramble m n) :
    (physicalPackNetBlock s m n hn σ).depth ≤
      bitonicDepthBudget (Nat.clog 2 m) - bitonicDepthBudget s +
        bitonicDepthBudget (Nat.clog 2 m) := by
  have h := ComparatorNetwork.depth_append_le (blockColumnSortNetwork s m n hn)
    (relabelNet (rowScrambleWirePerm m n hn σ).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel_lt hn σ))
  rw [relabelNet_depth] at h
  have e : physicalPackNetBlock s m n hn σ = (blockColumnSortNetwork s m n hn).append
    (relabelNet (rowScrambleWirePerm m n hn σ).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel_lt hn σ)) := rfl
  rw [e]
  have := blockColumnSortNetwork_depth_le s m n hn
  have := columnSortNetwork_depth_le_budget m n hn
  omega

end Chvatal

#print axioms Chvatal.physicalPackNetBlock_exec
#print axioms Chvatal.physicalPackNetBlock_depth_le
#print axioms Chvatal.blockColumnSortNetwork_exec_eq
#print axioms Chvatal.blockColumnSortNetwork_depth_le
#print axioms Bitonic.bitonicBlockSort_sorts
#print axioms Bitonic.bitonicBlockSort_depth_le
#print axioms bitonicBlockNetwork_sorts
#print axioms bitonicBlockNetwork_depth_le
