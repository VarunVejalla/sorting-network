import R1Induction
import AKS.Sort.Untangle
import AKS.Sort.Perm
import AKS.Bitonic.Shrink

/-! # The final layer at `k = 16` (W1, step 13)

Port of the package's `FinalSorts`: a prefix network sending the wires of each block onto an
interval of ranks, followed by bitonic sorters on the blocks, untangles into a sorting network. -/

namespace R1T

open Chvatal (KBag)

/-- A strictly monotone map `Fin m → ℕ` landing in `[base, base + m)` is `k ↦ base + k`. -/
theorem strictMono_interval16 {m : ℕ} (f : Fin m → ℕ) (hf : StrictMono f) (base : ℕ)
    (hlo : ∀ k, base ≤ f k) (hhi : ∀ k, f k < base + m) (k : Fin m) :
    f k = base + k.val := by
  have gap : ∀ (a b : ℕ) (ha : a < m) (hb : b < m), a ≤ b →
      f ⟨a, ha⟩ + (b - a) ≤ f ⟨b, hb⟩ := by
    intro a b ha hb hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      have := ih (by omega)
      have : f ⟨b, by omega⟩ < f ⟨b + 1, hb⟩ := hf (by simp [Fin.lt_def])
      omega
  have hm : 0 < m := Fin.pos k
  have h1 := gap 0 k.val hm k.isLt (Nat.zero_le _)
  have h2 := gap k.val (m - 1) k.isLt (by omega) (by omega)
  have h3 := hlo ⟨0, hm⟩
  have h4 := hhi ⟨m - 1, by omega⟩
  have e1 : f ⟨k.val, k.isLt⟩ = f k := rfl
  omega

/-- Conversion of a standard network to a generalized one. -/
def toGen16 {n : ℕ} (G : ComparatorNetwork n) : Untangle.GenNetwork n :=
  ⟨G.comparators.map fun c => ⟨c.i, c.j, ne_of_lt c.h⟩⟩

theorem toGen16_exec {n : ℕ} {α : Type*} [LinearOrder α] (G : ComparatorNetwork n)
    (v : Fin n → α) : (toGen16 G).exec v = G.exec v := by
  unfold toGen16 Untangle.GenNetwork.exec ComparatorNetwork.exec
  simp only [List.foldl_map]
  rfl

theorem toGen16_depth {n : ℕ} (G : ComparatorNetwork n) : (toGen16 G).depth = G.depth := by
  unfold toGen16 Untangle.GenNetwork.depth ComparatorNetwork.depth
  simp only [List.foldl_map]
  rfl

section Final

variable {d : ℕ} (S : KBag 16 d → Finset (Fin (16 ^ d)))
  (hdisj : ∀ b b', b ≠ b' → Disjoint (S b) (S b'))
  (hcover : ∀ w, ∃ b, w ∈ S b)
  (base : KBag 16 d → ℕ) (A : ComparatorNetwork (16 ^ d))
  (himage : ∀ (p : Equiv.Perm (Fin (16 ^ d))) (b : KBag 16 d),
    (S b).image (A.exec (fun w => p w)) =
      Finset.univ.filter (fun x : Fin (16 ^ d) => base b ≤ x.val ∧ x.val < base b + (S b).card))

include hdisj himage in
/-- On the wires of block `b`, the bitonic stage after `A` outputs `base b + k` at the `k`-th
wire of `S b`, whatever the permutation input. -/
theorem final_block_value (p : Equiv.Perm (Fin (16 ^ d))) (b : KBag 16 d) (k : Fin (S b).card) :
    ((stageNet S (fun _ n => bitonicNetwork n)).exec (A.exec (fun w => p w))
      (((S b).orderEmbOfFin rfl) k)).val = base b + k.val := by
  set e := (S b).orderEmbOfFin rfl with he
  set x : Fin (S b).card → Fin (16 ^ d) := fun i => A.exec (fun w => p w) (e i) with hx
  rw [stageNet_exec_inside S hdisj (fun _ n => bitonicNetwork n) (A.exec (fun w => p w)) b]
  obtain ⟨ρ', hρ'⟩ := ComparatorNetwork.exec_eq_comp_perm A (fun w => p w)
  have hxinj : Function.Injective x := fun i j hij => by
    simp only [hx, hρ', Function.comp] at hij
    exact e.injective (ρ'.injective (p.injective hij))
  obtain ⟨ρ, hρ⟩ := ComparatorNetwork.exec_eq_comp_perm (bitonicNetwork (S b).card) x
  set y := (bitonicNetwork (S b).card).exec x with hy
  have hymono : Monotone y := bitonicNetwork_sorts _ (Fin (16 ^ d)) x
  have hyinj : Function.Injective y := by rw [hρ]; exact hxinj.comp ρ.injective
  have hymem : ∀ k, base b ≤ (y k).val ∧ (y k).val < base b + (S b).card := fun k => by
    have : y k ∈ (S b).image (A.exec (fun w => p w)) := by
      rw [hρ]; exact Finset.mem_image_of_mem _ (Finset.orderEmbOfFin_mem _ rfl _)
    rw [himage p b] at this
    simpa using this
  exact strictMono_interval16 (fun k => (y k).val) (fun i j hij => hymono.strictMono_of_injective hyinj hij)
    (base b) (fun k => (hymem k).1) (fun k => (hymem k).2) k

include hdisj hcover himage in
/-- The output of the whole network on the permutation inputs does not depend on the input. -/
theorem final_exec_const (p : Equiv.Perm (Fin (16 ^ d))) (w : Fin (16 ^ d)) :
    (A.append (stageNet S (fun _ n => bitonicNetwork n))).exec (fun w => p w) w =
      (A.append (stageNet S (fun _ n => bitonicNetwork n))).exec
        (fun w => (1 : Equiv.Perm (Fin (16 ^ d))) w) w := by
  obtain ⟨b, hb⟩ := hcover w
  obtain ⟨k, rfl⟩ : w ∈ Set.range ((S b).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hb
  apply Fin.ext
  have e1 : ∀ q : Equiv.Perm (Fin (16 ^ d)),
      (A.append (stageNet S (fun _ n => bitonicNetwork n))).exec (fun w => q w) =
        (stageNet S (fun _ n => bitonicNetwork n)).exec (A.exec (fun w => q w)) :=
    fun q => ComparatorNetwork.exec_append A (stageNet S (fun _ n => bitonicNetwork n)) _
  rw [e1, e1, final_block_value S hdisj base A himage p b k,
    final_block_value S hdisj base A himage 1 b k]

include hdisj hcover himage in
/-- **Generic final layer.** `A` followed by bitonic sorters on the blocks `S b` can be untangled
into a sorting network of depth at most `A.depth + (stageNet ...).depth`. -/
theorem final_layer_sorts :
    ∃ T : ComparatorNetwork (16 ^ d),
      T.depth ≤ A.depth + (stageNet S (fun _ n => bitonicNetwork n)).depth ∧
        ComparatorNetwork.Sorts.{0} T := by
  set F := stageNet S (fun _ n => bitonicNetwork n) with hF
  set G := A.append F with hG
  obtain ⟨ρ, hρ⟩ := ComparatorNetwork.exec_eq_comp_perm G
    (fun w => (1 : Equiv.Perm (Fin (16 ^ d))) w)
  have hY : ∀ (p : Equiv.Perm (Fin (16 ^ d))) r, G.exec (fun w => p w) (ρ.symm r) = r := by
    intro p r
    rw [final_exec_const S hdisj hcover base A himage p, hρ]
    simp
  have hmono : ∀ (α : Type) [LinearOrder α] (v : Fin (16 ^ d) → α),
      Monotone (fun r : Fin (16 ^ d) => (toGen16 G).exec v (ρ.symm r)) := by
    intro α _ v
    obtain ⟨σ, hσ⟩ := exists_sorting_perm v
    have h := ComparatorNetwork.exec_comp_monotone G hσ (fun w => σ w)
    have : ∀ r, (toGen16 G).exec v (ρ.symm r) = (v ∘ ⇑σ.symm) r := fun r => by
      rw [toGen16_exec]
      have h2 : G.exec v (ρ.symm r) = G.exec ((v ∘ ⇑σ.symm) ∘ (fun w => σ w)) (ρ.symm r) :=
        by congr 1; funext w; simp only [Function.comp_apply, Equiv.symm_apply_apply]
      rw [h2, ← h]
      show (v ∘ ⇑σ.symm) (G.exec (fun w => σ w) (ρ.symm r)) = _
      rw [hY σ r]
    intro r s hrs
    show (toGen16 G).exec v (ρ.symm r) ≤ (toGen16 G).exec v (ρ.symm s)
    rw [this, this]
    exact hσ hrs
  obtain ⟨T, hT, hTs⟩ := Untangle.untangle (toGen16 G) ρ hmono
  exact ⟨T, by rw [hT, toGen16_depth]; exact ComparatorNetwork.depth_append_le A F, hTs⟩

end Final


section Stages

variable {d tf : ℕ}

/-- The first `t` stages, composed sequentially. -/
noncomputable def stagesNet (F : FlowTableB d tf)
    (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n) :
    ℕ → ComparatorNetwork (16 ^ d)
  | 0 => ⟨[]⟩
  | t + 1 => (stagesNet F nets t).append (stageNet (wireSets F t) (nets t))

theorem stagesNet_exec (F : FlowTableB d tf)
    (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (16 ^ d))) :
    ∀ t, (stagesNet F nets t).exec (fun w => v w) = X F nets v t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show ((stagesNet F nets t).append (stageNet (wireSets F t) (nets t))).exec _ = _
    unfold ComparatorNetwork.append
    rw [ComparatorNetwork.exec_append, ih]
    rfl

theorem stagesNet_depth_le (F : FlowTableB d tf)
    (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
    (D : ℕ → ℕ) (T : ℕ) (hT : T ≤ tf + 1)
    (hD : ∀ t < T, ∀ b n, (nets t b n).depth ≤ D t) :
    (stagesNet F nets T).depth ≤ ∑ t ∈ Finset.range T, D t := by
  induction T with
  | zero => simp [stagesNet, ComparatorNetwork.depth]
  | succ T ih =>
    rw [Finset.sum_range_succ]
    refine (ComparatorNetwork.depth_append_le _ _).trans (add_le_add
      (ih (by omega) (fun t ht => hD t (by omega))) ?_)
    exact stageNet_depth_le _ (wireSets_disjoint F (by omega)) _
      (fun b => hD T (by omega) b _)

end Stages

section Blocks

variable {d : ℕ}

/-- Final occupancy: only the meeting level is occupied, `16^4` wires per node. -/
def FinalFact (F : FlowTableB d (tf d)) : Prop :=
  ∀ b : KBag 16 d, F.a (tf d) b = if b.l = meet d then 16 ^ 4 else 0

/-- The final blocks: the wires of the meeting-level nodes. -/
noncomputable def finalS (F : FlowTableB d (tf d)) (b : KBag 16 d) : Finset (Fin (16 ^ d)) :=
  if b.l = meet d then wireSets F (tf d) b else ∅

variable (F : FlowTableB d (tf d)) (hfin : FinalFact F)
include hfin

theorem finalS_card (b : KBag 16 d) (hb : b.l = meet d) : (finalS F b).card = 16 ^ 4 := by
  unfold finalS; rw [if_pos hb, wireSets_card F le_rfl b, hfin b, if_pos hb]

omit hfin in
theorem finalS_disjoint (b b' : KBag 16 d) (hne : b ≠ b') : Disjoint (finalS F b) (finalS F b') := by
  unfold finalS
  split_ifs
  · exact wireSets_disjoint F le_rfl b b' hne
  all_goals simp

theorem finalS_cover (w : Fin (16 ^ d)) : ∃ b : KBag 16 d, w ∈ finalS F b := by
  obtain ⟨q, hq⟩ := wireSets_complete F (t := tf d) le_rfl w
  have hql : q.l = meet d := by
    by_contra h
    have := wireSets_card F le_rfl q
    rw [hfin q, if_neg h, Finset.card_eq_zero] at this
    simp [this] at hq
  exact ⟨q, by unfold finalS; rw [if_pos hql]; exact hq⟩

theorem finalS_card_cases (b : KBag 16 d) : (finalS F b).card = 0 ∨ (finalS F b).card = 2 ^ 16 := by
  by_cases hb : b.l = meet d
  · right; rw [finalS_card F hfin b hb]; norm_num
  · left; unfold finalS; rw [if_neg hb]; rfl

/-- **Purity at `t_f`** (Lemma 4.5): `μ · c(d−4, t_f) = μ · 2^16 < 1`. -/
theorem purity (hd : 10 ≤ d) (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (16 ^ d)))
    (hP : OutsiderBoundLe d (tf d) (execPlacement F nets v (tf d) le_rfl) id)
    (b : KBag 16 d) (hb : b.l = meet d) :
    b.strangers 1 id ((execPlacement F nets v (tf d) le_rfl).regs b) (by norm_num : 1 ≤ 16) = 0 := by
  have h := hP b 0 (Nat.zero_le d)
  rw [hb, cap_eq_pow d (meet d) (tf d) 16 (by have := exp_meet d hd; push_cast; omega)] at h
  have hlt : (mu * delta ^ 0 * ((2 ^ 16 : ℕ) : ℚ)) < 1 := by unfold mu; norm_num
  have : ((b.strangers (0 + 1) id ((execPlacement F nets v (tf d) le_rfl).regs b) : ℕ) : ℚ) < 1 :=
    lt_of_le_of_lt h hlt
  have h1 : b.strangers (0 + 1) id ((execPlacement F nets v (tf d) le_rfl).regs b) < 1 := by
    exact_mod_cast this
  simpa using h1

/-- Purity turns each final block into a rank interval. -/
theorem finalS_image (hd : 10 ≤ d) (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (16 ^ d)))
    (hP : OutsiderBoundLe d (tf d) (execPlacement F nets v (tf d) le_rfl) id) (b : KBag 16 d) :
    (finalS F b).image (X F nets v (tf d)) =
      Finset.univ.filter (fun x : Fin (16 ^ d) =>
        b.x * 2 ^ 16 ≤ x.val ∧ x.val < b.x * 2 ^ 16 + (finalS F b).card) := by
  by_cases hb : b.l = meet d
  · rw [finalS_card F hfin b hb]
    have hsize : 16 ^ (d - b.l) = 2 ^ 16 := by
      rw [hb]; unfold meet; rw [show d - (d - 4) = 4 by omega]; norm_num
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hk
      have hw' : w ∈ wireSets F (tf d) b := by unfold finalS at hw; rwa [if_pos hb] at hw
      have h0 := purity F hfin hd nets v hP b hb
      unfold KBag.strangers at h0
      have hnot := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.mp h0)
        (show X F nets v (tf d) w ∈ (execPlacement F nets v (tf d) le_rfl).regs b from
          Finset.mem_image_of_mem _ hw')
      simp only [KBag.Strange, show (1 : ℕ) ≠ 0 by omega, false_or, not_not] at hnot
      have hanc : b.ancestor (1 - 1) (by norm_num : 1 ≤ 16) = b := by
        apply KBag.ext <;> simp [KBag.ancestor]
      rw [hanc] at hnot
      simp only [KBag.Native, Chvatal.nativeBagIdx, Chvatal.bagSize, id, hsize] at hnot
      have h1 := Nat.div_mul_le_self (X F nets v (tf d) w).val (2 ^ 16)
      have h2 := Nat.lt_div_mul_add (a := (X F nets v (tf d) w).val) (by positivity : 0 < 2 ^ 16)
      rw [hnot] at h1 h2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by norm_num at h1 ⊢; omega, by norm_num at h2 ⊢; omega⟩
    · rw [Finset.card_image_of_injective _ (X_injective _ nets v _), finalS_card F hfin b hb]
      have hsub : (Finset.univ.filter (fun x : Fin (16 ^ d) =>
            b.x * 2 ^ 16 ≤ x.val ∧ x.val < b.x * 2 ^ 16 + 16 ^ 4)).map Fin.valEmbedding ⊆
          Finset.Ico (b.x * 2 ^ 16) (b.x * 2 ^ 16 + 16 ^ 4) := by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
        exact Finset.mem_Ico.mpr (Finset.mem_filter.1 hx).2
      have := Finset.card_le_card hsub
      rw [Finset.card_map, Nat.card_Ico] at this
      omega
  · have : finalS F b = ∅ := by unfold finalS; rw [if_neg hb]
    rw [this]
    ext x
    simp

end Blocks

/-- **The sorter from the flow facts.** -/
theorem r1_sorter_of_facts {d : ℕ} (hd : 10 ≤ d) (F : FlowTableB d (tf d))
    (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
    (hspec : R1Specs F nets) (hpar : ∀ t, t ≤ tf d → ParityFact F t) (hres : ResidFact F)
    (hfin : FinalFact F) :
    ∃ T : ComparatorNetwork (16 ^ d), ComparatorNetwork.Sorts.{0} T ∧
      T.depth ≤ (stagesNet F nets (tf d)).depth +
        (stageNet (finalS F) (fun _ n => bitonicNetwork n)).depth := by
  have hP := fun v => P_all F nets hspec hpar hres v (tf d) le_rfl
  obtain ⟨T, hTd, hTs⟩ := final_layer_sorts (finalS F) (finalS_disjoint F)
    (finalS_cover F hfin) (fun b => b.x * 2 ^ 16) (stagesNet F nets (tf d)) (by
      intro p b
      rw [stagesNet_exec]
      exact finalS_image F hfin hd nets p (hP p) b)
  exact ⟨T, hTs, hTd⟩

end R1T
