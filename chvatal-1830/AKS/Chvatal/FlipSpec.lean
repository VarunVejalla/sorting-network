module
public import AKS.Chvatal.PackSpec
public import AKS.Chvatal.GeneralSeparator
public import AKS.Chvatal.ExecPlacement
public import Mathlib.Data.Fin.Tuple.Sort
public import AKS.Chvatal.ModuleA

/-! # Two-sided node guarantee: the flipped scramble and flip symmetry

Reversing key order and cell order turns the scramble `σ` into `flipScramble σ`; the smallest-key
statements follow from the largest-key ones by this symmetry. Contents: `flipScramble`, flip
equivariance of the semantic and physical executions, `packSpec_low`, and two-sided existence of
scrambles by pigeonhole. -/

@[expose] public section

namespace Chvatal

/-- Flipped scramble: row `r` is row `m-1-r` of `σ`, conjugated by column reversal. -/
def flipScramble {m n : ℕ} (σ : Scramble m n) : Scramble m n :=
  fun r => Fin.revPerm * σ (Fin.rev r) * Fin.revPerm

theorem flipScramble_apply {m n : ℕ} (σ : Scramble m n) (r : Fin m) (j : Fin n) :
    flipScramble σ r j = Fin.rev (σ (Fin.rev r) (Fin.rev j)) := rfl

theorem flipScramble_flipScramble {m n : ℕ} (σ : Scramble m n) :
    flipScramble (flipScramble σ) = σ := by
  funext r
  ext j
  simp [flipScramble_apply]

/-- The flip preserves the cardinality of any failure set. -/
theorem card_filter_flip {m n : ℕ} (P : Scramble m n → Prop) [DecidablePred P] :
    (Finset.univ.filter fun σ : Scramble m n => ¬ P (flipScramble σ)).card =
      (Finset.univ.filter fun σ : Scramble m n => ¬ P σ).card :=
  Finset.card_equiv (Function.Involutive.toPerm flipScramble flipScramble_flipScramble) (by simp)

open Classical in
/-- Two-sided Properties B (pipeline) and F: `σ` and its flip both satisfy them. -/
theorem exists_twoSided_pipelineB_paperF {m n f : ℕ} (hm : 100 ≤ m) (hn : 16 ≤ n)
    (hf : Even f) (hfbig : 17 * 10 ^ 9 ≤ f) (hfm : f ≤ m) {epsB : ℝ}
    (hepsB : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB) (hepsB0 : 0 < epsB) :
    ∃ σ : Scramble m n,
      (HasCombinatorialPropertyBOnPipeline σ epsB ∧ HasPaperPropertyF hf σ (128 / 4095) eps) ∧
      (HasCombinatorialPropertyBOnPipeline (flipScramble σ) epsB ∧
        HasPaperPropertyF hf (flipScramble σ) (128 / 4095) eps) := by
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  let O := DecodeMatrixClassObligation.standard hmpos hnpos (Nat.succ_le_of_lt hmpos)
    (Nat.succ_le_of_lt hnpos) hepsB
  have hBfail := lemma61FailBound_onPipeline_of_decodeClass epsB O
  have hfac : lemma61_failFactor m n < 1 / 100 := lemma61_failFactor_lt_one_hundredth m n hm hn
  have hFfail := paperF_fail_fraction_final hf hfm hfbig hn
  have hNpos : (0 : ℝ) < (Fintype.card (Scramble m n) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Scramble m n))
  by_contra hno
  push_neg at hno
  set N : ℝ := (Fintype.card (Scramble m n) : ℝ) with hN
  let badB := Finset.univ.filter fun σ : Scramble m n =>
    ¬ HasCombinatorialPropertyBOnPipeline σ epsB
  let badF := Finset.univ.filter fun σ : Scramble m n =>
    ¬ HasPaperPropertyF hf σ (128 / 4095) eps
  let badB' := Finset.univ.filter fun σ : Scramble m n =>
    ¬ HasCombinatorialPropertyBOnPipeline (flipScramble σ) epsB
  let badF' := Finset.univ.filter fun σ : Scramble m n =>
    ¬ HasPaperPropertyF hf (flipScramble σ) (128 / 4095) eps
  have hBle : (badB.card : ℝ) ≤ lemma61_failFactor m n * N :=
    hBfail.bound badB (fun σ hσ => by simpa [badB] using hσ)
  have hB'le : (badB'.card : ℝ) ≤ lemma61_failFactor m n * N := by
    have hc : badB'.card = badB.card :=
      card_filter_flip (fun σ => HasCombinatorialPropertyBOnPipeline σ epsB)
    rw [hc]; exact hBle
  have hFle : (badF.card : ℝ) ≤ 44 / 100 * N := hFfail
  have hF'le : (badF'.card : ℝ) ≤ 44 / 100 * N := by
    have hc : badF'.card = badF.card :=
      card_filter_flip (fun σ => HasPaperPropertyF hf σ (128 / 4095) eps)
    rw [hc]; exact hFle
  have hcover : (Finset.univ : Finset (Scramble m n)) ⊆ ((badB ∪ badF) ∪ badB') ∪ badF' := by
    intro σ _
    by_cases h1 : HasCombinatorialPropertyBOnPipeline σ epsB
    · by_cases h2 : HasPaperPropertyF hf σ (128 / 4095) eps
      · by_cases h3 : HasCombinatorialPropertyBOnPipeline (flipScramble σ) epsB
        · have h4 := hno σ ⟨h1, h2⟩ h3
          exact Finset.mem_union_right _ (by simp [badF', h4])
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [badB', h3]))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (by simp [badF, h2])))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (by simp [badB, h1])))
  have hcard : N ≤ (badB.card : ℝ) + badF.card + badB'.card + badF'.card := by
    have h1 := Finset.card_le_card hcover
    have h2 : (badB ∪ badF ∪ badB' ∪ badF').card ≤
        badB.card + badF.card + badB'.card + badF'.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right
          (Finset.card_union_le badB badF) _)) _)
    simp only [Finset.card_univ] at h1
    have := h1.trans h2
    rw [hN]
    exact_mod_cast this
  have hfacN : lemma61_failFactor m n * N ≤ 1 / 100 * N :=
    mul_le_mul_of_nonneg_right hfac.le hNpos.le
  linarith

open Classical in
/-- Two-sided Property B only (pipeline), no `f` constraint. -/
theorem exists_twoSided_B {m n : ℕ} (hm : 100 ≤ m) (hn : 16 ≤ n) {epsB : ℝ}
    (hepsB : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB) :
    ∃ σ : Scramble m n,
      HasCombinatorialPropertyBOnPipeline σ epsB ∧
        HasCombinatorialPropertyBOnPipeline (flipScramble σ) epsB := by
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  let O := DecodeMatrixClassObligation.standard hmpos hnpos (Nat.succ_le_of_lt hmpos)
    (Nat.succ_le_of_lt hnpos) hepsB
  have hBfail := lemma61FailBound_onPipeline_of_decodeClass epsB O
  have hfac : lemma61_failFactor m n < 1 / 100 := lemma61_failFactor_lt_one_hundredth m n hm hn
  have hNpos : (0 : ℝ) < (Fintype.card (Scramble m n) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Scramble m n))
  by_contra hno
  push_neg at hno
  set N : ℝ := (Fintype.card (Scramble m n) : ℝ) with hN
  let badB := Finset.univ.filter fun σ : Scramble m n =>
    ¬ HasCombinatorialPropertyBOnPipeline σ epsB
  let badB' := Finset.univ.filter fun σ : Scramble m n =>
    ¬ HasCombinatorialPropertyBOnPipeline (flipScramble σ) epsB
  have hBle : (badB.card : ℝ) ≤ lemma61_failFactor m n * N :=
    hBfail.bound badB (fun σ hσ => by simpa [badB] using hσ)
  have hB'le : (badB'.card : ℝ) ≤ lemma61_failFactor m n * N := by
    have hc : badB'.card = badB.card :=
      card_filter_flip (fun σ => HasCombinatorialPropertyBOnPipeline σ epsB)
    rw [hc]; exact hBle
  have hcover : (Finset.univ : Finset (Scramble m n)) ⊆ badB ∪ badB' := by
    intro σ _
    by_cases h1 : HasCombinatorialPropertyBOnPipeline σ epsB
    · exact Finset.mem_union_right _ (by simp [badB', hno σ h1])
    · exact Finset.mem_union_left _ (by simp [badB, h1])
  have hcard : N ≤ (badB.card : ℝ) + badB'.card := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_union_le badB badB'
    simp only [Finset.card_univ] at h1
    rw [hN]
    exact_mod_cast h1.trans h2
  have hfacN : lemma61_failFactor m n * N ≤ 1 / 100 * N :=
    mul_le_mul_of_nonneg_right hfac.le hNpos.le
  linarith

/-! ## 2. Flip equivariance of the semantic execution -/

/-- Two monotone rearrangements of the same vector coincide. -/
theorem monotone_rearr_unique {m : ℕ} {β : Type*} [LinearOrder β] (g : Fin m → β)
    (τ τ' : Equiv.Perm (Fin m)) (h : Monotone (g ∘ τ)) (h' : Monotone (g ∘ τ')) :
    g ∘ τ = g ∘ τ' := by
  rw [Tuple.comp_sort_eq_comp_iff_monotone.2 h, Tuple.comp_sort_eq_comp_iff_monotone.2 h']

/-- Sorting commutes with an order-reversing map composed with position reversal. -/
theorem rearr_flip {m : ℕ} {β : Type*} [LinearOrder β] (e : β → β) (he : Antitone e)
    (u S T : Fin m → β) (ρ ρ' : Equiv.Perm (Fin m))
    (hS : S = u ∘ ρ) (hSm : Monotone S)
    (hT : T = (fun r => e (u (Fin.rev r))) ∘ ρ') (hTm : Monotone T) :
    T = fun r => e (S (Fin.rev r)) := by
  have hR : (fun r => e (S (Fin.rev r))) =
      (fun r => e (u (Fin.rev r))) ∘
        ((Fin.revPerm : Equiv.Perm (Fin m)) * ρ * (Fin.revPerm : Equiv.Perm (Fin m))) := by
    funext r
    simp [hS]
  have hRm : Monotone (fun r => e (S (Fin.rev r))) :=
    fun a b hab => he (hSm (Fin.rev_le_rev.2 hab))
  rw [hR]
  rw [hR] at hRm
  rw [hT]
  exact monotone_rearr_unique _ _ _ (hT ▸ hTm) hRm

theorem fin_rev_antitone {N : ℕ} : Antitone (Fin.rev : Fin N → Fin N) :=
  fun _ _ h => Fin.rev_le_rev.2 h

private theorem rev_arith (m n r j : ℕ) (hr : r < m) (hj : j < n) :
    m * n - (r * n + j + 1) = (m - (r + 1)) * n + (n - (j + 1)) := by
  obtain ⟨a, rfl⟩ : ∃ a, m = r + 1 + a := ⟨m - (r + 1), by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = j + 1 + b := ⟨n - (j + 1), by omega⟩
  have e1 : r + 1 + a - (r + 1) = a := by omega
  have e2 : j + 1 + b - (j + 1) = b := by omega
  rw [e1, e2]
  apply Nat.sub_eq_of_eq_add
  ring

theorem rev_matrixWire (m n : ℕ) (r : Fin m) (j : Fin n) :
    Fin.rev (matrixWire m n r j) = matrixWire m n (Fin.rev r) (Fin.rev j) := by
  apply Fin.ext
  simp only [Fin.val_rev, matrixWire_row]
  have := rev_arith m n r.val j.val r.isLt j.isLt
  exact this

/-- Column sorting commutes with value reversal and cell reversal. -/
theorem colSort_flip {m n : ℕ} (hn : 0 < n) (v : Fin (m * n) → Fin (m * n)) :
    (columnSortNetwork m n hn).net.exec (fun w => Fin.rev (v (Fin.rev w))) =
      fun w => Fin.rev ((columnSortNetwork m n hn).net.exec v (Fin.rev w)) := by
  funext w
  rw [← matrixWire_matrixRow_col hn w]
  set r := matrixRow m n hn w
  set j := matrixCol m n hn w
  rw [rev_matrixWire, columnSortNetwork_exec_matrixWire, columnSortNetwork_exec_matrixWire]
  obtain ⟨ρ, hρ⟩ := ComparatorNetwork.exec_eq_comp_perm (bitonicNetwork m)
    (v ∘ columnWireEmbed m n hn (Fin.rev j))
  have hT : (fun w' : Fin (m * n) => Fin.rev (v (Fin.rev w'))) ∘ columnWireEmbed m n hn j =
      fun r => Fin.rev ((v ∘ columnWireEmbed m n hn (Fin.rev j)) (Fin.rev r)) := by
    funext r'
    simp only [Function.comp, columnWireEmbed_apply, rev_matrixWire, Fin.rev_rev]
  obtain ⟨ρ', hρ'⟩ := ComparatorNetwork.exec_eq_comp_perm (bitonicNetwork m)
    ((fun w' : Fin (m * n) => Fin.rev (v (Fin.rev w'))) ∘ columnWireEmbed m n hn j)
  have := rearr_flip (m := m) (fun k : Fin (m * n) => Fin.rev k) fin_rev_antitone
    (v ∘ columnWireEmbed m n hn (Fin.rev j))
    ((bitonicNetwork m).exec (v ∘ columnWireEmbed m n hn (Fin.rev j)))
    ((bitonicNetwork m).exec
      ((fun w' : Fin (m * n) => Fin.rev (v (Fin.rev w'))) ∘ columnWireEmbed m n hn j))
    ρ ρ' hρ (bitonicNetwork_sorts m _ _) (by rw [hρ', hT]) (bitonicNetwork_sorts m _ _)
  exact congrFun this r

theorem rowScrambleWirePerm_flip {m n : ℕ} (hn : 0 < n) (σ : Scramble m n) (w : Fin (m * n)) :
    rowScrambleWirePerm m n hn (flipScramble σ) (Fin.rev w) =
      Fin.rev (rowScrambleWirePerm m n hn σ w) := by
  rw [← matrixWire_matrixRow_col hn w]
  set r := matrixRow m n hn w
  set j := matrixCol m n hn w
  rw [rev_matrixWire, rowScrambleWirePerm_apply, rowScrambleWirePerm_apply, rev_matrixWire,
    flipScramble_apply, Fin.rev_rev, Fin.rev_rev]

theorem rowScrambleWirePerm_symm_flip {m n : ℕ} (hn : 0 < n) (σ : Scramble m n)
    (w : Fin (m * n)) :
    (rowScrambleWirePerm m n hn (flipScramble σ)).symm (Fin.rev w) =
      Fin.rev ((rowScrambleWirePerm m n hn σ).symm w) := by
  apply (rowScrambleWirePerm m n hn (flipScramble σ)).injective
  rw [Equiv.apply_symm_apply, rowScrambleWirePerm_flip, Equiv.apply_symm_apply]

/-- The semantic execution of the canonical pack, in closed form. -/
theorem semanticExec_canonical {m n : ℕ} (hn : 0 < n) (σ : Scramble m n)
    (v : Fin (m * n) → Fin (m * n)) :
    (canonicalSortScrambleSortPack m n hn σ).semanticExec v =
      (columnSortNetwork m n hn).net.exec
        (fun w => (columnSortNetwork m n hn).net.exec v
          ((rowScrambleWirePerm m n hn σ).symm w)) := by
  have hid : ∀ y : Fin (m * n) → Fin (m * n), (rowScrambleNetwork m n hn σ).net.exec y = y := by
    intro y
    simp [ComparatorNetwork.exec, rowScrambleNetwork_comparators_eq_nil m n hn σ]
  simp only [SortScrambleSortPack.semanticExec, SortScrambleSortPack.middleExec,
    sortScrambleMiddleExec, RowScrambleNetwork.wiredExec, canonicalSortScrambleSortPack,
    SortScrambleSortPack.colSort]
  rw [hid]
  rfl

/-- **Flip equivariance of the semantic execution.** With `x̃ w = rev (x (cellRev w))`
(`rev k = m·n-1-k`, `cellRev w = m·n-1-w`), the flipped scramble's pack acts on `x̃` as the
original acts on `x`, conjugated by the reversals. -/
theorem semanticExec_flip {m n : ℕ} (hn : 0 < n) (σ : Scramble m n)
    (x : Fin (m * n) → Fin (m * n)) :
    (canonicalSortScrambleSortPack m n hn (flipScramble σ)).semanticExec
        (fun w => Fin.rev (x (Fin.rev w))) =
      fun w => Fin.rev ((canonicalSortScrambleSortPack m n hn σ).semanticExec x (Fin.rev w)) := by
  have h : (fun w => (columnSortNetwork m n hn).net.exec
        (fun w => Fin.rev (x (Fin.rev w)))
        ((rowScrambleWirePerm m n hn (flipScramble σ)).symm w)) =
      fun w => Fin.rev ((fun w' => (columnSortNetwork m n hn).net.exec x
        ((rowScrambleWirePerm m n hn σ).symm w')) (Fin.rev w)) := by
    funext w
    rw [colSort_flip]
    have h2 : (rowScrambleWirePerm m n hn (flipScramble σ)).symm w =
        Fin.rev ((rowScrambleWirePerm m n hn σ).symm (Fin.rev w)) := by
      have := rowScrambleWirePerm_symm_flip hn σ (Fin.rev w)
      rwa [Fin.rev_rev] at this
    simp only [h2, Fin.rev_rev]
  rw [semanticExec_canonical, semanticExec_canonical, h]
  exact colSort_flip hn (fun w' => (columnSortNetwork m n hn).net.exec x
    ((rowScrambleWirePerm m n hn σ).symm w'))

/-- Physical flip equivariance: `physicalPackNet` for the flip on `x̃` is the reversed
physical output for `σ` on `x`. -/
theorem physicalPackNet_flip {m n : ℕ} (hn : 0 < n) (σ : Scramble m n)
    (x : Fin (m * n) → Fin (m * n)) :
    (physicalPackNet m n hn (flipScramble σ)).exec (fun w => Fin.rev (x (Fin.rev w))) =
      fun c => Fin.rev ((physicalPackNet m n hn σ).exec x (Fin.rev c)) := by
  funext c
  rw [physicalPackNet_exec, physicalPackNet_exec]
  show (canonicalSortScrambleSortPack m n hn (flipScramble σ)).semanticExec _
      (rowScrambleWirePerm m n hn (flipScramble σ) c) = _
  rw [semanticExec_flip]
  show Fin.rev ((canonicalSortScrambleSortPack m n hn σ).semanticExec x
      (Fin.rev (rowScrambleWirePerm m n hn (flipScramble σ) c))) =
    Fin.rev ((canonicalSortScrambleSortPack m n hn σ).semanticExec x
      (rowScrambleWirePerm m n hn σ (Fin.rev c)))
  congr 2
  have := rowScrambleWirePerm_flip hn σ (Fin.rev c)
  rw [Fin.rev_rev] at this
  rw [this, Fin.rev_rev]

/-- The flip of a permutation of keys (a permutation again). -/
def flipPerm {N : ℕ} (x : Equiv.Perm (Fin N)) : Equiv.Perm (Fin N) :=
  Fin.revPerm * x * Fin.revPerm

/-! ## 3. Low-side node guarantee -/

/-- Counting translation: the smallest `t` values at cells `≥ s` of `y` correspond, after
reversing values and cells, to the largest `t` values at cells `< N - s` of `yf`. -/
theorem card_low_eq_high {N : ℕ} (y yf : Fin N → Fin N)
    (hy : ∀ c, yf c = Fin.rev (y (Fin.rev c))) (t s : ℕ) :
    (Finset.univ.filter fun c : Fin N => (y c).val < t ∧ s ≤ c.val).card =
      (Finset.univ.filter fun c : Fin N => N - t ≤ (yf c).val ∧ c.val < N - s).card := by
  refine Finset.card_bij' (fun c _ => Fin.rev c) (fun c _ => Fin.rev c) ?_ ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rw [hy, Fin.rev_rev, Fin.val_rev, Fin.val_rev]
    have := (y c).isLt
    have := c.isLt
    omega
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rw [hy, Fin.val_rev] at hc
    rw [Fin.val_rev]
    have := (y (Fin.rev c)).isLt
    have := c.isLt
    constructor
    · omega
    · omega
  · intro c _; exact Fin.rev_rev c
  · intro c _; exact Fin.rev_rev c

theorem packSpec_low {m n f b : ℕ} (hn : 0 < n) (σ : Scramble m n)
    (hmfb : m = 2 * f + 64 * b) (hfm : f ≤ m) {epsB deltaF epsF : ℝ}
    (hB' : HasPackSemanticPropertyB hn
      (canonicalSortScrambleSortPack m n hn (flipScramble σ)) epsB)
    (hF' : HasPackSemanticPropertyF hn
      (canonicalSortScrambleSortPack m n hn (flipScramble σ)) f hfm deltaF epsF) :
    (∀ x : Equiv.Perm (Fin (m * n)), ∀ p ∈ blockBounds (2 * f * n) (b * n), p ≤ m * n →
      ((Finset.univ.filter fun c : Fin (m * n) =>
        ((physicalPackNet m n hn σ).exec (x : Fin (m * n) → Fin (m * n)) c).val < p ∧
          p ≤ c.val).card : ℝ) ≤ epsB / 2 * (m * n)) ∧
    (∀ x : Equiv.Perm (Fin (m * n)), ∀ j : ℕ, 0 < j → (j : ℝ) ≤ deltaF * (f * n) →
      ((Finset.univ.filter fun c : Fin (m * n) =>
        ((physicalPackNet m n hn σ).exec (x : Fin (m * n) → Fin (m * n)) c).val < j ∧
          (2 * f * n) / 2 ≤ c.val).card : ℝ) < epsF * j) := by
  have hH := packSpec_high hn (flipScramble σ) hmfb hfm hB' hF'
  have key : ∀ (x : Equiv.Perm (Fin (m * n))) (t s : ℕ),
      (Finset.univ.filter fun c : Fin (m * n) =>
        ((physicalPackNet m n hn σ).exec (x : Fin (m * n) → Fin (m * n)) c).val < t ∧
          s ≤ c.val).card =
      (Finset.univ.filter fun c : Fin (m * n) =>
        m * n - t ≤ ((physicalPackNet m n hn (flipScramble σ)).exec
          ((flipPerm x : Equiv.Perm (Fin (m * n))) : Fin (m * n) → Fin (m * n)) c).val ∧
          c.val < m * n - s).card := by
    intro x t s
    refine card_low_eq_high _ _ (fun c => ?_) t s
    exact congrFun (physicalPackNet_flip hn σ (x : Fin (m * n) → Fin (m * n))) c
  refine ⟨fun x p hp hpmn => ?_, fun x j hj hjd => ?_⟩
  · rw [key x p p]
    exact hH.1 (flipPerm x) p hp hpmn
  · rw [key x j _]
    have hdiv : 2 * f * n / 2 = f * n := by
      rw [show 2 * f * n = 2 * (f * n) by ring]; omega
    rw [hdiv]
    have := packSpec_high_F hn (flipScramble σ) hfm hF' (flipPerm x) j hj hjd
    rw [hdiv] at this
    exact this

/-! ## 4(c). Two-sided existence (semantic) -/

/-- Semantic Property F of the canonical pack from the paper Property F of `σ`. -/
theorem packSemanticF_of_paperF {m n f : ℕ} (hf : Even f) (hn : 0 < n) (hfm : f ≤ m)
    (σ : Scramble m n) (hF : HasPaperPropertyF hf σ (128 / 4095) eps)
    {deltaF epsF : ℝ} (hδ : deltaF ≤ 128 / 4095) (hε : eps ≤ epsF) :
    HasPackSemanticPropertyF hn (canonicalSortScrambleSortPack m n hn σ) f hfm deltaF epsF := by
  have h0 : HasPackSemanticPropertyF hn (canonicalSortScrambleSortPack m n hn σ) f hfm
      (128 / 4095) eps :=
    HasPackSemanticPropertyF.of_paperF (hf := hf) hn hfm (by norm_num)
      (IdealColumnSort.all_packs hn) (RowScrambleCorrect.all_packs_forall hn)
      (canonicalSortScrambleSortPack m n hn σ)
      (fun c j hc hj hjδ S => hF c j hc hj hjδ S)
  exact HasPackSemanticPropertyF.mono hn _ hfm hδ hε h0

/-- **Two-sided Thm 5.1 existence.** Some scramble `σ` has semantic Properties B and F for
both `σ` and the flipped scramble. -/
theorem ExistsScrambleSeparator_twoSided {g : ScrambleGeometry} {P : Theorem51Params g}
    (hfbig : 17 * 10 ^ 9 ≤ g.f) (hδ : P.deltaF ≤ 128 / 4095) (hε : eps ≤ P.epsF) :
    ∃ σ : Scramble g.m g.n,
      (HasPackSemanticPropertyB (scrambleGeometry_hn g)
          (canonicalSortScrambleSortPack g.m g.n (scrambleGeometry_hn g) σ) P.epsB ∧
        HasPackSemanticPropertyF (scrambleGeometry_hn g)
          (canonicalSortScrambleSortPack g.m g.n (scrambleGeometry_hn g) σ) g.f
          (scrambleGeometry_f_le_m g) P.deltaF P.epsF) ∧
      (HasPackSemanticPropertyB (scrambleGeometry_hn g)
          (canonicalSortScrambleSortPack g.m g.n (scrambleGeometry_hn g) (flipScramble σ))
          P.epsB ∧
        HasPackSemanticPropertyF (scrambleGeometry_hn g)
          (canonicalSortScrambleSortPack g.m g.n (scrambleGeometry_hn g) (flipScramble σ)) g.f
          (scrambleGeometry_f_le_m g) P.deltaF P.epsF) := by
  have hn := scrambleGeometry_hn g
  obtain ⟨σ, ⟨hB1, hF1⟩, ⟨hB2, hF2⟩⟩ := exists_twoSided_pipelineB_paperF (n := g.n) g.hm g.hn
    g.hfeven hfbig (scrambleGeometry_f_le_m g) P.hepsB_lb P.hepsB_pos
  exact ⟨σ,
    ⟨HasPackSemanticPropertyB_canonical_of_combinatorial_onPipeline hn σ hB1,
      packSemanticF_of_paperF g.hfeven hn (scrambleGeometry_f_le_m g) σ hF1 hδ hε⟩,
    ⟨HasPackSemanticPropertyB_canonical_of_combinatorial_onPipeline hn _ hB2,
      packSemanticF_of_paperF g.hfeven hn (scrambleGeometry_f_le_m g) _ hF2 hδ hε⟩⟩

/-- Two-sided semantic Property B only, for any `m ≥ 100`, `n ≥ 16`. -/
theorem ExistsScrambleSeparator_twoSided_B {m n : ℕ} (hm : 100 ≤ m) (hn : 16 ≤ n)
    {epsB : ℝ} (hepsB : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB) :
    ∃ σ : Scramble m n,
      HasPackSemanticPropertyB (lt_of_lt_of_le (by norm_num) hn)
          (canonicalSortScrambleSortPack m n (lt_of_lt_of_le (by norm_num) hn) σ) epsB ∧
        HasPackSemanticPropertyB (lt_of_lt_of_le (by norm_num) hn)
          (canonicalSortScrambleSortPack m n (lt_of_lt_of_le (by norm_num) hn)
            (flipScramble σ)) epsB := by
  obtain ⟨σ, h1, h2⟩ := exists_twoSided_B hm hn hepsB
  exact ⟨σ, HasPackSemanticPropertyB_canonical_of_combinatorial_onPipeline _ σ h1,
    HasPackSemanticPropertyB_canonical_of_combinatorial_onPipeline _ _ h2⟩

end Chvatal
