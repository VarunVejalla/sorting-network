-- Port of `../../tapered/BaselineFringe.lean` to the δ-generic `F2PD` (sub-800, LEAN-PLAN W2).
import PaddedFringe
import F2D
import Mathlib.Tactic

namespace Sub800

open Chvatal Tapered945

/-- The deterministic F2 estimate depends on column heights and live mass,
not on realizing the marked input as a permutation threshold. This is the
pure-column version of `F2_of_SR_R1_R2`. -/
theorem F2_columns_of_SR_R1_R2 {m n : Nat} (P : F2PD) (hfm : P.f ≤ m)
    {σ₁ σ₂ : Scramble m n} (hSR : SRd P σ₁)
    (hR₁ : R1d P σ₁) (hR₂ : R2nd P σ₂)
    (c c₁ : MonotoneColumnSums m n)
    (hc₁ : ∀ col, (c₁ col).val = scrambledColSum c σ₁ col)
    (j : Nat) (hj : 0 < j) (htot : totalColumnOnes c ≤ j) (hjmax : j ≤ P.jmax n) :
    (onesAboveBottom c₁ σ₂ P.f : Real) < (1 / (P.J : Real)) * j := by
  have hJ : 0 < P.J := P.hJ
  have hJR : (0 : Real) < P.J := by exact_mod_cast hJ
  by_cases hsmall : j ≤ P.J
  · have h0 : onesAboveBottom c₁ σ₂ P.f = 0 :=
      onesAboveBottom_eq_zero_of_le c₁ σ₂ hfm fun col => by
        rw [hc₁]
        exact round1_le_f_of_SRd P hfm hSR c
          (le_min (htot.trans hsmall) (htot.trans hjmax)) col
    rw [h0]
    simp only [Nat.cast_zero]
    positivity
  · have hsmall' : P.J < j := by omega
    let q := (j + P.J - 1) / P.J
    have hdm := Nat.div_add_mod (j + P.J - 1) P.J
    have hml := Nat.mod_lt (j + P.J - 1) hJ
    have hjQ : j ≤ P.J * q := by dsimp [q]; omega
    have hQj : P.J * q < j + P.J := by dsimp [q]; omega
    have hq2 : 2 ≤ q := by
      by_contra h
      have hmul : P.J * q ≤ P.J * 1 := Nat.mul_le_mul_left P.J (by omega)
      omega
    have hjE : totalColumnOnes c ≤ P.jE n q := by
      exact le_min (htot.trans (by simpa only [Nat.mul_comm] using hjQ)) (htot.trans hjmax)
    have hqJ : (q - 1) * P.J + P.J = P.J * q := by
      obtain ⟨q', heq⟩ := Nat.exists_eq_add_of_le (show 1 ≤ q by omega)
      rw [heq]
      simp only [Nat.add_sub_cancel_left]
      ring
    have hEJ : (q - 1) * P.J ≤ P.jmax n := by omega
    have hlt := escapes_ltd P hfm hR₁ hR₂ c c₁ hc₁ q hq2 hEJ hjE
    set esc := onesAboveBottom c₁ σ₂ P.f
    have h1 : P.J * (esc + 1) ≤ P.J * q := Nat.mul_le_mul_left P.J hlt
    have h2 : esc * P.J < j := by
      rw [Nat.mul_add] at h1
      rw [Nat.mul_comm]
      omega
    have h3 : (esc : Real) * P.J < j := by exact_mod_cast h2
    rw [one_div, inv_mul_eq_div, lt_div_iff₀ hJR]
    exact h3

theorem network_exec_pointwise_mono {N : Nat} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork N) (v w : Fin N → α) (h : ∀ i, v i ≤ w i) :
    ∀ i, net.exec v i ≤ net.exec w i := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing v w with
  | nil => exact h
  | cons c cs ih =>
    simp only [List.foldl_cons]
    apply ih
    intro i
    simp only [Comparator.apply]
    split_ifs
    · exact min_le_min (h c.i) (h c.j)
    · exact max_le_max (h c.i) (h c.j)
    · exact h i

theorem semanticExec2_pointwise_mono {m n : Nat} (hn : 0 < n)
    (σ₁ σ₂ : Scramble m n) (v w : Fin (m * n) → Bool) (h : ∀ i, v i ≤ w i) :
    ∀ i, semanticExec2 hn σ₁ σ₂ v i ≤ semanticExec2 hn σ₁ σ₂ w i := by
  apply network_exec_pointwise_mono
  intro i
  apply network_exec_pointwise_mono
  intro j
  exact network_exec_pointwise_mono _ v w h _

theorem matrix_region_count_mono {m n : Nat} (hn : 0 < n)
    (v w : Fin (m * n) → Bool) (h : ∀ i, v i ≤ w i) (f : Nat) :
    matrixOnesCountInRegion hn v f ≤ matrixOnesCountInRegion hn w f := by
  apply Finset.card_le_card
  intro i hi
  simp only [matrixOnesCountInRegion, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨hi.1, Bool.le_iff_imp.mp (h i) hi.2⟩

/-- Filling the last raw row; this is independent of the input permutation. -/
def fillBottomRow {m n : Nat} (hn : 0 < n) (v : Fin ((m + 1) * n) → Bool) :
    Fin ((m + 1) * n) → Bool :=
  fun w => if (matrixRow (m + 1) n hn w).val = m then true else v w

theorem fillBottomRow_dominates {m n : Nat} (hn : 0 < n)
    (v : Fin ((m + 1) * n) → Bool) : ∀ w, v w ≤ fillBottomRow hn v w := by
  intro w
  simp only [fillBottomRow]
  split_ifs <;> simp

/-- Residual heights are exactly the marked cells in the first `m` rows. -/
def filledRowResidual {m n : Nat} (v : Fin ((m + 1) * n) → Bool) :
    MonotoneColumnSums m n := fun col =>
  ⟨(Finset.univ.filter fun r : Fin m =>
    v (matrixWire (m + 1) n r.castSucc col) = true).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩

theorem filledRow_column_count {m n : Nat} (hn : 0 < n)
    (v : Fin ((m + 1) * n) → Bool) (col : Fin n) :
    matrixColumnTrueCount col (fillBottomRow hn v) = (filledRowResidual v col).val + 1 := by
  simp only [matrixColumnTrueCount, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  have htop : ∀ r : Fin m,
      fillBottomRow hn v (matrixWire (m + 1) n r.castSucc col) =
        v (matrixWire (m + 1) n r.castSucc col) := by
    intro r
    have hr := r.isLt
    simp only [fillBottomRow, (matrixWire_row_col hn _ _).1, Fin.val_castSucc]
    rw [if_neg (by omega)]
  have hlast : fillBottomRow hn v (matrixWire (m + 1) n (Fin.last m) col) = true := by
    simp [fillBottomRow, (matrixWire_row_col hn _ _).1]
  simp only [htop, hlast, if_true, filledRowResidual, Finset.card_filter]

theorem filledRow_initial_decode {m n : Nat} (hn : 0 < n)
    (v : Fin ((m + 1) * n) → Bool) :
    monotoneColumnSumsOfBool ((columnSortNetwork (m + 1) n hn).exec (fillBottomRow hn v)) =
      baselineLiftColumnSums (filledRowResidual v) := by
  funext col
  apply Fin.ext
  change matrixColumnTrueCount col
    ((columnSortNetwork (m + 1) n hn).exec (fillBottomRow hn v)) = _
  rw [matrixColumnTrueCount_exec_eq hn col _
    (columnSortNetwork_columnLocal (m + 1) n hn), filledRow_column_count]
  rfl

theorem filledRowResidual_total {m n : Nat} (hn : 0 < n)
    (v : Fin ((m + 1) * n) → Bool) :
    totalColumnOnes (filledRowResidual v) =
      (Finset.univ.filter fun w : Fin ((m + 1) * n) =>
        (matrixRow (m + 1) n hn w).val < m ∧ v w = true).card := by
  simp only [totalColumnOnes, filledRowResidual, Finset.card_filter]
  rw [sum_matrixWire hn]
  apply Finset.sum_congr rfl
  intro col _
  have hrow : ∀ r : Fin (m + 1),
      matrixRow (m + 1) n hn (matrixWire (m + 1) n r col) = r :=
    fun r => (matrixWire_row_col hn r col).1
  rw [Fin.sum_univ_castSucc]
  simp only [hrow, Fin.val_castSucc, Fin.val_last, lt_self_iff_false,
    false_and, if_false, Nat.add_zero]
  apply Finset.sum_congr rfl
  intro r _
  simp [r.isLt]

/-- On the top `m` rows the padded input has only live ranks. Injectivity
counts those high keys against the `j`-element live rank interval. -/
theorem padded_threshold_residual_le {m n a : Nat} (hn : 0 < n)
    (ha : a ≤ (m + 1) * n) (hlive : m * n ≤ a)
    (p : Equiv.Perm (Fin a)) (j : Nat) (hja : j ≤ a) :
    totalColumnOnes (filledRowResidual
      (fun w => decide (a - j ≤ (padRankPerm ha p w).val))) ≤ j := by
  rw [filledRowResidual_total hn]
  have hcount := Finset.card_le_card_of_injOn
    (fun w : Fin ((m + 1) * n) => (padRankPerm ha p w).val)
    (s := Finset.univ.filter fun w : Fin ((m + 1) * n) =>
      (matrixRow (m + 1) n hn w).val < m ∧
      decide (a - j ≤ (padRankPerm ha p w).val) = true)
    (t := Finset.Ico (a - j) a)
    (by
      intro w hw
      change w ∈ (Finset.univ.filter fun w : Fin ((m + 1) * n) =>
        (matrixRow (m + 1) n hn w).val < m ∧
        decide (a - j ≤ (padRankPerm ha p w).val) = true) at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_iff] at hw
      have hwlt : w.val < m * n := by
        have h := hw.1
        rw [matrixRow_val] at h
        exact (Nat.div_lt_iff_lt_mul hn).mp h
      have hwa : w.val < a := hwlt.trans_le hlive
      have hkey : (padRankPerm ha p w).val < a := by
        change (padFinRanks ha p w).val < a
        simp only [padFinRanks, dif_pos hwa]
        exact (p ⟨w.val, hwa⟩).isLt
      exact Finset.mem_Ico.mpr ⟨hw.2, hkey⟩)
    (by
      intro w _ w' _ heq
      exact (padRankPerm ha p).injective (Fin.ext heq))
  simpa only [Nat.card_Ico, Nat.sub_sub_self hja] using hcount

/-- The augmented input obtains genuinely multiplicative two-round F from
the truncated scramble witnesses; the dummy cohort never enters the budget. -/
theorem baseline_semantic_F2 {m n : Nat} (P : F2PD) (hn : 0 < n)
    (hfm : P.f ≤ m) (σ₁ σ₂ : Scramble (m + 1) n)
    (hSR : SRd P (truncateBottomScramble σ₁))
    (hR₁ : R1d P (truncateBottomScramble σ₁))
    (hR₂ : R2nd P (truncateBottomScramble σ₂))
    (v : Fin ((m + 1) * n) → Bool) (j : Nat) (hj : 0 < j)
    (htot : totalColumnOnes (filledRowResidual v) ≤ j) (hjmax : j ≤ P.jmax n) :
    (matrixOnesCountInRegion hn (semanticExec2 hn σ₁ σ₂ v) (P.f + 1) : Real) <
      (1 / (P.J : Real)) * j := by
  obtain ⟨C₁, hC₁, hreg⟩ := semanticExec2_decode hn σ₁ σ₂ (fillBottomRow hn v) (P.f + 1)
  rw [filledRow_initial_decode hn v] at hC₁
  let c := filledRowResidual v
  have hpos : ∀ col, 1 ≤ (C₁ col).val := by
    intro col
    rw [hC₁, baselineLift_scrambledColSum]
    omega
  let c₁ : MonotoneColumnSums m n := fun col =>
    ⟨(C₁ col).val - 1, by have := (C₁ col).isLt; have := hpos col; omega⟩
  have hc₁ : ∀ col, (c₁ col).val = scrambledColSum c (truncateBottomScramble σ₁) col := by
    intro col
    change (C₁ col).val - 1 =
      scrambledColSum (filledRowResidual v) (truncateBottomScramble σ₁) col
    rw [hC₁, baselineLift_scrambledColSum]
    omega
  have hesc := F2_columns_of_SR_R1_R2 P hfm hSR hR₁ hR₂ c c₁ hc₁ j hj htot hjmax
  have hlift := baselineLift_two_round_escapes c c₁ C₁ σ₁ σ₂ hc₁ hC₁ P.f
  have hmono := matrix_region_count_mono hn _ _
    (semanticExec2_pointwise_mono hn σ₁ σ₂ v (fillBottomRow hn v)
      (fillBottomRow_dominates hn v)) (P.f + 1)
  have hmonoR : (matrixOnesCountInRegion hn (semanticExec2 hn σ₁ σ₂ v) (P.f + 1) : Real) ≤
    (matrixOnesCountInRegion hn (semanticExec2 hn σ₁ σ₂ (fillBottomRow hn v)) (P.f + 1) : Real) := by
    exact_mod_cast hmono
  rw [hreg, hlift] at hmonoR
  exact hmonoR.trans_lt hesc

/-- Genuine multiplicative rare-rank guarantee on the restricted live
register. Unlike ordinary padding transfer, the budget is `eps*j` with no
dummy-rank surcharge. Truncated F2 witnesses are explicit proof obligations. -/
theorem paddedPack2Net_fHigh_baseline {m n a : Nat} (P : F2PD) (hn : 0 < n)
    (ha : a ≤ (m + 1) * n) (hlive : m * n ≤ a) (hfm : P.f ≤ m)
    (σ₁ σ₂ : Scramble (m + 1) n)
    (hSR : SRd P (truncateBottomScramble σ₁))
    (hR₁ : R1d P (truncateBottomScramble σ₁))
    (hR₂ : R2nd P (truncateBottomScramble σ₂))
    (p : Equiv.Perm (Fin a)) (u j : Nat) (hu : u ≤ a)
    (hfringe : (P.f + 1) * n ≤ u + ((m + 1) * n - a))
    (hj : 0 < j) (hja : j ≤ a) (hjmax : j ≤ P.jmax n) :
    ((Finset.univ.filter fun c : Fin a =>
      a - j ≤ ((paddedPack2Net hn ha σ₁ σ₂).exec p c).val ∧ c.val < a - u).card : Real) <
      (1 / (P.J : Real)) * j := by
  let A := (m + 1) * n
  let net := physicalPack2Net (m + 1) n hn σ₁ σ₂
  let x := padRankPerm ha p
  let v : Fin A → Bool := fun w => decide (a - j ≤ (x w).val)
  have hres : totalColumnOnes (filledRowResidual v) ≤ j :=
    padded_threshold_residual_le hn ha hlive p j hja
  have hsem := baseline_semantic_F2 P hn hfm σ₁ σ₂ hSR hR₁ hR₂ v j hj hres hjmax
  have ht : A - (j + (A - a)) = a - j := by dsimp [A]; omega
  have hphysical := physical_threshold_count_eq_semantic2 hn σ₁ σ₂ x
    (j + (A - a)) (P.f + 1)
  rw [ht] at hphysical
  have hfull : ((Finset.univ.filter fun c : Fin A =>
      a - j ≤ (net.exec x c).val ∧ c.val < A - (P.f + 1) * n).card : Real) <
      (1 / (P.J : Real)) * j := by
    rw [hphysical]
    exact hsem
  have hcut : a - u ≤ A - (P.f + 1) * n := by dsimp [A]; omega
  have hsub : (Finset.univ.filter fun c : Fin A =>
      a - j ≤ (net.exec x c).val ∧ c.val < a - u) ⊆
    (Finset.univ.filter fun c : Fin A =>
      a - j ≤ (net.exec x c).val ∧ c.val < A - (P.f + 1) * n) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨hc.1, hc.2.trans_le hcut⟩
  have hcount : ((Finset.univ.filter fun c : Fin A =>
      a - j ≤ (net.exec x c).val ∧ c.val < a - u).card : Real) ≤
    ((Finset.univ.filter fun c : Fin A =>
      a - j ≤ (net.exec x c).val ∧ c.val < A - (P.f + 1) * n).card : Real) := by
    exact_mod_cast Finset.card_le_card hsub
  have hevent := padding_rank_event_card ha net p
    (fun wire rank => a - j ≤ rank ∧ wire < a - u) (by intro i hi; omega)
  rw [hevent] at hcount
  exact hcount.trans_lt hfull

/-- Symmetric low-fringe transfer for the same restricted live prefix.
Unlike the high-side theorem, this follows by reversing the full padded
physical network: the dummy suffix has ranks at least `a`, so it contributes
no keys to the lowest `j` cohort. The protected fringe must fit inside the
actual requested suffix (`u`), without charging padding. -/
theorem paddedPack2Net_fLow_baseline {m n a : Nat} (P : F2PD) (hn : 0 < n)
    (ha : a ≤ (m + 1) * n) (hfm : P.f ≤ m)
    (σ₁ σ₂ : Scramble (m + 1) n)
    (hSR : SRd P (truncateBottomScramble (flipScramble σ₁)))
    (hR₁ : R1d P (truncateBottomScramble (flipScramble σ₁)))
    (hR₂ : R2nd P (truncateBottomScramble (flipScramble σ₂)))
    (p : Equiv.Perm (Fin a)) (u j : Nat)
    (hfringe : (P.f + 1) * n ≤ u)
    (hj : 0 < j) (hja : j ≤ a) (hjmax : j ≤ P.jmax n) :
    ((Finset.univ.filter fun c : Fin a =>
      ((paddedPack2Net hn ha σ₁ σ₂).exec p c).val < j ∧ u ≤ c.val).card : Real) <
        (1 / (P.J : Real)) * j := by
  let A := (m + 1) * n
  let net := physicalPack2Net (m + 1) n hn σ₁ σ₂
  let x := padRankPerm ha p
  let xf := flipPerm x
  have hxflip : (xf : Fin A → Fin A) = fun w => Fin.rev (x (Fin.rev w)) := by
    funext w
    simp [xf, flipPerm, Equiv.Perm.mul_apply]
  have hres : totalColumnOnes (filledRowResidual
      (fun w => decide (A - j ≤ (xf w).val))) ≤ j := by
    rw [filledRowResidual_total hn]
    have hmarks : (Finset.univ.filter fun w : Fin A => A - j ≤ (xf w).val).card = j := by
      have himage : (Finset.univ.filter (fun w : Fin A => A - j ≤ (xf w).val)).image xf =
          Finset.univ.filter (fun k : Fin A => A - j ≤ k.val) := by
        ext k
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact hw
        · intro hk
          exact ⟨xf.symm k, by simpa using hk, xf.apply_symm_apply k⟩
      calc
        _ = ((Finset.univ.filter (fun w : Fin A => A - j ≤ (xf w).val)).image xf).card :=
          (Finset.card_image_of_injective _ xf.injective).symm
        _ = (Finset.univ.filter (fun k : Fin A => A - j ≤ k.val)).card := by rw [himage]
        _ = j := by rw [card_filter_val_ge _ _ (Nat.sub_le _ _)]; simp [A]; omega
    apply le_trans (Finset.card_le_card ?_)
    · exact_mod_cast (Nat.le_of_eq hmarks)
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hw ⊢
      exact hw.2
  have hsem := baseline_semantic_F2 P hn hfm (flipScramble σ₁) (flipScramble σ₂)
    hSR hR₁ hR₂
    (fun w => decide (A - j ≤ (xf w).val)) j hj hres hjmax
  have hphysical := physical_threshold_count_eq_semantic2 hn
    (flipScramble σ₁) (flipScramble σ₂) xf j (P.f + 1)
  have hhigh : ((Finset.univ.filter fun c : Fin A =>
      A - j ≤ ((physicalPack2Net (m + 1) n hn
        (flipScramble σ₁) (flipScramble σ₂)).exec xf c).val ∧
        c.val < A - (P.f + 1) * n).card : Real) <
      (1 / (P.J : Real)) * j := by
    have hphysicalR :
        ((Finset.univ.filter fun c : Fin A =>
          A - j ≤ ((physicalPack2Net (m + 1) n hn
            (flipScramble σ₁) (flipScramble σ₂)).exec xf c).val ∧
            c.val < A - (P.f + 1) * n).card : Real) =
          (matrixOnesCountInRegion hn
            (semanticExec2 hn (flipScramble σ₁) (flipScramble σ₂)
              (fun w => decide (A - j ≤ (xf w).val))) (P.f + 1) : Real) := by
      exact_mod_cast hphysical
    rw [hphysicalR]
    exact hsem
  have hdual := physicalPack2Net_flip (m := m + 1) (n := n) hn σ₁ σ₂
    (x : Fin A → Fin A)
  have hrel : ∀ c : Fin A,
      ((physicalPack2Net (m + 1) n hn (flipScramble σ₁)
        (flipScramble σ₂)).exec xf c) =
        Fin.rev ((net.exec x) (Fin.rev c)) := by
    intro c
    have h := congrFun hdual c
    simpa [net, xf, hxflip] using h
  have hfull : ((Finset.univ.filter fun c : Fin A =>
      (net.exec x c).val < j ∧ u ≤ c.val).card : Real) <
      (1 / (P.J : Real)) * j := by
    have hcount := card_low_eq_high (net.exec x)
      ((physicalPack2Net (m + 1) n hn
        (flipScramble σ₁) (flipScramble σ₂)).exec xf)
      (by intro c; exact hrel c) j u
    have hcut : A - u ≤ A - (P.f + 1) * n := Nat.sub_le_sub_left hfringe A
    have hsub : (Finset.univ.filter fun c : Fin A =>
        A - j ≤ ((physicalPack2Net (m + 1) n hn
          (flipScramble σ₁) (flipScramble σ₂)).exec xf c).val ∧
          c.val < A - u) ⊆
      Finset.univ.filter fun c : Fin A =>
        A - j ≤ ((physicalPack2Net (m + 1) n hn
          (flipScramble σ₁) (flipScramble σ₂)).exec xf c).val ∧
          c.val < A - (P.f + 1) * n := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact ⟨hc.1, hc.2.trans_le hcut⟩
    have hcast : ((Finset.univ.filter fun c : Fin A =>
        (net.exec x c).val < j ∧ u ≤ c.val).card : Real) ≤
      ((Finset.univ.filter fun c : Fin A =>
        A - j ≤ ((physicalPack2Net (m + 1) n hn
          (flipScramble σ₁) (flipScramble σ₂)).exec xf c).val ∧
          c.val < A - (P.f + 1) * n).card : Real) := by
      rw [hcount]
      exact_mod_cast (Finset.card_le_card hsub)
    exact hcast.trans_lt hhigh
  have hrestrict := padding_rank_event_card ha net p
    (fun wire rank => rank < j ∧ u ≤ wire)
    (by
      intro i hi
      simp only [not_and]
      intro hlt
      have : j ≤ i := hja.trans hi
      omega)
  have hrestrict' :
      ((Finset.univ.filter fun i : Fin A =>
        (net.exec x i).val < j ∧ u ≤ i.val).card) =
      ((Finset.univ.filter fun i : Fin a =>
        ((paddedPack2Net hn ha σ₁ σ₂).exec p i).val < j ∧ u ≤ i.val).card) := by
    simpa [net, x, paddedPack2Net] using hrestrict
  change ((Finset.univ.filter fun c : Fin a =>
      ((paddedPack2Net hn ha σ₁ σ₂).exec p c).val < j ∧ u ≤ c.val).card : Real) < _
  rw [← hrestrict']
  exact hfull

end Sub800
