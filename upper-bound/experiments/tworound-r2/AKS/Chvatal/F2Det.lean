module

public import AKS.Chvatal.F2Defs
public import AKS.Chvatal.PackSpec2
public import AKS.Chvatal.Lemma62Bridge

/-! # Two-round fringe contract: the deterministic reduction (`F2ROUND.md` §2)

`F2_of_SR_R1_R2 : F2SmallRank P σ1 → F2R1 P σ1 → F2R2 P σ2 →
  HasPackSemanticPropertyF2 hn σ1 σ2 P.f hfm (128/4095) (1 / P.J)`.

Lean form of the note's lemmas (all for a fixed monotone input `c`, round-1 heights
`c1 col = scrambledColSum c σ1 col`, round-2 heights `scrambledColSum c1 σ2`):

* D2 `scrambledColSum_le_add_hits`: `z_col ≤ g1 + H_col`, `H_col = scrambledColSumInAboveBottomRows c σ1 g1 col`.
* D3: `w_v ≤ g2 + D_v`, `D_v = scrambledColSumInAboveBottomRows c1 σ2 g2 v`; instead of passing to
  `ŷ = (H - Δ)₊` we apply R2 to `c1` itself, whose part above `g2` is dominated by `ŷ`
  (so the support/sum conditions follow from R1).  This avoids D1 (monotone rounds) altogether.
* D4 `F2SmallRank_zero_escapes`, D5 `escapes_lt`.

Corollaries: `F2_flip_pair` (flipped pair). -/

@[expose] public section

namespace Chvatal

open Finset

/-- Ones in the rows above `g` landing in `S` = sum over `S` of the per-column hit counts. -/
theorem onesInRows_topRows_eq_sum {m n : ℕ} (g : ℕ) (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (S : Finset (Fin n)) :
    onesInRows c σ (topRows m g) S = ∑ col ∈ S, scrambledColSumInAboveBottomRows c σ g col := by
  have h := onesAboveHalfFringe_eq_sum_aboveBottomRows (2 * g) c σ S
  have e : 2 * g / 2 = g := by omega
  unfold onesAboveHalfFringe at h
  rw [e] at h
  exact h

/-- **D2/D3 (one round).** -/
theorem scrambledColSum_le_add_hits {m n : ℕ} (c : MonotoneColumnSums m n) (σ : Scramble m n)
    {g : ℕ} (hg : g ≤ m) (col : Fin n) :
    scrambledColSum c σ col ≤ g + scrambledColSumInAboveBottomRows c σ g col := by
  have := onesAboveBottom_le_scrambledColSumInAboveBottomRows c σ g col hg
  omega

theorem scrambledColSumInAboveBottomRows_eq_zero {m n : ℕ} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) {g : ℕ} (hle : ∀ col, (c col).val ≤ g) (col : Fin n) :
    scrambledColSumInAboveBottomRows c σ g col = 0 := by
  classical
  unfold scrambledColSumInAboveBottomRows
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro r _ ⟨hr, hmem⟩
  simp only [scrambledRowOnes, monotoneRowOnes, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and] at hmem
  obtain ⟨x, hx, -⟩ := hmem
  have := hle x
  have := r.isLt
  omega

theorem onesAboveBottom_eq_zero_of_le {m n : ℕ} (c : MonotoneColumnSums m n) (σ : Scramble m n)
    {g : ℕ} (hgm : g ≤ m) (hle : ∀ col, (c col).val ≤ g) : onesAboveBottom c σ g = 0 := by
  refine Finset.sum_eq_zero fun col _ => ?_
  have := onesAboveBottom_le_scrambledColSumInAboveBottomRows c σ g col hgm
  rw [scrambledColSumInAboveBottomRows_eq_zero c σ hle] at this
  omega

/-- **D4.** SR bounds every round-1 column height by `f`. -/
theorem round1_le_f_of_SR {m n : ℕ} (P : F2Params) (hfm : P.f ≤ m) {σ1 : Scramble m n}
    (hSR : F2SmallRank P σ1) (c : MonotoneColumnSums m n)
    (htot : totalColumnOnes c ≤ min P.J (P.jmax n)) (col : Fin n) :
    scrambledColSum c σ1 col ≤ P.f := by
  have h1 := hSR c htot {col} (Finset.card_singleton col)
  rw [onesInRows_topRows_eq_sum, Finset.sum_singleton] at h1
  have := P.hg12
  have := P.hg2f
  have h2 := scrambledColSum_le_add_hits c σ1 (g := P.g1) (by omega) col
  omega

/-- **D5.** Under R1 and R2 the escapes of a matrix of total at most `j_E` are `< E`. -/
theorem escapes_lt {m n : ℕ} (P : F2Params) (hfm : P.f ≤ m) {σ1 σ2 : Scramble m n}
    (hR1 : F2R1 P σ1) (hR2 : F2R2 P σ2) (c c1 : MonotoneColumnSums m n)
    (hc1 : ∀ col, (c1 col).val = scrambledColSum c σ1 col) (E : ℕ) (hE : 2 ≤ E)
    (htot : totalColumnOnes c ≤ P.jE n E) :
    onesAboveBottom c1 σ2 P.f < E := by
  classical
  have hg1 := P.hg12
  have hg2 := P.hg2f
  have hg1m : P.g1 ≤ m := by omega
  have hg2m : P.g2 ≤ m := by omega
  have hΔ : P.g2 = P.g1 + P.Δ := by unfold F2Params.Δ; omega
  have hB : 0 < P.B E := P.B_pos (by omega)
  set H : Fin n → ℕ := fun col => scrambledColSumInAboveBottomRows c σ1 P.g1 col with hH
  have hz : ∀ col, (c1 col).val ≤ P.g1 + H col := fun col => by
    rw [hc1]; exact scrambledColSum_le_add_hits c σ1 hg1m col
  have hsumH : ∀ S : Finset (Fin n), onesInRows c σ1 (topRows m P.g1) S = ∑ col ∈ S, H col :=
    fun S => onesInRows_topRows_eq_sum P.g1 c σ1 S
  set S0 : Finset (Fin n) := Finset.univ.filter fun col => P.Δ + 1 ≤ H col with hS0
  -- (a): support
  have hcard : S0.card ≤ P.κ E := by
    by_contra h
    push_neg at h
    obtain ⟨S', hsub, hcd⟩ := Finset.exists_subset_card_eq (show P.κ E + 1 ≤ S0.card by omega)
    have h1 := hR1.1 E hE c htot S' hcd
    rw [hsumH] at h1
    have h2 : (P.Δ + 1) * S'.card ≤ ∑ col ∈ S', H col := by
      calc (P.Δ + 1) * S'.card = ∑ _col ∈ S', (P.Δ + 1) := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum fun col hcol => (Finset.mem_filter.mp (hsub hcol)).2
    rw [hcd] at h2
    omega
  have hout : ∀ col, col ∉ S0 → (c1 col).val - P.g2 = 0 := fun col hcol => by
    simp only [hS0, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hcol
    have := hz col
    omega
  -- (b): total
  have hsum : ∑ col, ((c1 col).val - P.g2) < P.B E := by
    rw [← Finset.sum_subset (Finset.subset_univ S0) (fun col _ hcol => hout col hcol)]
    rcases S0.eq_empty_or_nonempty with he | hne
    · rw [he]; simpa using hB
    · have h1 := hR1.2 E hE c htot S0 hne.card_pos hcard
      rw [hsumH] at h1
      have h2 : ∑ col ∈ S0, (((c1 col).val - P.g2) + P.Δ) ≤ ∑ col ∈ S0, H col :=
        Finset.sum_le_sum fun col hcol => by
          have := hz col
          have := (Finset.mem_filter.mp hcol).2
          omega
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm] at h2
      omega
  have hsupp : (Finset.univ.filter fun col => P.g2 < (c1 col).val).card ≤ P.κ E := by
    refine le_trans (Finset.card_le_card fun col hcol => ?_) hcard
    have := (Finset.mem_filter.mp hcol).2
    have := hz col
    simp only [hS0, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  by_contra hge
  push_neg at hge
  set S := excessColumnSet c1 σ2 (P.f + 1) with hS
  have hesc : onesAboveBottom c1 σ2 P.f = ∑ col ∈ S, (scrambledColSum c1 σ2 col - P.f) := by
    unfold onesAboveBottom
    rw [hS, excessColumnSet, Finset.sum_filter]
    exact Finset.sum_congr rfl fun col _ => by split_ifs <;> omega
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro he
    rw [he, Finset.sum_empty] at hesc
    omega
  have h2 := hR2 E hE c1 hsupp hsum S hne
  rw [onesInRows_topRows_eq_sum] at h2
  have h3 : ∑ col ∈ S, ((scrambledColSum c1 σ2 col - P.f) + P.Φ) ≤
      ∑ col ∈ S, scrambledColSumInAboveBottomRows c1 σ2 P.g2 col :=
    Finset.sum_le_sum fun col hcol => by
      have := onesAboveBottom_le_scrambledColSumInAboveBottomRows c1 σ2 P.g2 col hg2m
      have := (mem_excessColumnSet _ _ _ _).mp hcol
      have : P.Φ = P.f - P.g2 := rfl
      omega
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm, ← hesc] at h3
  omega

/-- Decode of the two-round region count: a monotone matrix `c1` whose column heights are the
round-1 scrambled sums of `c` and which carries the whole second round. -/
theorem semanticExec2_decode {m n : ℕ} (hn : 0 < n) (σ1 σ2 : Scramble m n)
    (v : Fin (m * n) → Bool) (i : ℕ) :
    ∃ c1 : MonotoneColumnSums m n,
      (∀ col, (c1 col).val = scrambledColSum
        (monotoneColumnSumsOfBool ((columnSortNetwork m n hn).exec v)) σ1 col) ∧
      matrixOnesCountInRegion hn (semanticExec2 hn σ1 σ2 v) i = onesAboveBottom c1 σ2 i := by
  set c := monotoneColumnSumsOfBool ((columnSortNetwork m n hn).exec v) with hc
  have hu1 : (columnSortNetwork m n hn).exec v = monotoneMatrixBool hn c :=
    monotoneMatrixBool_eq_of_columnMonotone hn _ (columnSortNetwork_columnMonotone hn v)
  have hcm : ColumnMonotoneInput m n hn (semanticExec hn σ1 v) :=
    columnSortNetwork_columnMonotone hn _
  set c1 := monotoneColumnSumsOfBool (semanticExec hn σ1 v) with hc1
  have hu : semanticExec hn σ1 v = monotoneMatrixBool hn c1 :=
    monotoneMatrixBool_eq_of_columnMonotone hn _ hcm
  refine ⟨c1, fun col => ?_, ?_⟩
  · show matrixColumnTrueCount col (semanticExec hn σ1 v) = _
    rw [semanticExec, matrixColumnTrueCount_exec_eq hn col _ (columnSortNetwork_columnLocal m n hn),
      hu1, scrambledColSum_eq_matrixColumnTrueCount hn σ1 c col]
  · have e : semanticExec2 hn σ1 σ2 v = (columnSortNetwork m n hn).exec
        (semanticExec hn σ1 v ∘ (rowScrambleWirePerm m n hn σ2).symm) := rfl
    rw [e, matrixOnesCountInRegion_colSort_eq_sum_columnSub hn i]
    refine Finset.sum_congr rfl fun col _ => ?_
    rw [scrambledColSum_eq_matrixColumnTrueCount hn σ2 c1 col, ← hu]

/-- **Small-rank form** (σ1-only): SR gives zero escapes of the one-round semantic output. -/
theorem F2SmallRank_zero_escapes {m n : ℕ} (P : F2Params) (hn : 0 < n) (hfm : P.f ≤ m)
    {σ1 : Scramble m n} (hSR : F2SmallRank P σ1) :
    ∀ (v : Equiv.Perm (Fin (m * n))) (j : ℕ), 0 < j → j ≤ P.J →
      (j : ℝ) ≤ (128 / 4095 : ℝ) * (P.f * n) →
      matrixOnesCountInRegion hn
        (semanticExec hn σ1 fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)) P.f = 0 := by
  intro v j hj hjJ hjδ
  have hjmn : j ≤ m * n := by
    have : (P.f : ℝ) * n ≤ m * n := by gcongr
    exact_mod_cast (by push_cast; linarith [show (0 : ℝ) ≤ P.f * n by positivity] :
      (j : ℝ) ≤ (m * n : ℕ))
  rw [matrixOnesCountInRegion_semanticExec]
  set c := monotoneColumnSumsOfBool
      ((columnSortNetwork m n hn).exec fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w))
  have htot : totalColumnOnes c = j := sum_topJ_colSums_eq_j hn v j hjmn
  have hjmax : j ≤ P.jmax n := Nat.le_floor hjδ
  refine Finset.sum_eq_zero fun col _ => ?_
  have := round1_le_f_of_SR P hfm hSR c (by rw [htot]; exact le_min hjJ hjmax) col
  omega

/-- Zero escapes survive any second round. -/
theorem F2SmallRank_zero_escapes2 {m n : ℕ} (P : F2Params) (hn : 0 < n) (hfm : P.f ≤ m)
    {σ1 : Scramble m n} (σ2 : Scramble m n) (hSR : F2SmallRank P σ1)
    (v : Equiv.Perm (Fin (m * n))) (j : ℕ) (hj : 0 < j) (hjJ : j ≤ P.J)
    (hjδ : (j : ℝ) ≤ (128 / 4095 : ℝ) * (P.f * n)) :
    matrixOnesCountInRegion hn
      (semanticExec2 hn σ1 σ2 fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)) P.f
      = 0 :=
  Nat.eq_zero_of_le_zero
    ((matrixOnesCountInRegion_semanticExec2_le hn σ1 σ2 _ P.f).trans
      (F2SmallRank_zero_escapes P hn hfm hSR v j hj hjJ hjδ).le)

/-- **Main deterministic reduction (F2 from SR, R1, R2).** -/
theorem F2_of_SR_R1_R2 {m n : ℕ} (P : F2Params) (hn : 0 < n) (hfm : P.f ≤ m)
    {σ1 σ2 : Scramble m n} (hSR : F2SmallRank P σ1) (hR1 : F2R1 P σ1) (hR2 : F2R2 P σ2) :
    HasPackSemanticPropertyF2 hn σ1 σ2 P.f hfm (128 / 4095) (1 / (P.J : ℝ)) := by
  intro v j hj hjδ
  have hJ : 0 < P.J := P.hJ
  have hJR : (0 : ℝ) < P.J := by exact_mod_cast hJ
  have hjmn : j ≤ m * n := by
    have : (P.f : ℝ) * n ≤ m * n := by gcongr
    exact_mod_cast (by push_cast; linarith [show (0 : ℝ) ≤ P.f * n by positivity] :
      (j : ℝ) ≤ (m * n : ℕ))
  obtain ⟨c1, hc1, hreg⟩ := semanticExec2_decode hn σ1 σ2
    (fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)) P.f
  rw [hreg]
  set c := monotoneColumnSumsOfBool
      ((columnSortNetwork m n hn).exec fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w))
  have htot : totalColumnOnes c = j := sum_topJ_colSums_eq_j hn v j hjmn
  have hjmax : j ≤ P.jmax n := Nat.le_floor hjδ
  by_cases hsmall : j ≤ P.J
  · have h0 : onesAboveBottom c1 σ2 P.f = 0 :=
      onesAboveBottom_eq_zero_of_le c1 σ2 hfm fun col => by
        rw [hc1]; exact round1_le_f_of_SR P hfm hSR c (by rw [htot]; exact le_min hsmall hjmax) col
    rw [h0]
    simp only [Nat.cast_zero]
    positivity
  · push_neg at hsmall
    obtain ⟨q, hq⟩ : ∃ q, q = (j + P.J - 1) / P.J := ⟨_, rfl⟩
    have hdm := Nat.div_add_mod (j + P.J - 1) P.J
    have hml := Nat.mod_lt (j + P.J - 1) hJ
    rw [← hq] at hdm
    generalize (j + P.J - 1) % P.J = r at hdm hml
    generalize hQ : P.J * q = Q at hdm
    have hjQ : j ≤ Q := by omega
    have hQj : Q < j + P.J := by omega
    have hq2 : 2 ≤ q := by
      by_contra h
      push_neg at h
      have : P.J * q ≤ P.J * 1 := Nat.mul_le_mul_left P.J (by omega)
      omega
    have hjE : totalColumnOnes c ≤ P.jE n q := by
      rw [htot]
      exact le_min (by rw [Nat.mul_comm, hQ]; exact hjQ) hjmax
    have hlt := escapes_lt P hfm hR1 hR2 c c1 hc1 q hq2 hjE
    set esc := onesAboveBottom c1 σ2 P.f
    have h1 : P.J * (esc + 1) ≤ P.J * q := Nat.mul_le_mul_left P.J hlt
    have h2 : esc * P.J < j := by
      rw [Nat.mul_add, hQ] at h1
      rw [Nat.mul_comm]
      omega
    have h3 : (esc : ℝ) * P.J < j := by exact_mod_cast h2
    rw [one_div, inv_mul_eq_div, lt_div_iff₀ hJR]
    exact h3

/-- **Flipped pair.**  The flip of a good pair is handled by applying the theorem to
`flipScramble σ1`, `flipScramble σ2`; this is the form consumed by `packSpec2_low`. -/
theorem F2_flip_pair {m n : ℕ} (P : F2Params) (hn : 0 < n) (hfm : P.f ≤ m)
    {σ1 σ2 : Scramble m n} (hSR : F2SmallRank P (flipScramble σ1))
    (hR1 : F2R1 P (flipScramble σ1)) (hR2 : F2R2 P (flipScramble σ2)) :
    HasPackSemanticPropertyF2 hn (flipScramble σ1) (flipScramble σ2) P.f hfm (128 / 4095)
      (1 / (P.J : ℝ)) :=
  F2_of_SR_R1_R2 P hn hfm hSR hR1 hR2

/-- Both orientations at once. -/
theorem F2_both_orientations {m n : ℕ} (P : F2Params) (hn : 0 < n) (hfm : P.f ≤ m)
    {σ1 σ2 : Scramble m n}
    (h : F2SmallRank P σ1 ∧ F2R1 P σ1 ∧ F2R2 P σ2)
    (h' : F2SmallRank P (flipScramble σ1) ∧ F2R1 P (flipScramble σ1) ∧
      F2R2 P (flipScramble σ2)) :
    HasPackSemanticPropertyF2 hn σ1 σ2 P.f hfm (128 / 4095) (1 / (P.J : ℝ)) ∧
    HasPackSemanticPropertyF2 hn (flipScramble σ1) (flipScramble σ2) P.f hfm (128 / 4095)
      (1 / (P.J : ℝ)) :=
  ⟨F2_of_SR_R1_R2 P hn hfm h.1 h.2.1 h.2.2, F2_flip_pair P hn hfm h'.1 h'.2.1 h'.2.2⟩

/-- The concrete instance: `eps = 1/(86·10⁶)`. -/
theorem F2_of_SR_R1_R2_std {m n : ℕ} (hn : 0 < n) (hfm : 131040 ≤ m)
    {σ1 σ2 : Scramble m n} (hSR : F2SmallRank F2Params.std σ1) (hR1 : F2R1 F2Params.std σ1)
    (hR2 : F2R2 F2Params.std σ2) :
    HasPackSemanticPropertyF2 hn σ1 σ2 131040 hfm (128 / 4095) eps := by
  have h := F2_of_SR_R1_R2 F2Params.std hn hfm hSR hR1 hR2
  have e : (1 / ((F2Params.std.J : ℕ) : ℝ)) = eps := by
    unfold eps F2Params.std; norm_num
  rw [e] at h
  exact h

end Chvatal
