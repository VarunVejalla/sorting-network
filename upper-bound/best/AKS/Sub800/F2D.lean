import AKS.Chvatal.F2Det

/-! # Two-round fringe contract with a general fringe fraction `δ`

Copy of the package's `F2Defs` predicates and `F2Det` reduction, with `128/4095` replaced by the
field `δ` of `F2PD`. Only the parameter-dependent pieces are copied; the `δ`-free lemmas
(`onesInRows_topRows_eq_sum`, `semanticExec2_decode`, ...) are reused from the package. -/

namespace Chvatal

/-- Parameters of the two-round contract with fringe fraction `δ`. -/
structure F2PD where
  f : ℕ
  g1 : ℕ
  g2 : ℕ
  J : ℕ
  c : ℝ
  b : ℝ
  δ : ℝ
  hg1 : 0 < g1
  hg12 : g1 < g2
  hg2f : g2 < f
  hJ : 0 < J
  hc0 : 0 < c
  hb0 : 0 < b
  hδ : 0 < δ
  hδ1 : δ ≤ 1

namespace F2PD

def Δ (P : F2PD) : ℕ := P.g2 - P.g1
def Φ (P : F2PD) : ℕ := P.f - P.g2
noncomputable def κ (P : F2PD) (E : ℕ) : ℕ := ⌈P.c * E⌉₊
noncomputable def B (P : F2PD) (E : ℕ) : ℕ := ⌈P.b * E⌉₊
/-- `Jmax = ⌊δ f n⌋`. -/
noncomputable def jmax (P : F2PD) (n : ℕ) : ℕ := ⌊P.δ * (P.f * n)⌋₊
noncomputable def jE (P : F2PD) (n E : ℕ) : ℕ := min (E * P.J) (P.jmax n)

theorem B_pos (P : F2PD) {E : ℕ} (hE : 1 ≤ E) : 0 < P.B E :=
  Nat.ceil_pos.mpr (mul_pos P.hb0 (by exact_mod_cast hE))

end F2PD

/-- **SR** (small ranks): for every monotone `c` of total at most `min J Jmax`, every column
receives at most `f - g1` ones of `c` in the rows strictly above the bottom `g1`, after scramble
`σ1`.  Complement: `tailBadSet c (topRows m g1) 1 (f - g1 + 1)`. -/
def SRd {m n : ℕ} (P : F2PD) (σ1 : Scramble m n) : Prop :=
  ∀ c : MonotoneColumnSums m n, totalColumnOnes c ≤ min P.J (P.jmax n) →
    ∀ S : Finset (Fin n), S.card = 1 →
      onesInRows c σ1 (topRows m P.g1) S < P.f - P.g1 + 1

/-- **R1(a)** : no `κ_E + 1` columns carry `(Δ + 1)(κ_E + 1)` hits.  Complement:
`tailBadSet c (topRows m g1) (κ_E + 1) ((Δ + 1) (κ_E + 1))`. -/
def R1ad {m n : ℕ} (P : F2PD) (σ1 : Scramble m n) : Prop :=
  ∀ E : ℕ, 2 ≤ E → ∀ c : MonotoneColumnSums m n, totalColumnOnes c ≤ P.jE n E →
    ∀ S : Finset (Fin n), S.card = P.κ E + 1 →
      onesInRows c σ1 (topRows m P.g1) S < (P.Δ + 1) * (P.κ E + 1)

/-- **R1(b)** : no `s ∈ [1, κ_E]` columns carry `Δ s + B_E` hits.  Complement:
`tailBadSet c (topRows m g1) s (Δ s + B_E)`. -/
def R1bd {m n : ℕ} (P : F2PD) (σ1 : Scramble m n) : Prop :=
  ∀ E : ℕ, 2 ≤ E → ∀ c : MonotoneColumnSums m n, totalColumnOnes c ≤ P.jE n E →
    ∀ S : Finset (Fin n), 1 ≤ S.card → S.card ≤ P.κ E →
      onesInRows c σ1 (topRows m P.g1) S < P.Δ * S.card + P.B E

/-- **R1** = R1(a) ∧ R1(b). -/
def R1d {m n : ℕ} (P : F2PD) (σ1 : Scramble m n) : Prop := R1ad P σ1 ∧ R1bd P σ1

/-- **R2**: for every monotone `c` whose part above `g2` (the `y`-vector `c - g2`) has support of
size at most `κ_E` and total at most `B_E - 1`, no nonempty column set `S` receives `Φ |S| + E`
ones of `c` in the rows above `g2` after scramble `σ2`.  Complement:
`tailBadSet c (topRows m g2) s (Φ s + E)`.

Note (deviation from `F2ROUND.md` §1): the note writes `onesInRows(y, σ2, all rows, S)`; the
deterministic reduction (D3) uses the rows `ℓ > g2` of `σ2` with heights `g2 + y`, i.e.
`onesInRows c σ2 (topRows m g2) S` with `c = g2 + y`.  The two have the same law for a uniform
`σ2` (rows are i.i.d.), and the `topRows m g2` form is the one that is deterministically needed. -/
def R2d {m n : ℕ} (P : F2PD) (σ2 : Scramble m n) : Prop :=
  ∀ E : ℕ, 2 ≤ E → ∀ c : MonotoneColumnSums m n,
    (Finset.univ.filter fun col => P.g2 < (c col).val).card ≤ P.κ E →
    ∑ col, ((c col).val - P.g2) < P.B E →
    ∀ S : Finset (Fin n), S.Nonempty →
      onesInRows c σ2 (topRows m P.g2) S < P.Φ * S.card + E

/-- `R2d` restricted to the ranks `E` with `(E - 1) J ≤ jmax n` (the only ones used by
`F2Det.F2_of_SR_R1_R2d`, where `E = ⌈j/J⌉` and `j ≤ jmax n`). -/
def R2nd {m n : ℕ} (P : F2PD) (σ2 : Scramble m n) : Prop :=
  ∀ E : ℕ, 2 ≤ E → (E - 1) * P.J ≤ P.jmax n → ∀ c : MonotoneColumnSums m n,
    (Finset.univ.filter fun col => P.g2 < (c col).val).card ≤ P.κ E →
    ∑ col, ((c col).val - P.g2) < P.B E →
    ∀ S : Finset (Fin n), S.Nonempty →
      onesInRows c σ2 (topRows m P.g2) S < P.Φ * S.card + E

/-- **D4.** SR bounds every round-1 column height by `f`. -/
theorem round1_le_f_of_SRd {m n : ℕ} (P : F2PD) (hfm : P.f ≤ m) {σ1 : Scramble m n}
    (hSR : SRd P σ1) (c : MonotoneColumnSums m n)
    (htot : totalColumnOnes c ≤ min P.J (P.jmax n)) (col : Fin n) :
    scrambledColSum c σ1 col ≤ P.f := by
  have h1 := hSR c htot {col} (Finset.card_singleton col)
  rw [onesInRows_topRows_eq_sum, Finset.sum_singleton] at h1
  have := P.hg12
  have := P.hg2f
  have h2 := scrambledColSum_le_add_hits c σ1 (g := P.g1) (by omega) col
  omega

/-- **D5.** Under R1 and R2 the escapes of a matrix of total at most `j_E` are `< E`. -/
theorem escapes_ltd {m n : ℕ} (P : F2PD) (hfm : P.f ≤ m) {σ1 σ2 : Scramble m n}
    (hR1 : R1d P σ1) (hR2 : R2nd P σ2) (c c1 : MonotoneColumnSums m n)
    (hc1 : ∀ col, (c1 col).val = scrambledColSum c σ1 col) (E : ℕ) (hE : 2 ≤ E)
    (hEJ : (E - 1) * P.J ≤ P.jmax n)
    (htot : totalColumnOnes c ≤ P.jE n E) :
    onesAboveBottom c1 σ2 P.f < E := by
  classical
  have hg1 := P.hg12
  have hg2 := P.hg2f
  have hg1m : P.g1 ≤ m := by omega
  have hg2m : P.g2 ≤ m := by omega
  have hΔ : P.g2 = P.g1 + P.Δ := by unfold F2PD.Δ; omega
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
  have h2 := hR2 E hE hEJ c1 hsupp hsum S hne
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

/-- **Small-rank form** (σ1-only): SR gives zero escapes of the one-round semantic output. -/
theorem SRd_zero_escapes {m n : ℕ} (P : F2PD) (hn : 0 < n) (hfm : P.f ≤ m)
    {σ1 : Scramble m n} (hSR : SRd P σ1) :
    ∀ (v : Equiv.Perm (Fin (m * n))) (j : ℕ), 0 < j → j ≤ P.J →
      (j : ℝ) ≤ P.δ * (P.f * n) →
      matrixOnesCountInRegion hn
        (semanticExec hn σ1 fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)) P.f = 0 := by
  intro v j hj hjJ hjδ
  have hjmn : j ≤ m * n := by
    have : (P.f : ℝ) * n ≤ m * n := by gcongr
    have hδf : P.δ * (P.f * n) ≤ P.f * n :=
      mul_le_of_le_one_left (by positivity) P.hδ1
    exact_mod_cast (by push_cast; linarith : (j : ℝ) ≤ (m * n : ℕ))
  rw [matrixOnesCountInRegion_semanticExec]
  set c := monotoneColumnSumsOfBool
      ((columnSortNetwork m n hn).exec fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w))
  have htot : totalColumnOnes c = j := sum_topJ_colSums_eq_j hn v j hjmn
  have hjmax : j ≤ P.jmax n := Nat.le_floor hjδ
  refine Finset.sum_eq_zero fun col _ => ?_
  have := round1_le_f_of_SRd P hfm hSR c (by rw [htot]; exact le_min hjJ hjmax) col
  omega

/-- Zero escapes survive any second round. -/
theorem SRd_zero_escapes2 {m n : ℕ} (P : F2PD) (hn : 0 < n) (hfm : P.f ≤ m)
    {σ1 : Scramble m n} (σ2 : Scramble m n) (hSR : SRd P σ1)
    (v : Equiv.Perm (Fin (m * n))) (j : ℕ) (hj : 0 < j) (hjJ : j ≤ P.J)
    (hjδ : (j : ℝ) ≤ P.δ * (P.f * n)) :
    matrixOnesCountInRegion hn
      (semanticExec2 hn σ1 σ2 fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w)) P.f
      = 0 :=
  Nat.eq_zero_of_le_zero
    ((matrixOnesCountInRegion_semanticExec2_le hn σ1 σ2 _ P.f).trans
      (SRd_zero_escapes P hn hfm hSR v j hj hjJ hjδ).le)

/-- **Main deterministic reduction (F2 from SR, R1, R2).** -/
theorem F2_of_SR_R1_R2d {m n : ℕ} (P : F2PD) (hn : 0 < n) (hfm : P.f ≤ m)
    {σ1 σ2 : Scramble m n} (hSR : SRd P σ1) (hR1 : R1d P σ1) (hR2 : R2nd P σ2) :
    HasPackSemanticPropertyF2 hn σ1 σ2 P.f hfm P.δ (1 / (P.J : ℝ)) := by
  intro v j hj hjδ
  have hJ : 0 < P.J := P.hJ
  have hJR : (0 : ℝ) < P.J := by exact_mod_cast hJ
  have hjmn : j ≤ m * n := by
    have : (P.f : ℝ) * n ≤ m * n := by gcongr
    have hδf : P.δ * (P.f * n) ≤ P.f * n :=
      mul_le_of_le_one_left (by positivity) P.hδ1
    exact_mod_cast (by push_cast; linarith : (j : ℝ) ≤ (m * n : ℕ))
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
        rw [hc1]; exact round1_le_f_of_SRd P hfm hSR c (by rw [htot]; exact le_min hsmall hjmax) col
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
    have hqJ : (q - 1) * P.J + P.J = P.J * q := by
      obtain ⟨q', rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ q by omega)
      simp only [Nat.add_sub_cancel_left]; ring
    have hEJ : (q - 1) * P.J ≤ P.jmax n := by omega
    have hlt := escapes_ltd P hfm hR1 hR2 c c1 hc1 q hq2 hEJ hjE
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
theorem F2_flip_paird {m n : ℕ} (P : F2PD) (hn : 0 < n) (hfm : P.f ≤ m)
    {σ1 σ2 : Scramble m n} (hSR : SRd P (flipScramble σ1))
    (hR1 : R1d P (flipScramble σ1)) (hR2 : R2nd P (flipScramble σ2)) :
    HasPackSemanticPropertyF2 hn (flipScramble σ1) (flipScramble σ2) P.f hfm P.δ
      (1 / (P.J : ℝ)) :=
  F2_of_SR_R1_R2d P hn hfm hSR hR1 hR2

/-- Both orientations at once. -/
theorem F2_both_orientationsd {m n : ℕ} (P : F2PD) (hn : 0 < n) (hfm : P.f ≤ m)
    {σ1 σ2 : Scramble m n}
    (h : SRd P σ1 ∧ R1d P σ1 ∧ R2nd P σ2)
    (h' : SRd P (flipScramble σ1) ∧ R1d P (flipScramble σ1) ∧
      R2nd P (flipScramble σ2)) :
    HasPackSemanticPropertyF2 hn σ1 σ2 P.f hfm P.δ (1 / (P.J : ℝ)) ∧
    HasPackSemanticPropertyF2 hn (flipScramble σ1) (flipScramble σ2) P.f hfm P.δ
      (1 / (P.J : ℝ)) :=
  ⟨F2_of_SR_R1_R2d P hn hfm h.1 h.2.1 h.2.2, F2_flip_paird P hn hfm h'.1 h'.2.1 h'.2.2⟩


end Chvatal
