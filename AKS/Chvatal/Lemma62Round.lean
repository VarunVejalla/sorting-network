module

/-
  # Rounding `j` up to a multiple of `1/ε` and summing the geometric series (Lemma 6.2, T3)

  Source: V. Chvátal, DCS-TR-294 (1992), proof of Lemma 6.2.

  * `HasPaperPropertyF`: the corrected Property F (the event class ties `j` to the ones of `c`).
  * `ones_mono` (L1), `exists_extension` (L2): monotonicity and extension of column sums.
  * `round_event` (L3): a bad event at `(c, j)` yields a bad event at `j' = 8·10^7·E`,
    `E = ⌈ε j⌉`, in `badSetF`, with `Lemma62Params`.
  * `paperF_fail_fraction` (L4): union bound over `E ∈ [1, ⌈ε f n⌉]` and the geometric sum
    `∑ (3/10)^E ≤ 3/7`, given the per-`E` failure bound `hfail` as hypothesis.
  * `exists_paperF`: existence of a scramble with the corrected Property F.
-/

public import AKS.Chvatal.Lemma62FailReduce
public import AKS.Chvatal.Lemma62Ratio

@[expose] public section

namespace Chvatal

/-- Corrected paper Property F. -/
def HasPaperPropertyF {m n f : ℕ} (hf : Even f) (σ : Scramble m n) (deltaF epsF : ℝ) : Prop :=
  ∀ (c : MonotoneColumnSums m n) (j : ℕ), totalColumnOnes c = j → 0 < j →
    (j : ℝ) ≤ deltaF * (f * n) →
      ∀ S : Finset (Fin n), ¬ fringeColumnEventBad hf deltaF epsF c σ j S

/-- L1: the fringe count is monotone in the column sums. -/
theorem ones_mono {m n f : ℕ} (hf : Even f) {c c' : MonotoneColumnSums m n}
    (h : ∀ col, c col ≤ c' col) (σ : Scramble m n) (S : Finset (Fin n)) :
    onesAboveHalfFringe hf c σ S ≤ onesAboveHalfFringe hf c' σ S := by
  classical
  unfold onesAboveHalfFringe
  refine Finset.sum_le_sum fun r _ => ?_
  unfold rowHit
  have hsub : monotoneRowOnes c r ⊆ monotoneRowOnes c' r := by
    intro x hx
    simp only [monotoneRowOnes, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans (h x)
  exact Finset.card_le_card
    (Finset.inter_subset_inter (Finset.image_subset_image hsub) subset_rfl)

theorem totalColumnOnes_le {m n : ℕ} (c : MonotoneColumnSums m n) :
    totalColumnOnes c ≤ m * n := by
  unfold totalColumnOnes
  calc ∑ j : Fin n, (c j).val ≤ ∑ _j : Fin n, m :=
        Finset.sum_le_sum fun j _ => Nat.lt_succ_iff.mp (c j).isLt
    _ = m * n := by simp [mul_comm]

/-- L2: extension of a monotone column-sum vector to a larger total. -/
theorem exists_extension {m n : ℕ} :
    ∀ (d : ℕ) (c : MonotoneColumnSums m n), totalColumnOnes c + d ≤ m * n →
      ∃ c' : MonotoneColumnSums m n, (∀ col, c col ≤ c' col) ∧
        totalColumnOnes c' = totalColumnOnes c + d := by
  classical
  intro d
  induction d with
  | zero => intro c _; exact ⟨c, fun _ => le_rfl, by simp⟩
  | succ d ih =>
    intro c hc
    have hex : ∃ col, (c col).val < m := by
      by_contra hno
      push_neg at hno
      have : totalColumnOnes c = m * n := by
        apply le_antisymm (totalColumnOnes_le c)
        calc m * n = ∑ _j : Fin n, m := by simp [mul_comm]
          _ ≤ _ := Finset.sum_le_sum fun j _ => hno j
      omega
    obtain ⟨col, hcol⟩ := hex
    let c1 : MonotoneColumnSums m n := Function.update c col ⟨(c col).val + 1, by omega⟩
    have hc1tot : totalColumnOnes c1 = totalColumnOnes c + 1 := by
      unfold totalColumnOnes
      have h1 := Finset.sum_update_of_mem (Finset.mem_univ col) (fun j => (c j).val)
        ((c col).val + 1)
      have h2 : (∑ j : Fin n, (c1 j).val) =
          ∑ j : Fin n, (Function.update (fun j => (c j).val) col ((c col).val + 1)) j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j = col
        · subst hj; simp [c1]
        · simp [c1, hj]
      rw [h2, h1]
      have h3 := Finset.sum_erase_add Finset.univ (fun j => (c j).val) (Finset.mem_univ col)
      have h4 : (∑ x ∈ Finset.univ \ {col}, (c x).val) =
          ∑ x ∈ Finset.univ.erase col, (c x).val := by
        congr 1; ext x; simp
      rw [h4]; simp only at h3; omega
    have hle1 : ∀ x, c x ≤ c1 x := by
      intro x
      by_cases hx : x = col
      · subst hx; simp [c1, Fin.le_def]
      · simp [c1, hx]
    obtain ⟨c', hc', htot⟩ := ih c1 (by omega)
    exact ⟨c', fun x => (hle1 x).trans (hc' x), by omega⟩

lemma eps_mul_J (E : ℕ) : eps * ((8 * 10 ^ 7 * E : ℕ) : ℝ) = (E : ℝ) := by
  unfold eps; push_cast; field_simp; norm_num

/-- L3: rounding step. -/
theorem round_event {m n f : ℕ} (hf : Even f) (hfm : f ≤ m) (hfbig : 17 * 10 ^ 9 ≤ f)
    (hn : 16 ≤ n) (c : MonotoneColumnSums m n) (σ : Scramble m n) (j : ℕ) (S : Finset (Fin n))
    (htot : totalColumnOnes c = j) (hj0 : 0 < j)
    (hjδ : (j : ℝ) ≤ (128 / 4095 : ℝ) * (f * n))
    (hbad : fringeColumnEventBad hf (128 / 4095) eps c σ j S) :
    ∃ E : ℕ, 1 ≤ E ∧ E ≤ ⌈eps * ((f : ℝ) * n)⌉₊ ∧
      Lemma62Params n (f : ℝ) ((8 * 10 ^ 7 * E : ℕ) : ℝ) ∧
      σ ∈ badSetF (m := m) (n := n) hf (128 / 4095) eps (8 * 10 ^ 7 * E) := by
  classical
  have heps := eps_pos
  have hfR : (17 * 10 ^ 9 : ℝ) ≤ f := by exact_mod_cast hfbig
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hfmR : (f : ℝ) ≤ m := by exact_mod_cast hfm
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj0
  have hfn : (17 * 10 ^ 9 * 16 : ℝ) ≤ f * n := by nlinarith
  set E := ⌈eps * (j : ℝ)⌉₊ with hE
  have hE1 : 1 ≤ E := Nat.one_le_iff_ne_zero.mpr (by
    have := Nat.ceil_pos.mpr (mul_pos heps hjR); omega)
  have hEge : eps * (j : ℝ) ≤ E := Nat.le_ceil _
  have hElt : (E : ℝ) < eps * j + 1 := Nat.ceil_lt_add_one (by positivity)
  have hEK : E ≤ ⌈eps * ((f : ℝ) * n)⌉₊ := by
    apply Nat.ceil_mono
    have : (j : ℝ) ≤ f * n := by nlinarith
    exact mul_le_mul_of_nonneg_left this heps.le
  set j' : ℕ := 8 * 10 ^ 7 * E with hj'
  have hj'R : (j' : ℝ) = 8 * 10 ^ 7 * E := by rw [hj']; push_cast; ring
  have hepsv : eps = 1 / (8 * 10 ^ 7) := rfl
  have hjeq : (j : ℝ) = 8 * 10 ^ 7 * (eps * j) := by rw [hepsv]; field_simp
  have hjj' : (j : ℝ) ≤ j' := by
    rw [hj'R]; nlinarith
  have hj'lt : (j' : ℝ) < j + 8 * 10 ^ 7 := by
    rw [hj'R]; nlinarith
  have hj'f : (j' : ℝ) ≤ f * n / 31 := by nlinarith
  have hj'm : j' ≤ m * n := by
    have : (j' : ℝ) ≤ m * n := by nlinarith
    exact_mod_cast this
  have hjj'N : j ≤ j' := by exact_mod_cast hjj'
  have hj'pos : (0 : ℝ) < j' := hjR.trans_le hjj'
  have hparams : Lemma62Params n (f : ℝ) (j' : ℝ) :=
    ⟨hn, hfR, hj'pos, hj'f⟩
  -- integrality
  unfold fringeColumnEventBad at hbad
  have hf2 : ((f / 2 : ℕ) : ℝ) = (f : ℝ) / 2 := by
    obtain ⟨k, hk⟩ := hf
    subst hk
    push_cast [show (k + k) / 2 = k by omega]; ring
  rw [← hf2] at hbad
  have hbad' : (((f / 2 * S.card : ℕ)) : ℝ) + eps * j ≤ (onesAboveHalfFringe hf c σ S : ℝ) := by
    push_cast; exact hbad
  have hlt : f / 2 * S.card < onesAboveHalfFringe hf c σ S := by
    have : ((f / 2 * S.card : ℕ) : ℝ) < onesAboveHalfFringe hf c σ S := by
      have := mul_pos heps hjR; linarith
    exact_mod_cast this
  have hEN : f / 2 * S.card + E ≤ onesAboveHalfFringe hf c σ S := by
    have h1 : E ≤ onesAboveHalfFringe hf c σ S - f / 2 * S.card := by
      apply Nat.ceil_le.mpr
      rw [Nat.cast_sub hlt.le]; linarith
    omega
  obtain ⟨c', hcc', htot'⟩ := exists_extension (m := m) (n := n) (j' - j) c
    (by rw [htot]; omega)
  rw [htot] at htot'
  have htot'' : totalColumnOnes c' = j' := by omega
  have hmono := ones_mono hf hcc' σ S
  refine ⟨E, hE1, hEK, hparams, ?_⟩
  unfold badSetF
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, c', htot'', S, ?_⟩
  unfold fringeColumnEventBad
  rw [← hf2]
  have h1 : ((f / 2 * S.card + E : ℕ) : ℝ) ≤ (onesAboveHalfFringe hf c' σ S : ℝ) := by
    exact_mod_cast hEN.trans hmono
  have h2 : eps * (j' : ℝ) = E := eps_mul_J E
  push_cast at h1
  rw [h2]; exact h1

lemma geom_Icc (K : ℕ) :
    ∑ E ∈ Finset.Icc 1 K, (3 / 10 : ℝ) ^ E = 3 / 7 - 3 / 7 * (3 / 10 : ℝ) ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]; ring

theorem geom_Icc_le (K : ℕ) : ∑ E ∈ Finset.Icc 1 K, (3 / 10 : ℝ) ^ E ≤ 3 / 7 := by
  rw [geom_Icc]
  have : (0 : ℝ) ≤ (3 / 10 : ℝ) ^ K := by positivity
  linarith

open Classical in
/-- L4: the corrected Property F fails on at most `44%` of scrambles, given per-`E` bounds. -/
theorem paperF_fail_fraction {m n f : ℕ} (hf : Even f) (hfm : f ≤ m) (hfbig : 17 * 10^9 ≤ f)
    (hn : 16 ≤ n)
    (hfail : ∀ (j E : ℕ), 1 ≤ E → (E : ℝ) = eps * j → Lemma62Params n (f : ℝ) (j : ℝ) →
      ((badSetF (m := m) (n := n) hf (128/4095) eps j).card : ℝ) ≤
        1.025 * (3/10 : ℝ)^E * (Fintype.card (Scramble m n) : ℝ)) :
    (((Finset.univ.filter fun σ : Scramble m n =>
        ¬ HasPaperPropertyF hf σ (128/4095) eps).card : ℝ) ≤
      44/100 * (Fintype.card (Scramble m n) : ℝ)) := by
  classical
  set K := ⌈eps * ((f : ℝ) * n)⌉₊
  set I := (Finset.Icc 1 K).filter
    (fun E => Lemma62Params n (f : ℝ) ((8 * 10 ^ 7 * E : ℕ) : ℝ)) with hI
  have hsub : (Finset.univ.filter fun σ : Scramble m n =>
        ¬ HasPaperPropertyF hf σ (128/4095) eps) ⊆
      I.biUnion fun E => badSetF (m := m) (n := n) hf (128/4095) eps (8 * 10 ^ 7 * E) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    unfold HasPaperPropertyF at hσ
    push_neg at hσ
    obtain ⟨c, j, htot, hj0, hjδ, S, hbad⟩ := hσ
    obtain ⟨E, hE1, hEK, hpar, hmem⟩ :=
      round_event hf hfm hfbig hn c σ j S htot hj0 hjδ hbad
    exact Finset.mem_biUnion.mpr ⟨E, by
      rw [hI, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hE1, hEK⟩, hpar⟩, hmem⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hcardR : (((Finset.univ.filter fun σ : Scramble m n =>
        ¬ HasPaperPropertyF hf σ (128/4095) eps).card : ℕ) : ℝ) ≤
      ∑ E ∈ I, ((badSetF (m := m) (n := n) hf (128/4095) eps (8 * 10 ^ 7 * E)).card : ℝ) := by
    exact_mod_cast hcard
  have hterm : ∀ E ∈ I,
      ((badSetF (m := m) (n := n) hf (128/4095) eps (8 * 10 ^ 7 * E)).card : ℝ) ≤
        1.025 * (3/10 : ℝ)^E * (Fintype.card (Scramble m n) : ℝ) := by
    intro E hE
    rw [hI, Finset.mem_filter, Finset.mem_Icc] at hE
    exact hfail _ E hE.1.1 (eps_mul_J E).symm hE.2
  have hsum := hcardR.trans (Finset.sum_le_sum hterm)
  have hIsub : I ⊆ Finset.Icc 1 K := Finset.filter_subset _ _
  have hC : (0 : ℝ) ≤ Fintype.card (Scramble m n) := by positivity
  have hg : ∑ E ∈ I, (3 / 10 : ℝ) ^ E ≤ 3 / 7 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hIsub (fun _ _ _ => by positivity)).trans
      (geom_Icc_le K)
  have : ∑ E ∈ I, 1.025 * (3/10 : ℝ)^E * (Fintype.card (Scramble m n) : ℝ) =
      1.025 * (∑ E ∈ I, (3 / 10 : ℝ) ^ E) * (Fintype.card (Scramble m n) : ℝ) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [this] at hsum
  refine hsum.trans ?_
  have h2 : 1.025 * (∑ E ∈ I, (3 / 10 : ℝ) ^ E) ≤ 44 / 100 := by norm_num at *; linarith
  exact mul_le_mul_of_nonneg_right h2 hC

open Classical in
theorem exists_paperF {m n f : ℕ} (hf : Even f) (hfm : f ≤ m) (hfbig : 17 * 10^9 ≤ f)
    (hn : 16 ≤ n)
    (hfail : ∀ (j E : ℕ), 1 ≤ E → (E : ℝ) = eps * j → Lemma62Params n (f : ℝ) (j : ℝ) →
      ((badSetF (m := m) (n := n) hf (128/4095) eps j).card : ℝ) ≤
        1.025 * (3/10 : ℝ)^E * (Fintype.card (Scramble m n) : ℝ)) :
    ∃ σ : Scramble m n, HasPaperPropertyF hf σ (128/4095) eps := by
  classical
  by_contra hno
  push_neg at hno
  have h := paperF_fail_fraction hf hfm hfbig hn hfail
  have hall : (Finset.univ.filter fun σ : Scramble m n =>
      ¬ HasPaperPropertyF hf σ (128/4095) eps) = Finset.univ := by
    ext σ; simp [hno σ]
  rw [hall, Finset.card_univ] at h
  have hpos : (0 : ℝ) < Fintype.card (Scramble m n) := by
    exact_mod_cast Fintype.card_pos
  linarith

end Chvatal
