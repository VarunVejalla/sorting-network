import AKS.Sub800.F2D
import AKS.Chvatal.F2R1Fail

/-! # R1 failure bounds for `F2PD` (port of the package's `F2R1Fail`, general `c, b, δ`)

The package's analytic per-`E` bounds `R1a_real`/`R1b_real` and union lemmas are reused; the
preconditions that the package stores in `F2Params` are bundled in `F2Pre`, and the `E`-range
cutoff `3·jmax` (from `c = 1/3`) becomes `K·jmax` with `K c ≥ 1`. -/

namespace Chvatal

/-- Preconditions of the two-round contract not stored in `F2PD`. -/
structure F2Pre (P : F2PD) : Prop where
  hD1 : P.δ * P.f ≤ (P.Δ : ℝ) + 1
  hD3 : P.δ * P.f ≤ ((P.g1 : ℝ) + 1) ^ 2
  hcΔ : (P.J : ℝ) / ((P.g1 : ℝ) + 1) ≤ P.c * (P.Δ : ℝ)
  hbJ : (P.J : ℝ) / ((P.g1 : ℝ) + 1) ≤ P.b
  hf16 : 1 ≤ P.δ * P.f * 16
  hcb : P.c + 1 / 2 ≤ P.b
  hc2 : P.c ≤ 1 / 2
  hb1 : 1 ≤ P.b

theorem jE_factsd (P : F2PD) (H : F2Pre P) {n : ℕ} (hn : 16 ≤ n) {E : ℕ} (hE : 2 ≤ E) :
    1 ≤ P.jE n E ∧ ((P.jE n E : ℕ) : ℝ) ≤ P.δ * P.f * n ∧
      ((P.jE n E : ℕ) : ℝ) ≤ E * P.J ∧ P.jE n E ≤ P.jmax n := by
  have hn' : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hjm1 : 1 ≤ P.jmax n := by
    unfold F2PD.jmax
    refine Nat.le_floor ?_
    push_cast
    have h0 : 0 ≤ P.δ * P.f := mul_nonneg P.hδ.le (Nat.cast_nonneg _)
    have := H.hf16
    nlinarith
  have hjmD : (P.jmax n : ℝ) ≤ P.δ * P.f * n := by
    unfold F2PD.jmax
    calc _ ≤ P.δ * (P.f * n) := Nat.floor_le (by have := P.hδ; positivity)
      _ = _ := by ring
  have hEJ : 1 ≤ E * P.J := by
    have := P.hJ
    nlinarith
  refine ⟨?_, ?_, ?_, min_le_right _ _⟩
  · unfold F2PD.jE; exact le_min hEJ hjm1
  · exact (Nat.cast_le.mpr (min_le_right _ _)).trans hjmD
  · have : P.jE n E ≤ E * P.J := min_le_left _ _
    exact_mod_cast this

/-- Numeric hypotheses for R1(a). -/
def R1aNumd (P : F2PD) : Prop :=
  (P.J : ℝ) / ((P.g1 : ℝ) + 1) ≤ 1641 ∧
  0 ≤ ((P.Δ : ℝ) + 1) * (Real.log ((P.Δ : ℝ) + 1) - 1) - 1 - Real.log ((P.J : ℝ) / P.c)
      - (P.Δ : ℝ) * Real.log (P.δ * P.f) ∧
  (P.J : ℝ) / ((P.g1 : ℝ) + 1) *
      (2 + 2 * Real.log ((P.g1 : ℝ) + 1) - Real.log (P.δ * P.f)) -
    P.c * (((P.Δ : ℝ) + 1) * (Real.log ((P.Δ : ℝ) + 1) - 1) - 1 - Real.log ((P.J : ℝ) / P.c)
      - (P.Δ : ℝ) * Real.log (P.δ * P.f)) ≤ -15

/-- Numeric hypotheses for R1(b). -/
def R1bNumd (P : F2PD) : Prop :=
  (P.J : ℝ) / ((P.g1 : ℝ) + 1) ≤ 1641 ∧
  1 + Real.log (P.J : ℝ) + (P.Δ : ℝ) * (1 - Real.log (P.Δ : ℝ)) +
      (1 - (P.Δ : ℝ)) * (-Real.log (P.δ * P.f)) ≤ 0 ∧
  (P.J : ℝ) / ((P.g1 : ℝ) + 1) *
      (2 + 2 * Real.log ((P.g1 : ℝ) + 1) - Real.log (P.δ * P.f)) +
    P.b * (1 + Real.log (P.δ * P.f) - Real.log (P.Δ : ℝ)) ≤ -22

lemma log_D_led (P : F2PD) (H : F2Pre P) :
    0 ≤ 2 + 2 * Real.log ((P.g1 : ℝ) + 1) - Real.log (P.δ * P.f) := by
  have hf : (0 : ℝ) < P.f := by
    have : 0 < P.f := by have := P.hg2f; have := P.hg12; have := P.hg1; omega
    exact_mod_cast this
  have hD0 : (0 : ℝ) < P.δ * P.f := by have := P.hδ; positivity
  have h := Real.log_le_log hD0 H.hD3
  rw [Real.log_pow] at h
  push_cast at h
  linarith

set_option maxHeartbeats 1600000 in
/-- Probability of the R1(a) event at a fixed `E`. -/
theorem R1a_event_card_led (P : F2PD) (H : F2Pre P) (hnum : R1aNumd P)
    {m n : ℕ} (hn : 16 ≤ n) {E : ℕ} (hE : 2 ≤ E) :
    ((Finset.univ.filter fun σ : Scramble m n => ∃ c : MonotoneColumnSums m n,
        totalColumnOnes c ≤ P.jE n E ∧ ∃ S : Finset (Fin n), S.card = P.κ E + 1 ∧
          (P.Δ + 1) * (P.κ E + 1) ≤ onesInRows c σ (topRows m P.g1) S).card : ℝ) ≤
      Real.exp (-10 * E) * Fintype.card (Scramble m n) := by
  classical
  have hn0 : 0 < n := by omega
  obtain ⟨hj1, hjD, hjE, -⟩ := jE_factsd P H hn hE
  obtain ⟨hα, h2, h3⟩ := hnum
  set j := P.jE n E with hjdef
  set s := P.κ E + 1 with hsdef
  have hs1 : 1 ≤ s := by omega
  have hs0 : 0 < s := hs1
  have hsE : P.c * E + 1 ≤ (s : ℝ) := by
    have := Nat.le_ceil (P.c * E)
    simp only [hsdef, F2PD.κ]; push_cast; linarith
  set T : ℕ := (P.Δ + 1) * s with hT
  set Ev : MonotoneColumnSums m n → Finset (Scramble m n) :=
    fun c => tailBadSet c (topRows m P.g1) s (T : ℝ) with hEv
  have hsub : (Finset.univ.filter fun σ : Scramble m n => ∃ c : MonotoneColumnSums m n,
        totalColumnOnes c ≤ j ∧ ∃ S : Finset (Fin n), S.card = s ∧
          (P.Δ + 1) * s ≤ onesInRows c σ (topRows m P.g1) S) ⊆
      Finset.univ.filter fun σ : Scramble m n => ∃ c, totalColumnOnes c ≤ j ∧ σ ∈ Ev c := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    obtain ⟨c, hc1, S, hS, hS2⟩ := hσ
    refine ⟨c, hc1, ?_⟩
    simp only [hEv, tailBadSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩, ?_⟩
    rw [hT]; exact_mod_cast hS2
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  have hn0r : (0 : ℝ) < n := by exact_mod_cast hn0
  have hs0r : (0 : ℝ) < s := by exact_mod_cast hs0
  have hD1 : P.δ * P.f ≤ (P.Δ : ℝ) + 1 := H.hD1
  have hjn : (j : ℝ) / n ≤ (P.Δ : ℝ) + 1 := by
    rw [div_le_iff₀ hn0r]; nlinarith
  have hTr : (T : ℝ) = ((P.Δ : ℝ) + 1) * s := by rw [hT]; push_cast; ring
  have hB : ∀ c : MonotoneColumnSums m n, totalColumnOnes c ≤ j →
      ((Ev c).card : ℝ) ≤
        ((n.choose s : ℝ) * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ)) *
          Fintype.card (Scramble m n) := by
    intro c hcj
    refine tail_union_le hn0 c P.g1 s (j : ℝ) (T : ℝ) hjpos (by exact_mod_cast hcj) hs0 ?_
    have h := (div_le_iff₀ hn0r).mp hjn
    rw [hTr, div_le_iff₀ hn0r]
    nlinarith [mul_le_mul_of_nonneg_right h hs0r.le]
  have hBnn : (0 : ℝ) ≤ (n.choose s : ℝ) * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ) := by
    positivity
  have hmain := bad_card_le_tops (m := m) (n := n) P.g1 j Ev _ hBnn
    (fun c c' h => tailBadSet_eq_of_top c c' h s (T : ℝ)) hB
  have hjg : j ≤ (P.g1 + 1) ^ 2 * n := by
    have h1 : (j : ℝ) ≤ ((P.g1 : ℝ) + 1) ^ 2 * n := by
      have := H.hD3
      calc (j : ℝ) ≤ P.δ * P.f * n := hjD
        _ ≤ _ := mul_le_mul_of_nonneg_right this hn0r.le
    exact_mod_cast h1
  have htops := tops_card_le_gen P.g1 n j hn0 hj1 hjg
  have hchoose : (n.choose s : ℝ) ≤ (Real.exp 1 * n / s) ^ s := choose_le_exp_pow n hs1
  have hreal := R1a_real (n := n) (j := j) (s := s) (E := E) (G := (P.g1 : ℝ) + 1)
    (Dl := (P.Δ : ℝ)) (D := P.δ * P.f) (J := (P.J : ℝ)) (c := P.c)
    hn0 hj1 hjD hjE hs1 hsE (by positivity) (by exact_mod_cast (show 0 < P.Δ from by
      unfold F2PD.Δ; have := P.hg12; omega))
    (by have : (0 : ℝ) < P.f := by exact_mod_cast (by have := P.hg2f; omega : 0 < P.f)
        have := P.hδ; positivity)
    (by exact_mod_cast P.hJ) P.hc0 H.hcΔ hα (log_D_led P H) h2 h3 hE
  have hAnn : 0 ≤ ((j : ℝ) / ((P.g1 : ℝ) + 1) + 1) *
      (Real.exp 1 ^ 2 * n * ((P.g1 : ℝ) + 1) ^ 2 / j) ^ ((j : ℝ) / ((P.g1 : ℝ) + 1)) := by
    positivity
  have hZnn : 0 ≤ (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ) := by positivity
  have hScr : (0 : ℝ) ≤ Fintype.card (Scramble m n) := Nat.cast_nonneg _
  calc _ ≤ ((Finset.univ.filter fun σ : Scramble m n =>
          ∃ c, totalColumnOnes c ≤ j ∧ σ ∈ Ev c).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := hmain
    _ ≤ (((j : ℝ) / ((P.g1 : ℝ) + 1) + 1) *
        (Real.exp 1 ^ 2 * n * ((P.g1 : ℝ) + 1) ^ 2 / j) ^ ((j : ℝ) / ((P.g1 : ℝ) + 1)) *
          ((n.choose s : ℝ) * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ))) *
          Fintype.card (Scramble m n) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htops hBnn) hScr
    _ ≤ (((j : ℝ) / ((P.g1 : ℝ) + 1) + 1) *
        (Real.exp 1 ^ 2 * n * ((P.g1 : ℝ) + 1) ^ 2 / j) ^ ((j : ℝ) / ((P.g1 : ℝ) + 1)) *
          ((Real.exp 1 * n / s) ^ s * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ))) *
          Fintype.card (Scramble m n) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hchoose hZnn) hAnn) hScr
    _ = (((j : ℝ) / ((P.g1 : ℝ) + 1) + 1) *
        (Real.exp 1 ^ 2 * n * ((P.g1 : ℝ) + 1) ^ 2 / j) ^ ((j : ℝ) / ((P.g1 : ℝ) + 1)) *
          (Real.exp 1 * n / s) ^ s * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ)) *
          Fintype.card (Scramble m n) := by ring
    _ ≤ Real.exp (-10 * E) * Fintype.card (Scramble m n) := by
        refine mul_le_mul_of_nonneg_right ?_ hScr
        rw [hTr]; exact hreal

set_option maxHeartbeats 1600000 in
/-- Probability of the R1(b) event at a fixed `E`. -/
theorem R1b_event_card_led (P : F2PD) (H : F2Pre P) (hnum : R1bNumd P)
    {m n : ℕ} (hn : 16 ≤ n) {E : ℕ} (hE : 2 ≤ E) :
    ((Finset.univ.filter fun σ : Scramble m n => ∃ c : MonotoneColumnSums m n,
        totalColumnOnes c ≤ P.jE n E ∧ ∃ S : Finset (Fin n), 1 ≤ S.card ∧ S.card ≤ P.κ E ∧
          P.Δ * S.card + P.B E ≤ onesInRows c σ (topRows m P.g1) S).card : ℝ) ≤
      Real.exp (-10 * E) * Fintype.card (Scramble m n) := by
  classical
  have hn0 : 0 < n := by omega
  obtain ⟨hj1, hjD, hjE, -⟩ := jE_factsd P H hn hE
  obtain ⟨hα, hRs, hNb⟩ := hnum
  have hE2 : (2 : ℝ) ≤ E := by exact_mod_cast hE
  set j := P.jE n E with hjdef
  set κ := P.κ E with hκ
  have hκE : (κ : ℝ) < P.c * E + 1 := by
    simp only [hκ, F2PD.κ]; exact Nat.ceil_lt_add_one (by have := P.hc0; positivity)
  have hκB : κ ≤ P.B E := by
    simp only [hκ, F2PD.κ, F2PD.B]
    exact Nat.ceil_mono (by have := H.hcb; have : (0 : ℝ) ≤ E := Nat.cast_nonneg _; nlinarith)
  have hBr : P.b * E ≤ (P.B E : ℝ) := Nat.le_ceil _
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  have hn0r : (0 : ℝ) < n := by exact_mod_cast hn0
  have hD1 : P.δ * P.f ≤ (P.Δ : ℝ) + 1 := H.hD1
  have hjn : (j : ℝ) / n ≤ (P.Δ : ℝ) + 1 := by
    rw [div_le_iff₀ hn0r]; nlinarith
  have hjn' := (div_le_iff₀ hn0r).mp hjn
  have hjg : j ≤ (P.g1 + 1) ^ 2 * n := by
    have h1 : (j : ℝ) ≤ ((P.g1 : ℝ) + 1) ^ 2 * n := by
      have := H.hD3
      calc (j : ℝ) ≤ P.δ * P.f * n := hjD
        _ ≤ _ := mul_le_mul_of_nonneg_right this hn0r.le
    exact_mod_cast h1
  have htops := tops_card_le_gen P.g1 n j hn0 hj1 hjg
  have hScr : (0 : ℝ) ≤ Fintype.card (Scramble m n) := Nat.cast_nonneg _
  have hper : ∀ s ∈ Finset.Icc 1 κ,
      ((Finset.univ.filter fun σ : Scramble m n => ∃ c : MonotoneColumnSums m n,
        totalColumnOnes c ≤ j ∧ σ ∈ tailBadSet c (topRows m P.g1) s
          ((P.Δ * s + P.B E : ℕ) : ℝ)).card : ℝ) ≤
        Real.exp (-16 * E) * Fintype.card (Scramble m n) := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    obtain ⟨hs1, hsκ⟩ := hs
    have hs0 : 0 < s := hs1
    have hs0r : (0 : ℝ) < s := by exact_mod_cast hs0
    have hsB : s ≤ P.B E := hsκ.trans hκB
    have hsb : (s : ℝ) ≤ P.b * E := by
      have : (s : ℝ) ≤ κ := by exact_mod_cast hsκ
      have := H.hcb; nlinarith
    set T : ℕ := P.Δ * s + P.B E with hT
    have hTr : (T : ℝ) = (P.Δ : ℝ) * s + (P.B E : ℝ) := by rw [hT]; push_cast; ring
    have hB : ∀ c : MonotoneColumnSums m n, totalColumnOnes c ≤ j →
        ((tailBadSet c (topRows m P.g1) s (T : ℝ)).card : ℝ) ≤
          ((n.choose s : ℝ) * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ)) *
            Fintype.card (Scramble m n) := by
      intro c hcj
      refine tail_union_le hn0 c P.g1 s (j : ℝ) (T : ℝ) hjpos (by exact_mod_cast hcj) hs0 ?_
      have hsBr : (s : ℝ) ≤ (P.B E : ℝ) := by exact_mod_cast hsB
      rw [hTr, div_le_iff₀ hn0r]
      nlinarith [mul_le_mul_of_nonneg_right hjn' hs0r.le]
    have hBnn : (0 : ℝ) ≤ (n.choose s : ℝ) * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ) := by
      positivity
    have hmain := bad_card_le_tops (m := m) (n := n) P.g1 j
      (fun c => tailBadSet c (topRows m P.g1) s (T : ℝ)) _ hBnn
      (fun c c' h => tailBadSet_eq_of_top c c' h s (T : ℝ)) hB
    have hchoose : (n.choose s : ℝ) ≤ (Real.exp 1 * n / s) ^ s := choose_le_exp_pow n hs1
    have hreal := R1b_real (n := n) (j := j) (s := s) (E := E) (G := (P.g1 : ℝ) + 1)
      (Dl := (P.Δ : ℝ)) (D := P.δ * P.f) (J := (P.J : ℝ)) (bb := P.b)
      (Bn := (P.B E : ℝ))
      hn0 hj1 hjD hjE hs1 hsb hBr (by positivity)
      (by exact_mod_cast (show 1 ≤ P.Δ from by
        unfold F2PD.Δ; have := P.hg12; omega))
      (by have : (0 : ℝ) < P.f := by exact_mod_cast (by have := P.hg2f; omega : 0 < P.f)
          have := P.hδ; positivity)
      hD1 (by exact_mod_cast P.hJ) P.hb0 H.hbJ hα (log_D_led P H) hRs hNb hE
    have hAnn : 0 ≤ ((j : ℝ) / ((P.g1 : ℝ) + 1) + 1) *
        (Real.exp 1 ^ 2 * n * ((P.g1 : ℝ) + 1) ^ 2 / j) ^ ((j : ℝ) / ((P.g1 : ℝ) + 1)) := by
      positivity
    have hZnn : 0 ≤ (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ) := by positivity
    calc _ ≤ _ := hmain
      _ ≤ (((j : ℝ) / ((P.g1 : ℝ) + 1) + 1) *
          (Real.exp 1 ^ 2 * n * ((P.g1 : ℝ) + 1) ^ 2 / j) ^ ((j : ℝ) / ((P.g1 : ℝ) + 1)) *
            ((n.choose s : ℝ) * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ))) *
            Fintype.card (Scramble m n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htops hBnn) hScr
      _ ≤ (((j : ℝ) / ((P.g1 : ℝ) + 1) + 1) *
          (Real.exp 1 ^ 2 * n * ((P.g1 : ℝ) + 1) ^ 2 / j) ^ ((j : ℝ) / ((P.g1 : ℝ) + 1)) *
            ((Real.exp 1 * n / s) ^ s * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ))) *
            Fintype.card (Scramble m n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hchoose hZnn) hAnn) hScr
      _ = (((j : ℝ) / ((P.g1 : ℝ) + 1) + 1) *
          (Real.exp 1 ^ 2 * n * ((P.g1 : ℝ) + 1) ^ 2 / j) ^ ((j : ℝ) / ((P.g1 : ℝ) + 1)) *
            (Real.exp 1 * n / s) ^ s * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ)) *
            Fintype.card (Scramble m n) := by ring
      _ ≤ Real.exp (-16 * E) * Fintype.card (Scramble m n) := by
          refine mul_le_mul_of_nonneg_right ?_ hScr
          rw [hTr]; exact hreal
  have hsub : (Finset.univ.filter fun σ : Scramble m n => ∃ c : MonotoneColumnSums m n,
        totalColumnOnes c ≤ j ∧ ∃ S : Finset (Fin n), 1 ≤ S.card ∧ S.card ≤ κ ∧
          P.Δ * S.card + P.B E ≤ onesInRows c σ (topRows m P.g1) S) ⊆
      (Finset.Icc 1 κ).biUnion fun s => Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ j ∧ σ ∈ tailBadSet c (topRows m P.g1) s
          ((P.Δ * s + P.B E : ℕ) : ℝ) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨c, hc1, S, hS1, hS2, hS3⟩ := hσ
    refine Finset.mem_biUnion.mpr ⟨S.card, Finset.mem_Icc.mpr ⟨hS1, hS2⟩, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨c, hc1, ?_⟩
    simp only [tailBadSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩, by exact_mod_cast hS3⟩
  have hκ_le : (κ : ℝ) ≤ E := by have := H.hc2; nlinarith
  have hexpE : (E : ℝ) ≤ Real.exp (6 * E) := by
    have := Real.add_one_le_exp (6 * (E : ℝ))
    linarith
  calc _ ≤ (((Finset.Icc 1 κ).biUnion fun s => Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ j ∧ σ ∈ tailBadSet c (topRows m P.g1) s
          ((P.Δ * s + P.B E : ℕ) : ℝ)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ s ∈ Finset.Icc 1 κ, ((Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ j ∧ σ ∈ tailBadSet c (topRows m P.g1) s
          ((P.Δ * s + P.B E : ℕ) : ℝ)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ s ∈ Finset.Icc 1 κ, Real.exp (-16 * E) * Fintype.card (Scramble m n) :=
        Finset.sum_le_sum hper
    _ = κ * (Real.exp (-16 * E) * Fintype.card (Scramble m n)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    _ ≤ E * (Real.exp (-16 * E) * Fintype.card (Scramble m n)) :=
        mul_le_mul_of_nonneg_right hκ_le (by positivity)
    _ ≤ Real.exp (6 * E) * (Real.exp (-16 * E) * Fintype.card (Scramble m n)) :=
        mul_le_mul_of_nonneg_right hexpE (by positivity)
    _ = Real.exp (-10 * E) * Fintype.card (Scramble m n) := by
        rw [← mul_assoc, ← Real.exp_add]; ring_nf

/-! ## Part 4: summing over `E` -/

open Classical in
theorem F2R1a_faild (P : F2PD) (H : F2Pre P) (K : ℕ) (hK : 1 ≤ (K : ℝ) * P.c) (hnum : R1aNumd P)
    {m n : ℕ} (hn : 16 ≤ n) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ R1ad P σ).card : ℝ) ≤
      (1 / 20000) * Fintype.card (Scramble m n) := by
  classical
  have hsub : (Finset.univ.filter fun σ : Scramble m n => ¬ R1ad P σ) ⊆
      (Finset.Ico 2 (K * P.jmax n)).biUnion fun E => Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ P.jE n E ∧
          ∃ S : Finset (Fin n), S.card = P.κ E + 1 ∧
            (P.Δ + 1) * (P.κ E + 1) ≤ onesInRows c σ (topRows m P.g1) S := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, R1ad] at hσ
    push_neg at hσ
    obtain ⟨E, hE, c, hcj, S, hS, hS2⟩ := hσ
    refine Finset.mem_biUnion.mpr ⟨E, Finset.mem_Ico.mpr ⟨hE, ?_⟩, ?_⟩
    · by_contra hlt
      push_neg at hlt
      obtain ⟨hj1, -, -, hjm⟩ := jE_factsd P H hn hE
      have hκ : P.jmax n ≤ P.κ E := by
        have : (P.jmax n : ℝ) ≤ P.κ E := by
          have h1 : (K * P.jmax n : ℝ) ≤ E := by exact_mod_cast hlt
          have h2 : P.c * E ≤ (P.κ E : ℝ) := Nat.le_ceil _
          have h3 := mul_le_mul_of_nonneg_left h1 P.hc0.le
          have h4 := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg (P.jmax n))
          nlinarith
        exact_mod_cast this
      have h3 : onesInRows c σ (topRows m P.g1) S ≤ P.jmax n :=
        (onesInRows_le_total _ _ _ _).trans (hcj.trans hjm)
      have h4 : P.κ E + 1 ≤ (P.Δ + 1) * (P.κ E + 1) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨c, hcj, S, hS, hS2⟩
  have hScr : (0 : ℝ) ≤ Fintype.card (Scramble m n) := Nat.cast_nonneg _
  calc _ ≤ (((Finset.Ico 2 (K * P.jmax n)).biUnion fun E =>
        Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ P.jE n E ∧
          ∃ S : Finset (Fin n), S.card = P.κ E + 1 ∧
            (P.Δ + 1) * (P.κ E + 1) ≤ onesInRows c σ (topRows m P.g1) S).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ E ∈ Finset.Ico 2 (K * P.jmax n), ((Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ P.jE n E ∧
          ∃ S : Finset (Fin n), S.card = P.κ E + 1 ∧
            (P.Δ + 1) * (P.κ E + 1) ≤ onesInRows c σ (topRows m P.g1) S).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ E ∈ Finset.Ico 2 (K * P.jmax n), Real.exp (-10 * (E : ℝ)) *
          Fintype.card (Scramble m n) :=
        Finset.sum_le_sum fun E hE =>
          R1a_event_card_led P H hnum hn (Finset.mem_Ico.mp hE).1
    _ = (∑ E ∈ Finset.Ico 2 (K * P.jmax n), Real.exp (-10 * (E : ℝ))) *
          Fintype.card (Scramble m n) := by rw [Finset.sum_mul]
    _ ≤ (1 / 20000) * Fintype.card (Scramble m n) :=
        mul_le_mul_of_nonneg_right (sum_exp_Ico_le _) hScr

open Classical in
theorem F2R1b_faild (P : F2PD) (H : F2Pre P) (K : ℕ) (hK1 : 1 ≤ K)
    (hnum : R1bNumd P) {m n : ℕ} (hn : 16 ≤ n) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ R1bd P σ).card : ℝ) ≤
      (1 / 20000) * Fintype.card (Scramble m n) := by
  classical
  have hsub : (Finset.univ.filter fun σ : Scramble m n => ¬ R1bd P σ) ⊆
      (Finset.Ico 2 (K * P.jmax n)).biUnion fun E => Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ P.jE n E ∧
          ∃ S : Finset (Fin n), 1 ≤ S.card ∧ S.card ≤ P.κ E ∧
            P.Δ * S.card + P.B E ≤ onesInRows c σ (topRows m P.g1) S := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, R1bd] at hσ
    push_neg at hσ
    obtain ⟨E, hE, c, hcj, S, hS1, hS2, hS3⟩ := hσ
    refine Finset.mem_biUnion.mpr ⟨E, Finset.mem_Ico.mpr ⟨hE, ?_⟩, ?_⟩
    · by_contra hlt
      push_neg at hlt
      obtain ⟨hj1, -, -, hjm⟩ := jE_factsd P H hn hE
      have hB : K * P.jmax n ≤ P.B E := by
        have h1 : (K * P.jmax n : ℝ) ≤ E := by exact_mod_cast hlt
        have h2 : P.b * E ≤ (P.B E : ℝ) := Nat.le_ceil _
        have h3 : (E : ℝ) ≤ P.b * E := by have := H.hb1; nlinarith
        exact_mod_cast h1.trans (h3.trans h2)
      have h3 : onesInRows c σ (topRows m P.g1) S ≤ P.jmax n :=
        (onesInRows_le_total _ _ _ _).trans (hcj.trans hjm)
      have := Nat.le_mul_of_pos_left (P.jmax n) hK1
      have : 1 ≤ P.Δ * S.card := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by unfold F2PD.Δ; have := P.hg12; omega) (by omega))
      omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨c, hcj, S, hS1, hS2, hS3⟩
  have hScr : (0 : ℝ) ≤ Fintype.card (Scramble m n) := Nat.cast_nonneg _
  calc _ ≤ (((Finset.Ico 2 (K * P.jmax n)).biUnion fun E =>
        Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ P.jE n E ∧
          ∃ S : Finset (Fin n), 1 ≤ S.card ∧ S.card ≤ P.κ E ∧
            P.Δ * S.card + P.B E ≤ onesInRows c σ (topRows m P.g1) S).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ E ∈ Finset.Ico 2 (K * P.jmax n), ((Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ P.jE n E ∧
          ∃ S : Finset (Fin n), 1 ≤ S.card ∧ S.card ≤ P.κ E ∧
            P.Δ * S.card + P.B E ≤ onesInRows c σ (topRows m P.g1) S).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ E ∈ Finset.Ico 2 (K * P.jmax n), Real.exp (-10 * (E : ℝ)) *
          Fintype.card (Scramble m n) :=
        Finset.sum_le_sum fun E hE =>
          R1b_event_card_led P H hnum hn (Finset.mem_Ico.mp hE).1
    _ = (∑ E ∈ Finset.Ico 2 (K * P.jmax n), Real.exp (-10 * (E : ℝ))) *
          Fintype.card (Scramble m n) := by rw [Finset.sum_mul]
    _ ≤ (1 / 20000) * Fintype.card (Scramble m n) :=
        mul_le_mul_of_nonneg_right (sum_exp_Ico_le _) hScr

open Classical in
/-- Assembly, given the numeric hypotheses. -/
theorem F2R1_faild (P : F2PD) (H : F2Pre P) (K : ℕ) (hK1 : 1 ≤ K)
    (hK : 1 ≤ (K : ℝ) * P.c) (ha : R1aNumd P) (hbn : R1bNumd P) {m n : ℕ} (hn : 16 ≤ n) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ R1d P σ).card : ℝ) ≤
      (1 / 10000) * Fintype.card (Scramble m n) := by
  classical
  have hsub : (Finset.univ.filter fun σ : Scramble m n => ¬ R1d P σ) ⊆
      (Finset.univ.filter fun σ : Scramble m n => ¬ R1ad P σ) ∪
        (Finset.univ.filter fun σ : Scramble m n => ¬ R1bd P σ) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, R1d] at hσ ⊢
    by_contra h
    push_neg at h
    exact hσ ⟨h.1, h.2⟩
  have h1 := F2R1a_faild P H K hK ha (m := m) hn
  have h2 := F2R1b_faild P H K hK1 hbn (m := m) hn
  have h3 : (((Finset.univ.filter fun σ : Scramble m n => ¬ R1d P σ)).card : ℝ) ≤
      ((Finset.univ.filter fun σ : Scramble m n => ¬ R1ad P σ).card : ℝ) +
        ((Finset.univ.filter fun σ : Scramble m n => ¬ R1bd P σ).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  linarith


end Chvatal
