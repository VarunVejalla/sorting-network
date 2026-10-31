import AKS.Sub800.F2DSR

/-! Lean-checked local-dimension bridge for the ragged 13-bit F2 screen.
This is scratch outside `upper-bound/best`; it checks the scalar preconditions,
the actual positive rank cap at n = 8307, and the resulting generic jE facts. -/

namespace Chvatal.RaggedF2Local

open Real
open scoped Classical

noncomputable def P14 : F2PD where
  f := 14
  g1 := 7
  g2 := 9
  J := 1
  c := 1 / 3
  b := 6 / 5
  δ := 18 / (14 * 8307)
  hg1 := by norm_num
  hg12 := by norm_num
  hg2f := by norm_num
  hJ := by norm_num
  hc0 := by norm_num
  hb0 := by norm_num
  hδ := by norm_num
  hδ1 := by norm_num

noncomputable def P15 : F2PD where
  f := 15
  g1 := 8
  g2 := 10
  J := 1
  c := 1 / 3
  b := 6 / 5
  δ := 18 / (15 * 8307)
  hg1 := by norm_num
  hg12 := by norm_num
  hg2f := by norm_num
  hJ := by norm_num
  hc0 := by norm_num
  hb0 := by norm_num
  hδ := by norm_num
  hδ1 := by norm_num

/-- The f=13, epsilonF=1/3 probability point used by the ragged waterfill
candidate at its proposed minimum local dimension 3832. -/
noncomputable def P13J3 : F2PD where
  f := 13
  g1 := 3
  g2 := 7
  J := 3
  c := 2 / 5
  b := 2
  δ := 18 / (13 * 3832)
  hg1 := by norm_num
  hg12 := by norm_num
  hg2f := by norm_num
  hJ := by norm_num
  hc0 := by norm_num
  hb0 := by norm_num
  hδ := by norm_num
  hδ1 := by norm_num


/-- All scalar F2Pre inequalities except its uniform-in-n `hf16` guard. -/
def LocalPre (P : F2PD) : Prop :=
  P.δ * P.f ≤ (P.Δ : ℝ) + 1 ∧
  P.δ * P.f ≤ ((P.g1 : ℝ) + 1) ^ 2 ∧
  (P.J : ℝ) / ((P.g1 : ℝ) + 1) ≤ P.c * (P.Δ : ℝ) ∧
  (P.J : ℝ) / ((P.g1 : ℝ) + 1) ≤ P.b ∧
  P.c + 1 / 2 ≤ P.b ∧ P.c ≤ 1 / 2 ∧ 1 ≤ P.b

theorem pre14 : LocalPre P14 := by
  norm_num [LocalPre, P14, F2PD.Δ]

theorem pre15 : LocalPre P15 := by
  norm_num [LocalPre, P15, F2PD.Δ]

theorem pre13J3 : LocalPre P13J3 := by
  norm_num [LocalPre, P13J3, F2PD.Δ]

theorem positive_rank14 : (1 : ℕ) ≤ P14.jmax 8307 := by
  unfold F2PD.jmax
  apply Nat.floor_pos.mpr
  norm_num [P14]
  exact le_of_lt (by norm_num : (1 : ℝ) < 18)

theorem positive_rank15 : (1 : ℕ) ≤ P15.jmax 8307 := by
  unfold F2PD.jmax
  apply Nat.floor_pos.mpr
  norm_num [P15]
  exact le_of_lt (by norm_num : (1 : ℝ) < 18)

theorem hf16_fails14 : ¬ 1 ≤ P14.δ * P14.f * 16 := by
  norm_num [P14]

theorem hf16_fails15 : ¬ 1 ≤ P15.δ * P15.f * 16 := by
  norm_num [P15]

theorem hf16_fails13J3 : ¬ 1 ≤ P13J3.δ * P13J3.f * 16 := by
  norm_num [P13J3]

theorem local_rank_positive13J3 : 1 ≤ P13J3.jmax 3832 := by
  unfold F2PD.jmax
  apply Nat.floor_pos.mpr
  norm_num [P13J3]
  exact le_of_lt (by norm_num : (1 : ℝ) < 18)

/-- The rank cap stays positive for every ragged-provider column count above
the all-depth geometric threshold. -/
theorem local_rank_positive13J3_of_lower_bound {n : ℕ} (hn : 3832 ≤ n) :
    1 ≤ P13J3.jmax n := by
  unfold F2PD.jmax
  apply Nat.floor_pos.mpr
  have hnR : (3832 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num [P13J3]
  nlinarith

/-- The `jE_factsd` bounds localized to a concrete dimension.  The old
uniform `hf16` condition is replaced by the actual rank-positivity fact. -/
theorem jE_factsd_local (P : F2PD) {n : ℕ}
    (hRank : 1 ≤ P.jmax n) {E : ℕ} (hE : 2 ≤ E) :
    1 ≤ P.jE n E ∧ ((P.jE n E : ℕ) : ℝ) ≤ P.δ * P.f * n ∧
      ((P.jE n E : ℕ) : ℝ) ≤ E * P.J ∧ P.jE n E ≤ P.jmax n := by
  have hjmD : (P.jmax n : ℝ) ≤ P.δ * P.f * n := by
    unfold F2PD.jmax
    calc _ ≤ P.δ * (P.f * n) := Nat.floor_le (by have := P.hδ; positivity)
      _ = _ := by ring
  have hEJ : 1 ≤ E * P.J := by
    have := P.hJ
    nlinarith
  refine ⟨?_, ?_, ?_, min_le_right _ _⟩
  · unfold F2PD.jE
    exact_mod_cast le_min hEJ hRank
  · have hmin : P.jE n E ≤ P.jmax n := min_le_right _ _
    exact (Nat.cast_le.mpr hmin).trans hjmD
  · have hmin : P.jE n E ≤ E * P.J := min_le_left _ _
    exact_mod_cast hmin

/-- The exponent called `beta` in the aggregate R1(a) screen is exactly the
negative of the `Q0` term in the existing per-E analytic proof. This identity
is the algebraic bridge needed to retain the geometric-sum factor instead of
forcing the old `exp(-10 E)` pointwise bound. -/
theorem r1a_beta_eq_neg_Q0 {Dl D J c : ℝ}
    (hDl : 0 < Dl) (hD : 0 < D) (hJ : 0 < J) (hc : 0 < c) :
    Real.log (Real.exp 1 * J / (c * D)) +
        (Dl + 1) * Real.log (Real.exp 1 * D / (Dl + 1)) =
      -((Dl + 1) * (Real.log (Dl + 1) - 1) - 1 - Real.log (J / c) -
        Dl * Real.log D) := by
  have hDl1 : 0 < Dl + 1 := by linarith
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (Real.exp_pos 1).ne' hJ.ne', Real.log_exp,
    Real.log_mul hc.ne' hD.ne',
    Real.log_div (by positivity) hDl1.ne',
    Real.log_mul (Real.exp_pos 1).ne' hD.ne', Real.log_exp,
    Real.log_div hJ.ne' hc.ne']
  ring

example {E : ℕ} (hE : 2 ≤ E) :
    1 ≤ P14.jE 8307 E ∧ ((P14.jE 8307 E : ℕ) : ℝ) ≤ P14.δ * P14.f * 8307 ∧
      ((P14.jE 8307 E : ℕ) : ℝ) ≤ E * P14.J ∧ P14.jE 8307 E ≤ P14.jmax 8307 :=
  jE_factsd_local P14 positive_rank14 hE

example {E : ℕ} (hE : 2 ≤ E) :
    1 ≤ P15.jE 8307 E ∧ ((P15.jE 8307 E : ℕ) : ℝ) ≤ P15.δ * P15.f * 8307 ∧
      ((P15.jE 8307 E : ℕ) : ℝ) ≤ E * P15.J ∧ P15.jE 8307 E ≤ P15.jmax 8307 :=
  jE_factsd_local P15 positive_rank15 hE

example {E : ℕ} (hE : 2 ≤ E) :
    1 ≤ P13J3.jE 3832 E ∧ ((P13J3.jE 3832 E : ℕ) : ℝ) ≤ P13J3.δ * P13J3.f * 3832 ∧
      ((P13J3.jE 3832 E : ℕ) : ℝ) ≤ E * P13J3.J ∧ P13J3.jE 3832 E ≤ P13J3.jmax 3832 :=
  jE_factsd_local P13J3 local_rank_positive13J3 hE

theorem SRd_fail_card_le_local (P : F2PD) (K0 Xn qd N : ℕ)
    (hK0 : P.J / (P.g1 + 1) ≤ K0) (hT : N + K0 + 1 ≤ P.f - P.g1 + 1)
    (hD2 : P.δ * P.f ≤ ((P.f - P.g1 : ℕ) : ℝ) + 1)
    (hXe : Real.exp 1 * P.J ≤ Xn * (((P.f - P.g1 : ℕ) : ℝ) + 1)) (hXn : 1 ≤ Xn)
    (hqe : qd * (Real.exp 1 * (P.δ * P.f)) ≤ ((P.f - P.g1 : ℕ) : ℝ) + 1) (hqd : 1 ≤ qd)
    (hnat : 10000 * ((K0 + 1) * P.J ^ K0 * Xn ^ (K0 + 1)) ≤ qd ^ N)
    {m n : ℕ} (hn : 16 ≤ n) (hRank : 1 ≤ P.jmax n) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ SRd P σ).card : ℝ) ≤
      (1 / 10000) * Fintype.card (Scramble m n) := by
  classical
  have hn0' : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn0'
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ := P.hδ
  set j0 : ℕ := min P.J (P.jmax n) with hj0def
  set T : ℕ := P.f - P.g1 + 1 with hTdef
  have hjmaxR : (P.jmax n : ℝ) ≤ P.δ * (P.f * n) := by
    unfold F2PD.jmax
    exact Nat.floor_le (by positivity)
  have hj0R : (j0 : ℝ) ≤ P.δ * (P.f * n) :=
    (by exact_mod_cast min_le_right _ _ : (j0 : ℝ) ≤ P.jmax n).trans hjmaxR
  have hj0pos : 0 < j0 := by
    have hJpos : 0 < P.J := P.hJ
    have hjpos : 0 < P.jmax n := by omega
    exact lt_min hJpos hjpos
  have hj0J : j0 ≤ P.J := min_le_left _ _
  have hTR : (T : ℝ) = ((P.f - P.g1 : ℕ) : ℝ) + 1 := by rw [hTdef]; push_cast; ring
  have hTpos : (0 : ℝ) < T := by rw [hTR]; positivity
  have hTj : (j0 : ℝ) / n ≤ (T : ℝ) := by
    rw [div_le_iff₀ hn0, hTR]
    have h2 := mul_le_mul_of_nonneg_right hD2 hn0.le
    calc (j0 : ℝ) ≤ P.δ * (P.f * n) := hj0R
      _ = P.δ * P.f * n := by ring
      _ ≤ _ := h2
  have hbad : ∀ σ ∈ (Finset.univ.filter fun σ : Scramble m n => ¬ SRd P σ),
      ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ j0 ∧
        ∃ S : Finset (Fin n), S.card = 1 ∧ T ≤ onesInRows c σ (topRows m P.g1) S := by
    intro σ hσ
    have h := (Finset.mem_filter.mp hσ).2
    unfold SRd at h
    push_neg at h
    obtain ⟨c, hc, S, hS, hle⟩ := h
    exact ⟨c, hc, S, hS, hle⟩
  have hmain := F2SR_union_bound P.g1 j0 T hn0' hj0pos hTj _ hbad
  have htops := tops_card_le_crude P.g1 n j0 hn0' hj0pos
  have hKle : j0 / (P.g1 + 1) ≤ K0 := (Nat.div_le_div_right hj0J).trans hK0
  set K := j0 / (P.g1 + 1) with hKdef
  set b : ℝ := Real.exp 1 * j0 / (n * (T : ℝ)) with hbdef
  set X : ℝ := Real.exp 1 * P.J / T with hXdef
  have he0 := Real.exp_pos 1
  have hb0 : 0 ≤ b := by positivity
  have hbX : b ≤ X / n := by
    rw [hbdef, hXdef, div_div, mul_comm (T : ℝ) (n : ℝ)]
    gcongr
  have hX0 : 0 ≤ X := by positivity
  have hX : X ≤ Xn := by
    rw [hXdef, div_le_iff₀ hTpos, hTR]; exact hXe
  have hqd0 : (0 : ℝ) < qd := by exact_mod_cast hqd
  have hb7 : b ≤ 1 / qd := by
    rw [hbdef, div_le_div_iff₀ (by positivity) hqd0, one_mul]
    have h1 : Real.exp 1 * j0 ≤ Real.exp 1 * (P.δ * (P.f * n)) :=
      mul_le_mul_of_nonneg_left hj0R he0.le
    have h2 := mul_le_mul_of_nonneg_right hqe hn0.le
    rw [← hTR] at h2
    nlinarith
  have hnum := SRd_numeric n K T j0 K0 P.J Xn qd N hKle hT b X hb0 hqd hb7 hbX hn0' hX0 hX hXn
    hj0J P.hJ hnat
  have hcard : (0 : ℝ) ≤ Fintype.card (Scramble m n) := Nat.cast_nonneg _
  rw [Real.rpow_natCast] at hmain
  refine hmain.trans ?_
  have htopsR : ((tops P.g1 n j0).card : ℝ) ≤ ((K + 1 : ℕ) : ℝ) * ((n : ℝ) * j0) ^ K := by
    exact_mod_cast htops
  calc ((tops P.g1 n j0).card : ℝ) * ((n : ℝ) * b ^ T) * (Fintype.card (Scramble m n) : ℝ)
      ≤ (((K + 1 : ℕ) : ℝ) * ((n : ℝ) * j0) ^ K) * ((n : ℝ) * b ^ T) *
          (Fintype.card (Scramble m n) : ℝ) := by
        gcongr
    _ ≤ (1 / 10000) * (Fintype.card (Scramble m n) : ℝ) := by
        exact mul_le_mul_of_nonneg_right hnum hcard

theorem sr_fail14 (m : ℕ) :
    ((Finset.univ.filter fun σ : Scramble m 8307 => ¬ SRd P14 σ).card : ℝ) ≤
      (1 / 10000) * Fintype.card (Scramble m 8307) := by
  exact SRd_fail_card_le_local (P := P14) (K0 := 0) (Xn := 1) (qd := 4) (N := 7)
    (hK0 := by norm_num [P14])
    (hT := by norm_num [P14])
    (hD2 := by norm_num [P14])
    (hXe := by
      have he := Real.exp_one_lt_d9
      norm_num [P14] at he ⊢
      linarith)
    (hXn := by norm_num)
    (hqe := by
      have he := Real.exp_one_lt_d9
      norm_num [P14] at he ⊢
      nlinarith)
    (hqd := by norm_num)
    (hnat := by norm_num)
    (m := m) (n := 8307) (hn := by norm_num) (hRank := positive_rank14)

theorem sr_fail15 (m : ℕ) :
    ((Finset.univ.filter fun σ : Scramble m 8307 => ¬ SRd P15 σ).card : ℝ) ≤
      (1 / 10000) * Fintype.card (Scramble m 8307) := by
  exact SRd_fail_card_le_local (P := P15) (K0 := 0) (Xn := 1) (qd := 4) (N := 7)
    (hK0 := by norm_num [P15])
    (hT := by norm_num [P15])
    (hD2 := by norm_num [P15])
    (hXe := by
      have he := Real.exp_one_lt_d9
      norm_num [P15] at he ⊢
      linarith)
    (hXn := by norm_num)
    (hqe := by
      have he := Real.exp_one_lt_d9
      norm_num [P15] at he ⊢
      nlinarith)
    (hqd := by norm_num)
    (hnat := by norm_num)
    (m := m) (n := 8307) (hn := by norm_num) (hRank := positive_rank15)

/-- Uniform round-one small-rank bound for the 13-row candidate, at every
column count admitted by the all-depth geometry gate. -/
theorem sr_fail13J3 {m n : ℕ} (hn : 3832 ≤ n) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ SRd P13J3 σ).card : ℝ) ≤
      (1 / 10000) * Fintype.card (Scramble m n) := by
  exact SRd_fail_card_le_local (P := P13J3) (K0 := 0) (Xn := 1)
    (qd := 4) (N := 7)
    (hK0 := by norm_num [P13J3])
    (hT := by norm_num [P13J3])
    (hD2 := by norm_num [P13J3])
    (hXe := by
      have he := Real.exp_one_lt_d9
      norm_num [P13J3] at he ⊢
      linarith)
    (hXn := by norm_num)
    (hqe := by
      have he := Real.exp_one_lt_d9
      norm_num [P13J3] at he ⊢
      nlinarith)
    (hqd := by norm_num)
    (hnat := by norm_num)
    (m := m) (n := n) (hn := by omega)
    (hRank := local_rank_positive13J3_of_lower_bound hn)


set_option maxHeartbeats 1600000 in
/-- The real-number core of R1(a): the bound `(K+1) X^K (e n/s)^s (e j/(n(Δ+1)))^{(Δ+1)s} ≤ e^{-10E}`. -/
theorem R1a_aggregate_real {n j s E : ℕ} {G Dl D J c beta : ℝ}
    (hn : 0 < n) (hj : 1 ≤ j) (hjD : (j : ℝ) ≤ D * n) (hjE : (j : ℝ) ≤ E * J)
    (hs1 : 1 ≤ s) (hs : c * E + 1 ≤ s)
    (hG : 0 < G) (hDl : 0 < Dl) (hD : 0 < D) (hJ : 0 < J) (hc : 0 < c)
    (hαc : J / G ≤ c * Dl)
    (h1 : 0 ≤ 2 + 2 * Real.log G - Real.log D)
    (h2 : 0 ≤ (Dl + 1) * (Real.log (Dl + 1) - 1) - 1 - Real.log (J / c) - Dl * Real.log D)
    (hbeta : beta = Real.log (Real.exp 1 * J / (c * D)) +
      (Dl + 1) * Real.log (Real.exp 1 * D / (Dl + 1)))
    (hE : 2 ≤ E) :
    ((j : ℝ) / G + 1) * (Real.exp 1 ^ 2 * n * G ^ 2 / j) ^ ((j : ℝ) / G) *
      (Real.exp 1 * n / s) ^ s *
      (Real.exp 1 * j * s / (n * ((Dl + 1) * s))) ^ ((Dl + 1) * (s : ℝ)) ≤
        (((E : ℝ) * J / G + 1) * Real.exp beta *
          Real.exp ((E : ℝ) * (J / G * (2 + 2 * Real.log G - Real.log D) + c * beta))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
  have hE2 : (2 : ℝ) ≤ E := by exact_mod_cast hE
  have hE0 : (0 : ℝ) < E := by linarith
  have he := Real.exp_pos 1
  have hDl1 : 0 < Dl + 1 := by linarith
  set Kr : ℝ := (j : ℝ) / G with hKr
  have hKr0 : 0 < Kr := by positivity
  set L : ℝ := Real.log n - Real.log j with hLdef
  have hL : -Real.log D ≤ L := by
    have := Real.log_le_log hj0 hjD
    rw [Real.log_mul hD.ne' hn0.ne'] at this
    rw [hLdef]; linarith
  set a0 : ℝ := 2 + 2 * Real.log G with ha0
  -- the three logarithms
  have hX : (0 : ℝ) < Real.exp 1 ^ 2 * n * G ^ 2 / j := by positivity
  have hlogX : Real.log (Real.exp 1 ^ 2 * n * G ^ 2 / j) = a0 + L := by
    rw [Real.log_div (by positivity) hj0.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_exp,
      hLdef, ha0]
    push_cast; ring
  have hY : (0 : ℝ) < Real.exp 1 * n / s := by positivity
  have hcj : c * j ≤ J * s := by
    have h1 : c * (j : ℝ) ≤ c * (E * J) := mul_le_mul_of_nonneg_left hjE hc.le
    nlinarith
  have hlogY : Real.log (Real.exp 1 * n / s) ≤ 1 + Real.log (J / c) + L := by
    rw [Real.log_div (by positivity) hs0.ne', Real.log_mul he.ne' hn0.ne', Real.log_exp,
      Real.log_div hJ.ne' hc.ne', hLdef]
    have := Real.log_le_log (by positivity) hcj
    rw [Real.log_mul hc.ne' hj0.ne', Real.log_mul hJ.ne' hs0.ne'] at this
    linarith
  have hZeq : Real.exp 1 * j * s / (n * ((Dl + 1) * s)) = Real.exp 1 * j / (n * (Dl + 1)) := by
    field_simp
  have hZ : (0 : ℝ) < Real.exp 1 * j * s / (n * ((Dl + 1) * s)) := by positivity
  have hlogZ : Real.log (Real.exp 1 * j * s / (n * ((Dl + 1) * s))) = 1 - L - Real.log (Dl + 1) := by
    rw [hZeq, Real.log_div (by positivity) (by positivity), Real.log_mul he.ne' hj0.ne',
      Real.log_mul hn0.ne' hDl1.ne', Real.log_exp, hLdef]
    ring
  -- rewrite the product as an exponential
  have hK1 : (0 : ℝ) < Kr + 1 := by linarith
  have hprod : (Kr + 1) * (Real.exp 1 ^ 2 * n * G ^ 2 / j) ^ Kr * (Real.exp 1 * n / s) ^ s *
      (Real.exp 1 * j * s / (n * ((Dl + 1) * s))) ^ ((Dl + 1) * (s : ℝ)) =
      Real.exp (Real.log (Kr + 1) + Real.log (Real.exp 1 ^ 2 * n * G ^ 2 / j) * Kr +
        s * Real.log (Real.exp 1 * n / s) +
        Real.log (Real.exp 1 * j * s / (n * ((Dl + 1) * s))) * ((Dl + 1) * s)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hK1, ← Real.rpow_def_of_pos hX,
      ← pow_eq_exp' _ hY, ← Real.rpow_def_of_pos hZ]
  have hRHS :
      (((E : ℝ) * J / G + 1) * Real.exp beta *
        Real.exp ((E : ℝ) * (J / G * (2 + 2 * Real.log G - Real.log D) + c * beta))) =
      Real.exp (Real.log ((E : ℝ) * J / G + 1) + beta +
        (E : ℝ) * (J / G * (2 + 2 * Real.log G - Real.log D) + c * beta)) := by
    calc
      _ = Real.exp (Real.log ((E : ℝ) * J / G + 1)) * Real.exp beta *
          Real.exp ((E : ℝ) * (J / G * (2 + 2 * Real.log G - Real.log D) + c * beta)) := by
            rw [Real.exp_log (by positivity)]
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  rw [hRHS, hprod]
  refine Real.exp_le_exp.mpr ?_
  rw [hlogX, hlogZ]
  -- the exponent
  have hd : 0 ≤ L + Real.log D := by linarith
  have hA : 0 ≤ a0 + L := by linarith
  set Q0 : ℝ := (Dl + 1) * (Real.log (Dl + 1) - 1) - 1 - Real.log (J / c) - Dl * Real.log D with hQ0
  have hKE : Kr ≤ E * J / G := by
    rw [hKr]; exact div_le_div_of_nonneg_right hjE hG.le
  have hP1 : Kr * (a0 + L) ≤ E * J / G * (a0 + L) := mul_le_mul_of_nonneg_right hKE hA
  have hP2 : (c * E + 1) * Q0 ≤ s * Q0 :=
    mul_le_mul_of_nonneg_right (by linarith) h2
  have hP3 : J / G * E * (L + Real.log D) ≤ s * (Dl * (L + Real.log D)) := by
    have e1 : J / G * E ≤ c * Dl * E := mul_le_mul_of_nonneg_right hαc hE0.le
    have e2 : J / G * E * (L + Real.log D) ≤ c * Dl * E * (L + Real.log D) :=
      mul_le_mul_of_nonneg_right e1 hd
    have e3 : c * E * (Dl * (L + Real.log D)) ≤ s * (Dl * (L + Real.log D)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e4 : c * Dl * E * (L + Real.log D) = c * E * (Dl * (L + Real.log D)) := by ring
    linarith [e2, e3, e4]
  have hYs : (s : ℝ) * Real.log (Real.exp 1 * n / s) ≤ s * (1 + Real.log (J / c) + L) :=
    mul_le_mul_of_nonneg_left hlogY hs0.le
  have hid : s * (1 + Real.log (J / c) + L) + (1 - L - Real.log (Dl + 1)) * ((Dl + 1) * s) =
      -(s * Q0) - s * (Dl * (L + Real.log D)) := by
    rw [hQ0]; ring
  have hBetaNeg : beta = -Q0 := by
    rw [hbeta, hQ0]
    exact r1a_beta_eq_neg_Q0 hDl hD hJ hc
  have hH : E * (J / G * (a0 - Real.log D) - c * Q0) =
      E * (J / G * (2 + 2 * Real.log G - Real.log D) + c * beta) := by
    rw [ha0, hBetaNeg]
    ring
  have hlogK : Real.log (Kr + 1) ≤ Real.log ((E : ℝ) * J / G + 1) := by
    apply Real.log_le_log
    · positivity
    · have := hKE
      linarith
  have hexp : E * J / G * (a0 + L) = J / G * E * (a0 - Real.log D) + J / G * E * (L + Real.log D) := by
    ring
  have hcomm : (a0 + L) * Kr = Kr * (a0 + L) := mul_comm _ _
  have htail :
      s * Real.log (Real.exp 1 * n / s) +
        Real.log (Real.exp 1 * j * s / (n * ((Dl + 1) * s))) * ((Dl + 1) * s) ≤
      -s * Q0 - s * (Dl * (L + Real.log D)) := by
    calc
      _ ≤ s * (1 + Real.log (J / c) + L) +
          Real.log (Real.exp 1 * j * s / (n * ((Dl + 1) * s))) * ((Dl + 1) * s) :=
        add_le_add hYs le_rfl
      _ = -s * Q0 - s * (Dl * (L + Real.log D)) := by
        rw [hlogZ, hQ0]
        ring
  have hsum :
      Real.log (Kr + 1) + Kr * (a0 + L) +
        s * Real.log (Real.exp 1 * n / s) +
        Real.log (Real.exp 1 * j * s / (n * ((Dl + 1) * s))) * ((Dl + 1) * s) ≤
      Real.log (Kr + 1) + E * (J / G * (a0 - Real.log D) - c * Q0) + beta := by
    calc
      _ ≤ Real.log (Kr + 1) + E * J / G * (a0 + L) - s * Q0 -
            s * (Dl * (L + Real.log D)) := by
          have hmain : Kr * (a0 + L) +
              (s * Real.log (Real.exp 1 * n / s) +
                Real.log (Real.exp 1 * j * s / (n * ((Dl + 1) * s))) * ((Dl + 1) * s)) ≤
              E * J / G * (a0 + L) - s * Q0 - s * (Dl * (L + Real.log D)) := by
            calc
              _ ≤ E * J / G * (a0 + L) +
                  (-s * Q0 - s * (Dl * (L + Real.log D))) := add_le_add hP1 htail
              _ = _ := by ring
          linarith [hmain]
      _ ≤ Real.log (Kr + 1) + E * J / G * (a0 + L) -
            (c * E + 1) * Q0 - E * J / G * (L + Real.log D) := by
          have hP2neg : -(s * Q0) ≤ -((c * E + 1) * Q0) := neg_le_neg hP2
          have hP3neg : -(s * (Dl * (L + Real.log D))) ≤
              -(E * J / G * (L + Real.log D)) := by
            calc
              _ ≤ -(J / G * E * (L + Real.log D)) := neg_le_neg hP3
              _ = _ := by ring
          linarith [hP2neg, hP3neg]
      _ = Real.log (Kr + 1) + E * (J / G * (a0 - Real.log D) - c * Q0) + beta := by
          rw [hBetaNeg]
          ring
  have hfinal :
      Real.log (Kr + 1) + E * (J / G * (a0 - Real.log D) - c * Q0) + beta ≤
      Real.log ((E : ℝ) * J / G + 1) + beta +
        E * (J / G * (2 + 2 * Real.log G - Real.log D) + c * beta) := by
    rw [hH]
    linarith [hlogK]
  rw [hlogZ] at hsum
  rw [hcomm]
  exact hsum.trans hfinal

open scoped BigOperators

/-- A simple polynomial-geometric tail estimate used to sum the aggregate
R1(a) event bound over all scale indices `E >= 2`. -/
theorem r1a_linear_geometric_sum_le (K : ℕ) {alpha r : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hr0 : 0 ≤ r) (hr : r ≤ 2 / 3) :
    (∑ E ∈ Finset.Ico 2 K, (alpha * (E : ℝ) + 1) * r ^ E) ≤ 64 / 3 := by
  have hpoly : ∀ E : ℕ, 2 ≤ E →
      (E + 1 : ℝ) ≤ 3 * (4 / 3 : ℝ) ^ E := by
    intro E hE
    induction E, hE using Nat.le_induction with
    | base => norm_num
    | succ E hE ih =>
        have hden : (0 : ℝ) < E + 1 := by positivity
        have hEreal : (2 : ℝ) ≤ E := by exact_mod_cast hE
        have hfactor : ((E : ℝ) + 2) / ((E : ℝ) + 1) ≤ (4 / 3 : ℝ) := by
          rw [div_le_iff₀ hden]
          nlinarith
        calc
          ((E + 1 + 1 : ℕ) : ℝ) = ((E : ℝ) + 1) *
              (((E : ℝ) + 2) / ((E : ℝ) + 1)) := by
                push_cast
                field_simp
                ring
          _ ≤ (3 * (4 / 3 : ℝ) ^ E) * (4 / 3) :=
                mul_le_mul ih hfactor (by positivity) (by positivity)
          _ = 3 * (4 / 3 : ℝ) ^ (E + 1) := by rw [pow_succ]; ring
  have hterm : ∀ E ∈ Finset.Ico 2 K,
      (alpha * (E : ℝ) + 1) * r ^ E ≤ 3 * (8 / 9 : ℝ) ^ E := by
    intro E hE
    have hE2 : 2 ≤ E := (Finset.mem_Ico.mp hE).1
    have hE0 : 0 ≤ (E : ℝ) := Nat.cast_nonneg _
    have hcoef : alpha * (E : ℝ) + 1 ≤ (E : ℝ) + 1 := by nlinarith
    have hpow : r ^ E ≤ (2 / 3 : ℝ) ^ E :=
      pow_le_pow_left₀ hr0 hr (E : ℕ)
    calc
      _ ≤ ((E : ℝ) + 1) * r ^ E :=
        mul_le_mul_of_nonneg_right hcoef (pow_nonneg hr0 _)
      _ ≤ ((E : ℝ) + 1) * (2 / 3 : ℝ) ^ E :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ (3 * (4 / 3 : ℝ) ^ E) * (2 / 3 : ℝ) ^ E :=
        mul_le_mul_of_nonneg_right (hpoly E hE2) (by positivity)
      _ = 3 * (8 / 9 : ℝ) ^ E := by
        calc
          _ = 3 * ((4 / 3 : ℝ) ^ E * (2 / 3 : ℝ) ^ E) := by ring
          _ = 3 * ((4 / 3 : ℝ) * (2 / 3)) ^ E := by rw [← mul_pow]
          _ = _ := by norm_num
  have hgeo := geom_sum_Ico_le_of_lt_one (m := 2) (n := K)
      (by norm_num : (0 : ℝ) ≤ 8 / 9) (by norm_num : (8 / 9 : ℝ) < 1)
  calc
    _ ≤ ∑ E ∈ Finset.Ico 2 K, 3 * (8 / 9 : ℝ) ^ E :=
      Finset.sum_le_sum fun E hE => hterm E hE
    _ = 3 * ∑ E ∈ Finset.Ico 2 K, (8 / 9 : ℝ) ^ E := by rw [Finset.mul_sum]
    _ ≤ 3 * ((8 / 9 : ℝ) ^ 2 / (1 - 8 / 9)) :=
      mul_le_mul_of_nonneg_left hgeo (by norm_num)
    _ = 64 / 3 := by norm_num

/-- Once the aggregate rate has `lambda >= 1/2` and `beta <= -12`, the
entire finite R1(a) union over `E` costs less than `1/1000`. -/
theorem r1a_aggregate_sum_le (K : ℕ) {alpha beta lambda : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hbeta : beta ≤ -12) (hlambda : 1 / 2 ≤ lambda) :
    (∑ E ∈ Finset.Ico 2 K,
      (alpha * (E : ℝ) + 1) * Real.exp beta * Real.exp (-lambda * E)) ≤ 1 / 1000 := by
  have hr0 : 0 ≤ Real.exp (-lambda) := (Real.exp_pos _).le
  have hhalf : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
    have := Real.add_one_le_exp (1 / 2 : ℝ)
    norm_num at this ⊢
    linarith
  have hr : Real.exp (-lambda) ≤ 2 / 3 := by
    rw [Real.exp_neg, inv_eq_one_div]
    have hden : Real.exp (1 / 2) ≤ Real.exp lambda := by
      exact Real.exp_le_exp.mpr (by linarith)
    apply (div_le_iff₀ (Real.exp_pos lambda)).2
    norm_num
    linarith [hhalf, hden]
  have hpow : ∀ E : ℕ, Real.exp (-lambda * (E : ℝ)) = Real.exp (-lambda) ^ E := by
    intro E
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have he : (5 / 2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    norm_num at h ⊢
    linarith
  have hpow12 : (50000 : ℝ) ≤ Real.exp 12 := by
    have hpow : (50000 : ℝ) ≤ (5 / 2 : ℝ) ^ 12 := by norm_num
    have hlow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 2) he 12
    have hpow' : (5 / 2 : ℝ) ^ 12 ≤ Real.exp 1 ^ 12 := hlow
    have hexp : Real.exp 1 ^ 12 = Real.exp 12 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [← hexp]
    exact hpow.trans hpow'
  have hbetaExp : Real.exp beta ≤ 1 / 50000 := by
    have hmono : Real.exp beta ≤ Real.exp (-12) := Real.exp_le_exp.mpr hbeta
    have hsmall : Real.exp (-12) ≤ 1 / 50000 := by
      rw [Real.exp_neg]
      apply (div_le_iff₀ (Real.exp_pos 12)).2
      norm_num
      exact hpow12
    exact hmono.trans hsmall
  have hsum := r1a_linear_geometric_sum_le K halpha0 halpha1 hr0 hr
  have hfactor : 0 ≤ Real.exp beta := (Real.exp_pos _).le
  calc
    _ = ∑ E ∈ Finset.Ico 2 K,
          Real.exp beta * ((alpha * (E : ℝ) + 1) * Real.exp (-lambda) ^ E) := by
        apply Finset.sum_congr rfl
        intro E hE
        rw [hpow E]
        ring
    _ ≤ Real.exp beta * (64 / 3) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hsum hfactor
    _ ≤ (1 / 50000) * (64 / 3) :=
        mul_le_mul_of_nonneg_right hbetaExp (by norm_num)
    _ ≤ 1 / 1000 := by norm_num


end Chvatal.RaggedF2Local
