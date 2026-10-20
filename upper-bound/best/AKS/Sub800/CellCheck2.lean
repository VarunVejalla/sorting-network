import AKS.Sub800.CellLemmas2
import AKS.Sub800.CellCheck1

/-! # Round-2 cells as checked data

As `CellCheck1`, for the round-2 cell conditions `Round2Num.CellOK2` (through
`CellLemmas2.cellOK2_of_bounds`): two rates `al`, `be` per cell, the entropy at the endpoint
`pb ≤ 1/2`, and cells covering `[0, 1/2]`. -/

open Real Round2Col ExpCert CellCheck1

namespace CellCheck2

structure Cell where
  pa : ℚ
  pb : ℚ
  lam : ℚ
  tt : ℚ
  al : ℚ
  be : ℚ
  Eua : ℚ
  Ela : ℚ
  Qa : ℚ
  Lqa : ℚ
  Eub : ℚ
  Elb : ℚ
  Qb : ℚ
  Lqb : ℚ
  C1a : ℚ
  C1b : ℚ
  Lq2 : ℚ
  A : ℚ
  B : ℚ
  cEua : Cert
  cEla : Cert
  cQa : Cert
  cLqa : Cert
  cEub : Cert
  cElb : Cert
  cQb : Cert
  cLqb : Cert
  cC1a : Cert
  cC1b : Cert
  cLq2 : Cert
  cA : Cert
  cB : Cert

structure Glob where
  E1 : ℚ
  d : ℚ
  gp : ℕ
  M : ℚ
  η : ℚ
  lnG : ℚ
  A1 : ℚ
  B1 : ℚ
  L15000 : ℚ
  cA1 : Cert
  cB1 : Cert
  cL : Cert

def Hq (c : Cell) : ℚ := c.pb * c.A + (1 - c.pb) * c.B

def globOK (g : Glob) : Bool :=
  decide (0 < g.E1) && decide (0 < g.d) && decide (0 < g.η) && decide (g.η ≤ 1 / 100) &&
    decide (15 / g.η = 15000) && expUp (1 / 1000) g.cA1 g.A1 && expLo (-(1 / 1000)) g.cB1 g.B1 &&
    logUp 15000 g.L15000 g.cL

def check (g : Glob) (c : Cell) : Bool :=
  decide (0 ≤ c.pa) && decide (c.pa ≤ c.pb) && decide (c.pb ≤ 1 / 2) && decide (0 ≤ c.lam) &&
    decide (0 < c.tt) && decide (c.tt < c.al) && decide (c.tt < c.be) &&
    decide (c.lam * g.E1 ≤ g.d / 2) &&
    expUp c.al c.cEua c.Eua && expLo c.al c.cEla c.Ela && decide (1 ≤ c.Ela) &&
    expLo (c.al * (c.pa + c.lam)) c.cQa c.Qa && decide (1 + c.pa * (c.Eua - 1) ≤ c.Qa) &&
    expLo c.Lqa c.cLqa (1 + c.pa * (c.Eua - 1)) &&
    decide (c.Lqa + (c.pb - c.pa) * (c.Eua - 1) / (1 + c.pa * (c.Ela - 1)) ≤ c.al * (c.pb + c.lam)) &&
    expUp c.be c.cEub c.Eub && expLo c.be c.cElb c.Elb && decide (1 ≤ c.Elb) &&
    expLo (c.be * ((1 - c.pb) + c.lam)) c.cQb c.Qb && decide (1 + (1 - c.pb) * (c.Eub - 1) ≤ c.Qb) &&
    expLo c.Lqb c.cLqb (1 + (1 - c.pb) * (c.Eub - 1)) &&
    decide (c.Lqb + ((1 - c.pa) - (1 - c.pb)) * (c.Eub - 1) / (1 + (1 - c.pb) * (c.Elb - 1)) ≤
      c.be * ((1 - c.pa) + c.lam)) &&
    decide (0 < c.pb) && decide (c.pb < 1) && expLo c.A c.cA (1 / c.pb) &&
    expLo c.B c.cB (1 / (1 - c.pb)) &&
    expUp ((c.tt - c.al) * (1 / 1000 / c.tt)) c.cC1a c.C1a && decide (c.C1a < 1) &&
    expUp ((c.tt - c.be) * (1 / 1000 / c.tt)) c.cC1b c.C1b && decide (c.C1b < 1) &&
    expLo c.Lq2 c.cLq2 (g.A1 * (1 + (1 - g.B1) / (1 - c.C1a)) + g.A1 * (1 + (1 - g.B1) / (1 - c.C1b)) - 1) &&
    decide (c.lam * (g.E1 * g.M + g.gp) + (Hq c + c.Lq2 + (g.lnG + g.L15000) / 16) / c.tt ≤ g.d / 2 * g.M)

set_option maxHeartbeats 2000000 in
/-- **A checked cell satisfies the round-2 cell conditions.** -/
theorem check_sound (g : Glob) (c : Cell) (hg : globOK g = true) (h : check g c = true) :
    Round2Num.CellOK2 (g.E1 : ℝ) g.d (g.gp : ℝ) g.M g.η g.lnG c.pa c.pb c.lam c.tt c.al c.be := by
  unfold globOK at hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hη⟩, hA1⟩, hB1⟩, hL⟩ := hg
  unfold check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpa, hpab⟩, hpb⟩, hlam⟩, ht⟩, htal⟩, htbe⟩,
    hlamE⟩, hEua⟩, hEla⟩, hEla1⟩, hQa⟩, hQa'⟩, hLqa⟩, hrba⟩, hEub⟩, hElb⟩, hElb1⟩, hQb⟩, hQb'⟩,
    hLqb⟩, hrbb⟩, hq0⟩, hq1⟩, hA⟩, hB⟩, hC1a⟩, hC1a'⟩, hC1b⟩, hC1b'⟩, hLq2⟩, hfin⟩ := h
  have hA1' := expUp_sound hA1
  have hB1' := expLo_sound hB1
  have hL' := logUp_sound hL
  have hEua' := expUp_sound hEua
  have hEla' := expLo_sound hEla
  have hQa'' := expLo_sound hQa
  have hLqa' := expLo_sound hLqa
  have hEub' := expUp_sound hEub
  have hElb' := expLo_sound hElb
  have hQb'' := expLo_sound hQb
  have hLqb' := expLo_sound hLqb
  have hA' := expLo_sound hA
  have hB' := expLo_sound hB
  have hC1a'' := expUp_sound hC1a
  have hC1b'' := expUp_sound hC1b
  have hLq2' := expLo_sound hLq2
  push_cast at hA1' hB1' hL' hQa'' hLqa' hQb'' hLqb' hA' hB' hC1a'' hC1b'' hLq2'
  have hpb' : (c.pb : ℝ) ≤ 1 / 2 := cast_le_lit hpb (by norm_num)
  have hH : ∀ p : ℝ, (c.pa : ℝ) ≤ p → p ≤ c.pb → binEntropy p ≤ (Hq c : ℝ) := by
    intro p hp1 hp2
    have hc := CellLemmas.binEntropy_cell_le (c.pa : ℝ) c.pb p (by exact_mod_cast hpa)
      (by linarith) hp1 hp2
    rw [if_pos hpb'] at hc
    have hent := CellLemmas.binEntropy_le_of (c.pb : ℝ) c.A c.B (by exact_mod_cast hq0)
      (by exact_mod_cast hq1) hA' hB'
    unfold Hq; push_cast; linarith
  exact CellLemmas2.cellOK2_of_bounds _ _ _ _ _ _ _ _ _ _ _ _ c.Eua c.Ela c.Qa c.Lqa c.Eub c.Elb c.Qb
    c.Lqb (Hq c) c.C1a c.C1b c.Lq2 g.A1 g.B1 g.L15000 (by exact_mod_cast hpa) (by exact_mod_cast hpab)
    hpb' (by exact_mod_cast hlam) (by exact_mod_cast ht) (by exact_mod_cast htal)
    (by exact_mod_cast htbe) (by exact_mod_cast hlamE) (by exact_mod_cast hη) hEua' hEla'
    (by exact_mod_cast hEla1) hQa'' (by exact_mod_cast hQa') hLqa' (by exact_mod_cast hrba) hEub' hElb'
    (by exact_mod_cast hElb1) hQb'' (by exact_mod_cast hQb') hLqb' (by exact_mod_cast hrbb) hH hA1' hB1'
    hC1a'' (by exact_mod_cast hC1a') hC1b'' (by exact_mod_cast hC1b') hLq2' hL' (by exact_mod_cast hfin)

/-- The cells are contiguous from `a` and end at `1/2`. -/
def chainOK : ℚ → List Cell → Bool
  | _, [] => false
  | a, [c] => decide (c.pa = a) && decide (c.pb = 1 / 2)
  | a, c :: t => decide (c.pa = a) && chainOK c.pb t

theorem chain_cover : ∀ (cs : List Cell) (a : ℚ), chainOK a cs = true → ∀ p : ℝ, (a : ℝ) ≤ p →
    p ≤ 1 / 2 → ∃ c ∈ cs, (c.pa : ℝ) ≤ p ∧ p ≤ c.pb
  | [], _, h, _, _, _ => by simp [chainOK] at h
  | [c], a, h, p, hp0, hp1 => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨c, by simp, ?_, ?_⟩
    · rw [h.1]; exact hp0
    · rw [h.2]; push_cast; exact hp1
  | c :: d :: t, a, h, p, hp0, hp1 => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hp : p ≤ c.pb
    · exact ⟨c, by simp, by rw [h.1]; exact hp0, hp⟩
    · obtain ⟨e, he, h'⟩ := chain_cover (d :: t) c.pb h.2 p (le_of_lt (not_le.1 hp)) hp1
      exact ⟨e, List.mem_cons_of_mem _ he, h'⟩

def allOK (g : Glob) (cs : List Cell) : Bool :=
  globOK g && chainOK 0 cs && cs.all (check g)

open Classical in
/-- **Round-2 failure bound from checked cells.** -/
theorem round2_of_cert (g : Glob) (cs : List Cell) (h : allOK g cs = true) {m n : ℕ} (hn : 16 ≤ n)
    (hmM : (g.M : ℝ) ≤ m) (hm : 0 < m)
    (hG : Real.log ((Round2Num.grid m (2 * g.gp + 1)).card : ℝ) ≤ (g.lnG : ℝ)) :
    ((Finset.univ.filter fun σ : Chvatal.Scramble m n =>
        ¬ Chvatal.HasCombinatorialPropertyB2 σ (g.E1 : ℝ) (g.d : ℝ)).card : ℝ) ≤
      (g.η : ℝ) * ((Fintype.card (Chvatal.Scramble m n) : ℕ) : ℝ) := by
  unfold allOK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hg, hch⟩, hall⟩ := h
  have hg' := hg
  unfold globOK at hg'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg'
  obtain ⟨⟨⟨⟨⟨⟨⟨hE1, hd⟩, hη0⟩, hη1⟩, _⟩, _⟩, _⟩, _⟩ := hg'
  refine Round2Num.round2_bound (g.E1 : ℝ) g.d g.M g.η g.lnG g.gp (by exact_mod_cast hE1)
    (by exact_mod_cast hd) (by exact_mod_cast hη0) (cast_le_lit hη1 (by norm_num)) (K := cs.length)
    (fun i => (cs.get i).pa) (fun i => (cs.get i).pb) (fun i => (cs.get i).lam)
    (fun i => (cs.get i).tt) (fun i => (cs.get i).al) (fun i => (cs.get i).be) ?_ ?_ hn hmM hm hG
  · intro p hp0 hp1
    obtain ⟨c, hc, h'⟩ := chain_cover cs 0 hch p (by exact_mod_cast hp0) hp1
    obtain ⟨i, rfl⟩ := List.get_of_mem hc
    exact ⟨i, h'⟩
  · intro i
    exact check_sound g _ hg (hall _ (List.get_mem cs i))

end CellCheck2
