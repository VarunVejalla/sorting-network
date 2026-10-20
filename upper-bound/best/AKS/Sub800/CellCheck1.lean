import AKS.Sub800.CellLemmas
import AKS.Sub800.ExpCert

/-! # Round-1 cells as checked data

A round-1 cell is a record of rationals (the cell `[pa, pb]`, its parameters and the witnesses of
`CellLemmas.cellOK1_of_bounds`) together with `ExpCert` certificates for every `exp`/`log` value.
`check` is a `Bool` computation over `ℚ`; `check_sound` turns a successful check into
`Round1Num.CellOK1`. `round1_of_cert` assembles a checked, contiguous list of cells covering `[0, 1]`
into the round-1 failure bound, so a concrete instance is closed by one `decide +kernel`. -/

open Real Round2Col ExpCert

namespace CellCheck1

/-- Entropy witness of a cell: `log 2 ≤ Hq` (a cell containing `1/2`), or the value at the endpoint
`q` nearest to `1/2` through `1/q ≤ exp A`, `1/(1-q) ≤ exp B` (`Hq = q A + (1-q) B`). -/
inductive Ent
  | mid (Hq : ℚ) (c2 : Cert)
  | atQ (A B : ℚ) (cA cB : Cert)

structure Cell where
  pa : ℚ
  pb : ℚ
  lam : ℚ
  tt : ℚ
  al : ℚ
  Eu : ℚ
  El : ℚ
  Q : ℚ
  Lq : ℚ
  C1 : ℚ
  Lq2 : ℚ
  cEu : Cert
  cEl : Cert
  cQ : Cert
  cLq : Cert
  cC1 : Cert
  cLq2 : Cert
  ent : Ent

structure Glob where
  E1 : ℚ
  M : ℚ
  η : ℚ
  A1 : ℚ
  B1 : ℚ
  L1500 : ℚ
  cA1 : Cert
  cB1 : Cert
  cL : Cert

/-- The entropy endpoint of a cell not containing `1/2`. -/
def qOf (c : Cell) : ℚ := if c.pb ≤ 1 / 2 then c.pb else c.pa

def Hq (c : Cell) : ℚ :=
  match c.ent with
  | .mid H _ => H
  | .atQ A B _ _ => qOf c * A + (1 - qOf c) * B

def entOK (c : Cell) : Bool :=
  match c.ent with
  | .mid H c2 => decide (¬ c.pb ≤ 1 / 2) && decide (¬ 1 / 2 ≤ c.pa) && expLo H c2 2
  | .atQ A B cA cB => decide (c.pb ≤ 1 / 2 ∨ 1 / 2 ≤ c.pa) && decide (0 < qOf c) && decide (qOf c < 1) &&
      expLo A cA (1 / qOf c) && expLo B cB (1 / (1 - qOf c))

def globOK (g : Glob) : Bool :=
  decide (0 < g.E1) && decide (0 < g.η) && decide (g.η ≤ 1 / 100) && decide (15 / g.η = 1500) &&
    expUp (1 / 1000) g.cA1 g.A1 && expLo (-(1 / 1000)) g.cB1 g.B1 && decide (g.B1 ≤ 1) &&
    logUp 1500 g.L1500 g.cL

def check (g : Glob) (c : Cell) : Bool :=
  decide (0 ≤ c.pa) && decide (c.pa ≤ c.pb) && decide (c.pb ≤ 1) && decide (0 ≤ c.lam) &&
    decide (0 < c.tt) && decide (c.tt < c.al) && decide (c.lam ≤ g.E1 / 2) &&
    expUp c.al c.cEu c.Eu && expLo c.al c.cEl c.El && decide (1 ≤ c.El) &&
    expLo (c.al * (c.pa + c.lam)) c.cQ c.Q && decide (1 + c.pa * (c.Eu - 1) ≤ c.Q) &&
    expLo c.Lq c.cLq (1 + c.pa * (c.Eu - 1)) &&
    decide (c.Lq + (c.pb - c.pa) * (c.Eu - 1) / (1 + c.pa * (c.El - 1)) ≤ c.al * (c.pb + c.lam)) &&
    entOK c &&
    expUp ((c.tt - c.al) * (1 / 1000 / c.tt)) c.cC1 c.C1 && decide (c.C1 < 1) &&
    expLo c.Lq2 c.cLq2 (g.A1 * (1 + (1 - g.B1) / (1 - c.C1))) &&
    decide (c.lam * g.M + (Hq c + c.Lq2 + g.L1500 / 16) / c.tt ≤ g.E1 / 2 * g.M)

/-- Casting a rational comparison with a literal right-hand side. -/
theorem cast_le_lit {a b : ℚ} {r : ℝ} (h : a ≤ b) (hb : (b : ℝ) = r) : (a : ℝ) ≤ r :=
  hb ▸ Rat.cast_le.2 h

theorem cast_lit_le {a b : ℚ} {r : ℝ} (h : a ≤ b) (ha : (a : ℝ) = r) : r ≤ (b : ℝ) :=
  ha ▸ Rat.cast_le.2 h

theorem cast_not_le_lit {a b : ℚ} {r : ℝ} (h : ¬ a ≤ b) (hb : (b : ℝ) = r) : ¬ (a : ℝ) ≤ r :=
  hb ▸ fun h' => h (Rat.cast_le.1 h')

theorem cast_not_lit_le {a b : ℚ} {r : ℝ} (h : ¬ a ≤ b) (ha : (a : ℝ) = r) : ¬ r ≤ (b : ℝ) :=
  ha ▸ fun h' => h (Rat.cast_le.1 h')

theorem entropy_sound (c : Cell) (h0 : 0 ≤ c.pa) (h1 : c.pb ≤ 1) (h : entOK c = true) :
    ∀ p : ℝ, (c.pa : ℝ) ≤ p → p ≤ c.pb → binEntropy p ≤ (Hq c : ℝ) := by
  intro p hp1 hp2
  have h0' : (0 : ℝ) ≤ c.pa := by exact_mod_cast h0
  have h1' : (c.pb : ℝ) ≤ 1 := by exact_mod_cast h1
  have hc := CellLemmas.binEntropy_cell_le (c.pa : ℝ) c.pb p h0' h1' hp1 hp2
  unfold entOK at h
  unfold Hq
  split at h
  · rename_i H c2 hent
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hnb, hna⟩, h2⟩ := h
    have hnb' : ¬ (c.pb : ℝ) ≤ 1 / 2 := cast_not_le_lit hnb (by norm_num)
    have hna' : ¬ (1 / 2 : ℝ) ≤ c.pa := cast_not_lit_le hna (by norm_num)
    rw [if_neg hnb', if_neg hna'] at hc
    have hl : Real.log 2 ≤ (H : ℝ) := by
      have := expLo_sound h2
      push_cast at this
      exact ExpBounds.log_le _ _ (by norm_num) this
    exact hc.trans hl
  · rename_i A B cA cB hent
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hside, hq0⟩, hq1⟩, hA⟩, hB⟩ := h
    have hA' := expLo_sound hA
    have hB' := expLo_sound hB
    push_cast at hA' hB'
    have hq0' : (0 : ℝ) < (qOf c : ℝ) := by exact_mod_cast hq0
    have hq1' : ((qOf c : ℚ) : ℝ) < 1 := by exact_mod_cast hq1
    have hent := CellLemmas.binEntropy_le_of _ _ _ hq0' hq1' hA' hB'
    have hval : binEntropy p ≤ binEntropy ((qOf c : ℚ) : ℝ) := by
      unfold qOf
      by_cases hb : c.pb ≤ 1 / 2
      · have hb' : (c.pb : ℝ) ≤ 1 / 2 := cast_le_lit hb (by norm_num)
        rw [if_pos hb'] at hc
        rw [if_pos hb]; exact hc
      · have ha : 1 / 2 ≤ c.pa := hside.resolve_left hb
        have hb' : ¬ (c.pb : ℝ) ≤ 1 / 2 := cast_not_le_lit hb (by norm_num)
        have ha' : (1 / 2 : ℝ) ≤ c.pa := cast_lit_le ha (by norm_num)
        rw [if_neg hb', if_pos ha'] at hc
        rw [if_neg hb]; exact hc
    push_cast
    linarith

set_option maxHeartbeats 1000000 in
/-- **A checked cell satisfies the round-1 cell conditions.** -/
theorem check_sound (g : Glob) (c : Cell) (hg : globOK g = true) (h : check g c = true) :
    Round1Num.CellOK1 (g.E1 : ℝ) g.M g.η c.pa c.pb c.lam c.tt c.al := by
  unfold globOK at hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hη⟩, hA1⟩, hB1⟩, hB11⟩, hL⟩ := hg
  unfold check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpa, hpab⟩, hpb⟩, hlam⟩, ht⟩, htal⟩, hlamE⟩, hEu⟩, hEl⟩, hEl1⟩, hQ⟩,
    hQ'⟩, hLq⟩, hrb⟩, hent⟩, hC1⟩, hC1'⟩, hLq2⟩, hfin⟩ := h
  have hA1' := expUp_sound hA1
  have hB1' := expLo_sound hB1
  have hL' := logUp_sound hL
  have hEu' := expUp_sound hEu
  have hEl' := expLo_sound hEl
  have hQ'' := expLo_sound hQ
  have hLq' := expLo_sound hLq
  have hC1'' := expUp_sound hC1
  have hLq2' := expLo_sound hLq2
  push_cast at hA1' hB1' hL' hQ'' hLq' hC1'' hLq2'
  have hH := entropy_sound c hpa hpb hent
  refine CellLemmas.cellOK1_of_bounds _ _ _ _ _ _ _ _ c.Eu c.El c.Q c.Lq (Hq c) c.C1 c.Lq2 g.A1 g.B1
    g.L1500 (by exact_mod_cast hpa) (by exact_mod_cast hpab) (by exact_mod_cast hpb)
    (by exact_mod_cast hlam) (by exact_mod_cast ht) (by exact_mod_cast htal)
    (by exact_mod_cast hlamE) (by exact_mod_cast hη) hEu' hEl' (by exact_mod_cast hEl1) hQ''
    (by exact_mod_cast hQ') hLq' (by exact_mod_cast hrb) hH hA1' hB1' (by exact_mod_cast hB11) hC1''
    (by exact_mod_cast hC1') hLq2' hL' (by exact_mod_cast hfin)

/-- The cells are contiguous from `a` and end at `1`. -/
def chainOK : ℚ → List Cell → Bool
  | _, [] => false
  | a, [c] => decide (c.pa = a) && decide (c.pb = 1)
  | a, c :: t => decide (c.pa = a) && chainOK c.pb t

theorem chain_cover : ∀ (cs : List Cell) (a : ℚ), chainOK a cs = true → ∀ p : ℝ, (a : ℝ) ≤ p → p ≤ 1 →
    ∃ c ∈ cs, (c.pa : ℝ) ≤ p ∧ p ≤ c.pb
  | [], _, h, _, _, _ => by simp [chainOK] at h
  | [c], a, h, p, hp0, hp1 => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨c, by simp, ?_, ?_⟩
    · rw [h.1]; exact hp0
    · rw [h.2]; exact_mod_cast hp1
  | c :: d :: t, a, h, p, hp0, hp1 => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hp : p ≤ c.pb
    · exact ⟨c, by simp, by rw [h.1]; exact hp0, hp⟩
    · obtain ⟨e, he, h'⟩ := chain_cover (d :: t) c.pb h.2 p (le_of_lt (not_le.1 hp)) hp1
      exact ⟨e, List.mem_cons_of_mem _ he, h'⟩

def allOK (g : Glob) (cs : List Cell) : Bool :=
  globOK g && chainOK 0 cs && cs.all (check g)

open Classical in
/-- **Round-1 failure bound from checked cells.** -/
theorem round1_of_cert (g : Glob) (cs : List Cell) (h : allOK g cs = true) {m n : ℕ} (hn : 16 ≤ n)
    (hmM : (g.M : ℝ) ≤ m) (hm : 0 < m) :
    ((Finset.univ.filter fun σ : Chvatal.Scramble m n =>
        ¬ Chvatal.HasCombinatorialPropertyBOnPipeline σ (g.E1 : ℝ)).card : ℝ) ≤
      (g.η : ℝ) * ((Fintype.card (Chvatal.Scramble m n) : ℕ) : ℝ) := by
  unfold allOK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hg, hch⟩, hall⟩ := h
  have hg' := hg
  unfold globOK at hg'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg'
  obtain ⟨⟨⟨⟨⟨⟨⟨hE1, hη0⟩, hη1⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hg'
  refine Round1Num.round1_bound (g.E1 : ℝ) g.M g.η (by exact_mod_cast hE1) (by exact_mod_cast hη0)
    (cast_le_lit hη1 (by norm_num)) (K := cs.length) (fun i => (cs.get i).pa) (fun i => (cs.get i).pb)
    (fun i => (cs.get i).lam) (fun i => (cs.get i).tt) (fun i => (cs.get i).al) ?_ ?_ hn hmM hm
  · intro p hp0 hp1
    obtain ⟨c, hc, h'⟩ := chain_cover cs 0 hch p (by exact_mod_cast hp0) hp1
    obtain ⟨i, rfl⟩ := List.get_of_mem hc
    exact ⟨i, h'⟩
  · intro i
    exact check_sound g _ hg (hall _ (List.get_mem cs i))

end CellCheck1
