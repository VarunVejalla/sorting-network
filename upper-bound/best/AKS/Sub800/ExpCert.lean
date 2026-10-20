import AKS.Sub800.ExpBounds

/-! # Kernel-checkable certificates for `exp` and `log` bounds

A certificate for `exp x ≤ u` (or `l ≤ exp x`) at a rational `x` is a halving count `k` and the
list of rational values bounding `exp (x / 2^k)`, `exp (x / 2^(k-1))`, …, `exp x`: the first is
checked against the six-term Taylor bound (`ExpBounds.exp_le_base`), each next one against the
square of the previous (`exp (2w) = exp w ^ 2`). The checks are `Bool` computations over `ℚ`, so a
concrete certificate is closed by `decide +kernel`; `expUp_sound`, `expLo_sound`, `logUp_sound` and
`logLo_sound` turn a successful check into the real inequality. -/

namespace ExpCert

/-- Six-term Taylor upper value (the bound of `ExpBounds.exp_le_six`). -/
def tupQ (y : ℚ) : ℚ := 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 + |y| ^ 6 * (7 / 4320)

/-- Six-term Taylor lower value (the bound of `ExpBounds.six_le_exp`). -/
def tloQ (y : ℚ) : ℚ := 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 - |y| ^ 6 * (7 / 4320)

/-- A certificate: `k` halvings, and the bounds from the base `x / 2^k` up to `x`. -/
structure Cert where
  k : ℕ
  hs : List ℚ

/-- Upper squaring chain ending below `u`. -/
def upChain : ℚ → List ℚ → ℚ → Bool
  | p, [], u => decide (p ≤ u)
  | p, h :: t, u => decide (p * p ≤ h) && upChain h t u

/-- Lower squaring chain ending above `l`. -/
def loChain : ℚ → List ℚ → ℚ → Bool
  | p, [], l => decide (l ≤ p)
  | p, h :: t, l => decide (0 ≤ p) && decide (h ≤ p * p) && loChain h t l

/-- Check of `exp x ≤ u`. -/
def expUp (x : ℚ) (c : Cert) (u : ℚ) : Bool :=
  match c.hs with
  | [] => false
  | b :: t => decide (|x / 2 ^ c.k| ≤ 1) && decide (tupQ (x / 2 ^ c.k) ≤ b) && (t.length == c.k) &&
      upChain b t u

/-- Check of `l ≤ exp x`. -/
def expLo (x : ℚ) (c : Cert) (l : ℚ) : Bool :=
  match c.hs with
  | [] => false
  | b :: t => decide (|x / 2 ^ c.k| ≤ 1) && decide (b ≤ tloQ (x / 2 ^ c.k)) && (t.length == c.k) &&
      loChain b t l

/-- Check of `log y ≤ q` (through `y ≤ exp q`). -/
def logUp (y q : ℚ) (c : Cert) : Bool := decide (0 < y) && expLo q c y

/-- Check of `q ≤ log y` (through `exp q ≤ y`). -/
def logLo (y q : ℚ) (c : Cert) : Bool := decide (0 < y) && expUp q c y

theorem tupQ_cast (y : ℚ) : ((tupQ y : ℚ) : ℝ) = 1 + (y : ℝ) + (y : ℝ) ^ 2 / 2 + (y : ℝ) ^ 3 / 6 +
    (y : ℝ) ^ 4 / 24 + (y : ℝ) ^ 5 / 120 + |(y : ℝ)| ^ 6 * (7 / 4320) := by
  unfold tupQ; push_cast; ring

theorem tloQ_cast (y : ℚ) : ((tloQ y : ℚ) : ℝ) = 1 + (y : ℝ) + (y : ℝ) ^ 2 / 2 + (y : ℝ) ^ 3 / 6 +
    (y : ℝ) ^ 4 / 24 + (y : ℝ) ^ 5 / 120 - |(y : ℝ)| ^ 6 * (7 / 4320) := by
  unfold tloQ; push_cast; ring

theorem upChain_sound : ∀ (t : List ℚ) (w : ℝ) (p u : ℚ), Real.exp w ≤ p → upChain p t u = true →
    Real.exp (2 ^ t.length * w) ≤ u
  | [], w, p, u, hw, h => by
    simp only [upChain, decide_eq_true_eq] at h
    simpa using hw.trans (by exact_mod_cast h)
  | h :: t, w, p, u, hw, hc => by
    simp only [upChain, Bool.and_eq_true, decide_eq_true_eq] at hc
    have h0 : 0 ≤ Real.exp w := (Real.exp_pos w).le
    have h2 : Real.exp (2 * w) ≤ h := by
      rw [show 2 * w = w + w by ring, Real.exp_add]
      calc Real.exp w * Real.exp w ≤ (p : ℝ) * p := mul_le_mul hw hw h0 (h0.trans hw)
        _ ≤ h := by exact_mod_cast hc.1
    have := upChain_sound t (2 * w) h u h2 hc.2
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this

theorem loChain_sound : ∀ (t : List ℚ) (w : ℝ) (p l : ℚ), (p : ℝ) ≤ Real.exp w → loChain p t l = true →
    (l : ℝ) ≤ Real.exp (2 ^ t.length * w)
  | [], w, p, l, hw, h => by
    simp only [loChain, decide_eq_true_eq] at h
    simpa using (show (l : ℝ) ≤ p by exact_mod_cast h).trans hw
  | h :: t, w, p, l, hw, hc => by
    simp only [loChain, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hp : (0 : ℝ) ≤ p := by exact_mod_cast hc.1.1
    have h2 : (h : ℝ) ≤ Real.exp (2 * w) := by
      rw [show 2 * w = w + w by ring, Real.exp_add]
      calc (h : ℝ) ≤ (p : ℝ) * p := by exact_mod_cast hc.1.2
        _ ≤ Real.exp w * Real.exp w := mul_le_mul hw hw hp (hp.trans hw)
    have := loChain_sound t (2 * w) h l h2 hc.2
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this

theorem exp_halves (x : ℝ) (k : ℕ) : Real.exp x = Real.exp (2 ^ k * (x / 2 ^ k)) := by
  congr 1; field_simp

/-- **`exp x ≤ u` from a checked certificate.** -/
theorem expUp_sound {x u : ℚ} {c : Cert} (h : expUp x c u = true) : Real.exp (x : ℝ) ≤ u := by
  unfold expUp at h
  split at h
  · exact absurd h (by simp)
  · rename_i b t hbt
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨hy, hb⟩, hlen⟩, hch⟩ := h
    have hy' : |((x / 2 ^ c.k : ℚ) : ℝ)| ≤ 1 := by exact_mod_cast hy
    have hb' : Real.exp ((x / 2 ^ c.k : ℚ) : ℝ) ≤ b :=
      ExpBounds.exp_le_base _ _ hy' (by rw [← tupQ_cast]; exact_mod_cast hb)
    have := upChain_sound t _ b u hb' hch
    rw [hlen] at this
    rw [exp_halves (x : ℝ) c.k]
    simpa using this

/-- **`l ≤ exp x` from a checked certificate.** -/
theorem expLo_sound {x l : ℚ} {c : Cert} (h : expLo x c l = true) : (l : ℝ) ≤ Real.exp (x : ℝ) := by
  unfold expLo at h
  split at h
  · exact absurd h (by simp)
  · rename_i b t hbt
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨hy, hb⟩, hlen⟩, hch⟩ := h
    have hy' : |((x / 2 ^ c.k : ℚ) : ℝ)| ≤ 1 := by exact_mod_cast hy
    have hb' : (b : ℝ) ≤ Real.exp ((x / 2 ^ c.k : ℚ) : ℝ) :=
      ExpBounds.le_exp_base _ _ hy' (by rw [← tloQ_cast]; exact_mod_cast hb)
    have := loChain_sound t _ b l hb' hch
    rw [hlen] at this
    rw [exp_halves (x : ℝ) c.k]
    simpa using this

/-- **`log y ≤ q` from a checked certificate.** -/
theorem logUp_sound {y q : ℚ} {c : Cert} (h : logUp y q c = true) : Real.log (y : ℝ) ≤ q := by
  unfold logUp at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ExpBounds.log_le _ _ (by exact_mod_cast h.1) (expLo_sound h.2)

/-- **`q ≤ log y` from a checked certificate.** -/
theorem logLo_sound {y q : ℚ} {c : Cert} (h : logLo y q c = true) : (q : ℝ) ≤ Real.log y := by
  unfold logLo at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ExpBounds.le_log _ _ (by exact_mod_cast h.1) (expUp_sound h.2)

/-- Check of `exp x ≤ u` through a certificate at a larger point `xr` (`exp` is monotone); keeps
the certified values small when `x` is very negative. -/
def expUpLe (x xr : ℚ) (c : Cert) (u : ℚ) : Bool := decide (x ≤ xr) && expUp xr c u

/-- **`exp x ≤ u` from a checked certificate at a larger point.** -/
theorem expUpLe_sound {x xr u : ℚ} {c : Cert} (h : expUpLe x xr c u = true) :
    Real.exp (x : ℝ) ≤ u := by
  unfold expUpLe at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact (Real.exp_le_exp.2 (by exact_mod_cast h.1)).trans (expUp_sound h.2)

-- smoke test: `exp (3/2) ≤ 4.4817` with 6 halvings
example : Real.exp ((3 / 2 : ℚ) : ℝ) ≤ ((44817 / 10000 : ℚ) : ℝ) :=
  expUp_sound (c := ⟨6, [12796429 / 12500000, 104799101 / 100000000, 27457129 / 25000000,
    12062303 / 10000000, 72749577 / 50000000, 211700039 / 100000000, 224084533 / 50000000]⟩)
    (by decide +kernel)

end ExpCert
