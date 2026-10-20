import AKS.Sub800.R1Sep
import AKS.Sub800.R1Occ
import AKS.Sub800.R1GeomGen
import AKS.Chvatal.Bulk2Exists

/-! # Separator geometry and node networks at a generic R1 point (W2, step 3; R1-PROOF §4, §6)

An `R1Point` bundles the invariant scalars (`R1Scal`), the bulk certificate on the row window
`[Mlo, 2^q]`, the Batcher threshold `2^s`, two fringe classes `A` (interior, rising top, and
descending bottom with `R/c = 1`) and `B` (descending bottom with `R/c = 1/64`), and the rational
checks of `R1GeomGen` for them. Write `X = 2^(e−19)`, so `c = 2^19 X`:
* class `A`: `π/2 ∈ {63X, 64X}`, `524032 X ≤ a ≤ 525312 X`;
* class `B`: `π/2 = 63X`, `8176 X ≤ a ≤ 8192 X`.

Every stage after the root has depth `≤ 3 S(q)` (`R1Point.stage`, `S(q) = q(q+1)/2`):
* `spec_padded`: the padded separator of a fringe class;
* `spec_Bonly`: the B-only separator with `n = ⌈a/2^q⌉` (a large root);
* `spec_sorter`: Batcher's sort for `a ≤ 2^s` (`S(s) ≤ 3 S(q)`);
* `spec_root`: the package's B2 separator on `2^42` rows at `t = 0`, depth `≤ 2709`. -/

namespace R1T

open Chvatal Tapered945 Sub800

/-- A fringe class with a rational `δ_F`. -/
structure FClass where
  C : FringeCert
  dF : ℚ
  hδ : C.P.δ = (dF : ℝ)

/-- **A generic R1 point** at the schedule `(16, 32, 1/8)`. -/
structure R1Point where
  sc : R1Scal
  bulk : BulkCert
  /-- Batcher's sort serves the senders with `a ≤ 2^s`. -/
  s : ℕ
  A : FClass
  B : FClass
  hepsB : bulk.epsB = ((sc.epsB : ℚ) : ℝ)
  hJA : ((sc.epsF : ℚ) : ℝ) = 1 / (A.C.P.J : ℝ)
  hJB : ((sc.epsF : ℚ) : ℝ) = 1 / (B.C.P.J : ℝ)
  hs : 38 ≤ s
  batcher : bitonicDepthBudget s ≤ 3 * bitonicDepthBudget bulk.q
  /-- The stage depth pays for the root and the final layer: `2709 + 136 ≤ 15 · 3 S(q)`. -/
  stage_big : 2845 ≤ 15 * (3 * bitonicDepthBudget bulk.q)
  geomA63 : GeomOK A.C.P.f 63 524032 525312 (2 ^ s / 525312 + 1) bulk.Mlo bulk.q sc.mu A.dF sc.epsB
    sc.eta sc.gam
  geomA64 : GeomOK A.C.P.f 64 524032 525312 (2 ^ s / 525312 + 1) bulk.Mlo bulk.q sc.mu A.dF sc.epsB
    sc.eta sc.gam
  geomB : GeomOK B.C.P.f 63 8176 8192 (2 ^ s / 8192 + 1) bulk.Mlo bulk.q sc.mu B.dF sc.epsB sc.eta
    sc.gam
  bonly : BonlyOK s bulk.Mlo bulk.q sc.epsB sc.eta sc.gam
  /-- The root separator's budget: `ε_root/2 · 2^6 + 2^-36 ≤ (ε_B η + γ)/2`. -/
  root : (1 / 59000000 : ℚ) / 2 * 64 + 1 / 2 ^ 36 ≤ (sc.epsB * sc.eta + sc.gam) / 2

namespace R1Point

variable (P : R1Point)

/-- The depth of a stage after the root: three column sorts of height `2^q`. -/
def stage : ℕ := 3 * bitonicDepthBudget P.bulk.q

theorem epsB_nonneg : 0 ≤ P.bulk.epsB := by
  rw [P.hepsB]; exact_mod_cast P.sc.epsB_nonneg

end R1Point

/-! ### Geometry of the two classes -/

/-- `X ≥ 2^s/aH + 1` from `2^s < a ≤ aH X`. -/
theorem X0_le {s aH a X : ℕ} (hbig : 2 ^ s < a) (hH : a ≤ aH * X) : 2 ^ s / aH + 1 ≤ X := by
  rcases Nat.eq_zero_or_pos aH with h0 | hpos
  · subst h0; rw [zero_mul] at hH; exact absurd (lt_of_lt_of_le hbig hH) (Nat.not_lt_zero _)
  have : 2 ^ s / aH < X :=
    (Nat.div_lt_iff_lt_mul hpos).2 (lt_of_lt_of_le hbig (hH.trans (Nat.mul_comm _ _).le))
  exact this

/-- **Class `A`.** -/
theorem geomA (P : R1Point) (K a π X : ℕ) (hK : K = 63 ∨ K = 64) (hπ : π / 2 = K * X)
    (hL : 524032 * X ≤ a) (hH : a ≤ 525312 * X) (hbig : 2 ^ P.s < a) :
    ∃ m n : ℕ, 16 ≤ n ∧ a ≤ (m + 1) * n ∧ m * n ≤ a ∧ P.A.C.P.f ≤ m ∧ P.bulk.Mlo ≤ m + 1 ∧
      m + 1 ≤ 2 ^ P.bulk.q ∧ π / 2 ≤ a ∧ (P.A.C.P.f + 1) * n ≤ π / 2 ∧
      ((P.sc.mu : ℚ) : ℝ) * ((524288 * X : ℕ) : ℝ) ≤ (P.A.dF : ℝ) * ((P.A.C.P.f : ℝ) * n) ∧
      ((P.sc.epsB : ℚ) : ℝ) / 2 * (((m + 1 : ℕ) : ℝ) * n) + n ≤
        ((((P.sc.epsB * P.sc.eta + P.sc.gam) * ((524288 * X : ℕ) : ℚ) / 2 : ℚ)) : ℝ) := by
  have hX := X0_le hbig hH
  rcases hK with rfl | rfl
  · exact geom P.geomA63 a π X hπ hL hH hX
  · exact geom P.geomA64 a π X hπ hL hH hX

/-- **Class `B`.** -/
theorem geomB (P : R1Point) (a π X : ℕ) (hπ : π / 2 = 63 * X)
    (hL : 8176 * X ≤ a) (hH : a ≤ 8192 * X) (hbig : 2 ^ P.s < a) :
    ∃ m n : ℕ, 16 ≤ n ∧ a ≤ (m + 1) * n ∧ m * n ≤ a ∧ P.B.C.P.f ≤ m ∧ P.bulk.Mlo ≤ m + 1 ∧
      m + 1 ≤ 2 ^ P.bulk.q ∧ π / 2 ≤ a ∧ (P.B.C.P.f + 1) * n ≤ π / 2 ∧
      ((P.sc.mu : ℚ) : ℝ) * ((524288 * X : ℕ) : ℝ) ≤ (P.B.dF : ℝ) * ((P.B.C.P.f : ℝ) * n) ∧
      ((P.sc.epsB : ℚ) : ℝ) / 2 * (((m + 1 : ℕ) : ℝ) * n) + n ≤
        ((((P.sc.epsB * P.sc.eta + P.sc.gam) * ((524288 * X : ℕ) : ℚ) / 2 : ℚ)) : ℝ) :=
  geom P.geomB a π X hπ hL hH (X0_le hbig hH)

/-! ### Depths -/

theorem budget42 : bitonicDepthBudget 42 = 903 := by rw [bitonicDepthBudget_eq]

theorem padded_depth {q m n a : ℕ} (hn : 0 < n) (ha : a ≤ (m + 1) * n) (σ1 σ2 : Scramble (m + 1) n)
    (hm : m + 1 ≤ 2 ^ q) : (paddedPack2Net hn ha σ1 σ2).depth ≤ 3 * bitonicDepthBudget q := by
  refine (paddedPack2Net_depth_le hn ha σ1 σ2).trans
    ((physicalPack2Net_depth_le_budget _ _ hn σ1 σ2).trans ?_)
  exact Nat.mul_le_mul_left 3 (bitonicDepthBudget_mono (Nat.clog_le_of_le_pow hm))

/-! ### Node networks -/

open Classical in
/-- **The padded separator with fringe class `F`.** -/
theorem spec_padded (P : R1Point) (F : FClass) (hJ : ((P.sc.epsF : ℚ) : ℝ) = 1 / (F.C.P.J : ℝ))
    {a π : ℕ} (m n : ℕ) (hn16 : 16 ≤ n) (ha : a ≤ (m + 1) * n) (hlive : m * n ≤ a)
    (hfm : F.C.P.f ≤ m) (hmlo : P.bulk.Mlo ≤ m + 1) (hmhi : m + 1 ≤ 2 ^ P.bulk.q) (hπa : π / 2 ≤ a)
    (hfr : (F.C.P.f + 1) * n ≤ π / 2) (Jmax : ℕ) (hJm : Jmax ≤ F.C.P.jmax n) (EB : ℝ)
    (hEB : ((P.sc.epsB : ℚ) : ℝ) / 2 * (((m + 1 : ℕ) : ℝ) * n) + n ≤ EB) :
    ∃ net : ComparatorNetwork a, NodeSpecAll a π net EB Jmax ((P.sc.epsF : ℚ) : ℝ) ∧
      net.depth ≤ P.stage := by
  have hn : 0 < n := by omega
  obtain ⟨σ1, σ2, hgood⟩ := sep_pair_exists_of P.bulk F.C (m := m) (n := n)
    (by exact_mod_cast hmlo) hmhi hn16
  refine ⟨paddedPack2Net hn ha σ1 σ2, ?_, padded_depth hn ha σ1 σ2 hmhi⟩
  have := nodeSpec_padded F.C.P P.bulk.epsB P.epsB_nonneg hn ha hlive hfm σ1 σ2 hgood π hπa hfr
    Jmax hJm EB (by rw [P.hepsB]; exact hEB)
  rwa [hJ]

/-- **The B-only separator** for a large root, `n = ⌈a/2^q⌉` (no fringe). -/
theorem spec_Bonly (P : R1Point) {a : ℕ} (π : ℕ) (hbig : 2 ^ P.s < a) (e : ℕ)
    (ha : (a : ℚ) ≤ 4104 * 2 ^ e / 4096) (εF : ℝ) :
    ∃ net : ComparatorNetwork a, NodeSpecAll a π net
      ((((P.sc.epsB * P.sc.eta + P.sc.gam) * 2 ^ e / 2 : ℚ)) : ℝ) 0 εF ∧ net.depth ≤ P.stage := by
  obtain ⟨m, n, hn16, ha', hmlo, hmhi, hEB⟩ := bonly P.bonly a e hbig ha
  have hnpos : 0 < n := by omega
  obtain ⟨σ1, σ2, hgood⟩ := sep_pair_exists_of P.bulk P.A.C (m := m) (n := n)
    (by exact_mod_cast hmlo) hmhi hn16
  refine ⟨paddedPack2Net hnpos ha' σ1 σ2, ?_, padded_depth hnpos ha' σ1 σ2 hmhi⟩
  exact nodeSpec_Bonly hnpos ha' σ1 σ2 P.bulk.epsB P.epsB_nonneg hgood.1.2.2.2 hgood.2.2.2.2 π _ εF
    (by rw [P.hepsB]; exact hEB)

/-- **Batcher's sort** for `a ≤ 2^s`. -/
theorem spec_sorter (P : R1Point) {a : ℕ} (π : ℕ) (ha : a ≤ 2 ^ P.s) {EB εF : ℝ} (hEB : 0 ≤ EB)
    (hε : 0 < εF) {Jmax : ℕ} (hJ : Jmax ≤ π / 2) :
    ∃ net : ComparatorNetwork a, NodeSpecAll a π net EB Jmax εF ∧ net.depth ≤ P.stage := by
  refine ⟨bitonicNetwork a, nodeSpec_sorter π _ (bitonicNetwork_sorts a) hEB hε hJ, ?_⟩
  refine (bitonicNetwork_depth_le_budget a).trans ?_
  exact (bitonicDepthBudget_mono (Nat.clog_le_of_le_pow ha)).trans P.batcher

/-- **The root at `t = 0`**: the package's B2 separator on `2^42` rows. -/
theorem spec_root {d : ℕ} (hd : 12 ≤ d) (π : ℕ) (EB εF : ℝ)
    (hEB : (1 / 59000000 : ℝ) / 2 * (16 : ℝ) ^ d + 2 ^ (4 * d - 42) ≤ EB) :
    ∃ net : ComparatorNetwork (16 ^ d), NodeSpecAll (16 ^ d) π net EB 0 εF ∧ net.depth ≤ 2709 := by
  set n := 2 ^ (4 * d - 42) with hn
  have hn16 : 16 ≤ n := by
    rw [hn, show (16 : ℕ) = 2 ^ 4 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnpos : 0 < n := by omega
  have hmn : 16 ^ d = 2 ^ 42 * n := by
    rw [hn, ← pow_add, show 42 + (4 * d - 42) = 4 * d by omega, pow_mul]; norm_num
  have ha : 16 ^ d ≤ 2 ^ 42 * n := hmn.le
  obtain ⟨σ1, σ2, ⟨-, hB⟩, ⟨-, hB'⟩⟩ := ExistsScrambleSeparator_twoSided_B2 (m := 2 ^ 42) (n := n)
    le_rfl hn16 (fun _ => True) (by
      simp only [not_true_eq_false, Finset.filter_false, Finset.card_empty, Nat.cast_zero]
      positivity)
  refine ⟨paddedPack2Net hnpos ha σ1 σ2, ?_, ?_⟩
  · refine nodeSpec_Bonly hnpos ha σ1 σ2 (1 / 59000000) (by norm_num) hB hB' π EB εF (le_trans ?_ hEB)
    have : ((2 ^ 42 : ℕ) : ℝ) * (n : ℝ) = (16 : ℝ) ^ d := by exact_mod_cast hmn.symm
    rw [this, hn]; push_cast; exact le_refl _
  · refine (paddedPack2Net_depth_le hnpos ha σ1 σ2).trans
      ((physicalPack2Net_depth_le_budget _ _ hnpos σ1 σ2).trans ?_)
    rw [Nat.clog_pow 2 42 (by norm_num), budget42]

end R1T
