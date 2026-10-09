module

public import AKS.Chvatal.FlowSizes7
public import AKS.Chvatal.WireFlow
public import AKS.Chvatal.NodeSpec
public import AKS.Chvatal.Theorem51Core
public import AKS.Chvatal.Lemma62Ratio
public import AKS.Chvatal.Params
public import AKS.Chvatal.ExecPlacement
public import AKS.Chvatal.StageKernel

@[expose] public section

/-! Shared setup for the real-network stage kernel: `RealSpecs` (every node that sends wires down
runs a network meeting the Theorem 5.1 guarantee `NodeSpec` with `EB = ε_B a/2`, `Jmax = ⌊δ_F π/2⌋`,
`ε_F = 1/(8·10^7)`), the invariant parameters `invariantReal`, and the two routing fields. -/

namespace Chvatal

/-- Intrusion budget `EB`: `ε_B·a/2`, with the root's exceptional `ε_*` at `t = 0`. -/
noncomputable def specEB (t a : ℕ) : ℝ :=
  (if t = 0 then paperRootEpsB else paperOrdinaryEpsB) * (a : ℝ) / 2

/-- Fringe range `Jmax = ⌊δ_F · π/2⌋`, `δ_F = 128/4095`. -/
noncomputable def specJmax (π : ℕ) : ℕ := ⌊(128 / 4095 : ℝ) * ((π : ℝ) / 2)⌋₊

/-- Every node that sends wires down runs a network meeting the node guarantee. -/
def RealSpecs {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n) : Prop :=
  ∀ (t : ℕ) (q : KBag 64 d), t < tf7 d → 0 < (flowSizes7 d hd).down q.l t →
    NodeSpec (wireSets (flowSizes7 d hd) t q).card ((flowSizes7 d hd).up q.l t)
      ((flowSizes7 d hd).down q.l t) (nets t q (wireSets (flowSizes7 d hd) t q).card)
      (specEB t ((flowSizes7 d hd).a q.l t)) (specJmax ((flowSizes7 d hd).up q.l t)) eps

/-- Invariant parameters for the real network: the paper-ordinary budgets, but with
`μ = (1 - 2^-10)·2^-30`, which keeps (4.1)–(4.5) true and makes `μ·c < 1` whenever `c ≤ 2^30`. -/
def invariantReal : InvariantParams where
  mu := 1023 / 1099511627776
  delta := invariant7.delta
  epsB := 1 / 80000000
  epsF := invariant7.epsF
  deltaF := invariant7.deltaF
  epsStar := (1023 / 1099511627776) / 64
  hmu_pos := by norm_num
  hdelta_pos := invariant7.hdelta_pos
  hdelta_lt := invariant7.hdelta_lt
  hepsB_nonneg := by norm_num
  hepsF_nonneg := invariant7.hepsF_nonneg
  hdeltaF_pos := invariant7.hdeltaF_pos
  hdeltaF_lt := invariant7.hdeltaF_lt
  hepsStar_nonneg := by norm_num

theorem separatorConds_real : SeparatorConds params7 invariantReal := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold Cond41 params7 invariantReal; norm_num
  · unfold Cond42 siblingFactor slackCoeff params7 invariantReal invariant7; norm_num
  · unfold Cond43 params7 invariantReal; norm_num
  · unfold Cond44 params7 invariantReal invariant7; norm_num
  · unfold Cond45 params7 invariantReal invariant7; norm_num

/-- The paper's actual (4.4): `μ ≤ ½·δ_F·(Aνk−1)/(A²k²)`; gives `μ c ≤ δ_F·π/2`. -/
theorem cond44_real :
    invariantReal.mu ≤ (1 / 2) * invariantReal.deltaF * (4095 : ℚ) / 68719476736 := by
  unfold invariantReal invariant7; norm_num

theorem mu_real_mul_le_one (c : ℚ) (hc : c ≤ 1073741824) : invariantReal.mu * c < 1 := by
  unfold invariantReal
  show (1023 / 1099511627776 : ℚ) * c < 1
  linarith

theorem capacity_params7_nonneg (d i t : ℕ) : 0 ≤ capacity params7 d i t :=
  (capacity_pos params7 d i t).le

/-- Every bag below the root is a child of some node. -/
theorem exists_parent_child {d : ℕ} (b : KBag 64 d) (hb : 1 ≤ b.l) :
    ∃ (q : KBag 64 d) (hq : q.l < d) (j : Fin 64), q.child j.val j.isLt hq = b := by
  have hqlt : (b.parent (by norm_num : 1 ≤ 64)).l < d := by
    have := b.hl
    show b.l - 1 < d
    omega
  exact ⟨_, hqlt, ⟨b.x % 64, Nat.mod_lt _ (by norm_num)⟩, KBag.parent_child b hb (by norm_num) hqlt⟩

/-- If the parent sends nothing down, nothing arrives from it. -/
theorem fromParentK_eq_empty {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (b : KBag 64 d)
    (h0 : (flowSizes7 d hd).down (b.l - 1) t = 0) :
    fromParentK (flowSizes7 d hd) nets v t b = ∅ := by
  unfold fromParentK
  rw [Finset.image_eq_empty]
  unfold downSet blockOf
  rw [h0]
  exact Finset.filter_false_of_mem fun w _ h => by omega

/-- Field shape of `StageKernel.hBadSend0` for the real network (`t ≥ 1` handled by callers). -/
def BadSendField {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht : t ≤ tf7 d) : Prop :=
  ∀ (b : KBag 64 d) (hb : 1 ≤ b.l),
    ((b.strangers 1 id (fromParentK (flowSizes7 d hd) nets v t b) (br_ge_one params7) : ℕ) : ℚ) ≤
      parentOutMass params7 d (execPlacement (flowSizes7 d hd) nets v t ht) id b hb +
        sibMassBound params7 invariantReal d t b hb +
        invariantReal.epsB * capacity params7 d (b.l - 1) t +
        slackBound params7 d t b hb

/-- Field shape of `StageKernel.hFringeSend` (with `fringeSent src := ε_F·src`). -/
def FringeSendField {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht : t ≤ tf7 d) : Prop :=
  ∀ (b : KBag 64 d) (r : ℕ) (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) id (fromParentK (flowSizes7 d hd) nets v t b) (br_ge_one params7) : ℕ) : ℚ) ≤
      invariantReal.epsF *
        (((b.parent (br_ge_one params7)).strangers r id
          ((execPlacement (flowSizes7 d hd) nets v t ht).regs (b.parent (br_ge_one params7)))
          (br_ge_one params7) : ℕ) : ℚ)

end Chvatal
