module

public import AKS.Chvatal.Lemma41Real
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # Per-bag, non-uniform flow table (`FlowTableB`) and its numeric facts (`FlowFacts`)

Stage 1a of the slack-free (design D2) refactor; see `upper-bound/experiments/slackfree/INTERFACE.md`
and `GATE0.md`.  Definitions only (no numerics): the uniform Chvátal table is shown to satisfy this
interface in `FlowTableBUniform.lean` (`flowFacts_current`).

* `FlowTableB d tf` replaces `FlowSizes d tf`: sizes are per **bag** (not per level) and each
  node sends its own amount `down t b j` to child `j` (sums replace `64 *`).
* `FlowFacts` replaces `NodeShape`/`NodeFacts`/`node_facts`/`hwires7`/`hpar7`/`nodeGeom_exists`/
  `flowA7_tf`.  It is **slack aware**: `up` (π′) is only assumed to be at least `upFrac · cap`
  (never an exact value or an upper bound); all rounding is absorbed by `η` and `rT`.
-/

namespace Chvatal

open Finset

variable {d tf : ℕ}

/-- Per-bag integer flow table (non-uniform blocks).  Generic; no numerics.

Consumers today (of the per-level `FlowSizes` analogue):
* `ha_root`, `ha_init`: `RealInduction.P_one`, `total_mass` (`Wires31`), `wireSets` at `t = 0`;
* `hup_even`: `WireFlow.upSet_card` (`wireSets_card`), `BadSendReal`;
* `hup_root`, `hdown_leaf`: `WireFlow.wireSets_card`, `total_mass`, `FringeSendReal`;
* `hsplit`: `WireFlow.downSet_card`/`wireSets_card`, `BadSendReal.window_real`, `FringeSendField`;
* `hcons`: `WireFlow.wireSets_card`/`wireSets_inv`, `total_mass`. -/
structure FlowTableB (d tf : ℕ) where
  /-- wires at bag `b` at time `t` -/
  a : ℕ → KBag 64 d → ℕ
  /-- `π_b(t)`: wires sent to the parent (`π′` of the slack-free rule; not Chvátal's exact value) -/
  up : ℕ → KBag 64 d → ℕ
  /-- `τ_{b,j}(t)`: wires sent to child `j` -/
  down : ℕ → KBag 64 d → Fin 64 → ℕ
  ha_root : a 0 (KBag.root 64 d) = 64 ^ d
  ha_init : ∀ b, b ≠ KBag.root 64 d → a 0 b = 0
  hup_even : ∀ t b, t < tf → 2 ∣ up t b
  hup_root : ∀ t, t < tf → up t (KBag.root 64 d) = 0
  hdown_leaf : ∀ t b j, t < tf → b.l = d → down t b j = 0
  hsplit : ∀ t b, t < tf → a t b = up t b + ∑ j, down t b j
  hcons : ∀ t b, t < tf → a (t + 1) b =
    (if 1 ≤ b.l then down t b.parent ⟨b.x % 64, Nat.mod_lt _ (by norm_num)⟩ else 0) +
    (if h : b.l < d then ∑ j : Fin 64, up t (b.child j j.isLt h) else 0)

namespace FlowTableB

variable (F : FlowTableB d tf)

/-- Prefix offsets: child `j` gets the cells `[π/2 + off j, π/2 + off (j+1))` of the middle.
(`WireFlow.downSet`, `ExecPlacement.mem_image_downSet_iff`, `NodeKeys.intruder_keys`,
`BadSendReal`.) -/
def off (t : ℕ) (b : KBag 64 d) (j : ℕ) : ℕ :=
  ∑ i : Fin 64 with i.val < j, F.down t b i

/-- Suffix sum: the total sent to children strictly above `j`
(`NodeKeys.intruder_keys`: the window of child `j` ends at `a − π/2 − sufOff j`). -/
def sufOff (t : ℕ) (b : KBag 64 d) (j : ℕ) : ℕ :=
  ∑ i : Fin 64 with j < i.val, F.down t b i

/-- Deficit `G_b = R_b − W_b` (the Lemma 3.1 quantity): the keys addressed to the subtree of `b`
(`64^(d − b.l)` of them) minus the wires currently held in it.  In `ℚ` so that no sign is needed.
Replaces `hwires7` / `NodeFacts.Δ` (`Lemma41Real.keys_below_child_le`, `BadSendField`). -/
def deficit (t : ℕ) (b : KBag 64 d) : ℚ :=
  (64 : ℚ) ^ (d - b.l) - ∑ z ∈ subtreeBags 64 d (by norm_num) b, (F.a t z : ℚ)

/-- `θ_i = G_{child i} − τ_i` of the `i`-th child of `b` (SLACKFREE §3). -/
def theta (t : ℕ) (b : KBag 64 d) (hb : b.l < d) (i : Fin 64) : ℚ :=
  F.deficit t (b.child i i.isLt hb) - F.down t b i

/-- The one-sided Lemma 4.2 residual of window `j`: the part of the lower (resp. upper) cumulative
deficit that the fringe `π/2` does not absorb.  Replaces `NodeFacts.half`/`slack`. -/
def residAt (t : ℕ) (b : KBag 64 d) (hb : b.l < d) (j : Fin 64) : ℚ :=
  max 0 ((∑ i : Fin 64 with i < j, F.theta t b hb i) - (F.up t b : ℚ) / 2) +
  max 0 ((∑ i : Fin 64 with j < i, F.theta t b hb i) - (F.up t b : ℚ) / 2)

end FlowTableB

/-- Geometry of a separator node with `a` wires, `up` to the parent, `down j` to child `j`:
`m × n` matrix, fringe `f` rows at each end and per-child blocks `b j` rows
(`m = 2f + Σ b j`).  Replaces `NodeGeom`.  Generic: `NodeGeom a up d` is the case
`b j = b`, `down j = b n`. -/
structure NodeGeomV (a up : ℕ) (down : Fin 64 → ℕ) where
  m : ℕ
  n : ℕ
  f : ℕ
  b : Fin 64 → ℕ
  hm : m = 2 * f + ∑ j, b j
  ha : a = m * n
  hup : up = 2 * f * n
  hdown : ∀ j, down j = b j * n
  hm1 : 2 ^ 42 < m
  hm2 : m ≤ 2 ^ 43
  hn : 16 ≤ n
  hf : f = 0 ∨ (131040 ≤ f ∧ Even f)

/-- Numeric facts of a flow table `F` for capacity function `cap l t` (`Schedule7.capacity d`),
meeting level `lam`, and constants:
* `η` bounds `a / cap` (1 today), `rT` bounds the Lemma 4.2 residual per capacity
  (`slackCoeff` today), `upFrac` is the lower fringe floor (`4095 / 2^36` today) and `topCap` the
  top-descending cut-off (`2^30` today).

Every field is generic in the table (nothing mentions equal blocks); `up` is never constrained
from above (slack-aware). -/
structure FlowFacts (F : FlowTableB d tf) (cap : ℕ → ℕ → ℚ) (lam : ℕ)
    (η rT upFrac topCap : ℚ) : Prop where
  /-- wrong-parity bags are empty (`Wires31.hpar7`; consumed by `Lemma41Real.subtree_bad_le_parity`
  via `BadSendField.hM_keys`, `Wires31.total_mass`). -/
  parity : ∀ t b, 1 ≤ t → t ≤ tf → b.l % 2 ≠ t % 2 → F.a t b = 0
  /-- `a ≤ η · cap` at senders (`NodeFacts.a_le`; consumed by `BadSendField.badSendField_real`
  through `hEB`, and `StageKernel.cond42_scaled`).  `η = 1` today. -/
  a_le : ∀ t b, 1 ≤ t → t < tf → 0 < ∑ j, F.down t b j → (F.a t b : ℚ) ≤ η * cap b.l t
  /-- the one-sided Lemma 4.2 residual (`NodeFacts.half`/`slack`; consumed by
  `BadSendField.badSendField_real`, giving `slackBound := rT * cap` of `StageKernel.cond42_scaled`). -/
  resid : ∀ t b (hb : b.l < d) (j : Fin 64), 1 ≤ t → t < tf → 0 < F.down t b j →
    F.residAt t b hb j ≤ rT * cap b.l t
  /-- fringe dichotomy (`node_facts` 2nd component; consumed by
  `FringeSendField.jmax_ok`). -/
  fringe : ∀ t b, 1 ≤ t → t < tf → 0 < ∑ j, F.down t b j →
    (F.up t b = 0 ∧ (b.l = 0 ∨ cap b.l t ≤ topCap)) ∨ upFrac * cap b.l t ≤ F.up t b
  /-- separator geometry of big senders (`NodeGeom.nodeGeom_exists`; consumed by
  `RealNets.nodeGood_exists`). -/
  geom : ∀ t b, 1 ≤ t → t < tf → 0 < ∑ j, F.down t b j → 2 ^ 63 < F.a t b →
    Nonempty (NodeGeomV (F.a t b) (F.up t b) (F.down t b))
  /-- the root at `t = 0` (`RealNets.nodeGood_exists` root case, `RealInduction.P_one`). -/
  root : F.up 0 (KBag.root 64 d) = 0 ∧ ∀ j, F.down 0 (KBag.root 64 d) j = 64 ^ (d - 1)
  /-- at `t = 1` only level `1` is occupied (`RealInduction.P_one`). -/
  one : ∀ b, b.l ≠ 1 → F.a 1 b = 0
  /-- the final distribution: every bag at level `lam` holds its whole subtree's keys
  (`RealBlocks.flowA7_tf`, `finalS_card`, `RealInduction.real_purity`). -/
  final : ∀ b, F.a tf b = if b.l = lam then 64 ^ (d - lam) else 0

end Chvatal
