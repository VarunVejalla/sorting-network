module

public import AKS.Chvatal.NodeSpec
public import AKS.Chvatal.Theorem51Core
public import AKS.Chvatal.Lemma62Ratio
public import AKS.Chvatal.ExecPlacement
public import AKS.Chvatal.StageKernel

@[expose] public section

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

/-- The paper's actual (4.4): `μ ≤ ½·δ_F·(Aνk−1)/(A²k²)`, `δ_F = 128/4095`; gives `μ c ≤ δ_F·π/2`. -/
theorem cond44_real : invMu ≤ (1 / 2) * (128 / 4095 : ℚ) * (4095 : ℚ) / 68719476736 := by
  unfold invMu; norm_num

theorem mu_real_mul_le_one (c : ℚ) (hc : c ≤ 1073741824) : invMu * c < 1 := by
  unfold invMu
  linarith

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

/-- BadSendField property definition. -/
def BadSendField {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht : t ≤ tf7 d) : Prop :=
  ∀ (b : KBag 64 d) (hb : 1 ≤ b.l),
    ((b.strangers 1 id (fromParentK (flowSizes7 d hd) nets v t b) : ℕ) : ℚ) ≤
      parentOutMass d (execPlacement (flowSizes7 d hd) nets v t ht) id b hb +
        sibMassBound d t b hb +
        invEpsB * capacity d (b.l - 1) t +
        slackBound d t b hb

/-- FringeSendField property definition. -/
def FringeSendField {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht : t ≤ tf7 d) : Prop :=
  ∀ (b : KBag 64 d) (r : ℕ) (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) id (fromParentK (flowSizes7 d hd) nets v t b) : ℕ) : ℚ) ≤
      invEpsF *
        (((b.parent).strangers r id
          ((execPlacement (flowSizes7 d hd) nets v t ht).regs (b.parent))
          : ℕ) : ℚ)

end Chvatal
