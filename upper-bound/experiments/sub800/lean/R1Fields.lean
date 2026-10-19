import R1StageKernel

/-! # The send fields from the node specifications (W1, step 11)

`R1Specs F nets`: every sender's network meets `NodeSpecAll` with
`EB = (ε_B η + 0.1 μ) c / 2` and `Jmax = ⌊μ c⌋` (`0` at the root), `c = c(q.l, t)`.

`badSend_field`: with the parity and residual facts of the flow table and `P` at stage `t`, the
order-0 strangers each node receives from its parent are at most the parent's order-0 strangers
plus `B0 · c(parent)` (the `hBad` hypothesis of `realStageKernel`). -/

namespace R1T

open Finset
open Chvatal (KBag Placement subtreeBags)

variable {d tf : ℕ}

/-- The separator budget of a sender. -/
noncomputable def EBv (d t l : ℕ) : ℝ := (((epsB * eta + gammaRes) * cap d l t / 2 : ℚ) : ℝ)

/-- The fringe range of a sender. -/
noncomputable def JmaxR (d t l : ℕ) : ℕ := if l = 0 then 0 else ⌊mu * cap d l t⌋₊

/-- Node specifications of all senders. -/
def R1Specs (F : FlowTableB d tf) (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n) :
    Prop :=
  ∀ t (q : KBag 16 d), t < tf → 0 < ∑ j, F.down t q j →
    NodeSpecAll (wireSets F t q).card (F.up t q) (nets t q (wireSets F t q).card)
      (EBv d t q.l) (JmaxR d t q.l) (epsF : ℝ)

/-- The children's deficits of `q`, as a function on `ℕ`. -/
noncomputable def Gd (F : FlowTableB d tf) (t : ℕ) (q : KBag 16 d) (hq : q.l < d) (h : ℕ) : ℝ :=
  if hh : h < 16 then ((F.deficit t (q.child h hh hq) : ℚ) : ℝ) else 0

/-- The residual fact of the flow table (design P: (I4)). -/
def ResidFact (F : FlowTableB d tf) : Prop :=
  ∀ t (q : KBag 16 d) (hq : q.l < d) (j : ℕ), j < 16 → t < tf → 0 < ∑ i, F.down t q i →
    residG (F.up t q) (downN F t q) (Gd F t q hq) j ≤ ((rstar * cap d q.l t : ℚ) : ℝ)

/-- The parity fact: wrong-parity bags hold no wires. -/
def ParityFact (F : FlowTableB d tf) (t : ℕ) : Prop :=
  ∀ b : KBag 16 d, b.l % 2 ≠ t % 2 → F.a t b = 0

theorem fromParentK_eq_empty (F : FlowTableB d tf)
    (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (16 ^ d))) (t : ℕ) (b : KBag 16 d)
    (h0 : ∑ i, F.down t b.parent i = 0) : fromParentK F nets v t b = ∅ := by
  unfold fromParentK
  rw [Finset.image_eq_empty]
  unfold downSetB blockOf
  have hoff : ∀ j, F.off t b.parent j = 0 := fun j => by
    unfold FlowTableB.off
    refine Finset.sum_eq_zero fun i _ => ?_
    exact (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ _)
  rw [hoff, hoff]
  exact Finset.filter_false_of_mem fun w _ h => by omega

/-- **The order-0 send field.** -/
theorem badSend_field (F : FlowTableB d tf)
    (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (16 ^ d))) (t : ℕ) (ht : t + 1 ≤ tf)
    (hspec : R1Specs F nets) (hpar : ParityFact F t) (hres : ResidFact F)
    (hP : OutsiderBoundLe d t (execPlacement F nets v t (by omega)) id)
    (b : KBag 16 d) (hb : 1 ≤ b.l) :
    ((b.strangers 1 id (fromParentK F nets v t b) : ℕ) : ℚ) ≤
      ((b.parent).strangers 1 id ((execPlacement F nets v t (by omega)).regs b.parent) : ℚ) +
        B0 * cap d (b.l - 1) t := by
  classical
  have ht' : t < tf := by omega
  set q := b.parent with hqdef
  have hql : q.l = b.l - 1 := rfl
  have hq : q.l < d := by have := b.hl; omega
  have hc := (cap_pos d q.l t).le
  have hB0 : 0 ≤ B0 := by unfold B0 sib gammaRes mu delta rstar epsB eta; norm_num
  have hnn : (0 : ℚ) ≤ B0 * cap d (b.l - 1) t := by rw [← hql]; positivity
  by_cases hsend : ∑ i, F.down t q i = 0
  · rw [fromParentK_eq_empty F nets v t b hsend, KBag.strangers_empty, Nat.cast_zero]
    have : (0 : ℚ) ≤ ((b.parent).strangers 1 id ((execPlacement F nets v t (by omega)).regs b.parent) : ℚ) :=
      Nat.cast_nonneg _
    linarith
  have hpos : 0 < ∑ i, F.down t q i := Nat.pos_of_ne_zero hsend
  -- `q` is occupied, hence on the parity of `t`
  have hqpar : q.l % 2 = t % 2 := by
    by_contra hne
    have h0 := hpar q hne
    rw [F.hsplit t q ht'] at h0
    omega
  set j := b.x % 16 with hj
  have hj16 : j < 16 := Nat.mod_lt _ (by norm_num)
  have hbq : b = q.child j hj16 hq := KBag.eq_parent_child b hb hq
  set ρ : ℝ := ((mu * sib * cap d q.l t : ℚ) : ℝ) with hρdef
  have hρ : 0 ≤ ρ := by
    rw [hρdef]; have := mu_pos; have := sib_pos; exact_mod_cast (by positivity : (0 : ℚ) ≤ _)
  have hM : ∀ h (hh : h < 16),
      ((((execPlacement F nets v t ht'.le).regs q).filter fun κ =>
        (q.child h hh hq).Native κ id).card : ℝ) ≤ Gd F t q hq h + ρ := by
    intro h hh
    have h1 := keys_below_child_le d t (execPlacement F nets v t ht'.le) (fun z => F.a t z)
      (fun z => execPlacement_card F nets v t ht'.le z) hpar hP q hq h hh hqpar
    have e : F.deficit t (q.child h hh hq) = (16 : ℚ) ^ (d - q.l - 1) -
        ∑ z ∈ subtreeBags 16 d (by norm_num) (q.child h hh hq), (F.a t z : ℚ) := by
      unfold FlowTableB.deficit
      rw [show (q.child h hh hq).l = q.l + 1 from rfl, show d - (q.l + 1) = d - q.l - 1 by omega]
    rw [← e] at h1
    unfold Gd
    rw [dif_pos hh, hρdef]
    exact_mod_cast h1
  have hπe : 2 ∣ F.up t q := by
    rcases F.hup_even t q ht' with h | h
    · exact h
    · have := F.hsplit t q ht'; omega
  have hmain := bad_send0_real_gen F nets v t ht' q hq j hj16 (EBv d t q.l) (JmaxR d t q.l)
    (epsF : ℝ) (Gd F t q hq) ρ hρ hπe (hspec t q ht' hpos) hM
  have hr := hres t q hq j hj16 ht' hpos
  rw [← hbq] at hmain
  have hgoal : ((b.strangers 1 id (fromParentK F nets v t b) : ℕ) : ℝ) ≤
      ((q.strangers 1 id ((execPlacement F nets v t ht'.le).regs q) : ℕ) : ℝ) +
        ((B0 * cap d (b.l - 1) t : ℚ) : ℝ) := by
    refine hmain.trans ?_
    rw [← hql]
    have hEB : 2 * EBv d t q.l = (((epsB * eta + gammaRes) * cap d q.l t : ℚ) : ℝ) := by
      unfold EBv; push_cast; ring
    have hB0e : ((B0 * cap d q.l t : ℚ) : ℝ) = 15 * ρ + ((rstar * cap d q.l t : ℚ) : ℝ) +
        (((epsB * eta + gammaRes) * cap d q.l t : ℚ) : ℝ) := by
      rw [hρdef]; unfold B0; push_cast; ring
    linarith
  exact_mod_cast hgoal

/-- **The fringe send field.** -/
theorem fringeSend_field (F : FlowTableB d tf)
    (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (16 ^ d))) (t : ℕ) (ht : t + 1 ≤ tf)
    (hspec : R1Specs F nets)
    (hP : OutsiderBoundLe d t (execPlacement F nets v t (by omega)) id)
    (b : KBag 16 d) (r : ℕ) (hr1 : 1 ≤ r) (hrd : r ≤ d) (hb : 1 ≤ b.l) :
    ((b.strangers (r + 1) id (fromParentK F nets v t b) : ℕ) : ℚ) ≤
      epsF * ((b.parent).strangers r id ((execPlacement F nets v t (by omega)).regs b.parent) : ℚ) := by
  classical
  have ht' : t < tf := by omega
  set q := b.parent with hqdef
  have hq : q.l < d := by have := b.hl; show b.l - 1 < d; omega
  have hεF : (0 : ℚ) ≤ epsF := epsF_nonneg
  by_cases hsend : ∑ i, F.down t q i = 0
  · rw [fromParentK_eq_empty F nets v t b hsend, KBag.strangers_empty, Nat.cast_zero]
    exact mul_nonneg hεF (Nat.cast_nonneg _)
  have hpos : 0 < ∑ i, F.down t q i := Nat.pos_of_ne_zero hsend
  set j := b.x % 16 with hj
  have hj16 : j < 16 := Nat.mod_lt _ (by norm_num)
  have hbq : b = q.child j hj16 hq := KBag.eq_parent_child b hb hq
  have hJ : q.strangers r id ((execPlacement F nets v t ht'.le).regs q) ≤ JmaxR d t q.l := by
    unfold JmaxR
    split_ifs with h0
    · rw [KBag.strangers_eq_zero_of_lt_order q r id _ (by norm_num) hr1 (by omega)]
    · apply Nat.le_floor
      have h1 := hP q (r - 1) (by omega)
      rw [Nat.sub_add_cancel hr1] at h1
      have hd1 : delta ^ (r - 1) ≤ 1 := pow_le_one₀ delta_pos.le (by unfold delta; norm_num)
      have hc := (cap_pos d q.l t).le
      have : mu * delta ^ (r - 1) * cap d q.l t ≤ mu * cap d q.l t := by
        have := mu_pos.le
        calc mu * delta ^ (r - 1) * cap d q.l t = mu * cap d q.l t * delta ^ (r - 1) := by ring
          _ ≤ mu * cap d q.l t * 1 := mul_le_mul_of_nonneg_left hd1 (by positivity)
          _ = _ := by ring
      exact h1.trans this
  have hπe : 2 ∣ F.up t q := by
    rcases F.hup_even t q ht' with h | h
    · exact h
    · have := F.hsplit t q ht'; omega
  have hmain := fringe_send_real_gen F nets v t ht' q hq ⟨j, hj16⟩ r hr1 (EBv d t q.l) (JmaxR d t q.l)
    (epsF : ℝ) hπe (hspec t q ht' hpos) hJ
  rw [← hbq] at hmain
  have : ((b.strangers (r + 1) id (fromParentK F nets v t b) : ℕ) : ℝ) ≤
      ((epsF * ((q.strangers r id ((execPlacement F nets v t ht'.le).regs q) : ℕ) : ℚ) : ℚ) : ℝ) := by
    push_cast; exact hmain
  exact_mod_cast this

end R1T
