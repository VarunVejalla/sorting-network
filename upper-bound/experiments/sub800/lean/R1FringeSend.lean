import R1Kernel
import AKS.Chvatal.FringeSendReal

/-! # Fringe send for the real network at `k = 16`, unequal blocks (W1, step 9)

Port of UB-12's `fringe_send_real` (generic over `FlowTableB`) with `NodeSpecAll`; the window of
child `j` lies in the middle `[π/2, a − π/2)` because `off (j+1) ≤ off 16 = a − π`. -/

namespace R1T

open Finset
open Chvatal (KBag rk keySet card_keySet exec_mem_keySet exec_keySet_injective cellOf cellOf_apply
  filter_image_cellOf strangers_split sent_outside_le)

theorem native_id_iff {d : ℕ} (A : KBag 16 d) (κ : Fin (16 ^ d)) :
    A.Native κ id ↔ A.lo ≤ (κ : ℕ) ∧ (κ : ℕ) < A.hi := by
  simpa using KBag.native_iff A κ id (by norm_num)

theorem strangers_eq_filter {d : ℕ} (q : KBag 16 d) (r : ℕ) (hr : 1 ≤ r)
    (S : Finset (Fin (16 ^ d))) :
    q.strangers r id S = (S.filter fun κ : Fin (16 ^ d) =>
      ¬ ((q.ancestor (r - 1)).lo ≤ (κ : ℕ) ∧ (κ : ℕ) < (q.ancestor (r - 1)).hi)).card := by
  unfold KBag.strangers
  congr 1
  refine Finset.filter_congr fun κ _ => ?_
  simp [KBag.Strange, native_id_iff, Nat.one_le_iff_ne_zero.1 hr]


section Real

variable {d tf : ℕ}

/-- **Lemma 4.4 (parent part), real network.**  The order-`(r+1)` outsiders among the keys
sent from `q` to its child `b = q.child j` at stage `t` number at most `εF` times the order-`r`
outsiders among the keys on `q`, given the node specification (Property F) and
`strangers ≤ Jmax`. -/
theorem fringe_send_real_gen (F : FlowTableB d tf)
    (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (16 ^ d))) (t : ℕ) (ht : t < tf) (q : KBag 16 d) (hq : q.l < d)
    (j : Fin 16) (r : ℕ) (hr : 1 ≤ r) (EB : ℝ) (Jmax : ℕ) (εF : ℝ) (hπe : 2 ∣ F.up t q)
    (hspec : NodeSpecAll (wireSets F t q).card (F.up t q)
      (nets t q (wireSets F t q).card) EB Jmax εF)
    (hJ : q.strangers r id ((execPlacement F nets v t ht.le).regs q) ≤ Jmax) :
    (((q.child j.val j.isLt hq).strangers (r + 1) id (fromParentK F nets v t
        (q.child j.val j.isLt hq)) : ℕ) : ℝ) ≤
      εF * ((q.strangers r id ((execPlacement F nets v t ht.le).regs q) : ℕ) : ℝ) := by
  classical
  set s := wireSets F t q with hs
  set π := F.up t q
  set xr : Fin s.card → Fin (16 ^ d) :=
    fun i => X F nets v t (s.orderEmbOfFin rfl i) with hxrdef
  have hxr : Function.Injective xr := fun i i' h =>
    (s.orderEmbOfFin rfl).injective (X_injective F nets v t h)
  set y := (nets t q s.card).exec xr with hydef
  have hyinj : Function.Injective y := exec_keySet_injective hxr _
  have hK : (execPlacement F nets v t ht.le).regs q = keySet xr := by
    show s.image (X F nets v t) = _
    ext κ
    simp only [Finset.mem_image, keySet, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨c, rfl⟩ := exists_orderEmb_eq hw
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨_, Finset.orderEmbOfFin_mem _ rfl _, rfl⟩
  have hKy : keySet xr = Finset.univ.image y := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro κ hκ
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hκ
      exact exec_mem_keySet _ c
    · rw [card_keySet hxr, Finset.card_image_of_injective _ hyinj]; simp
  have hcard : (keySet xr).card = s.card := card_keySet hxr
  have hfilt : ∀ (Q : Fin (16 ^ d) → Prop) [DecidablePred Q],
      (keySet xr).filter Q = (Finset.univ.image y).filter Q := fun Q _ => by rw [hKy]
  rw [hK] at hJ ⊢
  set b := q.child j.val j.isLt hq with hb
  set A := q.ancestor (r - 1) with hA
  have hbs : b.strangers (r + 1) id (fromParentK F nets v t b) =
      q.strangers r id (fromParentK F nets v t b) := by
    rw [← KBag.strangers_parent_eq b r hr (by show 1 ≤ q.l + 1; omega) id _ (by norm_num),
      hb, KBag.child_parent q _ _ _ (by norm_num)]
  -- the sent keys
  have hfp : fromParentK F nets v t b = (downSetB s π (F.off t q) j.val).image (X F nets v (t + 1)) := by
    unfold fromParentK
    have hp : b.parent (by omega) = q := KBag.child_parent q _ _ _ (by norm_num)
    have hx : b.x % 16 = j.val := by
      show (16 * q.x + j.val) % 16 = j.val
      rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt j.isLt
    rw [hp, hx]
  -- strangers of b
  have hbs' := strangers_eq_filter q r hr (fromParentK F nets v t b)
  have hqs := strangers_eq_filter q r hr (keySet xr)
  have hsplit := strangers_split (keySet xr) A.lo A.hi (Nat.mul_le_mul_right _ (Nat.le_succ _))
  -- positions
  set pos := cellOf y with hpos
  have hsub : (fromParentK F nets v t b).filter
        (fun κ : Fin (16 ^ d) => ¬ (A.lo ≤ (κ : ℕ) ∧ (κ : ℕ) < A.hi)) ⊆
      (((keySet xr).filter fun κ : Fin (16 ^ d) =>
          π / 2 ≤ pos κ ∧ pos κ < (keySet xr).card - π / 2).filter
        fun κ : Fin (16 ^ d) => ¬ (A.lo ≤ (κ : ℕ) ∧ (κ : ℕ) < A.hi)) := by
    intro κ hκ
    simp only [Finset.mem_filter] at hκ ⊢
    obtain ⟨hκS, hn⟩ := hκ
    rw [hfp, mem_image_downSet_iff F nets v t ht q π (F.off t q) j.val κ] at hκS
    obtain ⟨c, h1, h2, rfl⟩ := hκS
    have hpc : pos (y c) = c.val := cellOf_apply hyinj c
    refine ⟨⟨exec_mem_keySet _ c, ?_, ?_⟩, hn⟩
    · rw [hpc]; omega
    · rw [hpc, hcard]
      have hle16 : F.off t q (j.val + 1) ≤ F.off t q 16 := F.off_mono t q (by have := j.isLt; omega)
      have hs16 : s.card = π + F.off t q 16 := by
        rw [hs, wireSets_card F ht.le q, F.hsplit t q ht, FlowTableB.off_sixteen]
      have hev : 2 ∣ π := hπe
      obtain ⟨p, hp⟩ := hev
      omega
  have hle : (b.strangers (r + 1) id (fromParentK F nets v t b) : ℕ) ≤
      (((keySet xr).filter fun κ : Fin (16 ^ d) =>
          π / 2 ≤ pos κ ∧ pos κ < (keySet xr).card - π / 2).filter
        fun κ : Fin (16 ^ d) => ¬ (A.lo ≤ (κ : ℕ) ∧ (κ : ℕ) < A.hi)).card := by
    rw [hbs, hbs']; exact Finset.card_le_card hsub
  have hHhi : ((keySet xr).filter fun κ : Fin (16 ^ d) => A.hi ≤ (κ : ℕ)).card ≤ Jmax := by
    rw [hqs, hsplit] at hJ; omega
  have hHlo : ((keySet xr).filter fun κ : Fin (16 ^ d) => (κ : ℕ) < A.lo).card ≤ Jmax := by
    rw [hqs, hsplit] at hJ; omega
  have hfH : ∀ k, 0 < k → k ≤ Jmax → k ≤ (keySet xr).card →
      (((keySet xr).filter fun (κ : Fin (16 ^ d)) =>
        (keySet xr).card - k ≤ rk (keySet xr) κ ∧ pos κ < (keySet xr).card - π / 2).card : ℝ)
        < εF * k := by
    intro k hk hkJ hkK
    rw [hcard] at hkK ⊢
    have h1 := hspec.fHigh_keys hxr k hk hkJ hkK
    have h2 := filter_image_cellOf hyinj
      (fun κ n => s.card - k ≤ rk (keySet xr) κ ∧ n < s.card - π / 2)
    rw [hfilt]
    simp only [← hydef] at h1
    rw [h2]; exact h1
  have hfL : ∀ k, 0 < k → k ≤ Jmax → k ≤ (keySet xr).card →
      (((keySet xr).filter fun (κ : Fin (16 ^ d)) =>
        rk (keySet xr) κ < k ∧ π / 2 ≤ pos κ).card : ℝ) < εF * k := by
    intro k hk hkJ hkK
    rw [hcard] at hkK
    have h1 := hspec.fLow_keys hxr k hk hkJ hkK
    have h2 := filter_image_cellOf hyinj
      (fun κ n => rk (keySet xr) κ < k ∧ π / 2 ≤ n)
    rw [hfilt]
    simp only [← hydef] at h1
    rw [h2]; exact h1
  have hmain := sent_outside_le (keySet xr) pos π A.lo A.hi Jmax εF hfH hfL hHhi hHlo
  have hcast : ((b.strangers (r + 1) id (fromParentK F nets v t b) : ℕ) : ℝ) ≤
      ((((keySet xr).filter fun κ : Fin (16 ^ d) =>
          π / 2 ≤ pos κ ∧ pos κ < (keySet xr).card - π / 2).filter
        fun κ : Fin (16 ^ d) => ¬ (A.lo ≤ (κ : ℕ) ∧ (κ : ℕ) < A.hi)).card : ℝ) := by
    exact_mod_cast hle
  have hq' : ((q.strangers r id (keySet xr) : ℕ) : ℝ) =
      (((keySet xr).filter fun κ : Fin (16 ^ d) => A.hi ≤ (κ : ℕ)).card : ℝ) +
      (((keySet xr).filter fun κ : Fin (16 ^ d) => (κ : ℕ) < A.lo).card : ℝ) := by
    rw [hqs, hsplit]; push_cast; ring
  rw [hq']
  exact hcast.trans hmain

end Real


end R1T
