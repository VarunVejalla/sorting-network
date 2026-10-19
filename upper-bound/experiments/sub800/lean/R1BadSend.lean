import R1Window

/-! # Lemma 4.2′ for the real network (W1, step 6)

`bad_send0_real_gen`: the order-0 strangers that node `q` sends to its child `j` in stage `t` are at
most `strangers₁(q) + 15ρ + resid_j + 2·EB`, where `ρ` bounds the Lemma 4.1′ excess
(`#keys of q addressed to child h ≤ G_h + ρ`) and
`resid_j = (Σ_{h<j} (G_h − down_h) − π/2)⁺ + (Σ_{h>j} (G_h − down_h) − π/2)⁺`. -/

namespace R1T

open Finset
open Chvatal (KBag Placement rk keySet exec_mem_keySet card_filter_val rankN_val bagSize)
open Chvatal (KBag.parent_child')
open Chvatal.BW (rankN)

section Native

variable {d : ℕ}

theorem ancestor_zero_eq (b : KBag 16 d) : b.ancestor 0 = b := by
  apply KBag.ext <;> simp [KBag.ancestor]

theorem strangers_one_eq (b : KBag 16 d) (S : Finset (Fin (16 ^ d))) :
    b.strangers 1 id S = (S.filter fun κ => ¬ b.Native κ id).card := by
  unfold KBag.strangers
  congr 1
  apply Finset.filter_congr
  intro κ _
  simp [KBag.Strange, ancestor_zero_eq]

theorem pow_sub_succ (d l : ℕ) (hl : l < d) : (16 : ℕ) ^ (d - l) = 16 * 16 ^ (d - l - 1) := by
  rw [← pow_succ']; congr 1; omega

theorem native_child_iff (q : KBag 16 d) (hq : q.l < d) (j : ℕ) (hj : j < 16)
    (κ : Fin (16 ^ d)) :
    (q.child j hj hq).Native κ id ↔
      q.x * 16 ^ (d - q.l) + j * 16 ^ (d - q.l - 1) ≤ κ.val ∧
        κ.val < q.x * 16 ^ (d - q.l) + (j + 1) * 16 ^ (d - q.l - 1) := by
  rw [KBag.native_iff _ _ _ (by norm_num)]
  have e := pow_sub_succ d q.l hq
  have e2 : d - (q.l + 1) = d - q.l - 1 := by omega
  simp only [KBag.lo, KBag.hi, KBag.size, bagSize, KBag.child, id, e2]
  have h1 : (16 * q.x + j) * 16 ^ (d - q.l - 1) =
      q.x * 16 ^ (d - q.l) + j * 16 ^ (d - q.l - 1) := by rw [e]; ring
  have h2 : (16 * q.x + j + 1) * 16 ^ (d - q.l - 1) =
      q.x * 16 ^ (d - q.l) + (j + 1) * 16 ^ (d - q.l - 1) := by rw [e]; ring
  rw [h1, h2]

theorem native_self_iff (q : KBag 16 d) (hq : q.l < d) (κ : Fin (16 ^ d)) :
    q.Native κ id ↔
      q.x * 16 ^ (d - q.l) ≤ κ.val ∧
        κ.val < q.x * 16 ^ (d - q.l) + 16 * 16 ^ (d - q.l - 1) := by
  rw [KBag.native_iff _ _ _ (by norm_num)]
  have e := pow_sub_succ d q.l hq
  simp only [KBag.lo, KBag.hi, KBag.size, bagSize, id]
  have h2 : (q.x + 1) * 16 ^ (d - q.l) = q.x * 16 ^ (d - q.l) + 16 * 16 ^ (d - q.l - 1) := by
    rw [← e]; ring
  rw [h2]

end Native

/-- The node's residual for window `j` (as in `FlowTableB.residAt`, with deficits `G`). -/
noncomputable def residG (π : ℕ) (b : ℕ → ℕ) (G : ℕ → ℝ) (j : ℕ) : ℝ :=
  max 0 (∑ h ∈ range j, (G h - b h) - (π : ℝ) / 2) +
    max 0 (∑ h ∈ Ico (j + 1) 16, (G h - b h) - (π : ℝ) / 2)

/-- The key-level window count for `Fin` keys and unequal blocks. -/
theorem window_real_gen {d : ℕ} (K : Finset (Fin (16 ^ d))) (q : KBag 16 d) (hq : q.l < d)
    (j : ℕ) (hj : j < 16) (π : ℕ) (b : ℕ → ℕ) (hKc : K.card = π + ∑ h ∈ range 16, b h)
    (hπ : 2 ∣ π) (G : ℕ → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hM : ∀ h (hh : h < 16),
      ((K.filter fun κ => (q.child h hh hq).Native κ id).card : ℝ) ≤ G h + ρ) :
    ((K.filter fun κ => π / 2 + ∑ h ∈ range j, b h ≤ rk K κ ∧
        rk K κ < π / 2 + ∑ h ∈ range j, b h + b j ∧
          ¬ (q.child j hj hq).Native κ id).card : ℝ) ≤
      (q.strangers 1 id K : ℝ) + 15 * ρ + residG π b G j := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : ℕ, S = 16 ^ (d - q.l - 1) := ⟨_, rfl⟩
  obtain ⟨Ulo, hUlo⟩ : ∃ U : ℕ, U = q.x * 16 ^ (d - q.l) := ⟨_, rfl⟩
  have hOL : ((K.image Fin.val).filter (· < Ulo)).card = (K.filter fun κ => κ.val < Ulo).card :=
    card_filter_val K (fun m => m < Ulo)
  have hOR : ((K.image Fin.val).filter (Ulo + 16 * S ≤ ·)).card =
      (K.filter fun κ => Ulo + 16 * S ≤ κ.val).card :=
    card_filter_val K (fun m => Ulo + 16 * S ≤ m)
  have hstr : (q.strangers 1 id K : ℝ) =
      (((K.image Fin.val).filter (· < Ulo)).card : ℝ) +
        (((K.image Fin.val).filter (Ulo + 16 * S ≤ ·)).card : ℝ) := by
    rw [hOL, hOR, strangers_one_eq, ← Nat.cast_add]
    congr 1
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext κ
      simp only [Finset.mem_filter, Finset.mem_union, native_self_iff q hq]
      simp only [← hS, ← hUlo]
      by_cases hk : κ ∈ K
      · simp only [hk, true_and]; omega
      · simp [hk]
    · rw [Finset.disjoint_filter]
      intro κ _ h1 h2
      omega
  have hcard : (K.image Fin.val).card = π + ∑ h ∈ range 16, b h := by
    rw [Finset.card_image_of_injective _ Fin.val_injective]; exact hKc
  have hM' : ∀ h < 16, (((K.image Fin.val).filter fun κ =>
      Ulo + h * S ≤ κ ∧ κ < Ulo + (h + 1) * S).card : ℝ) ≤ G h + ρ := by
    intro h hh
    rw [card_filter_val K (fun m => Ulo + h * S ≤ m ∧ m < Ulo + (h + 1) * S)]
    have := hM h hh
    convert this using 3
    ext κ
    simp only [Finset.mem_filter]
    simp only [native_child_iff q hq h hh, ← hS, ← hUlo]
  have key := window_wrong_gen (K.image Fin.val) 16 π Ulo S j b G ρ hj hρ hπ hcard hM'
  rw [← hstr] at key
  have hfilt := card_filter_val K (fun m => π / 2 + ∑ h ∈ range j, b h ≤ rankN (K.image Fin.val) m ∧
    rankN (K.image Fin.val) m < π / 2 + ∑ h ∈ range j, b h + b j ∧
      ¬ (Ulo + j * S ≤ m ∧ m < Ulo + (j + 1) * S))
  have heq : (K.filter fun κ => π / 2 + ∑ h ∈ range j, b h ≤ rk K κ ∧
        rk K κ < π / 2 + ∑ h ∈ range j, b h + b j ∧
          ¬ (q.child j hj hq).Native κ id) =
      K.filter fun κ => π / 2 + ∑ h ∈ range j, b h ≤ rankN (K.image Fin.val) κ.val ∧
        rankN (K.image Fin.val) κ.val < π / 2 + ∑ h ∈ range j, b h + b j ∧
          ¬ (Ulo + j * S ≤ κ.val ∧ κ.val < Ulo + (j + 1) * S) := by
    apply Finset.filter_congr
    intro κ _
    simp only [native_child_iff q hq j hj, ← hS, ← hUlo]
    rw [rankN_val]
  rw [heq, ← hfilt]
  have e15 : ((16 : ℕ) : ℝ) - 1 = 15 := by norm_num
  unfold residG
  rw [e15] at key
  linarith

section Main

variable {d tf : ℕ}

/-- The down-flow of `q` as a function on `ℕ` (zero beyond the children). -/
def downN (F : FlowTableB d tf) (t : ℕ) (q : KBag 16 d) (h : ℕ) : ℕ :=
  if hh : h < 16 then F.down t q ⟨h, hh⟩ else 0

theorem off_eq_sum (F : FlowTableB d tf) (t : ℕ) (q : KBag 16 d) :
    ∀ j, j ≤ 16 → F.off t q j = ∑ h ∈ range j, downN F t q h
  | 0, _ => by simp [FlowTableB.off_zero]
  | j + 1, hj => by
    rw [F.off_succ (t := t) (b := q) (j := j) (by omega), off_eq_sum F t q j (by omega), sum_range_succ]
    simp [downN, show j < 16 by omega]

theorem sum_downN (F : FlowTableB d tf) (t : ℕ) (q : KBag 16 d) :
    ∑ h ∈ range 16, downN F t q h = ∑ j, F.down t q j := by
  rw [← off_eq_sum F t q 16 le_rfl, FlowTableB.off_sixteen]

/-- **Lemma 4.2′ (real network, order 0).** Keys of `q` sent down to child `j` in stage `t` that
are not addressed to it. -/
theorem bad_send0_real_gen (F : FlowTableB d tf)
    (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (16 ^ d))) (t : ℕ) (ht : t < tf) (q : KBag 16 d) (hq : q.l < d)
    (j : ℕ) (hj : j < 16) (EB : ℝ) (Jmax : ℕ) (εF : ℝ) (G : ℕ → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hspec : NodeSpecAll (wireSets F t q).card (F.up t q)
      (nets t q (wireSets F t q).card) EB Jmax εF)
    (hM : ∀ h (hh : h < 16),
      ((((execPlacement F nets v t ht.le).regs q).filter fun κ =>
        (q.child h hh hq).Native κ id).card : ℝ) ≤ G h + ρ) :
    (((q.child j hj hq).strangers 1 id
        (fromParentK F nets v t (q.child j hj hq)) : ℕ) : ℝ) ≤
      (q.strangers 1 id ((execPlacement F nets v t ht.le).regs q) : ℝ) + 15 * ρ +
        residG (F.up t q) (downN F t q) G j + 2 * EB := by
  classical
  have hπ : 2 ∣ F.up t q := F.hup_even t q ht
  set bN := downN F t q with hbN
  have hsplit : F.a t q = F.up t q + ∑ h ∈ range 16, bN h := by
    rw [F.hsplit t q ht, hbN, sum_downN]
  have hcardS : (wireSets F t q).card = F.a t q := wireSets_card F ht.le q
  set K := (execPlacement F nets v t ht.le).regs q with hK
  have hKc : K.card = F.up t q + ∑ h ∈ range 16, bN h := by
    rw [hK, execPlacement_card F nets v t ht.le q, hsplit]
  let xr : Fin (wireSets F t q).card → Fin (16 ^ d) := fun i =>
    X F nets v t ((wireSets F t q).orderEmbOfFin rfl i)
  have hxr : Function.Injective xr :=
    (X_injective F nets v t).comp ((wireSets F t q).orderEmbOfFin rfl).injective
  have hkey : keySet xr = K := by
    ext κ
    simp only [keySet, Finset.mem_image, Finset.mem_univ, true_and, hK, execPlacement]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, Finset.orderEmbOfFin_mem _ rfl _, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨c, rfl⟩ := exists_orderEmb_eq hw
      exact ⟨c, rfl⟩
  set s := F.up t q / 2 + ∑ h ∈ range j, bN h with hs
  set e := F.up t q / 2 + ∑ h ∈ range j, bN h + bN j with he
  have hoffj : F.off t q j = ∑ h ∈ range j, bN h := off_eq_sum F t q j (by omega)
  have hoffj1 : F.off t q (j + 1) = ∑ h ∈ range j, bN h + bN j := by
    rw [off_eq_sum F t q (j + 1) (by omega), sum_range_succ]
  set b := q.child j hj hq with hb
  have hbp : b.parent = q := KBag.parent_child' q j hj hq
  have hbx : b.x % 16 = j := by
    show (16 * q.x + j) % 16 = j
    omega
  have hW : fromParentK F nets v t b =
      ((Finset.univ : Finset (Fin (wireSets F t q).card)).filter fun c =>
        s ≤ c.val ∧ c.val < e).image ((nets t q (wireSets F t q).card).exec xr) := by
    unfold fromParentK
    rw [hbp, hbx]
    ext κ
    rw [mem_image_downSet_iff F nets v t ht q, hoffj, hoffj1]
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, h1, h2, rfl⟩
      exact ⟨c, ⟨h1, by rw [he]; omega⟩, rfl⟩
    · rintro ⟨c, ⟨h1, h2⟩, rfl⟩
      exact ⟨c, h1, by rw [he] at h2; omega, rfl⟩
  rw [hW, strangers_one_eq]
  set Wn := ((Finset.univ : Finset (Fin (wireSets F t q).card)).filter fun c =>
        s ≤ c.val ∧ c.val < e).image ((nets t q (wireSets F t q).card).exec xr) with hWn
  have hWK : ∀ κ ∈ Wn, κ ∈ K := by
    intro κ hκ
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hκ
    rw [← hkey]; exact exec_mem_keySet _ c
  have hea : e ≤ (wireSets F t q).card := by
    rw [hcardS, hsplit, he]
    have : ∑ h ∈ range j, bN h + bN j ≤ ∑ h ∈ range 16, bN h := by
      rw [← sum_range_succ]
      exact sum_le_sum_of_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega)
    obtain ⟨p, hp⟩ := hπ
    omega
  have hI := hspec.intruder_keys hxr s e (by rw [he]; omega) hea
  rw [hkey] at hI
  have hsub : (Wn.filter fun κ => ¬ b.Native κ id) ⊆
      (Wn.filter fun κ => ¬ (s ≤ rk K κ ∧ rk K κ < e)) ∪
      (K.filter fun κ => s ≤ rk K κ ∧ rk K κ < e ∧ ¬ b.Native κ id) := by
    intro κ hκ
    simp only [Finset.mem_filter, Finset.mem_union] at hκ ⊢
    by_cases hw : s ≤ rk K κ ∧ rk K κ < e
    · exact Or.inr ⟨hWK κ hκ.1, hw.1, hw.2, hκ.2⟩
    · exact Or.inl ⟨hκ.1, hw⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le
    (Wn.filter fun κ => ¬ (s ≤ rk K κ ∧ rk K κ < e))
    (K.filter fun κ => s ≤ rk K κ ∧ rk K κ < e ∧ ¬ b.Native κ id)
  have h3 := window_real_gen K q hq j hj (F.up t q) bN hKc hπ G ρ hρ hM
  have h4 : (((Wn.filter fun κ => ¬ b.Native κ id).card : ℕ) : ℝ) ≤
      ((Wn.filter fun κ => ¬ (s ≤ rk K κ ∧ rk K κ < e)).card : ℝ) +
      ((K.filter fun κ => s ≤ rk K κ ∧ rk K κ < e ∧ ¬ b.Native κ id).card : ℝ) := by
    exact_mod_cast h1.trans h2
  have hWn' : Wn.filter (fun κ => ¬ (s ≤ rk K κ ∧ rk K κ < e)) =
      ((Finset.univ.filter fun c : Fin (wireSets F t q).card => s ≤ c.val ∧ c.val < e).image
        ((nets t q (wireSets F t q).card).exec xr)).filter
        fun κ => ¬ (s ≤ rk K κ ∧ rk K κ < e) := rfl
  rw [hWn'] at h4
  linarith

end Main

end R1T
