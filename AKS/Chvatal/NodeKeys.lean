module
/-
  # Real keys at a node: normalization to ranks and key-level `NodeSpec` statements

  `NodeSpec` is stated for permutations `x` of `Fin a`.  The real network runs a node network on
  injective real keys `xr : Fin a → Fin M`.  Replacing each key by its rank among the node's keys
  `K = image xr` is monotone, so it commutes with the network (`exec_comp_monotone`); hence the
  rank of the key at cell `c` after the network is `net.exec (rankPerm xr) c`, and the `NodeSpec`
  bounds transfer verbatim to key ranks.  We also prove the two-sided intruder bound for a block
  window.  The rank map is `ℕ`-valued (`rk K`) to avoid a `Fin a` codomain for keys outside `K`.
-/

public import AKS.Chvatal.ExecPlacement
public import AKS.Chvatal.NodeSpec
public import AKS.Sort.Monotone

@[expose] public section

namespace Chvatal

open Finset

variable {a M : ℕ}

/-- Number of keys of `K` strictly below `κ`. -/
def rk (K : Finset (Fin M)) (κ : Fin M) : ℕ := (K.filter (· < κ)).card

theorem rk_mono (K : Finset (Fin M)) : Monotone (rk K) := by
  intro x y hxy
  unfold rk
  exact Finset.card_le_card (fun z hz => by
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, lt_of_lt_of_le hz.2 hxy⟩)

theorem rk_lt_of_lt {K : Finset (Fin M)} {x y : Fin M} (hx : x ∈ K) (h : x < y) :
    rk K x < rk K y := by
  unfold rk
  apply Finset.card_lt_card
  refine ⟨fun z hz => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, lt_trans hz.2 h⟩
  · have := hsub (show x ∈ K.filter (· < y) from Finset.mem_filter.2 ⟨hx, h⟩)
    simp only [Finset.mem_filter] at this
    exact lt_irrefl _ this.2

theorem rk_injOn (K : Finset (Fin M)) : Set.InjOn (rk K) (K : Set (Fin M)) := by
  intro x hx y hy hxy
  rcases lt_trichotomy x y with h | h | h
  · exact absurd hxy (ne_of_lt (rk_lt_of_lt hx h))
  · exact h
  · exact absurd hxy.symm (ne_of_lt (rk_lt_of_lt hy h))

theorem rk_lt_card {K : Finset (Fin M)} {x : Fin M} (hx : x ∈ K) : rk K x < K.card := by
  unfold rk
  apply Finset.card_lt_card
  refine ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
  have := hsub hx
  simp only [Finset.mem_filter] at this
  exact lt_irrefl _ this.2

/-- The set of keys at a node. -/
def keySet (xr : Fin a → Fin M) : Finset (Fin M) := Finset.univ.image xr

theorem card_keySet {xr : Fin a → Fin M} (hxr : Function.Injective xr) :
    (keySet xr).card = a := by
  unfold keySet; rw [Finset.card_image_of_injective _ hxr]; simp

theorem mem_keySet (xr : Fin a → Fin M) (c : Fin a) : xr c ∈ keySet xr :=
  Finset.mem_image_of_mem _ (Finset.mem_univ c)

/-- The normalized input: cell `c` carries the rank of its key among the node's keys. -/
def rankFun {xr : Fin a → Fin M} (hxr : Function.Injective xr) : Fin a → Fin a :=
  fun c => ⟨rk (keySet xr) (xr c), by
    have := rk_lt_card (mem_keySet xr c); rwa [card_keySet hxr] at this⟩

theorem rankFun_injective {xr : Fin a → Fin M} (hxr : Function.Injective xr) :
    Function.Injective (rankFun hxr) := by
  intro c d h
  have h' : rk (keySet xr) (xr c) = rk (keySet xr) (xr d) := congrArg Fin.val h
  exact hxr (rk_injOn _ (mem_keySet xr c) (mem_keySet xr d) h')

/-- The normalized input as a permutation of `Fin a`. -/
noncomputable def rankPerm {xr : Fin a → Fin M} (hxr : Function.Injective xr) :
    Equiv.Perm (Fin a) :=
  Equiv.ofBijective (rankFun hxr) (Finite.injective_iff_bijective.1 (rankFun_injective hxr))

theorem rankPerm_apply {xr : Fin a → Fin M} (hxr : Function.Injective xr) (c : Fin a) :
    ((rankPerm hxr : Fin a → Fin a) c).val = rk (keySet xr) (xr c) := rfl

/-- **Normalization (K2.1).** A comparator network commutes with replacing keys by ranks:
the rank of the key at cell `c` after the network is the output of the network on the
normalized permutation. -/
theorem exec_rankPerm {xr : Fin a → Fin M} (hxr : Function.Injective xr)
    (net : ComparatorNetwork a) (c : Fin a) :
    (net.exec (rankPerm hxr : Fin a → Fin a) c).val = rk (keySet xr) (net.exec xr c) := by
  have h1 := net.exec_comp_monotone (f := Fin.val) (fun _ _ h => h)
    (rankPerm hxr : Fin a → Fin a)
  have h2 := net.exec_comp_monotone (f := rk (keySet xr)) (rk_mono _) xr
  have h3 : (Fin.val ∘ (rankPerm hxr : Fin a → Fin a)) = rk (keySet xr) ∘ xr := by
    funext d; exact rankPerm_apply hxr d
  rw [h3] at h1
  have := congrFun h1 c
  have h4 := congrFun h2 c
  simp only [Function.comp] at this h4
  rw [this, h4]

theorem exec_keySet_injective {xr : Fin a → Fin M} (hxr : Function.Injective xr)
    (net : ComparatorNetwork a) : Function.Injective (net.exec xr) := by
  obtain ⟨ρ, hρ⟩ := Chvatal.ComparatorNetwork.exec_eq_comp_perm net xr
  rw [hρ]; exact hxr.comp ρ.injective

/-- Keys of the output are the same set of keys. -/
theorem exec_mem_keySet {xr : Fin a → Fin M}
    (net : ComparatorNetwork a) (c : Fin a) : net.exec xr c ∈ keySet xr := by
  obtain ⟨ρ, hρ⟩ := Chvatal.ComparatorNetwork.exec_eq_comp_perm net xr
  rw [hρ]; exact mem_keySet xr _

/-! ### K2.2 key-level statements -/

section Spec
variable {π τ : ℕ} {net : ComparatorNetwork a} {EB : ℝ} {Jmax : ℕ} {εF : ℝ}

theorem NodeSpec.bHigh_keys (h : NodeSpec a π τ net EB Jmax εF) {xr : Fin a → Fin M}
    (hxr : Function.Injective xr) (p : ℕ) (hp : p ∈ blockBounds π τ) (hpa : p ≤ a) :
    ((Finset.univ.filter fun c : Fin a =>
        a - p ≤ rk (keySet xr) (net.exec xr c) ∧ c.val < a - p).card : ℝ) ≤ EB := by
  have := h.bHigh (rankPerm hxr) p hp hpa
  simpa only [exec_rankPerm hxr net] using this

theorem NodeSpec.bLow_keys (h : NodeSpec a π τ net EB Jmax εF) {xr : Fin a → Fin M}
    (hxr : Function.Injective xr) (p : ℕ) (hp : p ∈ blockBounds π τ) (hpa : p ≤ a) :
    ((Finset.univ.filter fun c : Fin a =>
        rk (keySet xr) (net.exec xr c) < p ∧ p ≤ c.val).card : ℝ) ≤ EB := by
  have := h.bLow (rankPerm hxr) p hp hpa
  simpa only [exec_rankPerm hxr net] using this

theorem NodeSpec.fHigh_keys (h : NodeSpec a π τ net EB Jmax εF) {xr : Fin a → Fin M}
    (hxr : Function.Injective xr) (j : ℕ) (hj : 0 < j) (hjm : j ≤ Jmax) (hja : j ≤ a) :
    ((Finset.univ.filter fun c : Fin a =>
        a - j ≤ rk (keySet xr) (net.exec xr c) ∧ c.val < a - π / 2).card : ℝ) < εF * j := by
  have := h.fHigh (rankPerm hxr) j hj hjm hja
  simpa only [exec_rankPerm hxr net] using this

theorem NodeSpec.fLow_keys (h : NodeSpec a π τ net EB Jmax εF) {xr : Fin a → Fin M}
    (hxr : Function.Injective xr) (j : ℕ) (hj : 0 < j) (hjm : j ≤ Jmax) (hja : j ≤ a) :
    ((Finset.univ.filter fun c : Fin a =>
        rk (keySet xr) (net.exec xr c) < j ∧ π / 2 ≤ c.val).card : ℝ) < εF * j := by
  have := h.fLow (rankPerm hxr) j hj hjm hja
  simpa only [exec_rankPerm hxr net] using this

/-- **Intruder bound (K2.2).** In the cell window `[s, s+τ)`, `s = π/2 + j τ`, at most `2·EB`
cells carry a key whose rank lies outside `[s, s+τ)`. -/
theorem NodeSpec.intruder_cells (h : NodeSpec a π τ net EB Jmax εF) {xr : Fin a → Fin M}
    (hxr : Function.Injective xr) (ha : a = π + 64 * τ) (hπ : 2 ∣ π) (j : ℕ) (hj : j < 64) :
    ((Finset.univ.filter fun c : Fin a =>
        π / 2 + j * τ ≤ c.val ∧ c.val < π / 2 + j * τ + τ ∧
          ¬ (π / 2 + j * τ ≤ rk (keySet xr) (net.exec xr c) ∧
             rk (keySet xr) (net.exec xr c) < π / 2 + j * τ + τ)).card : ℝ) ≤ 2 * EB := by
  obtain ⟨k, hk⟩ := hπ
  have hs : π / 2 + j * τ ∈ blockBounds π τ := by
    unfold blockBounds
    exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩
  have hp₂ : π / 2 + (63 - j) * τ ∈ blockBounds π τ := by
    unfold blockBounds
    exact Finset.mem_image.2 ⟨63 - j, Finset.mem_range.2 (by omega), rfl⟩
  have hsa : π / 2 + j * τ ≤ a := by
    have : j * τ ≤ 64 * τ := Nat.mul_le_mul_right _ (by omega)
    omega
  have hp₂a : π / 2 + (63 - j) * τ ≤ a := by
    have : (63 - j) * τ ≤ 64 * τ := Nat.mul_le_mul_right _ (by omega)
    omega
  have key : a - (π / 2 + (63 - j) * τ) = π / 2 + j * τ + τ := by
    have e : (63 - j) * τ + (j + 1) * τ = 64 * τ := by
      rw [← Nat.add_mul]; congr 1; omega
    have e2 : (j + 1) * τ = j * τ + τ := by rw [Nat.add_mul]; simp
    omega
  have h1 := h.bLow_keys hxr _ hs hsa
  have h2 := h.bHigh_keys hxr _ hp₂ hp₂a
  rw [key] at h2
  set s := π / 2 + j * τ
  have hsub : (Finset.univ.filter fun c : Fin a =>
        s ≤ c.val ∧ c.val < s + τ ∧
          ¬ (s ≤ rk (keySet xr) (net.exec xr c) ∧ rk (keySet xr) (net.exec xr c) < s + τ)) ⊆
      (Finset.univ.filter fun c : Fin a => rk (keySet xr) (net.exec xr c) < s ∧ s ≤ c.val) ∪
      (Finset.univ.filter fun c : Fin a =>
        s + τ ≤ rk (keySet xr) (net.exec xr c) ∧ c.val < s + τ) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hc ⊢
    obtain ⟨c1, c2, c3⟩ := hc
    by_cases hlt : rk (keySet xr) (net.exec xr c) < s
    · exact Or.inl ⟨hlt, c1⟩
    · exact Or.inr ⟨by by_contra hh; exact c3 ⟨by omega, by omega⟩, c2⟩
  have hc := Finset.card_le_card hsub
  have hc2 := Finset.card_union_le
    (Finset.univ.filter fun c : Fin a => rk (keySet xr) (net.exec xr c) < s ∧ s ≤ c.val)
    (Finset.univ.filter fun c : Fin a =>
        s + τ ≤ rk (keySet xr) (net.exec xr c) ∧ c.val < s + τ)
  have : (((Finset.univ.filter fun c : Fin a =>
        s ≤ c.val ∧ c.val < s + τ ∧
          ¬ (s ≤ rk (keySet xr) (net.exec xr c) ∧
            rk (keySet xr) (net.exec xr c) < s + τ)).card : ℕ) : ℝ)
      ≤ ((Finset.univ.filter fun c : Fin a =>
            rk (keySet xr) (net.exec xr c) < s ∧ s ≤ c.val).card : ℝ)
        + ((Finset.univ.filter fun c : Fin a =>
          s + τ ≤ rk (keySet xr) (net.exec xr c) ∧ c.val < s + τ).card : ℝ) := by
    exact_mod_cast hc.trans hc2
  linarith

/-- **K2.3** Key-count form: the keys sitting in the window `[s, s+τ)` of cells whose rank
(among the node's keys) is outside `[s, s+τ)` number at most `2·EB`. -/
theorem NodeSpec.intruder_keys (h : NodeSpec a π τ net EB Jmax εF) {xr : Fin a → Fin M}
    (hxr : Function.Injective xr) (ha : a = π + 64 * τ) (hπ : 2 ∣ π) (j : ℕ) (hj : j < 64) :
    (((((Finset.univ.filter fun c : Fin a =>
          π / 2 + j * τ ≤ c.val ∧ c.val < π / 2 + j * τ + τ)).image (net.exec xr)).filter
        fun κ => ¬ (π / 2 + j * τ ≤ rk (keySet xr) κ ∧
                    rk (keySet xr) κ < π / 2 + j * τ + τ)).card : ℝ) ≤ 2 * EB := by
  have hinj := exec_keySet_injective hxr net
  have heq : (((Finset.univ.filter fun c : Fin a =>
          π / 2 + j * τ ≤ c.val ∧ c.val < π / 2 + j * τ + τ)).image (net.exec xr)).filter
        (fun κ => ¬ (π / 2 + j * τ ≤ rk (keySet xr) κ ∧
                    rk (keySet xr) κ < π / 2 + j * τ + τ)) =
      (Finset.univ.filter fun c : Fin a =>
        π / 2 + j * τ ≤ c.val ∧ c.val < π / 2 + j * τ + τ ∧
          ¬ (π / 2 + j * τ ≤ rk (keySet xr) (net.exec xr c) ∧
             rk (keySet xr) (net.exec xr c) < π / 2 + j * τ + τ)).image (net.exec xr) := by
    ext κ
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨c, hc, rfl⟩, hn⟩; exact ⟨c, ⟨hc.1, hc.2, hn⟩, rfl⟩
    · rintro ⟨c, hc, rfl⟩; exact ⟨⟨c, ⟨hc.1, hc.2.1⟩, rfl⟩, hc.2.2⟩
  rw [heq, Finset.card_image_of_injective _ hinj]
  exact h.intruder_cells hxr ha hπ j hj

end Spec

end Chvatal
