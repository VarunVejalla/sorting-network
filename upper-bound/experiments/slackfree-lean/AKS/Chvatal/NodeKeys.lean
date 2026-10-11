module
public import AKS.Chvatal.ExecPlacement
public import AKS.Chvatal.NodeSpec
public import AKS.Sort.Monotone

@[expose] public section

/-! Real keys at a node: replacing keys by their ranks among the node's keys is monotone, so it
commutes with the node network (`exec_rankPerm`); hence the `NodeSpec` bounds transfer to key ranks
(`rk K` is `ℕ`-valued, to avoid a `Fin a` codomain for keys outside `K`). -/

namespace Chvatal

open Finset

variable {a M : ℕ}

/-- Number of keys of `K` strictly below `κ`. -/
def rk (K : Finset (Fin M)) (κ : Fin M) : ℕ := (K.filter (· < κ)).card

theorem rk_mono (K : Finset (Fin M)) : Monotone (rk K) := fun _ _ hxy =>
  Finset.card_le_card fun z hz => by
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, lt_of_lt_of_le hz.2 hxy⟩

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
    have := rankIn_lt_card (mem_keySet xr c); rwa [card_keySet hxr] at this⟩

/-- The normalized input as a permutation of `Fin a`. -/
noncomputable def rankPerm {xr : Fin a → Fin M} (hxr : Function.Injective xr) :
    Equiv.Perm (Fin a) :=
  Equiv.ofBijective (rankFun hxr) <| Finite.injective_iff_bijective.1 fun c d h =>
    hxr (rankIn_injOn (mem_keySet xr c) (mem_keySet xr d) (congrArg Fin.val h))

/-- **Normalization (K2.1).** A comparator network commutes with replacing keys by ranks:
the rank of the key at cell `c` after the network is the output of the network on the
normalized permutation. -/
theorem exec_rankPerm {xr : Fin a → Fin M} (hxr : Function.Injective xr)
    (net : ComparatorNetwork a) (c : Fin a) :
    (net.exec (rankPerm hxr : Fin a → Fin a) c).val = rk (keySet xr) (net.exec xr c) := by
  have h1 := net.exec_comp_monotone (f := Fin.val) (fun _ _ h => h) (rankPerm hxr : Fin a → Fin a)
  have h2 := net.exec_comp_monotone (f := rk (keySet xr)) (rk_mono _) xr
  rw [show (Fin.val ∘ (rankPerm hxr : Fin a → Fin a)) = rk (keySet xr) ∘ xr from rfl] at h1
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

section Spec
variable {π τ : ℕ} {net : ComparatorNetwork a} {EB : ℝ} {Jmax : ℕ} {εF : ℝ}

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

/-- **Intruder bound (K2.2/K2.3).** The keys sitting in the cell window `[s, s+τ)`,
`s = π/2 + j τ`, whose rank (among the node's keys) lies outside `[s, s+τ)` number at most
`2·EB`. -/
theorem NodeSpec.intruder_keys (h : NodeSpec a π τ net EB Jmax εF) {xr : Fin a → Fin M}
    (hxr : Function.Injective xr) (ha : a = π + 64 * τ) (hπ : 2 ∣ π) (j : ℕ) (hj : j < 64) :
    (((((Finset.univ.filter fun c : Fin a =>
          π / 2 + j * τ ≤ c.val ∧ c.val < π / 2 + j * τ + τ)).image (net.exec xr)).filter
        fun κ => ¬ (π / 2 + j * τ ≤ rk (keySet xr) κ ∧
                    rk (keySet xr) κ < π / 2 + j * τ + τ)).card : ℝ) ≤ 2 * EB := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ (exec_keySet_injective hxr net),
    Finset.filter_filter]
  simp only [Function.comp, ← exec_rankPerm hxr net]
  have h63 : (63 - j) * τ + (j + 1) * τ = 64 * τ := by
    rw [← Nat.add_mul]; congr 1; omega
  have hj1 : (j + 1) * τ = j * τ + τ := by rw [Nat.add_mul]; simp
  have hj2 : j * τ ≤ 64 * τ := Nat.mul_le_mul_right _ (by omega)
  have hj3 : (63 - j) * τ ≤ 64 * τ := Nat.mul_le_mul_right _ (by omega)
  have h1 := h.bLow (rankPerm hxr) (π / 2 + j * τ)
    (Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩) (by omega)
  have h2 := h.bHigh (rankPerm hxr) (π / 2 + (63 - j) * τ)
    (Finset.mem_image.2 ⟨63 - j, Finset.mem_range.2 (by omega), rfl⟩) (by omega)
  rw [show a - (π / 2 + (63 - j) * τ) = π / 2 + j * τ + τ by omega] at h2
  have hsub : (Finset.univ.filter fun c : Fin a =>
      (π / 2 + j * τ ≤ c.val ∧ c.val < π / 2 + j * τ + τ) ∧
        ¬ (π / 2 + j * τ ≤ (net.exec (rankPerm hxr : Fin a → Fin a) c).val ∧
           (net.exec (rankPerm hxr : Fin a → Fin a) c).val < π / 2 + j * τ + τ)) ⊆
      (Finset.univ.filter fun c : Fin a =>
        (net.exec (rankPerm hxr : Fin a → Fin a) c).val < π / 2 + j * τ ∧ π / 2 + j * τ ≤ c.val) ∪
      (Finset.univ.filter fun c : Fin a =>
        π / 2 + j * τ + τ ≤ (net.exec (rankPerm hxr : Fin a → Fin a) c).val ∧
          c.val < π / 2 + j * τ + τ) := by
    intro c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have h3 := Nat.cast_le (α := ℝ) |>.2 ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
  push_cast at h3
  linarith

end Spec

end Chvatal
