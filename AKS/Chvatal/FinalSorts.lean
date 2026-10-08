module

/-
  # A prefix network followed by a layer of block sorters sorts

  If the prefix network `A` sends every permutation input so that the wires of each block
  `S b` carry exactly the values of an interval `[base b, base b + |S b|)`, then following `A`
  by the bitonic sorters on the blocks (`stageNet`) gives a generalized network whose output
  on every permutation input is the identity (after the fixed relabelling `Y 1`), and
  `Untangle.untangle` turns it into a standard sorting network of the same depth.
-/

public import AKS.Chvatal.ExecPlacement
public import AKS.Sort.Untangle
public import AKS.Sort.Perm
public import AKS.Bitonic.Shrink

@[expose] public section

namespace Chvatal

/-- A strictly monotone `f : Fin m → ℕ` has gaps at least the index gap. -/
theorem strictMono_gap {m : ℕ} (f : Fin m → ℕ) (hf : StrictMono f) :
    ∀ (a b : ℕ) (ha : a < m) (hb : b < m), a ≤ b →
      f ⟨a, ha⟩ + (b - a) ≤ f ⟨b, hb⟩ := by
  intro a b ha hb hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hb' : b < m := by omega
    have h1 := ih hb'
    have h2 : f ⟨b, hb'⟩ < f ⟨b + 1, hb⟩ := hf (by simp [Fin.lt_def])
    omega

/-- A strictly monotone map `Fin m → ℕ` landing in `[base, base + m)` is `k ↦ base + k`. -/
theorem strictMono_interval {m : ℕ} (f : Fin m → ℕ) (hf : StrictMono f) (base : ℕ)
    (hlo : ∀ k, base ≤ f k) (hhi : ∀ k, f k < base + m) (k : Fin m) :
    f k = base + k.val := by
  have hm : 0 < m := Fin.pos k
  have h1 := strictMono_gap f hf 0 k.val hm k.isLt (Nat.zero_le _)
  have h2 := strictMono_gap f hf k.val (m - 1) k.isLt (by omega) (by omega)
  have h3 := hlo ⟨0, hm⟩
  have h4 := hhi ⟨m - 1, by omega⟩
  have e1 : f ⟨k.val, k.isLt⟩ = f k := rfl
  omega

/-- Conversion of a standard network to a generalized one. -/
def toGen {n : ℕ} (G : ComparatorNetwork n) : Untangle.GenNetwork n :=
  ⟨G.comparators.map fun c => ⟨c.i, c.j, ne_of_lt c.h⟩⟩

theorem toGen_exec {n : ℕ} {α : Type*} [LinearOrder α] (G : ComparatorNetwork n)
    (v : Fin n → α) : (toGen G).exec v = G.exec v := by
  unfold toGen Untangle.GenNetwork.exec ComparatorNetwork.exec
  simp only [List.foldl_map]
  rfl

theorem toGen_depth {n : ℕ} (G : ComparatorNetwork n) : (toGen G).depth = G.depth := by
  unfold toGen Untangle.GenNetwork.depth ComparatorNetwork.depth
  simp only [List.foldl_map]
  rfl

/-- On the wires of block `b`, the stage of bitonic sorters applied after `A` outputs
`base b + k` at the `k`-th wire of `S b`, whatever the permutation input. -/
theorem final_block_value {d : ℕ}
    (S : KBag 64 d → Finset (Fin (64 ^ d)))
    (hdisj : ∀ b b', b ≠ b' → Disjoint (S b) (S b'))
    (base : KBag 64 d → ℕ)
    (A : ComparatorNetwork (64 ^ d))
    (himage : ∀ (p : Equiv.Perm (Fin (64 ^ d))) (b : KBag 64 d),
      (S b).image (A.exec (fun w => p w)) =
        Finset.univ.filter (fun x : Fin (64 ^ d) => base b ≤ x.val ∧ x.val < base b + (S b).card))
    (p : Equiv.Perm (Fin (64 ^ d))) (b : KBag 64 d) (k : Fin (S b).card) :
    ((stageNet S (fun _ n => bitonicNetwork n)).exec (A.exec (fun w => p w))
      (((S b).orderEmbOfFin rfl) k)).val = base b + k.val := by
  set e := (S b).orderEmbOfFin rfl with he
  set x : Fin (S b).card → Fin (64 ^ d) := fun i => A.exec (fun w => p w) (e i) with hx
  have hinside := stageNet_exec_inside S hdisj (fun _ n => bitonicNetwork n)
    (A.exec (fun w => p w)) b
  obtain ⟨ρ', hρ'⟩ := ComparatorNetwork.exec_eq_comp_perm A (fun w => p w)
  have hxinj : Function.Injective x := by
    intro i j hij
    simp only [hx, hρ', Function.comp] at hij
    exact e.injective (ρ'.injective (p.injective hij))
  obtain ⟨ρ, hρ⟩ := ComparatorNetwork.exec_eq_comp_perm (bitonicNetwork (S b).card) x
  set y := (bitonicNetwork (S b).card).exec x with hy
  have hymono : Monotone y := bitonicNetwork_sorts _ (Fin (64 ^ d)) x
  have hyinj : Function.Injective y := by
    rw [hρ]; exact hxinj.comp ρ.injective
  have hymem : ∀ k, base b ≤ (y k).val ∧ (y k).val < base b + (S b).card := by
    intro k
    have : y k ∈ (S b).image (A.exec (fun w => p w)) := by
      rw [hρ]
      exact Finset.mem_image_of_mem _ (Finset.orderEmbOfFin_mem _ rfl _)
    rw [himage p b] at this
    simpa using this
  have hsm : StrictMono (fun k => (y k).val) :=
    fun i j hij => by
      have := (hymono.strictMono_of_injective hyinj) hij
      exact this
  have := strictMono_interval (fun k => (y k).val) hsm (base b)
    (fun k => (hymem k).1) (fun k => (hymem k).2) k
  rw [hinside]
  exact this

/-- The output of the whole network on the permutation inputs does not depend on the input. -/
theorem final_exec_const {d : ℕ}
    (S : KBag 64 d → Finset (Fin (64 ^ d)))
    (hdisj : ∀ b b', b ≠ b' → Disjoint (S b) (S b'))
    (hcover : ∀ w, ∃ b, w ∈ S b)
    (base : KBag 64 d → ℕ)
    (A : ComparatorNetwork (64 ^ d))
    (himage : ∀ (p : Equiv.Perm (Fin (64 ^ d))) (b : KBag 64 d),
      (S b).image (A.exec (fun w => p w)) =
        Finset.univ.filter (fun x : Fin (64 ^ d) => base b ≤ x.val ∧ x.val < base b + (S b).card))
    (p : Equiv.Perm (Fin (64 ^ d))) (w : Fin (64 ^ d)) :
    (A.append (stageNet S (fun _ n => bitonicNetwork n))).exec (fun w => p w) w =
      (A.append (stageNet S (fun _ n => bitonicNetwork n))).exec
        (fun w => (1 : Equiv.Perm (Fin (64 ^ d))) w) w := by
  obtain ⟨b, hb⟩ := hcover w
  have hw : w ∈ Set.range ((S b).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hb
  obtain ⟨k, rfl⟩ := hw
  apply Fin.ext
  have e1 : ∀ q : Equiv.Perm (Fin (64 ^ d)),
      (A.append (stageNet S (fun _ n => bitonicNetwork n))).exec (fun w => q w) =
        (stageNet S (fun _ n => bitonicNetwork n)).exec (A.exec (fun w => q w)) := by
    intro q
    exact ComparatorNetwork.exec_append A (stageNet S (fun _ n => bitonicNetwork n)) _
  rw [e1, e1, final_block_value S hdisj base A himage p b k,
    final_block_value S hdisj base A himage 1 b k]

/-- **Generic final layer.** A prefix network `A` that places, on every permutation input,
the interval of values `[base b, base b + |S b|)` on the wires of block `S b`, followed by
bitonic sorters on the blocks, can be rearranged (untangled) into a sorting network of depth
at most `A.depth + (stageNet ...).depth`. -/
theorem final_layer_sorts {d : ℕ}
    (S : KBag 64 d → Finset (Fin (64 ^ d)))
    (hdisj : ∀ b b', b ≠ b' → Disjoint (S b) (S b'))
    (hcover : ∀ w, ∃ b, w ∈ S b)
    (base : KBag 64 d → ℕ)
    (A : ComparatorNetwork (64 ^ d))
    (himage : ∀ (p : Equiv.Perm (Fin (64 ^ d))) (b : KBag 64 d),
      (S b).image (A.exec (fun w => p w)) =
        Finset.univ.filter (fun x : Fin (64 ^ d) => base b ≤ x.val ∧ x.val < base b + (S b).card)) :
    ∃ T : ComparatorNetwork (64 ^ d),
      T.depth ≤ A.depth + (stageNet S (fun _ n => bitonicNetwork n)).depth ∧
        ComparatorNetwork.Sorts.{0} T := by
  set F := stageNet S (fun _ n => bitonicNetwork n) with hF
  set G := A.append F with hG
  obtain ⟨ρ, hρ⟩ := ComparatorNetwork.exec_eq_comp_perm G
    (fun w => (1 : Equiv.Perm (Fin (64 ^ d))) w)
  have hY : ∀ (p : Equiv.Perm (Fin (64 ^ d))) r, G.exec (fun w => p w) (ρ.symm r) = r := by
    intro p r
    rw [final_exec_const S hdisj hcover base A himage p, hρ]
    simp
  have hmono : ∀ (α : Type) [LinearOrder α] (v : Fin (64 ^ d) → α),
      Monotone (fun r : Fin (64 ^ d) => (toGen G).exec v (ρ.symm r)) := by
    intro α _ v
    obtain ⟨σ, hσ⟩ := exists_sorting_perm v
    have hv : v = (v ∘ ⇑σ.symm) ∘ (fun w => σ w) := by
      funext w; simp
    have h := ComparatorNetwork.exec_comp_monotone G hσ (fun w => σ w)
    have : ∀ r, (toGen G).exec v (ρ.symm r) = (v ∘ ⇑σ.symm) r := by
      intro r
      rw [toGen_exec]
      have h2 : G.exec v (ρ.symm r) =
          G.exec ((v ∘ ⇑σ.symm) ∘ (fun w => σ w)) (ρ.symm r) :=
        congrArg (fun u => G.exec u (ρ.symm r)) hv
      rw [h2, ← h]
      show (v ∘ ⇑σ.symm) (G.exec (fun w => σ w) (ρ.symm r)) = _
      rw [hY σ r]
    intro r s hrs
    show (toGen G).exec v (ρ.symm r) ≤ (toGen G).exec v (ρ.symm s)
    rw [this, this]
    exact hσ hrs
  obtain ⟨T, hT, hTs⟩ := Untangle.untangle (toGen G) ρ hmono
  refine ⟨T, ?_, hTs⟩
  rw [hT, toGen_depth]
  exact ComparatorNetwork.depth_append_le A F

end Chvatal
