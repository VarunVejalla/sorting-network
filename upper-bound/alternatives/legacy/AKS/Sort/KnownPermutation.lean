module

public import AKS.Sort.KnownHalfPartition
public import AKS.Sort.ParallelEmbeddings

/-! A known rank permutation on `2^k` wires can be corrected in depth `k`.
Each recursion uses one matching to separate the rank halves, followed by
parallel corrections within the physical halves. -/

@[expose] public section

namespace Paterson

theorem exists_known_permutation_correction (k : ℕ) :
    ∀ w : Fin (2 ^ k) → Fin (2 ^ k), Function.Injective w →
      ∃ net : ComparatorNetwork (2 ^ k), net.depth ≤ k ∧ net.exec w = id := by
  induction k with
  | zero =>
    intro w _
    refine ⟨⟨[]⟩, by simp [depth_nil], ?_⟩
    funext i
    change (_ : Fin 1) = _
    exact Subsingleton.elim _ _
  | succ k ih =>
    rw [pow_succ']
    intro w hw
    let m := 2 ^ k
    have hm : 0 < m := by dsimp [m]; positivity
    let e : Fin 2 → (Fin m ↪o Fin (2 * m)) := fun s ↦
      { toFun := fun i ↦ ⟨s.val * m + i.val, by have := s.isLt; have := i.isLt; nlinarith⟩
        inj' := by intro a b h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega
        map_rel_iff' := by intro a b; change s.val * m + a.val ≤ s.val * m + b.val ↔ _; omega }
    have hdis : ∀ i j, e 0 i ≠ e 1 j := by
      intro i j h
      have hh := congrArg Fin.val h
      change 0 * m + i.val = 1 * m + j.val at hh
      have := i.isLt
      omega
    obtain ⟨first, hd, hl, hr⟩ := exists_known_half_partition m w hw
    let u := first.exec w
    have hu := ComparatorNetwork.exec_injective first hw
    have hp (s : Fin 2) (i : Fin m) :
        s.val * m ≤ (u (e s i)).val ∧ (u (e s i)).val < (s.val + 1) * m := by
      fin_cases s
      · have hh := hl i
        change 0 * m ≤ (u (e 0 i)).val ∧ (u (e 0 i)).val < (0 + 1) * m
        exact ⟨by omega, by simpa [e, u] using hh⟩
      · have hh := hr i
        change 1 * m ≤ (u (e 1 i)).val ∧ (u (e 1 i)).val < (1 + 1) * m
        exact ⟨by simpa [e, u] using hh, (u (e 1 i)).isLt⟩
    let cw : Fin 2 → (Fin m → Fin m) := fun s i ↦
      ⟨(u (e s i)).val - s.val * m, by
        have hh := hp s i
        rw [Nat.add_mul, one_mul] at hh
        omega⟩
    have hcw (s : Fin 2) : Function.Injective (cw s) := by
      intro a b h
      have hh := congrArg Fin.val h
      change (u (e s a)).val - s.val * m = (u (e s b)).val - s.val * m at hh
      have ha := hp s a
      have hb := hp s b
      apply (e s).injective
      apply hu
      apply Fin.ext
      change (u (e s a)).val = (u (e s b)).val
      omega
    choose nets hn hs using fun s ↦ ih (cw s) (hcw s)
    let rest := parallelEmbeddings e nets
    refine ⟨⟨first.comparators ++ rest.comparators⟩, ?_, ?_⟩
    · exact (depth_append first rest).trans (by
        have hh := parallelEmbeddings_depth_le e nets hdis hn
        change rest.depth ≤ k at hh
        change first.depth + rest.depth ≤ k + 1
        omega)
    · funext i
      let s : Fin 2 := ⟨i.val / m, by have := i.isLt; exact (Nat.div_lt_iff_lt_mul hm).mpr (by omega)⟩
      let j : Fin m := ⟨i.val % m, Nat.mod_lt _ hm⟩
      have hij : e s j = i := by
        apply Fin.ext
        change i.val / m * m + i.val % m = i.val
        exact Nat.div_add_mod' _ _
      rw [ComparatorNetwork.exec_append, ← hij,
        parallelEmbeddings_exec_inside e nets hdis]
      have hv : u ∘ e s = e s ∘ cw s := by
        funext a
        apply Fin.ext
        change (u (e s a)).val = s.val * m + ((u (e s a)).val - s.val * m)
        have := hp s a
        omega
      change (nets s).exec (u ∘ e s) j = e s j
      rw [hv, ComparatorNetwork.exec_comp_mono _ (e s).monotone, hs s]
      rfl

end Paterson
