import D2RankAlignment

/-! A column permutation within one 64-wire row changes a Boolean prefix
count by at most half the row width. -/

namespace Chvatal.D2RowPermutationCount

abbrev Col := Fin 64

def prefixTrueCount (v : Col -> Bool) (n : Nat) : Nat :=
  (Finset.univ.filter fun c : Col => c.val < n /\ v c = true).card

def suffixTrueCount (v : Col -> Bool) (n : Nat) : Nat :=
  (Finset.univ.filter fun c : Col => n <= c.val /\ v c = true).card

def trueCount (v : Col -> Bool) : Nat :=
  (Finset.univ.filter fun c : Col => v c = true).card

theorem prefix_suffix_trueCount (v : Col -> Bool) (n : Nat) :
    prefixTrueCount v n + suffixTrueCount v n = trueCount v := by
  classical
  unfold prefixTrueCount suffixTrueCount trueCount
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun c : Col => v c = true)
    (p := fun c : Col => c.val < n)
  have hprefix :
      (Finset.univ.filter (fun c : Col => v c = true)).filter
        (fun c : Col => c.val < n) =
      Finset.univ.filter (fun c : Col => c.val < n /\ v c = true) := by
    ext c
    simp [and_comm]
  have hsuffix :
      (Finset.univ.filter (fun c : Col => v c = true)).filter
        (fun c : Col => Not (c.val < n)) =
      Finset.univ.filter (fun c : Col => n <= c.val /\ v c = true) := by
    ext c
    simp [not_lt, and_comm]
  rw [hprefix, hsuffix] at h
  exact h

theorem prefixTrueCount_le (v : Col -> Bool) {n : Nat} (hn : n <= 64) :
    prefixTrueCount v n <= n := by
  classical
  by_cases hne : n = 64
  · subst n
    calc
      prefixTrueCount v 64 <= Finset.univ.card := Finset.card_filter_le _ _
      _ = 64 := by simp
  · have hnlt : n < 64 := by omega
    have hsub :
        (Finset.univ.filter fun c : Col => c.val < n /\ v c = true) ⊆
          Finset.Iio (Fin.mk n hnlt) := by
      intro c hc
      exact Finset.mem_Iio.mpr (Finset.mem_filter.mp hc).2.1
    have hcard := Finset.card_le_card hsub
    simpa [prefixTrueCount, Fin.card_Iio] using hcard

theorem suffixTrueCount_le (v : Col -> Bool) {n : Nat} (hn : n <= 64) :
    suffixTrueCount v n <= 64 - n := by
  classical
  by_cases hne : n = 64
  · subst n
    simp [suffixTrueCount]
  · have hnlt : n < 64 := by omega
    have hsub :
        (Finset.univ.filter fun c : Col => n <= c.val /\ v c = true) ⊆
          Finset.Ici (Fin.mk n hnlt) := by
      intro c hc
      exact Finset.mem_Ici.mpr (Finset.mem_filter.mp hc).2.1
    have hcard := Finset.card_le_card hsub
    simpa [suffixTrueCount, Fin.card_Ici] using hcard

theorem trueCount_comp_perm (v : Col -> Bool) (e : Equiv.Perm Col) :
    trueCount (Function.comp v e) = trueCount v := by
  classical
  unfold trueCount
  refine Finset.card_bij (fun c _ => e c) ?_ ?_ ?_
  case refine_1 =>
    intro c hc
    simpa using (Finset.mem_filter.mp hc).2
  case refine_2 =>
    intro a ha b hb hab
    exact e.injective hab
  case refine_3 =>
    intro b hb
    refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
    simpa using (Finset.mem_filter.mp hb).2

/-- Prefix counts of a Boolean row profile differ by at most 32 after any
permutation of its 64 columns. -/
theorem prefixTrueCount_comp_perm_le_32
    (v : Col -> Bool) (e : Equiv.Perm Col) (n : Nat) (hn : n <= 64) :
    prefixTrueCount (Function.comp v e) n <= prefixTrueCount v n + 32 /\
    prefixTrueCount v n <= prefixTrueCount (Function.comp v e) n + 32 := by
  have htotal := trueCount_comp_perm v e
  by_cases hnHalf : n <= 32
  case pos =>
    have h1 := prefixTrueCount_le (Function.comp v e) hn
    have h2 := prefixTrueCount_le v hn
    omega
  case neg =>
    have hsmall : 64 - n <= 32 := by omega
    have hs1 := suffixTrueCount_le (Function.comp v e) hn
    have hs2 := suffixTrueCount_le v hn
    have hp1 := prefix_suffix_trueCount (Function.comp v e) n
    have hp2 := prefix_suffix_trueCount v n
    rw [htotal] at hp1
    omega

end Chvatal.D2RowPermutationCount
