import D2LiftedShuffleBridge

open Chvatal.D2LiftedShuffleBridge

namespace Chvatal.D2PointwiseRankError

private theorem card_fin_lt {n : Nat} (a : Fin n) :
    (Finset.univ.filter fun x : Fin n => x.val < a.val).card = a.val := by
  calc
    (Finset.univ.filter fun x : Fin n => x.val < a.val).card =
        (Finset.range a.val).card := by
      apply Finset.card_bij (fun x _ => x.val)
      · intro x hx
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
      · intro x hx y hy h
        exact Fin.ext h
      · intro y hy
        have hy' := Finset.mem_range.mp hy
        refine ⟨⟨y, lt_trans hy' a.isLt⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'⟩
    _ = a.val := Finset.card_range _

private theorem card_fin_le {n : Nat} (a : Fin n) :
    (Finset.univ.filter fun x : Fin n => x.val <= a.val).card = a.val + 1 := by
  calc
    (Finset.univ.filter fun x : Fin n => x.val <= a.val).card =
        (Finset.range (a.val + 1)).card := by
      apply Finset.card_bij (fun x _ => x.val)
      · intro x hx
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hx).2)
      · intro x hx y hy h
        exact Fin.ext h
      · intro y hy
        have hy' : y < a.val + 1 := Finset.mem_range.mp hy
        refine ⟨⟨y, by omega⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_lt_succ hy'⟩
    _ = a.val + 1 := Finset.card_range _

private theorem countValuesLT_eq_val (v : Fin (4096 * 64) → Fin (4096 * 64))
    (hbij : Function.Bijective v) (a : Fin (4096 * 64)) :
    countValuesLT v a = a.val := by
  classical
  unfold countValuesLT
  calc
    (Finset.univ.filter fun q : Fin (4096 * 64) => v q < a).card =
        (Finset.univ.filter fun x : Fin (4096 * 64) => x.val < a.val).card := by
      apply Finset.card_bij (fun q _ => v q)
      · intro q hq
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩
      · intro x hx y hy hxy
        exact hbij.1 hxy
      · intro x hx
        obtain ⟨q, hq⟩ := hbij.2 x
        refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hq⟩
        have hx' := (Finset.mem_filter.mp hx).2
        simpa only [hq] using hx'
    _ = a.val := card_fin_lt a

private theorem countValuesLE_eq_succ (v : Fin (4096 * 64) → Fin (4096 * 64))
    (hbij : Function.Bijective v) (a : Fin (4096 * 64)) :
    countValuesLE v a = a.val + 1 := by
  classical
  unfold countValuesLE
  calc
    (Finset.univ.filter fun q : Fin (4096 * 64) => v q ≤ a).card =
        (Finset.univ.filter fun x : Fin (4096 * 64) => x.val ≤ a.val).card := by
      apply Finset.card_bij (fun q _ => v q)
      · intro q hq
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩
      · intro x hx y hy hxy
        exact hbij.1 hxy
      · intro x hx
        obtain ⟨q, hq⟩ := hbij.2 x
        refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hq⟩
        have hx' := (Finset.mem_filter.mp hx).2
        simpa only [hq] using hx'
    _ = a.val + 1 := card_fin_le a

/-- The checked two-shuffle threshold-count estimate is a pointwise bound on
the displacement of every key rank, for any permutation input already sorted
inside columns. -/
theorem semanticExec2_two_stride_rank_displacement
    (v : Fin (4096 * 64) → Fin (4096 * 64))
    (hbij : Function.Bijective v)
    (hmono : Chvatal.ColumnMonotoneInput 4096 64 (by omega) v)
    (w : Fin (4096 * 64)) :
    (Chvatal.semanticExec2 (by omega) (strideScramble 35)
      (strideScramble 25) v w).val ≤ w.val + 3392 ∧
    w.val ≤ (Chvatal.semanticExec2 (by omega) (strideScramble 35)
      (strideScramble 25) v w).val + 3392 := by
  have hinterval := semanticExec2_two_stride_rank_interval v hmono w
  have hlt := countValuesLT_eq_val v hbij
    (Chvatal.semanticExec2 (by omega) (strideScramble 35) (strideScramble 25) v w)
  have hle := countValuesLE_eq_succ v hbij
    (Chvatal.semanticExec2 (by omega) (strideScramble 35) (strideScramble 25) v w)
  have hlow : countValuesLT v
      (Chvatal.semanticExec2 (by omega) (strideScramble 35) (strideScramble 25) v w) ≤
      w.val + 3392 := hinterval.1
  have hhigh : w.val < countValuesLE v
      (Chvatal.semanticExec2 (by omega) (strideScramble 35) (strideScramble 25) v w) + 3392 :=
    hinterval.2
  rw [hlt] at hlow
  rw [hle] at hhigh
  exact ⟨hlow, by omega⟩

end Chvatal.D2PointwiseRankError
