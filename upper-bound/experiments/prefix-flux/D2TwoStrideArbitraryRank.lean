import D2PointwiseRankError

open Chvatal.D2LiftedShuffleBridge

namespace Chvatal.D2TwoStrideArbitraryRank

private theorem comparatorExec_bijective {n : Nat}
    (net : ComparatorNetwork n) (v : Fin n → Fin n)
    (hv : Function.Bijective v) : Function.Bijective (net.exec v) := by
  obtain ⟨ρ, hρ⟩ := ComparatorNetwork.exec_eq_comp_perm net v
  rw [hρ]
  exact hv.comp ρ.bijective

/-- The semantic two-stride executor has the 3392 rank-displacement bound
for every permutation input: its own first column sort establishes the
monotone-column hypothesis needed by the sharper checked estimate. -/
theorem semanticExec2_two_stride_rank_displacement_arbitrary
    (v : Fin (4096 * 64) → Fin (4096 * 64))
    (hbij : Function.Bijective v) (w : Fin (4096 * 64)) :
    (Chvatal.semanticExec2 (by omega) (strideScramble 35)
      (strideScramble 25) v w).val ≤ w.val + 3392 ∧
    w.val ≤ (Chvatal.semanticExec2 (by omega) (strideScramble 35)
      (strideScramble 25) v w).val + 3392 := by
  let C := Chvatal.columnSortNetwork 4096 64 (by omega)
  let v1 := C.exec v
  have hbij1 : Function.Bijective v1 := comparatorExec_bijective C v hbij
  have hmono1 : Chvatal.ColumnMonotoneInput 4096 64 (by omega) v1 :=
    Chvatal.columnSortNetwork_columnMonotone (by omega) v
  have hidem : C.exec v1 = v1 :=
    Chvatal.columnSort_exec_of_columnMonotone (by omega) v1 hmono1
  have hsem :
      Chvatal.semanticExec2 (by omega) (strideScramble 35)
        (strideScramble 25) v =
      Chvatal.semanticExec2 (by omega) (strideScramble 35)
        (strideScramble 25) v1 := by
    unfold Chvatal.semanticExec2 Chvatal.semanticExec
    change C.exec (C.exec (C.exec v ∘
        (Chvatal.rowScrambleWirePerm 4096 64 (by omega) (strideScramble 35)).symm) ∘
        (Chvatal.rowScrambleWirePerm 4096 64 (by omega) (strideScramble 25)).symm) =
      C.exec (C.exec (C.exec v1 ∘
        (Chvatal.rowScrambleWirePerm 4096 64 (by omega) (strideScramble 35)).symm) ∘
        (Chvatal.rowScrambleWirePerm 4096 64 (by omega) (strideScramble 25)).symm)
    rw [hidem]
  rw [hsem]
  exact Chvatal.D2PointwiseRankError.semanticExec2_two_stride_rank_displacement
    v1 hbij1 hmono1 w

end Chvatal.D2TwoStrideArbitraryRank
