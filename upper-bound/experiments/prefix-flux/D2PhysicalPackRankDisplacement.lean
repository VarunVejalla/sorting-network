import D2TwoStrideArbitraryRank
import D2PhysicalRankReindex
import AKS.Chvatal.PhysicalPack2

namespace Chvatal.D2PhysicalPackRankDisplacement

/-- Transfer a semantic rank-displacement estimate to the genuine physical
two-round comparator network. The only added rank cost is the cumulative
row-preserving output reindexing, bounded by the column width minus one. -/
theorem physicalPack2Net_displacement_of_semantic_bound
    {m n B : Nat} (hn : 0 < n) (σ1 σ2 : Chvatal.Scramble m n)
    (v : Fin (m * n) → Fin (m * n))
    (hsem : ∀ w, (Chvatal.semanticExec2 hn σ1 σ2 v w).val ≤ w.val + B ∧
      w.val ≤ (Chvatal.semanticExec2 hn σ1 σ2 v w).val + B)
    (w : Fin (m * n)) :
    ((Chvatal.physicalPack2Net m n hn σ1 σ2).exec v w).val ≤
      w.val + B + (n - 1) ∧
    w.val ≤ ((Chvatal.physicalPack2Net m n hn σ1 σ2).exec v w).val +
      B + (n - 1) := by
  let ρ := Chvatal.rowScrambleWirePerm2 m n hn σ1 σ2
  obtain ⟨hlocalUpper, hlocalLower⟩ := hsem (ρ w)
  obtain ⟨hwireUpper, hwireLower⟩ :=
    Chvatal.D2PhysicalRankReindex.rowScrambleWirePerm2_displacement hn σ1 σ2 w
  have hnet := Chvatal.physicalPack2Net_exec hn σ1 σ2 v
  have hpoint : (Chvatal.physicalPack2Net m n hn σ1 σ2).exec v w =
      Chvatal.semanticExec2 hn σ1 σ2 v (ρ w) := by
    simpa only [Function.comp_apply] using congrFun hnet w
  have hpointVal := congrArg Fin.val hpoint
  constructor
  · rw [hpointVal]
    calc
      (Chvatal.semanticExec2 hn σ1 σ2 v (ρ w)).val ≤ (ρ w).val + B :=
        hlocalUpper
      _ ≤ w.val + (n - 1) + B := Nat.add_le_add_right hwireUpper B
      _ = w.val + B + (n - 1) := by omega
  · rw [hpointVal]
    exact le_trans hwireLower
      (Nat.add_le_add_right hlocalLower (n - 1))

/-- At height4096 and width64, the existing semantic two-stride certificate
therefore gives a pointwise displacement bound of3455 for the actual physical
comparator network, for every permutation input. -/
theorem physicalPack2Net_two_stride_rank_displacement
    (v : Fin (4096 * 64) → Fin (4096 * 64))
    (hbij : Function.Bijective v) (w : Fin (4096 * 64)) :
    ((Chvatal.physicalPack2Net 4096 64 (by omega)
      (Chvatal.D2LiftedShuffleBridge.strideScramble 35)
      (Chvatal.D2LiftedShuffleBridge.strideScramble 25)).exec v w).val ≤
        w.val + 3455 ∧
    w.val ≤ ((Chvatal.physicalPack2Net 4096 64 (by omega)
      (Chvatal.D2LiftedShuffleBridge.strideScramble 35)
      (Chvatal.D2LiftedShuffleBridge.strideScramble 25)).exec v w).val + 3455 := by
  have hsem :=
    Chvatal.D2TwoStrideArbitraryRank.semanticExec2_two_stride_rank_displacement_arbitrary
      v hbij
  have hphysical := physicalPack2Net_displacement_of_semantic_bound
    (m := 4096) (n := 64) (B := 3392) (by omega)
    (Chvatal.D2LiftedShuffleBridge.strideScramble 35)
    (Chvatal.D2LiftedShuffleBridge.strideScramble 25) v hsem w
  simpa using hphysical

end Chvatal.D2PhysicalPackRankDisplacement
