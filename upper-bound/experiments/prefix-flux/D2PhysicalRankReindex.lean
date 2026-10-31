import AKS.Chvatal.PhysicalPack2

namespace Chvatal.D2PhysicalRankReindex

/-- A cumulative row-preserving scramble moves a row-major wire by at most
the column width minus one. This is the output-coordinate charge when the
physical two-round network is compared with its semantic execution. -/
theorem rowScrambleWirePerm2_displacement
    {m n : Nat} (hn : 0 < n) (σ1 σ2 : Chvatal.Scramble m n)
    (w : Fin (m * n)) :
    (Chvatal.rowScrambleWirePerm2 m n hn σ1 σ2 w).val ≤ w.val + (n - 1) ∧
      w.val ≤ (Chvatal.rowScrambleWirePerm2 m n hn σ1 σ2 w).val + (n - 1) := by
  let ρ := Chvatal.rowScrambleWirePerm2 m n hn σ1 σ2
  let r := Chvatal.matrixRow m n hn w
  let c := Chvatal.matrixCol m n hn w
  let p := ρ w
  let r' := Chvatal.matrixRow m n hn p
  let c' := Chvatal.matrixCol m n hn p
  have hr : r' = r := by
    dsimp [r', p, r, ρ]
    exact Chvatal.matrixRow_rowScrambleWirePerm2 hn σ1 σ2 w
  have hw : Chvatal.matrixWire m n r c = w :=
    Chvatal.matrixWire_matrixRow_col hn w
  have hp : Chvatal.matrixWire m n r' c' = p :=
    Chvatal.matrixWire_matrixRow_col hn p
  have hρ : ρ w = Chvatal.matrixWire m n r c' := by
    calc
      ρ w = p := rfl
      _ = Chvatal.matrixWire m n r' c' := hp.symm
      _ = Chvatal.matrixWire m n r c' := by rw [hr]
  have hwv : w.val = r.val * n + c.val := by
    rw [← hw, Chvatal.matrixWire_row]
  have hρv : (ρ w).val = r.val * n + c'.val := by
    rw [hρ, Chvatal.matrixWire_row]
  have hc := c.isLt
  have hc' := c'.isLt
  rw [hwv, hρv]
  constructor <;> omega

end Chvatal.D2PhysicalRankReindex
