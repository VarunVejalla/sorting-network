import AKS.Bounds.Certificate
import AKS.Bounds.Chvatal1830Final

/-! A small compile-time example of the contributor API. Candidate modules should define a closed
`SortingDepth.UpperBoundCertificate C K` from their construction, then use its generic limsup theorem.
The only bound object is the canonical `ComparatorNetwork`; the objective is the shared
`SortingDepth.minimum`. -/

namespace UpperBoundContrib

theorem limsup_of_certificate {C K : ℝ}
    (h : SortingDepth.UpperBoundCertificate C K) :
    Filter.limsup (fun n : ℕ => (SortingDepth.minimum n : ℝ) / Real.logb 2 n) Filter.atTop ≤ C :=
  h.limsup_bound

/-- Example provider: package the existing Chvátal endpoint as a closed global certificate. -/
noncomputable def chvatal1419Certificate :
    SortingDepth.UpperBoundCertificate 1419 (-43861) where
  threshold := 64 ^ 7
  network := by
    intro n hn
    have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 64 ^ 7) hn
    have hd7 : 7 ≤ Nat.clog 64 n := by
      have hmono : Nat.clog 64 (64 ^ 7) ≤ Nat.clog 64 n := Nat.clog_mono_right 64 hn
      rwa [Nat.clog_pow 64 7 (by decide)] at hmono
    let d := Nat.clog 64 n
    obtain ⟨net0, hsort0, hdepth0⟩ := SortingDepth.exists_sorter hd7
    have hnPow : n ≤ 64 ^ d := Nat.le_pow_clog (by decide : 1 < 64) n
    let net := net0.restrictWires n hnPow
    have hsort : ComparatorNetwork.Sorts.{0} net :=
      restrictWires_sorts net0 n hnPow (fun v => hsort0 (α := Bool) v)
    have hdepth : net.depth ≤ Chvatal.totalDepth d :=
      (restrictWires_depth_le _ _ _).trans hdepth0
    have hlog := Chvatal.totalDepth_logb_le hd7 rfl hn1
    exact ⟨net, hsort, (Nat.cast_le.2 hdepth).trans hlog⟩

theorem chvatal1419_limsup :
    Filter.limsup (fun n : ℕ => (SortingDepth.minimum n : ℝ) / Real.logb 2 n) Filter.atTop ≤ 1419 :=
  chvatal1419Certificate.limsup_bound

end UpperBoundContrib

#print axioms UpperBoundContrib.limsup_of_certificate
#print axioms UpperBoundContrib.chvatal1419_limsup
