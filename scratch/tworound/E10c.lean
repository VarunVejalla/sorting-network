import AKS.Chvatal.Bulk2Fail
import AKS.Chvatal.Bulk2Bridge
import AKS.Chvatal.FlipSpec
namespace Chvatal
open Classical in
theorem t1 {m n : ℕ} (hm : 2 ^ 42 ≤ m) (hn : 16 ≤ n) :
   ∃ σ2 : Scramble m n, HasCombinatorialPropertyB2 σ2 (371 / 10 ^ 8) (1 / 59000000) ∧ HasCombinatorialPropertyB2 (flipScramble σ2) (371 / 10 ^ 8) (1 / 59000000) := by
  exact exists_and_flip (m := m) (n := n)
    (fun σ => HasCombinatorialPropertyB2 σ (371 / 10 ^ 8) (1 / 59000000))
    (c := 1 / 1000) (by norm_num) (bulk2_fail_fraction_le hm hn)
end Chvatal
