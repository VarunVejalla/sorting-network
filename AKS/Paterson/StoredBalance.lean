module

public import AKS.Paterson.StoredRouting
public import AKS.Paterson.Transition

/-! # Rank balance from coherent subtree totals

The parent size and sibling subtree deficit share the same rounded total.
Consequently their rounding errors cancel instead of adding an independent
64-wire deficit. This remains valid for a parent adjacent to cold storage.
-/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem coherent_deficit {width cap half sibling : ℚ}
    (hcoherent : 2 * half + 2 * sibling =
      (scheduledSubtree fastParams width cap : ℚ)) :
    width / 2 - sibling ≤ half + ancestorReserve fastParams cap / 2 := by
  have hround := le_ceil32 (idealSubtree fastParams width cap)
  have hideal : width - ancestorReserve fastParams cap ≤ idealSubtree fastParams width cap :=
    le_max_right _ _
  change idealSubtree fastParams width cap ≤ (scheduledSubtree fastParams width cap : ℚ) at hround
  linarith

/-- Coherent integer allocation discharges the rank-balance premise from
subtree contamination and the old parent stranger bound. `P` is the sibling
native cohort and `Q` is the unwanted side of the child's threshold. -/
theorem coherent_cohort_balance {n : ℕ} (S T : Finset (Fin n))
    (hST : Disjoint S T) (P Q O : Fin n → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred O]
    (hcover : ∀ i ∈ S, Q i → P i ∨ O i)
    {width cap : ℚ} (hcap : fastParams.minCapacity ≤ cap)
    (heven : 2 ∣ S.card)
    (hhalf : cap / 2 - 64 ≤ ((S.card / 2 : ℕ) : ℚ))
    (hcoherent : (S.card : ℚ) + 2 * T.card = scheduledSubtree fastParams width cap)
    (hnative : ((univ.filter P).card : ℚ) = width / 2)
    (hintrusion : ((T.filter (fun i ↦ ¬ P i)).card : ℚ) ≤
      2 * fastParams.mu * fastParams.delta * fastParams.A ^ 2 /
        (1 - 4 * fastParams.delta ^ 2 * fastParams.A ^ 2) * cap)
    (hold : ((S.filter O).card : ℚ) ≤ fastParams.mu * cap) :
    goodCohort (S.card / 2) ≤ (S.filter (fun i ↦ ¬ Q i)).card := by
  let half : ℚ := (S.card / 2 : ℕ)
  let reserve := ancestorReserve fastParams cap / 2
  let intrusion := 2 * fastParams.mu * fastParams.delta * fastParams.A ^ 2 /
    (1 - 4 * fastParams.delta ^ 2 * fastParams.A ^ 2) * cap
  have hsize : (S.card : ℚ) = 2 * half := by
    have h := Nat.mul_div_cancel' heven
    dsimp [half]
    exact_mod_cast h.symm
  have hdeficit : ((univ.filter P).card : ℚ) - T.card ≤ half + reserve := by
    rw [hnative]
    apply coherent_deficit
    rw [← hsize]
    exact hcoherent
  have hraw := cohort_balance S T hST P Q O hcover hsize hdeficit hintrusion hold
  have hslack : patersonAlpha0 * half ≤ half - reserve - intrusion - fastParams.mu * cap := by
    apply fast_cohort_slack hcap hhalf
    · dsimp [reserve, ancestorReserve]
      linarith
    · exact le_rfl
    · exact le_rfl
  have hcohort := (goodCohort_bounds (S.card / 2)).2.1
  have hresult : (goodCohort (S.card / 2) : ℚ) ≤ (S.filter (fun i ↦ ¬ Q i)).card := by
    exact hcohort.trans (hslack.trans hraw)
  exact_mod_cast hresult

end Paterson.Bags
