import D2ScheduleReserve

namespace Chvatal.D2Reserve

/-! The relaxed sender-factor estimate needs a sharper exceptional profile
than the old native-allocation argument supplied. This lemma isolates the
precise endpoint bounds needed when the intervening child role is `botRise`.
-/

theorem d2_two_step_sender_factor_279_of_tolerant_role_profile
    {a c gOld gNow rhoOld : Rat} (childRho : Fin 8 → Rat)
    {childRole : D2Role}
    (hchildRole : childRole = .mid ∨ childRole = .botDesc ∨
      childRole = .botRise)
    (hid : a / c = 16 * gOld + 16 * rhoOld +
      32 * (Finset.univ.sum childRho) - gNow)
    (hgOld : gOld ≤ 23 / 4096) (hgNow : 0 ≤ gNow)
    (hold : rhoOld ≤ 1 / 256)
    (holdBot : childRole = .botRise → rhoOld ≤ 15 / 4096)
    (hregular : (childRole = .mid ∨ childRole = .botDesc) →
      ∀ j, childRho j ≤ 15 / 4096)
    (hbotEnds : childRole = .botRise →
      childRho 0 ≤ 49 / 16384 ∧ childRho 7 ≤ 49 / 16384)
    (hbotInterior : childRole = .botRise →
      ∀ j : Fin 8, j.val ≠ 0 → j.val ≠ 7 → childRho j ≤ 1 / 256) :
    a / c ≤ 279 / 256 := by
  have hcase : (rhoOld ≤ 15 / 4096 ∧
      32 * (Finset.univ.sum childRho) ≤ 241 / 256) ∨
      (rhoOld ≤ 1 / 256 ∧
      32 * (Finset.univ.sum childRho) ≤ 15 / 16) := by
    rcases hchildRole with hmid | hdesc | hbot
    · right
      constructor
      · exact hold
      · have hsum := Finset.sum_le_sum (s := Finset.univ)
          (fun j _ => hregular (Or.inl hmid) j)
        have hconst : (Finset.univ.sum fun _ : Fin 8 =>
            (15 / 4096 : Rat)) = 8 * (15 / 4096 : Rat) := by
          norm_num [Fin.sum_univ_succ]
        rw [hconst] at hsum
        nlinarith
    · right
      constructor
      · exact hold
      · have hsum := Finset.sum_le_sum (s := Finset.univ)
          (fun j _ => hregular (Or.inr hdesc) j)
        have hconst : (Finset.univ.sum fun _ : Fin 8 =>
            (15 / 4096 : Rat)) = 8 * (15 / 4096 : Rat) := by
          norm_num [Fin.sum_univ_succ]
        rw [hconst] at hsum
        nlinarith
    · left
      constructor
      · exact holdBot hbot
      · exact d2_botRise_child_quota_sum_of_endpoint_caps childRho
          (hbotEnds hbot).1 (hbotEnds hbot).2 (hbotInterior hbot)
  exact d2_two_step_sender_factor_279_of_tolerant_budget
    childRho hid hgOld hgNow hcase

end Chvatal.D2Reserve
