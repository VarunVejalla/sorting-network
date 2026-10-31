import D2ScheduleReserve

set_option maxHeartbeats 3000000

namespace Chvatal.D2Reserve

/-- A tighter one-step deficit estimate for ordinary D2 cuts. For a top-rise
parent the old deficit is zero and the `1/256` port is enough; for mid and
bottom-descending parents the exact `15/4096` port combines with a
`15/8192` old-deficit envelope. Every new endpoint then stays in the same
`15/8192` envelope at capacity `2*c`, while the six interior child deficits
are reset to zero. -/
theorem d2_ordinary_update_preserves_15over8192
    {a G total low high pi half c : Nat} (size pos : Fin 8 → Nat)
    (hbalance : low + high = G)
    (hconserve : a + G = total)
    (hpiAlloc : pi ≤ a)
    (heven : pi = 2 * half)
    (hlow : low ≤ G) (hhigh : high ≤ G)
    (hprofileCap : (G = 0 ∧ 256 * pi ≤ c) ∨
      (8192 * G ≤ 15 * c ∧ 4096 * pi ≤ 15 * c))
    (hleftReserve : c ≤ 128 * size 0)
    (hrightReserve : c ≤ 128 * size 7)
    (hstart : pos 0 = 0)
    (hcontig : ∀ k : Nat, (hk : k < 7) →
      pos ⟨k + 1, by omega⟩ = pos ⟨k, by omega⟩ + size ⟨k, by omega⟩)
    (htotal : pos 7 + size 7 = total) :
    ∀ j : Fin 8,
      4096 * d2LocalChildDeficitUpdate .mid (pos j) (size j)
        (low + half) (total - high - half) ≤ 15 * c := by
  have hpiCap : 256 * pi ≤ c := by
    rcases hprofileCap with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hweak : 4096 * G ≤ 23 * c := by
    rcases hprofileCap with ⟨hG, _⟩ | ⟨hG, _⟩ <;> nlinarith
  have hshape := d2_ordinary_update_shape_of_tolerant_reserve
    size pos hbalance hconserve hpiAlloc heven hweak hlow hhigh hpiCap
    hleftReserve hrightReserve hstart hcontig htotal
  intro j
  by_cases hj0 : j.val = 0
  · have hj : j = 0 := Fin.ext hj0
    subst j
    rw [hshape.1]
    rcases hprofileCap with ⟨hG, hpi⟩ | ⟨hG, hpi⟩
    · have hlow0 : low = 0 := by omega
      have hhalf : 512 * half ≤ c := by omega
      rw [hlow0]
      nlinarith
    · have hlowBound : 8192 * low ≤ 15 * c := by
        exact le_trans (Nat.mul_le_mul_left 8192 hlow) hG
      have hhalfBound : 8192 * half ≤ 15 * c := by
        rw [heven] at hpi
        omega
      nlinarith
  · by_cases hj7 : j.val = 7
    · have hj : j = 7 := Fin.ext hj7
      subst j
      rw [hshape.2.1]
      rcases hprofileCap with ⟨hG, hpi⟩ | ⟨hG, hpi⟩
      · have hhigh0 : high = 0 := by omega
        have hhalf : 512 * half ≤ c := by omega
        rw [hhigh0]
        nlinarith
      · have hhighBound : 8192 * high ≤ 15 * c := by
          exact le_trans (Nat.mul_le_mul_left 8192 hhigh) hG
        have hhalfBound : 8192 * half ≤ 15 * c := by
          rw [heven] at hpi
          omega
        nlinarith
    · have hjlo : 0 < j.val := by omega
      have hjhi : j.val < 7 := by omega
      rw [hshape.2.2 j hjlo hjhi]
      omega

/-- The observed sharp integer form of the same invariant. The seven-unit
slack is preserved exactly by a mid/bot-descending endpoint update because
`4096*pi = 15*c`; a top-rise parent has zero old deficit and its larger port
still leaves ample slack. -/
theorem d2_ordinary_update_preserves_affine_15over8192
    {a G total low high pi half c : Nat} (size pos : Fin 8 → Nat)
    (hcpos : 0 < c)
    (hbalance : low + high = G)
    (hconserve : a + G = total)
    (hpiAlloc : pi ≤ a)
    (heven : pi = 2 * half)
    (hlow : low ≤ G) (hhigh : high ≤ G)
    (hprofileCap : (G = 0 ∧ 256 * pi ≤ c) ∨
      (8192 * G + 7 ≤ 15 * c ∧ 4096 * pi ≤ 15 * c))
    (hleftReserve : c ≤ 128 * size 0)
    (hrightReserve : c ≤ 128 * size 7)
    (hstart : pos 0 = 0)
    (hcontig : ∀ k : Nat, (hk : k < 7) →
      pos ⟨k + 1, by omega⟩ = pos ⟨k, by omega⟩ + size ⟨k, by omega⟩)
    (htotal : pos 7 + size 7 = total) :
    ∀ j : Fin 8,
      8192 * d2LocalChildDeficitUpdate .mid (pos j) (size j)
        (low + half) (total - high - half) + 7 ≤ 30 * c := by
  have hpiCap : 256 * pi ≤ c := by
    rcases hprofileCap with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hweak : 4096 * G ≤ 23 * c := by
    rcases hprofileCap with ⟨hG, _⟩ | ⟨hG, _⟩ <;> nlinarith
  have hshape := d2_ordinary_update_shape_of_tolerant_reserve
    size pos hbalance hconserve hpiAlloc heven hweak hlow hhigh hpiCap
    hleftReserve hrightReserve hstart hcontig htotal
  intro j
  by_cases hj0 : j.val = 0
  · have hj : j = 0 := Fin.ext hj0
    subst j
    rw [hshape.1]
    rcases hprofileCap with ⟨hG, hpi⟩ | ⟨hG, hpi⟩
    · have hlow0 : low = 0 := by omega
      have hpiLarge : 4096 * pi ≤ 16 * c := by omega
      rw [hlow0]
      have hhalfEq : 8192 * half = 4096 * pi := by omega
      nlinarith
    · have hlowBound : 8192 * low ≤ 8192 * G := Nat.mul_le_mul_left 8192 hlow
      have hhalfEq : 8192 * half = 4096 * pi := by omega
      nlinarith
  · by_cases hj7 : j.val = 7
    · have hj : j = 7 := Fin.ext hj7
      subst j
      rw [hshape.2.1]
      rcases hprofileCap with ⟨hG, hpi⟩ | ⟨hG, hpi⟩
      · have hhigh0 : high = 0 := by omega
        have hpiLarge : 4096 * pi ≤ 16 * c := by omega
        rw [hhigh0]
        have hhalfEq : 8192 * half = 4096 * pi := by omega
        nlinarith
      · have hhighBound : 8192 * high ≤ 8192 * G := Nat.mul_le_mul_left 8192 hhigh
        have hhalfEq : 8192 * half = 4096 * pi := by omega
        nlinarith
    · have hjlo : 0 < j.val := by omega
      have hjhi : j.val < 7 := by omega
      rw [hshape.2.2 j hjlo hjhi]
      omega

/-- The sharp affine envelope is already strong enough to satisfy the
existing `1/512` parent-deficit gate. Its quota branch also implies the
existing `1/256` port gate, in both the top-rise and mid/bottom-descending
cases. -/
theorem d2_affine_profile_implies_existing_local_caps
    {G pi c : Nat}
    (hprofile : (G = 0 ∧ 256 * pi ≤ c) ∨
      (8192 * G + 7 ≤ 15 * c ∧ 4096 * pi ≤ 15 * c)) :
    512 * G ≤ c ∧ 256 * pi ≤ c := by
  rcases hprofile with ⟨hG, hpi⟩ | ⟨hG, hpi⟩
  · omega
  · constructor <;> nlinarith

/-- After an ordinary update, the sharp output estimate at scale `c`
immediately supplies the standard sender deficit gate at the next scheduled
capacity `2*c`. This is the local adapter needed when composing the sharp
profile with the existing recursive stage invariant. -/
theorem d2_ordinary_update_affine_output_to_next_sender_cap
    {a G total low high pi half c : Nat} (size pos : Fin 8 → Nat)
    (hcpos : 0 < c)
    (hbalance : low + high = G)
    (hconserve : a + G = total)
    (hpiAlloc : pi ≤ a)
    (heven : pi = 2 * half)
    (hlow : low ≤ G) (hhigh : high ≤ G)
    (hprofileCap : (G = 0 ∧ 256 * pi ≤ c) ∨
      (8192 * G + 7 ≤ 15 * c ∧ 4096 * pi ≤ 15 * c))
    (hleftReserve : c ≤ 128 * size 0)
    (hrightReserve : c ≤ 128 * size 7)
    (hstart : pos 0 = 0)
    (hcontig : ∀ k : Nat, (hk : k < 7) →
      pos ⟨k + 1, by omega⟩ = pos ⟨k, by omega⟩ + size ⟨k, by omega⟩)
    (htotal : pos 7 + size 7 = total) :
    ∀ j : Fin 8,
      512 * d2LocalChildDeficitUpdate .mid (pos j) (size j)
        (low + half) (total - high - half) ≤ 2 * c := by
  intro j
  have hchild := d2_ordinary_update_preserves_affine_15over8192
    size pos hcpos hbalance hconserve hpiAlloc heven hlow hhigh hprofileCap
    hleftReserve hrightReserve hstart hcontig htotal j
  nlinarith

end Chvatal.D2Reserve
