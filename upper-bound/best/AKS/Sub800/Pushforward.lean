import AKS.Chvatal.Lemma63

/-! # Uniform scrambles push forward to independent uniform row subsets

For output columns `S` with `#S = s`, a uniform permutation `π` of the `n` columns gives the
uniform `s`-subset `{j | π j ∈ S}`: every `s`-subset `T` is hit by exactly `s! (n-s)!`
permutations (`card_perm_supset_image`). Rows of a scramble are independent, so a uniform scramble
gives `m` independent uniform `s`-subsets. -/

open Finset BigOperators

namespace Push

open Chvatal

variable {n : ℕ}

/-- The input columns that `π` sends into `S`. -/
def rowSet (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun j => π j ∈ S

theorem card_rowSet (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : (rowSet π S).card = S.card := by
  classical
  refine Finset.card_bij (fun j _ => π j) (fun j hj => by simpa [rowSet] using hj)
    (fun a _ b _ h => π.injective h) (fun T hT => ⟨π.symm T, by simp [rowSet, hT], by simp⟩)

theorem rowSet_eq_iff (π : Equiv.Perm (Fin n)) (S T : Finset (Fin n)) (hT : T.card = S.card) :
    rowSet π S = T ↔ S ⊆ T.image π := by
  classical
  constructor
  · rintro rfl x hx
    rw [Finset.mem_image]
    exact ⟨π.symm x, by simp [rowSet, hx], by simp⟩
  · intro h
    have himg : T.image π = S := by
      apply (Finset.eq_of_subset_of_card_le h _).symm
      rw [Finset.card_image_of_injective _ π.injective, hT]
    ext j
    simp only [rowSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← himg, Finset.mem_image]
    constructor
    · rintro ⟨k, hk, hkj⟩
      rw [π.injective hkj] at hk
      exact hk
    · intro hj; exact ⟨j, hj, rfl⟩

/-- Fiber size: `s! (n-s)!` permutations send a given `s`-subset onto `S`. -/
theorem card_fiber (S T : Finset (Fin n)) (hT : T.card = S.card) :
    (Finset.univ.filter fun π : Equiv.Perm (Fin n) => rowSet π S = T).card =
      S.card.factorial * (n - S.card).factorial := by
  classical
  have : (Finset.univ.filter fun π : Equiv.Perm (Fin n) => rowSet π S = T) =
      Finset.univ.filter fun π : Equiv.Perm (Fin n) => S ⊆ T.image π := by
    ext π; simp [rowSet_eq_iff π S T hT]
  rw [this, ← Fintype.card_subtype, card_perm_supset_image, hT, Nat.descFactorial_self]

/-- One row: the pushforward of the uniform permutation is uniform on `s`-subsets. -/
theorem sum_perm_rowSet (S : Finset (Fin n)) (f : Finset (Fin n) → ℝ) :
    ∑ π : Equiv.Perm (Fin n), f (rowSet π S) =
      (S.card.factorial * (n - S.card).factorial : ℕ) *
        ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard S.card, f T := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun π => rowSet π S)
    (t := (Finset.univ : Finset (Fin n)).powersetCard S.card)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTc := (Finset.mem_powersetCard.1 hT).2
    rw [Finset.sum_congr rfl fun π hπ => by rw [(Finset.mem_filter.1 hπ).2]]
    rw [Finset.sum_const, nsmul_eq_mul, card_fiber S T hTc]
  · intro π _
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, card_rowSet π S⟩

/-- All rows: a uniform scramble pushes forward to independent uniform `s`-subsets. -/
theorem sum_scramble_rowSets {m : ℕ} (S : Finset (Fin n)) (F : (Fin m → Finset (Fin n)) → ℝ) :
    ∑ σ : Scramble m n, F (fun r => rowSet (σ r) S) =
      ((S.card.factorial * (n - S.card).factorial : ℕ) : ℝ) ^ m *
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin m => (Finset.univ : Finset (Fin n)).powersetCard S.card),
          F ω := by
  classical
  set P := Fintype.piFinset (fun _ : Fin m => (Finset.univ : Finset (Fin n)).powersetCard S.card)
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Scramble m n)))
    (g := fun σ => fun r => rowSet (σ r) S) (t := P)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω hω => ?_
    rw [Finset.sum_congr rfl fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2]]
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    -- the fiber is a product of the row fibers
    have hcard : (Finset.univ.filter fun σ : Scramble m n => (fun r => rowSet (σ r) S) = ω).card =
        (Fintype.piFinset fun r => Finset.univ.filter fun π : Equiv.Perm (Fin n) =>
          rowSet π S = ω r).card := by
      refine Finset.card_bij (fun σ _ => (σ : Fin m → Equiv.Perm (Fin n))) ?_ ?_ ?_
      · intro σ hσ
        rw [Fintype.mem_piFinset]
        intro r
        rw [Finset.mem_filter] at hσ ⊢
        exact ⟨Finset.mem_univ _, congrFun hσ.2 r⟩
      · intro a _ b _ h; exact h
      · intro σ hσ
        refine ⟨σ, ?_, rfl⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, funext fun r => ?_⟩
        rw [Fintype.mem_piFinset] at hσ
        exact (Finset.mem_filter.1 (hσ r)).2
    rw [hcard, Fintype.card_piFinset]
    have hω' := Fintype.mem_piFinset.1 hω
    rw [Finset.prod_congr rfl fun r _ => card_fiber S (ω r) (Finset.mem_powersetCard.1 (hω' r)).2]
    simp
  · intro σ _
    rw [Fintype.mem_piFinset]
    intro r
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, card_rowSet (σ r) S⟩

end Push
