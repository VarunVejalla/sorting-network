import D2OrdinaryRankRouting

open scoped BigOperators

namespace Chvatal.D2RoutedMass

open Chvatal.D2OrdinaryRankRouting

/-- The number of true Boolean values in a finite wire set. -/
def trueMass {α : Type*} [DecidableEq α] (value : α → Bool)
    (wires : Finset α) : Nat :=
  (wires.filter fun w => value w = true).card

/-- Grouping disjoint sender pieces by their schedule receiver preserves the
exact Boolean mass: each receiver's count is the sum of the counts in the
pieces tagged for it. This is the count-valued form of
`routedTargetPiece`; it supplies the elementary mass step needed when the
physical profile slices are identified with actual routed wire pieces. -/
theorem routedTargetPiece_trueMass_eq_sum
    {α I D J : Type*} [DecidableEq α] [Fintype D] [DecidableEq D]
    [DecidableEq J]
    (localPiece : I → D → Finset α) (target : I → D → J)
    (hdisjoint : ∀ i d d', d ≠ d' → Disjoint (localPiece i d) (localPiece i d'))
    (value : α → Bool) (i : I) (j : J) :
    trueMass value (routedTargetPiece localPiece target i j) =
      ∑ d ∈ Finset.univ.filter (fun d : D => target i d = j),
        trueMass value (localPiece i d) := by
  classical
  unfold trueMass routedTargetPiece
  rw [Finset.filter_biUnion]
  rw [Finset.card_biUnion (fun d _ d' _ hne =>
    Finset.disjoint_filter_filter (hdisjoint i d d' hne))]

/-- The number of false Boolean values in a finite wire set. -/
def falseMass {T : Type*} [DecidableEq T] (value : T -> Bool)
    (wires : Finset T) : Nat :=
  (wires.filter fun w => value w = false).card

/-- False mass obeys the same receiver partition identity. This is the form
used when rank ports are counted in the top-prefix false-profile orientation. -/
theorem routedTargetPiece_falseMass_eq_sum
    {T I D J : Type*} [DecidableEq T] [Fintype D] [DecidableEq D]
    [DecidableEq J]
    (localPiece : I -> D -> Finset T) (target : I -> D -> J)
    (hdisjoint : forall i d d', (d = d' -> False) ->
      Disjoint (localPiece i d) (localPiece i d'))
    (value : T -> Bool) (i : I) (j : J) :
    falseMass value (routedTargetPiece localPiece target i j) =
      Finset.sum (Finset.univ.filter fun d : D => target i d = j)
        (fun d => falseMass value (localPiece i d)) := by
  classical
  unfold falseMass routedTargetPiece
  rw [Finset.filter_biUnion]
  rw [Finset.card_biUnion (fun d _ d' _ hne =>
    Finset.disjoint_filter_filter (hdisjoint i d d' hne))]

end Chvatal.D2RoutedMass
