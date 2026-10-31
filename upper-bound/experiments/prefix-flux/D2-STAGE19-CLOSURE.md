# Stage 19 reserve-invariant closure

For depths `d = childDepth + 9` with `childDepth >= 7`, focused Lean checks now
verify all actual Stage-19 sender-input contracts and the Run-19-to-Run-20
invariant transition:

- `D2Stage19LevelSevenInputs.lean`: level-seven `botDesc` contract; Stage 18
  supplies its cap and balance, and the Stage-18 level-eight `botRise` leaves
  full native roots for the endpoint and mass reserves.
- `D2Stage19LevelFiveFloor.lean` and `D2Stage19LevelFiveInputs.lean`: the
  level-six floor is the Stage-18 level-six middle quota; the full level-five
  `mid` contract follows from the Stage-18 level-four regular cut.
- `D2Stage19LevelThreeFloor.lean` and `D2Stage19LevelThreeInputs.lean`: the
  level-four floor is the Stage-18 level-four middle quota; the full level-three
  `mid` contract follows from the Stage-18 level-two late contract.
- `D2Stage19LevelOneFloor.lean` and `D2Stage19LevelOneInputs.lean`: at depth 16
  the top sender is `topDesc`; from depth 17 it is `topRise`. Stage 18's root
  `topDesc` resets the level-one root to zero in both cases. The rising case
  uses the Stage-18 level-two middle quota as its child reserve.
- `D2Stage19PreservesInv.lean`: inactive level zero wraps the level-one
  contracts, and the generic stage-preservation theorem proves the full
  Run-19-to-Run-20 reserve-invariant step.

The quoted quota scales make the reserve margins transparent. For a `mid`
sender at levels 3 or 5, the Stage-18 child quota is 15 times the required
endpoint threshold. At level 1, the Stage-18 level-two quota is 15 times its
endpoint threshold and 30 times Stage 19's `topRise` quota.

These results close one more finite transition in the candidate schedule. They
do not prove a uniform arbitrary-stage provider, physical rank/port realization,
terminal sorting, or the coefficient-300 bound. The next formal gate is
Run-20-to-Run-21, whose active bands return to the even levels; after that, a
periodic/general stage argument is still needed to replace finite stage-by-stage
bridging.
