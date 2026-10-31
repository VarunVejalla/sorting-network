# Reflected physical pack checkpoint (2026-10-28)

`D2ReflectedPhysicalPack.lean` kernel-checks an actual comparator-network
realization of the fixed 4096-by-64 two-shuffle profile recurrence. The key is
to reflect each row-dependent *column permutation*, not reverse physical
wires: the post-shuffle inputs have the same column counts as the old
top-prefix model after row reflection. The semantic pack is linked to the
existing repair theorem.

The fixed Boolean stage consists of three 4096-wire column sorts and the
42-layer two-grid repair, for depth at most 276. For every Boolean input, its
output has monotone columns and one row-major uncertainty interval of at most
832 wires; all threshold bits outside that interval are false below and true
above.

This closes the physical realization gap for the local profile transition.
It does not prove a coefficient near 273 or 300: the 832-wire interval depends
on the threshold, and the missing global rank/address recurrence must show
that such windows compose across active blocks and satisfy an all-depth
terminal contract. The next bridge should test UB-34's L4 sidedness and
`sent_outside_le_of_tail_profile` against this explicit reflected wire map.

The arbitrary-input wrapper `reflectedPhysicalPack2Exec_of_input` now derives
the source-height profile as the actual per-column true counts of its Boolean
input, then gives the physical output as the corresponding unary profile
followed by the fixed row-preserving permutation. It kernel-checks in the
focused direct Lean build. This removes a local profile-realization premise;
it does not identify these columns with the D2 scheduler's next-stage sender
profiles or close the global recurrence.
