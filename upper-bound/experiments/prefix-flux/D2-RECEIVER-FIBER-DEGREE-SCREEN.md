# D2 receiver tile incidence screen

## Purpose

`receiver_fiber_types.py` measures the source/target tile incidence graph of
the exact finite `FlowDAG` routing. A source is one sender-local tile and a
target is one receiver-local tile; an edge means at least one wire is routed
between them. Alongside maximum target fan-in, the screen reports maximum
source fan-out.

## Current observation

Command:

```powershell
python upper-bound/experiments/prefix-flux/receiver_fiber_types.py --depths 7 8 9 --scale 8192 --params 3 3 2
```

An extension to depth 10 used the same command with `--depths 10`.

Across all stages at each tested depth:

| depth | max source tiles into a target tile | max target tiles reached by a source tile |
|---:|---:|---:|
| 7 | 3 | 3 |
| 8 | 3 | 3 |
| 9 | 4 | 3 |
| 10 | 4 | 3 |

At depth 10 the fan-in 4 occurs at stages 10 and 12; the source fan-out
remains at most 3. The depth-9 fan-in 4 occurs at stages 7 and 9. The screen includes the
parent-root overwrite context and exact interval routing from
`receiver_fiber_types.py`.

## Interpretation and next gate

This is finite routing evidence and a locality diagnostic only. It does not
bound the amount of Boolean/profile error carried on an edge, establish an
all-depth degree bound, or prove contraction. A source tile splitting among
at most three target tiles does not by itself stop error growth. The useful
next question is whether the *weighted edge masses* (or a spatial potential on
them) contract under the actual transition. Any analytic argument must include
the target fan-in, not assume it is at most three: depth 9 already has fan-in
four.

The current implementation expands physical tiles, so runtime grows quickly
with `scale * 8^depth`. The depth-10 extension confirms the same degree maxima,
but this is already expensive and does not advance the all-depth argument. Do
not use it as a deep asymptotic screen without replacing that expansion by a
compressed interval-incidence calculation.
