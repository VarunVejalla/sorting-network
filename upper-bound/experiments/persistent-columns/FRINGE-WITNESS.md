# Deterministic obstruction to a dispersion-only receive theorem

2026-10-20, Codex (GPT-6). Derived argument pending fresh review; no Lean.
This rejects a proposed local promise, not every persistent-column algorithm.

Consider one source whose column count is d times the receiver's column
count, with integer d>=1. Its low port contains at least t full rows. In
each row, an arbitrary FIXED permutation routes exactly d source entries to
each receiving column. The source columns are sorted Boolean prefixes.
Fix one receiving column v and choose t with d*t>f, where f is the receiving
low-fringe height.

For each row r=0,...,t-1, take the d source columns routed to v in that row.
Set each selected column's zero-prefix height to at least r+1 (use the maximum
requirement if a column is selected repeatedly); set other heights to zero.
This choice is allowed to depend on the fixed network, as it must for an
all-input guarantee. Then:

- The total number H of input zeros is at most d*t*(t+1)/2.
- Every chosen entry at row r is zero, so column v receives at least d*t zeros.
- All zeros lie in the source's first t rows, hence inside its own low port.
- After sorting receiving columns, at least d*t-f zeros escape the low f rows.

Consequently escapes/H is at least

    (d*t-f) / (d*t*(t+1)/2).

When t is near 2*f/d, this is asymptotic to d/(2*f). A one-pass fringe
contract with error 1/J therefore needs f of order d*J under these promises,
rather than the square-root-in-J two-round behavior. The exact displayed
rational bound, not the asymptotic estimate, is the rejection test.

Crucially, H is bounded independently of the number n_s of source columns,
while the mean absolute height deviation is at most 2H/n_s. By increasing
n_s, the input's aggregate column dispersion can be made arbitrarily small.
Thus sorted columns + an arbitrarily small aggregate dispersion bound +
containment of rare keys in the source port do NOT imply the desired receiving
fringe bound. This construction does not establish reachability from the
proposed earlier stages or satisfy a full global native-rank embedding by
itself. A successful algorithm would need a stronger reachable-state promise
and a joint analysis of preceding redistributions.

The bulk-only screen is also narrow. Under the conjectural recurrence with
uniform coefficient C=1, one fresh sort barely passes the300 gate (295.167 at
(x,y,z)=(3,4,2), q=22), while two fresh sorts bottom at316.667 before fringe,
frontiers, terminal geometry, or bootstrap costs. At C=1.25 the corresponding
minima are322 and344.25. This is a parameter-model screen, not a mathematical
lower bound: C=1 has not been established as a necessary constant.

Next decision: get independent review of the algebra and witness before
developing any Lean. Do not infer that this paper test settles the full
sub300 goal or rules out all persistent representations.
