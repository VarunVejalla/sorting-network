

`d2FlowCandidateRun_active_child_zero_or_affine_profile` now packages the active-child split as one checked interface: at the next snapshot an active child is either top-descending with exact zero root (using the core two snapshots back), or non-top-descending with the affine profile (using the core one snapshot back). This is the role-complete child input needed by a future recursive core-provider step. It still does not construct the recursive core, discharge the other active-node local fields (including endpoint reserves and balance), or prove the global sorting bound.


The role-complete interface is at `D2TopDescHistory.lean:786` and was checked by direct `lean` compilation after the final edit. It intentionally states only the branch-specific root obligation; it does not package endpoint reserves, node balance, or the recursive descendants required by `d2FlowStageAffineCoreInputs`.


`d2FlowCandidateRun_active_child_role_root_contract` (in `D2TopDescHistory.lean`) strengthens the split to match the role-specific root/profile cases of the affine core: `topDesc` and `topRise` have zero root, `mid`/`botDesc` have the affine profile, and `botRise` has no extra root condition. It compiles directly with Lean. The remaining local core fields are still balance and the two endpoint reserves for ordinary/top-rise roles; after those, the recursive all-node assembly and startup induction remain open.


For balance, `D2TopDescHistory.lean` now proves `d2FlowTreeInv_atPath` and `d2FlowTreeInv_child_balance_of_zero`, then specializes them in `d2FlowCandidateRun_zero_child_balanced_of_inv`. Thus the top-descending/top-rising zero-root branches also satisfy the core's endpoint-balance field whenever the target snapshot has the reserve invariant. This is conditional on target-stage invariant preservation; it does not solve the active `botRise` balance case or the ordinary-role endpoint reserves. The module compiled after these additions.
