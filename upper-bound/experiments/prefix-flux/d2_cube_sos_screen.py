"""Numerical degree-two Boolean-cube SOS screen; no exact certificate claims.

Keep only selected prefixes. Symmetrize under row permutations within the
resulting blocks. This is exact for the restricted-prefix SDP on K individual
Boolean variables, not a model that replaces a block by one Boolean variable.
For x=2*sigma, use diag(Q_full)=0 and bound
  c + x'Q_full x >= (1/2) sum_{i<=k} x_i - mu*k.
Each prefix gets independent multipliers lambda_i*(x_i^2-1).
The block-constant subspace gives the small PSD matrix below; orthogonal
within-block directions give lambda_i <= -H_ii/(b_i-1).
Minimizing c is an optimistic trace floor for the summed spectral method.
"""
import argparse
import json
import numpy as np
import cvxpy as cp


def screen(K, mu, density, solver, spread=None):
    ends = sorted(set([K] + [min(K, int(round(2**(j/density))))
                  for j in range(int(np.ceil(density*np.log2(K)))+1)]))
    b = np.diff([0]+ends).astype(float)
    L = len(b)
    H = cp.Variable((L,L), symmetric=True)
    lam = cp.Variable((L+1,L))
    c = cp.Variable()
    if spread is not None:
        mu = cp.Variable(nonneg=True)
    constraints = []
    for i in range(L):
        if b[i] == 1:
            constraints.append(H[i,i] == 0)
        else:
            constraints.append(lam[:,i] <= -H[i,i]/(b[i]-1))
    for j, k in enumerate([0]+ends):
        linear = (-np.sqrt(b)/4 * (np.arange(L)<j)).reshape(-1,1)
        residual = cp.bmat([[H-cp.diag(lam[j,:]), linear],
                           [linear.T, cp.reshape(c+mu*k+b@lam[j,:], (1,1), order='C')]])
        constraints.append(residual >> 0)
    problem = cp.Problem(cp.Minimize(c if spread is None else c+spread*mu), constraints)
    kwargs = dict(solver=solver)
    if solver == 'SCS':
        kwargs.update(eps=2e-5, max_iters=30000)
    value = problem.solve(**kwargs)
    violation = max(float(np.max(con.violation())) for con in constraints)
    return dict(K=K, mu=mu if spread is None else float(mu.value), spread=spread,
                density=density, blocks=L, status=problem.status,
                objective=value, max_primal_violation=violation,
                note='numerical restricted-prefix SDP optimum; not an exact lower bound')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--half-rows', type=int, default=4096)
    p.add_argument('--mus', nargs='+', type=float, default=[0,.05,.1,.15])
    p.add_argument('--density', type=int, default=1)
    p.add_argument('--solver', default='CLARABEL')
    p.add_argument('--output')
    p.add_argument('--coupled', action='store_true',
                   help='derive optimistic D=2*c_round1 and optimize round2 mu continuously')
    a=p.parse_args()
    results=[]
    for mu in a.mus:
        result=screen(a.half_rows,mu,a.density,a.solver)
        results.append(result)
        print(json.dumps(result),flush=True)
    if a.coupled:
        first=screen(a.half_rows,0,a.density,a.solver)
        result=screen(a.half_rows,0,a.density,a.solver,2*first['objective'])
        result['optimistic_first_round']=first
        results.append(result)
        print(json.dumps(result),flush=True)
    if a.output:
        from pathlib import Path
        Path(a.output).write_text(json.dumps(results,indent=2)+'\n')

if __name__=='__main__':
    main()
