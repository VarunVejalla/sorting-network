"""Screen additive and quadratic charges on compatible witness obligations.

LP outputs are rationalized and every layer inequality is checked exactly.
These are finite-width certificates, not asymptotic sorting bounds.
"""
import argparse
from fractions import Fraction
from itertools import combinations
import json

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack, vstack

from kahale_image_difficulty import graph


def features(n,arity):
    out = []
    for size in range(2,arity+1):
        for coords in combinations(range(n),size):
            mask = sum(1 << i for i in coords)
            ones = (mask-1)&mask
            while ones:
                zeros = mask ^ ones
                # At least one forced one lies before a forced zero.
                if zeros and (ones & -ones).bit_length() < zeros.bit_length():
                    for k in range(ones.bit_count(),n-zeros.bit_count()+1):
                        out.append((k,ones,zeros))
                ones = (ones-1)&mask
    return out


def probe(n):
    states,layers,edges,actual,prefix,suffix = graph(n)
    result = []
    for arity in sorted({2,min(4,n),n}):
        fs = features(n,arity)
        for counting,signed in ((False,False),(True,False),(False,True),(True,True)):
            rows = np.array([[sum(1 for x in image if x.bit_count()==k and x & a==a and not x & b)
                              for k,a,b in fs] for image in states],dtype=int)
            if not counting:
                rows = (rows>0).astype(int)
            terminal = next(i for i,d in enumerate(actual) if d==0)
            assert not rows[terminal].any()
            changes = np.array([rows[s]-rows[t] for s,row in enumerate(edges) for t in row])
            fit = linprog(-rows[0].astype(float),A_ub=csr_matrix(changes),
                          b_ub=np.ones(len(changes)),bounds=(None,None) if signed else (0,None),method="highs")
            assert fit.success
            weights = [Fraction(float(v)).limit_denominator(1000000) for v in fit.x]
            active = [(j,w) for j,w in enumerate(weights) if w]
            exact_changes = [sum(int(row[j])*w for j,w in active) for row in changes]
            scale = max(Fraction(1),max(exact_changes))
            weights = [w/scale for w in weights]
            active = [(j,w) for j,w in enumerate(weights) if w]
            for row in changes:
                assert sum(int(row[j])*w for j,w in active)<=1
            bound = sum(int(rows[0,j])*w for j,w in active)
            assert bound<=actual[0]
            dual = [(i,Fraction(float(-v)).limit_denominator(1000000))
                    for i,v in enumerate(fit.ineqlin.marginals) if v < -1e-10]
            assert all(w>=0 for i,w in dual)
            dual_columns = [sum(int(changes[i,j])*w for i,w in dual) for j in range(len(fs))]
            dual_valid = all(v==int(rows[0,j]) if signed else v>=int(rows[0,j])
                             for j,v in enumerate(dual_columns))
            dual_bound = sum(w for i,w in dual)
            tight = [i for i,v in enumerate(exact_changes) if v==scale]
            witness = None
            if tight:
                source,li = divmod(tight[0],len(layers))
                witness = dict(prefix=prefix(source),layer=layers[li])
            result.append(dict(maximum_arity=arity,counting=counting,signed=signed,features=len(fs),
                               numerical_optimum=float(-fit.fun),certified_lower_bound=str(bound),
                               exact_dual_valid=dual_valid,
                               certified_charge_family_upper_bound=str(dual_bound) if dual_valid else None,
                               exact_family_optimum=dual_valid and dual_bound==bound,
                               certified_bound_float=float(bound),exact_inequalities=len(changes),
                               active_weights=[dict(weight=str(w),rank=fs[j][0],ones_mask=fs[j][1],zeros_mask=fs[j][2]) for j,w in active],
                               dual_layer_weights=[dict(weight=str(w),source_image_index=i//len(layers),
                                                        layer=layers[i%len(layers)]) for i,w in dual],
                               tight_layer_witness=witness))
    return dict(wires=n,images=len(states),exact_sorting_depth=actual[0],screens=result)


def quadratic_probe(n):
    states,layers,edges,actual,prefix,suffix = graph(n)
    base = features(n,2)
    values = np.array([[int(any(x.bit_count()==k and x & a==a and not x & b for x in image))
                        for k,a,b in base] for image in states],dtype=int)
    columns,labels,seen = [],[],set()
    for i in range(len(base)):
        for j in range(i,len(base)):
            if abs(base[i][0]-base[j][0])>1:
                continue
            column = values[:,i]*values[:,j]
            key = tuple(column.tolist())
            if key not in seen:
                seen.add(key)
                columns.append(column)
                labels.append((i,j))
    rows = np.array(columns).T
    changes = np.array([rows[s]-rows[t] for s,row in enumerate(edges) for t in row])
    screens = []
    for signed in (False,True):
        fit = linprog(-rows[0].astype(float),A_ub=csr_matrix(changes),b_ub=np.ones(len(changes)),
                      bounds=(None,None) if signed else (0,None),method="highs")
        assert fit.success
        w = [Fraction(float(v)).limit_denominator(1000000) for v in fit.x]
        active = [(j,v) for j,v in enumerate(w) if v]
        scale = max(Fraction(1),max(sum(int(row[j])*v for j,v in active) for row in changes))
        active = [(j,v/scale) for j,v in active]
        assert all(sum(int(row[j])*v for j,v in active)<=1 for row in changes)
        bound = sum(int(rows[0,j])*v for j,v in active)
        assert bound<=actual[0]
        dual = [(i,Fraction(float(-v)).limit_denominator(1000000))
                for i,v in enumerate(fit.ineqlin.marginals) if v < -1e-10]
        dc = [sum(int(changes[i,j])*v for i,v in dual) for j in range(len(columns))]
        valid = all(v==int(rows[0,j]) if signed else v>=int(rows[0,j]) for j,v in enumerate(dc))
        db = sum(v for i,v in dual)
        screens.append(dict(signed=signed,certified_lower_bound=str(bound),
                            certified_family_upper_bound=str(db) if valid else None,
                            exact_family_optimum=valid and db==bound,
                            exact_inequalities=len(changes),
                            active_weights=[dict(weight=str(v),first=base[labels[j][0]],second=base[labels[j][1]])
                                            for j,v in active],
                            dual_layer_weights=[dict(weight=str(v),source_image_index=i//len(layers),layer=layers[i%len(layers)])
                                                for i,v in dual]))
    target = Fraction(3) if n==4 else Fraction(41,10)
    charge_matrix = csr_matrix(changes)
    split = hstack((charge_matrix,-charge_matrix),format="csr")
    initial_constraint = csr_matrix(np.concatenate((-rows[0],rows[0])).reshape(1,-1))
    sparse_fit = linprog(np.ones(2*len(columns)),A_ub=vstack((split,initial_constraint),format="csr"),
                         b_ub=np.concatenate((np.ones(len(changes)),[-float(target)])),
                         bounds=(0,None),method="highs")
    assert sparse_fit.success
    sw = [(Fraction(round(float(sparse_fit.x[j]-sparse_fit.x[len(columns)+j])*100000),100000)
           if n==5 else Fraction(float(sparse_fit.x[j]-sparse_fit.x[len(columns)+j])).limit_denominator(1000000))
          for j in range(len(columns))]
    sa = [(j,v) for j,v in enumerate(sw) if v]
    scale = max(Fraction(1),max(sum(int(row[j])*v for j,v in sa) for row in changes))
    sa = [(j,v/scale) for j,v in sa]
    sb = sum(int(rows[0,j])*v for j,v in sa)
    assert all(sum(int(row[j])*v for j,v in sa)<=1 for row in changes)
    assert sb>=3 if n==4 else sb>4
    return dict(wires=n,base_pair_features=len(base),distinct_quadratic_features=len(columns),
                rank_separation_at_most_one=True,screens=screens,
                simplified_certificate=dict(target=str(target),certified_lower_bound=str(sb),
                    active_terms=len(sa),exact_inequalities=len(changes),
                    active_weights=[dict(weight=str(v),first=base[labels[j][0]],second=base[labels[j][1]])
                                    for j,v in sa]))


def scope_counterexample(certificate):
    from kahale_image_difficulty import gate_image
    image = frozenset((0,2,3,7,8,9,11,12,14,15))
    layer = ((0,2),(1,3))
    terms = certificate["active_weights"]
    def potential(domain):
        def witness(p):
            k,a,b = p
            return any(x.bit_count()==k and x & a==a and not x & b for x in domain)
        return sum(Fraction(t["weight"])*witness(t["first"])*witness(t["second"]) for t in terms)
    after = frozenset(gate_image(x,layer) for x in image)
    drop = potential(image)-potential(after)
    assert drop>1
    states,*_ = graph(4)
    assert image not in states
    assert all((x==0 or any(x^(1 << i) in image for i in range(4) if (x >> i)&1))
               and (x==15 or any(x|(1 << i) in image for i in range(4) if not (x >> i)&1)) for x in image)
    for k in range(5):
        todo = {x for x in image if x.bit_count()==k}
        seen = {todo.pop()}
        while todo:
            new = {x for x in todo if any((x^y).bit_count()==2 for y in seen)}
            assert new
            seen |= new
            todo -= new
    return dict(image=sorted(image),layer=layer,exact_drop=str(drop),
                reachable=False,saturated_chain_covers=True,connected_rank_slices=True,
                obstruction="Singleton routing would need at least 2+3 input singleton sources, exceeding 4")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",required=True)
    args = parser.parse_args()
    result = dict(cases=[probe(n) for n in (4,5)],
                  quadratic_cases=[quadratic_probe(n) for n in (4,5)],
                  status="Exact rational charge and dual certificates where indicated; no asymptotic improvement")
    result["scope_counterexample"] = scope_counterexample(result["quadratic_cases"][0]["simplified_certificate"])
    with open(args.output,"w",encoding="utf-8") as handle:
        json.dump(result,handle,indent=2)
        handle.write("\n")
    print(json.dumps([dict(wires=c["wires"],screens=[{k:s[k] for k in
        ("maximum_arity","counting","signed","features","certified_lower_bound","certified_charge_family_upper_bound","exact_family_optimum")}
        for s in c["screens"]]) for c in result["cases"]],indent=2))
    print(json.dumps(result["quadratic_cases"],indent=2))
