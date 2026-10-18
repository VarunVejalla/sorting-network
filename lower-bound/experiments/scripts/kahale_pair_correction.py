"""Finite feasibility of an arbitrary singleton/pair mass correction.

The correction table is shared between genuine four-wire images and
five-wire output-zero fibers. No asymptotic claim is made.
"""
from collections import deque
from fractions import Fraction
from functools import cache
from pathlib import Path
import json
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from kahale_image_difficulty import graph, gate_image


def main():
    root = Path(__file__).resolve().parents[3]
    terms = json.loads((root/'docs/kahale-witness-charge-results.json').read_text())['quadratic_cases'][0]['simplified_certificate']['active_weights']
    def potential(domain):
        def witness(t):
            k,a,b=t
            return any(x.bit_count()==k and x&a==a and not x&b for x in domain)
        return sum(Fraction(t['weight'])*witness(t['first'])*witness(t['second']) for t in terms)
    signatures = {}
    constraints = []
    terminals = set()
    initial = set()
    reports = []
    provenance={}
    fixed_provenance={}
    sorted_points = {0,8,12,14,15}
    for n in (4,5):
        images,layers,edges,*_ = graph(n)
        inputs = [x for x in range(1<<n) if x.bit_count() in (1,2)]
        start = (0,tuple(inputs))
        todo = deque([start])
        states = {start}
        parents={start:None}
        def path(state):
            steps=[]
            while parents[state] is not None:
                state,step=parents[state]
                steps.append(step)
            return steps[::-1]
        @cache
        def describe(state):
            s,outputs=state
            fiber = set(images[s]) if n==4 else {x>>1 for x in images[s] if not x&1}
            hist = tuple(sum((y if n==4 else y>>1)==mask and (n==4 or not y&1)
                             for y in outputs) for mask in range(16) if mask.bit_count() in (1,2))
            sig = signatures.setdefault(hist,len(signatures))
            if fiber==sorted_points:
                terminals.add(sig)
                fixed_provenance.setdefault(sig,dict(wires=n,prefix=path(state),kind='sorted_fiber'))
            return sig,int(3*potential(fiber))
        initial.add(describe(start)[0])
        fixed_provenance[describe(start)[0]]=dict(wires=n,prefix=[],kind='initial')
        transitions = 0
        while todo:
            state=todo.popleft()
            source,value = describe(state)
            for j,layer in enumerate(layers):
                target=(edges[state[0]][j],tuple(gate_image(x,layer) for x in state[1]))
                if target not in states:
                    states.add(target)
                    parents[target]=state,layer
                    todo.append(target)
                dest,next_value=describe(target)
                constraints.append((source,dest,3-value+next_value))
                provenance.setdefault((source,dest,3-value+next_value),(n,state,layer))
                transitions += 1
        reports.append(dict(wires=n,reachable_states=len(states),transitions=transitions))
        for key,witness in list(provenance.items()):
            if isinstance(witness,tuple) and witness[0]==n:
                _,state,layer=witness
                provenance[key]=dict(wires=n,prefix=path(state),layer=layer)
    # h is scaled by three. Equal-signature edges give a direct obstruction.
    direct = [(s,t,b) for s,t,b in constraints if s==t and b<0]
    unique = sorted(set(constraints))
    rows,cols,values = [],[],[]
    for i,(s,t,b) in enumerate(unique):
        rows.extend((i,i));cols.extend((s,t));values.extend((1,-1))
    matrix=coo_matrix((values,(rows,cols)),shape=(len(unique),len(signatures))).tocsr()
    fixed=terminals|initial
    scratch=root/'LLM-helpers'
    scratch.mkdir(exist_ok=True)
    (scratch/'kahale-pair-base.json').write_text(json.dumps(dict(histograms=list(signatures),
        constraints=unique,fixed=sorted(fixed),constraint_witnesses=[provenance[key] for key in unique],
        fixed_witnesses={str(j):fixed_provenance[j] for j in fixed}))+'\n')
    fit=linprog(np.zeros(len(signatures)),A_ub=matrix,b_ub=[b for s,t,b in unique],
                bounds=[(0,0) if j in fixed else (None,None) for j in range(len(signatures))],method='highs')
    result=dict(catalogues=reports,histogram_masks=[x for x in range(16) if x.bit_count() in (1,2)],
                correction_scaling='Stored coefficients represent three times h; divide by 3',
                signatures=len(signatures),unique_constraints=len(unique),
                terminal_signatures=len(terminals),initial_signatures=len(initial),
                identical_signature_violations=len(direct),lp_status=int(fit.status),lp_message=fit.message,
                status='Finite feasibility screen; no Lean or asymptotic improvement')
    if fit.success:
        h=[Fraction(float(x)).limit_denominator(1000000) for x in fit.x]
        valid=all(h[s]-h[t]<=b for s,t,b in unique) and all(h[j]==0 for j in fixed)
        result['exact_rational_feasible']=valid
        if valid:
            result['correction_table']=[dict(histogram=hist,three_times_correction=str(h[j])) for hist,j in signatures.items()]
    histograms=np.array(list(signatures),dtype=np.int64)
    simple=[]
    for degree in (1,2):
        labels=[(i,) for i in range(10)]
        if degree==2:
            labels += [(i,j) for i in range(10) for j in range(i,10)]
        features=np.array([np.prod(histograms[:,label],axis=1) for label in labels]).T
        changes=np.array([features[s]-features[t] for s,t,b in unique])
        equality=features[sorted(fixed)]
        simple_fit=linprog(np.zeros(len(labels)),A_ub=changes,b_ub=[b for s,t,b in unique],
                           A_eq=equality,b_eq=np.zeros(len(fixed)),bounds=(None,None),method='highs')
        report=dict(degree=degree,features=len(labels),lp_status=int(simple_fit.status))
        if simple_fit.success:
            w=[Fraction(float(x)).limit_denominator(1000000) for x in simple_fit.x]
            if degree==2:
                from sympy import Matrix
                active=[i for i,slack in enumerate(simple_fit.ineqlin.residual) if abs(slack)<1e-7]
                system=Matrix(np.vstack((equality,changes[active])).tolist())
                rhs=Matrix([0]*len(equality)+[unique[i][2] for i in active])
                solution,parameters=system.gauss_jordan_solve(rhs)
                substitutions={p:Fraction(float(simple_fit.x[next(j for j,x in enumerate(solution) if x==p)])).limit_denominator(1000000)
                               for p in parameters}
                solution=solution.subs(substitutions)
                w=[Fraction(int(x.p),int(x.q)) for x in solution]
            report['exact_rational_feasible']=all(sum(int(row[j])*w[j] for j in range(len(w)))<=b
                for row,(s,t,b) in zip(changes,unique)) and all(sum(int(row[j])*w[j] for j in range(len(w)))==0 for row in equality)
            report['weights']=[dict(monomial=label,three_times_coefficient=str(v)) for label,v in zip(labels,w) if v]
        simple.append(report)
    result['polynomial_screens']=simple
    if simple[-1].get('exact_rational_feasible'):
        import random
        from kahale_layer_occupation import matchings
        rng=random.Random(20261011)
        six_layers=[layer for layer in matchings(tuple(range(6))) if layer]
        masks=[x for x in range(16) if x.bit_count() in (1,2)]
        def six_value(outputs):
            fiber={y>>2 for y in outputs if not y&3}
            histogram=tuple(sum(y>>2==mask and not y&3 for x,y in enumerate(outputs)
                                if x.bit_count() in (1,2)) for mask in masks)
            correction=sum(v*np.prod([histogram[i] for i in label]).item()
                           for label,v in zip(labels,w))/3
            return potential(fiber)+correction
        worst=Fraction(0)
        counter=None
        for trial in range(400):
            outputs=list(range(64))
            prefix=[]
            for depth in range(8):
                layer=rng.choice(six_layers)
                after=[gate_image(x,layer) for x in outputs]
                drop=six_value(outputs)-six_value(after)
                if drop>worst:
                    worst=drop
                    counter=dict(prefix=prefix.copy(),next_layer=layer,drop=str(drop))
                outputs=after
                prefix.append(layer)
        result['six_wire_sample']=dict(seed=20261011,paths=400,transitions=3200,
            worst_drop=str(worst),unit_drop_passed=worst<=1,worst_transition=counter,
            scope='Random actual prefixes; not exhaustive. Tests this fitted polynomial only.')
    (root/'docs/kahale-pair-correction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:([ {a:b for a,b in r.items() if a!='weights'} for r in v]
                         if k=='polynomial_screens' else v)
                      for k,v in result.items() if k!='correction_table'},indent=2))


if __name__=='__main__':
    main()
