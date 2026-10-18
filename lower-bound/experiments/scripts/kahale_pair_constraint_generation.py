"""Larger-source feasibility screens with exact Farkas certificates if found."""
from fractions import Fraction
from pathlib import Path
import json
import random
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack, vstack
from sympy import Matrix
from kahale_image_difficulty import gate_image
from kahale_layer_occupation import matchings


def main():
    root=Path(__file__).resolve().parents[3]
    base=json.loads((root/'LLM-helpers/kahale-pair-base.json').read_text())
    terms=json.loads((root/'docs/kahale-witness-charge-results.json').read_text())['quadratic_cases'][0]['simplified_certificate']['active_weights']
    masks=[x for x in range(16) if x.bit_count() in (1,2)]
    labels=[()]+[(i,) for i in range(10)]+[(i,j) for i in range(10) for j in range(i,10)]
    def features(hist):
        return tuple(int(np.prod([hist[i] for i in label])) for label in labels)
    fs=[features(hist) for hist in base['histograms']]
    constraints={ (tuple(a-b for a,b in zip(fs[s],fs[t])),bound):
                  witness for (s,t,bound),witness in zip(base['constraints'],base['constraint_witnesses'])}
    equalities={fs[j]:base['fixed_witnesses'][str(j)] for j in base['fixed']}
    table_signatures={tuple(hist):i for i,hist in enumerate(base['histograms'])}
    table_constraints=list(map(tuple,base['constraints']))
    table_fixed=set(base['fixed'])
    def describe(outputs,n):
        shift=n-4
        fiber={y>>shift for y in outputs if not y&((1<<shift)-1)}
        hist=tuple(sum(y>>shift==mask and not y&((1<<shift)-1)
                       for x,y in enumerate(outputs) if x.bit_count() in (1,2)) for mask in masks)
        def witness(t):
            k,a,b=t
            return any(y.bit_count()==k and y&a==a and not y&b for y in fiber)
        value=int(3*sum(Fraction(t['weight'])*witness(t['first'])*witness(t['second']) for t in terms))
        return features(hist),value,fiber=={0,8,12,14,15}
    reports=[]
    rng=random.Random(20261012)
    for n in (6,7,8):
        layers=[layer for layer in matchings(tuple(range(n))) if layer]
        checks=0
        for trial in range(150):
            outputs=list(range(1<<n))
            prefix=[]
            # Include the previous extrapolation failure explicitly.
            sampled=([((0,1),(3,5)),((0,5),(1,3))] if trial==0 and n==6 else [])
            sampled += [rng.choice(layers) for _ in range(8)]
            # Odd-even transposition gives a concrete sorted endpoint.
            sampled += [tuple((i,i+1) for i in range(round%2,n-1,2)) for round in range(n)]
            for layer in sampled:
                f,value,sorted_fiber=describe(outputs,n)
                if sorted_fiber:
                    equalities.setdefault(f,dict(wires=n,prefix=prefix.copy()))
                    table_fixed.add(table_signatures.setdefault(f[1:11],len(table_signatures)))
                after=[gate_image(y,layer) for y in outputs]
                g,next_value,next_sorted=describe(after,n)
                row=tuple(a-b for a,b in zip(f,g))
                constraints.setdefault((row,3-value+next_value),dict(wires=n,prefix=prefix.copy(),layer=layer))
                sid=table_signatures.setdefault(f[1:11],len(table_signatures))
                tid=table_signatures.setdefault(g[1:11],len(table_signatures))
                table_constraints.append((sid,tid,3-value+next_value))
                if next_sorted:
                    equalities.setdefault(g,dict(wires=n,prefix=prefix+[layer]))
                    table_fixed.add(tid)
                outputs=after;prefix.append(layer);checks+=1
            assert set(outputs)=={((1<<k)-1)<<(n-k) for k in range(n+1)}
        entries=list(constraints)
        eq=list(equalities)
        A=np.array([row for row,b in entries],dtype=np.int64)
        b=np.array([b for row,b in entries],dtype=np.int64)
        E=np.array(eq,dtype=np.int64)
        fit=linprog(np.zeros(len(labels)),A_ub=A,b_ub=b,A_eq=E,b_eq=np.zeros(len(eq)),bounds=(None,None),method='highs')
        report=dict(maximum_wires=n,sampled_transitions=checks,inequalities=len(entries),endpoint_equalities=len(eq),lp_status=int(fit.status))
        reports.append(report)
        print(json.dumps(report),flush=True)
        if fit.status==2:
            # Use the actual common initial histogram, rather than its index.
            initial_f,_,_=describe(list(range(16)),4)
            endpoint_only={initial_f:dict(wires=4,prefix=[],kind='initial')}
            for wn in range(4,n+1):
                sorting=[tuple((i,i+1) for i in range(round%2,wn-1,2)) for round in range(wn)]
                outputs=list(range(1<<wn))
                for step in sorting:
                    outputs=[gate_image(y,step) for y in outputs]
                f,_,is_sorted=describe(outputs,wn)
                assert is_sorted
                endpoint_only[f]=dict(wires=wn,prefix=sorting)
            endpoint_fit=linprog(np.zeros(len(labels)),A_ub=A,b_ub=b,A_eq=list(endpoint_only),
                b_eq=np.zeros(len(endpoint_only)),bounds=(None,None),method='highs')
            report['only_global_sorted_endpoints_status']=int(endpoint_fit.status)
            if endpoint_fit.status==2:
                equalities=endpoint_only
                eq=list(equalities)
                E=np.array(eq,dtype=np.int64)
                report['certificate_endpoint_scope']='Only common initial and globally sorted endpoints'
            from scipy.sparse import coo_matrix
            tc=sorted(set(table_constraints))
            rr=[];cc=[];vv=[]
            for i,(s,t,bound) in enumerate(tc):
                rr.extend((i,i));cc.extend((s,t));vv.extend((1,-1))
            tm=coo_matrix((vv,(rr,cc)),shape=(len(tc),len(table_signatures))).tocsr()
            tf=linprog(np.zeros(len(table_signatures)),A_ub=tm,b_ub=[bound for s,t,bound in tc],
                       bounds=[(0,0) if i in table_fixed else (None,None) for i in range(len(table_signatures))],method='highs')
            report['arbitrary_table_status']=int(tf.status)
            report['arbitrary_table_signatures']=len(table_signatures)
            if tf.success:
                th=[Fraction(float(x)).limit_denominator(1000000) for x in tf.x]
                report['arbitrary_table_exact_feasible']=all(th[s]-th[t]<=bound for s,t,bound in tc) and all(th[i]==0 for i in table_fixed)
                report['arbitrary_table_certificate']=[dict(histogram=hist,three_times_correction=str(th[i]))
                    for hist,i in table_signatures.items()]
            # Farkas: y>=0, A^T y+E^T z=0, b^T y=-1.
            dual_matrix=vstack((hstack((csr_matrix(A.T),csr_matrix(E.T))),
                hstack((csr_matrix(b.reshape(1,-1)),csr_matrix((1,len(eq))))))).tocsr()
            dual=linprog(np.concatenate((np.ones(len(entries)),np.zeros(len(eq)))),
                A_eq=dual_matrix,b_eq=[0]*len(labels)+[-1],
                bounds=[(0,None)]*len(entries)+[(None,None)]*len(eq),method='highs')
            assert dual.success
            support=[i for i,x in enumerate(dual.x) if abs(x)>1e-8]
            system=Matrix(dual_matrix[:,support].toarray().astype(np.int64).tolist())
            solution,parameters=system.gauss_jordan_solve(Matrix([0]*len(labels)+[-1]))
            solution=solution.subs({p:Fraction(float(dual.x[support[next(j for j,x in enumerate(solution) if x==p)]])).limit_denominator(1000000) for p in parameters})
            weights=[Fraction(int(x.p),int(x.q)) for x in solution]
            assert all(w>=0 for i,w in zip(support,weights) if i<len(entries))
            assert all(sum(int(dual_matrix[r,i])*w for i,w in zip(support,weights))==(-1 if r==len(labels) else 0) for r in range(len(labels)+1))
            report['exact_farkas_certificate']=True
            certificate=[]
            for i,w in zip(support,weights):
                if i<len(entries):
                    key=entries[i]
                    certificate.append(dict(kind='layer',weight=str(w),row=key[0],bound=key[1],witness=constraints[key]))
                else:
                    key=eq[i-len(entries)]
                    certificate.append(dict(kind='endpoint',weight=str(w),row=key,witness=equalities[key]))
            report['certificate']=certificate
            # Recompute every certificate row from its concrete input cube and
            # comparator prefix, independently of the base signature indices.
            for entry in certificate:
                witness=entry['witness'];wn=witness['wires']
                outputs=list(range(1<<wn))
                for step in witness['prefix']:
                    wires=[i for pair in step for i in pair]
                    assert len(wires)==len(set(wires)) and all(0<=a<b<wn for a,b in step)
                    outputs=[gate_image(y,step) for y in outputs]
                f,value,sorted_fiber=describe(outputs,wn)
                if entry['kind']=='layer':
                    after=[gate_image(y,witness['layer']) for y in outputs]
                    g,next_value,_=describe(after,wn)
                    assert tuple(a-b for a,b in zip(f,g))==tuple(entry['row'])
                    assert 3-value+next_value==entry['bound']
                else:
                    assert sorted_fiber or witness.get('kind')=='initial'
                    assert f==tuple(entry['row'])
            report['concrete_certificate_rows_verified']=len(certificate)
            break
    result=dict(seed=20261012,histogram_masks=masks,monomials=labels,reports=reports,
                status='Finite sampled larger-source constraints; exact infeasibility only where certified')
    (root/'docs/kahale-pair-constraint-generation-results.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
    main()
