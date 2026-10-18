"""Exact five-wire obstruction to lifting the four-wire witness charge."""
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import json
from kahale_image_difficulty import gate_image
from kahale_preimage_capacity import pair_union_capacity


def main():
    root = Path(__file__).resolve().parents[3]
    terms = json.loads((root/'docs/kahale-witness-charge-results.json').read_text())['quadratic_cases'][0]['simplified_certificate']['active_weights']
    def potential(domain):
        def witness(t):
            k,a,b = t
            return any(x.bit_count()==k and x&a==a and not x&b for x in domain)
        return sum(Fraction(t['weight'])*witness(t['first'])*witness(t['second']) for t in terms)
    prefix = (((0,1),(2,3)),((0,2),))
    def run(x):
        for layer in prefix:
            x = gate_image(x,layer)
        return x
    domain = {run(x) for x in range(32)}
    inputs = {x for x in range(32) if not run(x)&1}
    assert inputs=={x for x in range(32) if x&15!=15}
    fiber = {x>>1 for x in domain if not x&1}
    layer = ((0,2),(1,3))
    after = {gate_image(x,layer) for x in fiber}
    before_value,after_value = potential(fiber),potential(after)
    assert before_value-after_value==2
    q = [(run(1<<i)>>1).bit_length()-1 for i in range(5)]
    m = [q.count(i) for i in range(4)]
    assert q==[0,0,2,2,3] and m==[2,0,2,1]
    edges = [tuple(i for i in range(4) if y>>i&1) for y in fiber if y.bit_count()==2]
    for mask in range(1<<len(edges)):
        selected = [e for i,e in enumerate(edges) if mask>>i&1]
        assert len(selected)<=pair_union_capacity(m,selected)
    assert all(sum(m[i] for i in range(4) if y>>i&1)>=3 for y in fiber if y.bit_count()==3)
    # Independently check the concrete map on every surviving input and cube edge.
    for x in inputs:
        y = run(x)>>1
        assert y.bit_count()==x.bit_count()
        for i in range(5):
            z = x | (1<<i)
            if z in inputs:
                assert y & ~(run(z)>>1)==0
    result = dict(prefix=prefix,global_next_layer=((1,3),(2,4)),image=sorted(domain),
                  fiber=sorted(fiber),after_fiber=sorted(after),singleton_routes=q,
                  singleton_multiplicities=m,input_fiber_size=len(inputs),
                  potential_before=str(before_value),potential_after=str(after_value),drop='2',
                  rank_two_hall_subsets_checked=1<<len(edges),
                  status='Exact actual-network counterexample to the unweighted conditional-fiber lift; not a lower-bound improvement')
    (root/'docs/kahale-capacity-lift-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
